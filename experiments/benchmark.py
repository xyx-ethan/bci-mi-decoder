"""Frontier-vs-classical benchmark on the BCI-ISLA 2026 6-subject dataset.

Same data, same fold, same preprocessing for every method. No method
specifically tuned for our submission; published default hyperparameters
are used throughout.

Methods evaluated:
  Deep (via braindecode 1.4.0):
    - ShallowConvNet (Schirrmeister 2017)
    - Deep4Net       (Schirrmeister 2017)
    - EEGNetv4       (Lawhern 2018)
    - EEGConformer   (Song 2023)
    - ATCNet         (Altaheri 2022)
    - EEGITNet       (Salami 2022)
  Classical (this package):
    - CSP+SVM-RBF, mu band 8-13 Hz, n_components=4
    - CSP+LDA,     mu band 8-13 Hz, n_components=4
    - pyRiemann tangent-space + L2 logistic regression, broad 7-30 Hz

Protocol:
  - StratifiedKFold(n_splits=5, shuffle=True, random_state=42)
  - Crop samples 384-1537 (2.25 s @ 512 Hz) + bandpass 7-30 Hz + per-trial z-score
  - Deep models: 3 random seeds (42, 43, 44); 100 epochs;
    AdamW(lr=1e-3, weight_decay=1e-4); batch_size=32
  - All bases use the SAME preprocessed data and SAME folds; the only
    thing that varies between rows is the model class.

Outputs:
  - JSON per (method × subject × seed) under bench/results/
  - bench/summary.md aggregating per-subject CV mean ± std + macro mean
"""
from __future__ import annotations

import json
import os
import random
import sys
import time
import warnings
from dataclasses import dataclass
from pathlib import Path

import numpy as np
import torch
import torch.nn as nn
from sklearn.model_selection import StratifiedKFold

warnings.filterwarnings("ignore")

REPO = Path(r"C:\Users\manxw\Downloads\BCI -- ISLA2026\bci-mi-decoder-clone")
sys.path.insert(0, str(REPO / "src"))
from bci_mi_decoder.preprocessing import bandpass, crop, standardize
from bci_mi_decoder.models.csp_svm import make_csp_lda, make_csp_svm
from bci_mi_decoder.models.pyriemann_ts import make_tangent_space_lr

DATA = Path(r"C:\Users\manxw\Downloads\BCI -- ISLA2026\项目进展\2026-04-18-2041-下载BCI数据集\data")
OUT = Path(__file__).resolve().parent / "results"
OUT.mkdir(parents=True, exist_ok=True)

DEVICE = torch.device("cuda" if torch.cuda.is_available() else "cpu")
print(f"[init] device={DEVICE}")

# ---------- experimental constants ---------------------------------------
SUBJECTS = ["A", "B", "C", "D", "E", "F"]   # = Subject 1..6
CROP_WIN = (384, 1537)        # 2.25 s @ 512 Hz, 1153 samples
SFREQ    = 512.0
BAND     = (7.0, 30.0)        # broad MI band, neutral across methods
N_SPLITS = 5
SPLIT_SEED = 42

DEEP_SEEDS = [42, 43, 44]     # 3 seeds for deep run-to-run variance
DEEP_EPOCHS = 100
DEEP_BATCH = 32
DEEP_LR = 1e-3
DEEP_WD = 1e-4


# ---------- helpers ------------------------------------------------------
def load_subject(letter: str) -> tuple[np.ndarray, np.ndarray]:
    X = np.load(DATA / f"subject_{letter}_X_train.npy").astype(np.float64)
    y_raw = np.load(DATA / f"subject_{letter}_y_train.npy", allow_pickle=True)
    y = np.asarray([0 if str(v) == "left_hand" else 1 for v in y_raw], dtype=np.int64)
    return X, y


def preprocess(X: np.ndarray) -> np.ndarray:
    """Same preprocessing for every method."""
    return standardize(bandpass(crop(X, *CROP_WIN), *BAND, sfreq=SFREQ))


def set_all_seeds(seed: int) -> None:
    random.seed(seed)
    np.random.seed(seed)
    torch.manual_seed(seed)
    torch.cuda.manual_seed_all(seed)
    torch.backends.cudnn.deterministic = True
    torch.backends.cudnn.benchmark = False


# ---------- deep training loop -------------------------------------------
def train_eval_torch(
    model: nn.Module,
    X_tr: np.ndarray, y_tr: np.ndarray,
    X_va: np.ndarray, y_va: np.ndarray,
    epochs: int = DEEP_EPOCHS,
    batch_size: int = DEEP_BATCH,
    lr: float = DEEP_LR,
    weight_decay: float = DEEP_WD,
) -> float:
    """Standard training: AdamW + cross-entropy. Returns val accuracy."""
    model = model.to(DEVICE)
    Xtr = torch.tensor(X_tr, dtype=torch.float32, device=DEVICE)
    ytr = torch.tensor(y_tr, dtype=torch.long, device=DEVICE)
    Xva = torch.tensor(X_va, dtype=torch.float32, device=DEVICE)
    yva = torch.tensor(y_va, dtype=torch.long, device=DEVICE)

    opt = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=weight_decay)
    crit = nn.CrossEntropyLoss()

    n = Xtr.shape[0]
    for epoch in range(epochs):
        model.train()
        perm = torch.randperm(n, device=DEVICE)
        for i in range(0, n, batch_size):
            idx = perm[i:i + batch_size]
            xb, yb = Xtr[idx], ytr[idx]
            opt.zero_grad()
            logits = model(xb)
            loss = crit(logits, yb)
            loss.backward()
            opt.step()

    model.eval()
    with torch.no_grad():
        logits = model(Xva)
        pred = logits.argmax(dim=-1).cpu().numpy()
    return float((pred == y_va).mean())


# ---------- model factories ----------------------------------------------
def build_deep(name: str, n_chans: int, n_times: int):
    """Source-paper default hyperparameters per braindecode 1.4.0."""
    from braindecode.models import (
        ShallowFBCSPNet, Deep4Net, EEGNetv4, EEGConformer, ATCNet, EEGITNet,
    )
    factories = {
        "ShallowConvNet": lambda: ShallowFBCSPNet(n_chans=n_chans, n_outputs=2, n_times=n_times),
        "Deep4Net":       lambda: Deep4Net(n_chans=n_chans, n_outputs=2, n_times=n_times),
        "EEGNetv4":       lambda: EEGNetv4(n_chans=n_chans, n_outputs=2, n_times=n_times),
        "EEGConformer":   lambda: EEGConformer(n_chans=n_chans, n_outputs=2, n_times=n_times),
        "ATCNet":         lambda: ATCNet(n_chans=n_chans, n_outputs=2, n_times=n_times),
        "EEGITNet":       lambda: EEGITNet(n_chans=n_chans, n_outputs=2, n_times=n_times),
    }
    return factories[name]()


# ---------- runners ------------------------------------------------------
def run_deep(method: str, subject: str) -> dict:
    """Run one deep method on one subject across 3 seeds × 5 folds."""
    X, y = load_subject(subject)
    Xpp = preprocess(X).astype(np.float32)
    n_chans, n_times = Xpp.shape[1], Xpp.shape[2]

    skf = StratifiedKFold(n_splits=N_SPLITS, shuffle=True, random_state=SPLIT_SEED)
    seed_means = []
    seed_fold_table = []
    for seed in DEEP_SEEDS:
        set_all_seeds(seed)
        fold_accs = []
        for fold_i, (tr, va) in enumerate(skf.split(Xpp, y)):
            model = build_deep(method, n_chans, n_times)
            acc = train_eval_torch(model, Xpp[tr], y[tr], Xpp[va], y[va])
            fold_accs.append(acc)
            del model
            torch.cuda.empty_cache()
        seed_means.append(float(np.mean(fold_accs)))
        seed_fold_table.append(fold_accs)
    return {
        "method": method,
        "subject": subject,
        "seeds": DEEP_SEEDS,
        "seed_means": seed_means,
        "fold_accs_per_seed": seed_fold_table,
        "mean": float(np.mean(seed_means)),
        "std":  float(np.std(seed_means)),
        "n_chans": n_chans,
        "n_times": n_times,
    }


def run_classical(method: str, subject: str, band: tuple[float, float]) -> dict:
    """Run one classical (sklearn-style) method on one subject."""
    X, y = load_subject(subject)
    # Classical can use a method-specific band rather than the shared 7-30 Hz
    Xpp = standardize(bandpass(crop(X, *CROP_WIN), *band, sfreq=SFREQ))

    skf = StratifiedKFold(n_splits=N_SPLITS, shuffle=True, random_state=SPLIT_SEED)
    fold_accs = []
    for tr, va in skf.split(Xpp, y):
        if method == "csp_svm_mu":
            est = make_csp_svm(n_components=4, kernel="rbf")
        elif method == "csp_lda_mu":
            est = make_csp_lda(n_components=4)
        elif method == "csp_svm_broad":
            est = make_csp_svm(n_components=4, kernel="rbf")
        elif method == "csp_lda_broad":
            est = make_csp_lda(n_components=4)
        elif method == "riem_ts_broad":
            est = make_tangent_space_lr()
        else:
            raise ValueError(method)
        est.fit(Xpp[tr], y[tr])
        pred = est.predict(Xpp[va])
        fold_accs.append(float((pred == y[va]).mean()))
    return {
        "method": method,
        "subject": subject,
        "fold_accs": fold_accs,
        "mean": float(np.mean(fold_accs)),
        "std":  float(np.std(fold_accs)),
        "band": band,
    }


# ---------- driver -------------------------------------------------------
def main(target: str = "all") -> None:
    deep_methods = [
        "ShallowConvNet", "Deep4Net", "EEGNetv4", "EEGConformer",
        "ATCNet", "EEGITNet",
    ]
    classical_jobs = [
        ("csp_svm_mu",     (8.0, 13.0)),
        ("csp_lda_mu",     (8.0, 13.0)),
        ("csp_svm_broad",  (7.0, 30.0)),
        ("csp_lda_broad",  (7.0, 30.0)),
        ("riem_ts_broad",  (7.0, 30.0)),
    ]

    # ---- classical (fast, deterministic) ------------------------------
    if target in ("all", "classical"):
        print("\n[stage] classical methods (deterministic, ~10 min total)")
        for method, band in classical_jobs:
            for subj in SUBJECTS:
                tag = f"{method}__subj{subj}"
                out = OUT / f"{tag}.json"
                if out.exists():
                    print(f"  [skip] {tag}")
                    continue
                t0 = time.time()
                rec = run_classical(method, subj, band)
                rec["wall_seconds"] = time.time() - t0
                out.write_text(json.dumps(rec, indent=2))
                print(f"  [done] {tag:38s}  CV={rec['mean']:.4f}  ({rec['wall_seconds']:.1f}s)")

    # ---- deep (slow, GPU) ---------------------------------------------
    if target in ("all", "deep"):
        print(f"\n[stage] deep methods on {DEVICE}")
        total = len(deep_methods) * len(SUBJECTS)
        i = 0
        for method in deep_methods:
            for subj in SUBJECTS:
                i += 1
                tag = f"{method}__subj{subj}"
                out = OUT / f"{tag}.json"
                if out.exists():
                    print(f"  [{i}/{total}] [skip] {tag}")
                    continue
                t0 = time.time()
                try:
                    rec = run_deep(method, subj)
                except Exception as e:
                    rec = {"method": method, "subject": subj, "error": f"{type(e).__name__}: {e}"}
                rec["wall_seconds"] = time.time() - t0
                out.write_text(json.dumps(rec, indent=2))
                if "error" in rec:
                    print(f"  [{i}/{total}] [FAIL] {tag:38s}  {rec['error']}  ({rec['wall_seconds']:.1f}s)")
                else:
                    print(f"  [{i}/{total}] [done] {tag:38s}  CV={rec['mean']:.4f}±{rec['std']:.4f}  ({rec['wall_seconds']:.1f}s)")


if __name__ == "__main__":
    target = sys.argv[1] if len(sys.argv) > 1 else "all"
    main(target=target)
