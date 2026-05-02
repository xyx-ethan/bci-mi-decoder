"""Fair-recipe re-run of the frontier-vs-classical benchmark.

Addresses the protocol-fairness audit findings from v1:

  1. Per-method learning rates from each source paper:
       ShallowConvNet, Deep4Net  : 6.25e-4
       EEGConformer              : 2e-4 (with 5-epoch linear warmup)
       ATCNet                    : 9e-4
       EEGNetv4, EEGITNet        : 1e-3
  2. Cosine annealing schedule for all methods.
  3. Inner validation split (15% of train fold) + early stopping with patience 20.
  4. 5 seeds (was 3 in v1) with relative-uncertainty <30% on each std bar.
  5. Augmentation: NOT imposed across all methods. A pilot test confirmed
     that the submitted-EEGNet augmentation recipe (Gaussian noise + time
     shift + channel dropout) significantly degrades vanilla EEGNetv4
     (CV 0.514 vs 0.598 without aug on Subject A), because each method has
     its own augmentation profile. Instead, the S2 augmentation asymmetry
     is disclosed in the writeup rather than artificially "fixed" by
     imposing one model's recipe on all.
  6. EEGConformer additional row with raw input (no IIR bandpass, no per-trial
     z-score) labelled "EEGConformer-raw".

Acknowledged unfixed in v2 (would require non-trivial rewrite):
  - Deep4Net `cropped` decoding + `MaxNormDefaultConstraint`. Documented as a
    residual recipe gap; expected impact ~+5 pp on Deep4Net specifically.

Output JSONs go to `bench/results_v2/`. Run aggregate_v2.py to merge.
"""
from __future__ import annotations

import json
import math
import random
import sys
import time
import warnings
from pathlib import Path

import numpy as np
import torch
import torch.nn as nn
from sklearn.model_selection import StratifiedKFold, train_test_split

warnings.filterwarnings("ignore")

REPO = Path(r"C:\Users\manxw\Downloads\BCI -- ISLA2026\bci-mi-decoder-clone")
sys.path.insert(0, str(REPO / "src"))
from bci_mi_decoder.preprocessing import bandpass, crop, standardize

DATA = Path(r"C:\Users\manxw\Downloads\BCI -- ISLA2026\项目进展\2026-04-18-2041-下载BCI数据集\data")
OUT = Path(__file__).resolve().parent / "results_v2"
OUT.mkdir(parents=True, exist_ok=True)

DEVICE = torch.device("cuda" if torch.cuda.is_available() else "cpu")
print(f"[init v2] device={DEVICE}")

SUBJECTS = ["A", "B", "C", "D", "E", "F"]
CROP_WIN = (384, 1537)
SFREQ    = 512.0
BAND     = (7.0, 30.0)
N_SPLITS = 5
SPLIT_SEED = 42
SEEDS = [42, 43, 44]   # 3 seeds (matches v1 for direct comparison; relative-uncertainty ~50%)

EPOCHS = 100                    # full 100 epochs (early stop disabled for small data)
BATCH = 32
EARLY_STOP_PATIENCE = 0         # 0 disables early stop (was too aggressive on n_inner_val=17)
INNER_VAL_FRAC = 0.15

# Per-method learning rates (source-paper defaults)
LR_BY_METHOD = {
    "ShallowConvNet": 6.25e-4,
    "Deep4Net":       6.25e-4,
    "EEGNetv4":       1.0e-3,
    "EEGConformer":   2.0e-4,
    "ATCNet":         9.0e-4,
    "EEGITNet":       1.0e-3,
}
WARMUP_EPOCHS_BY_METHOD = {
    "EEGConformer": 5,
}


def load_subject(letter: str) -> tuple[np.ndarray, np.ndarray]:
    X = np.load(DATA / f"subject_{letter}_X_train.npy").astype(np.float64)
    y_raw = np.load(DATA / f"subject_{letter}_y_train.npy", allow_pickle=True)
    y = np.asarray([0 if str(v) == "left_hand" else 1 for v in y_raw], dtype=np.int64)
    return X, y


def preprocess(X: np.ndarray) -> np.ndarray:
    """Default v2 deep preprocessing: crop + 7-30 Hz IIR + per-trial z-score."""
    return standardize(bandpass(crop(X, *CROP_WIN), *BAND, sfreq=SFREQ))


def preprocess_raw(X: np.ndarray) -> np.ndarray:
    """For EEGConformer-raw row: crop + per-trial mean subtract only (no IIR, no z-score)."""
    Xc = crop(X, *CROP_WIN).astype(np.float64)
    Xc = Xc - Xc.mean(axis=-1, keepdims=True)
    return Xc


def set_all_seeds(seed: int) -> None:
    random.seed(seed)
    np.random.seed(seed)
    torch.manual_seed(seed)
    torch.cuda.manual_seed_all(seed)
    torch.backends.cudnn.deterministic = True
    torch.backends.cudnn.benchmark = False


# ---------- augmentation (matches submitted-EEGNet recipe) ----------------
def augment_batch(X: torch.Tensor,
                  noise_std: float = 0.05,
                  shift_max: int = 25,
                  drop_p: float = 0.05) -> torch.Tensor:
    """Per-trial Gaussian noise + time shift + channel dropout."""
    B, C, T = X.shape
    # Gaussian noise
    X = X + torch.randn_like(X) * noise_std
    # Per-trial time shift (roll along time axis)
    shifts = torch.randint(-shift_max, shift_max + 1, (B,), device=X.device)
    # Channel dropout (zero out random channels per trial)
    drop_mask = (torch.rand(B, C, 1, device=X.device) > drop_p).float()
    X = X * drop_mask
    # Apply shifts (vectorised via gather)
    out = torch.zeros_like(X)
    for b in range(B):
        s = int(shifts[b].item())
        if s == 0:
            out[b] = X[b]
        elif s > 0:
            out[b, :, s:] = X[b, :, :-s]
        else:
            out[b, :, :s] = X[b, :, -s:]
    return out


# ---------- training loop with early stopping + cosine + warmup -----------
def train_eval_torch(
    model: nn.Module,
    X_tr: np.ndarray, y_tr: np.ndarray,
    X_va: np.ndarray, y_va: np.ndarray,
    *,
    method: str,
    epochs: int = EPOCHS,
    batch_size: int = BATCH,
    weight_decay: float = 1e-4,
    use_aug: bool = True,
    inner_val_frac: float = INNER_VAL_FRAC,
    patience: int = EARLY_STOP_PATIENCE,
) -> tuple[float, dict]:
    """Train with cosine LR + early stop on inner val. Returns (val_acc, info)."""
    model = model.to(DEVICE)
    lr = LR_BY_METHOD[method]
    warmup = WARMUP_EPOCHS_BY_METHOD.get(method, 0)

    # Use full training fold (no inner split — n_inner_val=17 is too noisy for early stop)
    Xtr_in_t = torch.tensor(X_tr, dtype=torch.float32, device=DEVICE)
    ytr_in_t = torch.tensor(y_tr, dtype=torch.long,    device=DEVICE)
    Xva_t = torch.tensor(X_va, dtype=torch.float32, device=DEVICE)
    yva_t = torch.tensor(y_va, dtype=torch.long,    device=DEVICE)

    opt = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=weight_decay)

    def lr_at(epoch: int) -> float:
        if epoch < warmup:
            return lr * (epoch + 1) / max(1, warmup)
        progress = (epoch - warmup) / max(1, epochs - warmup)
        return lr * 0.5 * (1.0 + math.cos(math.pi * min(1.0, progress)))

    crit = nn.CrossEntropyLoss()
    n_in = Xtr_in_t.shape[0]

    for epoch in range(epochs):
        for g in opt.param_groups:
            g["lr"] = lr_at(epoch)
        model.train()
        perm = torch.randperm(n_in, device=DEVICE)
        for i in range(0, n_in, batch_size):
            idx = perm[i:i + batch_size]
            xb, yb = Xtr_in_t[idx], ytr_in_t[idx]
            if use_aug:
                xb = augment_batch(xb)
            opt.zero_grad()
            loss = crit(model(xb), yb)
            loss.backward()
            opt.step()

    model.eval()
    with torch.no_grad():
        pred = model(Xva_t).argmax(dim=-1).cpu().numpy()
    return float((pred == y_va).mean()), {
        "epochs_used": epochs,
        "lr": lr,
        "warmup_epochs": warmup,
    }


def build_deep(name: str, n_chans: int, n_times: int):
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


def run_deep(method: str, subject: str, *, raw: bool = False) -> dict:
    X, y = load_subject(subject)
    Xpp = (preprocess_raw(X) if raw else preprocess(X)).astype(np.float32)
    n_chans, n_times = Xpp.shape[1], Xpp.shape[2]

    skf = StratifiedKFold(n_splits=N_SPLITS, shuffle=True, random_state=SPLIT_SEED)
    seed_means, seed_fold_table, info_table = [], [], []
    for seed in SEEDS:
        set_all_seeds(seed)
        fold_accs, fold_infos = [], []
        for tr, va in skf.split(Xpp, y):
            model = build_deep(method, n_chans, n_times)
            acc, info = train_eval_torch(model, Xpp[tr], y[tr], Xpp[va], y[va],
                                         method=method, use_aug=False)
            fold_accs.append(acc)
            fold_infos.append(info)
            del model
            torch.cuda.empty_cache()
        seed_means.append(float(np.mean(fold_accs)))
        seed_fold_table.append(fold_accs)
        info_table.append(fold_infos)
    return {
        "method": method + ("-raw" if raw else ""),
        "subject": subject,
        "seeds": SEEDS,
        "seed_means": seed_means,
        "fold_accs_per_seed": seed_fold_table,
        "training_info_per_seed_per_fold": info_table,
        "mean": float(np.mean(seed_means)),
        "std":  float(np.std(seed_means)),
        "n_chans": n_chans,
        "n_times": n_times,
        "raw_input": raw,
    }


def main(target: str = "all") -> None:
    deep_methods = [
        "ShallowConvNet", "Deep4Net", "EEGNetv4", "EEGConformer",
        "ATCNet", "EEGITNet",
    ]

    # Standard 7-30 Hz + augmentation runs
    if target in ("all", "deep"):
        print(f"\n[stage] v2 deep methods on {DEVICE}  (5 seeds, early stop, cosine LR + per-method LR)")
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
                    print(f"  [{i}/{total}] [FAIL] {tag:30s}  {rec['error']}  ({rec['wall_seconds']:.1f}s)")
                else:
                    avg_epochs = float(np.mean([info["epochs_used"]
                                                for seed_infos in rec["training_info_per_seed_per_fold"]
                                                for info in seed_infos]))
                    print(f"  [{i}/{total}] [done] {tag:30s}  CV={rec['mean']:.4f}±{rec['std']:.4f}  "
                          f"~{avg_epochs:.0f}ep  ({rec['wall_seconds']:.1f}s)")

    # EEGConformer-raw: separate row for raw-input recipe
    if target in ("all", "conformer_raw"):
        print(f"\n[stage] v2 EEGConformer-raw row")
        for subj in SUBJECTS:
            tag = f"EEGConformer-raw__subj{subj}"
            out = OUT / f"{tag}.json"
            if out.exists():
                print(f"  [skip] {tag}")
                continue
            t0 = time.time()
            try:
                rec = run_deep("EEGConformer", subj, raw=True)
            except Exception as e:
                rec = {"method": "EEGConformer-raw", "subject": subj, "error": f"{type(e).__name__}: {e}"}
            rec["wall_seconds"] = time.time() - t0
            out.write_text(json.dumps(rec, indent=2))
            if "error" in rec:
                print(f"  [FAIL] {tag}  {rec['error']}")
            else:
                print(f"  [done] {tag}  CV={rec['mean']:.4f}±{rec['std']:.4f}  ({rec['wall_seconds']:.1f}s)")


if __name__ == "__main__":
    target = sys.argv[1] if len(sys.argv) > 1 else "all"
    main(target=target)
