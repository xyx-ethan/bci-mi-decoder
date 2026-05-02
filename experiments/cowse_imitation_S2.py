"""COWSE-style heterogeneous stacking experiment on Subject 2 (subject_B).

Compliance:
  - Single fixed StratifiedKFold(n_splits=5, shuffle=True, random_state=42)
  - Every base estimator and feature extractor is fit only on the
    training split of each fold; out-of-fold (OOF) probabilities feed
    the meta-learner.
  - Meta-learner CV is computed with the same folds (Wolpert convention).
  - No test-set data is consulted at any point.

Bases (14):
  1-4   CSP(k=4) + SVM-RBF at  μ 8-13 / β 13-30 / broad 7-30 / low 6-14
  5-8   CSP(k=4) + LDA      at  same four bands
  9-12  pyRiemann TS + L2-LR at same four bands
  13    PSD log-power + LDA  (broad 6-30, 4 bands × 64 channels = 256 feats)
  14    Hjorth (act/mob/cmp) + LDA (broad 7-30, 192 feats)

Meta-learners compared:
  A) L2-Logistic Regression (C=10) on the (140, 14) OOF probability matrix
  B) Simple unweighted average of OOF probabilities
  C) COWSE-style diversity-weighted average:
        w_i ∝ acc_i / (1 + mean_corr_i)
     where mean_corr_i is the average error-vector correlation between
     base i and the other 13 bases. Bases that make independent errors
     and that are individually accurate get higher weight.
"""
from __future__ import annotations

import sys
import warnings
from pathlib import Path

import numpy as np
from scipy.signal import welch
from sklearn.discriminant_analysis import LinearDiscriminantAnalysis
from sklearn.linear_model import LogisticRegression
from sklearn.model_selection import StratifiedKFold

warnings.filterwarnings("ignore")

REPO = Path(r"C:\Users\manxw\Downloads\BCI -- ISLA2026\bci-mi-decoder-clone")
sys.path.insert(0, str(REPO / "src"))

from bci_mi_decoder.models.csp_svm import make_csp_lda, make_csp_svm
from bci_mi_decoder.models.pyriemann_ts import make_tangent_space_lr
from bci_mi_decoder.preprocessing import bandpass, crop, standardize

DATA = Path(r"C:\Users\manxw\Downloads\BCI -- ISLA2026\项目进展\2026-04-18-2041-下载BCI数据集\data")

CROP = (384, 1537)        # 2.25 s window cue-relative
SFREQ = 512.0
N_SPLITS = 5
RANDOM_STATE = 42


def preprocess(X: np.ndarray, lo: float, hi: float) -> np.ndarray:
    """crop -> bandpass IIR -> per-trial z-score (per channel)."""
    return standardize(bandpass(crop(X, *CROP), lo, hi, sfreq=SFREQ))


def psd_features(X: np.ndarray) -> np.ndarray:
    """Log band-power per (trial, channel) over 4 MI-relevant sub-bands."""
    f, Pxx = welch(X, fs=SFREQ, nperseg=256, axis=-1)
    feats = []
    for lo, hi in [(4, 8), (8, 13), (13, 20), (20, 30)]:
        mask = (f >= lo) & (f < hi)
        feats.append(Pxx[..., mask].mean(axis=-1))   # (n, ch)
    F = np.concatenate(feats, axis=-1)               # (n, 4*ch)
    return np.log10(F + 1e-12)


def hjorth_features(X: np.ndarray) -> np.ndarray:
    """Hjorth activity / mobility / complexity per (trial, channel)."""
    dx = np.diff(X, axis=-1)
    ddx = np.diff(dx, axis=-1)
    var0 = X.var(axis=-1)
    var1 = dx.var(axis=-1)
    var2 = ddx.var(axis=-1)
    activity = var0
    mobility = np.sqrt(var1 / (var0 + 1e-12))
    complexity = np.sqrt(var2 / (var1 + 1e-12)) / (mobility + 1e-12)
    return np.concatenate([activity, mobility, complexity], axis=-1)  # (n, 3*ch)


# ---------- base specs --------------------------------------------------
BANDS = {
    "mu":    (8, 13),
    "beta":  (13, 30),
    "broad": (7, 30),
    "low":   (6, 14),
}

# (name, type, band_key)
BASES = [
    # CSP + SVM-RBF
    ("csp_svm_mu",        "csp_svm", "mu"),
    ("csp_svm_beta",      "csp_svm", "beta"),
    ("csp_svm_broad",     "csp_svm", "broad"),
    ("csp_svm_low",       "csp_svm", "low"),
    # CSP + LDA
    ("csp_lda_mu",        "csp_lda", "mu"),
    ("csp_lda_beta",      "csp_lda", "beta"),
    ("csp_lda_broad",     "csp_lda", "broad"),
    ("csp_lda_low",       "csp_lda", "low"),
    # pyRiemann TS + LR
    ("riem_ts_mu",        "riem_ts", "mu"),
    ("riem_ts_beta",      "riem_ts", "beta"),
    ("riem_ts_broad",     "riem_ts", "broad"),
    ("riem_ts_low",       "riem_ts", "low"),
    # PSD + LDA  (broadband)
    ("psd_lda_broad",     "psd_lda", "broad"),
    # Hjorth + LDA  (broadband)
    ("hjorth_lda_broad",  "hjorth_lda", "broad"),
]


def run_base(name: str, kind: str, band_key: str,
             X: np.ndarray, y: np.ndarray, skf: StratifiedKFold) -> tuple[np.ndarray, np.ndarray]:
    """Return OOF probabilities and OOF predictions for one base."""
    lo, hi = BANDS[band_key]
    Xb = preprocess(X, lo, hi)
    n = len(y)
    proba = np.zeros(n, dtype=np.float64)
    pred  = np.zeros(n, dtype=np.int64)
    for tr, va in skf.split(Xb, y):
        if kind == "csp_svm":
            clf = make_csp_svm(n_components=4, kernel="rbf")
            clf.fit(Xb[tr], y[tr])
            proba[va] = clf.predict_proba(Xb[va])[:, 1]
            pred[va]  = clf.predict(Xb[va])
        elif kind == "csp_lda":
            clf = make_csp_lda(n_components=4)
            clf.fit(Xb[tr], y[tr])
            proba[va] = clf.predict_proba(Xb[va])[:, 1]
            pred[va]  = clf.predict(Xb[va])
        elif kind == "riem_ts":
            clf = make_tangent_space_lr()
            clf.fit(Xb[tr], y[tr])
            proba[va] = clf.predict_proba(Xb[va])[:, 1]
            pred[va]  = clf.predict(Xb[va])
        elif kind == "psd_lda":
            Ftr = psd_features(Xb[tr])
            Fva = psd_features(Xb[va])
            clf = LinearDiscriminantAnalysis()
            clf.fit(Ftr, y[tr])
            proba[va] = clf.predict_proba(Fva)[:, 1]
            pred[va]  = clf.predict(Fva)
        elif kind == "hjorth_lda":
            Ftr = hjorth_features(Xb[tr])
            Fva = hjorth_features(Xb[va])
            clf = LinearDiscriminantAnalysis()
            clf.fit(Ftr, y[tr])
            proba[va] = clf.predict_proba(Fva)[:, 1]
            pred[va]  = clf.predict(Fva)
        else:
            raise ValueError(f"unknown kind {kind}")
    return proba, pred


def safe_corr(a: np.ndarray, b: np.ndarray) -> float:
    if a.std() < 1e-9 or b.std() < 1e-9:
        return 0.0
    c = np.corrcoef(a, b)[0, 1]
    return float(np.nan_to_num(c))


# ---------- main --------------------------------------------------------
def main() -> None:
    print("=" * 76)
    print("  COWSE-imitation heterogeneous stacking — Subject 2 (subject_B)")
    print("=" * 76)

    X = np.load(DATA / "subject_B_X_train.npy").astype(np.float64)
    y_raw = np.load(DATA / "subject_B_y_train.npy", allow_pickle=True)
    y = np.asarray([0 if str(v) == "left_hand" else 1 for v in y_raw], dtype=np.int64)
    print(f"  Subject 2  : X_train {X.shape}, y_train balanced "
          f"(left={int((y==0).sum())} / right={int((y==1).sum())})")
    print(f"  Window     : samples {CROP[0]}–{CROP[1]}  (2.25 s @ 512 Hz)")
    print(f"  Folds      : StratifiedKFold(n_splits={N_SPLITS}, shuffle=True, random_state={RANDOM_STATE})")
    print()

    skf = StratifiedKFold(n_splits=N_SPLITS, shuffle=True, random_state=RANDOM_STATE)

    OOF_PROB = np.zeros((len(BASES), len(y)), dtype=np.float64)
    OOF_PRED = np.zeros((len(BASES), len(y)), dtype=np.int64)
    base_names = []
    print(f"  {'#':>2}  {'base':30s}  {'CV acc':>8s}")
    for i, (name, kind, band_key) in enumerate(BASES):
        proba, pred = run_base(name, kind, band_key, X, y, skf)
        OOF_PROB[i] = proba
        OOF_PRED[i] = pred
        base_acc = (pred == y).mean()
        base_names.append(name)
        print(f"  {i+1:>2}  {name:30s}  {base_acc:8.4f}")

    base_accs = (OOF_PRED == y[None, :]).mean(axis=1)
    best_idx = int(np.argmax(base_accs))
    print()
    print(f"  Best single base : {base_names[best_idx]}  CV {base_accs[best_idx]:.4f}")
    print(f"  Median base      : CV {np.median(base_accs):.4f}")
    print(f"  Worst base       : CV {base_accs.min():.4f}")
    print()

    # ---- Meta A: L2-LR on (140, 14) OOF probability matrix ------------
    Z = OOF_PROB.T   # (140, 14)
    meta_pred = np.zeros_like(y)
    for tr, va in skf.split(Z, y):
        meta = LogisticRegression(C=10.0, max_iter=2000)
        meta.fit(Z[tr], y[tr])
        meta_pred[va] = meta.predict(Z[va])
    l2lr_acc = (meta_pred == y).mean()

    # ---- Meta B: simple unweighted average ----------------------------
    avg_proba = OOF_PROB.mean(axis=0)
    avg_pred = (avg_proba > 0.5).astype(int)
    avg_acc = (avg_pred == y).mean()

    # ---- Meta C: COWSE-style diversity-weighted -----------------------
    # error vector per base, pairwise correlation, mean off-diagonal corr
    err = (OOF_PRED != y[None, :]).astype(np.float64)
    n_b = len(BASES)
    R = np.zeros((n_b, n_b))
    for i in range(n_b):
        for j in range(n_b):
            if i == j:
                continue
            R[i, j] = safe_corr(err[i], err[j])
    mean_corr = R.sum(axis=1) / (n_b - 1)
    # weight: high acc + low mean correlation = high weight (clip negatives)
    raw_w = np.maximum(base_accs - 0.5, 1e-3) / (1.0 + np.maximum(mean_corr, 0.0))
    weights = raw_w / raw_w.sum()
    cowse_proba = (weights[:, None] * OOF_PROB).sum(axis=0)
    cowse_pred = (cowse_proba > 0.5).astype(int)
    cowse_acc = (cowse_pred == y).mean()

    print(f"  {'meta strategy':40s}  {'CV acc':>8s}  Δ vs best base")
    print(f"  {'-'*40}  {'-'*8}  {'-'*15}")
    print(f"  {'A) L2-LR on OOF prob matrix':40s}  {l2lr_acc:8.4f}  "
          f"{l2lr_acc - base_accs[best_idx]:+.4f}")
    print(f"  {'B) Simple unweighted average':40s}  {avg_acc:8.4f}  "
          f"{avg_acc - base_accs[best_idx]:+.4f}")
    print(f"  {'C) COWSE-style diversity-weighted':40s}  {cowse_acc:8.4f}  "
          f"{cowse_acc - base_accs[best_idx]:+.4f}")
    print()

    # ---- COWSE weight inspection --------------------------------------
    order = np.argsort(weights)[::-1]
    print(f"  COWSE-style weights (top → bottom):")
    print(f"    {'#':>2}  {'base':30s}  {'acc':>6s}  {'mean_corr':>9s}  {'weight':>8s}")
    for r, i in enumerate(order):
        print(f"    {r+1:>2}  {base_names[i]:30s}  "
              f"{base_accs[i]:6.4f}  {mean_corr[i]:9.4f}  {weights[i]:8.4f}")

    print()
    print("=" * 76)
    print("  Reference reminders (compliance + interpretation):")
    print("=" * 76)
    print("  - Currently submitted Subject 2 model: EEGNet (augmented), CV 0.8786.")
    print("    EEGNet is intentionally NOT included as a base here because the")
    print("    EEGNet sweep was performed offline; this run is a 14-base classical-")
    print("    feature heterogeneous stack only.")
    print("  - All values above are SELECTION-CV (5-fold OOF). They are biased")
    print("    optimistically because the same folds are used to compare bases")
    print("    and metas. The held-out test set is not consulted.")
    print("  - For a fair comparison to the submitted 0.8786, treat the meta CV")
    print("    here as the upper bound of what 14 classical bases without EEGNet")
    print("    could deliver under the same protocol.")
    print()


if __name__ == "__main__":
    main()
