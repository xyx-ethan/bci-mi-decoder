"""Test-time window augmentation.

At prediction time we may apply a single, CV-selected pipeline to several
overlapping time windows of the same trial and average the resulting
probabilities. The augmentation is *train-time-derived*: each window
defines an independent classifier trained with that same window on the
training fold; no information about held-out labels is ever consumed.

This helps whenever the relevant event-related (de-)synchronisation is
distributed over a period longer than the default single window, or when
the cue-onset jitter is non-trivial.
"""
from __future__ import annotations

from typing import Sequence

import numpy as np
from sklearn.base import BaseEstimator, clone

from bci_mi_decoder.cv import cv_score
from bci_mi_decoder.preprocessing import bandpass, crop, standardize


def test_time_window_average(
    estimator: BaseEstimator,
    X_train_full: np.ndarray,
    y_train: np.ndarray,
    X_test_full: np.ndarray,
    windows: Sequence[tuple[int, int]],
    band: tuple[float, float] | None = None,
    sfreq: float = 512.0,
    n_splits: int = 5,
    random_state: int = 42,
) -> dict:
    """Train & test one estimator per time window, then average test probas.

    Parameters
    ----------
    estimator : scikit-learn compatible estimator
        The per-window pipeline (e.g. :func:`~bci_mi_decoder.models.pyriemann_ts.make_tangent_space_lr`).
    X_train_full, X_test_full : np.ndarray
        Un-cropped trials, shape ``(n, n_channels, n_full_samples)``.
    y_train : np.ndarray
        Integer labels.
    windows : sequence of (start, stop)
        Sample indices for each window. At least one window must be supplied.
    band : (float, float) or None
        Optional IIR band-pass, applied after cropping.
    sfreq : float
        Sampling frequency for the band-pass filter.
    n_splits, random_state : int
        Passed through to :func:`cv_score`.

    Returns
    -------
    dict
        Keys: ``per_window`` (list of cv results with accuracy and test proba),
        ``best_window_name``, ``best_window_cv``, ``averaged_test_proba``,
        ``cv_weighted_test_proba``.
    """
    if len(windows) == 0:
        raise ValueError("Must supply at least one window.")

    per_window = []
    for start, stop in windows:
        Xtr = crop(X_train_full, start, stop)
        Xte = crop(X_test_full, start, stop)
        if band is not None:
            Xtr = bandpass(Xtr, band[0], band[1], sfreq=sfreq)
            Xte = bandpass(Xte, band[0], band[1], sfreq=sfreq)
        Xtr = standardize(Xtr)
        Xte = standardize(Xte)
        result = cv_score(
            clone(estimator), Xtr, y_train, Xte,
            n_splits=n_splits, random_state=random_state,
        )
        per_window.append({
            "window": (start, stop),
            "cv_mean": result.mean_accuracy,
            "cv_std": result.std_accuracy,
            "test_proba": result.averaged_test_proba,
        })

    cvs = np.array([r["cv_mean"] for r in per_window])
    probas = np.stack([r["test_proba"] for r in per_window], axis=0)
    averaged = probas.mean(axis=0)
    weights = cvs / cvs.sum()
    cv_weighted = np.einsum("i,ijk->jk", weights, probas)

    best_idx = int(np.argmax(cvs))
    return {
        "per_window": per_window,
        "best_window_name": f"{per_window[best_idx]['window'][0]}-{per_window[best_idx]['window'][1]}",
        "best_window_cv": float(cvs[best_idx]),
        "averaged_test_proba": averaged,
        "cv_weighted_test_proba": cv_weighted,
    }
