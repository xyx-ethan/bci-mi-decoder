"""EEG pre-processing: time cropping, IIR band-pass, per-trial z-scoring.

All functions operate on arrays with shape ``(n_trials, n_channels, n_samples)``
unless noted otherwise.
"""
from __future__ import annotations

import numpy as np
from mne.filter import filter_data

DEFAULT_SFREQ = 512.0


def crop(X: np.ndarray, start: int, stop: int) -> np.ndarray:
    """Return ``X[..., start:stop]`` with a copy to avoid downstream aliasing."""
    return np.ascontiguousarray(X[..., start:stop])


def bandpass(
    X: np.ndarray,
    l_freq: float,
    h_freq: float,
    sfreq: float = DEFAULT_SFREQ,
    method: str = "iir",
) -> np.ndarray:
    """Zero-phase IIR band-pass filter via :func:`mne.filter.filter_data`.

    Parameters
    ----------
    X : np.ndarray
        Input trials, shape ``(n_trials, n_channels, n_samples)``. A copy is
        made so the input is not mutated.
    l_freq, h_freq : float
        Low and high corner frequencies in Hz.
    sfreq : float
        Sampling frequency in Hz. Defaults to 512 Hz.
    method : str
        Filter method passed through to MNE.

    Returns
    -------
    np.ndarray
        Filtered trials with the same shape as ``X``.
    """
    return filter_data(
        X.astype(np.float64, copy=True),
        sfreq=sfreq,
        l_freq=l_freq,
        h_freq=h_freq,
        method=method,
        verbose=False,
    )


def standardize(X: np.ndarray, axis: int = -1, eps: float = 1e-6) -> np.ndarray:
    """Z-score each trial along ``axis`` (time by default), channel-wise.

    The output has zero mean and unit variance per (trial, channel).
    """
    mu = X.mean(axis=axis, keepdims=True)
    sd = X.std(axis=axis, keepdims=True)
    return (X - mu) / (sd + eps)
