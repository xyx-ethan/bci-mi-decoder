"""Smoke tests for the pipeline components, on small synthetic data."""
from __future__ import annotations

import numpy as np
import pytest

from bci_mi_decoder.cv import cv_score, stratified_cv
from bci_mi_decoder.metrics import accuracy, binomial_95ci
from bci_mi_decoder.models.csp_svm import make_csp_svm, make_csp_lda
from bci_mi_decoder.models.pyriemann_ts import make_tangent_space_lr
from bci_mi_decoder.preprocessing import bandpass, crop, standardize


def _make_synth(n_per_class: int = 30, n_channels: int = 8, n_samples: int = 256,
                seed: int = 0):
    """Two-class synthetic EEG with clearly separable power topographies."""
    rng = np.random.default_rng(seed)
    t = np.arange(n_samples) / 100.0
    left = np.stack([
        rng.normal(scale=0.1, size=(n_channels, n_samples))
        + (np.sin(2 * np.pi * 10 * t) *
           (np.arange(n_channels)[:, None] < n_channels // 2)) * 0.5
        for _ in range(n_per_class)
    ])
    right = np.stack([
        rng.normal(scale=0.1, size=(n_channels, n_samples))
        + (np.sin(2 * np.pi * 10 * t) *
           (np.arange(n_channels)[:, None] >= n_channels // 2)) * 0.5
        for _ in range(n_per_class)
    ])
    X = np.concatenate([left, right], axis=0)
    y = np.array([0] * n_per_class + [1] * n_per_class, dtype=np.int64)
    return X, y


def test_crop_and_standardize_shapes():
    X, _ = _make_synth()
    cropped = crop(X, 10, 200)
    assert cropped.shape == (X.shape[0], X.shape[1], 190)
    std = standardize(cropped)
    assert std.shape == cropped.shape
    assert np.allclose(std.mean(axis=-1), 0, atol=1e-6)


def test_csp_svm_synthetic():
    X, y = _make_synth()
    X_test, _ = _make_synth(seed=1)
    pipe = make_csp_svm(n_components=2)
    cv = cv_score(pipe, X, y, X_test, n_splits=3, random_state=0)
    assert cv.mean_accuracy > 0.8


def test_tangent_space_synthetic():
    X, y = _make_synth()
    X_test, _ = _make_synth(seed=1)
    pipe = make_tangent_space_lr()
    cv = cv_score(pipe, X, y, X_test, n_splits=3, random_state=0)
    assert cv.mean_accuracy > 0.8


def test_csp_lda_synthetic():
    X, y = _make_synth()
    X_test, _ = _make_synth(seed=1)
    pipe = make_csp_lda(n_components=2)
    cv = cv_score(pipe, X, y, X_test, n_splits=3, random_state=0)
    assert cv.mean_accuracy > 0.8


def test_accuracy_and_ci():
    y_true = np.array([0, 1, 0, 1, 0, 1, 0, 1, 0, 1])
    y_pred = np.array([0, 1, 0, 0, 0, 1, 0, 1, 0, 1])
    assert accuracy(y_true, y_pred) == pytest.approx(0.9)
    low, high = binomial_95ci(9, 10)
    assert 0.5 < low < 0.9
    assert 0.9 <= high <= 1.0


def test_stratified_cv_determinism():
    _, y = _make_synth()
    skf_a = stratified_cv(n_splits=3, random_state=0)
    skf_b = stratified_cv(n_splits=3, random_state=0)
    folds_a = [tuple(v.tolist()) for _, v in skf_a.split(np.zeros_like(y), y)]
    folds_b = [tuple(v.tolist()) for _, v in skf_b.split(np.zeros_like(y), y)]
    assert folds_a == folds_b
