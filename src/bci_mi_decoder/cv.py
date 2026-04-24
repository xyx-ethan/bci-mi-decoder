"""Deterministic stratified cross-validation utilities."""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

import numpy as np
from sklearn.base import clone, BaseEstimator
from sklearn.model_selection import StratifiedKFold

DEFAULT_N_SPLITS = 5
DEFAULT_RANDOM_STATE = 42


def stratified_cv(
    n_splits: int = DEFAULT_N_SPLITS,
    random_state: int = DEFAULT_RANDOM_STATE,
) -> StratifiedKFold:
    """Return a reproducibly-shuffled stratified k-fold splitter."""
    return StratifiedKFold(
        n_splits=n_splits,
        shuffle=True,
        random_state=random_state,
    )


@dataclass(frozen=True)
class CVResult:
    """Summary of a single cross-validation run."""
    mean_accuracy: float
    std_accuracy: float
    fold_accuracies: list[float]
    oof_proba: np.ndarray  # shape (n_train, n_classes)
    averaged_test_proba: np.ndarray  # shape (n_test, n_classes)


def cv_score(
    estimator: BaseEstimator,
    X_train: np.ndarray,
    y_train: np.ndarray,
    X_test: np.ndarray,
    n_splits: int = DEFAULT_N_SPLITS,
    random_state: int = DEFAULT_RANDOM_STATE,
) -> CVResult:
    """Run stratified k-fold CV; return OOF probabilities and averaged test probabilities.

    The estimator is cloned per fold. Out-of-fold probabilities are produced
    for the training set (so they can be used as meta-features for stacking).
    For the test set, each fold's predictions are stored and averaged.

    Parameters
    ----------
    estimator : scikit-learn compatible estimator
        Must implement ``fit`` and ``predict_proba``.
    X_train, y_train : np.ndarray
        Training features and integer labels.
    X_test : np.ndarray
        Held-out test features.
    n_splits : int
        Number of CV folds (default 5).
    random_state : int
        Reproducibility seed (default 42).

    Returns
    -------
    CVResult
    """
    skf = stratified_cv(n_splits=n_splits, random_state=random_state)
    n_classes = int(np.max(y_train)) + 1
    oof = np.zeros((len(y_train), n_classes), dtype=np.float64)
    fold_accs: list[float] = []
    test_probas: list[np.ndarray] = []

    for train_idx, val_idx in skf.split(X_train, y_train):
        est = clone(estimator)
        est.fit(X_train[train_idx], y_train[train_idx])
        oof[val_idx] = est.predict_proba(X_train[val_idx])
        fold_accs.append(float(est.score(X_train[val_idx], y_train[val_idx])))
        test_probas.append(est.predict_proba(X_test))

    return CVResult(
        mean_accuracy=float(np.mean(fold_accs)),
        std_accuracy=float(np.std(fold_accs)),
        fold_accuracies=fold_accs,
        oof_proba=oof,
        averaged_test_proba=np.mean(test_probas, axis=0),
    )
