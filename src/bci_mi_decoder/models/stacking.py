"""Stacking meta-learner.

Given ``K`` base pipelines fit under cross-validation, this module computes
out-of-fold class probabilities, trains a shallow meta-classifier (by default
an L2-regularised logistic regression) on the stacked ``(n_train, K)``
feature matrix, and returns final predictions on the held-out test set.

This is the classic stacking recipe of Wolpert (1992); the use of
out-of-fold predictions prevents information leakage from the base learners'
training splits into the meta-learner.

References
----------
Wolpert, D. H. (1992). *Stacked generalization.* Neural Networks, 5, 241–259.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, Sequence

import numpy as np
from sklearn.base import BaseEstimator, clone
from sklearn.linear_model import LogisticRegression

from bci_mi_decoder.cv import CVResult, cv_score, stratified_cv


def _positive_class_column(proba: np.ndarray) -> np.ndarray:
    """Return the probability of the positive class (index 1) as a 1D array."""
    return proba[:, 1]


@dataclass
class StackingMetaLearner:
    """Stacked ensemble over pre-specified base pipelines.

    The meta-learner is fit on out-of-fold positive-class probabilities from
    each base pipeline; its test-time input is the average of each base
    pipeline's per-fold test probabilities.

    Parameters
    ----------
    base_pipelines : sequence of (name, estimator) pairs
        Scikit-learn compatible estimators with ``predict_proba``.
    meta_estimator : BaseEstimator, optional
        Meta-classifier. Defaults to L2 logistic regression (``C=10``).
    n_splits : int
        Cross-validation folds used to obtain out-of-fold predictions.
    random_state : int
        Seed for reproducibility.
    """

    base_pipelines: Sequence[tuple[str, BaseEstimator]]
    meta_estimator: BaseEstimator | None = None
    n_splits: int = 5
    random_state: int = 42

    def __post_init__(self) -> None:
        if self.meta_estimator is None:
            self.meta_estimator = LogisticRegression(C=10.0, max_iter=1000)

    def fit_transform(
        self,
        X_train: np.ndarray,
        y_train: np.ndarray,
        X_test: np.ndarray,
    ) -> dict:
        """Fit base + meta learners and return all quantities for reporting.

        Returns a dictionary with the following keys:

        * ``base_cvs`` — list of :class:`~bci_mi_decoder.cv.CVResult` per base.
        * ``oof_features`` — meta-feature matrix, shape ``(n_train, K)``.
        * ``test_features`` — averaged test meta-features, shape ``(n_test, K)``.
        * ``meta_cv_accuracy`` — 5-fold CV accuracy of the meta-learner on OOF.
        * ``test_proba`` — final predicted probabilities on the test set.
        * ``test_pred`` — final predicted integer labels on the test set.
        """
        # 1. Get OOF + test probabilities from every base.
        base_cvs: list[CVResult] = []
        oof_cols: list[np.ndarray] = []
        test_cols: list[np.ndarray] = []
        for _, est in self.base_pipelines:
            result = cv_score(
                est,
                X_train,
                y_train,
                X_test,
                n_splits=self.n_splits,
                random_state=self.random_state,
            )
            base_cvs.append(result)
            oof_cols.append(_positive_class_column(result.oof_proba))
            test_cols.append(_positive_class_column(result.averaged_test_proba))

        oof_features = np.column_stack(oof_cols)
        test_features = np.column_stack(test_cols)

        # 2. CV of the meta-learner on OOF features.
        skf = stratified_cv(self.n_splits, self.random_state)
        meta_accs: list[float] = []
        for train_idx, val_idx in skf.split(oof_features, y_train):
            meta = clone(self.meta_estimator)
            meta.fit(oof_features[train_idx], y_train[train_idx])
            meta_accs.append(
                float(meta.score(oof_features[val_idx], y_train[val_idx]))
            )
        meta_cv_accuracy = float(np.mean(meta_accs))

        # 3. Final fit on all OOF rows; predict test.
        meta_final = clone(self.meta_estimator)
        meta_final.fit(oof_features, y_train)
        test_proba = meta_final.predict_proba(test_features)
        test_pred = np.argmax(test_proba, axis=1)

        return {
            "base_cvs": base_cvs,
            "oof_features": oof_features,
            "test_features": test_features,
            "meta_cv_accuracy": meta_cv_accuracy,
            "meta_fold_accuracies": meta_accs,
            "test_proba": test_proba,
            "test_pred": test_pred,
        }
