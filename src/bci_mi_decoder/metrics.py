"""Evaluation metrics used for reporting."""
from __future__ import annotations

import math

import numpy as np


def accuracy(y_true: np.ndarray, y_pred: np.ndarray) -> float:
    """Plain accuracy (fraction of correctly classified trials)."""
    y_true = np.asarray(y_true)
    y_pred = np.asarray(y_pred)
    if y_true.shape != y_pred.shape:
        raise ValueError(
            f"shape mismatch: y_true {y_true.shape} vs y_pred {y_pred.shape}"
        )
    return float((y_true == y_pred).mean())


def binomial_95ci(n_correct: int, n_total: int) -> tuple[float, float]:
    """Wilson score 95 % confidence interval for a binomial proportion.

    Preferable to the naïve normal-approximation interval for small samples
    or probabilities near 0/1, and well-suited to reporting held-out test
    accuracy with n=360.
    """
    if n_total == 0:
        return 0.0, 0.0
    z = 1.959963984540054  # 97.5th percentile of standard normal
    phat = n_correct / n_total
    denom = 1.0 + z * z / n_total
    centre = (phat + z * z / (2 * n_total)) / denom
    half = (
        z
        * math.sqrt((phat * (1 - phat) + z * z / (4 * n_total)) / n_total)
        / denom
    )
    return centre - half, centre + half
