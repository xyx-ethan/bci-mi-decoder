"""Per-subject data loading.

Expected on-disk layout under ``data_dir``::

    SUB1_X_train.npy     # (n_train, n_channels, n_samples)
    SUB1_y_train.npy     # (n_train,) strings: "left_hand" | "right_hand"
    SUB1_X_test.npy      # (n_test,  n_channels, n_samples)
    SUB2_X_train.npy
    ...

Labels are strings at rest; they are encoded to integers (``0`` = ``left_hand``,
``1`` = ``right_hand``) at load time.
"""
from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Sequence

import numpy as np

LABEL_TO_INT = {"left_hand": 0, "right_hand": 1}
INT_TO_LABEL = {v: k for k, v in LABEL_TO_INT.items()}


@dataclass(frozen=True)
class SubjectData:
    """Loaded single-subject EEG data.

    Attributes
    ----------
    subject_id : str
        Subject identifier, e.g. ``"SUB1"``.
    X_train : np.ndarray
        Training trials, shape ``(n_train, n_channels, n_samples)``, ``float64``.
    y_train : np.ndarray
        Integer labels for training trials, shape ``(n_train,)``, ``int64``.
    X_test : np.ndarray
        Test trials, shape ``(n_test, n_channels, n_samples)``, ``float64``.
    """

    subject_id: str
    X_train: np.ndarray
    y_train: np.ndarray
    X_test: np.ndarray

    @property
    def n_channels(self) -> int:
        return int(self.X_train.shape[1])

    @property
    def n_samples(self) -> int:
        return int(self.X_train.shape[2])


def _encode_labels(y_raw: np.ndarray) -> np.ndarray:
    """Convert object/str labels to int64 class indices."""
    try:
        return np.fromiter((LABEL_TO_INT[str(v)] for v in y_raw), dtype=np.int64)
    except KeyError as e:  # pragma: no cover - configuration error
        raise ValueError(
            f"Unknown class label: {e.args[0]!r}. Expected one of "
            f"{sorted(LABEL_TO_INT)}."
        )


def load_subject(subject_id: str, data_dir: str | Path) -> SubjectData:
    """Load the train/test arrays for a single subject.

    Parameters
    ----------
    subject_id : str
        Subject key, e.g. ``"SUB1"`` ... ``"SUB6"``.
    data_dir : str or Path
        Directory containing ``{subject_id}_X_train.npy``,
        ``{subject_id}_y_train.npy``, and ``{subject_id}_X_test.npy``.

    Returns
    -------
    SubjectData
    """
    data_dir = Path(data_dir)
    X_train = np.load(data_dir / f"{subject_id}_X_train.npy").astype(np.float64)
    y_raw = np.load(data_dir / f"{subject_id}_y_train.npy", allow_pickle=True)
    X_test = np.load(data_dir / f"{subject_id}_X_test.npy").astype(np.float64)
    y_train = _encode_labels(np.asarray(y_raw))

    if X_train.shape[0] != y_train.shape[0]:
        raise ValueError(
            f"{subject_id}: X_train has {X_train.shape[0]} trials but "
            f"y_train has {y_train.shape[0]}."
        )
    return SubjectData(
        subject_id=subject_id,
        X_train=X_train,
        y_train=y_train,
        X_test=X_test,
    )


def load_all_subjects(
    data_dir: str | Path, subject_ids: Sequence[str] | None = None
) -> dict[str, SubjectData]:
    """Load every subject found under ``data_dir`` (or a provided subset)."""
    if subject_ids is None:
        subject_ids = [f"SUB{i}" for i in range(1, 7)]
    return {sid: load_subject(sid, data_dir) for sid in subject_ids}
