"""Candidate model families for per-subject pipeline selection."""

from bci_mi_decoder.models.csp_svm import make_csp_svm, make_csp_lda
from bci_mi_decoder.models.pyriemann_ts import make_tangent_space_lr
from bci_mi_decoder.models.stacking import StackingMetaLearner
from bci_mi_decoder.models.tta import test_time_window_average

__all__ = [
    "make_csp_svm",
    "make_csp_lda",
    "make_tangent_space_lr",
    "StackingMetaLearner",
    "test_time_window_average",
]
