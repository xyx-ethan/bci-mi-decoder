"""Per-subject adaptive ensemble for binary motor imagery EEG classification."""

__version__ = "0.1.0"

from bci_mi_decoder.data import load_subject, SubjectData
from bci_mi_decoder.preprocessing import bandpass, standardize
from bci_mi_decoder.cv import stratified_cv, cv_score

__all__ = [
    "__version__",
    "load_subject",
    "SubjectData",
    "bandpass",
    "standardize",
    "stratified_cv",
    "cv_score",
]
