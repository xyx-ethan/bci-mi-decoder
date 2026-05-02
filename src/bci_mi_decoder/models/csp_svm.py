"""CSP-based pipelines.

Common Spatial Patterns (Ramoser et al., 2000; Blankertz et al., 2008) are
fit with Ledoit–Wolf shrinkage of the class covariance matrices. Log-variance
of the CSP-projected time series is then classified with a support vector
machine or linear discriminant analysis.

References
----------
Ramoser, H., Müller-Gerking, J., & Pfurtscheller, G. (2000). IEEE Trans. Rehabil. Eng., 8, 441–446.
Blankertz, B., et al. (2008). IEEE Signal Process. Mag., 25, 41–56.
"""
from __future__ import annotations

from sklearn.discriminant_analysis import LinearDiscriminantAnalysis
from sklearn.pipeline import Pipeline
from sklearn.svm import SVC

from mne.decoding import CSP


def make_csp_svm(
    n_components: int = 4,
    kernel: str = "rbf",
    C: float = 1.0,
    reg: str = "ledoit_wolf",
) -> Pipeline:
    """CSP → log-variance features → SVM.

    Parameters
    ----------
    n_components : int
        Number of CSP components to retain.
    kernel : {"rbf", "linear"}
        SVM kernel type.
    C : float
        SVM regularisation.
    reg : str
        Covariance regulariser passed to :class:`mne.decoding.CSP`.
    """
    return Pipeline(
        steps=[
            ("csp", CSP(n_components=n_components, log=True, reg=reg)),
            (
                "svm",
                SVC(
                    kernel=kernel,
                    probability=True,
                    C=C,
                    gamma="scale",
                    random_state=42,  # Platt-scaling internal CV is non-deterministic without this
                ),
            ),
        ]
    )


def make_csp_lda(
    n_components: int = 4,
    reg: str = "ledoit_wolf",
) -> Pipeline:
    """CSP → log-variance features → Linear Discriminant Analysis."""
    return Pipeline(
        steps=[
            ("csp", CSP(n_components=n_components, log=True, reg=reg)),
            ("lda", LinearDiscriminantAnalysis()),
        ]
    )
