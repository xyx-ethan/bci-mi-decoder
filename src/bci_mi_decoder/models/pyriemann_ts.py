"""Riemannian tangent-space pipelines.

Spatial covariance matrices lie on the manifold of symmetric positive-definite
matrices. Mapping them to the tangent space at the Riemannian mean linearises
the problem so that a standard Euclidean classifier (here, L2 logistic
regression) can be applied.

References
----------
Barachant, A., Bonnet, S., Congedo, M., & Jutten, C. (2012).
    *Multiclass brain-computer interface classification by Riemannian geometry.*
    IEEE Trans. Biomed. Eng., 59, 920–928.
Barachant, A., Bonnet, S., Congedo, M., & Jutten, C. (2013).
    *Classification of covariance matrices using a Riemannian-based kernel for BCI.*
    Neurocomputing, 112, 172–178.
"""
from __future__ import annotations

from pyriemann.estimation import Covariances
from pyriemann.tangentspace import TangentSpace
from sklearn.linear_model import LogisticRegression
from sklearn.pipeline import Pipeline


def make_tangent_space_lr(
    cov_estimator: str = "oas",
    metric: str = "riemann",
    C: float = 1.0,
    max_iter: int = 1000,
    class_weight: str | None = "balanced",
) -> Pipeline:
    """Covariances(OAS) → TangentSpace(metric) → LogisticRegression.

    Parameters
    ----------
    cov_estimator : str
        Covariance estimator forwarded to :class:`pyriemann.estimation.Covariances`.
        ``"oas"`` (Oracle Approximating Shrinkage) is the default.
    metric : str
        Riemannian metric for the tangent-space mapping. The default
        ``"riemann"`` is the affine-invariant metric.
    C : float
        L2 regularisation of the logistic regression.
    max_iter : int
        LBFGS iterations for logistic regression.
    class_weight : str or None
        Passed through to :class:`sklearn.linear_model.LogisticRegression`.
    """
    return Pipeline(
        steps=[
            ("cov", Covariances(estimator=cov_estimator)),
            ("ts", TangentSpace(metric=metric)),
            (
                "lr",
                LogisticRegression(
                    C=C,
                    max_iter=max_iter,
                    class_weight=class_weight,
                ),
            ),
        ]
    )
