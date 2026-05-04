---
title: 'bci-mi-decoder: A reproducible per-subject adaptive ensemble for binary motor-imagery EEG decoding under strict cross-validation'
tags:
  - Python
  - EEG
  - brain-computer interface
  - motor imagery
  - cross-validation
  - reproducibility
authors:
  - name: Yuxuan (Ethan) Xu
    orcid: 0000-0000-0000-0000
    affiliation: 1
affiliations:
  - name: Independent Researcher
    index: 1
date: 28 April 2026
bibliography: paper.bib
---

# Summary

`bci-mi-decoder` is an open-source Python package for binary motor-imagery
(MI) decoding from scalp electroencephalography (EEG). Given a per-subject
training set of single-trial EEG epochs, it enumerates a small,
pre-specified set of candidate pipelines — narrow-band Common Spatial
Pattern (CSP) classifiers [@ramoser:2000; @blankertz:2008], Riemannian
tangent-space classifiers [@barachant:2012; @barachant:2013], compact
convolutional networks [@lawhern:2018], and out-of-fold stacking
meta-learners [@wolpert:1992] — selects the highest-cross-validation
pipeline per subject under a single fixed
`StratifiedKFold(n_splits=5, shuffle=True, random_state=42)` partition,
and produces fold-bagged probabilistic predictions on a held-out test set
in a single command.

The package was developed during the BCI-ISLA 2026 motor-imagery
decoding challenge (Codabench competition 15044, organised at Inria);
the identical codepath shipped in release v0.1.0 of this repository
reached a held-out test accuracy of 0.93, tied for the highest
displayed test score among 114 participants on the development
leaderboard.

# Statement of need

Modern BCI research routinely combines sophisticated decoding pipelines
(deep neural networks, foundation models, transfer learning) with
permissive evaluation protocols. The combination is fragile: hyperparameters
tuned with repeated leaderboard probes can outperform a careful classical
baseline by margins that vanish on a held-out split, an effect documented
both in the model-selection literature [@cawley:2010] and in BCI-specific
reviews [@lotte:2018]. Practitioners in education, clinical pilots, and
graduate methods courses need a small, opinionated tool that:

- enforces fold-only fitting of every fold-dependent transform —
  covariance shrinkage, CSP filters, tangent-space reference means,
  scalers, classifier parameters;
- pre-specifies the candidate set before any test prediction is generated;
- documents every per-subject selection decision in a reproducible
  artefact (Markdown report plus JSON summary);
- delivers a strong baseline within the sample-efficient regime
  characteristic of motor-imagery BCI (typically 100–200 labelled
  trials per subject).

Existing toolkits address adjacent concerns but not this combination
directly. **MOABB** [@jayaram:2018] is a comprehensive benchmarking
framework spanning many datasets and pipelines, but is not opinionated
about per-subject adaptive selection or stacking topology under a fixed
single-fold split. **Braindecode** [@schirrmeister:2017] focuses on
end-to-end deep learning for EEG with extensive support for training
recipes, but provides minimal scaffolding for classical-versus-deep
candidate comparison under a single shared cross-validation protocol.
**MNE-Python** [@gramfort:2013] supplies the preprocessing utilities and
CSP implementation that this package wraps, and **pyRiemann**
[@barachant:2014] supplies the Riemannian-geometry classifiers used as
one of the candidate families. `bci-mi-decoder` fills the remaining gap by
providing a single end-to-end command that loads per-subject NumPy arrays,
sweeps the candidate set with shared folds, performs per-subject pipeline
selection (with optional stacking meta-learner), generates fold-bagged
test probabilities, and emits a labelled submission file alongside the
methodology and selection-decision artefacts.

# Functionality

The package exposes:

- `bci_mi_decoder.preprocessing`: cue-relative cropping, MNE-based
  zero-phase IIR band-pass filtering, per-trial channel-wise z-scoring;
- `bci_mi_decoder.cv`: a deterministic `StratifiedKFold` cross-validator
  and out-of-fold (OOF) probability collector;
- `bci_mi_decoder.models`: scikit-learn-compatible factories for CSP+SVM
  (RBF / linear), CSP+LDA, pyRiemann tangent-space + L2 logistic
  regression, an OOF stacking meta-learner with leakage-safe test-time
  aggregation, and window-based test-time augmentation;
- `bci_mi_decoder.metrics`: accuracy and Wilson confidence intervals;
- `scripts/train.py`: an end-to-end script that fits per-subject
  pipelines, generates fold-bagged test probabilities, and writes the
  submission file alongside `report.md` and `summary.json`.

A YAML configuration (`configs/default.yaml`) reproduces the per-subject
pipelines used in the validation challenge. A test suite (six tests,
runnable via `pytest tests/`) verifies the pipelines on synthetic data
without requiring access to the underlying challenge dataset.

# Compliance and limitations

Every fold-dependent transform is fit only on each fold's training split.
Test-time window choice is determined by training-fold cross-validation
only. The package author used zero leaderboard submissions during
development and one final evaluation submission. The cross-validation
score reported per subject is a model-selection score, not an unbiased
generalisation estimate; users are encouraged to interpret it accordingly
and to consult `docs/methodology.md` for the full leakage-control
checklist and an explicit Limitations section.

# Acknowledgements

The author thanks the BCI-ISLA 2026 challenge organiser
(Pedro L. C. Rodrigues, Inria) for hosting the public benchmark on which
this package was validated, and the maintainers of MNE-Python, pyRiemann,
and scikit-learn, on which the package directly depends.

# References
