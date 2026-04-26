# Methodology

This note describes the full per-subject adaptive ensemble protocol used in
this repository. It is written to be self-contained; cross-references to the
reference list appear as inline citations.

## 1. Problem statement

Each subject provides 140 labelled EEG trials (training) and 60 unlabelled
trials (test) at 512 Hz and 64 channels, with two balanced classes
(left-hand vs. right-hand imagined movement). The goal is to output a
single predicted label per test trial.

## 2. Pre-processing

- **Sampling rate & montage.** 512 Hz, 64 channels (10–10 layout, as
  supplied). Channel order is consumed as-is from the supplied NumPy
  arrays.
- **Trial cropping.** Cue-relative windows: default 2.25 s (samples
  384–1537) for CSP and EEGNet pipelines; extended 2.5 s (samples
  256–1537) for the pyRiemann tangent-space pipelines and for
  Subjects 5 and 6 (see § 5 for the ablation motivating the wider
  window).
- **Band-pass.** Zero-phase IIR filter via
  ``mne.filter.filter_data(method="iir")`` with subject- and
  pipeline-specific cutoffs listed in Table 1 of the README.
  Applied independently per trial on the cropped window.
- **Per-trial z-score.** Mean and standard deviation are computed
  per trial × per channel along the time axis and used to standardise
  that trial.
- **Not applied.** No notch filter, no session-level re-referencing,
  no ICA, no manual artifact rejection. This keeps the protocol
  reproducible on any 64-channel EEG dataset without requiring trained
  analysts.
- **Class balance.** Binary labels are balanced within each subject
  (70 / 70 in training, 30 / 30 in test); chance accuracy is 0.5.

## 3. Candidate model families

Each candidate is a standard published pipeline evaluated with identical
cross-validation (§ 4).

### 3.1 CSP + SVM / LDA

Common Spatial Patterns (Ramoser et al., 2000; Blankertz et al., 2008)
maximise the ratio of class-conditional trial variances. Class covariances
are regularised with Ledoit–Wolf shrinkage (``mne.decoding.CSP(reg="ledoit_wolf")``);
the log-variance of the top *k* projected channels is fed to an SVM or LDA.

We sweep ``n_components ∈ {2, 4, 6, 8}`` and report the best by CV.

### 3.2 pyRiemann tangent-space + L2 logistic regression

Sample covariance matrices (Oracle Approximating Shrinkage estimator)
are projected to the tangent space at their Riemannian mean under the
affine-invariant metric, and classified with an L2 logistic regression
(Barachant et al., 2012, 2013). The pyRiemann ``TangentSpace`` is
configured with ``metric="riemann"`` and ``tsupdate=False``: the
reference mean is estimated only on training-fold data and is *not*
re-fit on the test covariance distribution at inference. This pipeline
is strong on subjects with clean, broadband EEG.

### 3.3 Filter-Bank CSP

FBCSP (Ang et al., 2012) computes CSP features in nine overlapping
sub-bands, performs mutual-information feature selection, and classifies
with LDA. Evaluated but rarely selected by CV on this dataset.

### 3.4 EEGNet with strong augmentation

EEGNet (Lawhern et al., 2018) is a compact 1-D separable convolutional
network. Because each fold sees roughly 112 training trials, we found
that training end-to-end from scratch under our resource budget was
unreliable (strong run-to-run variance at fixed hyperparameters). Instead
we evaluated a broad sweep over temporal-filter count, augmentation
strength (Gaussian noise, time shift, channel dropout), and random-seed
realisations under the same fold protocol, and selected the highest-CV
configuration for Subject 2.

## 4. Cross-validation protocol

A single stratified 5-fold split — ``StratifiedKFold(n_splits=5,
shuffle=True, random_state=42)`` — defines the evaluation partition.
All candidate pipelines use the same folds, so per-fold accuracies are
directly comparable. The ``shuffle=True`` flag is required for
``random_state`` to take effect; without it scikit-learn's
``StratifiedKFold`` is deterministic by trial order and ignores the
seed.

For candidates where stacking is used (§ 5.2), the same folds produce
out-of-fold probabilities; the meta-learner is then CV'd on the OOF
matrix using the same 5-fold partition (*not* nested CV). This is the
standard stacking convention.

### 4.1 Selection-CV is a selection score, not an unbiased estimator

Because the same folds are used to choose among many candidate pipelines
per subject, the selected per-subject CV should be interpreted as a
**model-selection score**, not as an unbiased generalisation estimate
(Cawley & Talbot, *JMLR* 2010). A fully unbiased training-set-only
estimate would require nested CV; here, the held-out test set provides
the external check on whether the selected protocol generalises.

### 4.2 Leakage controls

- All fold-dependent transforms are fit only on the training split of
  each fold: covariance shrinkage, CSP filters, pyRiemann tangent-space
  reference means, per-channel scalers, mutual-information feature
  selectors, and all classifier parameters.
- Test-time window choice (§ 5.3) is selected on training-fold CV; the
  per-fold classifier is then retrained on that window before being
  applied to the matching test window. No test-set information enters
  the choice.
- Leaderboard usage during development: 0 submissions. Final evaluation
  submissions: 1.

## 5. Model selection

### 5.1 Per-subject single-model selection

For Subject 1, Subject 2, Subject 3, Subject 5, and Subject 6 the pipeline with the single
highest CV mean is chosen.

### 5.2 Stacking for Subject 4

For Subject 4, five pyRiemann-tangent-space variants at fixed
bandpasses — ``6–30``, ``8–30``, ``4–40``, ``8–13``, and ``6–14`` Hz
(see ``configs/default.yaml``) — are fit with 5-fold CV, yielding a
``(140, 5)`` matrix of out-of-fold positive-class probabilities. The
five base variants are pre-specified before any stacking meta-learner
is fit, and frozen before any test prediction is generated. An L2
logistic regression (``C = 10``) is then fit on these meta-features;
its 5-fold CV accuracy (0.9857) exceeds that of the single best base
(0.9786) and is therefore preferred.

**Test-time stacking protocol.** Each base variant is run through
identical 5-fold CV, producing two outputs: an out-of-fold positive-class
probability matrix on the 140 training trials (the meta-feature columns)
and an averaged-across-folds test-probability matrix on the 60 test trials.
The meta-learner is fit once on the (140, 5) OOF matrix and then applied
to the (60, 5) averaged-test matrix. By construction, every meta-training
row is the prediction of a base model that did not see that row during
base training (the standard Wolpert leakage-free stacking recipe). The
implementation is in ``src/bci_mi_decoder/models/stacking.py``.

### 5.3 Test-time window augmentation (Subject 3, Subject 5, Subject 6)

For these three subjects the optimal window (by CV) is 2.5 s rather than
the 2.25 s default. Each candidate model is trained on the 2.5 s window
and produces test predictions from that same window. The augmentation is
"train-time-derived": a new classifier is trained for the new window;
no test-set information is consumed.

## 6. Final submission

The 5 per-fold models of the selected pipeline are each used to predict
probabilities on the test set. These five test-probability matrices are
averaged and argmax'd to yield the submitted labels — a standard CV-bagged
ensemble. Each fold-model is therefore trained on 112 / 140 trials.

**Why CV-bagging rather than a full-140 refit.** The foldwise ensemble
provides an internal averaging effect that reduces variance relative to
a single full-data fit, and using exactly the foldwise models keeps the
test-time protocol bit-identical to the protocol that produced the
selection-CV scores. A post-selection full-140 refit was *not* tested
before the single-shot submission; this repository therefore makes no
empirical claim that CV-bagging outperformed a full-data refit on the
held-out set. It was simply the protocol that the CV-driven selection
implicitly committed to.

## 7. Compliance notes

- The test set is *never* consulted during candidate enumeration,
  cross-validation, or model selection.
- No leaderboard / submission score informs any subsequent choice.
- Every selection decision can be reconstructed from the artifacts
  written by ``scripts/train.py`` (``report.md``, ``summary.json``).

## 8. Limitations

- **Small N.** 140 training trials per subject is at the lower end of
  what modern deep networks require; conclusions about deep-model
  performance here do not generalise to larger datasets.
- **Within-session evaluation.** The test split is drawn from the same
  recording session as the training split; this is not a cross-session
  generalisation estimate.
- **Selection-CV optimism.** The macro-average is reported two ways:
  0.9512 selection-CV (using the fixed-seed Subject 3 score of 1.0000
  that argmax selection actually consumed) and 0.9496 robustness-
  adjusted (substituting Subject 3 with its 6-seed stratified-CV mean
  of 0.9905). Both are selection scores in the sense of § 4.1; the
  held-out test accuracy (0.93) is the primary external estimate.
- **Candidate set is broad but not exhaustive.** Riemannian Procrustes
  alignment, deep tangent-space networks, and recent transformer
  variants tuned for sensorimotor rhythms were either tested only at
  default settings or not tested at all.

## References

Ang, K. K., Chin, Z. Y., Wang, C., Guan, C., & Zhang, H. (2012).
  Filter bank common spatial pattern algorithm on BCI Competition IV
  Datasets 2a and 2b. *Frontiers in Neuroscience*, 6, 39.
Barachant, A., Bonnet, S., Congedo, M., & Jutten, C. (2012).
  Multiclass brain–computer interface classification by Riemannian geometry.
  *IEEE Trans. Biomed. Eng.*, 59(4), 920–928.
Barachant, A., Bonnet, S., Congedo, M., & Jutten, C. (2013).
  Classification of covariance matrices using a Riemannian-based kernel for BCI
  applications. *Neurocomputing*, 112, 172–178.
Blankertz, B., Tomioka, R., Lemm, S., Kawanabe, M., & Müller, K.-R. (2008).
  Optimizing spatial filters for robust EEG single-trial analysis.
  *IEEE Signal Process. Mag.*, 25(1), 41–56.
Cawley, G. C., & Talbot, N. L. C. (2010). On over-fitting in model
  selection and subsequent selection bias in performance evaluation.
  *J. Mach. Learn. Res.*, 11, 2079–2107.
Lawhern, V. J., Solon, A. J., Waytowich, N. R., Gordon, S. M., Hung, C. P.,
  & Lance, B. J. (2018). EEGNet: A compact convolutional neural network
  for EEG-based brain–computer interfaces. *J. Neural Eng.*, 15(5), 056013.
Lotte, F., et al. (2018). A review of classification algorithms for EEG-based
  brain-computer interfaces: a 10-year update. *J. Neural Eng.*, 15(3), 031005.
Ramoser, H., Müller-Gerking, J., & Pfurtscheller, G. (2000).
  Optimal spatial filtering of single trial EEG during imagined hand movement.
  *IEEE Trans. Rehabil. Eng.*, 8(4), 441–446.
Wolpert, D. H. (1992). Stacked generalization. *Neural Networks*, 5, 241–259.
