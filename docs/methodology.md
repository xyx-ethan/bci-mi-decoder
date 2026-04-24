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

All trials are cropped to a fixed time window relative to the cue. The
default window is 2.25 s (samples 384 to 1537). pyRiemann-based pipelines
additionally use an extended 2.5 s window (samples 256 to 1537); see
§ 5 for the ablation motivating this choice.

Each trial is band-pass filtered with a zero-phase IIR filter (MNE-Python's
``filter_data`` with ``method="iir"``) and z-scored per channel. The band
used is model-specific and is listed in Table 1 of the README.

No ICA, artifact rejection, or session-level re-referencing is applied. This
keeps the protocol reproducible on any 64-channel EEG dataset without
requiring trained analysts.

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

Sample covariance matrices (Ledoit–Wolf / Oracle Approximating Shrinkage
estimator) are projected to the tangent space at their Riemannian mean
under the affine-invariant metric, and classified with an L2 logistic
regression (Barachant et al., 2012, 2013). This pipeline is strong on
subjects with clean, broadband EEG.

### 3.3 Filter-Bank CSP

FBCSP (Ang et al., 2012) computes CSP features in nine overlapping
sub-bands, performs mutual-information feature selection, and classifies
with LDA. Evaluated but rarely selected by CV on this dataset.

### 3.4 EEGNet with strong augmentation

EEGNet (Lawhern et al., 2018) is a compact 1-D separable convolutional
network. In this study we did not re-train it end-to-end; predictions from
a previously computed pool of 91 hyperparameter variants (trained by a
collaborator under the same split convention) were treated as an external
candidate and the single highest-CV variant was used for SUB2.

## 4. Cross-validation protocol

A single stratified 5-fold split (``random_state = 42``) defines the
evaluation partition. All candidate pipelines use the same folds, so
per-fold accuracies are directly comparable.

For candidates where stacking is used (§ 5.2), the same folds produce
out-of-fold probabilities; the meta-learner is then CV'd on the OOF
matrix using the same 5-fold partition (*not* nested CV). This is the
standard stacking convention.

## 5. Model selection

### 5.1 Per-subject single-model selection

For SUB1, SUB2, SUB3, SUB5, and SUB6 the pipeline with the single
highest CV mean is chosen.

### 5.2 Stacking for SUB4

For SUB4, five pyRiemann-tangent-space variants (different bandpasses;
see ``configs/default.yaml``) are fit with 5-fold CV, yielding a
``(140, 5)`` matrix of out-of-fold positive-class probabilities. An L2
logistic regression (``C = 10``) is fit on these meta-features; its
5-fold CV accuracy (0.9857) exceeds that of the single best base
(0.9786) and is therefore preferred.

### 5.3 Test-time window augmentation (SUB3, SUB5, SUB6)

For these three subjects the optimal window (by CV) is 2.5 s rather than
the 2.25 s default. Each candidate model is trained on the 2.5 s window
and produces test predictions from that same window. The augmentation is
"train-time-derived": a new classifier is trained for the new window;
no test-set information is consumed.

## 6. Final submission

The 5 per-fold models of the selected pipeline are each used to predict
probabilities on the test set. These five test-probability matrices are
averaged and argmax'd to yield the submitted labels. This is equivalent
to a standard bagged-CV ensemble and reduces variance relative to
retraining on all 140 trials.

## 7. Compliance notes

- The test set is *never* consulted during candidate enumeration,
  cross-validation, or model selection.
- No leaderboard / submission score informs any subsequent choice.
- Every selection decision can be reconstructed from the artifacts
  written by ``scripts/train.py`` (``report.md``, ``summary.json``).

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
Lawhern, V. J., Solon, A. J., Waytowich, N. R., Gordon, S. M., Hung, C. P.,
  & Lance, B. J. (2018). EEGNet: A compact convolutional neural network
  for EEG-based brain–computer interfaces. *J. Neural Eng.*, 15(5), 056013.
Lotte, F., et al. (2018). A review of classification algorithms for EEG-based
  brain-computer interfaces: a 10-year update. *J. Neural Eng.*, 15(3), 031005.
Ramoser, H., Müller-Gerking, J., & Pfurtscheller, G. (2000).
  Optimal spatial filtering of single trial EEG during imagined hand movement.
  *IEEE Trans. Rehabil. Eng.*, 8(4), 441–446.
Wolpert, D. H. (1992). Stacked generalization. *Neural Networks*, 5, 241–259.
