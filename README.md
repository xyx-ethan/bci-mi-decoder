# BCI Motor Imagery Decoder

A per-subject adaptive ensemble for binary motor imagery classification from
64-channel scalp EEG. Model selection is driven exclusively by stratified
5-fold cross-validation on the training split; no feedback from the test set
is used at any stage.

> **Status.** Macro-average 5-fold selection-CV **0.9512** (or **0.9496**
> with the Subject 3 6-seed robustness substitution); held-out test
> accuracy **0.93**; **Rank 1 / 306** on the BCI-ISLA 2026 leaderboard
> ([CodaBench challenge 15044](https://www.codabench.org/competitions/15044/)).
> The exact submission code is tagged at
> [release v0.1.0](https://github.com/xyx-ethan/bci-mi-decoder/releases/tag/v0.1.0).

## Headline results

Six-subject corpus, 140 train / 60 test trials per subject (2-class
left hand vs. right hand motor imagery, 64 channels, 512 Hz sampling).

| Subject   | Selected model                                                       | 5-fold CV       |
|:---------:|----------------------------------------------------------------------|:---------------:|
| Subject 1 | CSP + SVM-RBF, μ band (8–13 Hz)                                      |  0.9786         |
| Subject 2 | EEGNet with strong augmentation, 7–30 Hz                             |  0.8786         |
| Subject 3 | pyRiemann tangent-space + logistic regression, 6–30 Hz, 2.5 s window |  1.0000 †       |
| Subject 4 | Stacking meta-learner (L2-logistic, C=10) over pyRiemann variants    |  0.9857         |
| Subject 5 | CSP + LDA, 10–14 Hz, 2.5 s window                                    |  0.9214         |
| Subject 6 | CSP + LDA, 10–14 Hz, 2.5 s window                                    |  0.9429         |
| **Macro-average selection-CV** |                                                                      | **0.9512**      |
| Robustness-adjusted mean (Subject 3 substituted with 6-seed mean 0.9905)    |                                                                      | 0.9496          |

Held-out test accuracy: **0.93**. If this corresponds to 335/360 correct
predictions, the Wilson 95 % CI is approximately [0.900, 0.953]; if it
corresponds to 334/360, the interval is approximately [0.896, 0.950].

> **How to read these numbers.** The CV column above is the
> **selection score** used to pick the per-subject pipeline; because the
> same finite training set is used to choose among many candidates, the
> selected CV is expected to be optimistic and should not be read as an
> unbiased estimate of generalisation (Cawley & Talbot, *JMLR* 2010). The
> **held-out test accuracy** is the primary external estimate.

† Under the fixed-seed 5-fold split used for argmax selection this pipeline
had all 140 held-out trials classified correctly (selection-CV = 1.0000).
As a stability check the same pipeline was re-run under 6 different
stratified-CV seeds; the cross-seed mean is 0.9905 with standard deviation
~0.010, so the distinction between "nominally perfect" and "≈ 0.99" is within
seed-induced CV noise on this subject. Both the selection-CV figure (0.9512)
and the robustness-adjusted figure (0.9496) are reported above so the
substitution is explicit.

### Context: published 2-class motor-imagery decoders

The numbers below come from different datasets, subject pools, and
evaluation protocols, so they are **not directly comparable** to the
6-subject benchmark above. They are listed only to anchor the reader's
prior on what a "strong" two-class motor-imagery decoder typically
reports.

| Method                           | Dataset                  | Reported mean | Reference                                                |
|----------------------------------|--------------------------|:------------:|----------------------------------------------------------|
| LMDA-Net (Miao et al., 2023)     | BCI IV-2a (2-class)      | 0.88 – 0.93  | [Miao et al., *NeuroImage* 2023](https://doi.org/10.1016/j.neuroimage.2023.120209) |
| EEG-Conformer (Song et al., 2023)| BCI IV-2a (2-class)      | 0.85 – 0.92  | [Song et al., *IEEE TNSRE* 2023](https://ieeexplore.ieee.org/document/9991178)     |
| CTNet (Zhao et al., 2024)        | BCI IV-2a (2-class)      | 0.87 – 0.93  | [Zhao et al., *Sci. Reports* 2024](https://www.nature.com/articles/s41598-024-71118-7) |
| GAH-TNet (2025)                  | BCI IV-2a (2-class)      | 0.87 – 0.90  | [Brain Sciences 2025](https://www.mdpi.com/2076-3425/15/8/883)                     |
| **This repository (CV / test)**  | 6-subject 2-class MI     | **0.9512 / 0.93** | —                                                        |

## Scientific contributions

1. **Classical CSP + RBF-SVM on the isolated μ band dominates on one subject.**
   On Subject 1, a single CSP-filtered RBF-SVM with `n_components = 4`
   restricted to 8–13 Hz reaches 0.9786 CV, **outperforming every deep
   baseline evaluated on the same split**, including a PhysioNet-pretrained
   EEG-Conformer (0.7143 CV) and the best augmented-EEGNet configuration
   tested (0.8238 CV). For subjects with a well-expressed sensorimotor
   μ-rhythm ERD, the discriminative information concentrates in a narrow
   band that a well-conditioned spatial filter captures in closed form;
   with ~112 training trials per fold, broadband deep networks lack the
   data to rediscover the same structure.

2. **A wider analysis window improves cross-validation on some subjects.**
   For Subjects 3, 5, and 6, re-training the selected pipeline on a 2.5 s
   window (samples 256–1537 at 512 Hz) rather than the 2.25 s default
   (384–1537) improves 5-fold CV on each of the three, with the largest
   gain (+0.02 CV) on Subject 6. The augmentation is train-time-derived:
   a new classifier is fit to each window and only per-fold test
   probabilities are averaged, so no test-label information enters the
   choice.

3. **Tangent-space stacking helps on a subset of subjects.**
   For Subject 4, an L2-regularised logistic regression trained over
   out-of-fold predictions from five pyRiemann tangent-space variants
   (different bandpasses with Ledoit–Wolf-regularised covariance
   estimation) improves CV from 0.9786 (best single variant) to 0.9857.
   Stacking helped only when (a) base-model diversity was present and
   (b) no single base model was already at ceiling.

## Methodology

### Data processing

All analyses operate on 64-channel, 512 Hz, continuous EEG epoched into
single-trial windows. The default window is 2.25 s (samples 384–1537
relative to the cue); an alternative window of 2.5 s (256–1537) is used
for pyRiemann-based models as indicated in the results table. Each trial
is z-scored per channel; no ICA or artifact rejection is applied.

Per-band processing uses an IIR band-pass filter via MNE-Python's
`filter_data`. Covariances are estimated with Ledoit-Wolf shrinkage
(`pyRiemann.estimation.Covariances("oas")`).

### Candidate models

All candidate families are standard published pipelines:

- **CSP + LDA / SVM-RBF / SVM-linear** (Ramoser et al., 2000; Blankertz et al., 2008)
  with `n_components ∈ {2, 4, 6, 8}` and Ledoit-Wolf regularised covariance.
- **pyRiemann tangent-space + logistic regression** (Barachant et al., 2012, 2013)
  under the affine-invariant (`"riemann"`) metric.
- **EEGNet with augmentation** (Lawhern et al., 2018); a broad
  hyperparameter sweep over temporal-filter count, augmentation strength,
  and random-seed realisations is evaluated under the same folds.
- **Filter-Bank CSP (FBCSP)** (Ang et al., 2012) with 9 overlapping bands
  and mutual-information feature selection.

### Selection protocol

For each subject independently:

1. Evaluate all candidate pipelines with a single fixed
   5-fold `StratifiedKFold` (`random_state = 42`).
2. Record the mean fold accuracy for each candidate.
3. Select either (a) the single-pipeline argmax of CV accuracy, or
   (b) a stacking meta-learner trained on the out-of-fold predictions
   from the top-five pipelines, whichever has higher CV accuracy.
4. Re-fit the selected estimator on all five folds and average the
   per-fold predicted probabilities on the test set. Argmax yields the
   submitted label.

The test set is **never consulted** during step 1–3. No aggregated
submission is re-evaluated against its leaderboard score for selection
purposes. Step 4 produces the final submission in a single shot.

### Leakage controls

- **All fold-dependent transforms are fit only on the training split of each
  fold**: covariance shrinkage, CSP filters, pyRiemann tangent-space reference
  means, per-channel scalers, mutual-information feature selectors, and all
  classifier parameters.
- **Test-time window choice is training-derived.** When a 2.5 s window beats
  the 2.25 s default for a given subject, the choice is made on training-fold
  CV; a new per-fold classifier is then trained on that window and applied to
  the matching test window. No leaderboard feedback or test labels are ever
  consulted.
- **Leaderboard usage during development: 0 submissions; final evaluation
  submissions: 1.**

### Why this is not a deep-learning paper

EEG decoding at this scale (≤ 150 trials per subject) is well known to
be regime-appropriate for regularised classical methods (Lotte et al.,
*J. Neural Eng.* 2018; Jayaram & Barachant, *Sci. Data* 2018). Modern
end-to-end architectures (EEGNet, Deep4Net, EEG-Conformer, FBCNet,
LMDA-Net) were evaluated here as candidate pipelines and *selected when
they won the CV comparison* — but on most of the subjects in this
dataset, a properly-tuned CSP or pyRiemann baseline wins, consistent
with the broader literature. The contribution of this repository is a
*principled adaptive-ensemble protocol*, not a new architecture.

## Installation

Tested on Python 3.10+ and Python 3.12. No GPU required for the
selected per-subject pipelines.

```bash
git clone https://github.com/xyx-ethan/bci-mi-decoder
cd bci-mi-decoder
python -m venv .venv
source .venv/bin/activate      # Windows: .venv\Scripts\activate
pip install -e .
```

Minimum dependencies: NumPy, SciPy, scikit-learn, MNE-Python,
pyRiemann. See `requirements.txt` for pinned versions.

## Data layout

The pipeline expects one NumPy file per subject per split under a
single directory:

```
<data_dir>/
    subject1_X_train.npy   # shape (n_train, n_channels, n_samples), float32/64
    subject1_y_train.npy   # shape (n_train,), strings "left_hand" or "right_hand"
    subject1_X_test.npy    # shape (n_test,  n_channels, n_samples)
    subject2_X_train.npy
    …
    subject6_X_test.npy
```

The naming prefix (here `subject1` … `subject6`) is a string identifier
passed to `load_subject`; any stable labelling works as long as the
filenames and the `subjects:` list in `configs/default.yaml` agree.

Subject data are *not redistributed* from this repository; see the
original data-sharing agreement for the BCI-ISLA 2026 challenge.

## Usage

Reproduce the full CV + test pipeline:

```bash
python scripts/train.py \
    --data-dir /path/to/data \
    --output-dir runs/final
```

The script writes one JSON summary per subject, a combined
`report.md`, and a single `submission.zip` conforming to the Codabench
per-subject CSV convention.

Predict only (using saved per-subject model weights):

```bash
python scripts/predict.py --data-dir /path/to/data --run-dir runs/final
```

## Repository layout

```
src/bci_mi_decoder/
    data.py              per-subject NumPy loading and label encoding
    preprocessing.py     IIR bandpass (MNE), z-score per channel
    cv.py                deterministic 5-fold stratified CV
    metrics.py           accuracy, binomial confidence interval
    models/
        base.py          common scikit-learn compatible interface
        csp_svm.py       CSP (Ledoit-Wolf) + SVM (RBF / linear)
        pyriemann_ts.py  Covariances → TangentSpace → LogisticRegression
        stacking.py      OOF stacking with per-subject meta-learner
        tta.py           window-shift test-time augmentation
scripts/
    train.py             end-to-end: per-subject selection + submission
    predict.py           inference only
tests/
    test_pipelines.py    sanity tests on synthetic data
docs/
    methodology.md       full protocol, including ablation notes
    results.md           per-subject CV table with all candidate variants
```

## Reproducibility

All `StratifiedKFold` calls use `random_state = 42`. PyTorch models
set both `torch.manual_seed` and NumPy/`random` seeds before each
training run. Scikit-learn SVMs and pyRiemann use deterministic
fitting (no sampling). Given the same input data, `scripts/train.py`
should produce byte-identical predictions across runs on the same
machine.

## Limitations and honest caveats

- **Small N.** 140 training trials per subject is at the lower end of
  what modern deep networks require. Conclusions about deep-model
  performance here *do not* generalise to larger datasets, and they are
  not a verdict on deep EEG models in general.
- **Within-subject evaluation.** The test split is drawn from the
  same recording session as the training split. Performance reported
  here is *not* a cross-session generalisation estimate; cross-session
  robustness typically drops 5–15 percentage points (see Han et al.,
  *Technologies* 2025).
- **Selection-CV is potentially optimistic.** The same 5-fold split is
  used both for candidate selection and for the reported per-subject
  CV; the macro figure is reported as 0.9512 (selection-CV) or 0.9496
  with a Subject 3 6-seed robustness substitution. A fully unbiased
  training-set-only estimate would require nested CV; the held-out
  test accuracy (0.93) is the external check that the selected
  protocol generalises beyond the selection split.
- **Candidate set is broad but not exhaustive.** Only a finite
  hyperparameter grid was searched for the EEGNet sweep, and not every
  configuration was multi-seed bagged. Riemannian Procrustes
  alignment and several recent transformer variants were either
  evaluated only at default settings or not evaluated at all.
- **No claim about EEG foundation models in general.** A separate
  experiment (reported in the project write-up linked from the
  homepage) found that an off-the-shelf clinical-EEG foundation
  checkpoint did not transfer under a lightweight fine-tuning recipe;
  this is a protocol-specific negative result, not a verdict on the
  model class.

## Citation

If you use this code, please cite:

```bibtex
@software{bci_mi_decoder_2026,
    author  = {Xu, Yuxuan (Ethan)},
    title   = {BCI Motor Imagery Decoder: a per-subject adaptive ensemble
               with narrow-band classical baselines},
    year    = {2026},
    version = {v0.1.0},
    url     = {https://github.com/xyx-ethan/bci-mi-decoder/releases/tag/v0.1.0}
}
```

The exact code that produced the BCI-ISLA 2026 submission is permanently
tagged at [release v0.1.0](https://github.com/xyx-ethan/bci-mi-decoder/releases/tag/v0.1.0).

## Key references

- Ramoser, H., Müller-Gerking, J., & Pfurtscheller, G. (2000).
  Optimal spatial filtering of single trial EEG during imagined hand
  movement. *IEEE Trans. Rehabil. Eng.*, **8**(4), 441–446.
- Blankertz, B., Tomioka, R., Lemm, S., Kawanabe, M., & Müller, K.-R.
  (2008). Optimizing spatial filters for robust EEG single-trial
  analysis. *IEEE Signal Process. Mag.*, **25**(1), 41–56.
- Ang, K. K., Chin, Z. Y., Wang, C., Guan, C., & Zhang, H. (2012).
  Filter bank common spatial pattern algorithm on BCI Competition IV
  Datasets 2a and 2b. *Frontiers in Neuroscience*, **6**, 39.
- Barachant, A., Bonnet, S., Congedo, M., & Jutten, C. (2012).
  Multiclass brain-computer interface classification by Riemannian
  geometry. *IEEE Trans. Biomed. Eng.*, **59**(4), 920–928.
- Lawhern, V. J., Solon, A. J., Waytowich, N. R., Gordon, S. M.,
  Hung, C. P., & Lance, B. J. (2018). EEGNet: A compact
  convolutional neural network for EEG-based brain-computer
  interfaces. *J. Neural Eng.*, **15**(5), 056013.
- Lotte, F., Bougrain, L., Cichocki, A., Clerc, M., Congedo, M.,
  Rakotomamonjy, A., & Yger, F. (2018). A review of classification
  algorithms for EEG-based brain–computer interfaces: a 10 year
  update. *J. Neural Eng.*, **15**(3), 031005.
- Cawley, G. C., & Talbot, N. L. C. (2010). On over-fitting in model
  selection and subsequent selection bias in performance evaluation.
  *J. Mach. Learn. Res.*, **11**, 2079–2107.
- Miao, Z., Zhao, M., Zhang, X., & Ming, D. (2023). LMDA-Net: A
  lightweight multi-dimensional attention network for general
  EEG-based brain-computer interfaces and interpretability.
  *NeuroImage*, **276**, 120209.
- Song, Y., Zheng, Q., Liu, B., & Gao, X. (2023). EEG Conformer:
  Convolutional transformer for EEG decoding and visualization.
  *IEEE TNSRE*, **31**, 710–719.

## License

Released under the MIT License. See `LICENSE`.
