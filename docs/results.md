# Results

## Selected pipeline per subject

| Subject   | Selected model                                 | Band (Hz) | Window (s)      | 5-fold CV |
|:---------:|------------------------------------------------|:---------:|:---------------:|:---------:|
| Subject 1 | CSP(*k*=4) + SVM-RBF                           |   8–13    | 2.25 (384–1537) |  0.9786   |
| Subject 2 | EEGNet with strong augmentation                |   7–30    | 2.25            |  0.8786   |
| Subject 3 | pyRiemann TS + L2 logistic regression          |   6–30    | 2.50 (256–1537) |  0.9905 † |
| Subject 4 | Stacking (L2-logistic *C*=10) over 5 TS variants |   6–30    | 2.25            |  0.9857   |
| Subject 5 | CSP(*k*=4) + LDA                               |  10–14    | 2.50            |  0.9214   |
| Subject 6 | CSP(*k*=4) + LDA                               |  10–14    | 2.50            |  0.9429   |
| **Mean**  |                                                |           |                 | **0.9496** |

The CV column above is the **selection score** used to pick the per-subject
pipeline; because the same folds are reused for many candidates, it is
potentially optimistic and should not be read as an unbiased generalisation
estimate (Cawley & Talbot, *JMLR* 2010). The held-out test accuracy is the
primary external estimate.

Held-out test accuracy: **0.93** (335/360 correct; Wilson 95 % CI ≈ [0.900, 0.953]).

† Subject 3 is at this pipeline's ceiling. Under a single fixed-seed 5-fold
split all 140 held-out trials were classified correctly (nominal CV = 1.000).
With only 28 validation trials per fold, the cross-seed standard deviation
for this configuration is ~0.010, so the honest 6-seed stratified-CV mean
of 0.9905 is reported here. The distinction between "nominally perfect" and
"≈ 0.99" is within CV-variance noise on this subject.

## Full candidate search — Subject 1 (μ-band dominance)

All candidates evaluated on the same 5-fold CV partition.

| Candidate                                           | CV accuracy |
|-----------------------------------------------------|:-----------:|
| **CSP(*k*=4) + SVM-RBF, 8–13 Hz**                   | **0.9786**  |
| CSP(*k*=2) + SVM-RBF, 8–13 Hz                       |   0.9786    |
| CSP(*k*=4) + LDA, 8–13 Hz                           |   0.9714    |
| pyRiemann TS + LR, 6–14 Hz                          |   0.9214    |
| pyRiemann TS + LR, 8–13 Hz                          |   0.9357    |
| pyRiemann TS + LR, 6–30 Hz                          |   0.8929    |
| pyRiemann TS + LR, 8–30 Hz                          |   0.8786    |
| FBCSP + LR (9 bands, *k*=2 each, MI feat. select.)  |   0.9571    |
| EEGNet, best augmented configuration tested         |   0.8238    |
| EEG-Conformer, PhysioNet-pretrained + fine-tune     |   0.7143    |

The narrow μ-band CSP+SVM outperforms every broadband or deep candidate
on this subject. See §4 of the main README for the interpretation.

## Full candidate search — Subject 2 (deep network wins)

| Candidate                                           | CV accuracy |
|-----------------------------------------------------|:-----------:|
| **EEGNet with strong augmentation, 7–30 Hz**        | **0.8786**  |
| pyRiemann TS + LR, 6–30 Hz                          |   0.8214    |
| CSP(*k*=6) + SVM-RBF, 6–30 Hz                       |   0.7714    |
| CSP(*k*=4) + LDA, 6–30 Hz                           |   0.8000    |
| FBCSP + LR                                          |   0.7357    |
| EEG-Conformer, PhysioNet-pretrained + fine-tune     |   0.8714    |
| LMDA-Net, retrained from scratch                    |   0.8357    |

Subject 2 is the only subject on which a deep architecture wins the CV
comparison. The margin over the best pyRiemann variant is ~0.06 — real,
but not large in binomial-noise terms.

## Test-time window ablation — Subject 3

Same pyRiemann TS + LR pipeline, only the analysis window changes.
Accuracies are single-seed 5-fold CV and should be read with the caveat
in the main table: the cross-seed standard deviation at ceiling is ~0.01.

| Window (samples at 512 Hz / seconds) | CV accuracy |
|:------------------------------------:|:-----------:|
| 384–1537 (2.25 s, default)           |   0.9929    |
| **256–1537 (2.50 s)**                | **1.0000**  |
| 500–1537 (2.02 s)                    |   0.9929    |
| 300–1453 (2.25 s, shifted)           |   0.9857    |

## Binomial noise budget

Held-out test set: 60 trials × 6 subjects = 360 total. A single percentage
point of test accuracy corresponds to 3–4 additional trials being correctly
classified. Wilson 95 % CI at representative operating points:

- 0.92 (331/360) → [0.888, 0.945]
- 0.93 (335/360) → [0.900, 0.953]
- 0.94 (338/360) → [0.910, 0.961]

Differences smaller than roughly 1–2 percentage points should not be
over-interpreted on this set without paired predictions.
