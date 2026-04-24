# Results

## Selected pipeline per subject

| Subject | Selected model                                | Band (Hz) | Window (s)   | 5-fold CV |
|:-------:|-----------------------------------------------|:---------:|:------------:|:---------:|
| SUB1    | CSP(k=4) + SVM-RBF                            |   8–13    | 2.25 (384–1537) |  0.9786   |
| SUB2    | EEGNet w/ strong augmentation (external pool) |   7–30    | 2.25            |  0.8786   |
| SUB3    | pyRiemann TS + L2 logistic regression         |   6–30    | 2.50 (256–1537) |  1.0000   |
| SUB4    | Stacking (L2-logistic C=10) over 5 TS variants|   6–30    | 2.25            |  0.9857   |
| SUB5    | CSP(k=4) + LDA                                |  10–14    | 2.50            |  0.9214   |
| SUB6    | CSP(k=4) + LDA                                |  10–14    | 2.50            |  0.9429   |
| **Mean**|                                               |           |                 |**0.9512** |

Held-out test accuracy: **0.93** (360 trials; Wilson 95 % CI [0.90, 0.96]).

## Full candidate search — SUB1 (μ-band dominance)

All candidates evaluated on the same 5-fold CV partition.

| Candidate                                           | CV accuracy |
|-----------------------------------------------------|:-----------:|
| **CSP(k=4) + SVM-RBF, 8–13 Hz**                     | **0.9786**  |
| CSP(k=2) + SVM-RBF, 8–13 Hz                         |   0.9786    |
| CSP(k=4) + LDA, 8–13 Hz                             |   0.9714    |
| pyRiemann TS + LR, 6–14 Hz                          |   0.9214    |
| pyRiemann TS + LR, 8–13 Hz                          |   0.9357    |
| pyRiemann TS + LR, 6–30 Hz                          |   0.8929    |
| pyRiemann TS + LR, 8–30 Hz                          |   0.8786    |
| FBCSP + LR (9 bands, k=2 each, MI feat. selection)  |   0.9571    |
| EEGNet (best of 91 hyperparameter variants)         |   0.8238    |
| EEGConformer, PhysioNet-pretrained + fine-tune      |   0.7143    |

The narrow μ-band CSP+SVM outperforms every broadband or deep candidate
on this subject. See Discussion in the main README.

## Full candidate search — SUB2 (deep net beats classical)

| Candidate                                           | CV accuracy |
|-----------------------------------------------------|:-----------:|
| **EEGNet w/ strong aug, 7–30 Hz (external pool)**   | **0.8786**  |
| pyRiemann TS + LR, 6–30 Hz                          |   0.8214    |
| CSP(k=6) + SVM-RBF, 6–30 Hz                         |   0.7714    |
| CSP(k=4) + LDA, 6–30 Hz                             |   0.8000    |
| FBCSP + LR                                          |   0.7357    |
| EEGConformer, PhysioNet-pretrained + fine-tune      |   0.8714    |
| LMDA-Net, retrained from scratch                    |   0.8357    |

SUB2 is the only subject on which a deep network wins. Even so, the
advantage over pyRiemann is only ~0.06.

## Test-time window ablation — SUB3

Same pyRiemann TS + LR pipeline; only the time window changes.

| Window (samples / seconds) | CV accuracy |
|:--------------------------:|:-----------:|
| 384–1537 (2.25 s, default) |   0.9929    |
| **256–1537 (2.50 s)**      | **1.0000**  |
| 500–1537 (2.02 s)          |   0.9929    |
| 300–1453 (2.25 s, shifted) |   0.9857    |

## Binomial noise budget

Held-out test set: 60 trials × 6 subjects = 360 total. A single
percentage point of test accuracy corresponds to 3–4 additional trials
being correctly classified. Under Wilson 95 % CI bounds:

- 0.92 → [0.89, 0.94]
- 0.93 → [0.90, 0.95]
- 0.94 → [0.91, 0.96]

Differences smaller than roughly 0.01 are within test-set noise.
