# Results

## Selected pipeline per subject

| Subject   | Selected model                                   | Band (Hz) | Window (s)      | 5-fold CV |
|:---------:|--------------------------------------------------|:---------:|:---------------:|:---------:|
| Subject 1 | CSP (*k*=4) + SVM-RBF                            |   8–13    | 2.25 (384–1537) |  0.9786   |
| Subject 2 | EEGNet with strong augmentation                  |   7–30    | 2.25            |  0.8786   |
| Subject 3 | pyRiemann TS + L2 logistic regression            |   6–30    | 2.50 (256–1537) |  1.0000 † |
| Subject 4 | Stacking (L2-logistic *C*=10) over 5 TS variants |   6–30    | 2.25            |  0.9857   |
| Subject 5 | CSP (*k*=4) + LDA                                |  10–14    | 2.50            |  0.9214   |
| Subject 6 | CSP (*k*=4) + LDA                                |  10–14    | 2.50            |  0.9429   |
| **Macro-average selection-CV** |                                  |           |                 | **0.9512** |
| Robustness-adjusted mean (Subject 3 substituted with 6-seed mean 0.9905) |                       |           |                 | 0.9496    |

The CV column above is the **selection score** used to pick the per-subject
pipeline; because the same finite training set is reused for many
candidates, it is expected to be optimistic and should not be read as an
unbiased estimate of generalisation (Cawley & Talbot, *JMLR* 2010). The
held-out test accuracy is the primary external estimate.

Held-out test accuracy: **0.93**. If this corresponds to 335/360 correct
predictions, the Wilson 95 % CI is approximately [0.900, 0.953]; for
334/360 it is approximately [0.896, 0.950].

† Subject 3 sat at this pipeline's ceiling under the fixed-seed split used
for argmax selection: all 140 held-out trials were classified correctly
(selection-CV = 1.0000). As a stability check the same pipeline was re-run
under 6 different stratified-CV seeds; the cross-seed mean is 0.9905 with
standard deviation ~0.010. Both figures (selection-CV 0.9512, robustness-
adjusted 0.9496) are reported above so the substitution is explicit.

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

Differences smaller than roughly 2–3 percentage points should not be
over-interpreted on this set without paired predictions (e.g. McNemar's
test or a paired bootstrap).

## Frontier-vs-classical comparison (v1, four-agent audit-revised)

Running the package's adaptive ensemble against six modern deep MI
methods (ShallowConvNet, Deep4Net, EEGNetv4, EEGConformer, ATCNet,
EEGITNet via braindecode 1.4) and five classical baselines under the
SAME 5-fold split, same preprocessing (crop 384–1537, IIR 7–30 Hz,
per-trial z-score), and source-paper default hyperparameters
(`AdamW(lr=1e-3, weight_decay=1e-4)`, 100 epochs, batch size 32, 3
random seeds for deep methods).

Reproduction: `python experiments/benchmark.py all && python experiments/aggregate.py`.
Full table and per-cell asymmetry disclosures: `experiments/SUMMARY.md`.

### Headline deltas (audit-revised)

| Comparator | Macro CV | Δ vs submitted ensemble (0.9496) |
|-----------|---------:|---------------------------------:|
| **Best-of-N single methods (per-subject argmax, matched protocol)** | 0.8698 | **+7.98 pp** ← apples-to-apples |
| Best uniform single method (no per-subject selection) | 0.8369 | +11.27 pp ← deployment view |
| EEGConformer (Song 2023, best deep) | 0.7750 | +17.46 pp |
| Deep4Net (Schirrmeister 2017, weakest deep — protocol-disadvantaged) | 0.6325 | +31.71 pp |

### Honest caveats (the comparison does NOT support a "we win by 11 pp"
claim)

1. **Selection-bias optimism on the ensemble row.** Per-subject
   argmax over a candidate pool of N≥10 pipelines adds an expected
   **+4–6 pp upward bias** (Cawley & Talbot 2010) that the
   single-method rows do not carry. After this correction, the
   residual real advantage vs the strongest classical baseline is
   ≈+5–7 pp; the one-sided 95 % lower bound approaches 0.
2. **S4 stacking does not improve over `CSP+LDA broad 7–30 Hz`.**
   Both reach 138/140 = 0.9857 macro CV. Stacking should be removed
   from the S4 pipeline in any future deployment of this package.
3. **S5/S6 advantage is band+window confound.** The ensemble uses
   CSP+LDA at upper-μ 10–14 Hz with a 2.5 s window; deep rows use
   7–30 Hz with the default 2.25 s window. Whether band-tuned deep
   methods would close this gap is untested.
4. **S2 augmentation asymmetry.** The submitted EEGNet on S2 uses
   Gaussian-noise / time-shift / channel-dropout augmentation
   (CV 0.8786). The benchmark's `EEGNetv4` row is vanilla (CV 0.7357).
   The +0.14 gap on S2 is essentially the augmentation gap, not a
   model-class gap.
5. **Multiple-testing.** Across 77 cells (11 methods × 6 subjects + 11
   macros) the Bonferroni-adjusted significance threshold at the
   per-cell level is ≈32 pp; only the deltas vs Deep4Net (+31.7 pp)
   and EEGITNet (+34.9 pp) clearly survive Bonferroni at the macro
   level. The 11 pp lead vs strong classicals does **not** reach
   Bonferroni significance.
6. **Deep-side protocol is suboptimal.** Source-paper recipes call for
   per-method learning rates (Schirrmeister 6.25e-4; Song 2e-4 + cosine
   warmup; Altaheri 9e-4), cosine annealing schedules, early stopping,
   and (for Deep4Net) cropped decoding + MaxNormDefaultConstraint. A
   v2 re-run with these per-method recipes is being prepared; the
   expected lift on the deep ceiling is +5–10 pp, bringing the strongest
   deep method to **parity with classical (~0.83–0.85)** but not above.

### Defensible take-aways

- **Under a fixed-config-per-method deep protocol**, no tested deep
  MI method matches the per-subject adaptive ensemble.
- **All deep methods underperform `pyRiemann TS+LR broad` and
  `CSP+LDA broad`** on this dataset; no deep method individually beats
  classical even at parity.
- **Adaptive per-subject preprocessing selection (band, window,
  augmentation) explains a substantial fraction of the ensemble lead**
  over uniform single methods, more than any single deep architecture
  choice.
- **Subject 4 stacking buys no measurable accuracy** over a simpler
  `CSP+LDA broad 7–30 Hz` baseline (138/140 each); future deployments
  should use the simpler model on this subject.
