# Frontier-vs-classical benchmark on the BCI-ISLA 2026 dataset

**v2: revised per four-agent red-team audit (2026-05-02).** Several claims in v1 of this summary were over-stated. The honest deltas, matched-protocol baselines, and per-cell asymmetry disclosures are reported below.

**Protocol.** Same 6 subjects from the BCI-ISLA 2026 challenge (Cho 2017 subset). For deep methods: same 5-fold split (`StratifiedKFold(n_splits=5, shuffle=True, random_state=42)`), shared preprocessing (crop 384–1537 / IIR bandpass 7–30 Hz / per-trial z-score), source-paper default hyperparameters under `AdamW(lr=1e-3, weight_decay=1e-4)`, 100 epochs, batch size 32, no early stopping or learning-rate schedule, averaged over 3 seeds (42, 43, 44). For classical methods: pipeline-native band (μ 8–13 or broad 7–30 Hz), single-seed deterministic fitting.

**Headline numbers.** All cells are SELECTION-CV (5-fold OOF) — **not unbiased generalisation estimates**. The submitted-ensemble row uses per-subject argmax over a candidate pool of N≥10 pipelines, which adds an expected **+4–6 pp upward bias** (Cawley & Talbot 2010) that the single-method rows do not carry. The matched-protocol fairness baseline ('Best-of-N single methods') is the apples-to-apples comparison.

| Method | Reference / note | S1 | S2 | S3 | S4 | S5 | S6 | **Macro** |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| **Submitted ensemble (per-subject adaptive selection)** | this work — *off-protocol* (per-subject band/window/aug) | 0.9786 | 0.8786 | 0.9905 | 0.9857 | 0.9214 | 0.9429 | **0.9496** |
| **Best-of-N single methods (per-subject argmax, this benchmark)** | matched-protocol fairness baseline | 0.9143 | 0.8405 | 0.9714 | 0.9857 | 0.8214 | 0.6857 | **0.8698** |
| **Best uniform single method (no per-subject selection)** | = CSP+LDA, broad 7-30 Hz, k=4 | 0.9000 | 0.7214 | 0.9429 | 0.9857 | 0.8000 | 0.6714 | **0.8369** |
| ShallowConvNet | Schirrmeister 2017 | 0.638±0.015 | 0.776±0.045 | 0.893±0.021 | 0.888±0.017 | 0.636±0.020 | 0.576±0.024 | **0.7345** |
| Deep4Net | Schirrmeister 2017 | 0.581±0.009 | 0.700±0.053 | 0.693±0.029 | 0.726±0.013 | 0.514±0.015 | 0.581±0.020 | **0.6325** |
| EEGNetv4 | Lawhern 2018 | 0.598±0.019 | 0.736±0.046 | 0.929±0.006 | 0.879±0.006 | 0.581±0.024 | 0.567±0.040 | **0.7147** |
| EEGConformer | Song 2023 | 0.745±0.015 | 0.779±0.017 | 0.924±0.018 | 0.895±0.024 | 0.643±0.010 | 0.664±0.015 | **0.7750** |
| ATCNet | Altaheri 2022 | 0.600±0.048 | 0.840±0.019 | 0.938±0.003 | 0.929±0.010 | 0.576±0.034 | 0.605±0.024 | **0.7480** |
| EEGITNet | Salami 2022 | 0.505±0.041 | 0.619±0.033 | 0.686±0.047 | 0.714±0.036 | 0.548±0.026 | 0.533±0.032 | **0.6008** |
| CSP+SVM-RBF, μ 8-13 Hz, k=4 | single-method classical baseline | 0.9000 | 0.7071 | 0.9286 | 0.8357 | 0.6929 | 0.5143 | **0.7631** |
| CSP+LDA, μ 8-13 Hz, k=4 | single-method classical baseline | 0.9143 | 0.6857 | 0.9214 | 0.8643 | 0.6857 | 0.5143 | **0.7643** |
| CSP+SVM-RBF, broad 7-30 Hz, k=4 | single-method classical baseline | 0.8857 | 0.6714 | 0.9571 | 0.9500 | 0.8214 | 0.6857 | **0.8286** |
| CSP+LDA, broad 7-30 Hz, k=4 | single-method classical baseline | 0.9000 | 0.7214 | 0.9429 | 0.9857 | 0.8000 | 0.6714 | **0.8369** |
| pyRiemann TS+LR, broad 7-30 Hz | single-method classical baseline | 0.8143 | 0.7714 | 0.9714 | 0.9571 | 0.8214 | 0.6857 | **0.8369** |

## Honest delta accounting

- **Submitted ensemble macro CV : 0.9496**
- Best-of-N matched-protocol      : 0.8698  → Δ = **+7.98 pp** *(apples-to-apples, both selection-CV optimistic)*
- Best uniform single method      : 0.8369  → Δ = **+11.27 pp** *(deployment view; only the ensemble row is selection-biased)*

**Selection-bias optimism.** Of the +11.27 pp lead vs the best uniform method, an estimated 4–6 pp is the expected upward bias of argmax-over-N=10-pipelines selection-CV (Cawley & Talbot 2010). After correction, the residual real advantage is approximately +5–7 pp; the one-sided 95 % lower bound vs CSP+LDA broad 7–30 Hz approaches 0.

**Per-subject deltas vs the matched-protocol best-of-N winner:**

- **Subject 1** (A): submitted 0.9786 − best-of-N 0.9143 (CSP+LDA, μ 8-13 Hz, k=4) = **Δ +6.4 pp**
- **Subject 2** (B): submitted 0.8786 − best-of-N 0.8405 (ATCNet) = **Δ +3.8 pp**
- **Subject 3** (C): submitted 0.9905 − best-of-N 0.9714 (pyRiemann TS+LR, broad 7-30 Hz) = **Δ +1.9 pp**
- **Subject 4** (D): submitted 0.9857 − best-of-N 0.9857 (CSP+LDA, broad 7-30 Hz, k=4) = **Δ -0.0 pp**
- **Subject 5** (E): submitted 0.9214 − best-of-N 0.8214 (CSP+SVM-RBF, broad 7-30 Hz, k=4) = **Δ +10.0 pp**
- **Subject 6** (F): submitted 0.9429 − best-of-N 0.6857 (CSP+SVM-RBF, broad 7-30 Hz, k=4) = **Δ +25.7 pp**

## Per-cell asymmetries the submitted-ensemble row does NOT share with the single-method rows

- **S2 (B):** submitted uses EEGNet *with* Gaussian noise / time shift / channel dropout augmentation; benchmark's `EEGNetv4` row does not. The +0.14 gap on S2 is essentially the augmentation gap, not a model-class gap.
- **S3 (C):** submitted reports a 6-seed stratified-CV mean (0.9905); all other cells are 3-seed (deep) or single-seed (classical). Estimator mismatch.
- **S4 (D):** submitted stacking macro CV is 0.9857 (asserted, not run by this benchmark). The benchmark's `CSP+LDA broad 7-30 Hz` on S4 is also 0.9857 — both miss exactly 2 of 140 trials at the macro level. Stacking does **not** improve over CSP+LDA broad on this subject.
- **S5 (E), S6 (F):** submitted uses CSP+LDA at *upper-μ 10–14 Hz* with a *2.5 s* window (versus 7-30 Hz / 2.25 s for benchmark deep rows). The 25-28 pp lead over the strongest deep method on these subjects is therefore confounded by band+window choice; it is not a clean model-class result.
- **All cells:** submitted-ensemble per-subject scores are SELECTION-CV (argmax over the per-subject candidate pool). Single-method rows are no-selection. Carry +4–6 pp expected upward bias relative to single-method cells of equivalent variance.
- **Submitted S2 (EEGNet aug, 0.8786) and S4 (stacking, 0.9857) are not produced by `benchmark.py`.** They are asserted from the original challenge submission codepath.

## Multiple-testing correction

Across 11 single methods × 6 subjects + 11 macros = 77 cells compared against the submitted ensemble. Bonferroni-adjusted α = 0.00065 (z_crit ≈ 3.41). At per-subject level the per-cell SE on a paired CV difference (n=28 per fold) is roughly 0.095, so the per-cell delta needed to survive Bonferroni is **≈32 pp**. At the macro level (paired over 6 subjects), only the deltas vs Deep4Net (~+31.7 pp) and EEGITNet (~+34.9 pp) clearly survive Bonferroni; the 11 pp delta vs the strong classical baselines does **not** reach Bonferroni significance.

## What the table does and does not support

**Defensible:**
- Under the shared 7–30 Hz / AdamW(1e-3) protocol with no per-method tuning, **all six tested deep methods underperform the per-subject adaptive ensemble** by a margin that survives uncorrected paired bootstrap.
- **All deep methods underperform pyRiemann TS / CSP+LDA at broad 7–30 Hz**, and even with a charitable +5–10 pp lift from per-method recipe tuning, the deep ceiling lands at parity with classical, not above.
- **Subject 4 stacking buys no measurable accuracy** over `CSP+LDA broad 7–30 Hz`: both reach 138/140 = 0.9857 macro CV. Stacking should be removed from S4 in any future deployment.
- **Adaptive per-subject preprocessing selection (band, window, augmentation) explains a substantial fraction of the ensemble's lead** over uniform-config single methods, more than any single deep architecture choice.

**Not defensible from this table:**
- 'No published deep method beats us on this dataset.' Reframe as: 'No fixed-config deep method tested under our shared 7-30 Hz / AdamW(1e-3) protocol matches the per-subject adaptive ensemble; whether band-tuned and recipe-tuned deep methods would close the gap is untested.'
- 'Method class is what wins on S5/S6.' Reframe as: 'Narrow-band 10-14 Hz / 2.5 s preprocessing wins on S5/S6; whether deep methods at the same band+window would close the gap is untested.'
- 'The 11 pp lead is far beyond statistical noise.' Reframe as: 'The lead vs best uniform method is +11.27 pp uncorrected; the matched-protocol delta vs best-of-N is +7.98 pp; after subtracting expected +4-6 pp selection-CV optimism the residual real advantage is approximately +5-7 pp; Bonferroni-corrected significance is reached only against Deep4Net and EEGITNet at the macro level.'

## Honest limitations of the deep-side protocol

Per the protocol-fairness audit, the deep-method side of this comparison carries known disadvantages relative to each method's source-paper recipe:
- **No early stopping / no inner validation split.** Models train for 100 fixed epochs without patience; small-N overfitting is essentially guaranteed for >100 K-parameter models (Deep4Net, EEGConformer, ATCNet).
- **Single learning rate (1e-3) shared across all six methods.** Source-paper defaults are: ShallowConvNet/Deep4Net 6.25e-4, EEGConformer 2e-4 with cosine + warmup, ATCNet 9e-4, EEGNetv4/EEGITNet 1e-3. Three of six methods are run at 2-5x their source-paper learning rate.
- **No learning-rate schedule.** All six source papers use cosine annealing.
- **Deep4Net runs trial-wise without `cropped` decoding or `MaxNormDefaultConstraint`,** the two ingredients Schirrmeister 2017 §2.5 credits with +5-7 pp on BCI IV-2a.
- **EEGConformer is fed 7-30 Hz IIR + per-trial z-scored input.** Its source paper uses raw or 0-38 Hz input; pre-filtering removes high-frequency information the conformer's later attention layer relies on.
- **No augmentation parity with the submitted S2 EEGNet** (Gaussian noise, time shift, channel dropout).
- **3 seeds** with relative-uncertainty ~50% on each std bar. Std bars are decorative, not inferential.

A v3 re-run with these protocol fixes is in progress; the headline finding (`classical baselines at 0.84 macro beat all deep methods at 0.60-0.78 macro`) is expected to weaken to `parity with classical at 0.83-0.85 macro after +5-10 pp lift from per-method recipes`, but is not expected to flip.

## Foundation models

- CBraMod / EEGPT / LaBraM are deferred to a separate study because they require non-trivial channel-mapping and resampling adapters; CBraMod was previously evaluated on Subject 1 only and reached 0.4929 (close to chance) under a lightweight recipe.
- **MIRepNet is excluded.** Its public pretraining corpus contains the Cho 2017 dataset that this benchmark draws from; using it would constitute data leakage.
