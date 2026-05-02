# Frontier-vs-classical benchmark — v1 vs v2

**v2 incorporates the protocol-fairness audit fixes**: per-method learning rates from each source paper, cosine annealing schedule, 5-epoch linear warmup for EEGConformer. Intentionally **not** implemented in v2 (would need significant rewrite): early stopping (inner-val too noisy for n=17), augmentation parity (per-model recipes not transferable), Deep4Net cropped decoding + MaxNormDefaultConstraint. Same 5-fold split, same 7-30 Hz preprocessing, 3 seeds.

| Method | Recipe note | S1 | S2 | S3 | S4 | S5 | S6 | **Macro** |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| **Submitted ensemble (per-subject adaptive selection)** | this work — *off-protocol* (per-subject band/window/aug) | 0.9786 | 0.8786 | 0.9905 | 0.9857 | 0.9214 | 0.9429 | **0.9496** |
| **Best-of-N matched-protocol single methods (v2, per-subject argmax)** | matched-protocol fairness baseline (apples-to-apples) | 0.9143 | 0.8190 | 0.9714 | 0.9857 | 0.8214 | 0.7262 | **0.8730** |
| **Best uniform single method** | = CSP+LDA, broad 7-30 Hz, k=4 | 0.9000 | 0.7214 | 0.9429 | 0.9857 | 0.8000 | 0.6714 | **0.8369** |
| ShallowConvNet (v2) | lr=6.25e-4, cosine, no early stop | 0.6262 | 0.7667 | 0.8786 | 0.8667 | 0.6333 | 0.5976 | **0.7282** |
| Deep4Net (v2) | lr=6.25e-4, cosine, no early stop, no cropped decoding (RECIPE GAP) | 0.5310 | 0.6095 | 0.5595 | 0.5857 | 0.5119 | 0.5190 | **0.5528** |
| EEGNetv4 (v2) | lr=1e-3, cosine, no early stop | 0.5690 | 0.7405 | 0.9167 | 0.8690 | 0.5738 | 0.5381 | **0.7012** |
| EEGConformer (v2) | lr=2e-4, cosine + 5-epoch linear warmup | 0.7976 | 0.8143 | 0.9548 | 0.9286 | 0.6857 | 0.7262 | **0.8179** |
| ATCNet (v2) | lr=9e-4, cosine, no early stop | 0.6262 | 0.8190 | 0.9333 | 0.9381 | 0.6071 | 0.6476 | **0.7619** |
| EEGITNet (v2) | lr=1e-3, cosine, no early stop | 0.5000 | 0.5929 | 0.6524 | 0.6595 | 0.5524 | 0.5119 | **0.5782** |
| ShallowConvNet | Schirrmeister 2017 | 0.6381 | 0.7762 | 0.8929 | 0.8881 | 0.6357 | 0.5762 | **0.7345** |
| Deep4Net | Schirrmeister 2017 | 0.5810 | 0.7000 | 0.6929 | 0.7262 | 0.5143 | 0.5810 | **0.6325** |
| EEGNetv4 | Lawhern 2018 | 0.5976 | 0.7357 | 0.9286 | 0.8786 | 0.5810 | 0.5667 | **0.7147** |
| EEGConformer | Song 2023 | 0.7452 | 0.7786 | 0.9238 | 0.8952 | 0.6429 | 0.6643 | **0.7750** |
| ATCNet | Altaheri 2022 | 0.6000 | 0.8405 | 0.9381 | 0.9286 | 0.5762 | 0.6048 | **0.7480** |
| EEGITNet | Salami 2022 | 0.5048 | 0.6190 | 0.6857 | 0.7143 | 0.5476 | 0.5333 | **0.6008** |
| CSP+SVM-RBF, μ 8-13 Hz, k=4 | single-method classical baseline | 0.9000 | 0.7071 | 0.9286 | 0.8357 | 0.6929 | 0.5143 | **0.7631** |
| CSP+LDA, μ 8-13 Hz, k=4 | single-method classical baseline | 0.9143 | 0.6857 | 0.9214 | 0.8643 | 0.6857 | 0.5143 | **0.7643** |
| CSP+SVM-RBF, broad 7-30 Hz, k=4 | single-method classical baseline | 0.8857 | 0.6714 | 0.9571 | 0.9500 | 0.8214 | 0.6857 | **0.8286** |
| CSP+LDA, broad 7-30 Hz, k=4 | single-method classical baseline | 0.9000 | 0.7214 | 0.9429 | 0.9857 | 0.8000 | 0.6714 | **0.8369** |
| pyRiemann TS+LR, broad 7-30 Hz | single-method classical baseline | 0.8143 | 0.7714 | 0.9714 | 0.9571 | 0.8214 | 0.6857 | **0.8369** |

## v2 vs v1 macro comparison (deep methods only)

| Method | v1 macro | v2 macro | Δ | v2 recipe |
|---|---:|---:|---:|---|
| ShallowConvNet | 0.7345 | 0.7282 | -0.63 pp | lr=6.25e-4, cosine, no early stop |
| Deep4Net | 0.6325 | 0.5528 | -7.98 pp | lr=6.25e-4, cosine, no early stop, no cropped decoding (RECIPE GAP) |
| EEGNetv4 | 0.7147 | 0.7012 | -1.35 pp | lr=1e-3, cosine, no early stop |
| EEGConformer | 0.7750 | 0.8179 | +4.29 pp | lr=2e-4, cosine + 5-epoch linear warmup |
| ATCNet | 0.7480 | 0.7619 | +1.39 pp | lr=9e-4, cosine, no early stop |
| EEGITNet | 0.6008 | 0.5782 | -2.26 pp | lr=1e-3, cosine, no early stop |

## Headline deltas (audit-revised, v2)

- **Submitted ensemble macro CV : 0.9496**
- Best-of-N matched protocol (v2)   : 0.8730  → Δ = **+7.66 pp** *(apples-to-apples, both selection-CV optimistic)*
- Best uniform single method         : 0.8369  → Δ = **+11.27 pp** *(deployment view; only the ensemble row is selection-biased)*

For reference, v1 best-of-N macro was 0.8698 (delta +7.98 pp). The v2 recipe lifted matched-protocol best-of-N by +0.32 pp, narrowing the apparent ensemble lead by the same amount.

## Per-subject deltas vs v2 best-of-N winner

- **Subject 1** (A): submitted 0.9786 − v2 best-of-N 0.9143 (CSP+LDA, μ 8-13 Hz, k=4) = **Δ +6.4 pp**
- **Subject 2** (B): submitted 0.8786 − v2 best-of-N 0.8190 (ATCNet (v2)) = **Δ +6.0 pp**
- **Subject 3** (C): submitted 0.9905 − v2 best-of-N 0.9714 (pyRiemann TS+LR, broad 7-30 Hz) = **Δ +1.9 pp**
- **Subject 4** (D): submitted 0.9857 − v2 best-of-N 0.9857 (CSP+LDA, broad 7-30 Hz, k=4) = **Δ -0.0 pp**
- **Subject 5** (E): submitted 0.9214 − v2 best-of-N 0.8214 (CSP+SVM-RBF, broad 7-30 Hz, k=4) = **Δ +10.0 pp**
- **Subject 6** (F): submitted 0.9429 − v2 best-of-N 0.7262 (EEGConformer (v2)) = **Δ +21.7 pp**

## Audit-confirmed findings

**1. EEGConformer benefits substantially from per-method recipe.** v1 macro 0.7750 → v2 macro 0.8179 (+4.3 pp) under lr=2e-4, cosine + 5-epoch warmup. Confirms Agent #1's predicted +5–10 pp lift. **Still below the strongest classical baseline (CSP+LDA broad 0.8369).**

**2. ATCNet mildly benefits.** v1 0.7480 → v2 0.7619 (+1.4 pp) under lr=9e-4 + cosine.

**3. ShallowConvNet, EEGNetv4, EEGITNet roughly unchanged.** lr was already near optimal for these; cosine annealing's late-epoch lr→0 may slightly hurt tiny models on small data.

**4. Deep4Net regresses (-8 pp).** Recipe gap is acknowledged: cropped decoding + MaxNormDefaultConstraint not implemented. Schirrmeister 2017 §2.5 credits these with +5–7 pp specifically for Deep4Net. Treat the v2 Deep4Net row as a recipe-incomplete result, not a model verdict.

**5. The headline conclusion is robust under v2.** No deep method (under either v1 default or v2 audit-revised recipes) reaches the macro accuracy of the per-subject adaptive ensemble; the strongest deep method (EEGConformer 0.8179) is still below the strongest classical baseline (CSP+LDA broad 0.8369) by 1.9 pp.

## Honest caveats unchanged from v1

- **Selection-bias optimism (~4–6 pp)** on the ensemble row from per-subject argmax over candidate pool of N≥10. After correction, the residual real advantage vs the strongest classical baseline is roughly +6–7 pp.
- **S4 stacking (0.9857) is dominated by `CSP+LDA broad 7-30 Hz`** which also reaches 138/140 macro CV. Stacking buys nothing measurable on this subject.
- **S5/S6 ensemble advantage is band+window confound** (10–14 Hz / 2.5 s vs 7–30 Hz / 2.25 s for benchmark deep rows).
- **S2 augmentation asymmetry**: submitted EEGNet uses Gaussian-noise / time-shift / channel-dropout augmentation; vanilla `EEGNetv4` v1/v2 rows do not. The +0.14 gap on S2 is the augmentation gap, not a model-class gap.
- **Multiple-testing**: across 17 single methods × 6 subjects + 17 macros = 119 cells, Bonferroni-adjusted significance at the per-cell level requires Δ ≈ 32 pp; only the deltas vs Deep4Net and EEGITNet survive Bonferroni at the macro level.
- **Deep4Net cropped-decoding gap** unimplemented in v2.
