# Experiments — frontier-vs-classical benchmarks

Reproduction scripts for the comparative analyses cited in
`docs/results.md` and the project research write-up. These scripts are
**not part of the package's main API surface**; they require a few extra
runtime dependencies (`braindecode>=1.4`, `torch>=2.0`) and a working
GPU for tractable wall-time, and are intended for reviewers and
end-users who want to independently reproduce the benchmark numbers.

## Files

| File | Purpose | Wall time |
|------|---------|-----------|
| `benchmark.py` | v1 — frontier deep methods (ShallowConvNet, Deep4Net, EEGNetv4, EEGConformer, ATCNet, EEGITNet) vs. classical baselines under a shared 7–30 Hz / AdamW(1e-3) protocol with no early stopping or per-method hyperparameter tuning | ~70–90 min on RTX 4070 |
| `aggregate.py` | Reads `results/*.json` produced by `benchmark.py`, writes a Markdown comparison table (`SUMMARY.md`) including the matched-protocol best-of-N baseline and explicit selection-bias / multiple-testing disclosures | <1 s |
| `SUMMARY.md` | The aggregated comparison table (v1 + four-agent red-team audit fixes). The audit findings and honest delta accounting are inline. | — |
| `cowse_imitation_S2.py` | A 14-base heterogeneous-stack ablation on Subject 2 (the bottleneck subject), implementing the COWSE-style diversity-weighted meta-learner. Demonstrates that diversity-aware stacking does **not** exceed the strongest single classical base on this subject. | ~3 min |

## Reproducing v1

```bash
pip install -e ".[bench]"        # or:  pip install braindecode>=1.4 torch>=2.0
python experiments/benchmark.py all
python experiments/aggregate.py
```

Outputs land in `experiments/results/*.json` and `experiments/SUMMARY.md`.

## Honest limitations

`SUMMARY.md` documents these in detail. Briefly:

1. The submitted-ensemble row uses **per-subject preprocessing**
   (band, window, augmentation) that the single-method rows do not.
   The honest matched-protocol baseline is the "Best-of-N single
   methods" row.
2. Deep methods are run with a single shared learning rate (1e-3) and
   no schedule. The protocol-fairness audit flagged that several
   methods would benefit from per-method recipes (Schirrmeister 2017
   suggests 6.25e-4 + cropped decoding for ShallowConvNet/Deep4Net;
   Song 2023 specifies 2e-4 + cosine + warmup for EEGConformer).
   A v2 re-run with these per-method recipes is in progress.
3. 3-seed standard deviations have ≈50 % relative uncertainty and
   should not be used to rank methods.
4. The 11.27 pp macro lead vs the best uniform single method shrinks
   to **+7.98 pp** vs the matched-protocol best-of-N row, of which an
   estimated 4–6 pp is the expected upward bias of argmax-over-N
   selection-CV (Cawley & Talbot 2010).

## What this experiment supports / does not support

**Supports** (defensible):

- Under the shared 7–30 Hz / AdamW(1e-3) protocol, no tested deep
  method beats the per-subject adaptive ensemble.
- All deep methods underperform `pyRiemann TS+LR` and `CSP+LDA` at
  broad 7–30 Hz on this dataset.
- On Subject 4, `CSP+LDA broad 7–30 Hz` matches the submitted
  stacking pipeline at 138/140 macro accuracy. Stacking buys nothing
  measurable on this subject.

**Does not support** (over-claims to avoid):

- "No published deep method matches us." Per-method recipe tuning,
  per-subject band/window selection, and S2-style augmentation are
  not granted to the deep methods here.
- "Adaptive selection beats deep architectures by 11 pp." That figure
  conflates real signal (~5–7 pp) with selection-CV optimism (~4–6 pp).
- "The 28 pp lead on Subjects 5/6 is method-class superiority." It is
  band+window confound: the ensemble uses 10–14 Hz / 2.5 s; the deep
  rows use 7–30 Hz / 2.25 s.
