# Changelog

## 0.1.0 — 2026-04

Initial public release.

- Per-subject adaptive ensemble over CSP-SVM, pyRiemann tangent-space,
  and stacking meta-learner.
- Test-time window augmentation for subjects that benefit from longer
  windows.
- Reproducible 5-fold cross-validation with fixed seed.
- Held-out test accuracy 0.93 (≈335/360 correct; Wilson 95 % CI ≈
  [0.900, 0.953]); macro-average 5-fold selection-CV 0.9512, or 0.9496
  with a Subject 3 6-seed robustness substitution.
- Documentation explicitly distinguishes selection-CV (used to pick
  the per-subject pipeline; potentially optimistic) from the held-out
  test estimate; full leakage-control checklist and a Limitations
  section accompany the methodology.
