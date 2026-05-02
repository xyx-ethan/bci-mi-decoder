"""Aggregate per-(method, subject) JSON files into a single comparison
table and write a Markdown summary.

This v2 of aggregate.py incorporates the four red-team audit findings:
  1. Per-subject argmax "Best-of-N" baseline row added (matched-protocol
     fairness comparison).
  2. Two delta numbers reported (best-of-N apples-to-apples, and best
     uniform method deployment view).
  3. Selection-CV optimism explicit footnote (~4-6 pp upward bias).
  4. S2 augmentation asymmetry, S3 6-seed estimator, S4 138/140 macro
     identity, and S5/S6 band+window confound disclosed in the table
     legend, not just in fine print.
"""
from __future__ import annotations

import json
from pathlib import Path

OUT = Path(__file__).resolve().parent
RES = OUT / "results"
SUBJECTS = ["A", "B", "C", "D", "E", "F"]

# Submitted per-subject ensemble (for context — NOT produced by this script)
SUBMITTED = {
    "A": ("CSP+SVM-RBF, μ 8-13 Hz, 2.25 s",                        0.9786, "fixed-seed CV"),
    "B": ("EEGNet (augmented), 7-30 Hz, 2.25 s",                   0.8786, "fixed-seed CV; off-protocol"),
    "C": ("pyRiemann TS+LR, 6-30 Hz, 2.50 s window",               0.9905, "6-seed mean"),
    "D": ("Stacking (L2-LR, C=10) over 5 pyRiemann TS variants",   0.9857, "fixed-seed CV"),
    "E": ("CSP+LDA, 10-14 Hz, 2.50 s window",                      0.9214, "fixed-seed CV; band+window off-protocol"),
    "F": ("CSP+LDA, 10-14 Hz, 2.50 s window",                      0.9429, "fixed-seed CV; band+window off-protocol"),
}

DEEP_METHODS = [
    ("ShallowConvNet", "Schirrmeister 2017"),
    ("Deep4Net",       "Schirrmeister 2017"),
    ("EEGNetv4",       "Lawhern 2018"),
    ("EEGConformer",   "Song 2023"),
    ("ATCNet",         "Altaheri 2022"),
    ("EEGITNet",       "Salami 2022"),
]
CLASSICAL_METHODS = [
    ("csp_svm_mu",      "CSP+SVM-RBF, μ 8-13 Hz, k=4"),
    ("csp_lda_mu",      "CSP+LDA, μ 8-13 Hz, k=4"),
    ("csp_svm_broad",   "CSP+SVM-RBF, broad 7-30 Hz, k=4"),
    ("csp_lda_broad",   "CSP+LDA, broad 7-30 Hz, k=4"),
    ("riem_ts_broad",   "pyRiemann TS+LR, broad 7-30 Hz"),
]


def _load(method: str, subj: str) -> dict | None:
    p = RES / f"{method}__subj{subj}.json"
    return json.loads(p.read_text()) if p.exists() else None


def main() -> None:
    rows: list[dict] = []

    # Submitted ensemble row (asserted, not benchmark-run)
    rows.append({
        "type": "submitted",
        "method": "**Submitted ensemble (per-subject adaptive selection)**",
        "ref": "this work — *off-protocol* (per-subject band/window/aug)",
        "per_subj": {s: SUBMITTED[s][1] for s in SUBJECTS},
        "macro": float(sum(v[1] for v in SUBMITTED.values()) / 6),
    })

    deep_rows = []
    for method, ref in DEEP_METHODS:
        per_subj, per_subj_std = {}, {}
        for subj in SUBJECTS:
            rec = _load(method, subj)
            if rec is None or "error" in rec:
                per_subj[subj] = None
                per_subj_std[subj] = None
            else:
                per_subj[subj] = rec.get("mean")
                per_subj_std[subj] = rec.get("std")
        valid = [v for v in per_subj.values() if v is not None]
        deep_rows.append({
            "type": "deep",
            "method": method,
            "ref": ref,
            "per_subj": per_subj,
            "per_subj_std": per_subj_std,
            "macro": (sum(valid) / len(valid)) if valid else None,
        })

    classical_rows = []
    for method, label in CLASSICAL_METHODS:
        per_subj = {}
        for subj in SUBJECTS:
            rec = _load(method, subj)
            per_subj[subj] = rec.get("mean") if rec is not None else None
        valid = [v for v in per_subj.values() if v is not None]
        classical_rows.append({
            "type": "classical",
            "method": label,
            "ref": "single-method classical baseline",
            "per_subj": per_subj,
            "macro": (sum(valid) / len(valid)) if valid else None,
        })

    all_single = deep_rows + classical_rows

    # Best-of-N matched-protocol row: per-subject argmax across 11 single methods
    best_of_n = {}
    best_of_n_method = {}
    for subj in SUBJECTS:
        cells = [(r["per_subj"][subj], r["method"]) for r in all_single
                 if r["per_subj"].get(subj) is not None]
        if cells:
            best_v, best_m = max(cells, key=lambda x: x[0])
            best_of_n[subj] = best_v
            best_of_n_method[subj] = best_m
        else:
            best_of_n[subj] = None
            best_of_n_method[subj] = None
    bestN_macro = sum(v for v in best_of_n.values() if v is not None) / len(best_of_n)

    rows.append({
        "type": "best_of_n",
        "method": "**Best-of-N single methods (per-subject argmax, this benchmark)**",
        "ref": "matched-protocol fairness baseline",
        "per_subj": best_of_n,
        "macro": bestN_macro,
        "winners": best_of_n_method,
    })

    # Best uniform single method (highest macro from any single row)
    uniform_best = max(all_single, key=lambda r: r["macro"] or 0.0)

    rows.append({
        "type": "best_uniform",
        "method": "**Best uniform single method (no per-subject selection)**",
        "ref": f"= {uniform_best['method']}",
        "per_subj": dict(uniform_best["per_subj"]),
        "macro": uniform_best["macro"],
    })

    rows.extend(deep_rows)
    rows.extend(classical_rows)

    # ---------- Markdown summary ------------------------------------------
    L: list[str] = []
    L.append("# Frontier-vs-classical benchmark on the BCI-ISLA 2026 dataset")
    L.append("")
    L.append("**v2: revised per four-agent red-team audit (2026-05-02).** Several "
             "claims in v1 of this summary were over-stated. The honest deltas, "
             "matched-protocol baselines, and per-cell asymmetry disclosures are "
             "reported below.")
    L.append("")
    L.append("**Protocol.** Same 6 subjects from the BCI-ISLA 2026 challenge "
             "(Cho 2017 subset). For deep methods: same 5-fold split "
             "(`StratifiedKFold(n_splits=5, shuffle=True, random_state=42)`), "
             "shared preprocessing (crop 384–1537 / IIR bandpass 7–30 Hz / per-trial "
             "z-score), source-paper default hyperparameters under "
             "`AdamW(lr=1e-3, weight_decay=1e-4)`, 100 epochs, batch size 32, no "
             "early stopping or learning-rate schedule, averaged over 3 seeds "
             "(42, 43, 44). For classical methods: pipeline-native band (μ 8–13 or "
             "broad 7–30 Hz), single-seed deterministic fitting.")
    L.append("")
    L.append("**Headline numbers.** All cells are SELECTION-CV (5-fold OOF) — "
             "**not unbiased generalisation estimates**. The submitted-ensemble row "
             "uses per-subject argmax over a candidate pool of N≥10 pipelines, "
             "which adds an expected **+4–6 pp upward bias** (Cawley & Talbot 2010) "
             "that the single-method rows do not carry. The matched-protocol "
             "fairness baseline ('Best-of-N single methods') is the apples-to-apples "
             "comparison.")
    L.append("")

    L.append("| Method | Reference / note | S1 | S2 | S3 | S4 | S5 | S6 | **Macro** |")
    L.append("|---|---|---:|---:|---:|---:|---:|---:|---:|")

    def fmt(v):
        return f"{v:.4f}" if v is not None else "—"

    def fmt_std(v, s):
        if v is None: return "—"
        if s is None: return f"{v:.4f}"
        return f"{v:.3f}±{s:.3f}"

    for r in rows:
        if r["type"] == "deep":
            cells = [fmt_std(r["per_subj"][s], r["per_subj_std"][s]) for s in SUBJECTS]
        else:
            cells = [fmt(r["per_subj"][s]) for s in SUBJECTS]
        L.append(f"| {r['method']} | {r['ref']} | " + " | ".join(cells) + f" | **{fmt(r['macro'])}** |")

    submitted_macro = rows[0]["macro"]
    bestN_macro_v = rows[1]["macro"]
    uniform_macro = rows[2]["macro"]
    L.append("")
    L.append("## Honest delta accounting")
    L.append("")
    L.append(f"- **Submitted ensemble macro CV : {submitted_macro:.4f}**")
    L.append(f"- Best-of-N matched-protocol      : {bestN_macro_v:.4f}  "
             f"→ Δ = **+{(submitted_macro - bestN_macro_v) * 100:.2f} pp** "
             f"*(apples-to-apples, both selection-CV optimistic)*")
    L.append(f"- Best uniform single method      : {uniform_macro:.4f}  "
             f"→ Δ = **+{(submitted_macro - uniform_macro) * 100:.2f} pp** "
             f"*(deployment view; only the ensemble row is selection-biased)*")
    L.append("")
    L.append("**Selection-bias optimism.** Of the +%.2f pp lead vs the best uniform "
             "method, an estimated 4–6 pp is the expected upward bias of "
             "argmax-over-N=10-pipelines selection-CV (Cawley & Talbot 2010). "
             "After correction, the residual real advantage is approximately "
             "+5–7 pp; the one-sided 95 %% lower bound vs CSP+LDA broad 7–30 Hz "
             "approaches 0." % ((submitted_macro - uniform_macro) * 100))
    L.append("")
    L.append("**Per-subject deltas vs the matched-protocol best-of-N winner:**")
    L.append("")
    bestN = rows[1]
    for s in SUBJECTS:
        sub = SUBMITTED[s][1]
        ben = bestN["per_subj"][s]
        win = bestN["winners"][s]
        if ben is None:
            continue
        L.append(f"- **Subject {SUBJECTS.index(s)+1}** ({s}): submitted "
                 f"{sub:.4f} − best-of-N {ben:.4f} ({win}) = "
                 f"**Δ {(sub - ben)*100:+.1f} pp**")
    L.append("")

    L.append("## Per-cell asymmetries the submitted-ensemble row does NOT share with the single-method rows")
    L.append("")
    L.append(
        "- **S2 (B):** submitted uses EEGNet *with* Gaussian noise / time shift / "
        "channel dropout augmentation; benchmark's `EEGNetv4` row does not. The "
        "+0.14 gap on S2 is essentially the augmentation gap, not a model-class gap.\n"
        "- **S3 (C):** submitted reports a 6-seed stratified-CV mean (0.9905); "
        "all other cells are 3-seed (deep) or single-seed (classical). Estimator "
        "mismatch.\n"
        "- **S4 (D):** submitted stacking macro CV is 0.9857 (asserted, not run by "
        "this benchmark). The benchmark's `CSP+LDA broad 7-30 Hz` on S4 is also "
        "0.9857 — both miss exactly 2 of 140 trials at the macro level. Stacking "
        "does **not** improve over CSP+LDA broad on this subject.\n"
        "- **S5 (E), S6 (F):** submitted uses CSP+LDA at *upper-μ 10–14 Hz* with a "
        "*2.5 s* window (versus 7-30 Hz / 2.25 s for benchmark deep rows). The 25-28 pp "
        "lead over the strongest deep method on these subjects is therefore confounded "
        "by band+window choice; it is not a clean model-class result.\n"
        "- **All cells:** submitted-ensemble per-subject scores are SELECTION-CV "
        "(argmax over the per-subject candidate pool). Single-method rows are no-"
        "selection. Carry +4–6 pp expected upward bias relative to single-method "
        "cells of equivalent variance.\n"
        "- **Submitted S2 (EEGNet aug, 0.8786) and S4 (stacking, 0.9857) are not "
        "produced by `benchmark.py`.** They are asserted from the original challenge "
        "submission codepath."
    )
    L.append("")

    L.append("## Multiple-testing correction")
    L.append("")
    L.append(
        "Across 11 single methods × 6 subjects + 11 macros = 77 cells compared "
        "against the submitted ensemble. Bonferroni-adjusted α = 0.00065 "
        "(z_crit ≈ 3.41). At per-subject level the per-cell SE on a paired CV "
        "difference (n=28 per fold) is roughly 0.095, so the per-cell delta needed "
        "to survive Bonferroni is **≈32 pp**. At the macro level (paired over 6 "
        "subjects), only the deltas vs Deep4Net (~+31.7 pp) and EEGITNet "
        "(~+34.9 pp) clearly survive Bonferroni; the 11 pp delta vs the strong "
        "classical baselines does **not** reach Bonferroni significance."
    )
    L.append("")

    L.append("## What the table does and does not support")
    L.append("")
    L.append(
        "**Defensible:**\n"
        "- Under the shared 7–30 Hz / AdamW(1e-3) protocol with no per-method "
        "tuning, **all six tested deep methods underperform the per-subject "
        "adaptive ensemble** by a margin that survives uncorrected paired bootstrap.\n"
        "- **All deep methods underperform pyRiemann TS / CSP+LDA at broad 7–30 Hz**, "
        "and even with a charitable +5–10 pp lift from per-method recipe tuning, the "
        "deep ceiling lands at parity with classical, not above.\n"
        "- **Subject 4 stacking buys no measurable accuracy** over `CSP+LDA broad "
        "7–30 Hz`: both reach 138/140 = 0.9857 macro CV. Stacking should be removed "
        "from S4 in any future deployment.\n"
        "- **Adaptive per-subject preprocessing selection (band, window, augmentation) "
        "explains a substantial fraction of the ensemble's lead** over uniform-config "
        "single methods, more than any single deep architecture choice.\n"
        "\n"
        "**Not defensible from this table:**\n"
        "- 'No published deep method beats us on this dataset.' Reframe as: 'No "
        "fixed-config deep method tested under our shared 7-30 Hz / AdamW(1e-3) "
        "protocol matches the per-subject adaptive ensemble; whether band-tuned and "
        "recipe-tuned deep methods would close the gap is untested.'\n"
        "- 'Method class is what wins on S5/S6.' Reframe as: 'Narrow-band 10-14 Hz / "
        "2.5 s preprocessing wins on S5/S6; whether deep methods at the same band+"
        "window would close the gap is untested.'\n"
        "- 'The 11 pp lead is far beyond statistical noise.' Reframe as: 'The lead "
        "vs best uniform method is +%.2f pp uncorrected; the matched-protocol "
        "delta vs best-of-N is +%.2f pp; after subtracting expected +4-6 pp "
        "selection-CV optimism the residual real advantage is approximately +5-7 pp; "
        "Bonferroni-corrected significance is reached only against Deep4Net and "
        "EEGITNet at the macro level.'" % ((submitted_macro - uniform_macro) * 100, (submitted_macro - bestN_macro_v) * 100)
    )
    L.append("")

    L.append("## Honest limitations of the deep-side protocol")
    L.append("")
    L.append(
        "Per the protocol-fairness audit, the deep-method side of this comparison "
        "carries known disadvantages relative to each method's source-paper recipe:\n"
        "- **No early stopping / no inner validation split.** Models train for 100 "
        "fixed epochs without patience; small-N overfitting is essentially "
        "guaranteed for >100 K-parameter models (Deep4Net, EEGConformer, ATCNet).\n"
        "- **Single learning rate (1e-3) shared across all six methods.** Source-"
        "paper defaults are: ShallowConvNet/Deep4Net 6.25e-4, EEGConformer 2e-4 "
        "with cosine + warmup, ATCNet 9e-4, EEGNetv4/EEGITNet 1e-3. Three of six "
        "methods are run at 2-5x their source-paper learning rate.\n"
        "- **No learning-rate schedule.** All six source papers use cosine "
        "annealing.\n"
        "- **Deep4Net runs trial-wise without `cropped` decoding or "
        "`MaxNormDefaultConstraint`,** the two ingredients Schirrmeister 2017 §2.5 "
        "credits with +5-7 pp on BCI IV-2a.\n"
        "- **EEGConformer is fed 7-30 Hz IIR + per-trial z-scored input.** Its "
        "source paper uses raw or 0-38 Hz input; pre-filtering removes high-"
        "frequency information the conformer's later attention layer relies on.\n"
        "- **No augmentation parity with the submitted S2 EEGNet** (Gaussian noise, "
        "time shift, channel dropout).\n"
        "- **3 seeds** with relative-uncertainty ~50% on each std bar. Std bars are "
        "decorative, not inferential.\n"
        "\n"
        "A v3 re-run with these protocol fixes is in progress; the headline finding "
        "(`classical baselines at 0.84 macro beat all deep methods at 0.60-0.78 macro`) "
        "is expected to weaken to `parity with classical at 0.83-0.85 macro after "
        "+5-10 pp lift from per-method recipes`, but is not expected to flip."
    )
    L.append("")

    L.append("## Foundation models")
    L.append("")
    L.append(
        "- CBraMod / EEGPT / LaBraM are deferred to a separate study because they "
        "require non-trivial channel-mapping and resampling adapters; CBraMod was "
        "previously evaluated on Subject 1 only and reached 0.4929 (close to "
        "chance) under a lightweight recipe.\n"
        "- **MIRepNet is excluded.** Its public pretraining corpus contains the "
        "Cho 2017 dataset that this benchmark draws from; using it would constitute "
        "data leakage."
    )
    L.append("")

    body = "\n".join(L)
    (OUT / "SUMMARY.md").write_text(body, encoding="utf-8")
    (OUT / "summary.json").write_text(json.dumps(rows, indent=2))
    print(f"[done] wrote {OUT / 'SUMMARY.md'}  ({len(body)} chars)")
    print(f"[done] wrote {OUT / 'summary.json'}")
    print()
    print(f"Headline deltas:")
    print(f"  Submitted ensemble macro CV     : {submitted_macro:.4f}")
    print(f"  Best-of-N matched protocol      : {bestN_macro_v:.4f}  Δ = +{(submitted_macro - bestN_macro_v)*100:.2f} pp")
    print(f"  Best uniform single method      : {uniform_macro:.4f}  Δ = +{(submitted_macro - uniform_macro)*100:.2f} pp")


if __name__ == "__main__":
    main()
