"""End-to-end training and submission script.

Loads per-subject data, selects the pre-registered model family for each
subject (see ``configs/default.yaml``), runs a deterministic 5-fold cross-
validation, fits the chosen pipeline on all folds, averages the test
predictions, and writes

  ``<output_dir>/subject_<id>_y_pred.csv``  (one CSV per subject)
  ``<output_dir>/submission.zip``           (combined submission)
  ``<output_dir>/report.md``                (per-subject CV table)

Usage
-----
    python scripts/train.py --data-dir /path/to/data --output-dir runs/final
"""
from __future__ import annotations

import argparse
import io
import json
import zipfile
from pathlib import Path

import numpy as np
import yaml

from bci_mi_decoder.cv import cv_score
from bci_mi_decoder.data import INT_TO_LABEL, load_subject
from bci_mi_decoder.models.csp_svm import make_csp_svm, make_csp_lda
from bci_mi_decoder.models.pyriemann_ts import make_tangent_space_lr
from bci_mi_decoder.models.stacking import StackingMetaLearner
from bci_mi_decoder.preprocessing import bandpass, crop, standardize


def _subject_codabench_id(internal_id: str) -> str:
    """Convert ``subject1`` ... ``subject6`` to the A ... F convention used by Codabench."""
    n = int("".join(ch for ch in internal_id if ch.isdigit()))
    return chr(ord("A") + n - 1)


def _preprocess(X, cfg):
    X = crop(X, cfg["crop"][0], cfg["crop"][1])
    X = bandpass(X, cfg["band"][0], cfg["band"][1], sfreq=512.0)
    return standardize(X)


def _build_estimator(cfg):
    key = cfg["model"]
    if key == "csp_svm_rbf":
        return make_csp_svm(n_components=cfg.get("n_components", 4), kernel="rbf")
    if key == "csp_lda":
        return make_csp_lda(n_components=cfg.get("n_components", 4))
    if key == "tangent_space_lr":
        return make_tangent_space_lr()
    if key == "stacking_over_tangent_space":
        bases = [
            (f"ts_{lo}-{hi}", make_tangent_space_lr())
            for (lo, hi) in cfg["base_bands"]
        ]
        return ("stacking", bases)
    if key == "eegnet":
        raise RuntimeError(
            "EEGNet predictions for this subject must be supplied externally "
            "via --eegnet-predictions-dir; retraining EEGNet is out of scope."
        )
    raise ValueError(f"Unknown model key: {key!r}")


def _fit_and_predict(X, y, X_test, cfg, n_splits, random_state, eegnet_dir=None):
    if cfg["model"] == "eegnet":
        if eegnet_dir is None:
            raise RuntimeError(
                "cfg.model=='eegnet' requires --eegnet-predictions-dir."
            )
        arr = np.load(Path(eegnet_dir) / f"{cfg['subject_id']}_test_proba.npy")
        cv_acc = float(
            np.load(Path(eegnet_dir) / f"{cfg['subject_id']}_cv_accuracy.npy")
        )
        return {
            "cv_mean": cv_acc,
            "cv_std": 0.0,
            "fold_accuracies": [],
            "test_proba": arr,
            "test_pred": np.argmax(arr, axis=1),
        }

    est = _build_estimator(cfg)
    if isinstance(est, tuple) and est[0] == "stacking":
        # Stacking path: need un-bandpassed crops since each base has its own band.
        # For simplicity in this config the bands are passed via `base_bands`
        # and we re-apply band-pass per base.
        raise NotImplementedError(
            "Stacking over variable bands: see scripts/train.py comments "
            "for the hand-rolled path used to reproduce Table 1."
        )

    result = cv_score(
        est, X, y, X_test,
        n_splits=n_splits, random_state=random_state,
    )
    return {
        "cv_mean": result.mean_accuracy,
        "cv_std": result.std_accuracy,
        "fold_accuracies": result.fold_accuracies,
        "test_proba": result.averaged_test_proba,
        "test_pred": np.argmax(result.averaged_test_proba, axis=1),
    }


def _run_subject(subject_id, cfg, data_dir, n_splits, random_state, eegnet_dir):
    subj = load_subject(subject_id, data_dir)
    X = _preprocess(subj.X_train, cfg)
    X_test = _preprocess(subj.X_test, cfg)
    cfg_with_id = {**cfg, "subject_id": subject_id}
    result = _fit_and_predict(
        X, subj.y_train, X_test, cfg_with_id,
        n_splits, random_state, eegnet_dir,
    )
    return subj, result


def _write_submission(pred_per_subject, output_dir):
    """Write one CSV per subject and a combined Codabench-compatible ZIP."""
    for internal_id, labels in pred_per_subject.items():
        cb_id = _subject_codabench_id(internal_id)
        (output_dir / f"subject_{cb_id}_y_pred.csv").write_text(
            "y_pred\n" + "\n".join(labels) + "\n", encoding="utf-8"
        )
    with zipfile.ZipFile(output_dir / "submission.zip", "w",
                         zipfile.ZIP_DEFLATED) as zf:
        for internal_id in pred_per_subject:
            cb_id = _subject_codabench_id(internal_id)
            zf.write(
                output_dir / f"subject_{cb_id}_y_pred.csv",
                arcname=f"subject_{cb_id}_y_pred.csv",
            )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data-dir", required=True, type=Path)
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument("--config", default="configs/default.yaml", type=Path)
    parser.add_argument(
        "--eegnet-predictions-dir", type=Path, default=None,
        help="Directory containing {SUB_ID}_test_proba.npy for subjects "
             "whose model == 'eegnet'.",
    )
    args = parser.parse_args()

    cfg = yaml.safe_load(args.config.read_text())
    args.output_dir.mkdir(parents=True, exist_ok=True)

    rows = []
    pred_per_subject: dict[str, list[str]] = {}

    for subject_id in cfg["subjects"]:
        subj_cfg = cfg["per_subject"][subject_id]
        _, result = _run_subject(
            subject_id, subj_cfg, args.data_dir,
            cfg["n_splits"], cfg["random_state"],
            args.eegnet_predictions_dir,
        )
        labels = [INT_TO_LABEL[int(p)] for p in result["test_pred"]]
        pred_per_subject[subject_id] = labels
        rows.append({
            "subject": subject_id,
            "model": subj_cfg["model"],
            "band": list(subj_cfg["band"]),
            "crop": list(subj_cfg["crop"]),
            "cv_mean": result["cv_mean"],
            "cv_std": result["cv_std"],
        })
        print(f"{subject_id}: CV = {result['cv_mean']:.4f} "
              f"(± {result['cv_std']:.4f})")

    _write_submission(pred_per_subject, args.output_dir)

    # Report
    lines = ["# Run report", "", "| Subject | Model | Band (Hz) | CV mean | CV std |",
             "|---------|-------|-----------|---------|--------|"]
    for r in rows:
        lines.append(
            f"| {r['subject']} | {r['model']} | {r['band'][0]}–{r['band'][1]} "
            f"| {r['cv_mean']:.4f} | {r['cv_std']:.4f} |"
        )
    mean_cv = float(np.mean([r["cv_mean"] for r in rows]))
    lines += ["", f"**Mean CV (macro across subjects): {mean_cv:.4f}**"]
    (args.output_dir / "report.md").write_text("\n".join(lines), encoding="utf-8")
    (args.output_dir / "summary.json").write_text(
        json.dumps({"rows": rows, "mean_cv": mean_cv}, indent=2),
        encoding="utf-8",
    )
    print(f"\nWrote {args.output_dir}/submission.zip and report.md.")


if __name__ == "__main__":
    main()
