"""Inference-only script (no retraining).

Loads each subject's serialized pipeline and writes a submission. Useful
when you have already trained models via ``scripts/train.py`` and simply
want to re-score a fresh test set.
"""
from __future__ import annotations

import argparse
import pickle
import zipfile
from pathlib import Path

import numpy as np
import yaml

from bci_mi_decoder.data import INT_TO_LABEL, load_subject
from bci_mi_decoder.preprocessing import bandpass, crop, standardize


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data-dir", required=True, type=Path)
    parser.add_argument("--run-dir", required=True, type=Path)
    parser.add_argument("--config", default="configs/default.yaml", type=Path)
    args = parser.parse_args()

    cfg = yaml.safe_load(args.config.read_text())
    args.run_dir.mkdir(parents=True, exist_ok=True)

    for subject_id in cfg["subjects"]:
        subj_cfg = cfg["per_subject"][subject_id]
        subj = load_subject(subject_id, args.data_dir)
        X_test = crop(subj.X_test, subj_cfg["crop"][0], subj_cfg["crop"][1])
        X_test = bandpass(X_test, subj_cfg["band"][0], subj_cfg["band"][1])
        X_test = standardize(X_test)

        model_path = args.run_dir / f"{subject_id}_model.pkl"
        if not model_path.exists():
            raise FileNotFoundError(
                f"Missing model at {model_path}. Run scripts/train.py first "
                f"(or manually place the pickle)."
            )
        with model_path.open("rb") as f:
            estimator = pickle.load(f)
        proba = estimator.predict_proba(X_test)
        pred = np.argmax(proba, axis=1)
        labels = [INT_TO_LABEL[int(p)] for p in pred]
        cb_id = chr(ord("A") + int("".join(ch for ch in subject_id if ch.isdigit())) - 1)
        (args.run_dir / f"subject_{cb_id}_y_pred.csv").write_text(
            "y_pred\n" + "\n".join(labels) + "\n", encoding="utf-8"
        )
        print(f"{subject_id}: wrote {len(labels)} predictions.")

    with zipfile.ZipFile(args.run_dir / "submission.zip", "w",
                         zipfile.ZIP_DEFLATED) as zf:
        for subject_id in cfg["subjects"]:
            cb_id = chr(ord("A") + int("".join(ch for ch in subject_id if ch.isdigit())) - 1)
            zf.write(
                args.run_dir / f"subject_{cb_id}_y_pred.csv",
                arcname=f"subject_{cb_id}_y_pred.csv",
            )
    print(f"Wrote {args.run_dir}/submission.zip.")


if __name__ == "__main__":
    main()
