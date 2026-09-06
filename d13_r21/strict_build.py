from pathlib import Path
import sys, json

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "d13_r18"))
import strict_build_v3
import strict_build as s

# Reuse the audited strict proper-factor checker on the single Round-21 q2
# class that has a strictly positive exact marginal coverage gain.
s.ROOT = ROOT
s.OUT = ROOT / "evidence"
s.OUT.mkdir(parents=True, exist_ok=True)
s.ROWS = {"q1": [], "q2": [(60894913, 327392, 145262)]}
s.status = {"passed": False, "strict_build": False, "classes": 0, "round": 21}

if __name__ == "__main__":
    try:
        s.main()
        state = json.loads((s.OUT / "status.json").read_text())
        state["round"] = 21
        state["accepted_class"] = [60894913, 327392, 145262]
        (s.OUT / "status.json").write_text(json.dumps(state, indent=2) + "\n")
    except Exception as exc:
        s.status["error"] = repr(exc)
        s.save()
        raise
