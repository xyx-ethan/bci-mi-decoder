from pathlib import Path
import hashlib, json, re, subprocess, sys

ROOT = Path(__file__).resolve().parent
FC = Path(sys.argv[1]).resolve()
OUT = ROOT / "evidence"
OUT.mkdir(parents=True, exist_ok=True)

ROWS = {
    "q1": [(19,18,8),(97,96,24),(109,108,65),(331,110,2),(113,112,2),(131,130,118)],
    "q2": [(523,87,53),(911,91,67),(1237,103,37),(227,113,44),(709,118,55),(2287,127,48)],
}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
PIN = "8323e878b83fcd7f4a448256069352a265460d75"
MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"
status = {"passed": False, "strict_build": False, "classes": 0}

def save():
    (OUT / "status.json").write_text(json.dumps(status, indent=2) + "\n")

def call(args, name, timeout=2400):
    print("RUN", " ".join(map(str,args)), flush=True)
    r = subprocess.run(args, cwd=FC, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout)
    (OUT / name).write_text(r.stdout)
    print(r.stdout, flush=True)
    if r.returncode:
        raise RuntimeError(f"{name}: exit {r.returncode}")
    return r.stdout

CORE = r'''import Mathlib
import FormalConjectures.OEIS.«67599»

/-!
# D13 A067599 strict proper-factor certificates

This module is generated only for a strict `lake --wfail build` audit.
It proves twelve periodic proper-factor classes without using the open conjecture.
-/

namespace D13Round18

def Q (A a b D t : ℕ) : ℕ := (A * 10 ^ (a + b * t) + 1) / D

def q1 (t : ℕ) : ℕ := Q 740 136 199 2391 t

def q2 (t : ℕ) : ℕ := Q 370 666 930 2177 t

theorem not_prime_of_proper_factor {n d : ℕ}
    (h1 : 1 < d) (hlt : d < n) (hdvd : d ∣ n) : ¬ Nat.Prime n := by
  intro hp
  rcases hp.eq_one_or_self_of_dvd d hdvd with h | h
  · omega
  · omega

theorem Q_large (A a b D t : ℕ)
    (hA : 1 ≤ A) (ha : 16 ≤ a) (hD0 : 0 < D) (hD : D ≤ 2391) :
    1000000000 < Q A a b D t := by
  have hp : (10 : ℕ) ^ 16 ≤ 10 ^ (a + b * t) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hm : (10 : ℕ) ^ (a + b * t) ≤ A * 10 ^ (a + b * t) := by
    simpa only [one_mul] using Nat.mul_le_mul_right (10 ^ (a + b * t)) hA
  have hc : 1000000001 * D ≤ (10 : ℕ) ^ 16 := by
    calc
      1000000001 * D ≤ 1000000001 * 2391 := Nat.mul_le_mul_left _ hD
      _ ≤ (10 : ℕ) ^ 16 := by norm_num
  have hq : 1000000001 ≤ Q A a b D t := by
    apply (Nat.le_div_iff_mul_le hD0).2
    exact le_trans hc (le_trans hp (le_trans hm (Nat.le_add_right _ _)))
  exact lt_of_lt_of_le (by decide : 1000000000 < 1000000001) hq

theorem q1_large (t : ℕ) : 1000000000 < q1 t := by
  exact Q_large 740 136 199 2391 t (by decide) (by decide) (by decide) (by decide)

theorem q2_large (t : ℕ) : 1000000000 < q2 t := by
  exact Q_large 370 666 930 2177 t (by decide) (by decide) (by decide) (by decide)

theorem modpow_add {M x e f u v w : ℕ}
    (he : Nat.ModEq M (x ^ e) u) (hf : Nat.ModEq M (x ^ f) v)
    (hr : Nat.ModEq M (u * v) w) : Nat.ModEq M (x ^ (e + f)) w := by
  rw [pow_add]
  exact (he.mul hf).trans hr

theorem modpow_step (M x e f g u v w : ℕ) (hg : e + f = g)
    (he : Nat.ModEq M (x ^ e) u) (hf : Nat.ModEq M (x ^ f) v)
    (hr : Nat.ModEq M (u * v) w) : Nat.ModEq M (x ^ g) w := by
  rw [← hg]
  exact modpow_add he hf hr

theorem divisor_on_class (A a b D p r m k : ℕ) (hD : 0 < D)
    (hbase : Nat.ModEq (D * p) (A * 10 ^ (a + b * r) + 1) 0)
    (hstep : Nat.ModEq (D * p) (10 ^ (b * m)) 1) :
    p ∣ Q A a b D (r + m * k) := by
  have he : a + b * (r + m * k) = (a + b * r) + (b * m) * k := by ring
  have hpk : Nat.ModEq (D * p) ((10 ^ (b * m)) ^ k) 1 := by
    simpa only [one_pow] using Nat.ModEq.pow k hstep
  have hmul : Nat.ModEq (D * p)
      (A * 10 ^ (a + b * r) * (10 ^ (b * m)) ^ k + 1)
      (A * 10 ^ (a + b * r) + 1) := by
    simpa only [mul_one] using
      ((Nat.ModEq.refl (A * 10 ^ (a + b * r))).mul hpk).add (Nat.ModEq.refl 1)
  have hn : Nat.ModEq (D * p) (A * 10 ^ (a + b * (r + m * k)) + 1) 0 := by
    rw [he, pow_add, pow_mul, ← mul_assoc]
    exact hmul.trans hbase
  have hz : (A * 10 ^ (a + b * (r + m * k)) + 1) % (D * p) = 0 := by
    simpa only [Nat.ModEq, Nat.zero_mod] using hn
  obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero hz
  refine ⟨c, ?_⟩
  unfold Q
  rw [hc, Nat.mul_assoc, Nat.mul_div_cancel_left _ hD]

theorem divisor_on_class_explicit (A a b D p r m k E T M : ℕ)
    (hD : 0 < D) (hM : D * p = M) (hE : a + b * r = E) (hT : b * m = T)
    (hb : Nat.ModEq M (A * 10 ^ E + 1) 0)
    (hs : Nat.ModEq M (10 ^ T) 1) : p ∣ Q A a b D (r + m * k) := by
  apply divisor_on_class A a b D p r m k hD
  · rw [hM, hE]
    exact hb
  · rw [hM, hT]
    exact hs

-- Semantic and mutation checks for the exact upstream encoding. Kernel `decide` only.
example : OeisA67599.a 0 = 0 := by decide
example : OeisA67599.a 1 = 0 := by decide
example : OeisA67599.a 2 = 21 := by decide
example : OeisA67599.a 15 = 3151 := by decide
example : OeisA67599.a 24 = 2331 := by decide
example : OeisA67599.a 15 ≠ 3511 := by decide

'''

def power_chain(M, E, label):
    lines, seen = [], {}
    def go(e):
        if e in seen:
            return seen[e]
        name = f"{label}{e}"
        residue = pow(10, e, M)
        if e == 1:
            lines.append(f"  have {name} : Nat.ModEq {M} ((10 : ℕ) ^ 1) {residue} := by norm_num [Nat.ModEq]")
        else:
            x = e // 2; y = e - x
            hx = go(x); hy = go(y)
            rx = pow(10, x, M); ry = pow(10, y, M)
            lines.append(
                f"  have {name} : Nat.ModEq {M} ((10 : ℕ) ^ {e}) {residue} :=\n"
                f"    modpow_step {M} 10 {x} {y} {e} {rx} {ry} {residue} (by decide) {hx} {hy} (by norm_num [Nat.ModEq])"
            )
        seen[e] = name
        return name
    return lines, go(E)

def theorem(fam, p, m, r):
    A,a,b,D = (740,136,199,2391) if fam == "q1" else (370,666,930,2177)
    M = D*p; E = a+b*r; T = b*m
    assert (A*pow(10,E,M)+1) % M == 0
    assert pow(10,T,M) == 1
    name = f"{fam}_{p}"
    out = [f"theorem {name}_dvd (k : ℕ) : {p} ∣ {fam} ({r} + {m} * k) := by"]
    lines, hbpow = power_chain(M,E,"b"); out += lines
    out += [
        f"  have hb : Nat.ModEq {M} ({A} * 10 ^ {E} + 1) 0 := by",
        f"    exact (((Nat.ModEq.refl {A}).mul {hbpow}).add (Nat.ModEq.refl 1)).trans (by norm_num [Nat.ModEq])",
    ]
    lines, hspow = power_chain(M,T,"s"); out += lines
    out += [
        f"  exact divisor_on_class_explicit {A} {a} {b} {D} {p} {r} {m} k {E} {T} {M} (by decide) (by decide) (by decide) (by decide) hb {hspow}",
        f"theorem {name}_not_prime (k : ℕ) : ¬ Nat.Prime ({fam} ({r} + {m} * k)) := by",
        f"  apply not_prime_of_proper_factor (d := {p}) (by decide)",
        f"  · exact lt_trans (by decide : {p} < 1000000000) ({fam}_large _)",
        f"  · exact {name}_dvd k",
        "",
    ]
    return "\n".join(out), f"D13Round18.{name}_not_prime"

def main():
    save()
    assert call(["git","rev-parse","HEAD"],"upstream_commit.log").strip() == PIN
    assert (FC/"lean-toolchain").read_text().strip() == "leanprover/lean4:v4.33.1"
    manifest = json.loads((FC/"lake-manifest.json").read_text())
    assert next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib") == MATHLIB

    source = CORE; theorem_names = []; records = []
    for fam, rows in ROWS.items():
        for p,m,r in rows:
            text, name = theorem(fam,p,m,r)
            source += text + "\n"; theorem_names.append(name)
            records.append({"family":fam,"prime":p,"period":m,"residue":r,"theorem":name})
    source += "\nend D13Round18\n"
    source += "\n".join("#print axioms " + n for n in theorem_names) + "\n"
    for bad in ["sorry", "admit", "native_decide", "Lean.ofReduceBool", "Lean.trustCompiler", "unsafe", "axiom ", "maxRecDepth"]:
        assert bad not in source, bad

    moddir = FC/"D13Round18"; moddir.mkdir(exist_ok=True)
    (moddir/"CertifiedClasses.lean").write_text(source)
    (OUT/"CertifiedClasses.lean").write_text(source)
    (OUT/"classes.json").write_text(json.dumps(records,indent=2)+"\n")

    lake = FC/"lakefile.toml"; lake_text = lake.read_text()
    old = 'defaultTargets = ["FormalConjectures", "FormalConjecturesUtil", "FormalConjecturesForMathlib"]'
    assert old in lake_text
    lake_text = lake_text.replace(old, 'defaultTargets = ["D13Round18"]', 1)
    lake_text += '\n[[lean_lib]]\nname = "D13Round18"\nglobs = ["D13Round18.+"]\n'
    lake.write_text(lake_text)
    (OUT/"lakefile.strict.toml").write_text(lake_text)

    call(["lake","exe","cache","get"],"cache.log",1800)
    build = call(["lake","--wfail","build"],"lake_wfail_build.log",2400)

    axioms = {}
    for name in theorem_names:
        m = re.search(r"'"+re.escape(name)+r"' depends on axioms:\s*\[([^\]]*)\]", build, re.S)
        z = re.search(r"'"+re.escape(name)+r"' does not depend on any axioms", build)
        assert bool(m) ^ bool(z), (name, bool(m), bool(z))
        deps = [] if z else [x.strip() for x in m.group(1).split(',') if x.strip()]
        assert set(deps) <= ALLOWED_AXIOMS, (name,deps)
        axioms[name] = deps
    (OUT/"axioms.json").write_text(json.dumps(axioms,indent=2)+"\n")

    status.update({"passed":True,"strict_build":True,"command":"lake --wfail build","classes":len(records),
      "upstream_commit":PIN,"lean_toolchain":"leanprover/lean4:v4.33.1","mathlib_revision":MATHLIB,
      "source_sha256":hashlib.sha256(source.encode()).hexdigest(),"axioms_records":len(axioms)})
    save()
    (OUT/"SHA256SUMS").write_text("".join(hashlib.sha256(p.read_bytes()).hexdigest()+"  "+p.name+"\n" for p in sorted(OUT.iterdir()) if p.is_file() and p.name != "SHA256SUMS"))
    print("D13_R18_STRICT_LAKE_BUILD_PASS", json.dumps(status,sort_keys=True), flush=True)

if __name__ == "__main__":
    try: main()
    except Exception as exc:
        status["error"] = repr(exc); save(); raise
