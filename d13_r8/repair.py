"""Prevent unification from expanding large powers: pass every numerical parameter explicitly."""
import run
import shutil

def explicit_modpow(M,E,label):
    out=[];seen={}
    def go(e):
        if e in seen:return seen[e]
        nm=f'{label}_{e}';v=pow(10,e,M)
        if e==1:
            out.append(f'  have {nm} : Nat.ModEq {M} ((10 : ℕ) ^ 1) {v} := by norm_num [Nat.ModEq]')
        else:
            a=e//2;b=e-a;x=go(a);y=go(b)
            u=pow(10,a,M);w=pow(10,b,M)
            out.append(f'  have {nm} : Nat.ModEq {M} ((10 : ℕ) ^ {e}) {v} :=\n    modpow_add (M := {M}) (x := 10) (e := {a}) (f := {b}) (u := {u}) (v := {w}) (w := {v}) {x} {y} (by norm_num [Nat.ModEq])')
        seen[e]=nm
        return nm
    h=go(E)
    return out,h

run.modpow=explicit_modpow
shutil.copy2(__file__,run.OUT/'repair.py')
shutil.copy2(run.__file__,run.OUT/'run.py')
try:
    run.main()
except Exception as exc:
    run.state['error']=repr(exc)
    run.save()
    raise
