"""Use explicit exponent equality transports, never normalize a concrete huge power."""
import run
import shutil,json

run.CORE += r'''
theorem modpow_step (M x e f g u v w : ℕ) (hg : e + f = g)
    (he : Nat.ModEq M (x ^ e) u) (hf : Nat.ModEq M (x ^ f) v)
    (hr : Nat.ModEq M (u * v) w) : Nat.ModEq M (x ^ g) w := by
  rw [← hg]
  exact modpow_add he hf hr

theorem divisor_on_class_explicit (A a b D p r m k E T M : ℕ)
    (hD : 0 < D) (hM : D * p = M) (hE : a + b * r = E) (hT : b * m = T)
    (hb : Nat.ModEq M (A * 10 ^ E + 1) 0)
    (hs : Nat.ModEq M (10 ^ T) 1) : p ∣ Q A a b D (r + m * k) := by
  apply divisor_on_class A a b D p r m k hD
  · rw [hM, hE]
    exact hb
  · rw [hM, hT]
    exact hs
'''

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
            out.append(f'  have {nm} : Nat.ModEq {M} ((10 : ℕ) ^ {e}) {v} :=\n    modpow_step {M} 10 {a} {b} {e} {u} {w} {v} (by decide) {x} {y} (by norm_num [Nat.ModEq])')
        seen[e]=nm
        return nm
    h=go(E)
    return out,h

run.modpow=explicit_modpow
old_theorem=run.theorem
def repaired_theorem(f,p,m,r):
    A,a,b,D=(740,136,199,2391) if f=='q1' else (370,666,930,2177)
    s,n=old_theorem(f,p,m,r)
    old=f'  exact divisor_on_class {A} {a} {b} {D} {p} {r} {m} k (by decide) hb step_{b*m}'
    new=f'  exact divisor_on_class_explicit {A} {a} {b} {D} {p} {r} {m} k {a+b*r} {b*m} {D*p} (by decide) (by decide) (by decide) (by decide) hb step_{b*m}'
    assert s.count(old)==1
    return s.replace(old,new),n
run.theorem=repaired_theorem

def provenance():
    for src in [__file__,run.__file__,str(run.ROOT/'all_classes.json')]:
        shutil.copy2(src,run.OUT/run.Path(src).name)
try:
    provenance()
    run.main()
    pilot=run.state.copy()
    run.OUT=run.ROOT/'evidence'/'bulk';run.OUT.mkdir()
    run.state=dict(passed=False,run_id=pilot['run_id'],commit=pilot['commit'])
    run.ROWS=json.loads((run.ROOT/'all_classes.json').read_text())
    run.EXTRA={'q1':[],'q2':[]}
    assert sum(map(len,run.ROWS.values()))==92
    provenance()
    run.main()
    (run.ROOT/'evidence'/'SUMMARY.json').write_text(json.dumps({'pilot':pilot,'bulk':run.state},indent=2)+'\n')
except Exception as exc:
    run.state['error']=repr(exc)
    run.save()
    raise
