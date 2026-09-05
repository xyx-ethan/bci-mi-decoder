"""Generate and kernel-check D13 proper-factor classes. No native_decide or custom axioms."""
from pathlib import Path
import hashlib, json, os, re, shutil, subprocess, sys
ROOT=Path(__file__).resolve().parent
OUT=ROOT/'evidence'; OUT.mkdir(exist_ok=True)
FC=Path(sys.argv[1]).resolve()
PIN='8323e878b83fcd7f4a448256069352a265460d75'
ML='0df444a360eaa60ab8c11dca51a86af692955474'
ALLOW={'propext','Classical.choice','Quot.sound'}
state={'passed':False,'run_id':os.getenv('GITHUB_RUN_ID'),'commit':os.getenv('GITHUB_SHA')}
def save(): (OUT/'status.json').write_text(json.dumps(state,indent=2)+'\n')
def run(args,name,timeout=1200):
 print('RUN',args,flush=True)
 r=subprocess.run(args,cwd=FC,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=timeout)
 (OUT/name).write_text(r.stdout); print(r.stdout,flush=True)
 if r.returncode: raise RuntimeError(f'{name}: {r.returncode}')
 return r.stdout
CORE=r'''import Mathlib
namespace D13
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

theorem finite_cover_not_prime {k : ℕ} (q : ℕ → ℕ)
    (m r d : Fin k → ℕ)
    (hcover : ∀ t, ∃ j, t % m j = r j)
    (hproper : ∀ j t, t % m j = r j →
      1 < d j ∧ d j < q t ∧ d j ∣ q t) :
    ∀ t, ¬ Nat.Prime (q t) := by
  intro t
  obtain ⟨j, hj⟩ := hcover t
  obtain ⟨h1, hlt, hdvd⟩ := hproper j t hj
  exact not_prime_of_proper_factor h1 hlt hdvd

'''
ROWS={'q1':[(7,6,0),(13,6,2),(73,8,5),(31,15,8),(17,16,6),(23,22,13)],
      'q2':[(7,7,5),(17,8,1),(157,13,3),(53,13,7),(29,14,7),(97,16,6)]}
EXTRA={'q1':[(277,69,58),(797,797,529)],'q2':[(311,311,93)]}
def modpow(M,E,label):
 out=[];seen={}
 def go(e):
  if e in seen:return seen[e]
  nm=f'{label}_{e}';v=pow(10,e,M)
  if e==1:out.append(f'  have {nm} : Nat.ModEq {M} ((10 : ℕ) ^ 1) {v} := by norm_num [Nat.ModEq]')
  else:
   x=go(e//2);y=go(e-e//2)
   out.append(f'  have {nm} : Nat.ModEq {M} ((10 : ℕ) ^ {e}) {v} :=\n    modpow_add {x} {y} (by norm_num [Nat.ModEq])')
  seen[e]=nm;return nm
 h=go(E);return out,h

def theorem(f,p,m,r):
 A,a,b,D=(740,136,199,2391) if f=='q1' else (370,666,930,2177)
 M=D*p;E=a+b*r;name=f'r8_{f}_{p}'
 assert (A*pow(10,E,M)+1)%M==0 and pow(10,b*m,M)==1 and 1<p<10**9
 out=[f'theorem {name}_dvd (k : ℕ) : {p} ∣ {f} ({r} + {m} * k) := by']
 ls,h=modpow(M,E,'base');out+=ls
 out +=[f'  have hb : Nat.ModEq {M} ({A} * 10 ^ {E} + 1) 0 := by',f'    exact (((Nat.ModEq.refl {A}).mul {h}).add (Nat.ModEq.refl 1)).trans (by norm_num [Nat.ModEq])']
 ls,h=modpow(M,b*m,'step');out+=ls
 out +=[f'  exact divisor_on_class {A} {a} {b} {D} {p} {r} {m} k (by decide) hb {h}',f'theorem {name}_not_prime (k : ℕ) : ¬ Nat.Prime ({f} ({r} + {m} * k)) := by',f'  apply not_prime_of_proper_factor (d := {p}) (by decide)',f'  · exact lt_trans (by decide : {p} < 1000000000) ({f}_large _)',f'  · exact {name}_dvd k','']
 return '\n'.join(out),name+'_not_prime'
TAIL=r'''
theorem q1_resolution46_not_prime (k : ℕ) :
    ¬ Nat.Prime (q1 (12 + 46 * k)) := by
  have hd := Nat.mod_add_div k 3
  have hc : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hc with h | h | h
  · have he : 12 + 46 * k = 6 * (2 + 23 * (k / 3)) := by omega
    rw [he]
    simpa only [zero_add] using r8_q1_7_not_prime (2 + 23 * (k / 3))
  · have he : 12 + 46 * k = 58 + 69 * (2 * (k / 3)) := by omega
    rw [he]
    exact r8_q1_277_not_prime (2 * (k / 3))
  · have he : 12 + 46 * k = 2 + 6 * (17 + 23 * (k / 3)) := by omega
    rw [he]
    exact r8_q1_13_not_prime (17 + 23 * (k / 3))
'''

def main():
 save()
 assert run(['git','rev-parse','HEAD'],'upstream.log').strip()==PIN
 assert (FC/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.33.1'
 mf=json.loads((FC/'lake-manifest.json').read_text())
 assert next(x['rev'] for x in mf['packages'] if x['name']=='mathlib')==ML
 run(['lean','--version'],'lean_version.log')
 run(['lake','exe','cache','get'],'cache.log')
 assert run(['git','-C','.lake/packages/mathlib','rev-parse','HEAD'],'mathlib.log').strip()==ML
 code=CORE;names=['Q_large','finite_cover_not_prime','divisor_on_class']
 records=[]
 for f in ROWS:
  for p,m,r in ROWS[f]+EXTRA[f]:
   s,name=theorem(f,p,m,r);code+=s+'\n';names.append(name)
   records.append({'family':f,'prime':p,'period':m,'residue':r,'theorem':'D13.'+name})
 code+=TAIL;names.append('q1_resolution46_not_prime')
 code+='\nend D13\n'+'\n'.join('#print axioms D13.'+n for n in names)+'\n'
 for bad in ['sorry','admit','native_decide','maxRecDepth','axiom ']:
  assert bad not in code,bad
 (FC/'D13R8.lean').write_text(code);(OUT/'D13R8.lean').write_text(code)
 (OUT/'classes.json').write_text(json.dumps(records,indent=2)+'\n')
 text=run(['lake','env','lean','-o',str(OUT/'D13R8.olean'),'D13R8.lean'],'compile.log',900)
 axioms={}
 for n in names:
  n='D13.'+n
  a=re.findall(r"'"+re.escape(n)+r"' depends on axioms:\s*\[([^\]]*)\]",text,re.S)
  z=re.findall(r"'"+re.escape(n)+r"' does not depend on any axioms",text)
  assert len(a)+len(z)==1,(n,a,z)
  aa=[] if z or not a[0].strip() else [x.strip() for x in a[0].split(',')]
  assert set(aa)<=ALLOW,(n,aa)
  axioms[n]=aa
 assert (OUT/'D13R8.olean').stat().st_size>0
 (OUT/'axioms.json').write_text(json.dumps(axioms,indent=2)+'\n')
 state.update(passed=True,classes_kernel_checked=len(records),macro_classes_kernel_checked=1,axioms_audited=len(names),upstream_commit=PIN,mathlib_commit=ML,source_sha256=hashlib.sha256(code.encode()).hexdigest())
 save()
 (OUT/'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.name+'\n' for p in sorted(OUT.iterdir()) if p.is_file() and p.name!='SHA256SUMS'))
 print('D13_KERNEL_AND_AXIOM_AUDIT_PASS',state,flush=True)
if __name__=='__main__':
 try:main()
 except Exception as exc:
  state['error']=repr(exc);save();raise
