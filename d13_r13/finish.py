from pathlib import Path
import subprocess,sys,json,re,shutil,hashlib,difflib
R=Path(__file__).resolve().parent;F=Path(sys.argv[1]).resolve();O=R/'evidence'
p=R/'SevenBranches.lean';before=p.read_text()
old='  all_goals interval_cases e <;> norm_num at hp5 hL hU ⊢'
new='  all_goals interval_cases e\n  all_goals try norm_num at hp5\n  all_goals try norm_num at hL\n  all_goals try norm_num at hU\n  all_goals try norm_num'
assert before.count(old)==1
p.write_text(before.replace(old,new))
subprocess.run([sys.executable,str(R/'extend.py'),str(F)],check=True)
(O/'seven_tactic.patch').write_text(''.join(difflib.unified_diff(before.splitlines(True),p.read_text().splitlines(True))))
state=json.loads((O/'status.json').read_text());assert state['seven_passed']
shutil.copy2(O/'D13R13Seven.olean',F/'.lake/build/lib/lean/D13R13Seven.olean')
CORE=r'''import D13R13Seven

/-! Certified binomial power obstructions for the five finite branches. -/
namespace D13.R13

theorem binomial_power_obstruction (D C h u v : ℕ) (hD : 0 < D)
    (h10 : Nat.ModEq D (10^h) 1)
    (hu : Nat.ModEq D (C^h) u)
    (hv : Nat.ModEq D ((D-1)^h) v)
    (hne : ¬ Nat.ModEq D u v) :
    ∀ q k : ℕ, D*q ≠ C*10^k+1 := by
  intro q k hEq
  have hz : (C*10^k+1)%D=0 := by
    rw [← hEq]
    simp
  let x := (C*10^k)%D
  have hxlt : x < D := Nat.mod_lt _ hD
  have hxmod : (x+1)%D=0 := by
    simpa only [x, Nat.add_mod, Nat.mod_mod] using hz
  have hdiv : D ∣ x+1 := Nat.dvd_of_mod_eq_zero hxmod
  have hle : D ≤ x+1 := Nat.le_of_dvd (by omega) hdiv
  have hx : x=D-1 := by omega
  have hb : Nat.ModEq D (C*10^k) (D-1) := by
    change (C*10^k)%D=(D-1)%D
    rw [Nat.mod_eq_of_lt (by omega : D-1<D)]
    exact hx
  have hl : Nat.ModEq D ((C*10^k)^h) (C^h) := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm k h, pow_mul]
    simpa only [one_pow, mul_one] using
      (Nat.ModEq.refl (C^h)).mul (Nat.ModEq.pow k h10)
  have hm : Nat.ModEq D (C^h) ((D-1)^h) :=
    hl.symm.trans (Nat.ModEq.pow h hb)
  exact hne ((hu.symm.trans hm).trans hv)

'''
def power(M,b,E,label):
 lines=[];seen={}
 def go(e):
  if e in seen:return seen[e]
  name=label+str(e);r=pow(b,e,M)
  if e==1:lines.append(f'  have {name} : Nat.ModEq {M} (({b} : ℕ)^1) {r} := by norm_num [Nat.ModEq]')
  else:
   a=e//2;c=e-a;x=go(a);y=go(c)
   lines.append(f'  have {name} : Nat.ModEq {M} (({b} : ℕ)^{e}) {r} :=\n    D13.modpow_step {M} {b} {a} {c} {e} {pow(b,a,M)} {pow(b,c,M)} {r} (by decide) {x} {y} (by norm_num [Nat.ModEq])')
  seen[e]=name;return name
 name=go(E);return '\n'.join(lines)+'\n',name
source=CORE
records=[]
for p,e,D,C,h in [(3,6,719,360,359),(11,3,1321,1130,55),(17,3,4903,1730,1634),(23,3,12157,2330,2026),(29,3,24379,2930,8126)]:
 assert pow(10,h,D)==1 and pow(C,h,D)!=pow(D-1,h,D)
 source+=f'theorem no_branch_{p}_{e} (q k : ℕ) : {D}*q ≠ {C}*10^k+1 := by\n'
 names=[]
 for b,label in [(10,'s'),(C,'c'),(D-1,'d')]:
  text,name=power(D,b,h,label);source+=text;names.append(name)
 source+=f'  exact binomial_power_obstruction {D} {C} {h} {pow(C,h,D)} {pow(D-1,h,D)} (by decide) {names[0]} {names[1]} {names[2]} (by norm_num [Nat.ModEq]) q k\n\n'
 records.append({'p':p,'e':e,'D':D,'C':C,'h':h,'C_residue':pow(C,h,D),'negative_one_residue':pow(D-1,h,D)})
source+=r'''
theorem f_one_two_prime_exponent_pairs (p q e : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (he : 0 < e)
    (hfix : OeisA67599.a (p^e*q) = p^e*q) :
    (p=7 ∧ e=4) ∨ (p=3 ∧ e=7) := by
  have hEq := (D13.R12.f_one_equation p q e hp hq hpq he hfix).2
  rcases f_one_seven_branches p q e hp hq hpq he hfix with h | h | h | h | h | h | h
  · rcases h with ⟨rfl,rfl⟩
    norm_num at hEq
    exact (no_branch_3_6 q (Nat.digits 10 q).length hEq).elim
  · rcases h with ⟨rfl,rfl⟩
    exact Or.inr ⟨rfl,rfl⟩
  · rcases h with ⟨rfl,rfl⟩
    exact Or.inl ⟨rfl,rfl⟩
  · rcases h with ⟨rfl,rfl⟩
    norm_num at hEq
    exact (no_branch_11_3 q (Nat.digits 10 q).length hEq).elim
  · rcases h with ⟨rfl,rfl⟩
    norm_num at hEq
    exact (no_branch_17_3 q (Nat.digits 10 q).length hEq).elim
  · rcases h with ⟨rfl,rfl⟩
    norm_num at hEq
    exact (no_branch_23_3 q (Nat.digits 10 q).length hEq).elim
  · rcases h with ⟨rfl,rfl⟩
    norm_num at hEq
    exact (no_branch_29_3 q (Nat.digits 10 q).length hEq).elim

end D13.R13
'''
names=['D13.R13.'+n for n in re.findall(r'^theorem (\w+)',source,re.M)]
for bad in ['sorry','admit','native_decide','set_option','axiom ']:assert bad not in source
source+='\n'+'\n'.join('#print axioms '+n for n in names)+'\n'
(F/'D13R13Power.lean').write_text(source);(O/'D13R13Power.lean').write_text(source)
r=subprocess.run(['lake','env','lean','-o',str(O/'D13R13Power.olean'),'D13R13Power.lean'],cwd=F,text=True,capture_output=True,timeout=600)
text=r.stdout+r.stderr;(O/'power.log').write_text(text);print(text,flush=True)
state['power_passed']=False
if not r.returncode:
 ax=json.loads((O/'axioms.json').read_text())
 for n in names:
  a=re.findall("'"+re.escape(n)+r"' depends on axioms:\s*\[([^\]]*)\]",text,re.S)
  z=re.findall("'"+re.escape(n)+r"' does not depend on any axioms",text)
  assert len(a)+len(z)==1,n
  deps=[] if z or not a[0].strip() else [s.strip() for s in a[0].split(',')]
  assert set(deps)<={'propext','Classical.choice','Quot.sound'},(n,deps)
  ax[n]=deps
 (O/'axioms.json').write_text(json.dumps(ax,indent=2));state.update(power_passed=True,power_theorems=names,axioms_records=len(ax))
else:state['power_error']='Lean exited '+str(r.returncode)
(O/'status.json').write_text(json.dumps(state,indent=2));(O/'power_certificates.json').write_text(json.dumps(records,indent=2));shutil.copy2(__file__,O/'finish.py')
(O/'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.name+'\n'for p in sorted(O.iterdir())if p.is_file()and p.name!='SHA256SUMS'))
if r.returncode:raise SystemExit(r.returncode)
print('D13_R13_TWO_PAIRS_PASS',state,flush=True)
