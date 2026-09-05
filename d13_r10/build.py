from pathlib import Path
import sys,subprocess,shutil,json,hashlib,re,os
ROOT=Path(__file__).resolve().parent; FC=Path(sys.argv[1]).resolve(); OUT=ROOT/'evidence';OUT.mkdir(exist_ok=True)
state={'passed':False,'run_id':os.getenv('GITHUB_RUN_ID'),'commit':os.getenv('GITHUB_SHA')}
def save(): (OUT/'status.json').write_text(json.dumps(state,indent=2)+'\n')
def call(args,name,timeout=1500):
 p=subprocess.run(args,cwd=FC,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=timeout)
 (OUT/name).write_text(p.stdout); print(p.stdout,flush=True)
 if p.returncode:raise RuntimeError((name,p.returncode))
 return p.stdout
ROWS={'q1':[(2148803,5399,4018),(43600901,8764,1430),(4022587,10107,3097),(4234721,10640,9640),(3133057,15744,10780),(3411259,17142,11993)],'q2':[(4922677,1203,548),(2392891,2573,57),(7103651,4583,41),(10222561,5496,1706),(7976611,8577,1316),(6795883,12179,3844)]}
EXTRA=r'''
namespace D13.R10
theorem residue_cover_of_finite_period {k : ℕ} (L : ℕ)
    (m r : Fin k → ℕ) (hL : 0 < L) (hm : ∀ j, m j ∣ L)
    (hfinite : ∀ s, s < L → ∃ j, s % m j = r j) :
    ∀ t, ∃ j, t % m j = r j := by
  intro t
  obtain ⟨j, hj⟩ := hfinite (t % L) (Nat.mod_lt t hL)
  refine ⟨j, ?_⟩
  have ht : (t % L) % m j = t % m j :=
    (Nat.mod_modEq t L).of_dvd (hm j)
  exact ht.symm.trans hj

theorem finite_period_cover_not_prime {k : ℕ} (q : ℕ → ℕ)
    (L : ℕ) (m r d : Fin k → ℕ) (hL : 0 < L) (hm : ∀ j, m j ∣ L)
    (hfinite : ∀ s, s < L → ∃ j, s % m j = r j)
    (hproper : ∀ j t, t % m j = r j → 1 < d j ∧ d j < q t ∧ d j ∣ q t) :
    ∀ t, ¬ Nat.Prime (q t) := by
  exact D13.finite_cover_not_prime q m r d
    (residue_cover_of_finite_period L m r hL hm hfinite) hproper
end D13.R10
'''
def main():
 save()
 call([sys.executable,str(ROOT.parent/'d13_r9/build.py'),str(FC)],'parent_rebuild.log')
 parent=ROOT.parent/'d13_r9/evidence'
 assert json.loads((parent/'status.json').read_text())['passed'] is True
 for n in ['status.json','axioms.json','numbers.log','reconstruction.log','D13R9Numbers.lean','D13R9Reconstruction.lean','67599.original.lean']:
  (OUT/'parent').mkdir(exist_ok=True);shutil.copy2(parent/n,OUT/'parent'/n)
 sys.path.insert(0,str(ROOT.parent/'d13_r8'));import run
 prefix=(ROOT.parent/'d13_r8/repair.py').read_text().split('def provenance():',1)[0]
 exec(compile(prefix,'repair.py','exec'),{})
 source='import D13R9Numbers\nnamespace D13\n';names=[];records=[]
 for f,rs in ROWS.items():
  for p,m,r in rs:
   s,n=run.theorem(f,p,m,r);source+=s.replace('r8_','r10_')+'\n';names+=['D13.'+n.replace('r8_','r10_')]
   records.append({'family':f,'prime':p,'period':m,'residue':r,'theorem':names[-1]})
 source+='end D13\n'+EXTRA
 names+=['D13.R10.residue_cover_of_finite_period','D13.R10.finite_period_cover_not_prime']
 source+='\n'+'\n'.join('#print axioms '+n for n in names)+'\n'
 for x in ['sorry','admit','native_decide','maxRecDepth','axiom ','set_option']:assert x not in source
 (OUT/'D13R10.lean').write_text(source);(FC/'D13R10.lean').write_text(source)
 log=call(['lake','env','lean','-o',str(OUT/'D13R10.olean'),'D13R10.lean'],'compile.log',900)
 ax={}
 for n in names:
  a=re.findall(r"'"+re.escape(n)+r"' depends on axioms:\s*\[([^\]]*)\]",log,re.S)
  z=re.findall(r"'"+re.escape(n)+r"' does not depend on any axioms",log)
  assert len(a)+len(z)==1,(n,a,z)
  deps=[] if z or not a[0].strip() else [x.strip() for x in a[0].split(',')]
  assert set(deps)<={'propext','Classical.choice','Quot.sound'},(n,deps)
  ax[n]=deps
 (OUT/'axioms.json').write_text(json.dumps(ax,indent=2)+'\n');(OUT/'classes.json').write_text(json.dumps(records,indent=2)+'\n')
 assert (OUT/'D13R10.olean').stat().st_size>0
 state.update(passed=True,new_classes=12,cumulative_classes=116,axioms_records=len(ax),source_sha256=hashlib.sha256(source.encode()).hexdigest())
 save();shutil.copy2(__file__,OUT/'build.py')
 (OUT/'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+str(p.relative_to(OUT))+'\n' for p in sorted(OUT.rglob('*')) if p.is_file() and p.name!='SHA256SUMS'))
 print('D13_R10_KERNEL_PASS',state,flush=True)
if __name__=='__main__':
 try:main()
 except Exception as e:state['error']=repr(e);save();raise
