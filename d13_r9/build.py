from pathlib import Path
import sys,subprocess,json,shutil,hashlib,re,os
ROOT=Path(__file__).resolve().parent
FC=Path(sys.argv[1]).resolve()
OUT=ROOT/'evidence'; OUT.mkdir(exist_ok=True)
ALLOW={'propext','Classical.choice','Quot.sound'}
state={'passed':False,'run_id':os.getenv('GITHUB_RUN_ID'),'commit':os.getenv('GITHUB_SHA')}
def save(): (OUT/'status.json').write_text(json.dumps(state,indent=2)+'\n')
def call(args,name,timeout=1200):
 print('RUN',args,flush=True)
 r=subprocess.run(args,cwd=FC,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=timeout)
 (OUT/name).write_text(r.stdout);print(r.stdout,flush=True)
 if r.returncode:raise RuntimeError(f'{name}: {r.returncode}')
 return r.stdout
def audit(text,names):
 result={}
 for n in names:
  a=re.findall(r"'"+re.escape(n)+r"' depends on axioms:\s*\[([^\]]*)\]",text,re.S)
  z=re.findall(r"'"+re.escape(n)+r"' does not depend on any axioms",text)
  assert len(a)+len(z)==1,(n,a,z)
  aa=[] if z or not a[0].strip() else [x.strip() for x in a[0].split(',')]
  assert set(aa)<=ALLOW,(n,aa)
  result[n]=aa
 return result
ROWS={'q1':[(29,28,19),(211,30,5),(67,33,8),(83,41,11),(47,46,44),(139,46,45)],
      'q2':[(109,18,11),(47,23,16),(199,33,8),(173,43,41),(197,49,6),(113,56,24)]}
SUPPORT=r'''
theorem Q_exact (A a b D t : ℕ)
    (hb : Nat.ModEq D (A * 10^a + 1) 0)
    (hs : Nat.ModEq D (10^b) 1) :
    D * Q A a b D t = A * 10^(a+b*t)+1 := by
  have hp : Nat.ModEq D ((10^b)^t) 1 := by
    simpa only [one_pow] using Nat.ModEq.pow t hs
  have hm := ((Nat.ModEq.refl (A*10^a)).mul hp).add (Nat.ModEq.refl 1)
  have hn : Nat.ModEq D (A*10^(a+b*t)+1) 0 := by
    have h : Nat.ModEq D (A*10^(a+b*t)+1) (A*10^a+1) := by
      rw [pow_add, pow_mul, ← mul_assoc]
      simpa only [mul_one] using hm
    exact h.trans hb
  have hz : (A*10^(a+b*t)+1) % D = 0 := by
    simpa only [Nat.ModEq, Nat.zero_mod] using hn
  have hdiv := Nat.dvd_of_mod_eq_zero hz
  exact Nat.mul_div_cancel' hdiv
'''
def main():
 save()
 # Rebuild R8 itself under the same exact pins; no precompiled local object is trusted.
 call([sys.executable,str(ROOT.parent/'d13_r8/repair.py'),str(FC)],'parent_build.log')
 parent=ROOT.parent/'d13_r8/evidence/bulk'
 assert json.loads((parent/'status.json').read_text())['passed'] is True
 shutil.copytree(parent,OUT/'parent',dirs_exist_ok=True)
 lib=FC/'.lake/build/lib/lean';lib.mkdir(parents=True,exist_ok=True)
 shutil.copy2(parent/'D13R8.olean',lib/'D13R8.olean')
 shutil.copy2(parent/'D13R8.lean',FC/'D13R8.lean')
 sys.path.insert(0,str(ROOT.parent/'d13_r8'))
 import run
 code=(ROOT.parent/'d13_r8/repair.py').read_text().split('def provenance():',1)[0]
 exec(compile(code,str(ROOT.parent/'d13_r8/repair.py'),'exec'),{})
 source='import D13R8\nnamespace D13\n'+SUPPORT
 names=['D13.Q_exact'];records=[]
 for fam,rows in ROWS.items():
  for p,m,r in rows:
   s,n=run.theorem(fam,p,m,r);s=s.replace('r8_','r9_');n=n.replace('r8_','r9_')
   source+='\n'+s+'\n';names.extend(['D13.'+n.removesuffix('_not_prime')+'_dvd','D13.'+n])
   records.append({'family':fam,'prime':p,'period':m,'residue':r,'theorem':'D13.'+n})
 for fam,A,a,b,D in [('q1',740,136,199,2391),('q2',370,666,930,2177)]:
  source+=f'\ntheorem r9_{fam}_exact (t : ℕ) : {D} * {fam} t = {A} * 10^({a}+{b}*t)+1 := by\n'
  ls,h=run.modpow(D,a,'ibase');source+='\n'.join(ls)+'\n'
  source+=f'  have hb : Nat.ModEq {D} ({A}*10^{a}+1) 0 :=\n    (((Nat.ModEq.refl {A}).mul {h}).add (Nat.ModEq.refl 1)).trans (by norm_num [Nat.ModEq])\n'
  ls,h=run.modpow(D,b,'istep');source+='\n'.join(ls)+'\n'
  source+=f'  exact Q_exact {A} {a} {b} {D} t hb {h}\n'
  names.append('D13.r9_'+fam+'_exact')
 source+='\nend D13\n'+'\n'.join('#print axioms '+n for n in names)+'\n'
 for bad in ['sorry','admit','native_decide','maxRecDepth','axiom ','set_option']:
  assert bad not in source,bad
 (FC/'D13R9Numbers.lean').write_text(source);(OUT/'D13R9Numbers.lean').write_text(source)
 (OUT/'classes.json').write_text(json.dumps(records,indent=2)+'\n')
 log=call(['lake','env','lean','-o',str(lib/'D13R9Numbers.olean'),'D13R9Numbers.lean'],'numbers.log')
 ax=audit(log,names)
 shutil.copy2(lib/'D13R9Numbers.olean',OUT/'D13R9Numbers.olean')
 state['numbers_passed']=True;save()
 # Compile the unmodified upstream module, including the exact a definition.
 call(['lake','-v','build','+FormalConjecturesUtil'],'upstream_util.log')
 target='FormalConjectures/OEIS/67599.lean'
 assert call(['git','hash-object',target],'upstream_blob.log').strip()=='2053c62162ccab78f52e66f15b65ad3206626f90'
 o=lib/'FormalConjectures/OEIS/67599.olean';o.parent.mkdir(parents=True,exist_ok=True)
 call(['lake','env','lean','-o',str(o),target],'upstream_original.log')
 shutil.copy2(FC/target,OUT/'67599.original.lean')
 bridge=(ROOT/'Reconstruction.lean').read_text()
 bnames=['D13.R9.'+n for n in re.findall(r'^theorem (\w+)',bridge,re.M)]
 for bad in ['sorry','admit','native_decide','maxRecDepth','axiom ','set_option']:
  assert bad not in bridge,bad
 bridge+='\n'+'\n'.join('#print axioms '+n for n in bnames)+'\n'
 (FC/'D13R9Reconstruction.lean').write_text(bridge);(OUT/'D13R9Reconstruction.lean').write_text(bridge)
 log=call(['lake','env','lean','-o',str(OUT/'D13R9Reconstruction.olean'),'D13R9Reconstruction.lean'],'reconstruction.log')
 ax.update(audit(log,bnames))
 (OUT/'axioms.json').write_text(json.dumps(ax,indent=2)+'\n')
 shutil.copy2(__file__,OUT/'build.py')
 state.update(passed=True,new_classes=12,cumulative_classes=104,axioms_records=len(ax),bridge_theorems=bnames,
              source_sha256=hashlib.sha256(source.encode()).hexdigest(),bridge_sha256=hashlib.sha256(bridge.encode()).hexdigest())
 save()
 (OUT/'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+str(p.relative_to(OUT))+'\n' for p in sorted(OUT.rglob('*')) if p.is_file() and p.name!='SHA256SUMS'))
 print('D13_R9_KERNEL_AND_ACTUAL_ENCODING_BRIDGE_PASS',state,flush=True)
if __name__=='__main__':
 try:main()
 except Exception as exc:
  state['error']=repr(exc);save();raise
