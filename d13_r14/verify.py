from pathlib import Path
import subprocess,sys,json,re,hashlib,shutil,os
# Audit retrigger: proof source is unchanged; this commit only reruns the pinned kernel
# after installing the rebuilt parent power object into Lean's library search path.
R=Path(__file__).resolve().parent;F=Path(sys.argv[1]).resolve();O=R/'evidence';O.mkdir(exist_ok=True)
state={'passed':False,'run_id':os.getenv('GITHUB_RUN_ID'),'commit':os.getenv('GITHUB_SHA')}
def save():(O/'status.json').write_text(json.dumps(state,indent=2)+'\n')
def call(args,name,timeout=1800):
 r=subprocess.run(args,cwd=F,text=True,capture_output=True,timeout=timeout)
 text=r.stdout+r.stderr;(O/name).write_text(text);print(text,flush=True)
 if r.returncode:raise RuntimeError((name,r.returncode))
 return text
def audit(text,names):
 out={}
 for n in names:
  a=re.findall("'"+re.escape(n)+r"' depends on axioms:\s*\[([^\]]*)\]",text,re.S)
  z=re.findall("'"+re.escape(n)+r"' does not depend on any axioms",text)
  assert len(a)+len(z)==1,(n,a,z)
  deps=[] if z or not a[0].strip() else [x.strip()for x in a[0].split(',')]
  assert set(deps)<={'propext','Classical.choice','Quot.sound'},(n,deps)
  out[n]=deps
 return out
try:
 save()
 call([sys.executable,str(R.parent/'d13_r13/finish.py'),str(F)],'parent.log')
 P=R.parent/'d13_r13/evidence';ps=json.loads((P/'status.json').read_text());assert ps['power_passed']
 # finish.py writes the certified power module into its evidence directory rather
 # than the upstream library search path. Install that exact rebuilt object before
 # compiling ResidualBridge.lean. This is plumbing only: no proof source changes.
 lib=F/'.lake/build/lib/lean';lib.mkdir(parents=True,exist_ok=True)
 shutil.copy2(P/'D13R13Power.olean',lib/'D13R13Power.olean')
 source=(R/'ResidualBridge.lean').read_text();names=['D13.R14.'+n for n in re.findall(r'^theorem (\w+)',source,re.M)]
 for bad in ['sorry','admit','native_decide','set_option maxRecDepth','axiom ']:assert bad not in source
 source+='\n'+'\n'.join('#print axioms '+n for n in names)+'\n'
 (F/'D13R14Bridge.lean').write_text(source);(O/'D13R14Bridge.lean').write_text(source)
 text=call(['lake','env','lean','-o',str(O/'D13R14Bridge.olean'),'D13R14Bridge.lean'],'compile.log',900)
 ax=audit(text,names);(O/'axioms.json').write_text(json.dumps(ax,indent=2)+'\n')
 state.update(passed=True,theorems=names,axioms_records=len(ax),source_sha256=hashlib.sha256(source.encode()).hexdigest())
 save();shutil.copy2(__file__,O/'verify.py')
 (O/'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.name+'\n'for p in sorted(O.iterdir())if p.is_file()and p.name!='SHA256SUMS'))
 print('D13_R14_F1_RESIDUAL_EQUIVALENCE_PASS',state,flush=True)
except Exception as e:
 state['error']=repr(e);save();raise
