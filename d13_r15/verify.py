from pathlib import Path
import subprocess,sys,shutil,json,re,hashlib,os,importlib.util
R=Path(__file__).resolve().parent;F=Path(sys.argv[1]).resolve();O=R/'evidence';O.mkdir(exist_ok=True)
state={'passed':False,'new_classes_checked':0,'run_id':os.getenv('GITHUB_RUN_ID'),'commit':os.getenv('GITHUB_SHA')}
def save():(O/'status.json').write_text(json.dumps(state,indent=2)+'\n')
def call(args,name,seconds=1800):
 r=subprocess.run(args,cwd=F,capture_output=True,text=True,timeout=seconds)
 text=r.stdout+r.stderr;(O/name).write_text(text);print(text,flush=True)
 if r.returncode:raise RuntimeError((name,r.returncode))
 return text
def audit(text,names):
 out={}
 for n in names:
  a=re.findall("'"+re.escape(n)+r"' depends on axioms:\s*\[([^\]]*)\]",text,re.S)
  z=re.findall("'"+re.escape(n)+r"' does not depend on any axioms",text)
  assert len(a)+len(z)==1,n
  deps=[] if z or not a[0].strip() else [x.strip()for x in a[0].split(',')]
  assert set(deps)<={'propext','Classical.choice','Quot.sound'},(n,deps)
  out[n]=deps
 return out
ROWS={'q1':[[19,18,8],[97,96,24],[109,108,65],[331,110,2],[113,112,2],[131,130,118]],
      'q2':[[523,87,53],[911,91,67],[1237,103,37],[227,113,44],[709,118,55],[2287,127,48]]}
try:
 save()
 call([sys.executable,str(R.parent/'d13_r14/verify.py'),str(F)],'parent.log')
 P=R.parent/'d13_r14/evidence';assert json.loads((P/'status.json').read_text())['passed']
 lib=F/'.lake/build/lib/lean';lib.mkdir(parents=True,exist_ok=True)
 shutil.copy2(P/'D13R14Bridge.olean',lib/'D13R14Bridge.olean')
 spec=importlib.util.spec_from_file_location('parent_verify',R.parent/'d13_r12/verify.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
 mod.ROWS=ROWS
 code,names,records=mod.generate();code=code.replace('import D13R11','import D13R14Bridge').replace('r12_','r15_');names=[n.replace('r12_','r15_')for n in names]
 records=[r[:-1]+[r[-1].replace('r12_','r15_')]for r in records]
 for bad in ['sorry','admit','native_decide','set_option','axiom ']:assert bad not in code
 (F/'D13R15.lean').write_text(code);(O/'D13R15.lean').write_text(code)
 text=call(['lake','env','lean','-o',str(O/'D13R15.olean'),'D13R15.lean'],'compile.log',900)
 ax=audit(text,names);(O/'axioms.json').write_text(json.dumps(ax,indent=2)+'\n');(O/'classes.json').write_text(json.dumps(records,indent=2)+'\n')
 state.update(passed=True,new_classes_checked=12,cumulative_classes=164,theorems=names,axioms_records=len(ax),source_sha256=hashlib.sha256(code.encode()).hexdigest())
 save();shutil.copy2(__file__,O/'verify.py')
 (O/'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.name+'\n' for p in sorted(O.iterdir()) if p.is_file() and p.name!='SHA256SUMS'))
 print('D13_R15_SHORT_FACTOR_CLASSES_PASS',state,flush=True)
except Exception as e:
 state['error']=repr(e);save();raise
