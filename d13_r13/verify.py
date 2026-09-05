from pathlib import Path
import subprocess,sys,shutil,json,re,hashlib,os,importlib.util
R=Path(__file__).resolve().parent;F=Path(sys.argv[1]).resolve();O=R/'evidence';O.mkdir(exist_ok=True)
state={'passed':False,'new_classes_checked':0,'run_id':os.getenv('GITHUB_RUN_ID'),'commit':os.getenv('GITHUB_SHA')}
def save():(O/'status.json').write_text(json.dumps(state,indent=2)+'\n')
def call(args,name,seconds=1500):
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
ROWS={'q1':[[521,52,16],[107,53,45],[59,58,0],[61,60,47],[191,95,23],[199,99,52]],'q2':[[1741,58,25],[367,61,10],[877,73,67],[1481,74,29],[457,76,74],[317,79,30]]}
def main():
 save();call([sys.executable,str(R.parent/'d13_r12/verify.py'),str(F)],'parent.log')
 P=R.parent/'d13_r12/evidence';assert json.loads((P/'status.json').read_text())['passed']
 L=F/'.lake/build/lib/lean'
 for name in ['D13R12','D13R12Encoding']:shutil.copy2(P/(name+'.olean'),L/(name+'.olean'))
 shutil.copy2(P/'status.json',O/'parent_status.json')
 spec=importlib.util.spec_from_file_location('parent_verify',R.parent/'d13_r12/verify.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
 mod.ROWS=ROWS
 code,names,records=mod.generate();code=code.replace('import D13R11','import D13R12').replace('r12_','r13_');names=[n.replace('r12_','r13_')for n in names]
 records=[r[:-1]+[r[-1].replace('r12_','r13_')]for r in records]
 for s in ['sorry','admit','native_decide','set_option','axiom ']:assert s not in code
 (F/'D13R13.lean').write_text(code);(O/'D13R13.lean').write_text(code)
 text=call(['lake','env','lean','-o',str(O/'D13R13.olean'),'D13R13.lean'],'classes.log',600)
 ax=audit(text,names);(O/'classes.json').write_text(json.dumps(records,indent=2));(O/'classes_axioms.json').write_text(json.dumps(ax,indent=2))
 state.update(new_classes_checked=12,cumulative_classes=152);save()
 code=(R/'Bounds.lean').read_text();names=['D13.R13.'+n for n in re.findall(r'^theorem (\w+)',code,re.M)]
 for s in ['sorry','admit','native_decide','set_option','axiom ']:assert s not in code
 code+='\n'+'\n'.join('#print axioms '+n for n in names)+'\n'
 (F/'D13R13Bounds.lean').write_text(code);(O/'D13R13Bounds.lean').write_text(code)
 text=call(['lake','env','lean','-o',str(O/'D13R13Bounds.olean'),'D13R13Bounds.lean'],'bounds.log',600)
 ax.update(audit(text,names));(O/'axioms.json').write_text(json.dumps(ax,indent=2))
 state.update(passed=True,bounds_theorems=names,axioms_records=len(ax));save();shutil.copy2(__file__,O/'verify.py')
 (O/'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.name+'\n'for p in sorted(O.iterdir())if p.is_file()and p.name!='SHA256SUMS'))
 print('D13_R13_KERNEL_PASS',state,flush=True)
if __name__=='__main__':
 try:main()
 except Exception as e:state['error']=repr(e);save();raise
