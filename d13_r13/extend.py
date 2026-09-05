from pathlib import Path
import sys,subprocess,hashlib,shutil,json,re,os
R=Path(__file__).resolve().parent;F=Path(sys.argv[1]).resolve();O=R/'evidence'
subprocess.run([sys.executable,str(R/'verify.py'),str(F)],check=True)
state=json.loads((O/'status.json').read_text());assert state['passed']
shutil.copy2(O/'D13R13Bounds.olean',F/'.lake/build/lib/lean/D13R13Bounds.olean')
source=(R/'SevenBranches.lean').read_text();names=['D13.R13.'+n for n in re.findall(r'^theorem (\w+)',source,re.M)]
for bad in ['sorry','admit','native_decide','set_option','axiom ']:assert bad not in source
source+='\n'+'\n'.join('#print axioms '+n for n in names)+'\n'
(F/'D13R13Seven.lean').write_text(source);(O/'D13R13Seven.lean').write_text(source)
r=subprocess.run(['lake','env','lean','-o',str(O/'D13R13Seven.olean'),'D13R13Seven.lean'],cwd=F,text=True,capture_output=True,timeout=600)
text=r.stdout+r.stderr;(O/'seven.log').write_text(text);print(text,flush=True)
state['seven_passed']=False
if not r.returncode:
 ax=json.loads((O/'axioms.json').read_text())
 for name in names:
  a=re.findall("'"+re.escape(name)+r"' depends on axioms:\s*\[([^\]]*)\]",text,re.S)
  z=re.findall("'"+re.escape(name)+r"' does not depend on any axioms",text)
  assert len(a)+len(z)==1,name
  deps=[] if z or not a[0].strip() else [x.strip() for x in a[0].split(',')]
  assert set(deps)<={'propext','Classical.choice','Quot.sound'},(name,deps)
  ax[name]=deps
 (O/'axioms.json').write_text(json.dumps(ax,indent=2));state.update(seven_passed=True,seven_theorems=names,axioms_records=len(ax))
else:state['seven_error']='Lean exited '+str(r.returncode)
(O/'status.json').write_text(json.dumps(state,indent=2));shutil.copy2(__file__,O/'extend.py')
(O/'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.name+'\n' for p in sorted(O.iterdir())if p.is_file()and p.name!='SHA256SUMS'))
if r.returncode:raise SystemExit(r.returncode)
print('D13_R13_SEVEN_BRANCHES_PASS',state,flush=True)
