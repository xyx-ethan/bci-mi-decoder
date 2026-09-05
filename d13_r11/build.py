from pathlib import Path
import sys,subprocess,shutil,json,hashlib,re,os,urllib.request
ROOT=Path(__file__).resolve().parent;FC=Path(sys.argv[1]).resolve();OUT=ROOT/'evidence';OUT.mkdir(exist_ok=True)
state={'passed':False,'run_id':os.getenv('GITHUB_RUN_ID'),'commit':os.getenv('GITHUB_SHA')}
ALLOW={'propext','Classical.choice','Quot.sound'}
def save():(OUT/'status.json').write_text(json.dumps(state,indent=2)+'\n')
def call(args,name,timeout=1500):
 r=subprocess.run(args,cwd=FC,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=timeout)
 (OUT/name).write_text(r.stdout);print(r.stdout,flush=True)
 if r.returncode:raise RuntimeError((name,r.returncode))
 return r.stdout
def audit(text,names):
 ret={}
 for n in names:
  a=re.findall(r"'"+re.escape(n)+r"' depends on axioms:\s*\[([^\]]*)\]",text,re.S)
  z=re.findall(r"'"+re.escape(n)+r"' does not depend on any axioms",text)
  assert len(a)+len(z)==1,(n,a,z)
  deps=[] if z or not a[0].strip() else [x.strip()for x in a[0].split(',')]
  assert set(deps)<=ALLOW,(n,deps)
  ret[n]=deps
 return ret
ROWS={'q1':[(251922061,1265940,445509),(256282151,25757,10987),(124903147,104609,66105),(135707653,170487,53575),(123738599,310901,24109),(172317683,432959,383923)],'q2':[(252854911,271887,1253),(249623161,67103,7188),(137241961,73786,17537),(158378071,170299,116705),(161329891,173473,100969),(100427911,107987,97966)]}
HIST={'q1':[(7,6,0,8),(13,6,2,8),(73,8,5,8),(17,16,6,8),(23,22,13,8),(29,28,19,9)],'q2':[(17,8,1,8),(29,14,7,8),(97,16,6,8),(109,18,11,9),(157,13,3,8),(53,13,7,8)]}
def main():
 save();call([sys.executable,str(ROOT.parent/'d13_r10/build.py'),str(FC)],'parent_rebuild.log')
 parent=ROOT.parent/'d13_r10/evidence';assert json.loads((parent/'status.json').read_text())['passed']
 lib=FC/'.lake/build/lib/lean';shutil.copy2(parent/'D13R10.olean',lib/'D13R10.olean')
 (OUT/'parent').mkdir(exist_ok=True)
 for n in ['status.json','axioms.json','compile.log','classes.json','D13R10.lean']:shutil.copy2(parent/n,OUT/'parent'/n)
 # Fetch exact historical originals and verify Git blob identities, not branch HEAD.
 historical={}
 for fn,sha in [('A067599CI.lean','adb0d8f5eb016a5be90b84892275bc1a32e5c30f'),('a067599-squarefree.patch','4bb701c594e17b921d0d85b0a5203e5075e25c49')]:
  url='https://raw.githubusercontent.com/xyx-ethan/xyx-ethan.github.io/506bbcdeb6c28e170cefcef0d6cda3e3ab101df0/research/a067599-ci/'+fn
  raw=urllib.request.urlopen(url,timeout=60).read()
  assert hashlib.sha1(('blob '+str(len(raw))+'\0').encode()+raw).hexdigest()==sha
  historical[fn]=raw.decode();(OUT/fn).write_bytes(raw)
 added='\n'.join(x[1:]for x in historical['a067599-squarefree.patch'].splitlines()if x.startswith('+')and not x.startswith('+++'))
 sq='import FormalConjectures.OEIS.«67599»\nnamespace OeisA67599\n'+added+'\nend OeisA67599\n'
 sqnames=['OeisA67599.lt_a_of_squarefree','OeisA67599.a_ne_of_squarefree']
 sq+='\n'+'\n'.join('#print axioms '+n for n in sqnames)+'\n'
 (FC/'HistoricalSquarefree.lean').write_text(sq);(OUT/'HistoricalSquarefree.lean').write_text(sq)
 log=call(['lake','env','lean','-o',str(lib/'HistoricalSquarefree.olean'),'HistoricalSquarefree.lean'],'squarefree.log')
 ax=audit(log,sqnames);shutil.copy2(lib/'HistoricalSquarefree.olean',OUT/'HistoricalSquarefree.olean')
 orig=historical['A067599CI.lean'].replace('import FormalConjectures.OEIS.«67599»','import HistoricalSquarefree',1)
 hnames=['OeisA67599.'+n for n in re.findall(r'^theorem (\w+)',orig,re.M)]
 assert len(hnames)==12
 orig+='\n'+'\n'.join('#print axioms '+n for n in hnames)+'\n'
 (FC/'HistoricalOriginal.lean').write_text(orig);(OUT/'HistoricalOriginal.lean').write_text(orig)
 log=call(['lake','env','lean','-o',str(lib/'HistoricalOriginal.olean'),'HistoricalOriginal.lean'],'historical_original.log')
 ax.update(audit(log,hnames));shutil.copy2(lib/'HistoricalOriginal.olean',OUT/'HistoricalOriginal.olean')
 sys.path.insert(0,str(ROOT.parent/'d13_r8'));import run
 prefix=(ROOT.parent/'d13_r8/repair.py').read_text().split('def provenance():',1)[0]
 exec(compile(prefix,'repair.py','exec'),{})
 source='import D13R10\nimport HistoricalOriginal\nnamespace D13\n';names=[];records=[]
 for f,rs in ROWS.items():
  for p,m,r in rs:
   s,n=run.theorem(f,p,m,r);source+=s.replace('r8_','r11_')+'\n';names.append('D13.'+n.replace('r8_','r11_'))
   records.append({'family':f,'prime':p,'period':m,'residue':r,'theorem':names[-1]})
 source+='end D13\nnamespace OeisA67599\n'
 for f,rs in HIST.items():
  fam='residualFamilyOne'if f=='q1'else'residualFamilyTwo'
  for p,m,r,round in rs:
   name=f'original12_{f}_{p}_not_prime';names.append('OeisA67599.'+name)
   source+=f'theorem {name} (k : ℕ) : ¬ Nat.Prime ({fam} ({r}+{m}*k)) := by\n  change ¬ Nat.Prime (D13.{f} ({r}+{m}*k))\n  exact D13.r{round}_{f}_{p}_not_prime k\n'
 source+='end OeisA67599\n'+'\n'.join('#print axioms '+n for n in names)+'\n'
 for bad in ['sorry','admit','native_decide','maxRecDepth','axiom ','set_option']:assert bad not in source
 (FC/'D13R11.lean').write_text(source);(OUT/'D13R11.lean').write_text(source)
 log=call(['lake','env','lean','-o',str(OUT/'D13R11.olean'),'D13R11.lean'],'compile.log',900)
 ax.update(audit(log,names));(OUT/'axioms.json').write_text(json.dumps(ax,indent=2)+'\n')
 (OUT/'classes.json').write_text(json.dumps(records,indent=2)+'\n');(OUT/'historical_classes.json').write_text(json.dumps(HIST,indent=2)+'\n')
 state.update(passed=True,new_classes=12,cumulative_classes=128,historical_original_divisor_classes_rebuilt=12,historical_proper_factor_wrappers=12,squarefree_baseline_rebuilt=True,axioms_records=len(ax),source_sha256=hashlib.sha256(source.encode()).hexdigest())
 save();shutil.copy2(__file__,OUT/'build.py')
 (OUT/'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+str(p.relative_to(OUT))+'\n'for p in sorted(OUT.rglob('*'))if p.is_file()and p.name!='SHA256SUMS'))
 print('D13_R11_KERNEL_HISTORICAL_AND_NEW_CLASSES_PASS',state,flush=True)
if __name__=='__main__':
 try:main()
 except Exception as e:state['error']=repr(e);save();raise
