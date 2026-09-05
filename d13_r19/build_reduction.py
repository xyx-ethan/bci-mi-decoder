from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,sys
ROOT=Path(__file__).resolve().parent;FC=Path(sys.argv[1]).resolve();OUT=ROOT/'evidence_reduction';OUT.mkdir(parents=True,exist_ok=True)
PIN='8323e878b83fcd7f4a448256069352a265460d75';MATHLIB='0df444a360eaa60ab8c11dca51a86af692955474';state={'passed':False,'strict_build':False,'run_id':os.getenv('GITHUB_RUN_ID'),'commit':os.getenv('GITHUB_SHA')};ALLOW={'propext','Classical.choice','Quot.sound'}
def save():(OUT/'status.json').write_text(json.dumps(state,indent=2)+'\n')
def call(args,name,timeout=2100):
 r=subprocess.run(args,cwd=FC,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=timeout);(OUT/name).write_text(r.stdout);print(r.stdout,flush=True)
 if r.returncode:raise RuntimeError((name,r.returncode))
 return r.stdout
def main():
 save();assert call(['git','rev-parse','HEAD'],'upstream_commit.log').strip()==PIN
 assert (FC/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.33.1'
 man=json.loads((FC/'lake-manifest.json').read_text());assert next(p['rev'] for p in man['packages'] if p['name']=='mathlib')==MATHLIB
 src=(ROOT/'FiniteFge2Reduction.lean').read_text()
 for bad in ['sorry','admit','native_decide','Lean.ofReduceBool','Lean.trustCompiler','unsafe','axiom ','maxRecDepth']:assert bad not in src,bad
 mod=FC/'D13Round19Reduction';mod.mkdir(exist_ok=True);(mod/'FiniteFge2Reduction.lean').write_text(src);shutil.copy2(ROOT/'FiniteFge2Reduction.lean',OUT/'FiniteFge2Reduction.lean')
 lake=FC/'lakefile.toml';txt=lake.read_text();old='defaultTargets = ["FormalConjectures", "FormalConjecturesUtil", "FormalConjecturesForMathlib"]';assert old in txt;txt=txt.replace(old,'defaultTargets = ["D13Round19Reduction"]',1);txt+='\n[[lean_lib]]\nname = "D13Round19Reduction"\nglobs = ["D13Round19Reduction.+"]\n';lake.write_text(txt);(OUT/'lakefile.strict.toml').write_text(txt)
 call(['lake','exe','cache','get'],'cache.log',1500);log=call(['lake','--wfail','build'],'lake_wfail_build.log',1800)
 names=['D13Round19Reduction.cases_length','D13Round19Reduction.finite_fge2_reduces_to_cases'];ax={}
 for n in names:
  a=re.findall(r"'"+re.escape(n)+r"' depends on axioms:\s*\[([^\]]*)\]",log,re.S);z=re.findall(r"'"+re.escape(n)+r"' does not depend on any axioms",log);assert len(a)+len(z)==1,(n,a,z);deps=[] if z or not a[0].strip() else [x.strip() for x in a[0].split(',')];assert set(deps)<=ALLOW,(n,deps);ax[n]=deps
 (OUT/'axioms.json').write_text(json.dumps(ax,indent=2)+'\n');state.update(passed=True,strict_build=True,command='lake --wfail build',upstream_commit=PIN,lean_toolchain='leanprover/lean4:v4.33.1',mathlib_revision=MATHLIB,source_sha256=hashlib.sha256(src.encode()).hexdigest(),axioms_records=len(ax));save();shutil.copy2(__file__,OUT/'build_reduction.py');(OUT/'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.name+'\n' for p in sorted(OUT.iterdir()) if p.is_file() and p.name!='SHA256SUMS'));print('D13_R19_REDUCTION_STRICT_PASS',state,flush=True)
if __name__=='__main__':
 try:main()
 except Exception as e:state['error']=repr(e);save();raise
