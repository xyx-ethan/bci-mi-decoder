from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,sys
R=Path(__file__).resolve().parent;F=Path(sys.argv[1]).resolve();O=R/'evidence_structural';O.mkdir(parents=True,exist_ok=True)
PIN='8323e878b83fcd7f4a448256069352a265460d75';MATHLIB='0df444a360eaa60ab8c11dca51a86af692955474';state={'passed':False,'strict_build':False,'run_id':os.getenv('GITHUB_RUN_ID'),'commit':os.getenv('GITHUB_SHA')}
def save():(O/'status.json').write_text(json.dumps(state,indent=2)+'\n')
def call(args,name,timeout=1800):
 r=subprocess.run(args,cwd=F,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=timeout);(O/name).write_text(r.stdout);print(r.stdout,flush=True)
 if r.returncode:raise RuntimeError((name,r.returncode))
 return r.stdout
def main():
 save();assert call(['git','rev-parse','HEAD'],'upstream_commit.log').strip()==PIN;assert(F/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.33.1';man=json.loads((F/'lake-manifest.json').read_text());assert next(p['rev'] for p in man['packages'] if p['name']=='mathlib')==MATHLIB
 src=(R/'StructuralReduction.lean').read_text()
 for bad in ['sorry','admit','native_decide','Lean.ofReduceBool','Lean.trustCompiler','unsafe','axiom ','maxRecDepth']:assert bad not in src,bad
 mod=F/'D13Round19Structural';mod.mkdir(exist_ok=True);(mod/'StructuralReduction.lean').write_text(src);shutil.copy2(R/'StructuralReduction.lean',O/'StructuralReduction.lean')
 lake=F/'lakefile.toml';txt=lake.read_text();old='defaultTargets = ["FormalConjectures", "FormalConjecturesUtil", "FormalConjecturesForMathlib"]';assert old in txt;txt=txt.replace(old,'defaultTargets = ["D13Round19Structural"]',1);txt+='\n[[lean_lib]]\nname = "D13Round19Structural"\nglobs = ["D13Round19Structural.+"]\n';lake.write_text(txt);(O/'lakefile.strict.toml').write_text(txt)
 call(['lake','exe','cache','get'],'cache.log',1500);log=call(['lake','--wfail','build'],'lake_wfail_build.log',1500)
 n='D13Round19Structural.finite_fge2_structural_reduction';a=re.findall(r"'"+re.escape(n)+r"' depends on axioms:\s*\[([^\]]*)\]",log,re.S);z=re.findall(r"'"+re.escape(n)+r"' does not depend on any axioms",log);assert len(a)+len(z)==1,(a,z);deps=[] if z or not a[0].strip() else [x.strip()for x in a[0].split(',')];assert set(deps)<={'propext','Classical.choice','Quot.sound'},deps;(O/'axioms.json').write_text(json.dumps({n:deps},indent=2)+'\n');state.update(passed=True,strict_build=True,command='lake --wfail build',upstream_commit=PIN,lean_toolchain='leanprover/lean4:v4.33.1',mathlib_revision=MATHLIB,source_sha256=hashlib.sha256(src.encode()).hexdigest());save();shutil.copy2(__file__,O/'build_structural.py');(O/'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.name+'\n'for p in sorted(O.iterdir())if p.is_file()and p.name!='SHA256SUMS'));print('D13_R19_STRUCTURAL_STRICT_PASS',state,flush=True)
if __name__=='__main__':
 try:main()
 except Exception as e:state['error']=repr(e);save();raise
