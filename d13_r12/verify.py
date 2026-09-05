from pathlib import Path
import subprocess,sys,shutil,json,re,hashlib,os
R=Path(__file__).resolve().parent
F=Path(sys.argv[1]).resolve()
O=R/'evidence';O.mkdir(exist_ok=True)
status={'passed':False,'new_classes_checked':0,'run_id':os.getenv('GITHUB_RUN_ID'),'commit':os.getenv('GITHUB_SHA')}
def save(): (O/'status.json').write_text(json.dumps(status,indent=2))
def command(args,name,seconds=1500):
 result=subprocess.run(args,cwd=F,capture_output=True,text=True,timeout=seconds)
 text=result.stdout+result.stderr
 (O/name).write_text(text);print(text,flush=True)
 if result.returncode: raise RuntimeError((name,result.returncode))
 return text
def audit(text,names):
 out={}
 for name in names:
  records=re.findall("'"+re.escape(name)+r"' depends on axioms:\s*\[([^\]]*)\]",text)
  zero=re.findall("'"+re.escape(name)+r"' does not depend on any axioms",text)
  assert len(records)+len(zero)==1,name
  deps=[] if zero or not records[0].strip() else [d.strip() for d in records[0].split(',')]
  assert set(deps)<={'propext','Classical.choice','Quot.sound'},(name,deps)
  out[name]=deps
 return out
ROWS={'q1':[[140168437,176091,134941],[145453877,182731,124020],[116005459,194314,60605],[130676137,218888,170132],[108527039,272681,33044],[111208763,279419,46241]],'q2':[[162694201,43735,23668],[116615491,125393,85517],[120621931,129701,36763],[140894071,151499,65357],[174587971,187729,84566],[209807071,225599,96589]]}
def power(M,E,label):
 lines=[];known={}
 def visit(e):
  if e in known:return known[e]
  name=label+str(e);v=pow(10,e,M)
  if e==1:lines.append(f'  have {name} : Nat.ModEq {M} ((10 : ℕ)^1) {v} := by norm_num [Nat.ModEq]')
  else:
   a=e//2;b=e-a;x=visit(a);y=visit(b)
   lines.append(f'  have {name} : Nat.ModEq {M} ((10 : ℕ)^{e}) {v} :=\n    modpow_step {M} 10 {a} {b} {e} {pow(10,a,M)} {pow(10,b,M)} {v} (by decide) {x} {y} (by norm_num [Nat.ModEq])')
  known[e]=name;return name
 h=visit(E);return '\n'.join(lines)+'\n',h
def generate():
 code='import D13R11\n/-! Additional proper-factor proofs. -/\nnamespace D13\n';names=[];rows=[]
 for fam,vs in ROWS.items():
  A,a,b,D=(740,136,199,2391) if fam=='q1' else (370,666,930,2177)
  for p,m,r in vs:
   M=D*p;E=a+b*r;T=b*m;n=f'r12_{fam}_{p}'
   assert 1<p<10**9 and (A*pow(10,E,M)+1)%M==0 and pow(10,T,M)==1
   code+=f'theorem {n}_dvd (k : ℕ) : {p} ∣ {fam} ({r}+{m}*k) := by\n'
   chain,h=power(M,E,'b');code+=chain
   code+=f'  have hb : Nat.ModEq {M} ({A}*10^{E}+1) 0 :=\n    (((Nat.ModEq.refl {A}).mul {h}).add (Nat.ModEq.refl 1)).trans (by norm_num [Nat.ModEq])\n'
   chain,h=power(M,T,'s');code+=chain
   code+=f'  exact divisor_on_class_explicit {A} {a} {b} {D} {p} {r} {m} k {E} {T} {M} (by decide) (by decide) (by decide) (by decide) hb {h}\n'
   code+=f'theorem {n}_not_prime (k : ℕ) : ¬ Nat.Prime ({fam} ({r}+{m}*k)) := by\n  apply not_prime_of_proper_factor (d := {p}) (by decide)\n  · exact lt_trans (by decide : {p}<1000000000) ({fam}_large _)\n  · exact {n}_dvd k\n'
   names.append('D13.'+n+'_not_prime');rows.append([fam,p,m,r,n+'_not_prime'])
 code+='end D13\n'+'\n'.join('#print axioms '+n for n in names)+'\n'
 return code,names,rows
def main():
 save()
 command([sys.executable,str(R.parent/'d13_r11/build.py'),str(F)],'parent.log')
 P=R.parent/'d13_r11/evidence'
 assert json.loads((P/'status.json').read_text())['passed']
 L=F/'.lake/build/lib/lean'
 shutil.copy2(P/'D13R11.olean',L/'D13R11.olean')
 shutil.copy2(R.parent/'d13_r9/evidence/D13R9Reconstruction.olean',L/'D13R9Reconstruction.olean')
 shutil.copy2(P/'status.json',O/'parent_status.json')
 code,names,rows=generate()
 for forbidden in ['sorry','admit','native_decide','set_option','axiom ']:assert forbidden not in code
 (F/'D13R12.lean').write_text(code);(O/'D13R12.lean').write_text(code)
 text=command(['lake','env','lean','-o',str(O/'D13R12.olean'),'D13R12.lean'],'classes.log',600)
 ax=audit(text,names)
 (O/'classes.json').write_text(json.dumps(rows,indent=2));(O/'axioms.json').write_text(json.dumps(ax,indent=2))
 status['new_classes_checked']=12;status['cumulative_classes']=140;save()
 code=(R/'TwoPrimeEncoding.lean').read_text()
 names=['D13.R12.'+n for n in re.findall(r'^theorem (\w+)',code,re.M)]
 for forbidden in ['sorry','admit','native_decide','set_option','axiom ']:assert forbidden not in code
 code+='\n'+'\n'.join('#print axioms '+n for n in names)+'\n'
 (F/'D13R12Encoding.lean').write_text(code);(O/'D13R12Encoding.lean').write_text(code)
 text=command(['lake','env','lean','-o',str(O/'D13R12Encoding.olean'),'D13R12Encoding.lean'],'encoding.log',300)
 ax.update(audit(text,names));(O/'axioms.json').write_text(json.dumps(ax,indent=2))
 status.update(passed=True,encoding_theorems=names,axioms_records=len(ax));save()
 shutil.copy2(__file__,O/'verify.py')
 (O/'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.name+'\n'for p in sorted(O.iterdir())if p.is_file()and p.name!='SHA256SUMS'))
 print('D13_R12_VERIFIED',status,flush=True)
if __name__=='__main__':
 try:main()
 except Exception as error:status['error']=repr(error);save();raise
