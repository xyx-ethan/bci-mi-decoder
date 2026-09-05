from pathlib import Path
import subprocess,time,json,re,concurrent.futures,hashlib
O=Path('factor_evidence');O.mkdir(exist_ok=True)
CONFIG={'q1':(740,733,2391,120000),'q2':(370,666,2177,220000)}
def one(fam):
 A,E,D,seed=CONFIG[fam];N=(A*10**E+1)//D
 assert D*N==A*10**E+1
 start=time.monotonic();records=[];factors=[]
 for i in range(40):
  remaining=480-(time.monotonic()-start)
  if remaining<1:break
  args=['ecm','-sigma',str(seed+i),'1000000','100000000']
  try:
   result=subprocess.run(args,input=str(N)+'\n',capture_output=True,text=True,timeout=remaining)
   text=result.stdout+result.stderr;timed=False;rc=result.returncode
  except subprocess.TimeoutExpired as err:
   out=err.stdout or b'';error=err.stderr or b''
   text=(out.decode() if isinstance(out,bytes)else out)+(error.decode() if isinstance(error,bytes)else error)
   timed=True;rc=None
  (O/f'{fam}_{i:03d}.log').write_text(text)
  found=[int(v) for v in re.findall(r'Factor found in step\s+\d\s*:\s*(\d+)',text)]
  found=[d for d in found if 1<d<N]
  for d in found:
   assert N%d==0;factors.append(str(d))
  records.append({'curve':i,'sigma':seed+i,'returncode':rc,'timed_out':timed,'stage1_completed':'Step 1 took' in text,'stage2_completed':'Step 2 took' in text,'verified_factors':[str(d)for d in found]})
  if found or timed:break
 obj={'family':fam,'t':3 if fam=='q1' else 0,'A':A,'exponent':E,'D':D,'N':str(N),'B1':1000000,'B2':100000000,'wall_cap_seconds':480,'records':records,'factors':factors,'elapsed_seconds':time.monotonic()-start}
 (O/(fam+'.json')).write_text(json.dumps(obj,indent=2));print(fam,len(records),factors,flush=True)
 return obj
if __name__=='__main__':
 with concurrent.futures.ThreadPoolExecutor(max_workers=2)as pool:
  data=list(pool.map(one,CONFIG))
 (O/'SUMMARY.json').write_text(json.dumps(data,indent=2))
 (O/'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.name+'\n'for p in sorted(O.iterdir())if p.is_file()and p.name!='SHA256SUMS'))
