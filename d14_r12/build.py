"""Compile exact D14 sources against a pinned upstream checkout; audit actual logs."""
from pathlib import Path
import hashlib, json, os, re, shutil, subprocess, sys, time

ROOT = Path(__file__).resolve().parent
FC = Path(sys.argv[1]).resolve()
OUT = ROOT / 'evidence'
OUT.mkdir(exist_ok=False)
FC_SHA = '8323e878b83fcd7f4a448256069352a265460d75'
ML_SHA = '0df444a360eaa60ab8c11dca51a86af692955474'
ALLOW = {'propext', 'Classical.choice', 'Quot.sound'}
state = {'lean_kernel_checked': False, 'phase': 'STARTED',
         'run_id': os.getenv('GITHUB_RUN_ID'), 'commit': os.getenv('GITHUB_SHA')}

def save():
    (OUT / 'status.json').write_text(json.dumps(state, indent=2) + '\n')

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def run(args, name, timeout=900):
    print('RUN', args, flush=True)
    r = subprocess.run(args, cwd=FC, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=timeout, check=False)
    (OUT / name).write_text(r.stdout)
    print(r.stdout, flush=True)
    if r.returncode:
        raise RuntimeError(f'{name}: exit {r.returncode}')
    return r.stdout

def audit(text, names):
    result = {}
    for name in names:
        a = re.findall(r"'" + re.escape(name) + r"' depends on axioms:\s*\[([^\]]*)\]", text, re.S)
        z = re.findall(r"'" + re.escape(name) + r"' does not depend on any axioms", text)
        if len(a) + len(z) != 1:
            raise ValueError(f'missing/duplicate axiom record: {name}')
        items = [] if z or not a[0].strip() else [x.strip() for x in a[0].split(',')]
        if any(not x or x not in ALLOW for x in items) or len(set(items)) != len(items):
            raise ValueError(f'forbidden/malformed axioms: {name}: {items}')
        result[name] = sorted(items)
    return result

save()
try:
    state['phase'] = 'PINS_AND_DEPENDENCIES'; save()
    assert run(['git', 'rev-parse', 'HEAD'], 'upstream_commit.log').strip() == FC_SHA
    target = FC / 'FormalConjectures/OEIS/51903.lean'
    assert run(['git', 'hash-object', str(target)], 'upstream_blob.log').strip() == 'b9264ef620d88d7a0061af131ba38d3092113e0e'
    assert (FC / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.33.1'
    manifest = json.loads((FC / 'lake-manifest.json').read_text())
    assert next(p['rev'] for p in manifest['packages'] if p['name'] == 'mathlib') == ML_SHA
    version = run(['lean', '--version'], 'lean_version.log')
    assert 'version 4.33.1,' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
    run(['lake', '--version'], 'lake_version.log')
    run(['lake', 'exe', 'cache', 'get'], 'cache.log')
    assert run(['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD'], 'mathlib_commit.log').strip() == ML_SHA
    run(['lake', 'build', 'FormalConjectures.OEIS.51903'], 'dependency_build.log')
    shutil.copy2(target, OUT / '51903.original.lean')
    shutil.copy2(FC / 'lake-manifest.json', OUT / 'lake-manifest.json')
    shutil.copy2(FC / 'lean-toolchain', OUT / 'lean-toolchain')
    source = ROOT / 'D14ShortWitness.lean'
    before = digest(source)
    shutil.copy2(source, FC / 'D14ShortWitness.lean')
    shutil.copy2(source, OUT / 'D14ShortWitness.lean')
    state['phase'] = 'STANDALONE_COMPILE'; save()
    text = run(['lake', 'env', 'lean', '-o', str(OUT / 'D14ShortWitness.olean'), 'D14ShortWitness.lean'], 'standalone.log', 300)
    ax = audit(text, ['D14.R5.short_answer', 'D14.R5.exists_odd_witness'])
    assert (OUT / 'D14ShortWitness.olean').stat().st_size > 0
    original = target.read_text()
    proof = source.read_text().split('theorem short_answer :', 1)[1].split('\ntheorem exists_odd_witness', 1)[0]
    proof = proof.split(':= by\n', 1)[1].rstrip()
    old = '@[category research open, AMS 11]\ntheorem conjecture3 :\n    answer(sorry) ↔ ∃ n : ℕ, Odd n ∧ 1 < a n ∧ 2 ^ n ≡ 2 ^ (a n) [MOD n] := by\n  sorry'
    new = '@[category research solved, AMS 11]\ntheorem conjecture3 :\n    answer(True) ↔ ∃ n : ℕ, Odd n ∧ 1 < a n ∧ 2 ^ n ≡ 2 ^ (a n) [MOD n] := by\n' + proof
    assert original.count(old) == 1
    patched = original.replace(old, new, 1)
    (OUT / '51903.patched.lean').write_text(patched)
    import difflib
    (OUT / 'conjecture3.patch').write_text(''.join(difflib.unified_diff(original.splitlines(True), patched.splitlines(True), fromfile='a/FormalConjectures/OEIS/51903.lean', tofile='b/FormalConjectures/OEIS/51903.lean')))
    audit_tail = '''\n#print axioms OeisA51903.conjecture3\ntheorem D14R12.upstream_exists :\n    ∃ n : ℕ, Odd n ∧ 1 < OeisA51903.a n ∧\n      2 ^ n ≡ 2 ^ (OeisA51903.a n) [MOD n] :=\n  OeisA51903.conjecture3.mp True.intro\n#print axioms D14R12.upstream_exists\n'''
    target.write_text(patched + audit_tail)
    shutil.copy2(target, OUT / '51903.audit.lean')
    state['phase'] = 'PATCHED_UPSTREAM_COMPILE'; save()
    text = run(['lake', 'env', 'lean', '-o', str(OUT / '51903.olean'), 'FormalConjectures/OEIS/51903.lean'], 'upstream.log', 300)
    ax.update(audit(text, ['OeisA51903.conjecture3', 'D14R12.upstream_exists']))
    assert (OUT / '51903.olean').stat().st_size > 0
    assert digest(source) == before == digest(OUT / 'D14ShortWitness.lean')
    assert target.read_text() == patched + audit_tail
    (OUT / 'axioms.json').write_text(json.dumps(ax, indent=2) + '\n')
    state.update(lean_kernel_checked=True, phase='PASS', source_sha256=before,
                 lean_version=version.strip(), upstream_commit=FC_SHA, mathlib_commit=ML_SHA,
                 finished_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()))
    save()
    (OUT / 'SHA256SUMS').write_text(''.join(f'{digest(p)}  {p.name}\n' for p in sorted(OUT.iterdir()) if p.is_file() and p.name != 'SHA256SUMS'))
    print('D14_REAL_KERNEL_AND_AXIOM_AUDIT_PASS', json.dumps(state), flush=True)
except Exception as exc:
    state['error'] = repr(exc)
    save()
    raise
