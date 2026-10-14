"""Scoped floor-pulse, capacity-obstruction and unset-thread build evidence audit."""
from pathlib import Path
import json,re,math,hashlib,subprocess
base=Path(__file__).resolve().parent.parent;root=base.parents[2]
files=[root/'DkMath/NumberTheory/Legendre/GnomonQFloorPulse.lean',
 root/'DkMathTest/NumberTheory/GnomonQFloorPulseCalibration.lean',
 root/'DkMathTest/NumberTheory/GnomonQFloorPulseAxiomAudit.lean',
 root/'DkMath/NumberTheory/Legendre.lean']
for f in files:
    s=f.read_text();assert s.startswith('/-'+chr(10)+'Copyright (c) 2026 D. and Wise Wolf.')
    module=str(f.relative_to(root)).removesuffix('.lean').replace('/','.')
    imports=list(re.finditer(r'^import .+$',s,re.M));assert imports
    assert s[imports[-1].end():].startswith(chr(10)*2+'#print "file: '+module+'"')
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b',s)
    assert not any(line.rstrip()!=line for line in s.splitlines())
assert 'DkMath.RH.' not in files[0].read_text()
c=json.loads((base/'logs/coverage-042.json').read_text())
actual=re.findall(r'^(?:noncomputable def|def|theorem) (\w+)',files[0].read_text(),re.M)
assert actual==c['production_declarations'] and len(actual)==16
assert re.findall(r'^private theorem (\w+)',files[0].read_text(),re.M)==c['private_proof_helpers']==['correction_nonneg']
assert re.findall(r'^theorem (\w+)',files[1].read_text(),re.M)==c['calibration_declarations']
assert len(c['calibration_declarations'])==9
log=(base/'logs/axiom-audit-042.txt').read_text()
for name in actual:
    prefix="'DkMath.NumberTheory.Legendre."+name+"'"
    match=re.search(re.escape(prefix+' depends on axioms: [')+r'([^]]*)]',log)
    if not match:
        assert prefix+' does not depend on any axioms' in log,name
        continue
    assert set(re.findall(r'[A-Za-z]+(?:\.[A-Za-z]+)?',match[1])) <= {'propext','Classical.choice','Quot.sound'}
assert 'sorryAx' not in log
for label in ['focused','axiom-audit','facade','root']:
    d=json.loads((base/f'logs/performance-{label}-042.json').read_text())
    assert d['LEAN_NUM_THREADS'] is None and not d['LEAN_NUM_THREADS_in_environment']
    assert d['exit_code']==0
    assert 'Build completed successfully' in (base/f'logs/{label}-042.txt').read_text()
d=json.loads((base/'logs/diagnostics-042.json').read_text())
assert d['summary']['sample_count']==301
assert d['summary']['source040_sha256']==hashlib.sha256((base/'logs/diagnostics-040.json').read_bytes()).hexdigest()
assert d['summary']['source031_sha256']==hashlib.sha256((base/'logs/diagnostics-031.json').read_bytes()).hexdigest()
assert [r['n'] for r in d['rows']]==list(range(3,301))+[1031,2896,5000]
assert d['summary']['passing_target_capacity_count']==0
assert d['summary']['first_capacity_failure']['n']==3
assert d['summary']['worst_available_ratio']['n']==38
assert [a['n'] for a in d['anchors']]==[32,69,210,297,1031,2896,5000]
old={r['n']:r for r in json.loads((base/'logs/diagnostics-040.json').read_text())['rows']}
for r in d['rows']:
    n=r['n'];w=2*n;N=n*n;U=math.fsum(math.log(y)-math.log(2) for y in range(N+1,N+w+1))
    assert abs(U-r['proposed_U_Q_approx'])<1e-7
    assert abs(r['exact_Q_approx']-old[n]['singleton_approx'])<1e-6
    assert abs(r['B040_approx']-old[n]['budget040_approx'])<1e-7
    assert r['exact_Q_approx']<=U+1e-7 and U>=r['log_cell_approx']-1e-7
    assert abs(r['normalization_penalty_approx']-(math.lgamma(w+1)-w*math.log(2)))<1e-7
    assert abs(U-r['log_cell_approx']-r['normalization_penalty_approx'])<1e-5
    assert r['target_capacity_margin_approx']<=0 and r['exact_Q_margin_approx']>0
    assert 0<=r['Q_label_count']<=w
for a in d['anchors']:
    n=a['n'];assert a['target_cofactor_product_checked'] and a['quotient_window_inventory_checked']
    assert len(a['incidence_sha256'])==64
    for p,k,y in a['first_incidence_triples']+a['last_incidence_triples']:
        assert all(p%d for d in range(2,math.isqrt(p)+1))
        assert 2*n<p<=n*n and 2<=k<n and k==n*n//p+1 and y==k*p
        assert n*n<y<=n*n+2*n and (n*n+2*n)//p-n*n//p==1
for f in list(base.glob('*042*.md'))+list((base/'logs').glob('*042*.json'))+list((base/'logs').glob('*042*.txt')):
    assert f.read_text().isascii(),f
assert subprocess.run(['git','diff','--check'],cwd=root).returncode==0
print('PASS: 16 public declarations; 1 private helper audited transitively; 9 kernel regressions; 4 Lean headers/source scans; 301 diagnostics including 7 required anchors; 4 builds with LEAN_NUM_THREADS unset; whitespace.')
