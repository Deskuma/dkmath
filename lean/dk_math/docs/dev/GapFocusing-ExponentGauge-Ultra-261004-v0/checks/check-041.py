"""Scoped source, kernel regression, axiom, endpoint and build artifact checks."""
from pathlib import Path
import json,re,math,hashlib,subprocess
base=Path(__file__).resolve().parent.parent;root=base.parents[2]
files=[root/'DkMath/NumberTheory/Legendre/GnomonRepeatedBaseAggregate.lean',
 root/'DkMathTest/NumberTheory/GnomonRepeatedBaseAggregateCalibration.lean',
 root/'DkMathTest/NumberTheory/GnomonRepeatedBaseAggregateAxiomAudit.lean',
 root/'DkMath/NumberTheory/Legendre.lean']
for f in files:
    s=f.read_text();assert s.startswith('/-'+chr(10)+'Copyright (c) 2026 D. and Wise Wolf.')
    module=str(f.relative_to(root)).removesuffix('.lean').replace('/','.')
    imports=list(re.finditer(r'^import .+$',s,re.M));assert imports
    assert s[imports[-1].end():].startswith(chr(10)*2+'#print "file: '+module+'"')
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b',s)
    assert not any(line.rstrip()!=line for line in s.splitlines())
c=json.loads((base/'logs/coverage-041.json').read_text())
actual=re.findall(r'^(?:noncomputable def|def|theorem) (\w+)',files[0].read_text(),re.M)
assert actual==c['production_declarations'] and len(actual)==28
helpers=re.findall(r'^private theorem (\w+)',files[0].read_text(),re.M)
assert helpers==c['private_proof_helpers'] and len(helpers)==2
assert re.findall(r'^theorem (\w+)',files[1].read_text(),re.M)==c['calibration_declarations']
assert len(c['calibration_declarations'])==10
log=(base/'logs/axiom-audit-041.txt').read_text()
for name in actual:
    prefix="'DkMath.NumberTheory.Legendre."+name+"'"
    match=re.search(re.escape(prefix+' depends on axioms: [')+r'([^]]*)]',log)
    if not match:
        assert prefix+' does not depend on any axioms' in log,name
        continue
    assert set(re.findall(r'[A-Za-z]+(?:\.[A-Za-z]+)?',match[1])) <= {'propext','Classical.choice','Quot.sound'}
assert 'sorryAx' not in log
for label in ['focused','axiom-audit','facade','root']:
    d=json.loads((base/f'logs/performance-{label}-041.json').read_text())
    assert d['LEAN_NUM_THREADS']==4 and d['exit_code']==0
    assert 'Build completed successfully' in (base/f'logs/{label}-041.txt').read_text()
d=json.loads((base/'logs/diagnostics-041.json').read_text())
assert d['summary']['sample_count']==301
assert d['summary']['source_sha256']==hashlib.sha256((base/'logs/diagnostics-040.json').read_bytes()).hexdigest()
assert [r['n'] for r in d['rows']]==list(range(3,301))+[1031,2896,5000]
assert d['summary']['aggregate_above_band_anchors']==[15,22,26,29,31]
assert d['summary']['nonpositive_aggregate_margin_anchors']==[]
for r in d['rows']:
    assert r['repeated_phase040_approx']<=r['aggregate_repeated_approx']+1e-7
    assert r['budget040_approx']<=r['budget041_approx']+1e-7
    assert r['margin041_approx']>0
for a in d['anchors']:
    n=a['n'];N=n*n;top=N+2*n;seen=set()
    for w in a['square_windows']:
        p=w['base'];k=w['k'];assert 2<=k<=n-1
        L=max(math.isqrt(N//k),math.isqrt(2*n))+1
        U=min(n,math.isqrt(top//k));assert L==U==p==w['L']==w['U']
        assert p not in seen;seen.add(p)
        assert N<k*p*p<=top and p*p>2*n and k==N//(p*p)+1
    for p in a['small_base_blocks']:
        assert p['prime'] and p['base']**2<=2*n
    for p in a['small_base_blocks']+a['square_windows']:
        base_p=p['base'];e=2;power=base_p**e
        while power<=2*n:e+=1;power*=base_p
        length=0
        while power<=N:length+=1;power*=base_p
        assert p['first_exponent']==e and p['interval_length']==length
        assert abs(p['weight_approx']-length*math.log(base_p))<1e-7
    assert abs(math.fsum(p['weight_approx'] for p in a['small_base_blocks'])-a['small_base_mass_approx'])<1e-7
    assert abs(math.fsum(p['weight_approx'] for p in a['square_windows'])-a['large_endpoint_mass_approx'])<1e-7
    if n==69:
        assert [(w['k'],w['U']) for w in a['square_windows']]==[(2,49),(3,40),(5,31),(10,22),(11,21),(12,20),(15,18),(19,16),(34,12)]
        assert a['composite_square_window_count']==8
    if n==2896:
        p=next(p for p in a['small_base_blocks'] if p['base']==2)
        assert p['first_exponent']==13 and p['upper_exponent']==22 and p['interval_length']==10
for f in list(base.glob('*041*.md'))+list((base/'logs').glob('*041*.json'))+list((base/'logs').glob('*041*.txt')):
    assert f.read_text().isascii(),f
assert subprocess.run(['git','diff','--check'],cwd=root).returncode==0
print('PASS: 28 public declarations; 2 private proof helpers audited transitively; 10 kernel regressions; 4 Lean headers/source scans; 301 endpoint diagnostics; 4 four-thread builds; whitespace.')
