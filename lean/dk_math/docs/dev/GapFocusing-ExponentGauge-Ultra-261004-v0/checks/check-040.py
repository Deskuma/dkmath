"""Check scoped source, regressions, standard axioms, diagnostics and build evidence."""
from pathlib import Path
import re,json,subprocess,hashlib,math
base=Path(__file__).resolve().parent.parent;root=base.parents[2]
files=[root/'DkMath/NumberTheory/Legendre/GnomonRepeatedCarryPhase.lean',
 root/'DkMathTest/NumberTheory/GnomonRepeatedCarryPhaseCalibration.lean',
 root/'DkMathTest/NumberTheory/GnomonRepeatedCarryPhaseAxiomAudit.lean']
for f in files+[root/'DkMath/NumberTheory/Legendre/GnomonSmallCarryPhase.lean',root/'DkMath/NumberTheory/Legendre.lean']:
    s=f.read_text();assert s.startswith('/-'+chr(10)+'Copyright (c) 2026 D. and Wise Wolf.')
    module=str(f.relative_to(root)).removesuffix('.lean').replace('/','.')
    imports=list(re.finditer(r'^import .+$',s,re.M));assert imports
    assert s[imports[-1].end():].startswith(chr(10)*2+'#print "file: '+module+'"')
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b',s)
    assert not any(line.rstrip()!=line for line in s.splitlines())
coverage=json.loads((base/'logs/coverage-040.json').read_text())
actual=re.findall(r'^(?:noncomputable def|def|theorem) (\w+)',files[0].read_text(),re.M)
assert actual==coverage['production_declarations'] and len(actual)==15
assert len(re.findall(r'^instance ',files[0].read_text(),re.M))==coverage['anonymous_instances']==1
log=(base/'logs/axiom-audit-040.txt').read_text()
for name in actual+coverage['newly_exposed_previous_declarations']:
    match=re.search(re.escape("'DkMath.NumberTheory.Legendre."+name+"' depends on axioms: [")+r'([^]]*)]',log)
    if not match:
        assert "'DkMath.NumberTheory.Legendre."+name+"' does not depend on any axioms" in log,name
        continue
    assert set(re.findall(r'[A-Za-z]+(?:\.[A-Za-z]+)?',match[1])) <= {'propext','Classical.choice','Quot.sound'}
assert 'sorryAx' not in log
for label in ['focused','facade','root','axiom-audit']:
    stats=json.loads((base/f'logs/performance-{label}-040.json').read_text())
    assert stats['exit_code']==0 and stats['LEAN_NUM_THREADS']==2
    assert 'Build completed successfully' in (base/f'logs/{label}-040.txt').read_text()
d=json.loads((base/'logs/diagnostics-040.json').read_text())
assert d['summary']['sample_count']==301
assert d['summary']['source_sha256']==hashlib.sha256((base/'logs/diagnostics-036.json').read_bytes()).hexdigest()
assert [r['n'] for r in d['rows']]==list(range(3,301))+[1031,2896,5000]
assert d['summary']['remaining_sample_failures']==[]
for r in d['rows']:
    assert r['repeated_exact_approx']<=r['repeated_phase_approx']+1e-7
    assert r['repeated_phase_approx']<=r['repeated_band_approx']+1e-7
    assert r['correction_exact_approx']<=r['budget040_approx']+1e-7
    assert r['budget040_approx']<=r['budget037_approx']+1e-7
for anchor in d['anchors']:
    n=anchor['n'];weights=[];exact=[];band=[]
    for b in anchor['base_blocks']:
        p=b['base'];first=p**b['first_exponent']
        assert first==b['first_power'] and first>2*n
        assert b['first_exponent']>=2
        assert b['first_exponent']==2 or p**(b['first_exponent']-1)<=2*n
        assert b['first_gap']==first-n*n%first
        assert b['base_active']==(b['first_gap']<=2*n)
        assert b['exponent_count']==len(b['labels'])
        for z in b['labels']:
            a=z['exponent'];label=p**a
            assert label==z['label'] and 2*n<label<=n*n
            assert z['actual_carry']==(label-n*n%label<=2*n)
            band.append(math.log(p))
            if b['base_active']:weights.append(math.log(p))
            if z['actual_carry']:
                assert b['base_active'];exact.append(math.log(p))
    assert abs(math.fsum(weights)-anchor['repeated_phase_approx'])<1e-7
    assert abs(math.fsum(exact)-anchor['repeated_exact_approx'])<1e-7
    assert abs(math.fsum(band)-anchor['repeated_band_approx'])<1e-7
    if n in [69,297]:assert anchor['margin037_approx']<0<anchor['margin040_approx']
    if n==69:
        assert anchor['excluded_prime_power_count']==17
        assert any(z['label']==512 and not z['actual_carry'] for b in anchor['base_blocks'] if b['base_active'] for z in b['labels'])
    if n==2896:
        b=next(b for b in anchor['base_blocks'] if b['base']==2)
        assert b['base_active'] and b['exponent_count']==10
        assert [z['exponent'] for z in b['labels']]==list(range(13,23))
        assert all(z['actual_carry'] for z in b['labels'])
for f in list(base.glob('*040*.md'))+list((base/'logs').glob('*040*.json'))+list((base/'logs').glob('*040*.txt')):
    assert f.read_text().isascii(),f
assert subprocess.run(['git','diff','--check'],cwd=root).returncode==0
print('PASS: 15 named production declarations and 1 exposed identity; 1 decidability instance checked through envelope dependency; 5 Lean headers; source scan; 301 diagnostics; 4 two-thread builds; whitespace.')
