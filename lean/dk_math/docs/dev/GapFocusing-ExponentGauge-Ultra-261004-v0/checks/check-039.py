"""Reproduce the bounded source, axiom, diagnostic and build artifact audit."""
from pathlib import Path
import re,json,subprocess,hashlib
base=Path(__file__).resolve().parent.parent;root=base.parents[2]
files=[root/'DkMath/NumberTheory/Legendre/GnomonPooledThresholdAudit.lean',
 root/'DkMathTest/NumberTheory/GnomonPooledThresholdCalibration.lean',
 root/'DkMathTest/NumberTheory/GnomonPooledThresholdAxiomAudit.lean']
for f in files:
    s=f.read_text();assert s.startswith('/-'+chr(10)+'Copyright (c) 2026 D. and Wise Wolf.')
    module=str(f.relative_to(root)).removesuffix('.lean').replace('/','.')
    imports=list(re.finditer(r'^import .+$',s,re.M));assert imports
    assert s[imports[-1].end():].startswith(chr(10)*2+'#print "file: '+module+'"')
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b',s)
    assert not any(line.rstrip()!=line for line in s.splitlines())
coverage=json.loads((base/'logs/coverage-039.json').read_text())
actual=re.findall(r'^(?:noncomputable def|def|theorem) (\w+)',files[0].read_text(),re.M)
assert actual==coverage['production_declarations'] and len(actual)==6
log=(base/'logs/axiom-audit-039.txt').read_text()
for name in actual:
    match=re.search(re.escape("'DkMath.NumberTheory.Legendre."+name+"' depends on axioms: [")+r'([^]]*)]',log)
    assert match,name
    assert set(re.findall(r'[A-Za-z]+(?:\.[A-Za-z]+)?',match[1])) <= {'propext','Classical.choice','Quot.sound'}
assert 'sorryAx' not in log
for label in ['focused','facade','root','axiom-audit']:
    stats=json.loads((base/f'logs/performance-{label}-039.json').read_text())
    assert stats['exit_code']==0 and stats['LEAN_NUM_THREADS']==2
    assert 'Build completed successfully' in (base/f'logs/{label}-039.txt').read_text()
d=json.loads((base/'logs/diagnostics-039.json').read_text())
assert d['summary']['sample_count']==300
assert d['summary']['source_sha256']==hashlib.sha256((base/'logs/diagnostics-038.json').read_bytes()).hexdigest()
assert [r['n'] for r in d['rows']]==list(range(3,301))+[1031,5000]
assert d['summary']['first_sampled_threshold_failure']['n']==27
assert d['summary']['failing_sample_count']==1
for r in d['rows']:
    assert r['exact_total_product_inequality']
    assert r['threshold_principle_holds']==(r['first_threshold_failure'] is None)
for a in d['anchors']:
    assert int(a['total_left'])<=int(a['total_right'])
    if a['n']==27:
        assert a['failed_thresholds']==[8,9,10,11]
        assert a['first_threshold_failure']['left_above']=='4807'
        assert a['first_threshold_failure']['right_above']=='2491'
for f in list(base.glob('*039*.md'))+list((base/'logs').glob('*039*.json'))+list((base/'logs').glob('*039*.txt')):
    s=f.read_text();assert s.isascii(),f
assert subprocess.run(['git','diff','--check'],cwd=root).returncode==0
print('PASS: 6 production declarations; standard axioms only; 3 new Lean headers; source scan; 300 diagnostics; 4 two-thread builds; whitespace.')
