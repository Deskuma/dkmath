"""Reproduce the bounded source, axiom, diagnostic and build artifact audit."""
from pathlib import Path
import re,json,subprocess,hashlib
base=Path(__file__).resolve().parent.parent;root=base.parents[2]
files=[root/'DkMath/NumberTheory/Legendre/GnomonCofactorAdaptiveRoughness.lean',
 root/'DkMathTest/NumberTheory/GnomonCofactorAdaptiveRoughnessCalibration.lean',
 root/'DkMathTest/NumberTheory/GnomonCofactorAdaptiveRoughnessAxiomAudit.lean']
for f in files:
    s=f.read_text();assert s.startswith('/-'+chr(10)+'Copyright (c) 2026 D. and Wise Wolf.')
    module=str(f.relative_to(root)).removesuffix('.lean').replace('/','.')
    imports=list(re.finditer(r'^import .+$',s,re.M));assert imports
    assert s[imports[-1].end():].startswith(chr(10)*2+'#print "file: '+module+'"')
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b',s)
    assert not any(line.rstrip()!=line for line in s.splitlines())
coverage=json.loads((base/'logs/coverage-035.json').read_text())
actual=re.findall(r'^(?:def|theorem) (\w+)',files[0].read_text(),re.M)
assert actual==coverage['production_declarations'] and len(actual)==11
log=(base/'logs/axiom-audit-035.txt').read_text()
for name in actual:
    match=re.search(re.escape("'DkMath.NumberTheory.Legendre."+name+"' depends on axioms: [")+r'([^]]*)]',log)
    assert match,name
    assert set(re.findall(r'[A-Za-z]+(?:\.[A-Za-z]+)?',match[1])) <= {'propext','Classical.choice','Quot.sound'}
assert 'sorryAx' not in log
for label in ['focused','facade','root','axiom-audit']:
    stats=json.loads((base/f'logs/performance-{label}-035.json').read_text())
    assert stats['exit_code']==0 and stats['LEAN_NUM_THREADS']==2
    assert 'Build completed successfully' in (base/f'logs/{label}-035.txt').read_text()
d=json.loads((base/'logs/diagnostics-035.json').read_text())
assert d['summary']['sample_count']==300
assert d['summary']['source_sha256']==hashlib.sha256((base/'logs/diagnostics-034.json').read_bytes()).hexdigest()
assert [r['n'] for r in d['rows']]==list(range(3,301))+[1031,5000]
for r in d['rows']:
    assert r['composite_count']==r['semiprime_count']+r['triple_count']
    assert abs(r['remaining_error_approx'])<1e-7
for f in list(base.glob('*035*.md'))+list((base/'logs').glob('*035*.json'))+list((base/'logs').glob('*035*.txt')):
    s=f.read_text();assert s.isascii(),f
assert subprocess.run(['git','diff','--check'],cwd=root).returncode==0
print('PASS: 11 production declarations; standard axioms only; 3 new Lean headers; source scan; 300 diagnostics; 4 two-thread builds; whitespace.')
