"""Reproduce the bounded source, axiom, diagnostic and build artifact audit."""
from pathlib import Path
import re,json,subprocess,hashlib
base=Path(__file__).resolve().parent.parent;root=base.parents[2]
files=[root/'DkMath/NumberTheory/Legendre/GnomonNonSingletonCorrection.lean',
 root/'DkMathTest/NumberTheory/GnomonNonSingletonCorrectionCalibration.lean',
 root/'DkMathTest/NumberTheory/GnomonNonSingletonCorrectionAxiomAudit.lean']
for f in files:
    s=f.read_text();assert s.startswith('/-'+chr(10)+'Copyright (c) 2026 D. and Wise Wolf.')
    module=str(f.relative_to(root)).removesuffix('.lean').replace('/','.')
    imports=list(re.finditer(r'^import .+$',s,re.M));assert imports
    assert s[imports[-1].end():].startswith(chr(10)*2+'#print "file: '+module+'"')
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b',s)
    assert not any(line.rstrip()!=line for line in s.splitlines())
coverage=json.loads((base/'logs/coverage-036.json').read_text())
actual=re.findall(r'^(?:noncomputable def|theorem) (\w+)',files[0].read_text(),re.M)
assert actual==coverage['production_declarations'] and len(actual)==8
log=(base/'logs/axiom-audit-036.txt').read_text()
for name in actual:
    match=re.search(re.escape("'DkMath.NumberTheory.Legendre."+name+"' depends on axioms: [")+r'([^]]*)]',log)
    assert match,name
    assert set(re.findall(r'[A-Za-z]+(?:\.[A-Za-z]+)?',match[1])) <= {'propext','Classical.choice','Quot.sound'}
assert 'sorryAx' not in log
for label in ['focused','facade','root','axiom-audit']:
    stats=json.loads((base/f'logs/performance-{label}-036.json').read_text())
    assert stats['exit_code']==0 and stats['LEAN_NUM_THREADS']==2
    assert 'Build completed successfully' in (base/f'logs/{label}-036.txt').read_text()
d=json.loads((base/'logs/diagnostics-036.json').read_text())
assert d['summary']['sample_count']==300
assert d['summary']['source_sha256']==hashlib.sha256((base/'logs/diagnostics-031.json').read_bytes()).hexdigest()
assert [r['n'] for r in d['rows']]==list(range(3,301))+[1031,5000]
for r in d['rows']:
    assert r['correction_approx']<=r['budget_approx']+1e-7
    assert r['budget_approx']<=r['explicit_scale_approx']+1e-7
    assert abs(r['old_margin_approx']-r['reduced_margin_approx']-r['slack_approx'])<1e-6
for f in list(base.glob('*036*.md'))+list((base/'logs').glob('*036*.json'))+list((base/'logs').glob('*036*.txt')):
    s=f.read_text();assert s.isascii(),f
assert subprocess.run(['git','diff','--check'],cwd=root).returncode==0
print('PASS: 8 production declarations; standard axioms only; 3 new Lean headers; source scan; 300 diagnostics; 4 two-thread builds; whitespace.')
