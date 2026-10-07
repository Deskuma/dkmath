"""Reproduce the bounded source, axiom, diagnostic and build artifact audit."""
from pathlib import Path
import re,json,subprocess,hashlib
base=Path(__file__).resolve().parent.parent;root=base.parents[2]
files=[root/'DkMath/NumberTheory/Legendre/GnomonSmallCarryPhase.lean',
 root/'DkMathTest/NumberTheory/GnomonSmallCarryPhaseCalibration.lean',
 root/'DkMathTest/NumberTheory/GnomonSmallCarryPhaseAxiomAudit.lean']
for f in files:
    s=f.read_text();assert s.startswith('/-'+chr(10)+'Copyright (c) 2026 D. and Wise Wolf.')
    module=str(f.relative_to(root)).removesuffix('.lean').replace('/','.')
    imports=list(re.finditer(r'^import .+$',s,re.M));assert imports
    assert s[imports[-1].end():].startswith(chr(10)*2+'#print "file: '+module+'"')
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b',s)
    assert not any(line.rstrip()!=line for line in s.splitlines())
coverage=json.loads((base/'logs/coverage-037.json').read_text())
actual=re.findall(r'^(?:noncomputable def|def|theorem) (\w+)',files[0].read_text(),re.M)
assert actual==coverage['production_declarations'] and len(actual)==10
log=(base/'logs/axiom-audit-037.txt').read_text()
for name in actual:
    match=re.search(re.escape("'DkMath.NumberTheory.Legendre."+name+"' depends on axioms: [")+r'([^]]*)]',log)
    assert match,name
    assert set(re.findall(r'[A-Za-z]+(?:\.[A-Za-z]+)?',match[1])) <= {'propext','Classical.choice','Quot.sound'}
assert 'sorryAx' not in log
for label in ['focused','facade','root','axiom-audit']:
    stats=json.loads((base/f'logs/performance-{label}-037.json').read_text())
    assert stats['exit_code']==0 and stats['LEAN_NUM_THREADS']==2
    assert 'Build completed successfully' in (base/f'logs/{label}-037.txt').read_text()
d=json.loads((base/'logs/diagnostics-037.json').read_text())
assert d['summary']['sample_count']==300
assert d['summary']['source_sha256']==hashlib.sha256((base/'logs/diagnostics-036.json').read_bytes()).hexdigest()
assert [r['n'] for r in d['rows']]==list(range(3,301))+[1031,5000]
assert d['summary']['central_conjecture_range']==[3,10000]
assert d['summary']['sampled_central_counterexamples']==[]
for r in d['rows']:
    assert r['correction_approx']<=r['phase_budget_approx']+1e-7
    assert r['phase_budget_approx']<=r['previous_budget_approx']+1e-7
    assert abs(r['phase_margin_approx']-r['previous_margin_approx']-r['excluded_mass_approx'])<1e-6
for f in list(base.glob('*037*.md'))+list((base/'logs').glob('*037*.json'))+list((base/'logs').glob('*037*.txt')):
    s=f.read_text();assert s.isascii(),f
assert subprocess.run(['git','diff','--check'],cwd=root).returncode==0
print('PASS: 10 production declarations; standard axioms only; 3 new Lean headers; source scan; 300 diagnostics; 4 two-thread builds; whitespace.')
