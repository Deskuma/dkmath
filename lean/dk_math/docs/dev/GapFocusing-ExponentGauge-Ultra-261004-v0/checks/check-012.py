"""Complete012 declaration/header/dependency/source/document artifact audit."""
from pathlib import Path
import json
import re
import subprocess
import sys

base=Path(__file__).resolve().parent.parent
root=base.parents[2]
header='''/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

'''
paths=[
 'DkMath/NumberTheory/Legendre/ParitySafeCanonicalRootTail.lean',
 'DkMath/NumberTheory/Legendre/ParitySafeCanonicalRootEleven.lean',
 'DkMath/NumberTheory/Legendre/ParitySafeCanonicalRoughCount.lean',
 'DkMath/NumberTheory/Legendre/ParitySafePrimeAnchorCap.lean',
 'DkMathTest/NumberTheory/LegendreCanonicalTailCalibration.lean',
 'DkMathTest/NumberTheory/LegendreCanonicalTailDiagnostics.lean',
 'DkMathTest/NumberTheory/LegendreCanonicalTailDiagnosticCounts.lean',
 'DkMathTest/NumberTheory/LegendreCanonicalTailRegression.lean',
 'DkMathTest/NumberTheory/LegendreCanonicalPrimeCapCalibration.lean',
]
records=[]
for file in paths:
    namespace=''
    for line in (root/file).read_text().splitlines():
        if line.startswith('namespace '): namespace=line.split()[1]
        match=re.match(r'^(?:noncomputable )?(def|theorem|abbrev) (\w+)(?=\s*[:({])',line)
        if match: records.append(dict(name=namespace+'.'+match.group(2),kind=match.group(1),file=file))
manifest=base/'logs/declaration-coverage-012.json'
audit=root/'DkMathTest/NumberTheory/LegendreCanonicalTailAxiomAudit.lean'
if '--generate' in sys.argv:
    manifest.write_text(json.dumps(records,indent=2)+'\n')
    audit.write_text(header+'import DkMath.NumberTheory.Legendre\n'
      'import DkMathTest.NumberTheory.LegendreCanonicalTailRegression\n'
      'import DkMathTest.NumberTheory.LegendreCanonicalTailDiagnostics\n'
      'import DkMathTest.NumberTheory.LegendreCanonicalPrimeCapCalibration\n\n'
      '#print "file: DkMathTest.NumberTheory.LegendreCanonicalTailAxiomAudit"\n\n'+
      ''.join('#check '+r['name']+'\n#print axioms '+r['name']+'\n' for r in records))
    print(f'Generated {len(records)} complete declaration inspections.')
    raise SystemExit(0)
assert json.loads(manifest.read_text())==records
if '--sources-only' not in sys.argv:
    raw=(base/'logs/axiom-audit-012.txt').read_text()
    axioms={m.group(1):set(a.strip() for a in m.group(2).split(',') if a.strip())
            for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]",raw)}
    axioms.update({m.group(1):set() for m in re.finditer(r"'([^']+)' does not depend on any axioms",raw)})
    expected={r['name'] for r in records}
    assert len(expected)==len(records) and set(axioms)==expected,set(axioms)^expected
    for name,trust in axioms.items(): assert trust<={'propext','Classical.choice','Quot.sound'},(name,trust)
    prod=sum(r['file'].startswith('DkMath/') for r in records)
    msg=f'PASS: {len(records)}/{len(records)} complete dependency sets; production {prod}, calibration/regression {len(records)-prod}.\nPASS: only propext, Classical.choice, Quot.sound; no sorryAx dependencies.\n'
    (base/'logs/axiom-coverage-012.txt').write_text(msg);print(msg,end='')
files=[root/p for p in paths]+[root/'DkMath/NumberTheory/Legendre.lean',
    root/'DkMathTest/NumberTheory/LegendreCanonicalTailInventory.lean',audit]
scan=subprocess.run(['rg','-n',r'\b(sorry|sorryAx|admit|axiom|native_decide|unsafe)\b',*map(str,files)],capture_output=True,text=True)
assert scan.returncode==1,scan.stdout+scan.stderr
(base/'logs/forbidden-token-scan-012.txt').write_text('PASS: zero forbidden-token matches.\n'+'\n'.join(str(p.relative_to(root)) for p in files)+'\n')
for path in files:
    text=path.read_text(); assert text.startswith(header),path
    lines=text.splitlines();imports=[i for i,l in enumerate(lines) if l.startswith('import ')]
    assert imports[0]==6,path
    tail=[l for l in lines[imports[-1]+1:] if l.strip()]
    module=str(path.relative_to(root)).removesuffix('.lean').replace('/','.')
    assert tail[0]==f'#print "file: {module}"',(path,tail[0])
(base/'logs/header-style-012.txt').write_text(f'PASS: all {len(files)} written Lean headers and exact post-import module prints.\n')
print(f'PASS: {len(files)} written Lean files; uniform headers and zero forbidden tokens.')
tracked=subprocess.run(['git','diff','--check'],cwd=root,capture_output=True,text=True)
assert tracked.returncode==0,tracked.stdout+tracked.stderr
untracked=subprocess.run(['git','ls-files','--others','--exclude-standard'],cwd=root,capture_output=True,text=True,check=True).stdout.splitlines()
for p in untracked:
    check=subprocess.run(['git','diff','--no-index','--check','/dev/null',str(root/p)],capture_output=True,text=True)
    assert check.returncode in (0,1) and not check.stdout and not check.stderr,(p,check.stdout,check.stderr)
(base/'logs/diff-check-012.txt').write_text(f'PASS: tracked diff and {len(untracked)} new-file whitespace checks.\n')
print('PASS: tracked and new-file whitespace.')
rows=json.loads((base/'logs/root-tail-diagnostics-012.json').read_text())
report=(base/'report-012.md').read_text()
cal=(root/paths[4]).read_text();diag=(root/paths[5]).read_text()+(root/paths[6]).read_text()
for row in rows:
    n,A,B,D=row['n'],row['A'],row['B2'],row['D'];charges=row['charges'];cumul=row['cumulative']
    assert D==B-A+1 and cumul==[sum(charges[:k]) for k in range(1,5)]
    assert row['cutoff']==next(p for p,c in zip([3,5,7,11],cumul) if c>=D)
    assert f'({n},{A},{B},{",".join(map(str,charges))})' in cal
    assert '|'+ '|'.join(map(str,[n,A,B,D,*cumul,row['cutoff']]))+'|' in report
    assert f'({n},{row["E_diagnostic"]})' in diag
    assert f'({n},{row["union11"]},{row["credit11"]})' in cal
    assert row['charges'][3]==row['union11']+row['credit11']
    assert row['cutoff']**2<=n and row['cutoff']<=n
    for d in row['diagnostics']:
        P,H,T,R=d['P'],d['head'],d['tail'],d['rough_seats']
        assert H+T==row['E_diagnostic'] and d['remaining']==B-H
        assert d['demand_remaining']==max(D-H,0)
        assert B==A-d['uncovered_rough']+row['E_diagnostic']
        assert d['remaining']+R==A+d['rough_incidence']
        assert d['tail_multiplicity_bound']==R*(d['K']-1)
        assert 1<=d['L'] and d['L']**d['K']<=n*n+2*n<d['L']**(d['K']+1)
        assert f'({n},{P},{H},{T},{R})' in diag
    d=row['diagnostics'][3]
    assert d['rough_incidence']<d['rough_seats']
    assert f'({n},{d["rough_seats"]},{d["rough_incidence"]})' in cal
    assert f'({n},{d["rough_incidence"]-d["tail"]})' in diag
assert len(re.findall(r'^## \d+\.',report,re.M))==10
assert report.rstrip().endswith('Outcome A — HEAD/TAIL CANCELLATION GAINS NEW LEVERAGE')
(base/'logs/artifact-check-012.txt').write_text('PASS: seven structural rows and28 diagnostic rows/Lean/report cutoffs match; all10 report questions answered.\n')
for name in ('source-inventory','findings','report','validation'):
    doc=base/f'{name}-012.md'
    for target in re.findall(r'\]\(([^)]+)\)',doc.read_text()):
        if not target.startswith(('http:','https:','#')): assert (doc.parent/target.split('#')[0]).exists(),(doc,target)
for target in re.findall(r'\]\(([^)]+)\)',(base/'README.md').read_text()):
    if not target.startswith(('http:','https:','#')): assert (base/target.split('#')[0]).exists(),target
print('PASS: seven structural and28 diagnostic rows/report arithmetic and local documentation links.')
