"""Complete011 declaration/header/dependency/source/document artifact audit."""
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
 'DkMath/NumberTheory/Legendre/ParitySafeCanonicalRootFiber.lean',
 'DkMath/NumberTheory/Legendre/ParitySafeCanonicalRootSieve.lean',
 'DkMath/NumberTheory/Legendre/ParitySafeCanonicalRootCharge.lean',
 'DkMathTest/NumberTheory/LegendreCanonicalRootCharge.lean',
 'DkMathTest/NumberTheory/LegendreCanonicalRootRegression.lean',
]
records=[]
for file in paths:
    namespace=''
    for line in (root/file).read_text().splitlines():
        if line.startswith('namespace '): namespace=line.split()[1]
        match=re.match(r'^(?:noncomputable )?(def|theorem|abbrev) (\w+)(?=\s*[:({])',line)
        if match: records.append(dict(name=namespace+'.'+match.group(2),kind=match.group(1),file=file))
manifest=base/'logs/declaration-coverage-011.json'
audit=root/'DkMathTest/NumberTheory/LegendreCanonicalRootAxiomAudit.lean'
if '--generate' in sys.argv:
    manifest.write_text(json.dumps(records,indent=2)+'\n')
    audit.write_text(header+'import DkMath.NumberTheory.Legendre\n'
      'import DkMathTest.NumberTheory.LegendreCanonicalRootRegression\n\n'
      '#print "file: DkMathTest.NumberTheory.LegendreCanonicalRootAxiomAudit"\n\n'+
      ''.join('#check '+r['name']+'\n#print axioms '+r['name']+'\n' for r in records))
    print(f'Generated {len(records)} complete declaration inspections.')
    raise SystemExit(0)
assert json.loads(manifest.read_text())==records
raw=(base/'logs/axiom-audit-011.txt').read_text()
axioms={m.group(1):set(a.strip() for a in m.group(2).split(',') if a.strip())
        for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]",raw)}
axioms.update({m.group(1):set() for m in re.finditer(r"'([^']+)' does not depend on any axioms",raw)})
expected={r['name'] for r in records}
assert len(expected)==len(records) and set(axioms)==expected,set(axioms)^expected
for name,trust in axioms.items(): assert trust<={'propext','Classical.choice','Quot.sound'},(name,trust)
prod=sum(r['file'].startswith('DkMath/') for r in records)
msg=f'PASS: {len(records)}/{len(records)} complete dependency sets; production {prod}, calibration/regression {len(records)-prod}.\nPASS: only propext, Classical.choice, Quot.sound; no sorryAx dependencies.\n'
(base/'logs/axiom-coverage-011.txt').write_text(msg);print(msg,end='')
files=[root/p for p in paths]+[root/'DkMath/NumberTheory/Legendre.lean',
    root/'DkMathTest/NumberTheory/LegendreCanonicalRootInventory.lean',audit]
scan=subprocess.run(['rg','-n',r'\b(sorry|sorryAx|admit|axiom|native_decide|unsafe)\b',*map(str,files)],capture_output=True,text=True)
assert scan.returncode==1,scan.stdout+scan.stderr
(base/'logs/forbidden-token-scan-011.txt').write_text('PASS: zero forbidden-token matches.\n'+'\n'.join(str(p.relative_to(root)) for p in files)+'\n')
for path in files:
    text=path.read_text(); assert text.startswith(header),path
    lines=text.splitlines();imports=[i for i,l in enumerate(lines) if l.startswith('import ')]
    assert imports[0]==6,path
    tail=[l for l in lines[imports[-1]+1:] if l.strip()]
    module=str(path.relative_to(root)).removesuffix('.lean').replace('/','.')
    assert tail[0]==f'#print "file: {module}"',(path,tail[0])
(base/'logs/header-style-011.txt').write_text(f'PASS: all {len(files)} written Lean headers and exact post-import module prints.\n')
print(f'PASS: {len(files)} written Lean files; uniform headers and zero forbidden tokens.')
tracked=subprocess.run(['git','diff','--check'],cwd=root,capture_output=True,text=True)
assert tracked.returncode==0,tracked.stdout+tracked.stderr
untracked=subprocess.run(['git','ls-files','--others','--exclude-standard'],cwd=root,capture_output=True,text=True,check=True).stdout.splitlines()
for p in untracked:
    check=subprocess.run(['git','diff','--no-index','--check','/dev/null',str(root/p)],capture_output=True,text=True)
    assert check.returncode in (0,1) and not check.stdout and not check.stderr,(p,check.stdout,check.stderr)
(base/'logs/diff-check-011.txt').write_text(f'PASS: tracked diff and {len(untracked)} new-file whitespace checks.\n')
print('PASS: tracked and new-file whitespace.')
rows=json.loads((base/'logs/root-diagnostics-011.json').read_text())
report=(base/'report-011.md').read_text();data=(root/paths[3]).read_text()
for row in rows:
    n,A,B,D=row['n'],row['A'],row['B2'],row['D'];c3,c5,c7=row['charges'];cumul=row['cumulative']
    assert row['charges']==list(row['actual'].values())
    assert D==B-A+1 and cumul==[c3,c3+c5,c3+c5+c7]
    assert row['cutoff']==next(p for p,c in zip([3,5,7],cumul) if c>=D)
    assert f'({n},{A},{B},{c3},{c5},{c7},{row["cutoff"]})' in data
    assert f'|{n}|{A}|{B}|{D}|{cumul[0]}|{cumul[1]}|{cumul[2]}|{row["cutoff"]}|' in report
assert len(re.findall(r'^## \d+\.',report,re.M))==10
assert report.rstrip().endswith('Outcome A — CANONICAL ROOT SIEVE BREAKS FIXED-BASIS BARRIER')
(base/'logs/artifact-check-011.txt').write_text('PASS: five diagnostics/Lean rows/report cutoffs match; all10 report questions answered.\n')
for name in ('source-inventory','findings','report','validation'):
    doc=base/f'{name}-011.md'
    for target in re.findall(r'\]\(([^)]+)\)',doc.read_text()):
        if not target.startswith(('http:','https:','#')): assert (doc.parent/target.split('#')[0]).exists(),(doc,target)
for target in re.findall(r'\]\(([^)]+)\)',(base/'README.md').read_text()):
    if not target.startswith(('http:','https:','#')): assert (base/target.split('#')[0]).exists(),target
print('PASS: finite data/report arithmetic and local documentation links.')
