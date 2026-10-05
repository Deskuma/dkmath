"""Scoped declarations, trust, source/header, whitespace and artifact checks."""
from pathlib import Path
import json
import re
import subprocess
import sys

base = Path(__file__).resolve().parent.parent
root = base.parents[2]
prod = [
    'DkMath/NumberTheory/Legendre/ParitySafeSqrtCrossQuotient.lean',
    'DkMath/NumberTheory/Legendre/ParitySafeSqrtCompositeRouting.lean',
    'DkMath/NumberTheory/Legendre/ParitySafeSqrtQuotientConservation.lean',
]
tests = ['DkMathTest/NumberTheory/LegendreSqrtQuotient' + x + '.lean'
         for x in ['Calibration', 'Regression']]
header = '''/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

'''
records = []
for path in prod + tests:
    namespace = ''
    for line in (root / path).read_text().splitlines():
        if line.startswith('namespace '):
            namespace = line.split()[1]
        match = re.match(r'^(?:@\[[^\]]+\] )?(?:noncomputable )?(def|theorem|abbrev|instance) (\w+)(?=\s*[:({])', line)
        if match:
            records.append(dict(name=namespace + '.' + match[2], kind=match[1], file=path))
manifest = base / 'logs/declaration-coverage-015.json'
audit = root / 'DkMathTest/NumberTheory/LegendreSqrtQuotientAxiomAudit.lean'
if '--generate' in sys.argv:
    manifest.write_text(json.dumps(records, indent=2) + '\n')
    audit.write_text(header + '''import DkMath.NumberTheory.Legendre
import DkMathTest.NumberTheory.LegendreSqrtQuotientCalibration
import DkMathTest.NumberTheory.LegendreSqrtQuotientRegression

#print "file: DkMathTest.NumberTheory.LegendreSqrtQuotientAxiomAudit"

''' + ''.join('#check ' + r['name'] + '\n#print axioms ' + r['name'] + '\n' for r in records))
    print(f'Generated {len(records)} declaration audits; production {sum(r["file"] in prod for r in records)}.')
    sys.exit(0)
assert json.loads(manifest.read_text()) == records
if '--sources-only' not in sys.argv:
    raw = (base / 'logs/axiom-audit-015.txt').read_text()
    found = {m[1]: set(x.strip() for x in m[2].split(',') if x.strip())
             for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", raw)}
    found.update({m[1]: set() for m in re.finditer(r"'([^']+)' does not depend on any axioms", raw)})
    expected = {r['name'] for r in records}
    # Replayed facade imports also print five older declarations. Audit the complete manifest scope.
    assert len(expected) == len(records) and expected <= set(found), expected - set(found)
    found = {name: found[name] for name in expected}
    for name, deps in found.items():
        assert deps <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, deps)
    print(f'PASS: {len(records)}/{len(records)} complete axiom sets; only the three standard logical axioms.')
written = prod + tests + [str(audit.relative_to(root)), 'DkMath/NumberTheory/Legendre.lean']
for path in written:
    source = (root / path).read_text()
    assert source.startswith(header), path
    module = path[:-5].replace('/', '.')
    assert re.search(r'import [^\n]+\n\n#print "file: ' + re.escape(module) + r'"', source), path
    if path in prod + tests:
        assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b', source), path
    assert all(line == line.rstrip() for line in source.splitlines()), path
print(f'PASS: {len(written)} uniform headers/markers; scoped forbidden token and whitespace scans.')
subprocess.run(['git', 'diff', '--check'], cwd=root, check=True)
for path in prod + tests + [str(audit.relative_to(root))]:
    check = subprocess.run(['git', 'diff', '--no-index', '--check', '/dev/null', str(root / path)], capture_output=True, text=True)
    assert not check.stdout and not check.stderr, (path, check.stdout, check.stderr)
print('PASS: tracked and newly written Lean whitespace checks.')
discovery = json.loads((base / 'logs/discovery-015.json').read_text())
assert discovery['range'] == [3,3000] and discovery['anchor_count'] == 429
rows = discovery['rows']
assert len(rows) == 429 and rows[-1]['n'] == 2999
assert discovery['smallest_rejected'] == dict(n=11,p=5,q=27,small_prime=3)
assert discovery['smallest_multiowner'] == dict(n=8,point=75,owners=[dict(p=3,q=25),dict(p=5,q=15)])
assert discovery['smallest_prime_multiowner'] == dict(n=13,point=175,owners=[dict(p=5,q=35),dict(p=7,q=25)])
for r in rows:
    assert r['total'] == r['cross']+r['cube_mass']+r['repeat_mass']+r['triple_mass']+r['rejected']
    assert r['cube_mass']==r['cube'] and r['repeat_mass']==2*r['repeated'] and r['triple_mass']==3*r['triple']
    assert r['residual']==r['cross'] and r['rough_incidence']==r['total']-r['rejected']
    assert r['three_prime_lower']<=r['rejected']
    assert r['three_prime_cross_bound']==r['total']-r['cube_mass']-r['repeat_mass']-r['triple_mass']-r['three_prime_lower']
    assert r['cross']<=r['three_prime_cross_bound']<=r['cross_bound_without_rejection']<=r['total']
    assert r['near_total']+r['far_total']==r['total']
    for k in ['total','cross','cube_mass','repeat_mass','triple_mass','rejected']:
        assert sum(o[k] for o in r['owners'])==r[k]
    assert r['largest_owner_residual']==max((o['cross'] for o in r['owners']),default=0)
calibrations = [r for r in rows if r['n'] in [211,503,1009,1013,1019,1021]]
assert len(calibrations)==6
assert len(discovery['finite_three_prime_successes'])==410
next_basis=json.loads((base/'logs/next-basis-015.json').read_text())
assert next_basis['basis']==[3,5,7,11]
assert len(next_basis['rows'])==19 and all(r['passes'] and r['J4']>=r['required'] for r in next_basis['rows'])
assert {r['n'] for r in next_basis['rows']}=={r['n'] for r in rows if not r['three_prime_budget_holds']}
for name in ['report-015.md','source-inventory-015.md','findings-015.md','validation-015.md']:
    source=(base/name).read_text()
    for target in re.findall(r'\]\(([^)]+)\)',source):
        if '://' not in target and not target.startswith('#'):
            assert (base/target.split('#')[0]).exists(), (name,target)
report=(base/'report-015.md').read_text()
assert report.rstrip().endswith('Outcome C — COMPOSITE ROUTING REQUIRES A CORRECTED DECOMPOSITION')
for r in calibrations:
    expected='| ' + ' | '.join(str(r[k]) for k in ['n','cross','total','cube_mass','repeat_mass','triple_mass','rejected','residual']) + ' |'
    assert expected in report, expected
assert 'quotient1031_structural_endpoint' in report and 'quotient1031_uncovered_lower' in report
print('PASS: 429 complete diagnostics, six exact calibration rows, corrected conservation, counterexamples, and report scope.')
