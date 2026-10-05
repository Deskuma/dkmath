"""Scoped declarations, trust, source/header, whitespace and artifact checks."""
from pathlib import Path
import json
import re
import subprocess
import sys

base = Path(__file__).resolve().parent.parent
root = base.parents[2]
prod = [
    'DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughFactorization.lean',
    'DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughStrata.lean',
    'DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughSingleton.lean',
    'DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughCensus.lean',
]
tests = ['DkMathTest/NumberTheory/LegendreSqrtRoughCensus' + x + '.lean'
         for x in ['Counts', 'Calibration', 'Regression']]
new_factorization = {'sqrt_rough_square_quotient_one_or_prime', 'sqrt_singleton_point_cube_or_cross'}
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
        if match and (not path.endswith('ParitySafeSqrtRoughFactorization.lean') or match[2] in new_factorization):
            records.append(dict(name=namespace + '.' + match[2], kind=match[1], file=path))
# Also audit the new calibration structure, constructor, and all data projections.
for suffix in ['', '.mk', '.n', '.R', '.U', '.N1', '.N2', '.N3', '.cube', '.cross', '.repeated', '.triple']:
    records.append(dict(name='DkMathTest.LegendreSqrtRoughCensus.CensusRow' + suffix, kind='structure-api', file=tests[0]))
manifest = base / 'logs/declaration-coverage-014.json'
audit = root / 'DkMathTest/NumberTheory/LegendreSqrtRoughCensusAxiomAudit.lean'
if '--generate' in sys.argv:
    manifest.write_text(json.dumps(records, indent=2) + '\n')
    audit.write_text(header + '''import DkMath.NumberTheory.Legendre
import DkMathTest.NumberTheory.LegendreSqrtRoughCensusCalibration
import DkMathTest.NumberTheory.LegendreSqrtRoughCensusRegression

#print "file: DkMathTest.NumberTheory.LegendreSqrtRoughCensusAxiomAudit"

''' + ''.join('#check ' + r['name'] + '\n#print axioms ' + r['name'] + '\n' for r in records))
    print(f'Generated {len(records)} declaration audits; production {sum(r["file"] in prod for r in records)}.')
    sys.exit(0)
assert json.loads(manifest.read_text()) == records
if '--sources-only' not in sys.argv:
    raw = (base / 'logs/axiom-audit-014.txt').read_text()
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
discovery = json.loads((base / 'logs/discovery-014.json').read_text())
assert discovery['range'] == [3,3000] and discovery['anchor_count'] == 429
assert discovery['classification_counterexamples'] == []
rows = discovery['rows']
assert len(rows) == 429 and rows[-1]['n'] == 2999
for r in rows:
    assert r['R'] == r['N0']+r['cube']+r['cross']+r['repeat']+r['triple']
    assert r['N1'] == r['cube']+r['cross'] and r['N2'] == r['repeat'] and r['N3'] == r['triple']
    assert r['cube'] <= 1 and r['N0'] > 0
    assert r['cross'] <= r['odd_active_wave_capacity_sum'] <= r['geometric_capacity_sum']
    assert sum(f['count'] for f in r['fibers']) == r['cross']
    assert r['max_cross_fiber'] == max((f['count'] for f in r['fibers']), default=0)
calibrations = [r for r in rows if r['n'] in [211,503,1009,1013,1019,1021]]
assert len(calibrations) == 6
for name in ['report-014.md', 'source-inventory-014.md', 'findings-014.md', 'validation-014.md']:
    source = (base / name).read_text()
    for target in re.findall(r'\]\(([^)]+)\)', source):
        if '://' not in target and not target.startswith('#'):
            assert (base / target.split('#')[0]).exists(), (name,target)
report = (base / 'report-014.md').read_text()
assert report.rstrip().endswith('Outcome A — COMPLETE SQRT-ROUGH FACTORIZATION CENSUS')
for r in calibrations:
    row = [r[k] for k in ['n','R','N0','N1','N2','N3','cube','cross','repeat','triple']]
    assert '|'+'|'.join(map(str,row))+'|' in report
print('PASS: 429 bounded diagnostics, 6 census calibration rows, report judgment and links.')
