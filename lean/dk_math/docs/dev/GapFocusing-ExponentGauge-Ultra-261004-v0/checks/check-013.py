"""Scoped declarations, trust, source/header, whitespace and artifact checks."""
from pathlib import Path
import json
import re
import subprocess
import sys

base = Path(__file__).resolve().parent.parent
root = base.parents[2]
prod = [
    'DkMath/NumberTheory/Legendre/Internal/RoughMomentCombinatorics.lean',
    'DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughMoments.lean',
    'DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughProductWaves.lean',
    'DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughFactorization.lean',
]
tests = ['DkMathTest/NumberTheory/LegendreSqrtRoughMoment' + x + '.lean'
         for x in ['Counts', 'Calibration', 'Regression']]
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
        match = re.match(r'^(?:noncomputable )?(def|theorem|abbrev) (\w+)(?=\s*[:({])', line)
        if match:
            records.append(dict(name=namespace + '.' + match[2], kind=match[1], file=path))
manifest = base / 'logs/declaration-coverage-013.json'
audit = root / 'DkMathTest/NumberTheory/LegendreSqrtRoughMomentAxiomAudit.lean'
if '--generate' in sys.argv:
    manifest.write_text(json.dumps(records, indent=2) + '\n')
    audit.write_text(header + '''import DkMath.NumberTheory.Legendre
import DkMathTest.NumberTheory.LegendreSqrtRoughMomentCalibration
import DkMathTest.NumberTheory.LegendreSqrtRoughMomentRegression

#print "file: DkMathTest.NumberTheory.LegendreSqrtRoughMomentAxiomAudit"

''' + ''.join('#check ' + r['name'] + '\n#print axioms ' + r['name'] + '\n' for r in records))
    print(f'Generated {len(records)} declaration audits; production {sum(r["file"] in prod for r in records)}.')
    sys.exit(0)
assert json.loads(manifest.read_text()) == records
if '--sources-only' not in sys.argv:
    raw = (base / 'logs/axiom-audit-013.txt').read_text()
    found = {m[1]: set(x.strip() for x in m[2].split(',') if x.strip())
             for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", raw)}
    found.update({m[1]: set() for m in re.finditer(r"'([^']+)' does not depend on any axioms", raw)})
    expected = {r['name'] for r in records}
    assert len(expected) == len(records) and set(found) == expected, set(found) ^ expected
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
discovery = json.loads((base / 'logs/discovery-013.json').read_text())
assert discovery['scan_upper'] == 3000 and discovery['scan_count'] == 430
assert discovery['scan_last'] == 2999 and discovery['first'] is None
assert all(t['I'] < t['R'] and t['U'] > 0 for t in discovery['scan'])
for t in discovery['calibration'] + discovery['scan']:
    assert t['R'] + t['M2'] == t['U'] + t['I'] + t['M3']
    assert t['moment_margin'] == t['U']
    assert t['classes'][0] == t['U']
    assert sum(t['classes']) == t['R']
    assert t['I'] == sum(k*c for k,c in enumerate(t['classes']))
assert [t['n'] for t in discovery['calibration']] == [211, 503, 1009, 1013, 1019]
for name in ['report-013.md', 'source-inventory-013.md', 'findings-013.md', 'validation-013.md']:
    source = (base / name).read_text()
    for target in re.findall(r'\]\(([^)]+)\)', source):
        if '://' not in target and not target.startswith('#'):
            assert (base / target.split('#')[0]).exists(), (name, target)
report = (base / 'report-013.md').read_text()
assert report.rstrip().endswith('Outcome A — ROUGH MOMENT BALANCE ADDS QUANTITATIVE LEVERAGE')
for t in discovery['calibration']:
    row = [t[k] for k in ['n', 'P', 'R', 'I', 'M2', 'M3', 'U', 'direct_margin', 'moment_margin']]
    assert '|' + '|'.join(map(str, row)) + '|' in report
print('PASS: bounded discovery rows, 5 calibration rows, report judgment and local links.')
