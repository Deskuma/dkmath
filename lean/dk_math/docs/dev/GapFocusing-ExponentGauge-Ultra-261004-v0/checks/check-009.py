"""Generate and verify complete009 declaration/dependency/header/source audits.

Run --generate before the Lean inspection; run without it after the final build.
"""
from pathlib import Path
import json
import re
import subprocess
import sys

base = Path(__file__).resolve().parent.parent
root = base.parents[2]
header = '''/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

'''
paths = [
    'DkMath/NumberTheory/Legendre/ParitySafeCRTSeat.lean',
    'DkMathTest/NumberTheory/LegendreAdaptiveCertificate.lean',
    'DkMathTest/NumberTheory/LegendreCRTSeat.lean',
    'DkMathTest/NumberTheory/LegendreAdaptiveClassificationData.lean',
    'DkMathTest/NumberTheory/LegendreAdaptiveClassification.lean',
]
records = []
for file in paths:
    namespace = ''
    for line in (root/file).read_text().splitlines():
        if line.startswith('namespace '):
            namespace = line.split()[1]
        # Require the declaration's binder/type delimiter; do not count prose in module comments.
        match = re.match(r'^(?:noncomputable )?(def|theorem) (\w+)(?=\s*[:({])', line)
        if match:
            records.append({'name': namespace+'.'+match.group(2), 'kind': match.group(1), 'file': file})
manifest = base/'logs/declaration-coverage-009.json'
audit_source = root/'DkMathTest/NumberTheory/LegendreAdaptiveCertificateAxiomAudit.lean'
if '--generate' in sys.argv:
    manifest.write_text(json.dumps(records, indent=2)+'\n')
    audit_source.write_text(header+'import DkMath.NumberTheory.Legendre\n'
                           'import DkMathTest.NumberTheory.LegendreAdaptiveClassification\n\n'
                           '#print "file: DkMathTest.NumberTheory.LegendreAdaptiveCertificateAxiomAudit"\n\n'+
                           ''.join('#check '+r['name']+'\n#print axioms '+r['name']+'\n' for r in records))
    print(f'Generated {len(records)} declaration inspections.')
    sys.exit(0)
assert json.loads(manifest.read_text()) == records
expected = {r['name'] for r in records}
assert len(expected) == len(records)
raw = (base/'logs/axiom-audit-009.txt').read_text()
axioms = {}
for match in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", raw):
    axioms[match.group(1)] = {a.strip() for a in match.group(2).split(',') if a.strip()}
for match in re.finditer(r"'([^']+)' does not depend on any axioms", raw):
    axioms[match.group(1)] = set()
assert set(axioms) == expected, set(axioms) ^ expected
for name, trust in axioms.items():
    assert trust <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, trust)
production = sum(r['file'].startswith('DkMath/') for r in records)
result = (f'PASS: {len(expected)}/{len(records)} complete dependency sets; '
          f'production {production}, regression/data {len(records)-production}.\n'
          'PASS: every set uses only propext, Classical.choice, Quot.sound.\n')
(base/'logs/axiom-coverage-009.txt').write_text(result)
print(result, end='')

files = [root/file for file in paths] + [root/'DkMath/NumberTheory/Legendre.lean',
        root/'DkMathTest/NumberTheory/LegendreAdaptiveCertificateInventory.lean', audit_source]
scan = subprocess.run(['rg', '-n', r'\b(sorry|sorryAx|admit|axiom|native_decide|unsafe)\b',
                       *map(str, files)], capture_output=True, text=True)
assert scan.returncode == 1, scan.stdout+scan.stderr
(base/'logs/forbidden-token-scan-009.txt').write_text(
    'PASS: zero forbidden-token matches.\n'+'\n'.join(str(p.relative_to(root)) for p in files)+'\n')
print('PASS: forbidden-token scan of complete changed production/new probes.')

for path in files:
    text = path.read_text()
    assert text.startswith(header), path
    lines = text.splitlines()
    import_lines = [i for i, line in enumerate(lines) if line.startswith('import ')]
    assert import_lines and import_lines[0] == 6, path
    tail = [line for line in lines[import_lines[-1]+1:] if line.strip()]
    module = str(path.relative_to(root)).removesuffix('.lean').replace('/', '.')
    assert tail[0] == f'#print "file: {module}"', (path, tail[0])
(base/'logs/header-style-009.txt').write_text(
    f'PASS: uniform copyright/import/file-print headers in {len(files)} changed/new Lean files.\n')
print(f'PASS: all{len(files)} Lean headers and exact module prints.')

tracked = subprocess.run(['git', 'diff', '--check'], cwd=root, capture_output=True, text=True)
assert tracked.returncode == 0, tracked.stdout+tracked.stderr
untracked = subprocess.run(['git', 'ls-files', '--others', '--exclude-standard'], cwd=root,
                           capture_output=True, text=True, check=True).stdout.splitlines()
for file in untracked:
    check = subprocess.run(['git', 'diff', '--no-index', '--check', '/dev/null', str(root/file)],
                           capture_output=True, text=True)
    assert check.returncode in (0, 1) and not check.stdout and not check.stderr, (
        file, check.stdout, check.stderr)
(base/'logs/diff-check-009.txt').write_text(
    f'PASS: git diff --check and {len(untracked)} new-file whitespace checks.\n')
print('PASS: tracked/new-file whitespace.')

documents = [base/f'{name}-009.md' for name in
             ('source-inventory', 'findings', 'report', 'validation')] + [base/'README.md']
for document in documents:
    for target in re.findall(r'\]\(([^)]+)\)', document.read_text()):
        if not target.startswith(('http:', 'https:', '#')):
            assert (document.parent/target.split('#')[0]).exists(), (document, target)
print('PASS: all checkpoint local links resolve.')
