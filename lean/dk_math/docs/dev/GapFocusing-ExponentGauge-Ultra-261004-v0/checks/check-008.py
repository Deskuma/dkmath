"""Generate/check the complete008 declaration audit and document/source checks.

Run with --generate before Lean audit; run without it after all recorded builds.
The fixed baseline makes new-declaration classification independent of later commits.
"""
from pathlib import Path
import json
import re
import subprocess
import sys

base = Path(__file__).resolve().parent.parent
root = base.parents[2]
sources = [
    ('DkMath/NumberTheory/Legendre/ParitySafeIncidenceUpper.lean', 'DkMath.NumberTheory.Legendre.'),
    ('DkMath/NumberTheory/Legendre/ParitySafeExcessCertificate.lean', 'DkMath.NumberTheory.Legendre.'),
    ('DkMathTest/NumberTheory/LegendreHybridProvider.lean', 'DkMathTest.LegendreHybridProvider.'),
    ('DkMathTest/NumberTheory/LegendreHybridClassificationData.lean', 'DkMathTest.LegendreHybridClassification.'),
    ('DkMathTest/NumberTheory/LegendreHybridClassification.lean', 'DkMathTest.LegendreHybridClassification.'),
]
pattern = r'^(?:noncomputable )?(def|theorem) (\w+)'
records = []
for file, namespace in sources:
    old = subprocess.run(['git', 'show', 'a8d0be1e6:lean/dk_math/'+file], cwd=root,
                         capture_output=True, text=True)
    previous = {m.group(2) for m in re.finditer(pattern, old.stdout, re.M)}
    for m in re.finditer(pattern, (root/file).read_text(), re.M):
        prefix = 'DkMath.NumberTheory.' if m.group(2) == 'card_le_sub_two_exclusions' else namespace
        records.append({'name': prefix+m.group(2), 'kind': m.group(1), 'file': file,
                        'new': m.group(2) not in previous})
manifest = base/'logs/declaration-coverage-008.json'
audit_source = root/'DkMathTest/NumberTheory/LegendreHybridProviderAxiomAudit.lean'
if '--generate' in sys.argv:
    manifest.write_text(json.dumps(records, indent=2)+'\n')
    audit_source.write_text('import DkMath.NumberTheory.Legendre\n'
                           'import DkMathTest.NumberTheory.LegendreHybridClassification\n\n'+
                           ''.join('#check '+r['name']+'\n#print axioms '+r['name']+'\n' for r in records))
    print(f'Generated audit for {len(records)} declarations.')
    sys.exit(0)
assert json.loads(manifest.read_text()) == records
expected = {r['name'] for r in records}
assert len(expected) == len(records)
log = (base/'logs/axiom-audit-008.txt').read_text()
audit = {}
for match in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log):
    audit[match.group(1)] = {s.strip() for s in match.group(2).split(',') if s.strip()}
for match in re.finditer(r"'([^']+)' does not depend on any axioms", log):
    audit[match.group(1)] = set()
assert set(audit) == expected, (set(audit) ^ expected)
for name, axioms in audit.items():
    assert axioms <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, axioms)
production = [r for r in records if r['file'].startswith('DkMath/')]
new_production = sum(r['new'] for r in production)
result = (f'PASS: source-derived dependency coverage {len(audit)}/{len(expected)}.\n'
          f'Production {len(production)} including all{new_production} new; '
          f'regression {len(records)-len(production)}.\n'
          'PASS: only propext, Classical.choice, Quot.sound in every dependency set.\n')
(base/'logs/axiom-coverage-008.txt').write_text(result)
print(result, end='')

files = [root/p for p in (
    'DkMath/NumberTheory/Legendre.lean',
    'DkMath/NumberTheory/Legendre/ParitySafeIncidenceUpper.lean',
    'DkMath/NumberTheory/Legendre/ParitySafeExcessCertificate.lean',
)] + [root/file for file, _ in sources if file.startswith('DkMathTest/')]
files += [root/'DkMathTest/NumberTheory/LegendreHybridProviderInventory.lean', audit_source]
scan = subprocess.run(['rg', '-n', r'\b(sorry|sorryAx|admit|axiom|native_decide|unsafe)\b',
                       *map(str, files)], capture_output=True, text=True)
assert scan.returncode == 1, scan.stdout+scan.stderr
text = 'PASS: zero forbidden-token matches in the complete changed production and008 probes.\n'
text += '\n'.join(str(p.relative_to(root)) for p in files)+'\n'
(base/'logs/forbidden-token-scan-008.txt').write_text(text)
print(text.splitlines()[0])

tracked = subprocess.run(['git', 'diff', '--check'], cwd=root, capture_output=True, text=True)
assert tracked.returncode == 0, tracked.stdout+tracked.stderr
untracked = subprocess.run(['git', 'ls-files', '--others', '--exclude-standard'], cwd=root,
                           capture_output=True, text=True, check=True).stdout.splitlines()
for file in untracked:
    check = subprocess.run(['git', 'diff', '--no-index', '--check', '/dev/null', str(root/file)],
                           capture_output=True, text=True)
    assert check.returncode in (0, 1) and not check.stdout and not check.stderr, (
        file, check.stdout, check.stderr)
(base/'logs/diff-check-008.txt').write_text(
    f'PASS: git diff --check and {len(untracked)} new-file whitespace checks.\n')
print('PASS: tracked/new-file whitespace.')

documents = [base/f'{name}-008.md' for name in
             ('source-inventory', 'findings', 'report', 'validation')] + [base/'README.md']
for document in documents:
    for target in re.findall(r'\]\(([^)]+)\)', document.read_text()):
        if not target.startswith(('http:', 'https:', '#')):
            assert (document.parent/target.split('#')[0]).exists(), (document, target)
print('PASS: local document links resolve.')
