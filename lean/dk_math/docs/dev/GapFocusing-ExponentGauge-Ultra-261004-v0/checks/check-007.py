"""Check complete declaration coverage, dependency trust, source tokens and links.

Run from lean/dk_math after the recorded builds and Lean inspection commands.
"""
from pathlib import Path
import json
import re
import subprocess

base = Path(__file__).resolve().parent.parent
root = base.parents[2]
records = json.loads((base / 'logs/declaration-coverage-007.json').read_text())
expected = {r['name'] for r in records}
derived = {'DkMath.NumberTheory.Legendre.card_filter_odd_dvd_Ioc_eq_paritySafeDelta'}
for file, namespace in (
    ('DkMath/NumberTheory/Legendre/ParitySafeIncidenceUpper.lean',
     'DkMath.NumberTheory.Legendre.'),
    ('DkMathTest/NumberTheory/LegendreIncidenceUpper.lean',
     'DkMathTest.LegendreIncidenceUpper.'),
):
    derived.update(namespace + m.group(1) for m in re.finditer(
        r'^(?:noncomputable )?(?:def|theorem) (\w+)', (root / file).read_text(), re.M))
assert derived == expected, (derived ^ expected)
log = (base / 'logs/axiom-audit-007.txt').read_text()
audit = {}
for match in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log):
    audit[match.group(1)] = {s.strip() for s in match.group(2).split(',') if s.strip()}
for match in re.finditer(r"'([^']+)' does not depend on any axioms", log):
    audit[match.group(1)] = set()
assert set(audit) == expected, (set(audit) ^ expected)
for name, axioms in audit.items():
    assert axioms <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, axioms)
production = sum(r['name'].startswith('DkMath.NumberTheory.Legendre.') for r in records)
result = (f'PASS: source-derived declarations {len(derived)}/{len(expected)}; '
          f'production {production}, regression {len(expected)-production}.\n'
          'PASS: every dependency set uses only propext, Classical.choice, Quot.sound.\n')
(base / 'logs/axiom-coverage-007.txt').write_text(result)
print(result, end='')

files = [root / p for p in (
    'DkMath/NumberTheory/Legendre.lean',
    'DkMath/NumberTheory/Legendre/ParitySafeMobiusOddCorrection.lean',
    'DkMath/NumberTheory/Legendre/ParitySafeIncidenceUpper.lean',
)] + sorted((root / 'DkMathTest/NumberTheory').glob('LegendreIncidenceUpper*.lean'))
scan = subprocess.run(['rg', '-n', r'\b(sorry|sorryAx|admit|axiom|native_decide|unsafe)\b',
                       *map(str, files)], capture_output=True, text=True)
assert scan.returncode == 1, scan.stdout + scan.stderr
text = 'PASS: zero forbidden-token matches in complete changed production and new Lean probes.\n'
text += '\n'.join(str(p.relative_to(root)) for p in files) + '\n'
(base / 'logs/forbidden-token-scan-007.txt').write_text(text)
print(text.splitlines()[0])

tracked = subprocess.run(['git', 'diff', '--check'], cwd=root, capture_output=True, text=True)
assert tracked.returncode == 0, tracked.stdout + tracked.stderr
untracked = subprocess.run(['git', 'ls-files', '--others', '--exclude-standard'], cwd=root,
                           capture_output=True, text=True, check=True).stdout.splitlines()
for file in untracked:
    path = root / file
    check = subprocess.run(['git', 'diff', '--no-index', '--check', '/dev/null', str(path)],
                           capture_output=True, text=True)
    assert check.returncode in (0, 1) and not check.stdout and not check.stderr, (
        file, check.stdout, check.stderr)
(base / 'logs/diff-check-007.txt').write_text(
    f'PASS: git diff --check and {len(untracked)} new-file whitespace checks.\n')
print('PASS: tracked and new-file whitespace.')

documents = [base / f'{name}-007.md' for name in
             ('source-inventory', 'findings', 'report', 'validation')] + [base / 'README.md']
for document in documents:
    for target in re.findall(r'\]\(([^)]+)\)', document.read_text()):
        if not target.startswith(('http:', 'https:', '#')):
            assert (document.parent / target.split('#')[0]).exists(), (document, target)
print('PASS: all local links in checkpoint documents resolve.')
