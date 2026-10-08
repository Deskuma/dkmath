"""Scoped allocation residue sieve and build evidence audit."""
from pathlib import Path
import hashlib, json, re, subprocess

base = Path(__file__).resolve().parent.parent
root = base.parents[2]
production = [root / 'DkMath/FLT/Seven/SevenRamifiedFusionSixthPowerAllocationSieve.lean']
calibration = root / 'DkMathTest/FLT/Seven/SixthPowerAllocationSieveCalibration.lean'
audit = root / 'DkMathTest/FLT/Seven/SixthPowerAllocationSieveAxiomAudit.lean'
facade = root / 'DkMath/FLT/Seven.lean'
for path in production + [calibration, audit, facade]:
    s = path.read_text()
    assert s.startswith('/-\nCopyright (c) 2026 D. and Wise Wolf.')
    imports = list(re.finditer(r'^import .+$', s, re.M))
    module = str(path.relative_to(root)).removesuffix('.lean').replace('/', '.')
    assert s[imports[-1].end():].startswith('\n\n#print "file: ' + module + '"')
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b', s)
    assert all(line.rstrip() == line for line in s.splitlines())
assert all('DkMath.NumberTheory.Legendre' not in p.read_text() for p in production)
assert all(not re.search(r'^structure ', p.read_text(), re.M) for p in production)
coverage = json.loads((base / 'logs/coverage-048.json').read_text())
qualified = []
for path in production:
    stack, names = [], []
    for line in path.read_text().splitlines():
        m = re.match(r'^namespace (\S+)', line)
        if m:
            stack.append(m.group(1))
            continue
        if re.match(r'^end(?:\s|$)', line):
            stack.pop()
            continue
        m = re.match(r'^(?:def|theorem) ([A-Za-z0-9_.]+)', line)
        if m:
            names.append('.'.join(stack + [m.group(1)]))
    assert names == coverage[path.stem]
    qualified += names
assert len(qualified) == 14
assert re.findall(r'^#print axioms (\S+)', audit.read_text(), re.M) == qualified
log = (base / 'logs/axiom-audit-048.txt').read_text()
for q in qualified:
    match = re.search(re.escape("'" + q + "' depends on axioms: [") + r'([^]]*)]', log)
    if not match:
        assert "'" + q + "' does not depend on any axioms" in log, q
        continue
    assert set(re.findall(r'[A-Za-z]+(?:\.[A-Za-z]+)?', match[1])) <= {
        'propext', 'Classical.choice', 'Quot.sound'}
assert 'sorryAx' not in log
names = re.findall(r'^theorem ([A-Za-z0-9_.]+)', calibration.read_text(), re.M)
assert names == coverage['calibration_declarations'] and len(names) == 16
assert 'import DkMath.FLT.Seven.SevenRamifiedFusionSixthPowerAllocationSieve' in facade.read_text()
source = json.loads((base / 'logs/source-audit-048.json').read_text())
assert len(source['source_audit']) == 19
for entry in source['source_audit']:
    path = root / entry['path']
    assert hashlib.sha256(path.read_bytes()).hexdigest() == entry['sha256']
    assert entry['unchanged_from_HEAD']
    assert path.read_bytes() == subprocess.check_output(['git', 'show', 'HEAD:lean/dk_math/' + entry['path']], cwd=root)
assert source['new_public_declarations'] == 14
assert source['calibration_declarations'] == 16
assert len(source['mathlib_audit_sources']) == 4
for m in source['mathlib_audit_sources']:
    assert hashlib.sha256((root / m['path']).read_bytes()).hexdigest() == m['sha256']
assert source['facade_direct_imports'] == len(re.findall(r'^import ', facade.read_text(), re.M))
for label in ['focused', 'axiom-audit', 'facade', 'root']:
    d = json.loads((base / f'logs/performance-{label}-048.json').read_text())
    assert d['exit_code'] == 0
    assert d['LEAN_NUM_THREADS'] is None and not d['LEAN_NUM_THREADS_in_environment']
    assert 'Build completed successfully' in (base / f'logs/{label}-048.txt').read_text()
for label in ['focused', 'axiom-audit']:
    assert 'warning:' not in (base / f'logs/{label}-048.txt').read_text()
for path in [base / 'report-048.md'] + list((base / 'logs').glob('*048*')):
    assert path.read_text().isascii(), path
assert subprocess.run(['git', 'diff', '--check'], cwd=root).returncode == 0
print('PASS: all 14 new production declarations audited; 16 new kernel regressions; 4 Lean headers; '
      '19 unchanged repository source fingerprints and 4 audited Mathlib sources; no new packet structures or Legendre imports; '
      '4 successful builds with LEAN_NUM_THREADS unset; standard axioms only; whitespace.')
