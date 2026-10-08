"""Scoped FLT7 reconstruction source, declaration and build evidence audit."""
from pathlib import Path
import hashlib, json, re, subprocess

base = Path(__file__).resolve().parent.parent
root = base.parents[2]
production = [root / 'DkMath/FLT/Seven/PrimeTraceOneReconstructionFiniteChart.lean',
              root / 'DkMath/FLT/Seven/SevenRamifiedFusionDepthFourReconstructionAudit.lean']
calibration = root / 'DkMathTest/FLT/Seven/DepthFourReconstructionCalibration.lean'
audit = root / 'DkMathTest/FLT/Seven/DepthFourReconstructionAxiomAudit.lean'
facade = root / 'DkMath/FLT/Seven.lean'
files = production + [calibration, audit, facade]
for path in files:
    s = path.read_text()
    assert s.startswith('/-\nCopyright (c) 2026 D. and Wise Wolf.')
    imports = list(re.finditer(r'^import .+$', s, re.M))
    module = str(path.relative_to(root)).removesuffix('.lean').replace('/', '.')
    assert s[imports[-1].end():].startswith('\n\n#print "file: ' + module + '"')
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b', s)
    assert all(line.rstrip() == line for line in s.splitlines())
assert all('DkMath.NumberTheory.Legendre' not in p.read_text() for p in production)
assert all(not re.search(r'^structure ', p.read_text(), re.M) for p in production)
coverage = json.loads((base / 'logs/coverage-043.json').read_text())
qualified = []
for path in production:
    names = re.findall(r'^(?:def|theorem) ([A-Za-z0-9_.]+)', path.read_text(), re.M)
    prefix = 'DkMath.FLT.Seven.'
    if path.stem.startswith('SevenRamifiedFusion'):
        prefix += 'RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.'
    actual = [prefix + n for n in names]
    assert actual == coverage[path.stem]
    qualified += actual
assert len(qualified) == 11
assert re.findall(r'^#print axioms (\S+)', audit.read_text(), re.M) == qualified
log = (base / 'logs/axiom-audit-043.txt').read_text()
for q in qualified:
    match = re.search(re.escape("'" + q + "' depends on axioms: [") + r'([^]]*)]', log)
    assert match, q
    assert set(re.findall(r'[A-Za-z]+(?:\.[A-Za-z]+)?', match[1])) <= {
        'propext', 'Classical.choice', 'Quot.sound'}
assert 'sorryAx' not in log
names = re.findall(r'^theorem ([A-Za-z0-9_.]+)', calibration.read_text(), re.M)
assert names == coverage['calibration_declarations'] and len(names) == 9
assert 'import DkMath.FLT.Seven.SevenRamifiedFusionDepthFourReconstructionAudit' in facade.read_text()
source = json.loads((base / 'logs/source-audit-043.json').read_text())
assert len(source['source_audit']) == 23
for entry in source['source_audit']:
    p = root / entry['path']
    assert hashlib.sha256(p.read_bytes()).hexdigest() == entry['sha256']
assert source['facade_direct_imports'] == len(re.findall(r'^import ', facade.read_text(), re.M))
for label in ['focused', 'axiom-audit', 'facade', 'root']:
    d = json.loads((base / f'logs/performance-{label}-043.json').read_text())
    assert d['exit_code'] == 0
    assert d['LEAN_NUM_THREADS'] is None and not d['LEAN_NUM_THREADS_in_environment']
    assert 'Build completed successfully' in (base / f'logs/{label}-043.txt').read_text()
for label in ['focused', 'axiom-audit']:
    assert 'warning:' not in (base / f'logs/{label}-043.txt').read_text()
for path in list(base.glob('*043*.md')) + list((base / 'logs').glob('*043*')):
    assert path.read_text().isascii(), path
assert subprocess.run(['git', 'diff', '--check'], cwd=root).returncode == 0
print('PASS: 11 new public declarations; 9 kernel regressions; 5 Lean headers; '
      '23 existing source fingerprints; no parallel packet structures or Legendre imports; '
      '4 successful builds with LEAN_NUM_THREADS unset; standard axioms only; whitespace.')
