"""Complete public declaration, category, trust, source, diagnostic and report audit."""
from pathlib import Path
from collections import Counter
from math import isqrt
import json
import re
import subprocess
import sys

base = Path(__file__).resolve().parent.parent
root = base.parents[2]
prod = ['DkMath/CosmicFormula/QuadraticCenteredBridge.lean'] + [
    'DkMath/NumberTheory/Legendre/' + name + '.lean' for name in
    ['QuadraticGnomonFold', 'CenteredOwnerFold', 'CenteredFoldSupportNorm']]
tests = ['DkMathTest/NumberTheory/LegendreCenteredFoldRegression.lean']
audit = root / 'DkMathTest/NumberTheory/LegendreCenteredFoldAxiomAudit.lean'
header = '''/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

'''
# Categories apply to every theorem and, for coverage completeness, definitions too.
reasons = {
    'A': 'Thin algebraic adapter or consequence of existing support/parity/owner APIs; no provider.',
    'B': 'Exact finite geometry or definition of a finite carrier; no arithmetic restriction.',
    'C': 'New fold-facing arithmetic/counting bridge; no uniform full-cover obstruction.',
}
owner_c = {'centeredOwnerGapCapacityIndices_card'}
owner_b = {'centeredSameOwnerIndices', 'centeredDifferentOwnerIndices',
           'squareOffsetFold_successor_noncommuting'}
geometry_a = {'centered_offset_difference', 'centered_gap_eq_GTail'}
norm_b = {'centeredFoldNorm', 'centeredFoldNorm_odd', 'centeredFoldNorm_eq_point_sum',
          'centeredFoldNorm_eq_twice_left_add_gap', 'centeredCommonSupportIndices'}
norm_a = {'prime_dvd_centeredFoldNorm_ne_two'}
records = []
for path in prod + tests:
    namespace = ''
    for number, line in enumerate((root / path).read_text().splitlines(), 1):
        if line.startswith('namespace '):
            namespace = line.split()[1]
        match = re.match(r'^(?:noncomputable )?(def|theorem|abbrev) (\w+)(?=\s*[:({])', line)
        if match:
            name = match[2]
            if path in tests or 'QuadraticCenteredBridge' in path:
                category = 'A'
            elif 'QuadraticGnomonFold' in path:
                category = 'A' if name in geometry_a else 'B'
            elif 'CenteredOwnerFold' in path:
                category = 'C' if name in owner_c else 'B' if name in owner_b else 'A'
            else:
                category = 'B' if name in norm_b else 'A' if name in norm_a else 'C'
            reason = reasons[category]
            if path in tests:
                reason = 'Kernel calibration or explicit counterexample; applies proved APIs/numeral arithmetic.'
            records.append(dict(name=namespace + '.' + name, kind=match[1], file=path,
                                line=number, category=category, reason=reason))
manifest = base / 'logs/declaration-coverage-017.json'
classification = base / 'declaration-classification-017.md'
if '--generate' in sys.argv:
    manifest.write_text(json.dumps(records, indent=2) + '\n')
    audit.write_text(header + '''import DkMath.NumberTheory.Legendre
import DkMath.CosmicFormula.QuadraticCenteredBridge
import DkMathTest.NumberTheory.LegendreCenteredFoldRegression

#print "file: DkMathTest.NumberTheory.LegendreCenteredFoldAxiomAudit"

''' + ''.join('#check ' + r['name'] + '\n#print axioms ' + r['name'] + '\n' for r in records))
    classification.write_text('# Declaration classification 017\n\n'
        'A: duplicate/thin adapter. B: geometry/carrier. C: arithmetic bridge. D: capacity obstruction.\n'
        'No declaration is classified D. A closed calibration is labeled A; its exact scope is given by the statement.\n'
        'C claims a new application interface, not a newly discovered general number-theory fact.\n\n'
        + '\n'.join('## ' + path + '\n\n' + '\n'.join(
            '- `' + r['name'] + '` (' + r['kind'] + ', line ' + str(r['line']) + '): '
            + r['category'] + '. ' + r['reason'] for r in records if r['file'] == path)
            + '\n' for path in prod + tests))
    pc = Counter(r['category'] for r in records if r['file'] in prod)
    print(f'Generated {len(records)} audits, {sum(r["file"] in prod for r in records)} production declarations; categories {dict(pc)}.')
    sys.exit(0)
assert json.loads(manifest.read_text()) == records
expected = {r['name'] for r in records}
assert len(expected) == len(records)
if '--sources-only' not in sys.argv:
    raw = (base / 'logs/axiom-audit-017.txt').read_text()
    found = {m[1]: set(x.strip() for x in m[2].split(',') if x.strip())
             for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", raw)}
    found.update({m[1]: set() for m in re.finditer(r"'([^']+)' does not depend on any axioms", raw)})
    assert expected <= set(found), expected - set(found)
    for name in expected:
        assert found[name] <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, found[name])
    print(f'PASS: all {len(records)} public declaration axiom sets; no sorryAx or additional axioms.')
written = prod + tests + [str(audit.relative_to(root)), 'DkMath/NumberTheory/Legendre.lean', 'DkMath/CosmicFormula.lean']
for path in written:
    source = (root / path).read_text()
    assert source.startswith(header), path
    module = path[:-5].replace('/', '.')
    assert re.search(r'import [^\n]+\n\n#print "file: ' + re.escape(module) + r'"', source), path
    if path in prod + tests:
        assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b', source), path
    assert all(line == line.rstrip() for line in source.splitlines()), path
subprocess.run(['git', 'diff', '--check'], cwd=root, check=True)
for path in prod + tests + [str(audit.relative_to(root))]:
    result = subprocess.run(['git', 'diff', '--no-index', '--check', '/dev/null', str(root / path)], capture_output=True, text=True)
    assert not result.stdout and not result.stderr, (path, result.stdout, result.stderr)
print(f'PASS: {len(written)} uniform headers/markers, whitespace and scoped forbidden-token scans.')
# Generic half-step module must not become a Legendre import.
for path in prod[1:] + ['DkMath/NumberTheory/Legendre.lean']:
    assert 'import DkMath.CosmicFormula.QuadraticCenteredBridge' not in (root/path).read_text()
d = json.loads((base / 'logs/discovery-017.json').read_text())
assert d['range'] == [1, 300] and d['anchor_count'] == 300 and d['extra_anchors'] == [1031]
assert [r['n'] for r in d['rows']] == list(range(1,301)) + [1031]
for r in d['rows']:
    n = r['n']
    assert r['pair_count'] == r['different_owner_all'] == n
    assert r['same_owner_all'] == r['same_owner_covered'] == 0
    assert r['same_owner_by_prime'] == {} and r['same_owner_gaps'] == []
    assert len(r['coloring']) == n and all(a != b for j,a,b,c in r['coloring'])
    assert r['different_owner_covered'] + r['one_covered'] + r['neither_covered'] == n
    assert sum(r['capacities'].values()) == r['capacity_sum']
    assert sum(r['common_support_by_prime'].values()) == r['common_support_incidence']
    assert r['norm'] == n*n+(n+1)**2
    for p, c in r['capacities'].items():
        p = int(p)
        assert c == (0 if p == 2 else (n+(p-1)//2)//p)
        assert r['common_support_by_prime'].get(str(p),0) == (c if r['norm'] % p == 0 else 0)
    # Independently check completeness of the prime-gap list, including gaps above 1500 at 1031.
    gaps = [2*j+1 for j in range(n) if 2*j+1 > n and all((2*j+1)%q for q in range(2, isqrt(2*j+1)+1))]
    assert [event['gap'] for event in r['forced_prime_gap_pairs']] == gaps
assert [r['n'] for r in d['near_misses']] == [5,8,11,19,29,297,1031]
assert d['smallest_shared_support']['n'] == 6 and d['smallest_shared_support']['j'] == 2
assert d['smallest_false_gap_owner_rule']['n'] == 8 and d['smallest_false_gap_owner_rule']['j'] == 7
assert d['smallest_false_translation_rule'] == dict(n=3,m=7,p=2,translated=10)
print('PASS: all natural anchors 1..300 plus 1031; exact coloring, capacities, actual common support and complete prime-gap lists.')
for r in records:
    assert '`' + r['name'] + '`' in classification.read_text(),r['name']
artifacts = ['findings-017.md','source-inventory-017.md','declaration-classification-017.md']
if '--sources-only' not in sys.argv:
    artifacts += ['report-017.md', 'validation-017.md']
for name in artifacts:
    source = (base/name).read_text()
    source.encode('ascii')
    for target in re.findall(r'\]\(([^)]+)\)',source):
        if '://' not in target and not target.startswith('#'):
            assert (base/target.split('#')[0]).exists(), (name,target)
if '--sources-only' not in sys.argv:
    report=(base/'report-017.md').read_text()
    assert all(f'## {i}.' in report for i in range(1,14))
    assert report.rstrip().endswith('Outcome B - CENTERED FOLD PRODUCES A NEW EXACT ARITHMETIC BRIDGE')
    assert 'centeredPair_gcd_eq_norm_gap' in report and 'Constant curvature alone is not a Legendre provider.' in report
    print('PASS: all theorem categories, ASCII documents, links, thirteen report answers, single next contract and final Outcome B.')
