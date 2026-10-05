"""Complete declaration manifest, kernel trust, headers and bounded-search evidence."""
from pathlib import Path
import json
import re
import subprocess
import sys

base = Path(__file__).resolve().parent.parent
root = base.parents[2]
prod = ['DkMath/NumberTheory/Legendre/' + name + '.lean' for name in
        ['GnomonResidueCover','SquareShellWheelPeriod','SquareAnchorCounterexamplePacket','GnomonPrimorialTransition']]
tests = ['DkMathTest/NumberTheory/LegendreResidueCover' + name + '.lean' for name in ['Regression','Calibration']]
header = '''/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

'''
records = []
for path in prod + tests:
    namespace = ''
    for line in (root/path).read_text().splitlines():
        if line.startswith('namespace '):
            namespace = line.split()[1]
        match = re.match(r'^(?:@\[[^\]]+\] )?(?:noncomputable )?(def|theorem|abbrev|instance) (\w+)(?=\s*[:({])',line)
        if match:
            records.append(dict(name=namespace+'.'+match[2],kind=match[1],file=path))
manifest = base/'logs/declaration-coverage-016.json'
audit = root/'DkMathTest/NumberTheory/LegendreResidueCoverAxiomAudit.lean'
if '--generate' in sys.argv:
    manifest.write_text(json.dumps(records,indent=2)+'\n')
    audit.write_text(header+'''import DkMath.NumberTheory.Legendre
import DkMathTest.NumberTheory.LegendreResidueCoverCalibration

#print "file: DkMathTest.NumberTheory.LegendreResidueCoverAxiomAudit"

'''+''.join('#check '+r['name']+'\n#print axioms '+r['name']+'\n' for r in records))
    print(f'Generated {len(records)} audits; production {sum(r["file"] in prod for r in records)}.')
    sys.exit(0)
assert json.loads(manifest.read_text()) == records
if '--sources-only' not in sys.argv:
    raw=(base/'logs/axiom-audit-016.txt').read_text()
    found={m[1]:set(x.strip() for x in m[2].split(',') if x.strip())
           for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]",raw)}
    found.update({m[1]:set() for m in re.finditer(r"'([^']+)' does not depend on any axioms",raw)})
    expected={r['name'] for r in records}
    assert len(expected)==len(records) and expected<=set(found),expected-set(found)
    for name in expected:
        assert found[name]<={'propext','Classical.choice','Quot.sound'},(name,found[name])
    print(f'PASS: {len(records)}/{len(records)} complete axiom sets; no sorryAx or additional axioms.')
written=prod+tests+[str(audit.relative_to(root)),'DkMath/NumberTheory/Legendre.lean']
for path in written:
    source=(root/path).read_text()
    assert source.startswith(header),path
    module=path[:-5].replace('/','.')
    assert re.search(r'import [^\n]+\n\n#print "file: '+re.escape(module)+r'"',source),path
    if path in prod+tests:
        assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b',source),path
    assert all(line==line.rstrip() for line in source.splitlines()),path
subprocess.run(['git','diff','--check'],cwd=root,check=True)
for path in prod+tests+[str(audit.relative_to(root))]:
    result=subprocess.run(['git','diff','--no-index','--check','/dev/null',str(root/path)],capture_output=True,text=True)
    assert not result.stdout and not result.stderr,(path,result.stdout,result.stderr)
print(f'PASS: {len(written)} uniform headers/markers and tracked/new-source whitespace; scoped forbidden tokens absent.')
d=json.loads((base/'logs/discovery-016.json').read_text())
assert d['range']==[1,300] and d['anchor_count']==300
assert [r['n'] for r in d['rows']]==list(range(1,301))
for r in d['rows']+[d['calibration1031']]:
    n=r['n']; c=r['counts']
    assert r['width']==2*n and r['square_anchor']==n*n%r['period']
    assert c['R']==c['U']+c['Cube']+c['Cross']+c['Repeated']+c['Triple']
    assert c['Qtotal']==c['Cross']+c['Cube']+2*c['Repeated']+3*c['Triple']+c['Rejected']
    assert c['Qtotal']+c['U']==c['R']+c['Repeated']+2*c['Triple']+c['Rejected']
    assert sum(r['owner_fibers'].values())+r['escaping_card']==r['width']
    assert sum(r['support_overlap'].values())==r['width']
    assert r['support_overlap']['0']==r['escaping_card']
    assert (r['image_card']==r['width'])==(n==3 or n>=5)
    assert not r['full_cover'] and r['first_escape']>=1
    t=r['transition']
    assert sum(t['lower_common'].values())==n and sum(t['upper_common'].values())==n
    assert t['lower_owner_persist']==t['three_lower_owner_persist']==0
    if n>=5:
        assert 2*n+4<r['period'] and r['projected_survivors']==r['escaping_card']==c['U']
assert d['near_misses'][0]['n']==5 and d['near_misses'][0]['projected_survivors']==2
assert d['relative_stress'][0]['n']==297 and d['relative_stress'][0]['escaping_card']==45
assert d['smallest_false_owner_rule']==dict(n=8,r=11,point=75,owner=3,repeated_prime=5)
assert d['smallest_prime_false_owner_rule']==dict(n=29,r=6,point=847,owner=7,repeated_prime=11)
assert d['calibration1031']['counts']==dict(R=316,U=160,Cube=0,Cross=138,Repeated=3,Triple=15,Rejected=472,Qtotal=661)
print('PASS: all 300 natural anchors plus 1031, owner fibers, overlaps, both exact balances, transitions and near-miss records.')
if '--sources-only' not in sys.argv:
    for name in ['report-016.md','source-inventory-016.md','findings-016.md','validation-016.md']:
        source=(base/name).read_text()
        for target in re.findall(r'\]\(([^)]+)\)',source):
            if '://' not in target and not target.startswith('#'):
                assert (base/target.split('#')[0]).exists(),(name,target)
    report=(base/'report-016.md').read_text()
    assert report.rstrip().endswith('Outcome B - COUNTEREXAMPLE PACKET COMPLETE, TRANSITION LEVERAGE PARTIAL')
    assert all(f'## {i}.' in report for i in range(1,11))
    assert 'squareAnchor_corrected_gap' in report and 'n=1031' in report
    print('PASS: ten report answers, exact next-provider proposal, document links and final Outcome B.')
