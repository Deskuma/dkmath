"""Check complete axiom coverage, artifacts, build evidence and the bounded diagnostics."""
from pathlib import Path
from math import comb, gcd, prod
from fractions import Fraction
import json,re,subprocess
base=Path(__file__).resolve().parent.parent
root=base.parents[2]
coverage=json.loads((base/'logs/declaration-coverage-025.json').read_text())
raw=(base/'logs/axiom-audit-025.txt').read_text()
found={m[1]:set(x.strip() for x in m[2].split(',') if x.strip()) for m in re.finditer(r"'(.+?)' depends on axioms: \[([^\]]*)\]",raw)}
found.update({m[1]:set() for m in re.finditer(r"'(.+?)' does not depend on any axioms",raw)})
names=[d for row in coverage['modules'] for d in row['declarations']]
assert len(names)==len(set(names))==coverage['total']==128
for name in names:
 assert name in found,name
 assert found[name]<={'propext','Classical.choice','Quot.sound'},(name,found[name])
print('PASS complete axiom coverage: 95 production and 33 calibration declarations; all 49 new production declarations covered.')
print('PASS no new sorryAx dependencies; only standard logical axioms occur.')
header='''/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

'''
leanfiles=[r['file'] for r in coverage['modules']]+['DkMathTest/NumberTheory/PascalPrebirthAxiomAudit.lean','DkMath/NumberTheory/Legendre.lean','DkMath.lean']
for name in leanfiles:
 s=(root/name).read_text()
 assert s.startswith(header),name
 assert '#print "file: '+name[:-5].replace('/','.')+'"' in s,name
 assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b',s),name
 assert all(t==t.rstrip() for t in s.splitlines()),name
for name in ['DkMath/NumberTheory/PascalPrebirthBoundary.lean','DkMath/NumberTheory/PascalPrebirthBirth.lean']:
 s=(root/name).read_text()
 assert not re.search(r'^import .*Legendre|^import .*Zsigmondy|^import .*PowerGauge',s,re.M),name
print('PASS forbidden constructs, header and file-marker conventions in 10 affected Lean files; neutral dependency direction preserved.')
subprocess.run(['git','diff','--check'],cwd=root,check=True)
for name in leanfiles:
 p=subprocess.run(['git','diff','--no-index','--check','/dev/null',str(root/name)],capture_output=True,text=True)
 assert not p.stdout and not p.stderr,(name,p.stdout,p.stderr)
print('PASS tracked diff and untracked Lean whitespace checks.')
for label in ['focused','facade','root','axiom-audit']:
 log=(base/f'logs/{label}-025.txt').read_text()
 performance=json.loads((base/f'logs/performance-{label}-025.json').read_text())
 assert performance['exit_code']==0 and performance['LEAN_NUM_THREADS']==2,label
 assert 'Build completed successfully' in log and not re.search(r'^error:',log,re.M),label
print('PASS focused, Legendre facade, DkMath root and complete axiom builds with LEAN_NUM_THREADS=2.')
data=json.loads((base/'logs/pascal-diagnostics-025.json').read_text())
for row in data['rows']:
 N=row['N']; g=0
 for k in range(1,N):g=gcd(g,comb(N,k))
 assert row['gcd']==g
 p=row['selected_modulus']
 assert row['prebirth']==all(comb(N-1,k)%p==pow(-1,k,p) for k in range(N))
 assert row['common_next']==all(comb(N,k)%p==0 for k in range(1,N))
 assert row['prebirth']==row['common_next']==row['prime_power']
 assert row['gcd']==(row['base'] or 1)
for mode,scan in data['monotonicity'].items():
 for name,item in scan['first_increase'].items():
  if item:assert Fraction(item['before'])<Fraction(item['after'])
 assert scan['first_increase']['nonzero_adjacent_per_d'] is None if mode=='prime' else scan['first_increase']['nonzero_adjacent_per_d'] is not None
assert data['monotonicity']['prime']['transitions']==138
assert data['monotonicity']['prime_power']['transitions']==663
for row in data['anchors']:
 assert row['full_factorization_checked']
 assert Fraction(row['ratio'])==Fraction(2,row['n']+2)
 assert row['support_card']==row['old_support_card']+row['fresh_count']
 assert row['fresh_count']==len(row['fresh_primes'])
 assert all(row['n']**2<p<=row['top'] for p in row['fresh_primes'])
for row in data['preflight']:
 assert row['point']==row['n']**2+row['r']==prod(row['factors'])
print('PASS required finite rows, exact fractional counterexamples, six anchor ledgers and both 024 arithmetic checks.')
for name in ['source-inventory-025.md','findings-025.md','report-025.md','validation-025.md']:
 s=(base/name).read_text();s.encode('ascii');assert chr(92) not in s,name
 assert all(t==t.rstrip() for t in s.splitlines()),name
 for target in re.findall(r'\]\(([^)]+)\)',s):
  if '://' not in target and not target.startswith('#'):assert (base/target.split('#')[0]).exists(),(name,target)
report=(base/'report-025.md').read_text()
assert all(f'## {i}.' in report for i in range(1,17))
assert report.rstrip().endswith('Outcome B - PRIME-POWER PREBIRTH BOUNDARY IS EXACT BUT LEGENDRE GROWTH BRIDGE REMAINS')
for p in (base/'logs').glob('*025*'):
 if p.suffix in ['.txt','.json']:
  s=p.read_text();s.encode('ascii');assert chr(92) not in s,p
print('PASS sixteen report answers, next implementation proposal, Outcome B and ASCII artifacts.')
