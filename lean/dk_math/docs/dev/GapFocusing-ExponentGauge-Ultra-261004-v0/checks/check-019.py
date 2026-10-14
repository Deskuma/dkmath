"""Public API, kernel dependency, report, and focused build evidence audit."""
from pathlib import Path
import re,json,subprocess,sys
from math import gcd,isqrt
from math import prod as integer_product
from collections import Counter
base=Path(__file__).resolve().parent.parent
root=base.parents[2]
prod=['DkMath/NumberTheory/Primitive/CrossPeriod.lean','DkMath/NumberTheory/Legendre/PrimeWorldPacketBridge.lean','DkMath/NumberTheory/Legendre/CoarsePrimorialTown.lean']
retained='DkMath/NumberTheory/Legendre/PacketCross.lean'
test='DkMathTest/NumberTheory/LegendreCoarseTownRegression.lean'
audit='DkMathTest/NumberTheory/LegendreCoarseTownAxiomAudit.lean'
header='''/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

'''
pat=r'^(?:@\[[^\]]+\]\s+)?(?:noncomputable )?(def|theorem|lemma|abbrev)\s+(\w+)'
records=[]
for f in prod+[retained,test]:
 namespace=''
 for line,text in enumerate((root/f).read_text().splitlines(),1):
  if text.startswith('namespace '):namespace=text.split()[1]
  m=re.match(pat,text)
  if m and (f!=retained or m[2]=='squareAnchorPacketCrossOffsets_mul_dvd_diff'):
   records.append(dict(name=namespace+'.'+m[2],kind=m[1],file=f,line=line))
manifest=base/'logs/declaration-coverage-019.json'
if '--generate' in sys.argv:
 manifest.write_text(json.dumps(records,indent=2)+'\n')
 (root/audit).write_text(header+'''import DkMath.NumberTheory.Legendre
import DkMathTest.NumberTheory.LegendreCoarseTownRegression

#print "file: DkMathTest.NumberTheory.LegendreCoarseTownAxiomAudit"

'''+''.join('#check '+r['name']+'\n#print axioms '+r['name']+'\n' for r in records))
 print('Generated complete public audit:',len(records),'declarations')
 sys.exit(0)
assert json.loads(manifest.read_text())==records
raw=(base/'logs/axiom-audit-019.txt').read_text()
found={m[1]:set(x.strip() for x in m[2].split(',') if x.strip()) for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]",raw)}
found.update({m[1]:set() for m in re.finditer(r"'([^']+)' does not depend on any axioms",raw)})
for r in records:
 assert r['name'] in found,r
 assert found[r['name']]<={'propext','Classical.choice','Quot.sound'},(r,found[r['name']])
print('PASS public axioms:',len(records),'sets; standard logical axioms only')
for f in prod+[retained,test,audit,'DkMath/NumberTheory/Legendre.lean']:
 s=(root/f).read_text()
 assert s.startswith(header),f
 assert re.search(r'import [^\n]+\n\n#print "file: '+re.escape(f[:-5].replace('/','.'))+'"',s),f
 if f in prod+[retained,test]:assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b',s),f
 assert all(t==t.rstrip() for t in s.splitlines()),f
 for target in re.findall(r'^import (\S+)',s,re.M):
  if f in prod and ('Primitive/' in f):assert '.Legendre' not in target
subprocess.run(['git','diff','--check'],cwd=root,check=True)
for r in records:
 f=r['file']
 result=subprocess.run(['git','diff','--no-index','--check','/dev/null',str(root/f)],capture_output=True,text=True)
 assert not result.stdout and not result.stderr,(f,result.stdout,result.stderr)
print('PASS headers, import markers, forbidden tokens, dependency direction and whitespace')
d=json.loads((base/'logs/discovery-019.json').read_text())
assert len(d['rows'])==602 and d['range']==[1,300] and d['extra_anchors']==[1031]
primes=[p for p in range(2,1032) if all(p%q for q in range(2,isqrt(p)+1))]
for r in d['rows']:
 n=r['n'];M=r['M'];S=r['S']
 assert M==integer_product(S) and all(p in primes for p in S)
 old=[p for p in primes if p<=n];T=set(old)-set(S)
 B=[a for a in range(1,M+1) if gcd(n*n+a,M)==1]
 town=B+[M+a for a in B]
 supports={a:{p for p in old if (n*n+a)%p==0} for a in town}
 occupied=Counter((p,q) for a in B for p in supports[a] for q in supports[M+a])
 assert all(p!=q for p,q in occupied)
 assert r['incidence']==sum(occupied.values())
 assert r['near_incidence']==sum(v for (p,q),v in occupied.items() if p*q<=M)
 assert r['far_incidence']==sum(v for (p,q),v in occupied.items() if M<p*q)
 assert r['near_ordered_pairs']==sum(p!=q and p*q<=M for p in T for q in T)
 assert r['far_ordered_pairs']==sum(p!=q and M<p*q for p in T for q in T)
 assert r['actual_survivors']==[a for a in town if not supports[a]]
 assert r['fully_covered_packets']==[a for a in B if supports[a] and supports[M+a]]
 assert r['maximum_pair_occupancy']==max(occupied.values(),default=0)
 assert r['original_n_packet_count']==sum(gcd(n,a)==1 for a in range(1,n+1))
 family=r['greedy_disjoint_family']
 assert len(family)==len(set(family)) and set(family)<=set(town)
 assert all(not supports[a]&supports[b] for a in family for b in family if a<b)
 assert all(supports[a] for a in r['covered_disjoint_family'])
 assert len(B)==r['base_card'] and len(T)==r['T_card']
 assert r['M']<=r['n']
 assert r['base_card']==r['shift_card']==r['residue_card']==r['coprime_pair_count']
 assert r['town_card']==2*r['base_card']
 assert r['incidence']==r['near_incidence']+r['far_incidence']
 assert r['far_incidence']<=r['far_ordered_pairs']
 assert len(r['covered_disjoint_family'])<=r['T_card']
print('PASS 602 diagnostic rows and exact finite identities')
for name in ['source-inventory-019.md','findings-019.md','report-019.md','validation-019.md']:
 s=(base/name).read_text();s.encode('ascii');assert '\\' not in s,name
 assert all(t==t.rstrip() for t in s.splitlines()),name
 for target in re.findall(r'\]\(([^)]+)\)',s):
  if '://' not in target and not target.startswith('#'):assert (base/target.split('#')[0]).exists(),(name,target)
report=(base/'report-019.md').read_text()
assert all(f'## {i}.' in report for i in range(1,17))
assert report.rstrip().endswith('Outcome B - COARSE PRIMORIAL TOWN YIELDS A NEW EXACT ASSIGNMENT FRONTIER')
for name in ['focused','facade','root','axiom-audit']:
 raw=(base/f'logs/{name}-019.txt').read_text()
 assert 'Build completed successfully' in raw and not re.search(r'^error:',raw,re.M),name
print('PASS ASCII artifacts, sixteen answers, exact outcome and four successful builds')
