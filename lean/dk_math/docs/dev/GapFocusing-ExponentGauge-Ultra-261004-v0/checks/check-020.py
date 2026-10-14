"""Full public declaration audit and independent finite diagnostics verification."""
from pathlib import Path
from math import gcd,prod,comb,isqrt
import re,json,subprocess,sys
base=Path(__file__).resolve().parent.parent
root=base.parents[2]
production=['DkMath/Combinatorics/FinsetSupportPacking.lean']+[
 'DkMath/NumberTheory/Legendre/'+x+'.lean' for x in [
 'CoarsePrimeWorldFullTown','CoarsePrimeWorldVerticalCapacity','CoarseTownSupportPacking']]
regression='DkMathTest/NumberTheory/LegendreFullTownRegression.lean'
audit='DkMathTest/NumberTheory/LegendreFullTownAxiomAudit.lean'
header='''/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

'''
records=[]
for f in production+[regression]:
 namespace=''
 for line,text in enumerate((root/f).read_text().splitlines(),1):
  if text.startswith('namespace '):namespace=text.split()[1]
  m=re.match(r'^(?:@\[[^\]]+\]\s+)?(?:noncomputable )?(def|theorem|lemma|abbrev)\s+(\w+)',text)
  if m:records.append(dict(name=namespace+'.'+m[2],kind=m[1],file=f,line=line))
manifest=base/'logs/declaration-coverage-020.json'
if '--generate' in sys.argv:
 manifest.write_text(json.dumps(records,indent=2)+'\n')
 (root/audit).write_text(header+'''import DkMath.NumberTheory.Legendre
import DkMathTest.NumberTheory.LegendreFullTownRegression

#print "file: DkMathTest.NumberTheory.LegendreFullTownAxiomAudit"

'''+''.join('#check '+r['name']+'\n#print axioms '+r['name']+'\n' for r in records))
 print('Generated audit:',len(records),'declarations;',sum(r['file'] in production for r in records),'production')
 sys.exit(0)
assert json.loads(manifest.read_text())==records
raw=(base/'logs/axiom-audit-020.txt').read_text()
found={m[1]:set(x.strip() for x in m[2].split(',') if x.strip()) for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]",raw)}
found.update({m[1]:set() for m in re.finditer(r"'([^']+)' does not depend on any axioms",raw)})
for r in records:
 assert r['name'] in found,r
 assert found[r['name']]<={'propext','Classical.choice','Quot.sound'},(r,found[r['name']])
print('PASS complete public dependency audit:',len(records),'standard logical axiom sets')
for f in production+[regression,audit,'DkMath/NumberTheory/Legendre.lean']:
 s=(root/f).read_text();assert s.startswith(header),f
 assert re.search(r'import [^\n]+\n\n#print "file: '+re.escape(f[:-5].replace('/','.'))+'"',s),f
 assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b',s),f
 assert all(t==t.rstrip() for t in s.splitlines()),f
 if f in production and 'Combinatorics/' in f:
  assert not re.search(r'^import DkMath.NumberTheory',s,re.M)
subprocess.run(['git','diff','--check'],cwd=root,check=True)
for f in production+[regression,audit]:
 r=subprocess.run(['git','diff','--no-index','--check','/dev/null',str(root/f)],capture_output=True,text=True)
 assert not r.stdout and not r.stderr,(f,r.stdout,r.stderr)
print('PASS headers, markers, forbidden constructs, dependency direction and whitespace')
data=json.loads((base/'logs/discovery-020.json').read_text())
prior=json.loads((base/'logs/discovery-019.json').read_text())
assert len(data['rows'])==602 and data['range']==[1,300] and data['extra_anchors']==[1031]
for r,o in zip(data['rows'],prior['rows'],strict=True):
 n=r['n'];S=r['S'];M=r['M'];K=r['K']
 assert (n,r['world_kind'],S)==(o['n'],o['world_kind'],o['S'])
 old=[q for q in range(2,n+1) if all(q%d for d in range(2,isqrt(q)+1))]
 T=set(old)-set(S);B=[a for a in range(1,M+1) if gcd(n*n+a,M)==1]
 V={a+j*M for a in B for j in range(K)}
 sup={a:{q for q in old if (n*n+a)%q==0} for a in V}
 fibers={q:{a for a in V if q in sup[a]} for q in T}
 # Independent reconstruction through fiber unions rather than the discovery pair scan.
 E=set().union(*({(a,b) for a in C for b in C if a<b} for C in fibers.values())) if fibers else set()
 assert M==prod(S) and M>0 and M<=n and K==2*n//M
 assert r['fullTown_card']==K*len(B)==len(V)
 assert r['tail_size']==2*n-K*M and 0<=r['tail_size']<M
 assert all(1<=a<=2*n for a in V)
 assert all(sup[a]<=T for a in V)
 assert r['base_card']==len(B) and r['T_card']==len(T) and r['old_prime_card']==len(old)
 assert r['prime_fiber_cards']=={str(q):len(C) for q,C in fibers.items()}
 assert r['actual_support_incidence']==sum(map(len,sup.values()))==sum(map(len,fibers.values()))
 assert r['vertical_capacity']==sum((K+q-1)//q for q in T)
 assert r['vertical_slack']==r['vertical_capacity']-K
 assert r['uniform_sparse']==all(K<=q for q in T)
 assert r['minimum_outside_prime']==min(T,default=None)
 assert r['uniform_frontier_passes']==(K<=len(T))
 assert r['maximum_fiber_card']==max(map(len,fibers.values()),default=0)
 assert r['maximum_column_occupancy']==max((sum(q in sup[a+j*M] for j in range(K)) for a in B for q in T),default=0)
 for q,C in fibers.items():
  for a in B:
   occ=[j for j in range(K) if a+j*M in C]
   assert len(occ)<=(K+q-1)//q
   assert all((k-j)%q==0 for j in occ for k in occ)
  assert len(C)<=len(B)*((K+q-1)//q)
 assert r['collision_edges']==len(E)
 assert r['fiber_edge_upper']==sum(comb(len(C),2) for C in fibers.values())
 assert len(E)<=r['fiber_edge_upper']<=r['ceiling_edge_upper']
 assert r['ceiling_edge_upper']==sum(comb(len(B)*((K+q-1)//q),2) for q in T)
 assert r['edge_slack']==len(old)+len(E)-len(V)
 assert r['weak_packing_lower']==max(0,len(V)-len(E))
 R=V-{a for a,b in E}
 assert set(r['endpoint_deleted_family'])==R and len(V)<=len(R)+len(E)
 for family in [r['endpoint_deleted_family'],r['greedy_disjoint_family']]:
  assert set(family)<=V and len(family)==len(set(family))
  assert all(not sup[a]&sup[b] for a in family for b in family if a<b)
 assert r['deletion_consumer_fires']==(len(old)<len(R))
 assert r['greedy_consumer_fires']==(len(old)<len(r['greedy_disjoint_family']))
 assert r['two_street_assignment_slack']==o['near_incidence']+o['far_ordered_pairs']-len(B)
 assert r['fullTown_survivors']==sorted(a for a in V if not sup[a])
 assert r['norm']==n*n+(n-1)*(n-1)
 normP={q for q in old if r['norm']%q==0}
 assert r['norm_old_primes']==sorted(normP)
 assert r['norm_supported_seats']==sum(bool(sup[a]&normP) for a in V)
 assert r['norm_supported_edges']==sum(bool(sup[a]&sup[b]&normP) for a,b in E)
 assert r['centered_odd_gap_fits']==(o['odd_gap_radical']<=n)
print('PASS 602 independently reconstructed grids, supports, fibers, edges, packing families and 018 probes')
for name in ['source-inventory-020.md','findings-020.md','report-020.md','validation-020.md']:
 s=(base/name).read_text();s.encode('ascii');assert '\\' not in s,name
 assert all(t==t.rstrip() for t in s.splitlines()),name
 for target in re.findall(r'\]\(([^)]+)\)',s):
  if '://' not in target and not target.startswith('#'):assert (base/target.split('#')[0]).exists(),(name,target)
report=(base/'report-020.md').read_text()
assert all(f'## {i}.' in report for i in range(1,17))
assert report.rstrip().endswith('Outcome A - FULL-PERIOD TOWN YIELDS A NEW FULL-COVER OBSTRUCTION')
for name in ['focused','facade','root','axiom-audit']:
 s=(base/f'logs/{name}-020.txt').read_text()
 assert 'Build completed successfully' in s and not re.search(r'^error:',s,re.M),name
print('PASS sixteen report answers, exact judgment, ASCII artifacts and four successful validation builds')
