"""Full public declaration audit and independent finite diagnostics verification."""
from pathlib import Path
from math import gcd,prod,comb,isqrt
import re,json,subprocess,sys
base=Path(__file__).resolve().parent.parent
root=base.parents[2]
production=['DkMath/Combinatorics/FinsetSupportPacking.lean']+[
 'DkMath/NumberTheory/Legendre/'+x+'.lean' for x in [
 'OldSupportCapacityCertificate','CoarseTownDeletionCapacity']]
regressions=['DkMathTest/NumberTheory/'+x+'.lean' for x in [
 'LegendreDeletionRegression','LegendreCapacity297Calibration',
 'LegendreDeletion1031Data','LegendreDeletion1031Calibration','LegendreDeletionProvenance',
 'LegendreCapacity1031Calibration','LegendreDeletion1031Strictness']]
audit='DkMathTest/NumberTheory/LegendreDeletionAxiomAudit.lean'
header='''/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

'''
records=[]
for f in production+regressions:
 namespace=''
 for line,text in enumerate((root/f).read_text().splitlines(),1):
  if text.startswith('namespace '):namespace=text.split()[1]
  m=re.match(r'^(?:@\[[^\]]+\]\s+)?(?:noncomputable )?(def|theorem|lemma|abbrev)\s+(\w+)',text)
  if m:records.append(dict(name=namespace+'.'+m[2],kind=m[1],file=f,line=line))
manifest=base/'logs/declaration-coverage-021.json'
if '--generate' in sys.argv:
 manifest.write_text(json.dumps(records,indent=2)+'\n')
 (root/audit).write_text(header+'''import DkMath.NumberTheory.Legendre
import DkMathTest.NumberTheory.LegendreDeletionRegression
import DkMathTest.NumberTheory.LegendreCapacity297Calibration
import DkMathTest.NumberTheory.LegendreDeletionProvenance
import DkMathTest.NumberTheory.LegendreCapacity1031Calibration
import DkMathTest.NumberTheory.LegendreDeletion1031Strictness

#print "file: DkMathTest.NumberTheory.LegendreDeletionAxiomAudit"

'''+''.join('#check '+r['name']+'\n#print axioms '+r['name']+'\n' for r in records))
 print('Generated audit:',len(records),'declarations;',sum(r['file'] in production for r in records),'production')
 sys.exit(0)
assert json.loads(manifest.read_text())==records
raw=(base/'logs/axiom-audit-021.txt').read_text()
found={m[1]:set(x.strip() for x in m[2].split(',') if x.strip()) for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]",raw)}
found.update({m[1]:set() for m in re.finditer(r"'([^']+)' does not depend on any axioms",raw)})
for r in records:
 assert r['name'] in found,r
 assert found[r['name']]<={'propext','Classical.choice','Quot.sound'},(r,found[r['name']])
print('PASS complete public dependency audit:',len(records),'standard logical axiom sets')
for f in production+regressions+[audit,'DkMath/NumberTheory/Legendre.lean']:
 s=(root/f).read_text();assert s.startswith(header),f
 assert re.search(r'import [^\n]+\n\n#print "file: '+re.escape(f[:-5].replace('/','.'))+'"',s),f
 assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b',s),f
 assert all(t==t.rstrip() for t in s.splitlines()),f
 if f in production and 'Combinatorics/' in f:
  assert not re.search(r'^import DkMath.NumberTheory',s,re.M)
subprocess.run(['git','diff','--check'],cwd=root,check=True)
for f in production+regressions+[audit]:
 r=subprocess.run(['git','diff','--no-index','--check','/dev/null',str(root/f)],capture_output=True,text=True)
 assert not r.stdout and not r.stderr,(f,r.stdout,r.stderr)
print('PASS headers, markers, forbidden constructs, dependency direction and whitespace')
data=json.loads((base/'logs/discovery-021.json').read_text())
prior=json.loads((base/'logs/discovery-020.json').read_text())
assert len(data['rows'])==602 and data['range']==[1,300] and data['extra_anchors']==[1031]
for r,o in zip(data['rows'],prior['rows'],strict=True):
 n=r['n'];M=r['M'];K=r['K'];S=r['S']
 assert (n,r['world_kind'],S)==(o['n'],o['world_kind'],o['S'])
 P=[q for q in range(2,n+1) if all(q%d for d in range(2,isqrt(q)+1))]
 B=[a for a in range(1,M+1) if gcd(n*n+a,M)==1]
 V={a+j*M for a in B for j in range(K)}
 F={q:{a for a in V if (n*n+a)%q==0} for q in P}
 E=set().union(*({(a,b) for a in C for b in C if a<b} for C in F.values())) if F else set()
 D={a for a,b in E};Dr={b for a,b in E};R=V-D;Rr=V-Dr
 assert (len(V),len(E),len(D),len(Dr),len(R),len(Rr))==tuple(r[k] for k in ['town_card','edge_card','left_deletion_card','right_deletion_card','left_remainder_card','right_remainder_card'])
 assert len(V)==len(R)+len(D)==len(Rr)+len(Dr)
 assert D<=V and Dr<=V and not R&D and R|D==V
 assert D==set().union(*(C-{max(C)} if C else set() for C in F.values()))
 assert Dr==set().union(*(C-{min(C)} if C else set() for C in F.values()))
 assert all(len(R&C)<=1 and len(Rr&C)<=1 for C in F.values())
 assert r['raw_prime_fiber_deletion_bound']==sum(max(0,len(C)-1) for C in F.values())
 for flag,sz in [('left_fires',len(R)),('right_fires',len(Rr)),('greedy_fires',len(o['greedy_disjoint_family']))]:
  assert r[flag]==(len(P)<sz)
 assert r['best_endpoint_fires']==(r['left_fires'] or r['right_fires'])
 assert r['edge_fires']==(len(P)+len(E)<len(V))
 assert r['greedy_card']==len(o['greedy_disjoint_family'])
assert data['counts']=={k:sum(r[k] for r in data['rows']) for k in data['counts']}
for anchor,name,definition in [(297,'LegendreCapacity297Calibration','seats297'),(1031,'LegendreCapacity1031Calibration','seats1031List')]:
 text=(root/('DkMathTest/NumberTheory/'+name+'.lean')).read_text()
 match=re.search(r'def '+definition+r' : (?:Finset|List) ℕ :=\s*\(?\[([^]]+)\]',text)
 seats=list(map(int,re.findall(r'\d+',match[1])))
 row=next(r for r in prior['rows'] if r['n']==anchor and r['world_kind']=='initial')
 assert seats==sorted(row['greedy_disjoint_family'])
st=data['structure1031']
assert len(st['remainder'])==216 and len(st['deletion'])==216
assert len(st['empty_support_seats'])==144 and len(st['retained_supported_seats'])==72
assert sum(c['retained_count'] for c in st['columns'])==216 and len(st['columns'])==48
print('PASS 602 independently reconstructed oriented deletions, partitions, fibers, thresholds and explicit discovery witness')
for name in ['source-inventory-021.md','findings-021.md','report-021.md','validation-021.md']:
 s=(base/name).read_text();s.encode('ascii');assert '\\' not in s,name
 assert all(t==t.rstrip() for t in s.splitlines()),name
 for target in re.findall(r'\]\(([^)]+)\)',s):
  if '://' not in target and not target.startswith('#'):assert (base/target.split('#')[0]).exists(),(name,target)
report=(base/'report-021.md').read_text()
assert all(f'## {i}.' in report for i in range(1,18))
assert report.rstrip().endswith('Outcome A - EXACT DELETION CARRIER ADDS NEW KERNEL ENDPOINTS')
for name in ['focused','facade','root','axiom-audit']:
 s=(base/f'logs/{name}-021.txt').read_text()
 assert 'Build completed successfully' in s and not re.search(r'^error:',s,re.M),name
print('PASS seventeen report answers, exact judgment, ASCII artifacts and four successful validation builds')

for p in (base/'logs').glob('*021.txt'):
 s=p.read_text();s.encode('ascii');assert '\\' not in s,p
print('PASS ASCII plain text logs without backslash notation')
