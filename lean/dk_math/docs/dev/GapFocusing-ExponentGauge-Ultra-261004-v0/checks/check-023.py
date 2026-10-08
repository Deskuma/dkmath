"""Full public declaration audit and independent finite diagnostics verification."""
from pathlib import Path
from math import gcd,prod,comb,isqrt
import re,json,subprocess,sys
base=Path(__file__).resolve().parent.parent
root=base.parents[2]
production=['DkMath/Combinatorics/FinsetSupportDirections.lean']+[
 'DkMath/NumberTheory/Legendre/'+x+'.lean' for x in [
 'CoarseTownRetainedDirections','CoarseTownSymmetricDeletion','CoarseTownPrimeHandoff']]
regressions=['DkMathTest/NumberTheory/'+x+'.lean' for x in [
 'LegendreRetained297Calibration','LegendreRetained1031Calibration','LegendreHandoffRegression']]
audit='DkMathTest/NumberTheory/LegendreRetainedAxiomAudit.lean'
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
  m=re.match(r"^(?:@\[[^\]]+\]\s+)?(?:noncomputable )?(def|theorem|lemma|abbrev)\s+([\w']+)",text)
  if m:records.append(dict(name=namespace+'.'+m[2],kind=m[1],file=f,line=line))
# Preserve both 022 deterministic endpoint names in the same dependency audit.
for file,name in [
 ('DkMathTest/NumberTheory/LegendreSurvivor297Calibration.lean',
  'DkMathTest.LegendreSurvivor297Calibration.exists_prime_squareCell_297_of_right_survivor_deletion'),
 ('DkMathTest/NumberTheory/LegendreSurvivor1031Calibration.lean',
  'DkMathTest.LegendreSurvivor1031Calibration.exists_prime_squareCell_1031_of_survivor_deletion')]:
 line=next(i for i,t in enumerate((root/file).read_text().splitlines(),1) if t.startswith('theorem '+name.split('.')[-1]+' '))
 records.append(dict(name=name,kind='theorem',file=file,line=line))
manifest=base/'logs/declaration-coverage-023.json'
if '--generate' in sys.argv:
 manifest.write_text(json.dumps(records,indent=2)+'\n')
 (root/audit).write_text(header+'''import DkMath.NumberTheory.Legendre
import DkMathTest.NumberTheory.LegendreRetained297Calibration
import DkMathTest.NumberTheory.LegendreRetained1031Calibration
import DkMathTest.NumberTheory.LegendreHandoffRegression

#print "file: DkMathTest.NumberTheory.LegendreRetainedAxiomAudit"

'''+''.join('#check '+r['name']+'\n#print axioms '+r['name']+'\n' for r in records))
 print('Generated audit:',len(records),'declarations;',sum(r['file'] in production for r in records),'production')
 sys.exit(0)
assert json.loads(manifest.read_text())==records
raw=(base/'logs/axiom-audit-023.txt').read_text()
found={m[1]:set(x.strip() for x in m[2].split(',') if x.strip()) for m in re.finditer(r"'(.+?)' depends on axioms: \[([^\]]*)\]",raw)}
found.update({m[1]:set() for m in re.finditer(r"'(.+?)' does not depend on any axioms",raw)})
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
data=json.loads((base/'logs/discovery-023.json').read_text())
prior=json.loads((base/'logs/discovery-020.json').read_text())
assert len(data['rows'])==602
for row,old in zip(data['rows'],prior['rows'],strict=True):
 n=row['n'];S=set(row['S']);M=old['M'];K=old['K']
 assert (n,row['world_kind'],S)==(old['n'],old['world_kind'],set(old['S']))
 T={q for q in range(2,n+1) if q not in S and all(q%d for d in range(2,isqrt(q)+1))}
 V={a+j*M for a in range(1,M+1) if gcd(n*n+a,M)==1 for j in range(K)}
 f={a:{q for q in T if (n*n+a)%q==0} for a in V}
 E={(a,b) for a in V for b in V if a<b and f[a]&f[b]}
 U={a for a in V if not f[a]};A=set().union(*f.values()) if f else set()
 I=sum(map(len,f.values()));X=sum(max(0,len(t)-1) for t in f.values())
 assert tuple(row[k] for k in ['V','T','A','U','I','X'])==(len(V),len(T),len(A),len(U),I,X)
 assert I+len(U)==len(V)+X
 for side,D in [('left',{a for a,b in E}),('right',{b for a,b in E})]:
  r=row[side];R=V-D;rep=set().union(*(f[a] for a in R)) if R else set();lost=A-rep
  excess=sum(max(0,len(f[a])-1) for a in R)
  endpoint={q:(max if side=='left' else min)(a for a in V if q in f[a]) for q in A}
  H={(q,p) for q in A for p in A if p in f[endpoint[q]] and any(p in f[b] and (endpoint[q]<b if side=='left' else b<endpoint[q]) for b in V)}
  assert all(q!=p and (endpoint[q]<endpoint[p] if side=='left' else endpoint[p]<endpoint[q]) for q,p in H)
  assert lost=={q for q,p in H}
  assert rep=={q for q in A if endpoint[q] in R}
  depth={}
  for q in sorted(A,key=endpoint.get,reverse=side=='left'):
   depth[q]=max([1+depth[p] for x,p in H if x==q]+[0])
  mass=I-len(A);O=mass-len(D);loss=X-O
  assert tuple(r[k] for k in ['represented','unrepresented','retained_excess','loss','R','D','O','mass','handoff_edges','chain_depth'])==(len(rep),len(lost),excess,loss,len(R),len(D),O,mass,len(H),max(depth.values(),default=0))
  assert U<=R and loss==len(lost)+excess and len(rep)==len(R)-len(U)+excess
  assert len(R)+loss==len(U)+len(A) and len(R)+X==len(U)+len(A)+O
  assert O<=X and r['residual']==r['master_residual']==0
  if n in [29,297,1031] and row['world_kind']=='initial':
   d=data['details'][str(n)][side]
   assert d['remainder']==sorted(R) and d['represented']==sorted(rep) and d['unrepresented']==sorted(lost)
   assert d['edges']==[list(x) for x in sorted(H)]
 assert row['better_R']==max(row['left']['R'],row['right']['R'])
 assert row['better_loss']==min(row['left']['loss'],row['right']['loss'])
 assert row['better_R']+row['better_loss']==row['U']+row['A']
 assert row['survivor_capacity']==(row['T']<row['better_R'])==(row['better_loss']+row['T']-row['A']<row['U'])
assert data['counts']==dict(better=sum(r['survivor_capacity'] for r in data['rows']),left=sum(r['T']<r['left']['R'] for r in data['rows']),right=sum(r['T']<r['right']['R'] for r in data['rows']))
assert data['counts']==dict(better=586,left=570,right=572)
print('PASS 602 independently reconstructed edge selectors, retained unions, loss decompositions, handoffs and ranks')
for name in ['source-inventory-023.md','findings-023.md','report-023.md','validation-023.md']:
 s=(base/name).read_text();s.encode('ascii');assert '\\' not in s,name
 assert all(t==t.rstrip() for t in s.splitlines()),name
 for target in re.findall(r'\]\(([^)]+)\)',s):
  if '://' not in target and not target.startswith('#'):assert (base/target.split('#')[0]).exists(),(name,target)
report=(base/'report-023.md').read_text()
assert all(f'## {i}.' in report for i in range(1,21))
assert report.rstrip().endswith('Outcome C - RETAINED-DIRECTION THEORY CLOSES THE PACKING ROUTE')
for name in ['focused','facade','root','axiom-audit']:
 s=(base/f'logs/{name}-023.txt').read_text()
 assert 'Build completed successfully' in s and not re.search(r'^error:',s,re.M),name
print('PASS twenty report answers, exact judgment, ASCII artifacts and four successful validation builds')

for p in (base/'logs').glob('*023*.txt'):
 s=p.read_text();s.encode('ascii');assert '\\' not in s,p
print('PASS ASCII plain text logs without backslash notation')
