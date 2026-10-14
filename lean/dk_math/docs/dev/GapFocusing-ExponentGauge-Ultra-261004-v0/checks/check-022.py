"""Full public declaration audit and independent finite diagnostics verification."""
from pathlib import Path
from math import gcd,prod,comb,isqrt
import re,json,subprocess,sys
base=Path(__file__).resolve().parent.parent
root=base.parents[2]
production=['DkMath/Combinatorics/FinsetSupportPacking.lean']+[
 'DkMath/NumberTheory/Legendre/'+x+'.lean' for x in [
 'CoarseTownSurvivorCapacity','CoarseTownDeletionConservation']]
regressions=['DkMathTest/NumberTheory/'+x+'.lean' for x in [
 'LegendreConservationRegression','LegendreSurvivor297Calibration','LegendreSurvivor1031Calibration']]
audit='DkMathTest/NumberTheory/LegendreConservationAxiomAudit.lean'
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
# Keep the earlier search and old-world endpoint names visible in the same audit.
for file,name in [
 ('DkMathTest/NumberTheory/LegendreCapacity297Calibration.lean',
  'DkMathTest.LegendreCapacity297Calibration.exists_prime_squareCell_297_of_explicitCapacityCertificate'),
 ('DkMathTest/NumberTheory/LegendreDeletion1031Calibration.lean',
  'DkMathTest.LegendreDeletion1031Calibration.exists_prime_squareCell_1031_of_coarseTownDeletion')]:
 line=next(i for i,t in enumerate((root/file).read_text().splitlines(),1) if t.startswith('theorem '+name.split('.')[-1]+' '))
 records.append(dict(name=name,kind='theorem',file=file,line=line))
manifest=base/'logs/declaration-coverage-022.json'
if '--generate' in sys.argv:
 manifest.write_text(json.dumps(records,indent=2)+'\n')
 (root/audit).write_text(header+'''import DkMath.NumberTheory.Legendre
import DkMathTest.NumberTheory.LegendreConservationRegression
import DkMathTest.NumberTheory.LegendreSurvivor297Calibration
import DkMathTest.NumberTheory.LegendreSurvivor1031Calibration
import DkMathTest.NumberTheory.LegendreCapacity297Calibration

#print "file: DkMathTest.NumberTheory.LegendreConservationAxiomAudit"

'''+''.join('#check '+r['name']+'\n#print axioms '+r['name']+'\n' for r in records))
 print('Generated audit:',len(records),'declarations;',sum(r['file'] in production for r in records),'production')
 sys.exit(0)
assert json.loads(manifest.read_text())==records
raw=(base/'logs/axiom-audit-022.txt').read_text()
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
data=json.loads((base/'logs/discovery-022.json').read_text())
prior=json.loads((base/'logs/discovery-020.json').read_text())
assert len(data['rows'])==602
for r,o in zip(data['rows'],prior['rows'],strict=True):
 n=r['n'];S=set(r['S']);M=o['M'];K=o['K']
 assert (n,r['world_kind'],S)==(o['n'],o['world_kind'],set(o['S']))
 P=[q for q in range(2,n+1) if all(q%d for d in range(2,isqrt(q)+1))]
 T=set(P)-S
 V={a+j*M for a in range(1,M+1) if gcd(n*n+a,M)==1 for j in range(K)}
 # Reconstruct oriented edges independently of the discovery fiber-union algorithm.
 supports={a:{q for q in T if (n*n+a)%q==0} for a in V}
 E={(a,b) for a in V for b in V if a<b and supports[a]&supports[b]}
 D={a for a,b in E};Dr={b for a,b in E}
 R=V-D;Rr=V-Dr
 A=set().union(*supports.values()) if supports else set()
 U={a for a in V if not supports[a]}
 I=sum(map(len,supports.values()));X=sum(max(0,len(f)-1) for f in supports.values())
 m={a:sum(any(b>a and q in supports[b] for b in V) for q in supports[a]) for a in V}
 mass=sum(m.values());O=sum(m[a]-1 for a in D)
 assert D=={a for a in V if m[a]>0}
 assert all(m[a]<=len(supports[a]) for a in V)
 assert tuple(r[k] for k in ['V','T','A','U','I','X','Dleft','Rleft','deletion_mass','O','Dright','Rright'])==(len(V),len(T),len(A),len(U),I,X,len(D),len(R),mass,O,len(Dr),len(Rr))
 assert len(R)+X==len(U)+len(A)+O and len(D)+O==mass and mass+len(A)==I
 assert r['residual']==0 and O<=X and not r['conservation_left']
 assert r['inactive']==len(T)-len(A) and r['overlap_minus_excess']==O-X
 assert r['direct_left']==(len(T)<len(R)) and r['direct_right']==(len(T)<len(Rr))
 assert len(Rr)+X==len(U)+len(A)+r['Oright']
 assert r['direct_left']==(X-O+len(T)-len(A)<len(U))
 assert all(len(R&{a for a in V if q in supports[a]})<=1 for q in T)
assert data['counts']=={k:sum(r[k] for r in data['rows']) for k in data['counts']}
assert data['first_false_equivalence']['n']==1
for n in [5,11,19,29,297,1031]:assert any(r['n']==n for r in data['rows'])
r297=next(r for r in data['rows'] if r['n']==297 and r['world_kind']=='initial')
r1031=next(r for r in data['rows'] if r['n']==1031 and r['world_kind']=='initial')
assert (r297['T'],r297['Rright'],r297['Dright'])==(58,60,36)
assert (r1031['T'],r1031['Rleft'],r1031['O'],r1031['X'])==(169,216,95,151)
assert 'LegendreCapacity297Calibration' not in (root/regressions[1]).read_text()
print('PASS 602 independently reconstructed edge, incidence, multiplicity, both orientation and loss ledgers')
for name in ['source-inventory-022.md','findings-022.md','report-022.md','validation-022.md']:
 s=(base/name).read_text();s.encode('ascii');assert '\\' not in s,name
 assert all(t==t.rstrip() for t in s.splitlines()),name
 for target in re.findall(r'\]\(([^)]+)\)',s):
  if '://' not in target and not target.startswith('#'):assert (base/target.split('#')[0]).exists(),(name,target)
report=(base/'report-022.md').read_text()
assert all(f'## {i}.' in report for i in range(1,18))
assert report.rstrip().endswith('Outcome A - SURVIVOR-WORLD CAPACITY ADDS NEW DETERMINISTIC ENDPOINTS')
for name in ['focused','facade','root','axiom-audit']:
 s=(base/f'logs/{name}-022.txt').read_text()
 assert 'Build completed successfully' in s and not re.search(r'^error:',s,re.M),name
print('PASS seventeen report answers, exact judgment, ASCII artifacts and four successful validation builds')

for p in (base/'logs').glob('*022*.txt'):
 s=p.read_text();s.encode('ascii');assert '\\' not in s,p
print('PASS ASCII plain text logs without backslash notation')
