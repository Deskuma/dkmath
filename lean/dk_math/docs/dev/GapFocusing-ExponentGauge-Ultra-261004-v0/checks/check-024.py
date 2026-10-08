"""Complete declaration audit and independent factorization-based finite checks."""
from pathlib import Path
from math import gcd,isqrt,prod
from functools import lru_cache
import re,json,csv,subprocess,sys
base=Path(__file__).resolve().parent.parent
root=base.parents[2]
production=['DkMath/NumberTheory/Legendre/'+x+'.lean' for x in
            ['CoarseTownTerminalProduct','CoarseTownSourceMultiplicity']]
regressions=['DkMathTest/NumberTheory/LegendreTerminalProductCalibration.lean']
audit='DkMathTest/NumberTheory/LegendreTerminalProductAxiomAudit.lean'
header='''/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

'''
records=[]
for file in production+regressions:
    namespace=''
    for line,text in enumerate((root/file).read_text().splitlines(),1):
        if text.startswith('namespace '):namespace=text.split()[1]
        m=re.match(r"^(?:@\[[^\]]+\]\s+)?(?:noncomputable )?(def|theorem|lemma|abbrev)\s+([\w']+)",text)
        if m:records.append(dict(name=namespace+'.'+m[2],kind=m[1],file=file,line=line))
for file,name in [
    ('DkMathTest/NumberTheory/LegendreHandoffRegression.lean','DkMathTest.LegendreHandoffRegression.uniform_branching_297'),
    ('DkMathTest/NumberTheory/LegendreSurvivor297Calibration.lean','DkMathTest.LegendreSurvivor297Calibration.exists_prime_squareCell_297_of_right_survivor_deletion'),
    ('DkMathTest/NumberTheory/LegendreSurvivor1031Calibration.lean','DkMathTest.LegendreSurvivor1031Calibration.exists_prime_squareCell_1031_of_survivor_deletion')]:
    line=next(i for i,t in enumerate((root/file).read_text().splitlines(),1) if t.startswith('theorem '+name.split('.')[-1]+' '))
    records.append(dict(name=name,kind='theorem',file=file,line=line))
manifest=base/'logs/declaration-coverage-024.json'
if '--generate' in sys.argv:
    manifest.write_text(json.dumps(records,indent=2)+'\n')
    (root/audit).write_text(header+'''import DkMath.NumberTheory.Legendre
import DkMathTest.NumberTheory.LegendreTerminalProductCalibration

#print "file: DkMathTest.NumberTheory.LegendreTerminalProductAxiomAudit"

'''+''.join('#check '+r['name']+'\n#print axioms '+r['name']+'\n' for r in records))
    print('Generated',len(records),'entries;',sum(r['file'] in production for r in records),'production')
    sys.exit(0)
assert json.loads(manifest.read_text())==records
raw=(base/'logs/axiom-audit-024.txt').read_text()
found={m[1]:set(x.strip() for x in m[2].split(',') if x.strip()) for m in re.finditer(r"'(.+?)' depends on axioms: \[([^\]]*)\]",raw)}
found.update({m[1]:set() for m in re.finditer(r"'(.+?)' does not depend on any axioms",raw)})
for r in records:
    assert r['name'] in found,r
    assert found[r['name']]<={'propext','Classical.choice','Quot.sound'},(r,found[r['name']])
print('PASS complete public dependency coverage:',len(records),'standard logical axiom sets')
for file in production+regressions+[audit,'DkMath/NumberTheory/Legendre.lean']:
    s=(root/file).read_text();assert s.startswith(header),file
    assert re.search(r'import [^\n]+\n\n#print "file: '+re.escape(file[:-5].replace('/','.'))+'"',s),file
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b',s),file
    assert all(t==t.rstrip() for t in s.splitlines()),file
    if file in production:
        assert not re.search(r'^import .*Petal|^import .*PrimitiveSet.RealLog|^import .*PowerGauge',s,re.M)
subprocess.run(['git','diff','--check'],cwd=root,check=True)
for file in production+regressions+[audit]:
    r=subprocess.run(['git','diff','--no-index','--check','/dev/null',str(root/file)],capture_output=True,text=True)
    assert not r.stdout and not r.stderr,(file,r.stdout,r.stderr)
print('PASS standard headers, file markers, forbidden constructs, imports and whitespace')

@lru_cache(None)
def factors(x):
    result=set();d=2
    while d*d<=x:
        if x%d==0:
            result.add(d)
            while x%d==0:x//=d
        d+=1
    if x>1:result.add(x)
    return result

def local_capacity(B,point):
    # Minimal threshold exponent with point < B^(k+1), rather than discovery's floor loop.
    k=0
    while point>=B**(k+1):k+=1
    return k-1

data=json.loads((base/'logs/discovery-024.json').read_text())
prior=json.loads((base/'logs/discovery-023.json').read_text())['rows']
geometry=json.loads((base/'logs/discovery-020.json').read_text())['rows']
ints={'n','P','a','complete_point','power_base','support_card','terminal_card','continuing_card',
      'terminal_product','continuing_product','support_product','lower_power','local_source_capacity',
      'uniform_source_capacity','continuing_aware_capacity'}
booleans={'initial_cutoff_valid','capacity_improves_support_minus_one','continuing_aware_improves_support_minus_one'}
records_seats={}
with (base/'logs'/data['seats_file']).open(newline='') as stream:
    for r in csv.DictReader(stream):
        for field in ints:r[field]=int(r[field])
        for field in booleans:
            assert r[field] in ['True','False'];r[field]=r[field]=='True'
        for field in ['support','terminal','continuing']:r[field]=list(map(int,r[field].split(';'))) if r[field] else []
        r['initial_lower_power']=int(r['initial_lower_power']) if r['initial_lower_power'] else None
        key=(r['n'],r['world_kind'],r['side'],r['a'])
        assert key not in records_seats
        records_seats[key]=r
assert len(data['rows'])==602 and len(records_seats)==68813
used=set();aware_count=0
for row,old,g in zip(data['rows'],prior,geometry,strict=True):
    n,S,M,K=row['n'],set(row['S']),g['M'],g['K'];P=max(S,default=0)
    initial=S=={q for q in range(2,P+1) if factors(q)=={q}}
    B=max(2,P+1) if initial else 2
    assert (n,row['world_kind'],S)==(old['n'],old['world_kind'],set(old['S']))
    assert row['P']==P and row['initial_cutoff_valid']==initial and row['power_base']==B
    V={a for a in range(1,K*M+1) if gcd(n*n+a,M)==1}
    f={a:{q for q in factors(n*n+a) if q<=n and q not in S} for a in V}
    A=set().union(*f.values()) if f else set()
    k=0
    while B**(k+1)<(n+1)**2:k+=1
    uniform=max(0,k-1)
    assert row['uniform_k']==k and row['uniform_source_capacity']==uniform
    for side in ['left','right']:
        term={a:{q for q in f[a] if not any(q in f[b] for b in V if (a<b if side=='left' else b<a))} for a in V}
        C={a:f[a]-term[a] for a in V};D={a for a in V if C[a]};R=V-D
        sources=[q for a in D for q in term[a]]
        assert len(sources)==len(set(sources))
        missing=A-(set().union(*(f[a] for a in R)) if R else set())
        assert set(sources)==missing
        retained=sum(max(0,len(f[a])-1) for a in R)
        local_total=0;aware_side=0
        for a in D:
            key=(n,row['world_kind'],side,a);r=records_seats[key];used.add(key)
            support,t,c=f[a],term[a],C[a];point=n*n+a;capacity=local_capacity(B,point)
            assert (r['support'],r['terminal'],r['continuing'])==(sorted(support),sorted(t),sorted(c))
            assert (r['support_card'],r['terminal_card'],r['continuing_card'])==(len(support),len(t),len(c))
            assert (r['terminal_product'],r['continuing_product'],r['support_product'])==(prod(t),prod(c),prod(support))
            assert r['complete_point']==point and r['lower_power']==B**len(support)
            assert r['initial_lower_power']==((P+1)**len(support) if initial else None)
            assert r['P']==P and r['power_base']==B and r['initial_cutoff_valid']==initial
            assert r['local_source_capacity']==capacity and r['uniform_source_capacity']==uniform
            assert r['continuing_aware_capacity']==capacity+1-len(c)
            assert r['capacity_improves_support_minus_one']==(capacity<len(support)-1)==False
            aware=capacity+1-len(c)<len(support)-1
            assert r['continuing_aware_improves_support_minus_one']==aware
            aware_side+=aware;aware_count+=aware;local_total+=capacity
            assert point%prod(support)==0 and B**len(support)<=prod(support)<=point<(n+1)**2
            assert len(t)<=capacity and len(support)-1<=capacity and len(t)<=capacity+1-len(c)
            assert all(q>P for q in support) if initial else True
        rr=row[side]
        expected=dict(missing=len(missing),sum_terminal=len(sources),max_terminal=max([len(term[a]) for a in D]+[0]),
                      multi_source_seats=sum(len(term[a])>=2 for a in D),deleted=len(D),retained_excess=retained,
                      local_product_loss_upper=local_total+retained,uniform_product_loss_upper=len(D)*uniform+retained,
                      existing_loss=len(missing)+retained,existing_support_excess=sum(max(0,len(s)-1) for s in f.values()),
                      continuing_aware_local_improvements=aware_side,exact_source_residual=0)
        assert rr==expected,(n,side,rr,expected)
        assert rr['existing_loss']==old[side]['loss'] and rr['existing_support_excess']<=rr['local_product_loss_upper']
    assert row['better_loss']==old['better_loss'] and row['survivor_capacity']==old['survivor_capacity']
    assert row['product_better_loss_upper']==min(row[s]['local_product_loss_upper'] for s in ['left','right'])
    assert row['product_survivor_capacity']==(row['product_better_loss_upper']+old['T']-old['A']<old['U'])
    assert not row['product_survivor_capacity'] or row['survivor_capacity']
assert used==set(records_seats) and aware_count==68
assert data['counts']==dict(worlds=602,deleted_records=68813,simple_local_improvements=0,
                          continuing_aware_improvements=68,product_capacity_worlds=25,existing_capacity_worlds=586)
for seat in list(data['examples'].values())+list(data['counterexamples'].values()):
    assert records_seats[(seat['n'],seat['world_kind'],seat['side'],seat['a'])]==seat
assert data['examples']['first_shared']['n']==11 and data['examples']['first_shared']['a']==19
for r in json.loads((base/'logs/proposed-cofactor-024.json').read_text()):
    seat=data['examples'][r['example']];n,a=r['n'],r['a'];m=n*n+a
    g=next(g for g in geometry if (g['n'],g['world_kind'])==(n,seat['world_kind']))
    V={b for b in range(1,g['K']*g['M']+1) if gcd(n*n+b,g['M'])==1}
    delta=prod(b-a for b in V if a<b)
    assert r['difference_product_mod_point']==delta%m and r['common_gcd']==gcd(m,delta)
    assert r['proposed_cofactor']==m//gcd(m,delta)
    assert r['terminal_product']==seat['terminal_product'] and r['proposed_cofactor']%r['terminal_product']==0
    B=r['power_base'];e=r['proposed_source_capacity']
    assert B**e<=r['proposed_cofactor']<B**(e+1)
print('PASS 602 factorization-reconstructed worlds and 68813 exact carrier/product/capacity records')
print('PASS zero source-count residuals, no new capacity worlds, and continuing-aware comparison')

for name in ['source-inventory-024.md','findings-024.md','report-024.md','validation-024.md']:
    s=(base/name).read_text();s.encode('ascii');assert '\\' not in s,name
    assert all(t==t.rstrip() for t in s.splitlines()),name
    for target in re.findall(r'\]\(([^)]+)\)',s):
        if '://' not in target and not target.startswith('#'):assert (base/target.split('#')[0]).exists(),(name,target)
report=(base/'report-024.md').read_text()
assert all(f'## {i}.' in report for i in range(1,21))
assert report.rstrip().endswith('Outcome C - TERMINAL PRODUCT IS EXACT BUT GLOBALLY TOO WEAK')
for name in ['focused','facade','root','axiom-audit']:
    s=(base/f'logs/{name}-024.txt').read_text()
    assert 'Build completed successfully' in s and not re.search(r'^error:',s,re.M),name
for p in (base/'logs').glob('*024*'):
    if p.suffix in ['.txt','.csv','.json']:
        s=p.read_text();s.encode('ascii');assert '\\' not in s,p
print('PASS twenty report answers, final outcome, ASCII artifacts and four successful builds')
