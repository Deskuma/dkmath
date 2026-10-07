"""Audit complete declaration coverage, bounded diagnostic data and build evidence."""
from pathlib import Path
import json,re,subprocess,math
base=Path(__file__).resolve().parent.parent
root=base.parents[2]
coverage=json.loads((base/'logs/declaration-coverage-031.json').read_text())
raw=(base/'logs/axiom-audit-031.txt').read_text()
found={m[1]:set(x.strip() for x in m[2].split(',') if x.strip()) for m in re.finditer(r"'(.+?)' depends on axioms: \[([^\]]*)\]",raw)}
found.update({m[1]:set() for m in re.finditer(r"'(.+?)' does not depend on any axioms",raw)})
names=[d for row in coverage['modules'] for d in row['declarations']]
assert len(names)==len(set(names))==coverage['total']
for name in names:
    assert name in found,name
    assert found[name]<={'propext','Classical.choice','Quot.sound'},(name,found[name])
print('PASS complete axiom coverage: '+str(coverage['production_count'])+' production ('+str(coverage['new_production_count'])+' new) and '+str(coverage['calibration_count'])+' calibration declarations.')
print('PASS no sorryAx dependencies; only standard logical axioms occur.')
header='/-\nCopyright (c) 2026 D. and Wise Wolf. All rights reserved.\nReleased under MIT license as described in the file LICENSE.\nAuthors: D. and Wise Wolf.\n-/\n\n'
leanfiles=[r['file'] for r in coverage['modules']]+['DkMathTest/NumberTheory/GnomonCofactorSieveAxiomAudit.lean','DkMath/NumberTheory/Legendre.lean']
for name in leanfiles:
    s=(root/name).read_text()
    assert s.startswith(header),name
    marker='#print "file: '+name[:-5].replace('/','.')+'"'
    assert marker in s,name
    assert s[s.rfind('import ',0,s.index(marker)):s.index(marker)].strip().count('\n')==0,name
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b',s),name
    assert not re.search(r'^import DkMath\.RH',s,re.M),name
    assert all(t==t.rstrip() for t in s.splitlines()),name
    p=subprocess.run(['git','diff','--no-index','--check','/dev/null',str(root/name)],capture_output=True,text=True)
    assert not p.stdout and not p.stderr,(name,p.stdout,p.stderr)
production=(root/'DkMath/NumberTheory/Legendre/GnomonCofactorSieve.lean').read_text()
assert re.findall(r'^import (.+)$',production,re.M)==['DkMath.NumberTheory.Legendre.GnomonCofactorWindow','DkMath.NumberTheory.PrimorialUniverse.WheelSurvivor']
subprocess.run(['git','diff','--check'],cwd=root,check=True)
print('PASS forbidden constructs, production RH firewall, unified headers, immediate file markers and whitespace checks in '+str(len(leanfiles))+' affected Lean files.')
for label in ['focused','facade','root','axiom-audit']:
    log=(base/f'logs/{label}-031.txt').read_text()
    record=json.loads((base/f'logs/performance-{label}-031.json').read_text())
    assert record['exit_code']==0 and record['LEAN_NUM_THREADS']==2,label
    for key in ['maximum_resident_set_kbytes','major_page_faults','minor_page_faults','swap_count']:assert isinstance(record[key],int) and record[key]>=0
    assert record['maximum_resident_set_kbytes']>0
    assert record['failure_classification']=='none'
    telemetry=(base/f'logs/telemetry-{label}-031.txt').read_text()
    assert 'Exit status: 0' in telemetry and 'Maximum resident set size (kbytes)' in telemetry
    metric_labels={'maximum_resident_set_kbytes':'Maximum resident set size (kbytes)','major_page_faults':'Major (requiring I/O) page faults','minor_page_faults':'Minor (reclaiming a frame) page faults','swap_count':'Swaps'}
    for key,text in metric_labels.items():assert int(re.search(re.escape(text)+r':\s*(\d+)',telemetry)[1])==record[key]
    assert 'Build completed successfully' in log and not re.search(r'^error:',log,re.M),label
    warnings=re.findall(r'^warning:.*$',log,re.M)
    if label in ['focused','axiom-audit']:assert not warnings,label
    if label=='facade':assert all('DkMath/NumberTheory/Legendre/PacketCross.lean:285:' in w for w in warnings),warnings
print('PASS focused, Legendre facade, DkMath root and complete axiom builds with LEAN_NUM_THREADS=2.')

import hashlib
source=base/'logs/diagnostics-030.json'
data=json.loads((base/'logs/diagnostics-031.json').read_text())
summary=data['summary'];rows=data['rows']
assert summary['source_sha256']==hashlib.sha256(source.read_bytes()).hexdigest()
assert summary['source_sha256']=='767cd331861dff9bdb746db546e0fb16f5a2fda42dd0a3b658ccc6c80c4d0927'
assert [r['n'] for r in rows]==list(range(3,5001))
assert summary['first_surviving_composite']==dict(n=9,k=2,q=49,least_divisor=7)
assert summary['first_consumer_failure_approx']['n']==29
assert summary['passing_anchors_approx']==list(range(3,29))+[30,33]
assert summary['passing_count']==28 and summary['failure_count']==4970
assert summary['raw_above_geometric_anchors_approx']==[]
assert abs(summary['minimum_gain_over_030_approx'])<1e-6
assert summary['minimum_gain_after3_approx']>0
old={r['n']:r for r in json.loads(source.read_text())['rows']}
for r in rows:
    Q=r['singleton_mass_approx'];V=r['raw_sieve_mass_approx'];G=r['geometric_budget_approx'];W=r['sieve_budget_approx'];E=r['raw_composite_error_approx']
    assert r['basis']==[2,3,5] and r['modulus']==30
    assert r['survivor_count']>=r['prime_count']==old[r['n']]['singleton_count']
    assert r['composite_count']==r['survivor_count']-r['prime_count']
    assert E>=-1e-6 and G-W>=-1e-6
    for a,b in [(V-Q,E),(W,min(G,V)),(W-Q,min(G-Q,E)),(G-W,r['gain_over_030_approx']),(r['log_cell_approx']-r['old_budget_approx']-(W-Q),r['consumer_margin_approx'])]:assert abs(a-b)<1e-6
anchors={r['n']:r for r in data['anchors']}
for n,r in anchors.items():
    primes=[];composites=[];allqs=[]
    for w in r['windows']:
        k=w['k'];A=w['A'];B=w['B']
        assert A==max(n*n//k,2*n) and B==(n*n+2*n)//k
        qs=[q for q in range(A+1,B+1) if math.gcd(q,30)==1]
        assert qs==w['survivors'];allqs.extend(qs)
        cs=[]
        for q in qs:
            d=next((d for d in range(2,math.isqrt(q)+1) if q%d==0),None)
            if d:cs.append([q,d]);composites.append(q)
            else:primes.append(q)
        assert cs==w['composites']
        for M,v in w['alternatives'].items():
            M=int(M);assert {6:3,30:5,210:7,2310:11}[M]<=2*n
            aq=[q for q in range(A+1,B+1) if math.gcd(q,M)==1]
            assert len(aq)==v['count']
            assert abs(math.fsum(math.log(q) for q in aq)-v['weight_approx'])<1e-6
    assert len(primes)==len(set(primes))==r['prime_count']
    assert len(composites)==r['composite_count']
    assert abs(math.fsum(map(math.log,allqs))-r['raw_sieve_mass_approx'])<1e-6
    assert abs(math.fsum(map(math.log,composites))-r['raw_composite_error_approx'])<1e-6
assert math.prod(q for w in anchors[7]['windows'] for q in w['survivors'])==290377
assert 675*290377 < 37387265592825 < 675*128290919715
assert abs(anchors[9]['raw_composite_error_approx']-math.log(49))<1e-6
assert any(77 in w['survivors'] for w in anchors[12]['windows'])
r=anchors[29];sieve=math.prod(q for w in r['windows'] for q in w['survivors'])
geo=math.prod(min(math.comb(w['B'],max(w['B']-w['A'],0)),max(1,w['B'])**max((w['B']+1)//2-(w['A']+1)//2,0)) for w in r['windows'])
cell=math.comb(29*29+58,58)
assert cell<9404347421040*sieve and cell<9404347421040*geo
print('PASS source digest, 4998 weighted rows, direct anchor carriers, exact integer obstructions and floating-only margins.')
for name in ['source-inventory-031.md','findings-031.md','report-031.md','validation-031.md']:
    s=(base/name).read_text();s.encode('ascii');assert chr(92) not in s,name
    assert all(t==t.rstrip() for t in s.splitlines()),name
    for target in re.findall(r'\]\(([^)]+)\)',s):
        if '://' not in target and not target.startswith('#'):assert (base/target.split('#')[0]).exists(),(name,target)
assert (base/'report-031.md').read_text().rstrip().endswith('Outcome B - INDEPENDENT FINITE WHEEL BOUND WITH UNCONTROLLED ACCUMULATED ERROR')
for p in (base/'logs').glob('*031*'):
    if p.suffix in ['.txt','.json']:
        s=p.read_text();s.encode('ascii');assert chr(92) not in s,p
print('PASS independent sieve bound, exact error identity, scoped next proposal, Outcome B and parser-safe artifacts.')
