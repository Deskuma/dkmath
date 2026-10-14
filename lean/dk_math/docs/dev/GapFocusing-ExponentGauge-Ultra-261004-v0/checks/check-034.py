"""Audit complete declaration coverage, bounded diagnostic data and build evidence."""
from pathlib import Path
import json,re,subprocess,math
base=Path(__file__).resolve().parent.parent
root=base.parents[2]
coverage=json.loads((base/'logs/declaration-coverage-034.json').read_text())
raw=(base/'logs/axiom-audit-034.txt').read_text()
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
leanfiles=[r['file'] for r in coverage['modules']]+['DkMathTest/NumberTheory/GnomonCofactorThreePrimeAxiomAudit.lean','DkMath/NumberTheory/Legendre.lean']
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
production=(root/'DkMath/NumberTheory/Legendre/GnomonCofactorThreePrime.lean').read_text()
assert re.findall(r'^import (.+)$',production,re.M)==['DkMath.NumberTheory.Legendre.GnomonCofactorSemiprime','Mathlib.Data.Nat.Factors','Mathlib.Data.List.Sort']
subprocess.run(['git','diff','--check'],cwd=root,check=True)
print('PASS forbidden constructs, production RH firewall, unified headers, immediate file markers and whitespace checks in '+str(len(leanfiles))+' affected Lean files.')
for label in ['focused','facade','root','axiom-audit']:
    log=(base/f'logs/{label}-034.txt').read_text()
    record=json.loads((base/f'logs/performance-{label}-034.json').read_text())
    assert record['exit_code']==0 and record['LEAN_NUM_THREADS']==2,label
    for key in ['maximum_resident_set_kbytes','major_page_faults','minor_page_faults','swap_count']:assert isinstance(record[key],int) and record[key]>=0
    assert record['maximum_resident_set_kbytes']>0
    assert record['failure_classification']=='none'
    telemetry=(base/f'logs/telemetry-{label}-034.txt').read_text()
    assert 'Exit status: 0' in telemetry and 'Maximum resident set size (kbytes)' in telemetry
    metric_labels={'maximum_resident_set_kbytes':'Maximum resident set size (kbytes)','major_page_faults':'Major (requiring I/O) page faults','minor_page_faults':'Minor (reclaiming a frame) page faults','swap_count':'Swaps'}
    for key,text in metric_labels.items():assert int(re.search(re.escape(text)+r':\s*(\d+)',telemetry)[1])==record[key]
    assert 'Build completed successfully' in log and not re.search(r'^error:',log,re.M),label
    warnings=re.findall(r'^warning:.*$',log,re.M)
    if label in ['focused','axiom-audit']:assert not warnings,label
    if label=='facade':assert all('DkMath/NumberTheory/Legendre/PacketCross.lean:285:' in w for w in warnings),warnings
print('PASS focused, Legendre facade, DkMath root and complete axiom builds with LEAN_NUM_THREADS=2.')

import hashlib
source=base/'logs/diagnostics-033.json';wheel_source=base/'logs/diagnostics-031.json'
data=json.loads((base/'logs/diagnostics-034.json').read_text());summary=data['summary']
assert summary['source_sha256']==hashlib.sha256(source.read_bytes()).hexdigest()=='738d1f27965e44850bd337958ef3989026b44abc04afd60023086464ff036e61'
assert summary['wheel_source_sha256']==hashlib.sha256(wheel_source.read_bytes()).hexdigest()=='bf987dd0909a4149a05e00dec4d9c5121ead0ca2cf8b08db7b8987b41a0f328d'
assert [r['n'] for r in data['rows']]==list(range(3,301))+[1031,5000]
assert summary['first_sampled_consumer_failure_approx']==5000
previous={r['n']:r for r in json.loads(source.read_text())['rows']}
wheel={r['n']:r for r in json.loads(wheel_source.read_text())['rows']}
for r in data['rows']:
    p=wheel[r['n']];s=previous[r['n']];E=r['error_approx'];D=r['semiprime_mass_approx'];T=r['triple_mass_approx'];D3=r['combined_mass_approx'];Z=r['corrected_budget_approx']
    assert 0<=T and D<=D3+1e-6 and D3<=E+1e-6
    assert r['semiprime_count']+r['triple_count']<=r['composite_count']==p['composite_count']
    for a,b in [(D,s['semiprime_mass_approx']),(E,p['raw_composite_error_approx']),(D+T,D3),(E-D3,r['remaining_error_approx']),(Z,min(s['corrected_budget_approx'],p['raw_sieve_mass_approx']-D3)),(s['corrected_budget_approx']-Z,r['improvement_over033_approx']),(p['log_cell_approx']-p['old_budget_approx']-(Z-p['singleton_mass_approx']),r['consumer_margin_approx'])]:assert abs(a-b)<1e-6
    assert Z>=p['singleton_mass_approx']-1e-6 and Z<=s['corrected_budget_approx']+1e-6
assert summary['passing_anchors_approx']==list(range(3,301))+[1031]
anchors={r['n']:r for r in data['anchors']}
for n,r in anchors.items():
    masses=[];count=0
    for w in r['windows']:
        k=w['k'];A=max(n*n//k,2*n);B=(n*n+2*n)//k
        assert (A,B)==(w['A'],w['B'])
        isprime=lambda p: p>=2 and all(p%d for d in range(2,math.isqrt(p)+1))
        ps=[p for p in range(2,math.isqrt(B)+1) if isprime(p) and math.gcd(p,30)==1]
        triples=[[p,s,t] for p in ps if p**3<=B for s in ps if p<=s and s*s<=B//p
            for t in range(max(s,A//(p*s)+1),B//(p*s)+1) if isprime(t) and math.gcd(t,30)==1]
        assert triples==w['triples']
        products=[p*s*t for p,s,t in triples]
        assert products==w['triple_products'] and len(products)==len(set(products))
        assert not set(products)&set(w['semiprime_products'])
        assert set(products)<=set(q for q,_,_ in w['canonical'])
        for p,s,t in triples:assert p<=s<=t and A<p*s*t<=B and not isprime(p*s*t)
        masses.extend(map(math.log,products));count+=len(products)
    assert count==r['triple_count']
    assert abs(math.fsum(masses)-r['triple_mass_approx'])<1e-6
for n in [9,12,31,32]:assert abs(anchors[n]['remaining_error_approx'])<1e-6
assert abs(anchors[32]['triple_mass_approx']-math.log(343*539))<1e-6
assert abs(anchors[69]['remaining_error_approx']-math.log(2401))<1e-6
for n in [210,297,1031]:assert anchors[n]['consumer_margin_approx']>0 and previous[n]['consumer_margin_approx']<0
assert anchors[5000]['consumer_margin_approx']<0
print('PASS 300 endpoint rows, independent ordered triples, repeated factors, product injection, pair/triple disjointness, source digests and floating-only margins.')
for name in ['source-inventory-034.md','findings-034.md','report-034.md','validation-034.md']:
    s=(base/name).read_text();s.encode('ascii');assert chr(92) not in s,name
    assert all(t==t.rstrip() for t in s.splitlines()),name
    for target in re.findall(r'\]\(([^)]+)\)',s):
        if '://' not in target and not target.startswith('#'):assert (base/target.split('#')[0]).exists(),(name,target)
assert (base/'report-034.md').read_text().rstrip().endswith('Outcome B - THREE-PRIME CORRECTION WITH A FACTOR-DEPTH STOPPING BOUNDARY')
for p in (base/'logs').glob('*034*'):
    if p.suffix in ['.txt','.json']:
        s=p.read_text();s.encode('ascii');assert chr(92) not in s,p
print('PASS combined lower mass, exact ledger excess, stopping decision, Outcome B and parser-safe artifacts.')
