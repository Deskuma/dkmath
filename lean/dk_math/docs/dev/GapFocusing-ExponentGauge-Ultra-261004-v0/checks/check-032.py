"""Audit complete declaration coverage, bounded diagnostic data and build evidence."""
from pathlib import Path
import json,re,subprocess,math
base=Path(__file__).resolve().parent.parent
root=base.parents[2]
coverage=json.loads((base/'logs/declaration-coverage-032.json').read_text())
raw=(base/'logs/axiom-audit-032.txt').read_text()
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
leanfiles=[r['file'] for r in coverage['modules']]+['DkMathTest/NumberTheory/GnomonCofactorLeastFactorAxiomAudit.lean','DkMath/NumberTheory/Legendre.lean']
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
production=(root/'DkMath/NumberTheory/Legendre/GnomonCofactorLeastFactor.lean').read_text()
assert re.findall(r'^import (.+)$',production,re.M)==['DkMath.NumberTheory.Legendre.GnomonCofactorSieve']
subprocess.run(['git','diff','--check'],cwd=root,check=True)
print('PASS forbidden constructs, production RH firewall, unified headers, immediate file markers and whitespace checks in '+str(len(leanfiles))+' affected Lean files.')
for label in ['focused','facade','root','axiom-audit']:
    log=(base/f'logs/{label}-032.txt').read_text()
    record=json.loads((base/f'logs/performance-{label}-032.json').read_text())
    assert record['exit_code']==0 and record['LEAN_NUM_THREADS']==2,label
    for key in ['maximum_resident_set_kbytes','major_page_faults','minor_page_faults','swap_count']:assert isinstance(record[key],int) and record[key]>=0
    assert record['maximum_resident_set_kbytes']>0
    assert record['failure_classification']=='none'
    telemetry=(base/f'logs/telemetry-{label}-032.txt').read_text()
    assert 'Exit status: 0' in telemetry and 'Maximum resident set size (kbytes)' in telemetry
    metric_labels={'maximum_resident_set_kbytes':'Maximum resident set size (kbytes)','major_page_faults':'Major (requiring I/O) page faults','minor_page_faults':'Minor (reclaiming a frame) page faults','swap_count':'Swaps'}
    for key,text in metric_labels.items():assert int(re.search(re.escape(text)+r':\s*(\d+)',telemetry)[1])==record[key]
    assert 'Build completed successfully' in log and not re.search(r'^error:',log,re.M),label
    warnings=re.findall(r'^warning:.*$',log,re.M)
    if label in ['focused','axiom-audit']:assert not warnings,label
    if label=='facade':assert all('DkMath/NumberTheory/Legendre/PacketCross.lean:285:' in w for w in warnings),warnings
print('PASS focused, Legendre facade, DkMath root and complete axiom builds with LEAN_NUM_THREADS=2.')

import hashlib
source=base/'logs/diagnostics-031.json'
data=json.loads((base/'logs/diagnostics-032.json').read_text());summary=data['summary']
assert summary['source_sha256']==hashlib.sha256(source.read_bytes()).hexdigest()
assert summary['source_sha256']=='bf987dd0909a4149a05e00dec4d9c5121ead0ca2cf8b08db7b8987b41a0f328d'
assert summary['range']==[3,300] and summary['additional_anchors']==[1031,5000]
assert [r['n'] for r in data['rows']]==list(range(3,301))+[1031,5000]
assert summary['first_duplicate']==dict(n=32,k=2,q=539,pairs=[[7,77],[11,49]])
assert summary['first_corrected_consumer_failure_approx']==31
assert summary['passing_anchors_approx']==list(range(3,31))+[32,33]
old={r['n']:r for r in json.loads(source.read_text())['rows']}
for r in data['rows']:
    p=old[r['n']];E=r['error_approx'];F=r['factor_pair_budget_approx'];L=r['square_lower_mass_approx'];U=r['corrected_budget_approx']
    assert r['pair_count']>=r['composite_count']==p['composite_count']
    assert F>=E-1e-6 and 0<=L<=E+1e-6
    for a,b in [(E,p['raw_composite_error_approx']),(F-E,r['cover_excess_approx']),(E-L,r['remaining_error_approx']),(U,min(p['sieve_budget_approx'],p['raw_sieve_mass_approx']-L)),(p['sieve_budget_approx']-U,r['improvement_over031_approx']),(p['log_cell_approx']-p['old_budget_approx']-(U-p['singleton_mass_approx']),r['consumer_margin_approx'])]:assert abs(a-b)<1e-6
    assert U>=p['singleton_mass_approx']-1e-6
anchors={r['n']:r for r in data['anchors']}
for n,r in anchors.items():
    canonical=[];pairs=[];squares=[]
    for w in r['windows']:
        k=w['k'];A=max(n*n//k,2*n);B=(n*n+2*n)//k
        assert (A,B)==(w['A'],w['B'])
        ps=[p for p in range(2,math.isqrt(B)+1) if all(p%d for d in range(2,math.isqrt(p)+1)) and math.gcd(p,30)==1]
        independent=[[p,m] for p in ps for m in range(max(p,A//p+1),B//p+1) if math.gcd(m,30)==1]
        assert independent==w['pairs']
        qs=[q for q in range(A+1,B+1) if math.gcd(q,30)==1]
        cs=[]
        for q in qs:
            fac=next((p for p in range(2,math.isqrt(q)+1) if q%p==0),None)
            if fac:cs.append([q,fac,q//fac])
        assert cs==w['canonical']
        assert w['squares']==[p*m for p,m in independent if p==m]
        for q,p,m in cs:
            assert q==p*m and p<=m and p*p<=B and A//p<m<=B//p
            assert [p,m] in independent
            assert math.gcd(p,30)==math.gcd(m,30)==1
            assert all(m%a for a in range(2,p))
        canonical.extend(cs);pairs.extend(independent);squares.extend(w['squares'])
    assert len(pairs)==r['pair_count'] and len(canonical)==r['composite_count']
    assert abs(math.fsum(math.log(p*m) for p,m in pairs)-r['factor_pair_budget_approx'])<1e-6
    assert abs(math.fsum(math.log(q) for q in squares)-r['square_lower_mass_approx'])<1e-6
assert abs(anchors[9]['error_approx']-math.log(49))<1e-6
assert abs(anchors[12]['remaining_error_approx']-math.log(77))<1e-6
assert abs(anchors[32]['cover_excess_approx']-math.log(539))<1e-6
assert abs(anchors[29]['square_lower_mass_approx']-math.log(289*169*121))<1e-6
print('PASS 300 independent factor-pair rows, canonical routing, square witnesses, duplicate obstruction, source digest and floating-only margins.')
for name in ['source-inventory-032.md','findings-032.md','report-032.md','validation-032.md']:
    s=(base/name).read_text();s.encode('ascii');assert chr(92) not in s,name
    assert all(t==t.rstrip() for t in s.splitlines()),name
    for target in re.findall(r'\]\(([^)]+)\)',s):
        if '://' not in target and not target.startswith('#'):assert (base/target.split('#')[0]).exists(),(name,target)
assert (base/'report-032.md').read_text().rstrip().endswith('Outcome B - FACTOR-PAIR ERROR BOUND AND CERTIFIED SQUARE DELETION WITHOUT GLOBAL CLOSURE')
for p in (base/'logs').glob('*032*'):
    if p.suffix in ['.txt','.json']:
        s=p.read_text();s.encode('ascii');assert chr(92) not in s,p
print('PASS error-bound orientation, independent square correction, scoped frontier, Outcome B and parser-safe artifacts.')
