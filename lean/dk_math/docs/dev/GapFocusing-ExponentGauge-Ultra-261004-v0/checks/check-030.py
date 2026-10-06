"""Audit complete declaration coverage, bounded diagnostic data and build evidence."""
from pathlib import Path
import json,re,subprocess,math
base=Path(__file__).resolve().parent.parent
root=base.parents[2]
coverage=json.loads((base/'logs/declaration-coverage-030.json').read_text())
raw=(base/'logs/axiom-audit-030.txt').read_text()
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
leanfiles=[r['file'] for r in coverage['modules']]+['DkMathTest/NumberTheory/GnomonCofactorWindowAxiomAudit.lean','DkMath/NumberTheory/Legendre.lean']
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
production=(root/'DkMath/NumberTheory/Legendre/GnomonCofactorWindow.lean').read_text()
assert re.findall(r'^import (.+)$',production,re.M)==['DkMath.NumberTheory.Legendre.GnomonCarryFiber','Mathlib.Data.Nat.Choose.Dvd']
subprocess.run(['git','diff','--check'],cwd=root,check=True)
print('PASS forbidden constructs, production RH firewall, unified headers, immediate file markers and whitespace checks in '+str(len(leanfiles))+' affected Lean files.')
for label in ['focused','facade','root','axiom-audit']:
    log=(base/f'logs/{label}-030.txt').read_text()
    record=json.loads((base/f'logs/performance-{label}-030.json').read_text())
    assert record['exit_code']==0 and record['LEAN_NUM_THREADS']==2,label
    for key in ['maximum_resident_set_kbytes','major_page_faults','minor_page_faults','swap_count']:assert isinstance(record[key],int) and record[key]>=0
    assert record['maximum_resident_set_kbytes']>0
    assert record['failure_classification']=='none'
    telemetry=(base/f'logs/telemetry-{label}-030.txt').read_text()
    assert 'Exit status: 0' in telemetry and 'Maximum resident set size (kbytes)' in telemetry
    metric_labels={'maximum_resident_set_kbytes':'Maximum resident set size (kbytes)','major_page_faults':'Major (requiring I/O) page faults','minor_page_faults':'Minor (reclaiming a frame) page faults','swap_count':'Swaps'}
    for key,text in metric_labels.items():assert int(re.search(re.escape(text)+r':\s*(\d+)',telemetry)[1])==record[key]
    assert 'Build completed successfully' in log and not re.search(r'^error:',log,re.M),label
    warnings=re.findall(r'^warning:.*$',log,re.M)
    if label in ['focused','axiom-audit']:assert not warnings,label
    if label=='facade':assert all('DkMath/NumberTheory/Legendre/PacketCross.lean:285:' in w for w in warnings),warnings
print('PASS focused, Legendre facade, DkMath root and complete axiom builds with LEAN_NUM_THREADS=2.')

import hashlib
source=base/'logs/diagnostics-028.jsonl'
data=json.loads((base/'logs/diagnostics-030.json').read_text())
summary=data['summary'];rows=data['rows']
assert summary['source_sha256']==hashlib.sha256(source.read_bytes()).hexdigest()
assert summary['fiber_source_sha256']==hashlib.sha256((base/'logs/diagnostics-029.json').read_bytes()).hexdigest()
assert [r['n'] for r in rows]==list(range(3,5001))
assert summary['first_strict_slack_approx']['n']==4
assert summary['first_exact_higher_failure_approx']['n']==7
assert summary['exact_higher_passing_anchors_approx']==[3,4,5,6]
assert summary['loglog_passing_anchors_approx']==[3,4]
assert summary['odd_cardinality_passing_anchors_approx']==[3,4,5,6,8]
assert summary['improvements_over_029_fiber_budget_approx']==[]
assert summary['geometric_passing_anchors_approx']==[3,4,5,6,8]
assert summary['geometric_loglog_passing_anchors_approx']==[3,4,6]
assert summary['geometric_improvements_over_029_fiber_budget_approx']==[]
assert summary['exact_higher_failure_count']==4994 and summary['loglog_failure_count']==4996
index={r['n']:r for r in rows}
for r in rows:
    assert r['independent_pairs_equal_inventory'] and r['prime_projection_injective'] and r['target_projection_injective']
    assert r['binomial_budget_approx']>=r['geometric_budget_approx']-1e-8
    assert r['geometric_budget_approx']>=r['singleton_mass_approx']-1e-8
    assert r['odd_cardinality_budget_approx']>=r['geometric_budget_approx']-1e-8
    assert abs(r['odd_cardinality_budget_approx']-r['geometric_budget_approx'])<1e-8
    assert abs(r['log_cell_approx']-r['small_mass_approx']-r['repeated_mass_approx']-r['higher_mass_approx']-r['geometric_budget_approx']-r['geometric_consumer_margin_approx'])<1e-8
    assert r['repeated_mass_approx']>=-1e-8
    remainder=r['small_mass_approx']+r['repeated_mass_approx']+r['higher_mass_approx']
    assert abs(remainder+r['singleton_mass_approx']-r['exact_old_budget_approx'])<1e-8
    assert abs(r['log_cell_approx']-remainder-r['binomial_budget_approx']-r['exact_higher_consumer_margin_approx'])<1e-8
    assert abs(r['log_cell_approx']-remainder-r['odd_cardinality_budget_approx']-r['odd_cardinality_consumer_margin_approx'])<1e-8
    assert abs(r['binomial_budget_approx']+r['repeated_mass_approx']-r['new_large_envelope_approx'])<1e-8
for r in data['anchors']:
    n=r['n'];b=n*n;w=2*n;t=b+w;ps=[]
    assert all(r[k]==v for k,v in index[n].items())
    for window in r['windows']:
        k=window['k'];A=window['A'];B=window['B'];C=window['length']
        assert A==max(b//k,w) and B==t//k and C==max(B-A,0)
        coefficient=math.comb(B,C)
        for p in window['primes']:
            assert A<p<=B and b<k*p<=t and k==b//p+1 and p<=b
            assert all(p%d for d in range(2,math.isqrt(p)+1))
            assert C<p and coefficient%p==0
        ps.extend(window['primes'])
    assert len(ps)==len(set(ps))==r['singleton_count']
    assert abs(math.fsum(math.log(p) for p in ps)-r['singleton_mass_approx'])<1e-8
    if n in [3,4,7]:
        product=math.prod(math.comb(x['B'],x['length']) for x in r['windows'])
        assert product=={3:7,4:495,7:802638325125}[n]
        assert abs(math.log(product)-r['binomial_budget_approx'])<1e-8
        geometric_product=math.prod(min(math.comb(x['B'],x['length']),max(1,x['B'])**x['odd_count']) for x in r['windows'])
        assert geometric_product=={3:7,4:144,7:128290919715}[n]
        assert abs(math.log(geometric_product)-r['geometric_budget_approx'])<1e-8
assert 37387265592825 < 675*128290919715 == 86596370807625
print('PASS 4998 independent quotient-window rows, inherited source digests, exact carriers, disjointness, integer binomial divisibility and floating-only comparisons.')

for name in ['source-inventory-030.md','findings-030.md','report-030.md','validation-030.md']:
    s=(base/name).read_text();s.encode('ascii');assert chr(92) not in s,name
    assert all(t==t.rstrip() for t in s.splitlines()),name
    for target in re.findall(r'\]\(([^)]+)\)',s):
        if '://' not in target and not target.startswith('#'):assert (base/target.split('#')[0]).exists(),(name,target)
report=(base/'report-030.md').read_text()
assert report.rstrip().endswith('Outcome B - INDEPENDENT FINITE GEOMETRIC BOUND WITHOUT A STRICT BUDGET GAIN')
for p in (base/'logs').glob('*030*'):
    if p.suffix in ['.txt','.json']:
        s=p.read_text();s.encode('ascii');assert chr(92) not in s,p
print('PASS exact bridge, independent bound, first failure, scoped next proposal, Outcome B and parser-safe artifacts.')
