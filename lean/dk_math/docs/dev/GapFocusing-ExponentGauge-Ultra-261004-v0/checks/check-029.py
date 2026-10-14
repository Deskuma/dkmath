"""Audit complete declaration coverage, bounded diagnostic data and build evidence."""
from pathlib import Path
import json,re,subprocess,math
base=Path(__file__).resolve().parent.parent
root=base.parents[2]
coverage=json.loads((base/'logs/declaration-coverage-029.json').read_text())
raw=(base/'logs/axiom-audit-029.txt').read_text()
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
leanfiles=[r['file'] for r in coverage['modules']]+['DkMathTest/NumberTheory/GnomonCarryFiberAxiomAudit.lean','DkMath/NumberTheory/Legendre.lean']
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
production=(root/'DkMath/NumberTheory/Legendre/GnomonCarryFiber.lean').read_text()
assert re.findall(r'^import (.+)$',production,re.M)==['DkMath.NumberTheory.Legendre.GnomonDivisorCarry']
subprocess.run(['git','diff','--check'],cwd=root,check=True)
print('PASS forbidden constructs, production RH firewall, unified headers, immediate file markers and whitespace checks in '+str(len(leanfiles))+' affected Lean files.')
for label in ['focused','facade','root','axiom-audit']:
    log=(base/f'logs/{label}-029.txt').read_text()
    record=json.loads((base/f'logs/performance-{label}-029.json').read_text())
    assert record['exit_code']==0 and record['LEAN_NUM_THREADS']==2,label
    for key in ['maximum_resident_set_kbytes','major_page_faults','minor_page_faults','swap_count']:assert isinstance(record[key],int) and record[key]>=0
    assert record['maximum_resident_set_kbytes']>0
    assert record['failure_classification']=='none'
    telemetry=(base/f'logs/telemetry-{label}-029.txt').read_text()
    assert 'Exit status: 0' in telemetry and 'Maximum resident set size (kbytes)' in telemetry
    metric_labels={'maximum_resident_set_kbytes':'Maximum resident set size (kbytes)','major_page_faults':'Major (requiring I/O) page faults','minor_page_faults':'Minor (reclaiming a frame) page faults','swap_count':'Swaps'}
    for key,text in metric_labels.items():assert int(re.search(re.escape(text)+r':\s*(\d+)',telemetry)[1])==record[key]
    assert 'Build completed successfully' in log and not re.search(r'^error:',log,re.M),label
    warnings=re.findall(r'^warning:.*$',log,re.M)
    if label in ['focused','axiom-audit']:assert not warnings,label
    if label=='facade':assert all('DkMath/NumberTheory/Legendre/PacketCross.lean:285:' in w for w in warnings),warnings
print('PASS focused, Legendre facade, DkMath root and complete axiom builds with LEAN_NUM_THREADS=2.')

from collections import Counter
import hashlib
source=base/'logs/diagnostics-028.jsonl'
data=json.loads((base/'logs/diagnostics-029.json').read_text())
summary=data['summary'];rows=data['rows']
assert summary['source_sha256']==hashlib.sha256(source.read_bytes()).hexdigest()
assert [r['n'] for r in rows]==list(range(3,5001))
assert summary['first_mixed_base_without_large_hypothesis']==dict(n=7,y=51,labels=[[3,3,1],[17,17,1]])
assert summary['first_large_collision']==dict(n=11,p=2,y=128,exponents=[5,6])
assert summary['first_cutoff_slack']==dict(n=6,p=2,y=48,exponents=[4],cutoff_card=2,valuation=4)
assert summary['maximum_fiber']==dict(card=10,n=2896,p=2,y=8388608)
assert summary['provider_failures_approx']==[]
index={r['n']:r for r in rows}
for line in source.open():
    old=json.loads(line);n=old['n']
    if n<3:continue
    r=index[n]
    assert r['labels']==old['large_count'] and r['targets']==old['large_image_count']
    assert r['fiber_histogram']==old['large_fiber_histogram']
    assert abs(r['exact_weight_approx']-old['large_mass_approx'])<1e-8
    assert abs(r['cutoff_budget_approx']-r['exact_weight_approx']-r['slack_mass_approx'])<1e-8
    assert r['slack_mass_approx']>=0
    assert abs(r['old_envelope_approx']-r['old_budget_approx']-r['slack_mass_approx'])<1e-8
    assert r['all_exponent_intervals_equal'] and r['independent_divisibility_equal']
    q=0;weights=[]
    for delta in old['prime_label_deltas']:
        q+=delta
        if q>2*n:weights.append(math.log(q))
    assert abs(r['singleton_prime_mass_approx']-math.fsum(weights))<1e-8
    assert abs(r['singleton_prime_fraction_approx']-r['singleton_prime_mass_approx']/r['exact_weight_approx'])<1e-12
    assert abs(r['repeated_power_mass_approx']+r['singleton_prime_mass_approx']-r['exact_weight_approx'])<1e-8
for r in data['anchors']:
    n=r['n'];w=2*n;b=n*n;mass=[];cap=[]
    assert all(r[k]==v for k,v in index[n].items())
    for f in r['fibers']:
        p=f['p'];y=f['y'];L=f['lower'];U=f['old_upper'];v=f['valuation']
        assert p**L<=w<p**(L+1) and p**U<=b<p**(U+1)
        assert y%p**v==0 and y%p**(v+1)!=0
        assert b<y<=b+w
        assert f['exponents']==list(range(L+1,min(U,v)+1))
        assert f['card']==len(f['exponents']) and f['cutoff_card']==U-L
        assert f['slack_card']==f['cutoff_card']-f['card']
        mass.append(f['card']*math.log(p));cap.append(f['cutoff_card']*math.log(p))
    assert abs(math.fsum(mass)-r['exact_weight_approx'])<1e-8
    assert abs(math.fsum(cap)-r['cutoff_budget_approx'])<1e-8
print('PASS 4998 reconstructed same-base fibers rows, exact interval/card checks, inherited carrier digest, singleton weights and explicitly floating budgets.')
for name in ['source-inventory-029.md','findings-029.md','report-029.md','validation-029.md']:
    s=(base/name).read_text();s.encode('ascii');assert chr(92) not in s,name
    assert all(t==t.rstrip() for t in s.splitlines()),name
    for target in re.findall(r'\]\(([^)]+)\)',s):
        if '://' not in target and not target.startswith('#'):assert (base/target.split('#')[0]).exists(),(name,target)
report=(base/'report-029.md').read_text()
assert report.rstrip().endswith('Outcome B - EXACT SAME-BASE FIBERS WITHOUT A UNIVERSAL STRICT BUDGET GAIN')
for p in (base/'logs').glob('*029*'):
    if p.suffix in ['.txt','.json']:
        s=p.read_text();s.encode('ascii');assert chr(92) not in s,p
print('PASS production inventory, hypothesis-sensitive counterexamples, failure analysis, natural next frontier, Outcome B and parser-safe artifacts.')
