"""Audit complete declaration coverage, bounded diagnostic data and build evidence."""
from pathlib import Path
import json,re,subprocess,math
base=Path(__file__).resolve().parent.parent
root=base.parents[2]
coverage=json.loads((base/'logs/declaration-coverage-028.json').read_text())
raw=(base/'logs/axiom-audit-028.txt').read_text()
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
leanfiles=[r['file'] for r in coverage['modules']]+['DkMathTest/NumberTheory/GnomonDivisorCarryAxiomAudit.lean','DkMath/NumberTheory/Legendre.lean']
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
neutral=(root/'DkMath/NumberTheory/DivisorIncidence.lean').read_text()
assert not re.search(r'^import .*Legendre|^import .*RH|^import .*LSeries',neutral,re.M)
subprocess.run(['git','diff','--check'],cwd=root,check=True)
print('PASS forbidden constructs, production RH firewall, unified headers, immediate file markers and whitespace checks in '+str(len(leanfiles))+' affected Lean files.')
for label in ['focused','facade','root','axiom-audit']:
    log=(base/f'logs/{label}-028.txt').read_text()
    record=json.loads((base/f'logs/performance-{label}-028.json').read_text())
    assert record['exit_code']==0 and record['LEAN_NUM_THREADS']==2,label
    for key in ['maximum_resident_set_kbytes','major_page_faults','minor_page_faults','swap_count']:assert isinstance(record[key],int) and record[key]>=0
    assert record['maximum_resident_set_kbytes']>0
    assert record['failure_classification']=='none'
    telemetry=(base/f'logs/telemetry-{label}-028.txt').read_text()
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
source=json.loads((base/'logs/diagnostics-026.json').read_text())
summary=json.loads((base/'logs/diagnostics-summary-028.json').read_text())
assert summary['limit']==5000
assert summary['data_sha256']==hashlib.sha256((base/'logs/diagnostics-028.jsonl').read_bytes()).hexdigest()
assert summary['first_collision']==dict(n=11,multiple=128,labels=[[32,2,5],[64,2,6]])
anchors={};total=0
for n,line in enumerate((base/'logs/diagnostics-028.jsonl').open(),1):
    r=json.loads(line);o=source['rows'][n-1];b=n*n;w=2*n;t=b+w
    assert r['n']==n and r['base']==b and r['width']==w and r['top']==t
    q=0;events={}
    for delta in r['prime_label_deltas']:
        assert delta>0;q+=delta;events[q]=(q,1)
    for q,p,a in r['higher_labels']:
        assert a>1 and p**a==q and q not in events
        events[q]=(p,a)
    assert len(events)==r['low_event_count']
    for q,(p,a) in events.items():
        assert 1<=q<=b and q<=b%q+w%q and p**a==q
        assert t//q-b//q==w//q+1
    small=[q for q in events if q<=w];large=[q for q in events if w<q]
    assert len(small)==r['small_count'] and len(large)==r['large_count']
    fibers={}
    for q in large:
        m=q*(b//q+1)
        assert b<m<=t and m%q==0 and m+q>t and m-q<=b
        if n>=3:assert b//q+1<n
        fibers.setdefault(m,[]).append(q)
    hist=Counter(map(len,fibers.values()))
    assert sorted(hist.items())==[tuple(x) for x in r['large_fiber_histogram']]
    assert max(hist,default=0)==r['max_large_fiber'] and len(fibers)==r['large_image_count']
    assert all(len({events[q][0] for q in f})==1 for f in fibers.values())
    for k,qs in [('low_mass_approx',events),('small_mass_approx',small),('large_mass_approx',large)]:
        assert abs(r[k]-math.fsum(math.log(events[q][0]) for q in qs))<1e-8
    assert abs(r['shell_VM_approx']-o['von_mangoldt_mass_approx'])<1e-8
    assert abs(r['higher_correction_approx']-o['higher_mass_approx'])<1e-8
    assert r['independent_carrier_equal']
    if n>=3:
        assert r['old_integer_ledger_equal'] and r['central_integer_ledger_equal']
        assert abs(r['old_log_residual_approx'])<1e-8
        assert abs(r['central_log_residual_approx'])<1e-8
    if n in [3,5,11,19,29,297,1031]:anchors[n]=r
    total=n
assert total==5000
assert [r['n'] for r in summary['anchors']]==[3,5,11,19,29,297,1031]
for r in summary['anchors']:
    assert all(r[k]==v for k,v in anchors[r['n']].items())
assert summary['failed_log_log_provider_approx']==[]
print('PASS all 5000 rows, lossless event reconstruction, independent integer ledgers, exact image distributions, and comparison with the inherited 026 shell inventory.')
for name in ['source-inventory-028.md','findings-028.md','report-028.md','validation-028.md']:
    s=(base/name).read_text();s.encode('ascii');assert chr(92) not in s,name
    assert all(t==t.rstrip() for t in s.splitlines()),name
    for target in re.findall(r'\]\(([^)]+)\)',s):
        if '://' not in target and not target.startswith('#'):assert (base/target.split('#')[0]).exists(),(name,target)
report=(base/'report-028.md').read_text()
assert all(f'## {i}.' in report for i in range(1,23))
assert report.rstrip().endswith('Outcome B - BINARY CARRY MASS IS AN EXACT RECOORDINATION OF THE OLD FRONTIER')
for p in (base/'logs').glob('*028*'):
    if p.suffix in ['.txt','.json','.jsonl']:
        s=p.read_text();s.encode('ascii');assert chr(92) not in s,p
print('PASS 22 report answers, exactly one proposed next theorem, Outcome B, and parser-safe artifacts.')
