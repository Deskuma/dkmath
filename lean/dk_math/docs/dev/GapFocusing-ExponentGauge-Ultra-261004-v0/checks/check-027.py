"""Audit complete declaration coverage, bounded diagnostic data and build evidence."""
from pathlib import Path
import json,re,subprocess,math
base=Path(__file__).resolve().parent.parent
root=base.parents[2]
coverage=json.loads((base/'logs/declaration-coverage-027.json').read_text())
raw=(base/'logs/axiom-audit-027.txt').read_text()
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
leanfiles=[r['file'] for r in coverage['modules']]+['DkMathTest/NumberTheory/SquareShellReciprocalAxiomAudit.lean']
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
neutral=(root/'DkMath/NumberTheory/OddReciprocal.lean').read_text()
assert not re.search(r'^import .*Legendre|^import .*RH|^import .*LSeries',neutral,re.M)
subprocess.run(['git','diff','--check'],cwd=root,check=True)
print('PASS forbidden constructs, production RH firewall, unified headers, immediate file markers and whitespace checks in '+str(len(leanfiles))+' affected Lean files.')
for label in ['focused','facade','root','axiom-audit']:
    log=(base/f'logs/{label}-027.txt').read_text()
    record=json.loads((base/f'logs/performance-{label}-027.json').read_text())
    assert record['exit_code']==0 and record['LEAN_NUM_THREADS']==2,label
    for key in ['maximum_resident_set_kbytes','major_page_faults','minor_page_faults','swap_count']:assert isinstance(record[key],int) and record[key]>=0
    assert record['maximum_resident_set_kbytes']>0
    assert record['failure_classification']=='none'
    telemetry=(base/f'logs/telemetry-{label}-027.txt').read_text()
    assert 'Exit status: 0' in telemetry and 'Maximum resident set size (kbytes)' in telemetry
    metric_labels={'maximum_resident_set_kbytes':'Maximum resident set size (kbytes)','major_page_faults':'Major (requiring I/O) page faults','minor_page_faults':'Minor (reclaiming a frame) page faults','swap_count':'Swaps'}
    for key,text in metric_labels.items():assert int(re.search(re.escape(text)+r':\s*(\d+)',telemetry)[1])==record[key]
    assert 'Build completed successfully' in log and not re.search(r'^error:',log,re.M),label
    warnings=re.findall(r'^warning:.*$',log,re.M)
    if label in ['focused','axiom-audit']:assert not warnings,label
    if label=='facade':assert all('DkMath/NumberTheory/Legendre/PacketCross.lean:285:' in w for w in warnings),warnings
print('PASS focused, Legendre facade, DkMath root and complete axiom builds with LEAN_NUM_THREADS=2.')
from fractions import Fraction
import hashlib
source=base/'logs/diagnostics-026.json'
old=json.loads(source.read_text())
data=json.loads((base/'logs/diagnostics-027.json').read_text())
rows=data['rows'];summary=data['summary']
assert summary['source_sha256']==hashlib.sha256(source.read_bytes()).hexdigest()
assert [r['n'] for r in rows]==list(range(1,5001))
for r,o in zip(rows,old['rows']):
    n=r['n'];L=((n+1)**2).bit_length()-1
    assert r['top']==n*n+2*n and r['binary_cutoff']==L
    assert r['events']==o['events']
    assert r['occupied_depths']==[e['exponent'] for e in o['events']]
    assert len(r['occupied_depths'])==len(set(r['occupied_depths']))
    odds=list(range(3,L+1,2));assert r['odd_admissible_depths']==odds
    assert set(r['occupied_depths'])<=set(odds)
    rs=sum((Fraction(1,a) for a in odds),Fraction())
    assert Fraction(r['reciprocal_sum_exact'])==rs
    budgets=r['budgets_approx']
    assert abs(budgets['reciprocal']-math.log(r['top'])*float(rs))<1e-10
    assert abs(budgets['log_log']-math.log(r['top'])*math.log(L))<1e-10
    assert budgets['old_log_count']==o['logarithmic_mass_bound_approx']
    assert budgets['theta']==o['theta_approx'] and budgets['cube_candidate']==o['cube_candidate_mass_approx']
    correction=r['higher_correction_approx'];assert correction==o['higher_mass_approx']
    assert r['shell_mass_approx']==o['von_mangoldt_mass_approx']
    for key,v in budgets.items():
        assert r['strict_mass_comparison_approx'][key]==(v<r['shell_mass_approx'])
        ratio=r['correction_over_budget_approx'][key]
        assert ratio==(correction/v if v>0 else None)
    if n>=3:
        assert correction<=budgets['reciprocal']+1e-9
        assert budgets['reciprocal']<=budgets['log_log']+1e-9
        assert budgets['log_log']<=budgets['old_log_count']+1e-9
for key in ['reciprocal','log_log']:
    assert summary['first_new_beats_old'][key]==2
    assert summary['first_new_beats_old_provider_domain'][key]==3
    assert summary['new_not_strictly_below_old'][key]==[1]
    assert summary['conditional_comparison_failures'][key]==[]
assert summary['conditional_comparison_failures']['old_log_count']==[3,5,7,9]
assert [r['n'] for r in summary['anchors']]==[2,3,5,7,9,11,19,29,297,1031,2896]
assert summary['worst_ratio_provider_domain']['reciprocal'][1]==5
assert summary['worst_ratio_provider_domain']['log_log'][1]==5
print('PASS 5000-shell extension, exact rational reciprocal sums, anchored depth patterns, source digest and explicitly diagnostic floating budget comparisons.')
for name in ['source-inventory-027.md','findings-027.md','report-027.md','validation-027.md']:
    s=(base/name).read_text();s.encode('ascii');assert chr(92) not in s,name
    assert all(t==t.rstrip() for t in s.splitlines()),name
    for target in re.findall(r'\]\(([^)]+)\)',s):
        if '://' not in target and not target.startswith('#'):assert (base/target.split('#')[0]).exists(),(name,target)
report=(base/'report-027.md').read_text()
assert 'TELEMETRY_SUMMARY_027' not in report
assert all(f'## {i}.' in report for i in range(1,21))
assert report.rstrip().endswith('Outcome A - ODD-DEPTH RECIPROCAL GAUGE COMPRESSES THE HIGHER CORRECTION')
for p in (base/'logs').glob('*027*'):
    if p.suffix in ['.txt','.json']:
        s=p.read_text();s.encode('ascii');assert chr(92) not in s,p
print('PASS all 20 report answers, next lower-divisor bridge proposal, Outcome A and parser-safe ASCII artifacts.')
