"""Audit complete declaration coverage, bounded diagnostic data and build evidence."""
from pathlib import Path
import json,re,subprocess,math
base=Path(__file__).resolve().parent.parent
root=base.parents[2]
coverage=json.loads((base/'logs/declaration-coverage-026.json').read_text())
raw=(base/'logs/axiom-audit-026.txt').read_text()
found={m[1]:set(x.strip() for x in m[2].split(',') if x.strip()) for m in re.finditer(r"'(.+?)' depends on axioms: \[([^\]]*)\]",raw)}
found.update({m[1]:set() for m in re.finditer(r"'(.+?)' does not depend on any axioms",raw)})
names=[d for row in coverage['modules'] for d in row['declarations']]
assert len(names)==len(set(names))==coverage['total']
for name in names:
    assert name in found,name
    assert found[name]<={'propext','Classical.choice','Quot.sound'},(name,found[name])
print('PASS complete axiom coverage: '+str(coverage['production_count'])+' new production and '+str(coverage['calibration_count'])+' calibration declarations.')
print('PASS no sorryAx dependencies; only standard logical axioms occur.')
header='/-\nCopyright (c) 2026 D. and Wise Wolf. All rights reserved.\nReleased under MIT license as described in the file LICENSE.\nAuthors: D. and Wise Wolf.\n-/\n\n'
leanfiles=[r['file'] for r in coverage['modules']]+['DkMathTest/NumberTheory/SquareShellPrimePowerAxiomAudit.lean','DkMath/NumberTheory/Legendre.lean']
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
subprocess.run(['git','diff','--check'],cwd=root,check=True)
print('PASS forbidden constructs, production RH firewall, unified headers, immediate file markers and whitespace checks in '+str(len(leanfiles))+' affected Lean files.')
for label in ['focused','facade','root','axiom-audit']:
    log=(base/f'logs/{label}-026.txt').read_text()
    record=json.loads((base/f'logs/performance-{label}-026.json').read_text())
    assert record['exit_code']==0 and record['LEAN_NUM_THREADS']==2,label
    assert 'Build completed successfully' in log and not re.search(r'^error:',log,re.M),label
    warnings=re.findall(r'^warning:.*$',log,re.M)
    if label in ['focused','axiom-audit']:assert not warnings,label
    if label=='facade':assert all('DkMath/NumberTheory/Legendre/PacketCross.lean:285:' in w for w in warnings),warnings
print('PASS focused, Legendre facade, DkMath root and complete axiom builds with LEAN_NUM_THREADS=2.')
data=json.loads((base/'logs/diagnostics-026.json').read_text())
rows=data['rows'];summary=data['summary']
assert [r['n'] for r in rows]==list(range(1,5001))
def prime(p):return p>=2 and all(p%d for d in range(2,math.isqrt(p)+1))
expected={n:[] for n in range(1,5001)}
cap=5001**2-1
for p in range(2,math.isqrt(cap)+1):
    if not prime(p):continue
    a=3;q=p**a
    while q<=cap:
        n=math.isqrt(q)
        if q!=n*n:expected[n].append(dict(value=q,base=p,exponent=a))
        a+=2;q*=p*p
for r in rows:
    n=r['n'];ev=r['events']
    assert ev==sorted(expected[n],key=lambda e:e['value']),n
    assert r['higher_count']==len(ev)
    assert len({e['base'] for e in ev})==len(ev)
    assert len({e['exponent'] for e in ev})==len(ev)
    assert len(ev)<=((n+1)**2).bit_length()
    for e in ev:
        q,p,a=e['value'],e['base'],e['exponent']
        assert q==p**a and n*n<q<(n+1)**2 and prime(p) and not prime(q)
        assert a>=3 and a%2==1 and p<=n and p**3<(n+1)**2
        assert a<=((n+1)**2).bit_length()-1
    assert abs(r['von_mangoldt_mass_approx']-r['birth_mass_approx']-r['higher_mass_approx'])<1e-8
    if n>=3:
        assert r['higher_mass_approx']<=r['theta_approx']+1e-8
        assert r['higher_mass_approx']<=r['logarithmic_mass_bound_approx']+1e-8
    assert r['higher_mass_approx']<=r['cube_candidate_mass_approx']+1e-8
assert summary['max_higher_count']==2 and summary['max_exponent']==23
assert summary['shells_attaining_max']==[5,11,46]
assert not summary['shared_exponent_shells'] and not summary['shared_base_shells']
assert summary['first_higher_shell']['n']==2 and summary['first_multiple_shell']['n']==5
assert [r['n'] for r in summary['anchors']]==[1,2,5,11,19,29,297,1031]
print('PASS exact higher-event inventory for 5000 shells, preserved anchors, cutoff and multiplicity summaries; floating mass data checked as diagnostics only.')
for name in ['source-inventory-026.md','findings-026.md','report-026.md','validation-026.md']:
    s=(base/name).read_text();s.encode('ascii');assert chr(92) not in s,name
    assert all(t==t.rstrip() for t in s.splitlines()),name
    for target in re.findall(r'\]\(([^)]+)\)',s):
        if '://' not in target and not target.startswith('#'):assert (base/target.split('#')[0]).exists(),(name,target)
report=(base/'report-026.md').read_text()
assert all(f'## {i}.' in report for i in range(1,22))
assert report.rstrip().endswith('Outcome A - SQUARE-SHELL GAUGE GAP YIELDS A NEW SMALL HIGHER-POWER BUDGET')
for p in (base/'logs').glob('*026*'):
    if p.suffix in ['.txt','.json']:
        s=p.read_text();s.encode('ascii');assert chr(92) not in s,p
print('PASS all 21 report answers, next reciprocal-depth proposal, Outcome A and parser-safe ASCII artifacts.')
