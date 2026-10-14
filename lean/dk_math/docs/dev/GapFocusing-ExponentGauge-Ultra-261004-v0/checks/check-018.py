"""Complete declaration, trust, diagnostics, build-evidence and ASCII report audit."""
from pathlib import Path
from math import gcd, isqrt
import json
import re
import subprocess
import sys

base=Path(__file__).resolve().parent.parent
root=base.parents[2]
prod=['DkMath/NumberTheory/Legendre/'+name+'.lean' for name in ['CenteredFoldSupportNorm','CenteredFoldGcdAggregate']]
tests=['DkMathTest/NumberTheory/LegendreFoldGcdRegression.lean']
audit=root/'DkMathTest/NumberTheory/LegendreFoldGcdAxiomAudit.lean'
header='''/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

'''
pattern=r'^(?:@\[[^\]]+\]\s+)?(?:noncomputable )?(def|theorem|lemma|abbrev) (\w+)(?=\s*[:({])'
records=[]
for path in prod+tests:
    previous=subprocess.run(['git','show','HEAD:lean/dk_math/'+path],cwd=root,capture_output=True,text=True)
    old_names={m[2] for m in re.finditer(pattern,previous.stdout,re.M)} if previous.returncode==0 else set()
    namespace=''
    for number,line in enumerate((root/path).read_text().splitlines(),1):
        if line.startswith('namespace '): namespace=line.split()[1]
        m=re.match(pattern,line)
        if m: records.append(dict(name=namespace+'.'+m[2],kind=m[1],file=path,line=number,new=m[2] not in old_names))
manifest=base/'logs/declaration-coverage-018.json'
if '--generate' in sys.argv:
    manifest.write_text(json.dumps(records,indent=2)+'\n')
    audit.write_text(header+'''import DkMath.NumberTheory.Legendre
import DkMathTest.NumberTheory.LegendreFoldGcdRegression

#print "file: DkMathTest.NumberTheory.LegendreFoldGcdAxiomAudit"

'''+''.join('#check '+r['name']+'\n#print axioms '+r['name']+'\n' for r in records))
    print(f'Generated {len(records)} audits; new production {sum(r["new"] and r["file"] in prod for r in records)}, new regression {sum(r["new"] and r["file"] in tests for r in records)}.')
    sys.exit(0)
assert json.loads(manifest.read_text())==records
expected={r['name'] for r in records}
assert len(expected)==len(records)
if '--sources-only' not in sys.argv:
    raw=(base/'logs/axiom-audit-018.txt').read_text()
    found={m[1]:set(x.strip() for x in m[2].split(',') if x.strip()) for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]",raw)}
    found.update({m[1]:set() for m in re.finditer(r"'([^']+)' does not depend on any axioms",raw)})
    assert expected<=set(found),expected-set(found)
    for name in expected: assert found[name]<={'propext','Classical.choice','Quot.sound'},(name,found[name])
    print(f'PASS: {len(records)} complete public axiom sets, including all new declarations; no sorryAx or additional axioms.')
written=prod+tests+[str(audit.relative_to(root)),'DkMath/NumberTheory/Legendre.lean']
for path in written:
    source=(root/path).read_text()
    assert source.startswith(header),path
    assert re.search(r'import [^\n]+\n\n#print "file: '+re.escape(path[:-5].replace('/','.'))+r'"',source),path
    if path in prod+tests: assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b',source),path
    assert all(line==line.rstrip() for line in source.splitlines()),path
subprocess.run(['git','diff','--check'],cwd=root,check=True)
for path in written:
    proc=subprocess.run(['git','diff','--no-index','--check','/dev/null',str(root/path)],capture_output=True,text=True)
    assert not proc.stdout and not proc.stderr,(path,proc.stdout,proc.stderr)
print(f'PASS: {len(written)} uniform headers/markers, tracked/untracked whitespace and scoped forbidden tokens.')
for path in prod:
    assert not re.search(r'^import .*?(?:Analysis|Wallis|PadicVal.Basic|CyclotomicField)',(root/path).read_text(),re.M)
d=json.loads((base/'logs/discovery-018.json').read_text())
assert d['range']==[0,300] and d['extra_anchors']==[1031]
assert [r['n'] for r in d['rows']]==list(range(301))+[1031]
for r in d['rows']:
    n=r['n']; norm=r['norm']; nf={int(p):v for p,v in r['norm_factors'].items()}
    gap_v={int(p):v for p,v in r['odd_gap_valuations'].items()}
    visible={int(p):v for p,v in r['aggregate_valuations'].items()}
    local={int(p):v for p,v in r['local_gcd_product_valuations'].items()}
    assert norm==n*n+(n+1)**2
    assert r['odd_gap_prime_support']==[p for p in range(3,2*n,2) if all(p%q for q in range(2,isqrt(p)+1))]
    assert visible=={p:min(v,gap_v.get(p,0)) for p,v in nf.items() if gap_v.get(p,0)}
    assert set(visible)==set(local)
    value=1
    for p,v in visible.items():value*=p**v
    assert value==r['norm_gap_gcd']
    assert len(r['common_gcd_events'])==r['nontrivial_pair_count']
    assert r['visible_old']==[p for p in visible if p<=n]
    assert r['visible_fresh']==[p for p in visible if p>n]
    if n>0:
        assert r['norm_prime']==(value==1)==(r['nontrivial_pair_count']==0)
        assert not r['full_cover']
        if n>=2: assert r['U']==r['escaping_seat_count']
    for event in r['common_gcd_events']:
        j=event['j'];g=event['gcd']
        assert g==gcd(n*n+n-j,n*n+n+1+j)==gcd(norm,2*j+1)>1
        assert all(int(p)%4==1 and int(p)<2*n for p in event['factors'])
assert d['smallest_repeated_prime_gcd']['n']==21 and d['smallest_repeated_prime_gcd']['j']==12
assert d['smallest_aggregate_difference']['n']==8
assert d['smallest_large_gcd_with_old_support']['n']==21
assert d['smallest_covered_coprime_pair']==dict(n=4,j=0,left=20,right=21,gcd=1,norm=41)
r1031=d['rows'][-1]
assert r1031['norm_gap_gcd']==305 and r1031['nontrivial_pair_count']==220
assert r1031['local_gcd_product_valuations']=={'5':206,'61':17}
print('PASS: all natural anchors 0..300 plus 1031, complete prime support, valuations, old/fresh split and bounded counterexamples.')
artifacts=['source-inventory-018.md','findings-018.md']
if '--sources-only' not in sys.argv:
    artifacts+=['report-018.md','validation-018.md']
for name in artifacts:
    source=(base/name).read_text();source.encode('ascii')
    assert '\\' not in source,name
    assert all(line==line.rstrip() for line in source.splitlines()),name
    for target in re.findall(r'\]\(([^)]+)\)',source):
        if '://' not in target and not target.startswith('#'): assert (base/target.split('#')[0]).exists(),(name,target)
if '--sources-only' not in sys.argv:
    report=(base/'report-018.md').read_text()
    assert all(f'## {i}.' in report for i in range(1,15))
    assert report.rstrip().endswith('Outcome B - FOLD GCD AGGREGATE YIELDS A NEW PRIMORIAL OR CYCLOTOMIC BRIDGE')
    assert 'centeredFoldGcdProduct_padicVal_eq_primePowerFloorSum' in report
    for name in ['local-gcd','aggregate','regression','axiom-audit','facade','root']:
        raw=(base/f'logs/{name}-018.txt').read_text()
        assert 'Build completed successfully' in raw and not re.search(r'^error:',raw,re.M),name
    print('PASS: ASCII/no-backslash artifacts, links, fourteen answers, exact next contract, successful builds and Outcome B.')
