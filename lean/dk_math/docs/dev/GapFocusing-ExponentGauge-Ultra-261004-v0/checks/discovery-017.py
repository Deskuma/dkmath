"""All natural anchors 1..300 and 1031: distinguish least owners from shared support."""
from pathlib import Path
from math import isqrt, gcd
from collections import Counter
import json

base=Path(__file__).resolve().parent.parent
previous=json.loads((base/'logs/discovery-016.json').read_text())
previous_rows={r['n']:r for r in previous['rows']+[previous['calibration1031']]}
primes=[p for p in range(2,2101) if all(p%q for q in range(2,isqrt(p)+1))]

def factors(x):
    fs=[]
    for p in primes:
        if p*p>x:break
        if x%p==0:
            k=0
            while x%p==0:x//=p;k+=1
            fs.append((p,k))
    if x>1:fs.append((x,1))
    return fs

first_shared=None
first_divisor_owner_rule=None
first_translation=None
rows=[]
for n in list(range(1,301))+[1031]:
    norm=n*n+(n+1)**2
    norm_fs=factors(norm)
    capacities={p:(0 if p==2 else (n+(p-1)//2)//p) for p in primes if p<=n}
    common_by_prime=Counter(); same_by_prime=Counter()
    both,one,neither,same_total,different_total=0,0,0,0,0
    shared=[]; forced=[]; coloring=[]
    for j in range(n):
        left=n-j;right=n+1+j;gap=2*j+1
        lf=factors(n*n+left);rf=factors(n*n+right)
        lo=lf[0][0];ro=rf[0][0]
        lc=lo<=n;rc=ro<=n
        lsup={p for p,k in lf if p<=n};rsup={p for p,k in rf if p<=n}
        common=sorted(lsup&rsup)
        same_total+=lo==ro;different_total+=lo!=ro
        if lc and rc:
            both+=1
            if lo==ro:same_by_prime[lo]+=1
        elif lc or rc:one+=1
        else:neither+=1
        coloring.append([j,lo,ro,int(lc)+2*int(rc)])
        for p in common:
            assert gap%p==norm%p==0 and p%4==1
            common_by_prime[p]+=1
        if common:
            event=dict(n=n,j=j,left_point=n*n+left,right_point=n*n+right,gap=gap,
                       left_owner=lo,right_owner=ro,common=common)
            shared.append(event)
            if first_shared is None:first_shared=event
        if gap in primes and gap>n:
            assert not common and lo!=ro
            forced.append(dict(j=j,gap=gap,covered_both=lc and rc,left_owner=lo,right_owner=ro))
        if lc and rc and gap%lo==0 and lo!=ro and first_divisor_owner_rule is None:
            first_divisor_owner_rule=dict(n=n,j=j,left_point=n*n+left,right_point=n*n+right,
                                         gap=gap,left_owner=lo,right_owner=ro)
        assert left+right==2*n+1
        assert (n+1)**2 + (2*(n+1)+1-(left if left<n+1 else left+1)) == (n+1)**2+(right+1)+1
    assert same_total==0 and different_total==n and not same_by_prime
    assert both+one+neither==n
    if n>=2:
        assert neither==0 and one==previous_rows[n]['escaping_card']
    for p,c in capacities.items():
        expected=c if norm%p==0 else 0
        assert common_by_prime[p]==expected
    assert gcd(norm,(n+1)**2+(n+2)**2)==1
    total=sum(capacities.values())
    rows.append(dict(n=n,pair_count=n,same_owner_all=same_total,different_owner_all=different_total,
                     same_owner_covered=sum(same_by_prime.values()),different_owner_covered=both,
                     one_covered=one,neither_covered=neither,same_owner_by_prime=dict(same_by_prime),
                     same_owner_gaps=[],capacities=capacities,capacity_sum=total,
                     same_capacity_ratio=None if total==0 else [0,total],norm=norm,norm_factors=norm_fs,
                     common_support_by_prime=dict(sorted(common_by_prime.items())),common_pairs=shared,
                     common_support_incidence=sum(common_by_prime.values()),forced_prime_gap_pairs=forced,
                     coloring_columns=['j','left_owner','right_owner','cover_code_left1_right2'],coloring=coloring,
                     instruction016_survivors=previous_rows[n]['projected_survivors']))
    if first_translation is None:
        for m in range(n*n-n+1,n*n+n+1):
            for p in primes:
                if p>n:break
                if (m%p==0)!=((m+n)%p==0):
                    first_translation=dict(n=n,m=m,p=p,translated=m+n)
                    break
            if first_translation is not None:break
assert first_shared==dict(n=6,j=2,left_point=40,right_point=45,gap=5,left_owner=2,right_owner=3,common=[5])
assert first_divisor_owner_rule==dict(n=8,j=7,left_point=65,right_point=80,gap=15,left_owner=5,right_owner=2)
assert first_translation==dict(n=3,m=7,p=2,translated=10)
result=dict(range=[1,300],anchor_count=300,extra_anchors=[1031],rows=rows,
            smallest_shared_support=first_shared,smallest_false_gap_owner_rule=first_divisor_owner_rule,
            smallest_false_translation_rule=first_translation,
            near_misses=[r for r in rows if r['n'] in [5,8,11,19,29,297,1031]])
(base/'logs/discovery-017.json').write_text(json.dumps(result,indent=2)+'\n')
for r in result['near_misses']:
    print(json.dumps({k:r[k] for k in ['n','pair_count','same_owner_covered','different_owner_covered','one_covered',
                                      'capacity_sum','common_support_incidence','norm','norm_factors','common_support_by_prime']}))
print('smallest shared support:',first_shared)
print('smallest false gap-owner rule:',first_divisor_owner_rule)
print('smallest false translation rule:',first_translation)
