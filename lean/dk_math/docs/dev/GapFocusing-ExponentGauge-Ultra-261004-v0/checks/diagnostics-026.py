"""Exact integer event data; natural logarithms are floating approximations."""
from pathlib import Path
import json, math, time
base=Path(__file__).resolve().parent.parent
start=time.monotonic()
limit=5000
cap=(limit+1)**2-1
sieve=bytearray(b"1")*(cap+1)
sieve[0:2]=b"00"
for p in range(2,math.isqrt(cap)+1):
    if sieve[p]==49:
        count=(cap-p*p)//p+1
        sieve[p*p:cap+1:p]=b"0"*count
prime_counts=[0]*(limit+1);birth=[0.0]*(limit+1)
small=[]
for q in range(2,cap+1):
    if sieve[q]!=49:continue
    n=math.isqrt(q)
    if 1<=n<=limit:
        prime_counts[n]+=1;birth[n]+=math.log(q)
    if q<=limit:small.append(q)
events=[[] for _ in range(limit+1)]
for p in range(2,math.isqrt(cap)+1):
    if sieve[p]!=49:continue
    a=3;q=p**a
    while q<=cap:
        n=math.isqrt(q)
        if q!=n*n and n>=1:events[n].append(dict(value=q,base=p,exponent=a))
        a+=2;q*=p*p
rows=[]
theta=0.0;index=0
for n in range(1,limit+1):
    while index<len(small) and small[index]<=n:
        theta+=math.log(small[index]);index+=1
    ev=sorted(events[n],key=lambda e:e['value'])
    higher=sum(math.log(e['base']) for e in ev)
    cube=sum(math.log(p) for p in small if p<=n and p**3<(n+1)**2)
    cutoff=((n+1)**2).bit_length()-1
    bound=(cutoff+1)*math.log(n)
    rows.append(dict(n=n,prime_count=prime_counts[n],higher_count=len(ev),events=ev,
        von_mangoldt_mass_approx=birth[n]+higher,birth_mass_approx=birth[n],
        higher_mass_approx=higher,theta_approx=theta,cube_candidate_mass_approx=cube,
        binary_exponent_cutoff=cutoff,event_count_bound=cutoff+1,
        logarithmic_mass_bound_approx=bound))
nonempty=[r for r in rows if r['higher_count']]
multiple=[r for r in rows if r['higher_count']>1]
summary=dict(range=[1,limit],integer_data='exact sieve and integer powers',
    real_data='floating natural logarithms; diagnostic only',
    max_higher_count=max(r['higher_count'] for r in rows),
    shells_attaining_max=[r['n'] for r in rows if r['higher_count']==max(t['higher_count'] for t in rows)],
    max_exponent=max(e['exponent'] for r in rows for e in r['events']),
    shared_exponent_shells=[r['n'] for r in rows if len({e['exponent'] for e in r['events']})<r['higher_count']],
    shared_base_shells=[r['n'] for r in rows if len({e['base'] for e in r['events']})<r['higher_count']],
    first_higher_shell=nonempty[0],first_multiple_shell=multiple[0] if multiple else None,
    max_higher_over_theta=max((r['higher_mass_approx']/r['theta_approx'],r['n']) for r in nonempty),
    max_higher_over_log_bound=max((r['higher_mass_approx']/r['logarithmic_mass_bound_approx'],r['n']) for r in nonempty),
    max_higher_over_cube_bound=max((r['higher_mass_approx']/r['cube_candidate_mass_approx'],r['n']) for r in nonempty),
    theta_criterion_shells=sum(r['theta_approx']<r['von_mangoldt_mass_approx'] for r in rows if r['n']>=3),
    logarithmic_criterion_shells=sum(r['logarithmic_mass_bound_approx']<r['von_mangoldt_mass_approx'] for r in rows if r['n']>=3),
    anchors=[rows[n-1] for n in [1,2,5,11,19,29,297,1031]],
    elapsed_seconds=time.monotonic()-start)
(base/'logs/diagnostics-026.json').write_text(json.dumps(dict(summary=summary,rows=rows),indent=2)+'\n')
(base/'logs/diagnostics-summary-026.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
