"""Exact prime-only floor pulse and one global target-capacity experiment."""
from pathlib import Path
import math,json,hashlib,time,bisect
base=Path(__file__).resolve().parent.parent;start=time.monotonic()
source=base/'logs/diagnostics-040.json';old=json.loads(source.read_text())
source31=base/'logs/diagnostics-031.json'
old31={r['n']:r for r in json.loads(source31.read_text())['rows']}
limit=max(r['n']**2 for r in old['rows'])
sieve=bytearray([1])*(limit+1);sieve[:2]=bytes(2)
for p in range(2,math.isqrt(limit)+1):
    if sieve[p]:sieve[p*p:limit+1:p]=bytes((limit-p*p)//p+1)
primes=[p for p in range(2,limit+1) if sieve[p]]
rows=[];anchors=[];anchor_set={32,69,210,297,1031,2896,5000}
for r in old['rows']:
    n=r['n'];N=n*n;w=2*n;top=N+w
    # Primality is used only to calibrate exact Q, never to select the proposed U_Q.
    labels=[]
    for p in primes[bisect.bisect_right(primes,w):bisect.bisect_right(primes,N)]:
        pulse=top//p-N//p
        assert pulse in (0,1)
        if pulse:labels.append(p)
    ks=[N//p+1 for p in labels];targets=[p*k for p,k in zip(labels,ks)]
    assert len(targets)==len(set(targets))
    assert all(N<y<=top for y in targets)
    assert all(2<=k<n for k in ks)
    Q=math.fsum(math.log(p) for p in labels)
    assert abs(Q-r['singleton_approx'])<1e-6
    U=math.fsum(math.log(y)-math.log(2) for y in range(N+1,top+1))
    penalty=math.lgamma(w+1)-w*math.log(2)
    B=r['budget040_approx'];cell=r['log_cell_approx'];M=cell-B
    assert abs(U-cell-penalty)<1e-5
    assert Q<=U+1e-7 and U>=cell-1e-7
    margin=cell-U-B
    s=old31[n]
    row=dict(n=n,exact_Q_approx=Q,proposed_U_Q_approx=U,B040_approx=B,
        log_cell_approx=cell,available_M040_approx=M,target_capacity_margin_approx=margin,
        exact_Q_margin_approx=cell-Q-B,normalization_penalty_approx=penalty,
        Q_label_count=len(labels),shell_target_capacity=w,
        old030_Q_envelope_approx=s['geometric_budget_approx'],
        old031_Q_envelope_approx=s['sieve_budget_approx'],
        U_over_available_ratio_approx=U/M,
        saving_against030_approx=s['geometric_budget_approx']-U,
        saving_against031_approx=s['sieve_budget_approx']-U)
    rows.append(row)
    if n in anchor_set:
        pairs=list(zip(labels,ks,targets))
        assert math.prod(labels)*math.prod(ks)==math.prod(targets)
        # Direct quotient-window reconstruction cross-checks the floor-pulse inventory.
        windows=[p for k in range(2,n) for p in range(max(N//k,w)+1,top//k+1) if sieve[p]]
        assert sorted(windows)==labels
        anchors.append(dict(row,target_cofactor_product_checked=True,
            quotient_window_inventory_checked=True,
            incidence_sha256=hashlib.sha256(json.dumps(pairs,separators=(',',':')).encode()).hexdigest(),
            first_incidence_triples=pairs[:10],last_incidence_triples=pairs[-10:]))
summary=dict(sample_count=len(rows),range=[3,300],additional_anchors=[1031,2896,5000],
    required_anchors=sorted(anchor_set),source040_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
    source031_sha256=hashlib.sha256(source31.read_bytes()).hexdigest(),
    passing_target_capacity_count=sum(r['target_capacity_margin_approx']>0 for r in rows),
    first_capacity_failure=rows[0],worst_available_ratio=max(rows,key=lambda r:r['U_over_available_ratio_approx']),
    capacity_below030_count=sum(r['saving_against030_approx']>0 for r in rows),
    capacity_below031_count=sum(r['saving_against031_approx']>0 for r in rows),
    elapsed_seconds=round(time.monotonic()-start,3),
    scope='Exact prime-only floor pulses, integer target injection and selected products checked; U_Q uses every shell integer and cofactor lower bound 2, no prime filter. Logs and margins are floating diagnostics, never Lean premises. The failure of this envelope for all n>=3 is independently kernel checked.')
(base/'logs/diagnostics-042.json').write_text(json.dumps(dict(summary=summary,rows=rows,anchors=anchors),indent=2)+'\n')
print(json.dumps(summary,indent=2))
for r in rows:
    if r['n'] in anchor_set:print(json.dumps(r))
