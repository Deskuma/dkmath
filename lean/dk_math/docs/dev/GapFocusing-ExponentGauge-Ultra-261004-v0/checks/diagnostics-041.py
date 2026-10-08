"""Primality-free square-root endpoint envelope, with full exponent weights."""
from pathlib import Path
import math,json,hashlib,time
base=Path(__file__).resolve().parent.parent;start=time.monotonic()
source=base/'logs/diagnostics-040.json';old=json.loads(source.read_text())

def prime(p):return p>=2 and all(p%d for d in range(2,math.isqrt(p)+1))
def block(n,p):
    first=2;d=p*p
    while d<=2*n:first+=1;d*=p
    upper=first-1;c=0
    while d<=n*n:upper+=1;c+=1;d*=p
    return dict(base=p,first_exponent=first,upper_exponent=upper,interval_length=c,
                weight_approx=c*math.log(p),prime=prime(p))
rows=[];anchors=[]
for r in old['rows']:
    n=r['n'];N=n*n;top=N+2*n
    small=[block(n,p) for p in range(2,math.isqrt(2*n)+1) if prime(p) and p<=n]
    windows=[];seen=set()
    for k in range(2,n):
        L=max(math.isqrt(N//k),math.isqrt(2*n))+1
        U=min(n,math.isqrt(top//k))
        if L<=U:
            assert L==U and U not in seen
            seen.add(U)
            assert N<k*U*U<=top and 2*n<U*U
            assert k==N//(U*U)+1
            windows.append(dict(k=k,L=L,U=U,**block(n,U)))
    smallmass=math.fsum(p['weight_approx'] for p in small)
    large=math.fsum(p['weight_approx'] for p in windows)
    R=smallmass+large
    B=r['small_phase_bound_approx']+R+r['higher_reciprocal_approx']
    margin=r['log_cell_approx']-r['singleton_approx']-B
    assert r['repeated_phase_approx']<=R+1e-7
    assert smallmass<=math.isqrt(2*n)*math.log(N)+1e-7
    row=dict(n=n,repeated_exact_approx=r['repeated_exact_approx'],
        repeated_phase040_approx=r['repeated_phase_approx'],repeated_band037_approx=r['repeated_band_approx'],
        small_base_mass_approx=smallmass,large_endpoint_mass_approx=large,
        aggregate_repeated_approx=R,small_prime_base_count=len(small),
        occupied_square_window_count=len(windows),composite_square_window_count=sum(not w['prime'] for w in windows),
        budget040_approx=r['budget040_approx'],budget041_approx=B,
        margin040_approx=r['margin040_approx'],margin041_approx=margin)
    rows.append(row)
    if n in {3,32,69,297,1031,2896,5000}:anchors.append(dict(row,small_base_blocks=small,square_windows=windows))
summary=dict(sample_count=len(rows),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
    range=[3,300],additional_anchors=[1031,2896,5000],
    aggregate_above_band_anchors=[r['n'] for r in rows if r['aggregate_repeated_approx']>r['repeated_band037_approx']+1e-7],
    nonpositive_aggregate_margin_anchors=[r['n'] for r in rows if r['margin041_approx']<=0],
    elapsed_seconds=round(time.monotonic()-start,3),
    scope='Exact integer square-root endpoints and exponent multiplicity; floating log weights and margins are diagnostics, never Lean premises. Primality dropped for large bases; activity dropped for small prime bases. No later carry tests used.')
(base/'logs/diagnostics-041.json').write_text(json.dumps(dict(summary=summary,rows=rows,anchors=anchors),indent=2)+'\n')
print(json.dumps(summary,indent=2))
for r in rows:
    if r['n'] in {3,32,69,297,1031,2896,5000}:print(json.dumps(r))
