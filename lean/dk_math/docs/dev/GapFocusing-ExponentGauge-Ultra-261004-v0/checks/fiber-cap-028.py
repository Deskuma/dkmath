"""Diagnostic-only common-base fiber cap proposed for checkpoint 029."""
from pathlib import Path
import json,math
base=Path(__file__).resolve().parent.parent
def ilog(p,v):
    k=0;q=1
    while q*p<=v:q*=p;k+=1
    return k
rows=[];worst=(0,0);best=(1e9,0)
for line in (base/'logs/diagnostics-028.jsonl').open():
    r=json.loads(line);n=r['n']
    if n<3:continue
    q=0;events={}
    for d in r['prime_label_deltas']:q+=d;events[q]=(q,1)
    for q,p,a in r['higher_labels']:events[q]=(p,a)
    images={}
    for q,(p,a) in events.items():
        if q>2*n:
            m=q*(n*n//q+1)
            assert m not in images or images[m]==p
            images[m]=p
    cap=math.fsum((ilog(p,n*n)-ilog(p,2*n))*math.log(p) for p in images.values())
    assert cap+1e-8>=r['large_mass_approx']
    ratio=cap/r['large_mass_approx']
    if ratio>worst[0]:worst=(ratio,n)
    if ratio<best[0]:best=(ratio,n)
    if n in [3,5,11,19,29,297,1031,2896,5000]:
        rows.append(dict(n=n,large_mass_approx=r['large_mass_approx'],fiber_cap_approx=cap,cap_over_large_approx=ratio))
data=dict(scope='Diagnostic candidate bound only; no Lean theorem for this cap is added in checkpoint 028.',candidate='Sum over occupied shell images m of (Nat.log p_m base - Nat.log p_m width) * log(p_m); p_m is the unique prime base of the large labels at m.',range=[3,5000],worst_ratio=dict(ratio=worst[0],n=worst[1]),best_ratio=dict(ratio=best[0],n=best[1]),anchors=rows)
(base/'logs/fiber-cap-028.json').write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps({k:v for k,v in data.items() if k!='anchors'}))
