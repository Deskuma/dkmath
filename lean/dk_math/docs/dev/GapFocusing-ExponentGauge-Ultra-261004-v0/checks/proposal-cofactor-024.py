"""Numeric exploration of the proposed next theorem; no Lean proof claim."""
from pathlib import Path
from math import gcd
import json
base=Path(__file__).resolve().parent.parent
data=json.loads((base/'logs/discovery-024.json').read_text())
geometry=json.loads((base/'logs/discovery-020.json').read_text())['rows']
results=[]
for key in ['first_shared','297_largest_terminal','297_branching','1031_largest_terminal']:
    seat=data['examples'][key];n,a=seat['n'],seat['a'];m=n*n+a
    g=next(g for g in geometry if (g['n'],g['world_kind'])==(n,seat['world_kind']))
    V={b for b in range(1,g['K']*g['M']+1) if gcd(n*n+b,g['M'])==1}
    residue=1
    for b in sorted(V):
        if a<b:residue=residue*(b-a)%m
    common=gcd(m,residue);cofactor=m//common
    assert cofactor%seat['terminal_product']==0
    B=11 if n in [297,1031] else 2
    e=0
    while B**(e+1)<=cofactor:e+=1
    results.append(dict(example=key,n=n,a=a,complete_point=m,difference_product_mod_point=residue,
                        common_gcd=common,proposed_cofactor=cofactor,terminal_product=seat['terminal_product'],
                        terminal_card=seat['terminal_card'],power_base=B,proposed_source_capacity=e))
(base/'logs/proposed-cofactor-024.json').write_text(json.dumps(results,indent=2)+'\n')
for row in results:print(row)
