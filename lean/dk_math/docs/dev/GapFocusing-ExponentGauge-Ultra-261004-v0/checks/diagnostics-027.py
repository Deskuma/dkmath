"""Extend verified 026 integer inventory; all real-log comparisons are diagnostics."""
from pathlib import Path
from fractions import Fraction
import math,json,hashlib,time
base=Path(__file__).resolve().parent.parent
source=base/'logs/diagnostics-026.json'
start=time.monotonic();data=json.loads(source.read_text());rows=[]
for old in data['rows']:
    n=old['n'];L=((n+1)**2).bit_length()-1;top=n*n+2*n
    odds=list(range(3,L+1,2));occupied=[e['exponent'] for e in old['events']]
    reciprocal_sum=sum((Fraction(1,a) for a in odds),Fraction())
    budgets=dict(old_log_count=old['logarithmic_mass_bound_approx'],
        reciprocal=math.log(top)*float(reciprocal_sum),log_log=math.log(top)*math.log(L),
        theta=old['theta_approx'],cube_candidate=old['cube_candidate_mass_approx'])
    correction=old['higher_mass_approx'];mass=old['von_mangoldt_mass_approx']
    rows.append(dict(n=n,top=top,binary_cutoff=L,events=old['events'],
        occupied_depths=occupied,odd_admissible_depths=odds,
        reciprocal_sum_exact=str(reciprocal_sum),higher_correction_approx=correction,
        shell_mass_approx=mass,budgets_approx=budgets,
        correction_over_budget_approx={k:(correction/v if v>0 else None) for k,v in budgets.items()},
        strict_mass_comparison_approx={k:v<mass for k,v in budgets.items()},
        new_beats_old_approx={k:budgets[k]<budgets['old_log_count'] for k in ['reciprocal','log_log']}))
valid=[r for r in rows if r['n']>=3]
summary=dict(range=[1,5000],source='diagnostics-026.json',source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
    exact_content='integer events, binary cutoffs, occupied/admissible depths, rational reciprocal sums',
    approximate_content='all logarithms, mass ratios, budget comparisons and sufficient-comparison flags',
    worst_ratio_all={k:max((r['correction_over_budget_approx'][k],r['n']) for r in rows if r['correction_over_budget_approx'][k] is not None) for k in ['reciprocal','log_log']},
    worst_ratio_provider_domain={k:max((r['correction_over_budget_approx'][k],r['n']) for r in valid) for k in ['reciprocal','log_log']},
    first_new_beats_old={k:next((r['n'] for r in rows if r['new_beats_old_approx'][k]),None) for k in ['reciprocal','log_log']},
    first_new_beats_old_provider_domain={k:next((r['n'] for r in valid if r['new_beats_old_approx'][k]),None) for k in ['reciprocal','log_log']},
    new_not_strictly_below_old={k:[r['n'] for r in rows if not r['new_beats_old_approx'][k]] for k in ['reciprocal','log_log']},
    conditional_comparison_failures={k:[r['n'] for r in valid if not r['strict_mass_comparison_approx'][k]] for k in ['old_log_count','reciprocal','log_log','theta','cube_candidate']},
    anchors=[rows[n-1] for n in [2,3,5,7,9,11,19,29,297,1031,2896]],
    elapsed_seconds=time.monotonic()-start)
(base/'logs/diagnostics-027.json').write_text(json.dumps(dict(summary=summary,rows=rows),indent=2)+'\n')
(base/'logs/diagnostics-summary-027.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
