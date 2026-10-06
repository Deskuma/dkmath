"""Independent quotient windows, elementary envelopes, and exact ledger comparison."""
from pathlib import Path
from bisect import bisect_right
import hashlib, json, math, time

base = Path(__file__).resolve().parent.parent
source = base / 'logs/diagnostics-028.jsonl'
old = json.loads((base / 'logs/diagnostics-summary-028.json').read_text())
assert hashlib.sha256(source.read_bytes()).hexdigest() == old['data_sha256']
fiber_file = base / 'logs/diagnostics-029.json'
fiber_data = json.loads(fiber_file.read_text())
assert fiber_data['summary']['source_sha256'] == old['data_sha256']
fiber = {r['n']: r for r in fiber_data['rows']}
start = time.monotonic()
limit = (5000**2 + 10000)//2
sieve = bytearray(b'\x01') * (limit+1)
sieve[:2] = b'\x00\x00'
for p in range(2, math.isqrt(limit)+1):
    if sieve[p]:
        sieve[p*p::p] = b'\x00' * ((limit-p*p)//p+1)
primes = [p for p in range(2, limit+1) if sieve[p]]
rows, anchors = [], []
failures, loglog_failures = [], []
odd_passes, fiber_improvements = [], []
geometric_passes, geometric_loglog_passes, geometric_fiber_improvements = [], [], []
first_slack = None
for line in source.open():
    r = json.loads(line)
    n = r['n']
    if n < 3:
        continue
    b, w, t = n*n, 2*n, n*n+2*n
    inventory, p = [], 0
    for d in r['prime_label_deltas']:
        p += d
        if p > w:
            inventory.append(p)
    pairs, envelopes, raw, odd, geometric, packets = [], [], [], [], [], []
    # Above this cutoff B <= width, so A >= B and choose(B,B-A)=1.
    active = min(n-1, t//(w+1))
    for k in range(2, active+1):
        A, B = max(b//k, w), t//k
        C = max(B-A, 0)
        ps = primes[bisect_right(primes, A):bisect_right(primes, B)]
        assert all(b < k*p <= t and p > w and p <= b for p in ps)
        assert all(k == b//p+1 for p in ps)
        pairs.extend((k,p) for p in ps)
        value = math.lgamma(B+1)-math.lgamma(C+1)-math.lgamma(B-C+1)
        envelopes.append(value)
        raw.append(C*math.log(B) if B else 0)
        odd_value = ((B+1)//2-(A+1)//2)*math.log(B) if B else 0
        odd.append(odd_value)
        geometric.append(min(value,odd_value))
        if n in [3,4,5,6,7,8,11,19,29,297,1031,5000]:
            packets.append(dict(k=k,A=A,B=B,length=C,odd_count=((B+1)//2-(A+1)//2),
                primes=ps,binomial_log_approx=value,geometric_log_approx=min(value,odd_value)))
    actual = sorted(p for k,p in pairs)
    assert actual == inventory
    assert len(actual) == len(set(actual))
    assert len(pairs) == len(set(k*p for k,p in pairs))
    Q = math.fsum(math.log(p) for p in actual)
    U = math.fsum(envelopes)
    repeated = r['large_mass_approx']-Q
    assert repeated > -1e-8 and U >= Q-1e-8
    remainder = r['small_mass_approx']+repeated+r['higher_correction_approx']
    margin = r['log_cell_approx']-remainder-U
    loglog_margin = r['log_cell_approx']-r['small_mass_approx']-repeated-r['log_log_budget_approx']-U
    odd_margin = r['log_cell_approx']-remainder-math.fsum(odd)
    G = math.fsum(geometric)
    geometric_margin = r['log_cell_approx']-remainder-G
    geometric_loglog_margin = r['log_cell_approx']-r['small_mass_approx']-repeated-r['log_log_budget_approx']-G
    assert abs(remainder+Q-r['old_Pascal_budget_approx']) < 1e-8
    if margin <= 0:
        failures.append(n)
    if loglog_margin <= 0:
        loglog_failures.append(n)
    if odd_margin > 0:
        odd_passes.append(n)
    if U+repeated < fiber[n]['cutoff_budget_approx']-1e-8:
        fiber_improvements.append(n)
    if geometric_margin > 0:
        geometric_passes.append(n)
    if geometric_loglog_margin > 0:
        geometric_loglog_passes.append(n)
    if G+repeated < fiber[n]['cutoff_budget_approx']-1e-8:
        geometric_fiber_improvements.append(n)
    row = dict(n=n,active_cofactor_cutoff=active,singleton_count=len(actual),
        singleton_mass_approx=Q,repeated_mass_approx=repeated,binomial_budget_approx=U,
        all_integer_cardinality_budget_approx=math.fsum(raw),
        odd_cardinality_budget_approx=math.fsum(odd),
        exact_old_budget_approx=r['old_Pascal_budget_approx'],log_cell_approx=r['log_cell_approx'],
        small_mass_approx=r['small_mass_approx'],higher_mass_approx=r['higher_correction_approx'],
        exact_higher_consumer_margin_approx=margin,loglog_consumer_margin_approx=loglog_margin,
        odd_cardinality_consumer_margin_approx=odd_margin,
        fiber029_budget_approx=fiber[n]['cutoff_budget_approx'],
        new_large_envelope_approx=U+repeated,
        geometric_budget_approx=G,geometric_consumer_margin_approx=geometric_margin,
        geometric_loglog_margin_approx=geometric_loglog_margin,
        independent_pairs_equal_inventory=True,prime_projection_injective=True,target_projection_injective=True)
    if first_slack is None and U > Q+1e-8:
        first_slack = dict(row)
    rows.append(row)
    if packets:
        anchors.append(dict(row,windows=packets))
summary = dict(range=[3,5000],source_sha256=old['data_sha256'],
    fiber_source_sha256=hashlib.sha256(fiber_file.read_bytes()).hexdigest(),
    integer_scope='Independent prime sieve and quotient windows equal inherited singleton labels; both pair projections checked.',
    floating_scope='Logarithmic bounds and margins are diagnostics, not Lean proof premises.',
    first_strict_slack_approx=first_slack,
    first_exact_higher_failure_approx=next((r for r in rows if r['n'] in failures),None),
    exact_higher_passing_anchors_approx=[r['n'] for r in rows if r['n'] not in failures],
    loglog_passing_anchors_approx=[r['n'] for r in rows if r['n'] not in loglog_failures],
    odd_cardinality_passing_anchors_approx=odd_passes,
    improvements_over_029_fiber_budget_approx=fiber_improvements,
    geometric_passing_anchors_approx=geometric_passes,
    geometric_loglog_passing_anchors_approx=geometric_loglog_passes,
    geometric_improvements_over_029_fiber_budget_approx=geometric_fiber_improvements,
    exact_higher_failure_count=len(failures),loglog_failure_count=len(loglog_failures),
    elapsed_seconds=round(time.monotonic()-start,3))
(base/'logs/diagnostics-030.json').write_text(json.dumps(dict(summary=summary,rows=rows,anchors=anchors),separators=(',',':'))+'\n')
print(json.dumps(summary,indent=2))
