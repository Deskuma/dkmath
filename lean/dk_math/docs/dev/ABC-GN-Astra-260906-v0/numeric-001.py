"""Exact ASTRA-001 regressions; Python standard library only.
Finite calculations complement, and do not replace, the quantified Lean proofs.
"""
from math import gcd
import json


def gn(a, b):
    return a*a + 3*a*b + 3*b*b


def exact_root(q, k, f, derivative):
    x = next(r for r in range(q) if f(r) % q == 0)
    modulus = q
    for _ in range(k):
        assert f(x) % modulus == 0
        digit = (-(f(x)//modulus) * pow(derivative(x), -1, q)) % q
        x += modulus * digit
        modulus *= q
    x = (x + q**k) % modulus
    assert f(x) % q**k == 0 and f(x) % q**(k+1) != 0
    return x


for k, l in [(1, 1), (2, 3), (4, 2), (8, 8)]:
    x = exact_root(7, k, lambda a: gn(a, 1), lambda a: 2*a+3)
    y = exact_root(13, l, lambda a: gn(1, a), lambda a: 6*a+3)
    m, n = 7**(k+1), 13**(l+1)
    start = (x + ((y-x)*pow(m, -1, n) % n)*m) % (m*n)
    for t in range(10):
        a = start+m*n*t
        assert a > 0 and gcd(a, 1) == 1
        assert gn(a, 1) % 7**k == 0 and gn(a, 1) % 7**(k+1) != 0
        assert gn(1, a) % 13**l == 0 and gn(1, a) % 13**(l+1) != 0
    print('exact_depth_progression', json.dumps(dict(k=k, l=l, start=start, step=m*n, checked_terms=10)))

for n in [1, 2, 5, 9]:
    endpoint = 13**n
    depths = [7**(2*n), 13**(2*n)]
    joint = depths[0]*depths[1]
    upper = 3*(endpoint+1)**2
    assert all(d <= gn(endpoint, 1) for d in depths)
    assert joint > upper
    if n == 1:
        assert all(gn(a, 1) % joint != 0 for a in range(endpoint+1))
    print('empty_two_prime_profile', json.dumps(dict(n=n, X=endpoint, excess=2*n-1,
        local_depths=depths, joint_modulus=joint, cubic_upper=upper,
        each_local_depth_fits=True, joint_fiber_empty_by_size=True)))

for m in [0, 1, 2, 4]:
    n = 4*m+1
    endpoint = 13**n
    # Lean proves raw boundary sum >= lower and interval length <= scale.
    lower = 4*26**m*13**(4*m)
    scale = 14*13**(4*m)
    assert endpoint+1 <= scale
    assert 26*13**4 <= 91**3
    print('raw_sum_lower_bound', json.dumps(dict(m=m, n=n, X=endpoint,
        lower=lower, interval_scale_upper=scale,
        normalized_lower_numerator=2*26**m, normalized_lower_denominator=7)))
