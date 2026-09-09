"""ASTRA-001 independent repeated-prime-square sieve and fiber audit.

Run: python3 docs/dev/ABC-GN-Astra-260906-v1/numeric-001.py --limit 3000000
Only integer arithmetic is used for coordinates, comparisons and assertions.
Unlike numeric-000.py, this stores only points with repeated prime factors and
visits roots modulo p^2, not a full factorization of every polynomial value.
Output is stdout so it can be retained verbatim as a research log.
"""

import argparse
import collections
import json
import math
import random
from fractions import Fraction

import sympy


def F(a):
    return a * a + 3 * a + 3


def repeated_sieve(limit):
    """Return a -> [full repeated part, odd parity part] for M(a)>1."""
    rows = {}
    roots_checked = 0
    for p0 in sympy.primerange(7, limit + 3):
        p = int(p0)
        if p % 3 != 1:
            continue
        inv2 = pow(2, -1, p)
        roots = sorted({int((z - 3) * inv2 % p)
                        for z in sympy.sqrt_mod(-3, p, all_roots=True)})
        assert len(roots) == 2
        for root in roots:
            digit = -(F(root) // p) * pow(2 * root + 3, -1, p) % p
            lifted = root + p * digit
            modulus = p * p
            assert F(lifted) % modulus == 0
            roots_checked += 1
            for a in range(lifted, limit + 1, modulus):
                n, exponent = F(a), 0
                while n % p == 0:
                    n //= p
                    exponent += 1
                M, r = rows.get(a, (1, 1))
                rows[a] = (M * p ** exponent, r * (p if exponent % 2 else 1))
    return rows, roots_checked


def coords(a, rows):
    M, r = rows.get(a, (1, 1))
    S = F(a) // M
    d = math.isqrt(M // r)
    T = r * S
    assert M == r * d * d and d % r == 0
    assert M * S == F(a) and math.gcd(M, S) == 1
    assert (2 * a + 3) ** 2 + 3 == 4 * T * d * d
    return M, S, r, d, T


def main(limit):
    assert limit >= 88915
    rows, roots = repeated_sieve(limit)
    rng = random.Random(1001)
    sample = set(range(100)) | {rng.randrange(limit + 1) for _ in range(512)}
    sample |= {17, 21, 145, 2173, 3018, 5260, 6105, 7428, 88915}
    sample |= set(rng.sample(sorted(rows), min(256, len(rows))))
    for a in sorted(sample):
        factors = sympy.factorint(F(a))
        expected = math.prod(int(p) ** int(e) for p, e in factors.items() if e >= 2)
        M, S, r, d, T = coords(a, rows)
        assert M == expected
        assert all(int(e) == 1 for e in sympy.factorint(S).values())
        assert all(int(e) == 1 for e in sympy.factorint(T).values())
    print('SIEVE', json.dumps(dict(limit=limit, repeated_points=len(rows),
                                  lifted_roots_checked=roots, cross_checks=len(sample), seed=1001)))

    groups = collections.defaultdict(list)
    same_parameter = collections.defaultdict(list)
    for a in sorted(rows):
        M, S, r, d, T = coords(a, rows)
        u = d // r
        A = 4 * S * u * u
        assert (A * (2 * a + 3)) ** 2 == (A * r) ** 3 - 3 * A * A
        D = 1 << (M.bit_length() - 1)
        groups[T, r, D].append(a)
        same_parameter[T, r].append((d, a, M))
    collisions = [(key, points) for key, points in groups.items() if len(points) >= 2]
    adjacent_checks = 0
    for points in same_parameter.values():
        points.sort()
        for (d1, a1, _), (d2, a2, _) in zip(points, points[1:]):
            assert d1 < d2
            assert 2 * d1 * d1 <= d2 * d2
            # A pair with modulus ratio >=2 cannot share ANY [D,2D),
            # so this also tests non-power-of-two shell positions.
            adjacent_checks += 1
    print('FIBERS', json.dumps(dict(maximum=max(map(len, groups.values()), default=0),
                                   size_two=sum(len(points) == 2 for _, points in collisions),
                                   size_three_or_more=sum(len(points) >= 3 for _, points in collisions),
                                   adjacent_same_Tr_pairs=adjacent_checks,
                                   scope='all repeated points, without large-height filtering')))
    assert not collisions, collisions[:10]
    for X in sorted({100000, 300000, 1000000, limit}):
        if X > limit:
            continue
        shell = collections.defaultdict(list)
        for a, (M, _) in rows.items():
            if 1 <= a <= X and X + 1 < M:
                D = 1 << (M.bit_length() - 1)
                shell[D].append((a, M))
        print('WINDOW', json.dumps(dict(X=X, distinct=sum(len({m for _, m in s}) for s in shell.values()),
                                       witnesses=sum(map(len, shell.values())), shells=len(shell))))

    for M, points in ((169, [21, 145]), (8281, [2173, 3018, 5260, 6105])):
        assert all(coords(a, rows)[0] == M for a in points)
        print('MODULUS_REGRESSION', M, points)
    pell = []
    a, d = 0, 1
    for i in range(10):
        assert F(a) == 3 * d * d and a % 3 == 0 and d % 3 == 1
        if a <= limit:
            assert coords(a, rows) == (d * d, 3, 1, d, 3)
        pell.append((a, d))
        a, d = 7 * a + 12 * d + 9, 4 * a + 7 * d + 6
    print('PELL', json.dumps(pell))
    states = {}
    for a in range(1, 49, 7):
        states[a] = ('forward-deep' if F(a) % 49 == 0 else
                     'swap-deep' if (3*a*a+3*a+1) % 49 == 0 else 'shallow')
    assert states[29] == 'forward-deep' and states[22] == 'swap-deep'
    assert sum(s == 'shallow' for s in states.values()) == 5
    print('MOD49', json.dumps(states))
    a = 7428
    assert F(a) % 49 == 0 and F(a) % 343 != 0
    assert (3*a*a+3*a+1) % 169 == 0 and (3*a*a+3*a+1) % 2197 != 0
    print('PAIRED_EXACT_DEPTH', a, 'v7(F)=2, v13(G)=2')

    # Direct conic enumeration is independent of the polynomial sieve.
    conic_points = 0
    conic_adjacent = 0
    for T in range(2, 2001):
        previous_d = None
        for d in range(1, 3001):
            square = 4 * T * d * d - 3
            y = math.isqrt(square)
            if y * y == square:
                conic_points += 1
                if previous_d is not None:
                    assert 2 * previous_d ** 2 <= d ** 2
                    conic_adjacent += 1
                previous_d = d
    print('DIRECT_CONICS', json.dumps(dict(T_range=[2, 2000], d_range=[1, 3000],
                                          points=conic_points, adjacent_checks=conic_adjacent)))
    q = Fraction
    print('EXACT_EXPONENTS', json.dumps({
        'old_box_hybrid': str(q(3, 2)),
        'r_split_hybrid': str(q(17, 12)),
        'Mordell_transition_delta': str(q(5, 3)),
        'fixed_field_hybrid': str(q(2, 3) + q(5, 3)*q(3, 8)),
        'fixed_field_top': str(2 - 2*q(17, 40)),
        'critical_box_extra_saving_in_B_for_linear': str(q(31, 8)-3),
        'critical_box_extra_saving_in_H_for_linear': str(q(31, 24)-1),
    }))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--limit', type=int, default=3000000)
    main(parser.parse_args().limit)
