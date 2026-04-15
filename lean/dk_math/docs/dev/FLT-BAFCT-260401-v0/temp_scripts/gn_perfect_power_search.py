#!/usr/bin/env python3
"""
GN/p = s^p の解の存在性を直接調べる。

GN(p, gap, y)/p = s^p が成立する (gap, y, s) の組を網羅探索。
gap = p^{p-1} * t^p の形に制限。

目的: s^p = f(t, y) を満たす正整数解の構造を分析し、
FLT 反例条件 (coprimality) との両立性を調べる。
"""
from math import gcd, comb, isqrt


def GN(p, gap, y):
    """GN(p, gap, y) = Σ_{k=0}^{p-1} C(p, k+1) * gap^k * y^{p-1-k}"""
    return sum(comb(p, k + 1) * gap**k * y ** (p - 1 - k) for k in range(p))


def is_perfect_power(n, p):
    """Check if n is a perfect p-th power. Returns root if yes, None otherwise."""
    if n <= 0:
        return None
    # Binary search for the p-th root
    lo, hi = 1, int(n ** (1.0 / p)) + 2
    while lo <= hi:
        mid = (lo + hi) // 2
        val = mid**p
        if val == n:
            return mid
        elif val < n:
            lo = mid + 1
        else:
            hi = mid - 1
    return None


p = 5
pp_minus_1 = p ** (p - 1)  # 625

print(f"p = {p}")
print(f"p^(p-1) = {pp_minus_1}")
print(f"Normal form: gap = {pp_minus_1} * t^{p}")
print()

# Search for GN(p, gap, y)/p = s^p
print("=" * 80)
print(f"SEARCH: GN({p}, {pp_minus_1}*t^{p}, y) / {p} = s^{p}")
print("=" * 80)

solutions = []
max_t = 5  # t の上限
max_y = 200  # y の上限

for t in range(1, max_t + 1):
    gap = pp_minus_1 * t**p
    for y in range(1, max_y + 1):
        gn = GN(p, gap, y)
        if gn % p != 0:
            continue
        gn_div_p = gn // p
        s = is_perfect_power(gn_div_p, p)
        if s is not None:
            x = p * t * s
            z = gap + y
            # Check FLT: x^p + y^p == z^p?
            flt_check = x**p + y**p == z**p
            # Coprimality checks
            cop_ts = gcd(t, s) == 1
            cop_ty = gcd(t, y) == 1
            cop_sy = gcd(s, y) == 1
            cop_xy = gcd(x, y) == 1
            all_cop = cop_ts and cop_ty and cop_sy

            solutions.append(
                (t, y, s, gap, gn, x, z, flt_check, all_cop, cop_ts, cop_ty, cop_sy)
            )

            marker = "★ FLT!" if flt_check else ""
            cop_str = "✓ coprime" if all_cop else "✗ NOT coprime"
            print(f"  t={t}, y={y}: s={s}, gap={gap}, GN={gn}")
            print(f"    x={x}, z={z}, FLT: {flt_check} {marker}")
            print(
                f"    gcd(t,s)={gcd(t,s)}, gcd(t,y)={gcd(t,y)}, gcd(s,y)={gcd(s,y)} → {cop_str}"
            )
            if not all_cop:
                failures = []
                if not cop_ts:
                    failures.append(f"gcd(t,s)={gcd(t,s)}")
                if not cop_ty:
                    failures.append(f"gcd(t,y)={gcd(t,y)}")
                if not cop_sy:
                    failures.append(f"gcd(s,y)={gcd(s,y)}")
                print(f"    COPRIMALITY FAILURE: {', '.join(failures)}")
            print()

print(f"\nTotal solutions found: {len(solutions)}")
if solutions:
    flt_solutions = [s for s in solutions if s[7]]
    coprime_solutions = [s for s in solutions if s[8]]
    flt_and_coprime = [s for s in solutions if s[7] and s[8]]
    print(f"  FLT counterexamples: {len(flt_solutions)}")
    print(f"  Coprime solutions: {len(coprime_solutions)}")
    print(f"  FLT + coprime: {len(flt_and_coprime)}")
else:
    print("  ==> NO SOLUTIONS where GN/p is a perfect p-th power!")

# Try larger range with t=1
print()
print("=" * 80)
print(f"EXTENDED SEARCH: t=1, y up to 10000")
print("=" * 80)
t = 1
gap = pp_minus_1
count = 0
for y in range(1, 10001):
    gn = GN(p, gap, y)
    gn_div_p = gn // p
    s = is_perfect_power(gn_div_p, p)
    if s is not None:
        count += 1
        x = p * t * s
        z = gap + y
        flt_check = x**p + y**p == z**p
        cop_all = gcd(t, s) == 1 and gcd(t, y) == 1 and gcd(s, y) == 1
        print(f"  y={y}: s={s}, x={x}, z={z}, FLT={flt_check}, coprime={cop_all}")

if count == 0:
    print("  ==> NO SOLUTIONS for t=1, y ∈ [1, 10000]!")

# Analysis: WHY are there no solutions?
# s^5 = GN(5, 625, y)/5 = y^4 + 1250y^3 + 781250y^2 + 244140625y + 30517578125
# Is this polynomial EVER a perfect 5th power?

print()
print("=" * 80)
print("ANALYSIS: Gap between consecutive 5th powers vs f(y)")
print("=" * 80)


def f(y, t=1, p=5):
    gap = p ** (p - 1) * t**p
    return GN(p, gap, y) // p


# For y around the "crossing point" where s transitions from s to s+1
for y in range(1, 51):
    val = f(y)
    # Find nearest 5th power
    s_approx = int(val**0.2)
    for s_try in range(max(1, s_approx - 2), s_approx + 3):
        if s_try**5 == val:
            print(f"  y={y}: f(y)={val} = {s_try}^5 ★")
            break
    else:
        s_lo = s_approx
        while s_lo**5 > val:
            s_lo -= 1
        while (s_lo + 1) ** 5 <= val:
            s_lo += 1
        gap_below = val - s_lo**5
        gap_above = (s_lo + 1) ** 5 - val
        frac = (
            gap_below / ((s_lo + 1) ** 5 - s_lo**5) if (s_lo + 1) ** 5 > s_lo**5 else 0
        )
        if y <= 20 or y % 10 == 0:
            print(
                f"  y={y}: f(y)={val}, between {s_lo}^5={s_lo**5} and {s_lo+1}^5={(s_lo+1)**5}"
            )
            print(
                f"         gap below: {gap_below}, gap above: {gap_above}, fraction: {frac:.6f}"
            )

# KEY OBSERVATION: The polynomial f(y) grows as y^4, while s^5 grows as s^5.
# As y increases by 1, f(y) increases by O(y^3).
# s^5 gaps grow as s^4.
# Since s ~ y^{4/5}: s^4 ~ y^{16/5} ~ y^{3.2}
# And f(y+1)-f(y) ~ y^3.
# So the "density" of possible hits is ~ y^3 / y^{3.2} = y^{-0.2} → 0.
# This means hits become SPARSER as y grows!
# A heuristic Borel-Cantelli argument suggests only finitely many solutions.

print()
print("=" * 80)
print("DENSITY ANALYSIS: Probability of f(y) being a perfect 5th power")
print("=" * 80)

# f(y+1) - f(y) = derivative ≈ 4y^3 + 3750y^2 + ...
# s^5_next - s^5 ≈ 5s^4 ≈ 5 y^{16/5}

for y in [10, 100, 1000, 10000]:
    val = f(y)
    s_approx = round(val**0.2)
    f_increment = f(y + 1) - f(y)
    s5_gap = (s_approx + 1) ** 5 - s_approx**5
    density = f_increment / s5_gap if s5_gap > 0 else float("inf")
    print(
        f"  y={y}: f'(y) ≈ {f_increment}, s^5 gap ≈ {s5_gap}, density ≈ {density:.6f}"
    )

print()
print("=" * 80)
print("MODULAR OBSTRUCTION ANALYSIS")
print("=" * 80)

# Check f(y) mod small primes to find modular obstructions
for mod in [2, 3, 7, 11, 31]:
    residues = set()
    fifth_powers = set()
    for y in range(mod):
        residues.add(f(y) % mod)
    for s in range(mod):
        fifth_powers.add(pow(s, 5, mod))
    intersection = residues & fifth_powers
    print(f"  mod {mod}: f(y) residues = {sorted(residues)}")
    print(f"           5th power residues = {sorted(fifth_powers)}")
    print(f"           intersection = {sorted(intersection)}")
    if not intersection:
        print(f"  ★★★ MODULAR OBSTRUCTION AT {mod}! f(y) can NEVER be a 5th power! ★★★")
    print()
