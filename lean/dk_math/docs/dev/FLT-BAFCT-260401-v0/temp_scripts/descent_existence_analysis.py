#!/usr/bin/env python3
"""
DESCENT EXISTENCE の精密分析 — 反例文脈での整数解の構造

KEY QUESTION:
  反例 (x, y, z) で q | s (primitive prime) のとき、
  (x/q)^p + y^p は完全 p 乗冪か？

  z'^p = (x/q)^p + y^p  ← これが自然数 z' を持つか？

REFORMULATION:
  z^p + (q^p - 1)·y^p = q^p · z'^p

  必要条件: z^p ≡ y^p (mod q^p)  ← これは q|s から自動！
  十分条件: 商 W/q^p = (x/q)^p + y^p が完全 p 乗  ← OPEN

NEW APPROACH:
  W/q^p が完全 p 乗であることは "q | x を q で割った
  SMALLER Fermat triple の存在" と同値。

  つまり descent existence = "smaller FLT counterexample exists"。
  これ自体が FLT と同値なので、descent を使って FLT を証明する
  アプローチは本質的に「FLT ⟹ FLT」の循環。

  HOWEVER: Wiles の証明は descent を使わない。
  Elementary な approach で descent に頼ると循環する。

  では DESCENT を使わない CONTRADICTION はあるか？
"""
from math import gcd, comb
from sympy import factorint, isprime, nextprime


def GN(p, gap, y):
    return sum(comb(p, k + 1) * gap**k * y ** (p - 1 - k) for k in range(p))


p = 5
print("=" * 70)
print("PART A: CONTRADICTION WITHOUT DESCENT")
print("=" * 70)
print()

print("Approach: 最小反例の NORMAL FORM 条件の不整合性を探す")
print()
print("Normal form conditions (all must hold simultaneously):")
print("  (N1) gap = p^{p-1} · t^p")
print("  (N2) GN(p, gap, y) = p · s^p")
print("  (N3) x = p · t · s")
print("  (N4) gcd(t, s) = 1")
print("  (N5) gcd(t, y) = 1")
print("  (N6) gcd(s, y) = 1")
print("  (N7) s ≡ 1 (mod p)  [from primitive prime structure]")
print("  (N8) every prime q | s satisfies q ≡ 1 (mod p)")
print("  (N9) p | s is forbidden  [gcd(p, s) would violate normal form]")
print()

# Actually wait - let me re-check (N9)
print("Wait: is p | s actually forbidden?")
print("  If s = p·s₁, then GN = p·(p·s₁)^p = p^{p+1}·s₁^p")
print("  And gap·GN = p^{p-1}·t^p · p^{p+1}·s₁^p = p^{2p}·t^p·s₁^p")
print("  But x^p = p^p·t^p·s^p = p^p·t^p·(p·s₁)^p = p^{2p}·t^p·s₁^p ✓")
print("  So p | s is allowed! Not forbidden by normal form.")
print()

# Check if p | GN has some special structure
print("=" * 70)
print("PART B: v_p(GN) ANALYSIS")
print("=" * 70)
print()

print("GN(p, p^{p-1}·t^p, y) mod p^k:")
print()

for t_val in [1, 2]:
    gap_val = p ** (p - 1) * t_val**p
    for y_val in [1, 2, 3, 7, 11, 13]:
        if gcd(y_val, p) != 1:
            continue
        gn_val = GN(p, gap_val, y_val)
        vp_gn = 0
        temp = gn_val
        while temp % p == 0:
            temp //= p
            vp_gn += 1

        # Also compute GN/p mod p
        gn_div_p = gn_val // p
        gn_div_p_mod_p = gn_div_p % p

        # GN/p ≡ y^{p-1} (mod p) from the leading term
        y_pm1_mod_p = pow(y_val, p - 1, p)

        print(
            f"  t={t_val}, y={y_val}: v_p(GN)={vp_gn}, "
            f"GN/p mod p = {gn_div_p_mod_p}, "
            f"y^(p-1) mod p = {y_pm1_mod_p}, "
            f"match: {gn_div_p_mod_p == y_pm1_mod_p}"
        )

print()
print("Observation: GN/p ≡ y^{p-1} (mod p)")
print("So if GN/p = s^p, then s^p ≡ y^{p-1} (mod p)")
print("By Fermat's little theorem: s^p ≡ s (mod p)")
print("So s ≡ y^{p-1} (mod p)")
print("For p=5: s ≡ y^4 ≡ 1 (mod 5) (by FLT)")
print("This is consistent with (N7).")

# ============================================================
# PART C: 高次の p 整除条件
# ============================================================
print()
print("=" * 70)
print("PART C: HIGHER p-DIVISIBILITY of GN/p")
print("=" * 70)
print()

print("GN = p·y^{p-1} + Σ_{k≥1} C(p,k+1) · (p^{p-1}t^p)^k · y^{p-1-k}")
print()
print("GN/p = y^{p-1} + Σ_{k≥1} [C(p,k+1)/p] · p^{(p-1)k} · t^{pk} · y^{p-1-k}")
print()
print("For p=5:")
print("  C(5,2)/5 = 2,  C(5,3)/5 = 2,  C(5,4)/5 = 1,  C(5,5)/5 = 1/5 ← NOT integer!")
print()
print("Wait, C(5,5) = 1, so C(5,5)/5 = 1/5. But we're computing correctly:")
print("  GN/p = Σ C(p,k+1) · gap^k · y^{p-1-k} / p")
print("  For k=p-1: C(p,p)·gap^{p-1}·y^0 / p = gap^{p-1}/p")
print(f"  gap^(p-1)/p = (p^(p-1)·t^p)^(p-1) / p = p^((p-1)^2)·t^{p*(p-1)} / p")
print(f"  = p^((p-1)^2 - 1) · t^{p*(p-1)}")
print(f"  For p=5: = 5^{15} · t^{20}")
print()

print("Actually, computing GN more carefully:")
print("  GN = Σ_{k=0}^{p-1} C(p,k+1) · gap^k · y^{p-1-k}")
print("  = p·y^4 + C(5,2)·gap·y^3 + C(5,3)·gap²·y² + C(5,4)·gap³·y + C(5,5)·gap⁴")
print("  = 5y^4 + 10·gap·y^3 + 10·gap²·y² + 5·gap³·y + gap⁴")
print()
print("  GN/5 is NOT simply Σ C(p,k+1)/p · ...!")
print("  Rather: GN = 5(y^4 + 2·gap·y^3 + 2·gap²·y² + gap³·y) + gap⁴")
print("  And gap⁴ = (5⁴·t⁵)⁴ = 5¹⁶·t²⁰")
print("  So GN/5 = y^4 + 2·gap·y³ + 2·gap²·y² + gap³·y + 5¹⁵·t²⁰")
print()

# Verify
gap_val = 625  # p=5, t=1
for y_val in [1, 7, 11]:
    gn = GN(5, gap_val, y_val)
    formula = (
        y_val**4
        + 2 * gap_val * y_val**3
        + 2 * gap_val**2 * y_val**2
        + gap_val**3 * y_val
        + 5**15 * 1**20
    )
    print(
        f"  y={y_val}: GN/5 = {gn//5}, formula = {formula}, match: {gn//5 == formula}"
    )

# ============================================================
# PART D: s^p の構造 — 素因数の q ≡ 1 (mod p) 制約
# ============================================================
print()
print("=" * 70)
print("PART D: PRIME FACTOR STRUCTURE of s")
print("=" * 70)
print()

print(f"s^{p} = GN/{p}")
print(f"s must be composed of primes q ≡ 1 (mod {p})")
print(f"Smallest primes ≡ 1 (mod {p}): ", end="")
primes_1_mod_p = []
q = 2
while len(primes_1_mod_p) < 10:
    if isprime(q) and q % p == 1:
        primes_1_mod_p.append(q)
    q += 1
print(primes_1_mod_p)
print()

# For each possible small s, check if GN/p can equal s^p
print("For each small valid s, what y would give GN/p = s^p?")
print("-" * 60)

valid_s_values = [1]  # s=1 is trivially valid
for q1 in primes_1_mod_p[:5]:
    valid_s_values.append(q1)
    for q2 in primes_1_mod_p[:3]:
        if q2 <= q1:
            valid_s_values.append(q1 * q2)

valid_s_values = sorted(set(valid_s_values))[:15]
print(f"Testing s values: {valid_s_values}")
print()

gap_val = 625  # t=1, p=5
for s_val in valid_s_values:
    if s_val % p != 1 % p:  # s ≡ 1 (mod p)?
        s_mod_p = s_val % p
        # Actually s ≡ y^{p-1} ≡ 1 (mod p) by FLT
        pass  # Don't filter, just check

    target_gn_div_p = s_val**p
    target_gn = p * target_gn_div_p

    # Find y with GN(p, gap_val, y) = target_gn
    # GN is increasing in y, GN(p, gap_val, 0) = gap^{p-1} = 625^4 = 152587890625
    gn_at_0 = GN(p, gap_val, 0)

    if target_gn < gn_at_0:
        # Need GN < GN(0) — impossible since GN is increasing and minimum at y=0
        print(
            f"  s={s_val}: target GN = {target_gn} < GN(gap,0) = {gn_at_0} → IMPOSSIBLE"
        )
        continue

    # Binary search for y
    lo, hi = 0, 10**8
    # First check if target is reachable
    gn_at_hi = GN(p, gap_val, hi)
    if gn_at_hi < target_gn:
        print(f"  s={s_val}: target GN too large even for y={hi}")
        continue

    while lo < hi:
        mid = (lo + hi) // 2
        gn_mid = GN(p, gap_val, mid)
        if gn_mid < target_gn:
            lo = mid + 1
        else:
            hi = mid

    gn_lo = GN(p, gap_val, lo)
    if gn_lo == target_gn:
        z_val = gap_val + lo
        x_val = p * 1 * s_val  # t=1
        flt_check = x_val**p + lo**p == z_val**p
        cop_sy = gcd(s_val, lo) == 1
        cop_ty = gcd(1, lo) == 1  # t=1
        print(f"  s={s_val}: y={lo}, GN matches! z={z_val}, x={x_val}")
        print(f"    FLT: {flt_check}, gcd(s,y)={gcd(s_val,lo)}, coprime={cop_sy}")
    else:
        gn_below = GN(p, gap_val, lo - 1) if lo > 0 else gn_at_0
        diff_below = target_gn - gn_below
        diff_above = gn_lo - target_gn
        print(
            f"  s={s_val}: NO integer y. Nearest y={lo-1}→{lo}, "
            f"gaps: below={diff_below}, above={diff_above}"
        )

# ============================================================
# PART E: 不可能性の強い指標 — mod q 解析
# ============================================================
print()
print("=" * 70)
print("PART E: IMPOSSIBILITY VIA MOD q ANALYSIS")
print("=" * 70)
print()

print("For s = q (single prime), GN/p = q^p")
print("GN  = p · q^p")
print()
print("GN(p, gap, y) = p·q^p")
print("⟺ y^4 + 2·gap·y³ + 2·gap²·y² + gap³·y + 5^{15} = q^5  (for p=5, t=1)")
print()

# Check mod q for each q
for q_val in [11, 31, 41, 61]:
    target = q_val**p  # = GN/p
    print(f"q = {q_val}:")
    print(f"  target = GN/{p} = {q_val}^{p} = {target}")

    # GN/p mod q:
    # GN/p = y^4 + 2·625·y³ + 2·625²·y² + 625³·y + 5^15
    # mod q:
    gap_mod_q = gap_val % q_val
    five_15_mod_q = pow(5, 15, q_val)

    # Find y mod q with GN/p ≡ 0 mod q (since target ≡ 0 mod q)
    solutions_mod_q = []
    for y_trial in range(q_val):
        val = (
            pow(y_trial, 4, q_val)
            + 2 * gap_mod_q * pow(y_trial, 3, q_val)
            + 2 * pow(gap_mod_q, 2, q_val) * pow(y_trial, 2, q_val)
            + pow(gap_mod_q, 3, q_val) * y_trial
            + five_15_mod_q
        ) % q_val
        if val == 0:
            solutions_mod_q.append(y_trial)

    print(f"  y mod {q_val} solutions for GN/p ≡ 0: {solutions_mod_q}")

    # Additionally: gcd(s, y) = 1 means q ∤ y
    valid_solutions = [y for y in solutions_mod_q if y != 0]
    print(f"  After removing y ≡ 0 (coprimality): {valid_solutions}")

    # For s = q: GN/p = q^p ⟹ GN/p ≡ 0 (mod q^p)
    # So y must satisfy GN/p ≡ 0 (mod q^p)
    # Which means sum of terms ≡ 0 mod q^p
    qp_val = q_val**p
    solutions_mod_qp = []
    for y_trial in valid_solutions:
        # Hensel lift from mod q to mod q^p
        y_current = y_trial
        for lift_step in range(1, p):
            q_power = q_val ** (lift_step + 1)
            # Find delta such that f(y_current + delta*q^lift) ≡ 0 mod q^{lift+1}
            f_val = (
                y_current**4
                + 2 * gap_val * y_current**3
                + 2 * gap_val**2 * y_current**2
                + gap_val**3 * y_current
                + 5**15
            ) % q_power
            if f_val % q_val ** (lift_step) != 0:
                break  # Hensel fails
            f_val_reduced = f_val // q_val**lift_step
            # f'(y) = 4y^3 + 6·gap·y² + 4·gap²·y + gap³
            f_prime = (
                4 * y_current**3
                + 6 * gap_val * y_current**2
                + 4 * gap_val**2 * y_current
                + gap_val**3
            ) % q_val
            if f_prime == 0:
                break  # Double root, Hensel may fail
            delta = (-f_val_reduced * pow(f_prime, q_val - 2, q_val)) % q_val
            y_current = y_current + delta * q_val**lift_step

        # Verify
        f_final = (
            y_current**4
            + 2 * gap_val * y_current**3
            + 2 * gap_val**2 * y_current**2
            + gap_val**3 * y_current
            + 5**15
        ) % qp_val
        if f_final == 0:
            solutions_mod_qp.append(y_current)

    print(f"  Hensel lifts mod {q_val}^{p}: {solutions_mod_qp}")
    print()

# ============================================================
# PART F: SUMMARY
# ============================================================
print()
print("=" * 70)
print("SUMMARY: CURRENT STATE OF THE DESCENT ANALYSIS")
print("=" * 70)
print()
print("1. CIRCULARITY: GN/p = s^p ⟺ FLT counterexample (tautological)")
print()
print("2. DESCENT EXISTENCE: z'^p = (x/q)^p + y^p asking for another triple")
print("   = q^p·z'^p = z^p + (q^p-1)·y^p")
print("   Divisibility by q^p: AUTOMATIC from q|s")
print("   Perfect p-th power: OPEN (= FLT itself)")
print()
print("3. CRT OBSTRUCTION: For specific (q, p), t^p is determined mod q^p")
print("   and the determined value is NEVER a perfect p-th power (numerically)")
print("   BUT: this uses t < q (small t assumption), not general")
print()
print("4. CYCLOTOMIC APPROACH: GN = Π(z - ζ^j·y) gives ideal factorization")
print("   For regular primes: ideal-to-element upgrade works → descent ✓")
print("   For irregular primes: class group obstruction → need extra argument")
print()
print("5. COSMIC FORMULA: The normal form gap·GN = x^p is a REWRITING not a new eq.")
print("   The only new content is the COPRIMALITY + PRIME STRUCTURE of s")
print()
print("★ ACTIONABLE NEXT STEPS:")
print("  A. Formalize QAdicResidue (z ≡ ω^j·y mod q) — CONCRETE, provable")
print("  B. Formalize SizeReduction (z' < z) — TRIVIAL")
print("  C. Document circularity as a THEOREM in DescentChain")
print("  D. Investigate non-descent contradictions")
print("     (e.g., norm product constraints, Bernoulli number obstruction)")
