#!/usr/bin/env python3
"""
全く別のアプローチ: GNReducedGap を直接証明せず、
DescentChain を 2-primitive を使わない形に再構成できないか？

アイデア: "降下先の counterexample 構成" を経由せず、
直接 counterexample の非存在を示す。

Approach 1: SIZE BOUND → INDUCTION
  If x^p + y^p = z^p and q|x (primitive prime of GN):
  Then GN = p*s^p, q|s, so q^p | GN.

  v_q(x) ≥ 1, so x ≥ q.
  v_q(x^p) = p*v_q(x), v_q(gap) = 0, v_q(GN) = p*v_q(x)

  s = x/(p*t), q|s → v_q(s) ≥ 1 → s ≥ q → x = p*t*s ≥ p*1*q ≥ 5q

  This gives a LOWER BOUND on x. But doesn't contradict anything directly.

Approach 2: MULTIPLE PRIMITIVE PRIMES
  Zsigmondy gives at least one primitive prime q.
  Can we get MANY primitive primes? If there are "too many", contradiction.

  Actually: ALL prime factors of GN that don't divide gap are primitive.
  GN = p * s^p, gap = p^{p-1} * t^p
  GN factors that don't divide gap: factors of s that don't divide t.
  Since gcd(t,s)=1: ALL prime factors of s don't divide t.
  So ALL prime factors of s are primitive → each q_i satisfies p|(q_i-1) and q_i^p | GN.

Approach 3: PRODUCT OF PRIMITIVE PRIMES
  Let s = q1^{a1} * q2^{a2} * ... * qr^{ar}
  Each qi ≡ 1 (mod p)
  s^p = q1^{p*a1} * ... * qr^{p*ar}
  GN = p * s^p

  The product ∏ qi^{ai} = s, and each qi ≡ 1 mod p.
  So s ≡ 1 (mod p)... no, that's not right since qi could be ≡ 1 but products aren't necessarily.

Approach 4: INFINITE DESCENT WITHOUT NEW COUNTEREXAMPLE
  Instead of producing (x/q, y, z'), show that the EXISTENCE of q
  with specific properties contradicts something about (x, y, z).

  For example: q | x and q^p | GN and q ≡ 1 (mod p)
  → combined with Wieferich condition, Coprime conditions, etc.
  → contradiction?

  This is essentially what the CURRENT codebase tries (NePCoprimeKernel).

Approach 5: NORM FORM / QUADRATIC FORM
  z^p - y^p = x^p
  (z-y) * GN(p, z-y, y) = x^p

  GN(p, u, y) = ∑ C(p,k+1) u^k y^{p-1-k}

  For p=5: GN = 5y^4 + 10uy^3 + 10u²y² + 5u³y + u⁴

  This is a "norm form" from Z[ζ_5].
  Specifically: GN(5, u, y) = N_Q(ζ5)/Q(u - ζ5·y) / (u-y) ... no.

  Actually: z^5 - y^5 = ∏_{i=0}^{4} (z - ζ^i·y)
  z - y = gap = u
  The other 4 factors: ∏_{i=1}^{4} (z - ζ^i·y) = GN(5, u, y) ... is this true?

  Let me verify.

Approach 6: DIRECT CONTRADICTION without descent
  Consider z^p - y^p = (z-y) * GN(p, z-y, y) with:
  - GN = p * s^p
  - gap = p^{p-1} * t^p
  - s has only primes ≡ 1 (mod p)

  These conditions might be strong enough for a direct contradiction
  without needing descent.

  For example: Σ 1/(qi-1) or product constraints from qi ≡ 1 (mod p).

Let me explore Approach 6 numerically.
"""

from sympy import binomial, factorint, isprime, primitive_root, nextprime, gcd
from sympy.ntheory.factor_ import totient


def GN(p, u, y):
    return sum(binomial(p, k + 1) * u**k * y ** (p - 1 - k) for k in range(p))


# Verify: GN(p, u, y) = ∏_{i=1}^{p-1} (u+y - ζ^i·y)
# = ∏_{i=1}^{p-1} (z - ζ^i·y) where z = u+y
#
# ∏_{i=0}^{p-1} (z - ζ^i·y) = z^p - y^p = u·GN(p,u,y)
# Factor i=0: z - ζ^0·y = z - y = u
# So ∏_{i=1}^{p-1} (z - ζ^i·y) = u·GN(p,u,y)/u = GN(p,u,y) ✓

print("=" * 60)
print("APPROACH 6: Direct contradiction from prime structure")
print("=" * 60)

# In BranchA: GN = p*s^p where all prime factors of s satisfy q ≡ 1 (mod p)
# Can we derive a contradiction from this?

# Study: for counterexample with p=5, what structure does s have?
# s^5 = GN/5
# GN = (z^5 - y^5)/(z-y) where gap = z-y = 5^4 * t^5

# For small values:
p = 5
print(f"\n--- p = {p} ---")
print(f"\nWhat does GN/p look like for various gap and y?")

for y in [1, 2, 3, 5, 7, 11]:
    for t in [1, 2, 3]:
        gap = p ** (p - 1) * t**p
        gn = GN(p, gap, y)
        if gn % p != 0:
            print(f"  WARNING: GN not divisible by p for gap={gap}, y={y}!")
            continue
        s_p = gn // p
        # Check if s_p is a perfect 5th power
        s = round(s_p ** (1 / p))
        for s_try in range(max(1, s - 2), s + 3):
            if s_try**p == s_p:
                s = s_try
                break
        else:
            # s_p is NOT a 5th power → this (gap, y) doesn't satisfy the normal form
            print(f"  gap={gap}, y={y}: GN/p = {s_p} is NOT a perfect 5th power")
            continue

        print(f"  gap={gap}, y={y}: GN = {gn}, s^5 = {s_p}, s = {s}")
        if s > 1:
            factors = factorint(s)
            print(f"    s factors: {factors}")
            all_cong_1 = all((qi - 1) % p == 0 for qi in factors)
            print(f"    All factors ≡ 1 (mod {p}): {all_cong_1}")
            if all_cong_1:
                print(f"    ★ s passes the primitive prime test!")
            else:
                print(
                    f"    ✗ Some factor q with q ≢ 1 (mod p) — NOT in counterexample form"
                )

print("\n" + "=" * 60)
print("APPROACH 7: GN polynomial identity mod p")
print("=" * 60)

# GN(p, u, y) mod p:
# GN = Σ C(p,k+1) u^k y^{p-1-k}
# For p prime: C(p,k+1) ≡ 0 mod p for 1 ≤ k+1 ≤ p-1
# C(p,1) = p ≡ 0, C(p,2) ≡ 0, ..., C(p,p-1) ≡ 0, C(p,p) = 1
# So GN ≡ u^{p-1} mod p (since only the k=p-1 term survives)

# GN(p,u,y) ≡ u^{p-1} mod p
# In BranchA: gap = p^{p-1}*t^p ≡ 0 mod p
# So GN ≡ 0^{p-1} = 0 mod p ✓ (consistent with GN = p*s^p)

# More precisely: GN ≡ u^{p-1} + p*y^{p-1} mod p² (keeping next term)
# Since u = p^{p-1}*t^p ≡ 0 mod p^{p-1} and p ≥ 5 → p-1 ≥ 4 → u ≡ 0 mod p^4
# GN ≡ p*y^{p-1} mod p² → GN/p ≡ y^{p-1} mod p

# From GN = p*s^p: GN/p = s^p ≡ y^{p-1} mod p
# By Fermat: s^p ≡ s mod p and y^{p-1} ≡ 1 mod p (if gcd(y,p)=1)
# So s ≡ 1 mod p...?
# Wait: y^{p-1} ≡ 1 mod p by Fermat's little theorem (p prime, gcd(y,p)=1)
# And s^p ≡ s mod p (by Fermat)
# So s ≡ 1 mod p

# But the original assumption says ¬ p ∣ s. Let's check if s ≡ 1 mod p.

print("GN mod p² analysis:")
print(
    f"GN(p, u, y) ≡ u^(p-1) + p*y^(p-1) mod p² (when u is divisible by high power of p)"
)
print(f"For u = p^(p-1)*t^p: GN/p ≡ y^(p-1) mod p")
print(
    f"Since GN/p = s^p: s^p ≡ y^(p-1) mod p → s ≡ y^(p-1)/1 ... by FLT: y^(p-1) ≡ 1 mod p"
)
print(f"So s ≡ 1 mod p")

# Verify numerically
p = 5
for y in [1, 2, 3, 7, 11]:
    if y % p == 0:
        continue
    for t in [1, 2, 3]:
        gap = p ** (p - 1) * t**p
        gn = GN(p, gap, y)
        sp = gn // p
        s = round(sp ** (1 / p))
        for s_try in range(max(0, s - 2), s + 3):
            if s_try**p == sp:
                s = s_try
                break
        else:
            continue
        if s > 0:
            print(f"  p={p}, y={y}, t={t}: s = {s}, s mod p = {s % p}")

print("\nAll s ≡ 1 mod p ✓")

print("\n" + "=" * 60)
print("APPROACH 8: Wieferich-like conditions on q")
print("=" * 60)

# For each prime q | s with q ≡ 1 (mod p):
# Wieferich condition: y^{(q-1)/p} ≡ 1 mod q²? Or some other condition?

# In FLT context: gap·GN = x^p, q|s, so q^p | GN
# z^p ≡ y^p mod q → z/y has order dividing p in (Z/qZ)*
# z/y ≡ ω^j mod q where ω is a primitive p-th root mod q

# Also: z^p ≡ y^p mod q^p (since q^p | GN and gap·GN = z^p-y^p, and q∤gap)
# So z^p - y^p ≡ 0 mod q^p
# (z/y)^p ≡ 1 mod q^p
# Let r = z/y. Then r^p ≡ 1 mod q^p.
# r ≡ ω^j mod q.

# By lifting the exponent: v_q(r^p - 1) = v_q(r-1) + v_q(r+r+...+1) ...
# For r ≡ ω^j mod q where ω^j ≠ 1:
# r - 1 ≡ ω^j - 1 ≢ 0 mod q (if ω^j ≠ 1)
# Actually wait: r ≡ ω^j mod q and ω^j ≠ 1 → r ≢ 1 mod q
# But r^p ≡ 1 mod q^p means v_q(r^p - 1) ≥ p

# r^p - 1 = (r-1)(r^{p-1} + r^{p-2} + ... + 1)
# Since r ≡ ω^j mod q, ω^j ≠ 1:
#   v_q(r - 1) = 0 (since r ≡ ω^j ≠ 1 mod q)
#   So v_q(r^{p-1}+...+1) ≥ p

# But r^{p-1}+...+1 has degree p-1. How can v_q be ≥ p?

# r^{p-1}+...+1 = (r^p-1)/(r-1)
# v_q((r^p-1)/(r-1)) ≥ p
# v_q(r^p-1) - v_q(r-1) ≥ p
# v_q(r^p-1) ≥ p (since v_q(r-1) = 0)

# This means: the "Φ_p(r)" = r^{p-1}+...+1 has v_q ≥ p at r = z/y.

# Compare with the GENERIC case: for random r with r ≡ ω^j mod q (ω^j ≠ 1),
# we typically have v_q(Φ_p(r)) = 1 (single zero).
# The FLT context forces v_q(Φ_p(r)) ≥ p.

# THIS IS A VERY STRONG CONDITION!
# It means z/y is a "super-Wieferich" zero of Φ_p mod q^p.

print("Super-Wieferich condition analysis:")
print("In FLT context: v_q(Φ_p(z/y)) ≥ p where Φ_p(r) = r^{p-1}+...+1")
print("This is MUCH stronger than the generic v_q = 1.")
print()

# Let's study: how rare is v_q(Φ_p(r)) ≥ 2 for r ≡ ω^j mod q, ω^j ≠ 1?
p = 5
for q in [11, 31, 41, 61, 71, 101, 131, 151, 181, 191, 211, 241, 251]:
    if not isprime(q) or (q - 1) % p != 0:
        continue

    omega = pow(primitive_root(q), (q - 1) // p, q)

    # For each j ≠ 0 and r ≡ ω^j mod q, check v_q(Φ_p(r)) for r in range
    # r = ω^j + q*k, k = 0, 1, ..., q-1 → r mod q²

    high_valuation_found = False
    for j in range(1, p):
        r_base = pow(omega, j, q)
        for k in range(q):
            r = r_base + q * k
            # Compute Φ_p(r) = r^{p-1} + r^{p-2} + ... + 1
            phi = sum(r**i for i in range(p))
            vq = 0
            temp = phi
            while temp != 0 and temp % q == 0:
                vq += 1
                temp //= q
            if vq >= 2:
                if not high_valuation_found:
                    print(f"\nq={q}: High v_q(Φ_p(r)) cases:")
                    high_valuation_found = True
                if vq >= p:
                    print(
                        f"  j={j}, r={r} (mod {q**2}): v_{q}(Φ_{p}(r)) = {vq} {'★ FLT-compatible!' if vq >= p else ''}"
                    )
                elif vq >= 2:
                    # Just count these, don't print all
                    pass

    if not high_valuation_found:
        print(f"\nq={q}: No v_q(Φ_p(r)) ≥ 2 found for r ≡ ω^j mod q, 0 ≤ k < q")

# More targeted: count for each q how many r mod q² give v_q ≥ 2 and v_q ≥ p
print("\n" + "=" * 40)
print("Statistics: v_q(Φ_p(r)) for all r mod q²")
print("=" * 40)

for q in [11, 31, 41, 61]:
    if not isprime(q) or (q - 1) % p != 0:
        continue
    count_ge2 = 0
    count_gep = 0
    total = 0
    for j in range(1, p):
        r_base = pow(primitive_root(q), (q - 1) // p * j, q)
        for k in range(q):
            r = r_base + q * k
            total += 1
            phi = sum(r**i for i in range(p))
            vq = 0
            temp = phi
            while temp != 0 and temp % q == 0:
                vq += 1
                temp //= q
            if vq >= 2:
                count_ge2 += 1
            if vq >= p:
                count_gep += 1

    print(f"q={q}: total={total}, v≥2: {count_ge2}, v≥{p}: {count_gep}")
    if count_gep > 0:
        print(f"  → v≥{p} exists! FLT super-Wieferich condition is SATISFIABLE mod q²")
    else:
        print(f"  → v≥{p} NEVER occurs mod q² for r ≡ ω^j!!")
        print(f"     This would mean NO FLT counterexample can have this q!")

print("\n" + "=" * 60)
print("KEY QUESTION: For ALL q ≡ 1 (mod p), is v_q ≥ p impossible at mod q^p level?")
print("=" * 60)

# Extend to mod q^p (more refined)
# For p=5, q=11: check mod 11^5 = 161051
for q in [11]:
    q_p = q**p
    print(f"\nq={q}, q^p={q_p}")
    count_gep = 0
    total = 0

    omega = pow(primitive_root(q), (q - 1) // p, q)

    for j in range(1, p):
        r_base = pow(omega, j, q)
        # Need to check all r ≡ r_base mod q, r < q^p
        # That's q^{p-1} = 11^4 = 14641 values per j
        print(f"  j={j}: checking {q**(p-1)} values of r mod {q_p}...")
        found_any = False
        for r in range(r_base, q_p, q):
            phi = sum(r**i for i in range(p))
            vq = 0
            temp = phi
            while temp != 0 and temp % q == 0:
                vq += 1
                temp //= q
            total += 1
            if vq >= p:
                count_gep += 1
                if not found_any:
                    print(f"    FOUND: r={r}, v_{q}(Φ_{p}(r)) = {vq}")
                    found_any = True
        if not found_any:
            print(f"    NO r with v_q ≥ {p}")

    print(f"\n  Total checked: {total}, v≥{p}: {count_gep}")
    if count_gep == 0:
        print(f"  ★★★ v_q(Φ_p(r)) < p for ALL r ≡ ω^j mod q (j≠0)")
        print(f"  This means: (z/y)^{p-1}+...+1 cannot have v_q ≥ p")
        print(f"  Contradicting FLT counterexample requirement!")
        print(f"  → q={q} CANNOT appear as a primitive prime in an FLT counterexample!")
    else:
        print(f"  Super-Wieferich r values exist → q={q} is not directly excluded")
