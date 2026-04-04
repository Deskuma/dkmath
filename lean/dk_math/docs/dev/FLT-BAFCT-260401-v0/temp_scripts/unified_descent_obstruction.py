#!/usr/bin/env python3
"""
UNIFIED DESCENT KERNEL: 反例の直接矛盾を探る

2つの open kernel が同じ "descent existence" 問題であることが判明。
descent 自体を証明する代わりに、反例の存在が直接矛盾する方法を探る。

Key idea: 最小性 + Cosmic normal form + primitive prime structure
→ 何らかの不等式 or 整除性矛盾

Approach A: SIZE CONTRADICTION
  最小反例 (x, y, z) with z 最小:
  - gap = p^{p-1} * t^p
  - GN = p * s^p
  - x = p * t * s
  - gcd(t,s) = gcd(t,y) = gcd(s,y) = 1
  - s has only primes ≡ 1 (mod p)
  - z = gap + y = p^{p-1}*t^p + y

  z^p = x^p + y^p < 2*max(x,y)^p
  z < 2^{1/p} * max(x,y)

  z = p^{p-1}*t^p + y
  x = p*t*s

  From z^p = x^p + y^p:
  (p^{p-1}*t^p + y)^p = (p*t*s)^p + y^p

  For y small relative to gap: z ≈ p^{p-1}*t^p ≈ gap
  z^p ≈ gap^p = p^{p(p-1)} * t^{p^2}
  x^p = p^p * t^p * s^p

  gap^p / x^p = p^{p(p-1)} * t^{p^2} / (p^p * t^p * s^p)
              = p^{p^2-2p} * t^{p^2-p} / s^p

  Since z^p ≈ gap^p ≈ x^p + y^p ≈ x^p (for large x):
  gap^p ≈ x^p → p^{p(p-1)} * t^{p^2} ≈ p^p * t^p * s^p
  → p^{p^2-2p} * t^{p^2-p} ≈ s^p
  → s ≈ p^{(p^2-2p)/p} * t^{(p^2-p)/p} = p^{p-2} * t^{p-1}

  For p=5: s ≈ 5^3 * t^4 = 125 * t^4

  This gives: x = p*t*s ≈ 5*t*125*t^4 = 625*t^5

Approach B: PRIMITIVE PRIME PRODUCT BOUND
  s has only primes q ≡ 1 (mod p), each with q ≥ p+1.
  For p=5: each prime factor of s is ≥ 11.
  s ≈ 125 * t^4 must be composed of primes ≡ 1 (mod 5): 11, 31, 41, 61, 71, ...

  For t=1: s ≈ 125. But s must be composed of primes ≡ 1 (mod 5).
  Primes ≡ 1 (mod 5): 11, 31, 41, 61, 71, 101, 131, 151, ...
  Can 125 be approximated? 11*11 = 121 ≈ 125, or 11*12... no, 31*4...
  Closest: 11^2 = 121, 11*31 = 341 (too big)
  So s ∈ {11, 31, 41, 61, 71, ..., 11^2=121, 11*31=341, ...}
  s must also satisfy s ≡ 1 (mod p) = 1 (mod 5)

  This is getting interesting. Let's check which values of s are valid.

Approach C: KUMMER'S CRITERION via elementary means
  The classical result: if p is regular (p ∤ h(Q(ζ_p))) then FLT(p) is true.

  Regular primes: 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 43, 47, 53, 61, 67, 71, 73, 79, 83, 89, 97, ...
  (All primes < 100 except 37, 59, 67 are regular)
  Wait: irregular primes below 100: 37, 59, 67

  For REGULAR p, the descent works because Z[ζ_p] is a UFD (for class number purposes).

  Elementary approach to regularity:
  The Bernoulli number criterion: p is regular iff p ∤ numerator of B_k for k = 2, 4, ..., p-3

  For the CODEBASE: could we add the regularity criterion as an axiom/assumption?

  Actually: FLT is already proven for ALL primes by Wiles.
  The codebase is trying to prove it elementarily.
  Restricting to regular primes would be a useful MILESTONE.

Approach D: FERMAT QUOTIENT OBSTRUCTION
  In the counterexample: z^p ≡ y^p (mod q) for each primitive prime q.
  By FLT (Fermat's little theorem): z^{q-1} ≡ 1, y^{q-1} ≡ 1 (mod q).
  Since p | (q-1): z^p, y^p are p-th powers in (Z/qZ)*.

  Stronger: z^p ≡ y^p (mod q^p) from v_q(GN) ≥ p.

  Define the Fermat quotient: f_q(a) = (a^{q-1} - 1) / q

  Wieferich pair condition: z^p ≡ y^p (mod q^2) →
  a^{q-1} ≡ 1 (mod q^2) → Wieferich prime hypothesis

  Actually the relevant condition is:
  (z/y)^p ≡ 1 (mod q^p)

  Let r = z/y mod q (= ω^j). Then:
  r^p ≡ 1 (mod q), so r has order dividing p in (Z/qZ)*.

  The "super-Wieferich" condition: r^p ≡ 1 (mod q^p)
  This is much stronger than the standard Wieferich condition.

Approach E: PRODUCT FORMULA OBSTRUCTION
  gap · GN = x^p = (p*t*s)^p = p^p * t^p * s^p
  gap = p^{p-1} * t^p
  GN = p * s^p

  From these:
  t^p * p^{p-1} * p * s^p = p^p * t^p * s^p ✓ (identity)

  This is just a tautology. No contradiction from here.

  The content is in the FACTORIZATION of GN = p * s^p.
  s^p = GN/p = (GN as polynomial in gap, y) / p

  For s to be a natural number with s^p = GN/p:
  1. p | GN (we proved this: GN ≡ gap^{p-1} mod p, and gap ≡ 0 mod p)
  2. GN/p is a perfect p-th power

  Condition 2 is the content of the normal form.

  Can we derive a contradiction from:
  - GN(p, gap, y)/p = s^p
  - s has only primes ≡ 1 (mod p)
  - gcd(s, y) = 1
  - s ≡ 1 (mod p)
  ?

Approach F: CONGRUENCE OBSTRUCTION
  We established: s ≡ 1 (mod p)
  And each prime factor q of s satisfies q ≡ 1 (mod p).

  From Φ_p(z/y) = GN/y^{p-1}:
  In (Z/qZ)*: Φ_p(ω^j) = 0 (mod q) for some j

  But we need: Φ_p(z/y) ≡ 0 (mod q^p)
  i.e., z/y ≡ R_j (mod q^p) (Hensel root)

  This gives: z = R_j · y + q^p · c_j for some integer c_j
  For each prime q_i | s: z = R_{j_i} · y + q_i^p · c_i

  By CRT: z ≡ something definite mod (∏ q_i^p)

  And z = gap + y = p^{p-1}*t^p + y

  So: p^{p-1}*t^p ≡ (R_{j_i} - 1) · y (mod q_i^p) for each i

  Since gcd(y, q_i) = 1:
  t^p ≡ (R_{j_i} - 1) · y / p^{p-1} (mod q_i^p)

  For each q_i: t^p (mod q_i^p) is DETERMINED by j_i.

  By CRT: t^p (mod ∏ q_i^p) is determined by (j_1, ..., j_k).

  But ∏ q_i^p = s^p (if each a_i = 1, i.e., s is squarefree).
  And t < s (roughly? not necessarily...)

  Actually: t and s are independent, gcd(t,s) = 1.
  t^p mod s^p is well-defined.

  QUESTION: is there a contradiction between
    t^p ≡ f(j_1,...,j_k) mod s^p
  and the size bound t < ???

  For s squarefree: ∏ q_i^p ≥ 11^p = 11^5 = 161051 if just one prime.
  And from s ≈ p^{p-2} * t^{p-1} = 125*t^4:
  s^p ≈ 125^5 * t^{20} for p=5

  And t^5 mod s^5... this gives a single congruence on t^5
  in a modulus of size s^5 ≈ 125^5 * t^{20}.
  Since t^5 << s^5 (when t < s^{1-δ} for some δ > 0):
  the congruence actually DETERMINES t^5.
  → t^5 = specific value ← must match with t being a natural number.
"""

from sympy import isprime, primitive_root, binomial, factorint, gcd
import math

p = 5

print("=" * 60)
print("Approach F: Congruence determination of t")
print("=" * 60)

# For p=5, s composed of primes ≡ 1 (mod 5)
# Smallest such primes: 11, 31, 41, 61, 71, 101

# Consider s = 11 (simplest case):
# GN/p = s^5 = 11^5 = 161051
# gap = p^{p-1}*t^p = 625*t^5
# GN = p*s^p = 5*161051 = 805255
# gap * GN = x^p = (5*t*11)^5 = (55*t)^5

# gap * GN = 625*t^5 * 805255 = 503284375 * t^5 = (55*t)^5 = 503284375 * t^5 ✓

# z = gap + y = 625*t^5 + y
# z^5 = x^5 + y^5 = (55*t)^5 + y^5

# From z ≡ R_j · y (mod 11^5):
# 625*t^5 + y ≡ R_j * y (mod 161051)
# 625*t^5 ≡ (R_j - 1) * y (mod 161051)

# For specific y, this determines t^5 mod 161051
# If t^5 < 161051: t^5 is exactly determined!
# t^5 < 161051 → t ≤ 10 (since 10^5 = 100000 < 161051)

# But we need gcd(t, 11) = 1 (since gcd(t,s) = 1)
# And gcd(t, y) = 1

print("For s = 11, p = 5:")
print("  s^5 = 161051")
print("  modulus: 11^5 = 161051")
print("  t^5 is determined mod 161051 when t ≤ 10")
print()

# For each j and y, compute what t must be:
q = 11
omega_q = pow(primitive_root(q), (q - 1) // p, q)


# Compute Hensel lift R_j mod q^5
def hensel_lift_phi_p(omega_j_mod_q, p, q, N):
    """Lift root ω^j of Φ_p(x) = x^{p-1}+...+1 from mod q to mod q^N."""
    r = omega_j_mod_q
    for k in range(1, N):
        phi = sum(r**i for i in range(p))
        phi_deriv = sum(i * r ** (i - 1) for i in range(1, p))
        residue = (phi // q**k) % q
        deriv_mod = phi_deriv % q
        deriv_inv = pow(deriv_mod, q - 2, q)
        c = (-residue * deriv_inv) % q
        r = r + c * q**k
    return r


for j in range(1, p):
    R_j = hensel_lift_phi_p(pow(omega_q, j, q), p, q, p)
    print(f"  j={j}: R_j mod 11^5 = {R_j}")

    for y in [1, 2, 3, 4, 6, 7, 8, 9]:
        if gcd(y, p) != 1 or gcd(y, q) != 1:
            continue

        # 625*t^5 ≡ (R_j - 1) * y mod 161051
        rhs = ((R_j - 1) * y) % (q**p)

        # t^5 ≡ rhs / 625 mod 161051
        inv_625 = pow(625, q**p - 2, q**p)  # Nope, q^p need not be prime
        # Actually q^p = 11^5 = 161051, which is not prime.
        # Use extended GCD for modular inverse
        from sympy import mod_inverse

        try:
            inv_625_mod = mod_inverse(625, q**p)
        except ValueError:
            print(f"    y={y}: 625 not invertible mod {q**p} (gcd = {gcd(625, q**p)})")
            continue

        t5_mod = (rhs * inv_625_mod) % (q**p)

        # Is t5_mod = t^5 for some small t?
        found_t = None
        for t in range(1, 15):
            if gcd(t, q) != 1 or gcd(t, y) != 1:
                continue
            if t**5 % (q**p) == t5_mod:
                found_t = t
                break

        if found_t:
            print(f"    y={y}: t^5 ≡ {t5_mod} mod {q**p} → t = {found_t}")
            # Verify the counterexample
            t_val = found_t
            gap = p ** (p - 1) * t_val**p
            z_val = gap + y
            x_val = p * t_val * q  # s = q = 11
            check = x_val**p + y**p == z_val**p
            print(f"      gap={gap}, z={z_val}, x={x_val}, FLT check: {check}")
        else:
            # check if t5_mod is a 5th power at all
            t_approx = round(t5_mod**0.2)
            is_5th = False
            for tc in range(max(0, t_approx - 2), t_approx + 3):
                if tc**5 == t5_mod:
                    is_5th = True
                    found_t = tc
                    break
            if is_5th and found_t > 0:
                print(
                    f"    y={y}: t^5 ≡ {t5_mod} mod {q**p} → t = {found_t} (but may need gcd checks)"
                )
            else:
                print(
                    f"    y={y}: t^5 ≡ {t5_mod} mod {q**p} → NO t with t^5 = {t5_mod} exists!"
                )
                print(f"      5th root approx: {t5_mod**(1/5):.2f}")

print("\n" + "=" * 60)
print("ANALYSIS: Multiple primitive primes give more constraints")
print("=" * 60)

# If s = 11 * 31 = 341:
# Both q1=11 and q2=31 are primitive primes
# t^5 ≡ const1 mod 11^5 AND t^5 ≡ const2 mod 31^5
# Combined: t^5 ≡ const mod (11*31)^5 = 341^5 ≈ 4.6 * 10^12
# If t < 341 (which is s): t^5 < 341^5 ≈ 4.6*10^12
# The CRT value is unique in [0, 341^5)
# So t^5 is EXACTLY determined, and must be a perfect 5th power

print("Multiple primes give tighter constraints:")
print("  s = 11*31 = 341 → CRT modulus = 341^5 ≈ 4.6e12")
print("  t must satisfy t^5 < 341^5 and t^5 ≡ specific value mod 341^5")
print("  → t^5 is UNIQUELY determined as the CRT value itself")
print("  → That CRT value must be a perfect 5th power")
print("  → This is an extremely strong condition!")
print()
print("  In general: if t < s (or t^p < s^p):")
print("  t^p is determined by CRT, and must be a perfect p-th power")
print("  The probability that a 'random' CRT value is a p-th power is ≈ 0")
print()

# But wait: is t < s always? No!
# From s ≈ 125*t^4 (for p=5), we get s >> t for large t.
# Actually s grows as t^4, so s > t for t > 1/(125)^{1/3} ≈ 0.2
# So s > t ALWAYS for positive t.

# This means the CRT always determines t^5 exactly!

print("Size analysis: s ≈ p^{p-2} * t^{p-1} = 125 * t^4 for p=5")
print("  So s^p ≈ 125^5 * t^{20}")
print("  And t^p = t^5")
print("  Ratio: s^p / t^p ≈ 125^5 * t^{15} → grows with t")
print("  So t^p << s^p always (for t ≥ 1)")
print("  → CRT exactly determines t^p")
print()

# KEY: The CRT value F(y, j_1, ..., j_k) must be a perfect p-th power.
# F depends on y and the choice of omega-indices j_1, ..., j_k.
# If for NO choice of (y, j_1, ..., j_k) is F a perfect p-th power,
# then no counterexample exists!

print("=" * 60)
print("OBSTRUCTION TEST: For s=11, is the CRT value ever a 5th power?")
print("=" * 60)

q = 11
s = q
sp = s**p  # CRT modulus

for j in range(1, p):
    R_j = hensel_lift_phi_p(pow(omega_q, j, q), p, q, p)

    fifth_power_found = False
    for y in range(1, 100):
        if gcd(y, p) != 1 or gcd(y, q) != 1:
            continue

        rhs = ((R_j - 1) * y) % sp
        try:
            inv_ppow = mod_inverse(p ** (p - 1), sp)
        except ValueError:
            continue

        t5_mod = (rhs * inv_ppow) % sp

        # Check if t5_mod is a perfect 5th power
        t_root = round(t5_mod**0.2)
        for tc in range(max(1, t_root - 2), t_root + 3):
            if tc**5 == t5_mod:
                if gcd(tc, q) == 1 and gcd(tc, y) == 1:
                    fifth_power_found = True
                    print(f"  j={j}, y={y}: t^5 = {t5_mod} → t = {tc} ★")
                    # But this is necessary but not sufficient for counterexample!
                    # We also need z^p = x^p + y^p
                    gap = p ** (p - 1) * tc**p
                    z_val = gap + y
                    x_val = p * tc * s
                    check = x_val**p + y**p == z_val**p
                    if check:
                        print(f"    ★★★ COUNTEREXAMPLE: x={x_val}, y={y}, z={z_val}")
                    else:
                        print(
                            f"    Not a real counterexample: {x_val}^5 + {y}^5 ≠ {z_val}^5"
                        )
                break

    if not fifth_power_found:
        print(f"  j={j}: NO y ∈ [1,100] gives t^5 as a perfect 5th power! ✓")

print("\n" + "=" * 60)
print("WHAT THIS MEANS")
print("=" * 60)

print(
    """
The CRT determination of t^p from the Hensel congruences is a 
NECESSARY condition for a counterexample.

If for a given s (primitive prime factorization), NO valid (y, j_1,...,j_k) 
gives a perfect p-th power for t^p, then that s CANNOT appear in a counterexample.

THIS IS A COMPUTATIONALLY VERIFIABLE OBSTRUCTION.

For a proof: we need to show that for ALL possible s and ALL choices of 
(y, j_1,...,j_k), the CRT value is NEVER a perfect p-th power.

This seems possible if the CRT value is "generically" not a p-th power.
But proving "never" requires a theoretical argument, not just computation.

POSSIBLE THEORETICAL ARGUMENT:
  The CRT value F(y, j) = [(R_j - 1) · y / p^{p-1}]^{1/p} ???
  For F to be a p-th power: very special algebraic condition on y vs R_j.
  Since R_j is a Hensel lift of ω^j (a p-th root of unity):
  R_j depends on the cyclotomic structure of Z_q / q^p·Z_q.

  The condition "F is a perfect p-th power" imposes a polynomial relation
  on y, t, and the R_j parameters. This is an algebraic variety.
  If the variety is 0-dimensional (finitely many solutions), 
  we could potentially enumerate and exclude all cases.
"""
)
