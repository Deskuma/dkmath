#!/usr/bin/env python3
"""
APPROACH G: Elementary cyclotomic descent via Cosmic Formula

Key mathematical insight:
  x^p + y^p = z^p in N
  ⟺ gap · GN(p, gap, y) = x^p   where gap = z - y, GN = Σ C(p,k+1) gap^k y^{p-1-k}

Normal form: gap = p^{p-1} t^p, GN = p s^p, x = p t s, gcd(t,s) = gcd(t,y) = gcd(s,y) = 1

In Z[ζ_p], the cyclotomic factorization gives:
  z^p - y^p = Π_{j=0}^{p-1} (z - ζ^j y) = x^p

The factor (z - y) = gap corresponds to j=0.
The product of remaining factors Π_{j=1}^{p-1} (z - ζ^j y) = GN as a norm.

APPROACH: Show that GN = p s^p with the coprimality conditions
forces a contradiction via the NORM STRUCTURE.

Specifically: GN = p s^p = N_{Q(ζ_p)/Q}(z - ζ y) / (z - y)  (up to units of Z[ζ_p])

In Z[ζ_p]:
  z - ζ y = (z - y) + (1 - ζ) y = gap + (1 - ζ) y

The ideal (z - ζ y) = P^a · A  where P = (1-ζ) is the prime above p,
and A is an ideal with gcd(A, P) = 1.

Since Π_{j=0}^{p-1} (z - ζ^j y) = x^p in the ideal sense:
  Each (z - ζ^j y) = P^{a_j} · A_j
  with Σ a_j = p v_P(x) and Π A_j = (x/p^{v_p(x)})^p in some sense.

For j ≠ k:
  (z - ζ^j y) - (z - ζ^k y) = (ζ^k - ζ^j) y = -ζ^k(1 - ζ^{j-k}) y
  v_P((ζ^k - ζ^j) y) = v_P(1 - ζ^{j-k}) = 1  (since j-k ≢ 0 mod p)

So (z - ζ^j y) and (z - ζ^k y) share EXACTLY the prime P (and nothing else,
assuming gcd(x, y) = 1).

KEY CONSEQUENCE: The ideals A_j are PAIRWISE COPRIME.

Therefore: A_0 · A_1 · ... · A_{p-1} = (x/P^{v_P(x)})^p (up to units)
And the A_j are pairwise coprime → each A_j is a p-th power ideal:
  A_j = B_j^p for some ideal B_j.

THE OBSTRUCTION: B_j may not be PRINCIPAL.
  A_j = B_j^p → A_j is in the trivial class (since it's principal: A_j | (z - ζ^j y))
  B_j^p is trivial → B_j is in the p-torsion of the class group.
  If p ∤ h (regular prime): B_j^p trivial ⟹ B_j trivial ⟹ B_j principal.
  If p | h (irregular prime): B_j might not be principal.

For the Cosmic Formula approach:
  GN = Π_{j=1}^{p-1} (z - ζ^j y) / ???

  Actually: z^p - y^p = (z-y) · GN(p, z-y, y)
  And: z^p - y^p = Π_{j=0}^{p-1} (z - ζ^j y)

  So: (z-y) · GN = (z-y) · Π_{j=1}^{p-1} (z - ζ^j y)
  (using z^p - y^p = (z-y) Σ z^i y^{p-1-i} and the cyclotomic factorization)

  Wait: Π_{j=0}^{p-1} (z - ζ^j y) = z^p - y^p
  (z - ζ^0 y) = z - y = gap
  Π_{j=1}^{p-1} (z - ζ^j y) = (z^p - y^p)/(z - y) = GN(p, gap, y)

  So GN(p, gap, y) = Π_{j=1}^{p-1} (z - ζ^j y)

  This is a product of p-1 algebraic integers in Z[ζ_p].

ELEMENTARY CONSEQUENCE:
  GN = Π_{j=1}^{p-1} (z - ζ^j y) ∈ Z  (it's a rational integer that lies in Z[ζ_p])

  Each factor z - ζ^j y = (z - y) + (1 - ζ^j) y = gap + (1 - ζ^j) y

  These are Z[ζ_p]-integers with specific structure.

APPROACH: Instead of working in Z[ζ_p], work with the
NORM of z - ζy as a polynomial in ζ.

z - ζ y is a FIRST-DEGREE polynomial in ζ.
Its norm over Q(ζ_p)/Q is:
  N(z - ζy) = Π_{j=0}^{p-1} (z - ζ^j y) = z^p - y^p = x^p

But we can also compute the norm as a RESULTANT:
  N(z - ζy) = Res(z - ζy, Φ_p(ζ)) · (-y)^{p-1}  ???

  Actually Φ_p(ζ) = 0, so N_{Q(ζ_p)/Q}(z - ζy) = Π_{j=1}^{p-1} (z - ζ^j y) = GN

  Wait: the norm over Q(ζ_p)/Q has degree p-1, so:
  N(z - ζy) = Π_{j=1}^{p-1} (z - ζ^j y) = GN

  (where j runs over j=1,...,p-1, the Galois conjugates of ζ)

So: N_{Q(ζ_p)/Q}(z - ζy) = GN

And GN = p s^p (from normal form).

The norm of z - ζy is p s^p.

Now, the ideal factorization of (z - ζy):
  (z - ζy) = P^{a} · Π_{q|s} Q_q^{b_q}

  where P is the unique prime above p, and Q_q are primes above the primitive primes q.

Taking norms: N(P^a) · Π N(Q_q^{b_q}) = p · s^p

N(P) = p (since P has ramification index p-1, residue degree 1: N(P) = p)
Wait: (p) = P^{p-1} in Z[ζ_p], so N(P) = p.

N(Q_q) = q for each prime above q (since q splits completely, each prime has norm q).

So: p^a · Π q^{b_q} = p · s^p

With a = v_P(z - ζy):
  z - ζy = gap + (1-ζ)y
  v_P(gap) = v_P(p^{p-1} t^p) = (p-1)^2 + p · v_P(t)
    (v_P(p) = p-1, so v_P(p^{p-1}) = (p-1)^2)
  v_P((1-ζ)y) = 1 + 0 = 1  (v_P(1-ζ) = 1, gcd(y,p)=1)

  If (p-1)^2 ≥ 2 (always for p ≥ 3):
    v_P(z - ζy) = min((p-1)^2 + ..., 1) = 1

  So a = 1.

  N(P^1) = p^1 = p. ✓ (matches the p factor in GN = p·s^p)

  So: Π q^{b_q} = s^p

  Since the primes above q all have norm q, and (z-ζy) is a single element:
  b_q = p · v_{Q_q}(z - ζy) / conjugate considerations...

  Actually, for a single prime Q above q in Z[ζ_p]:
    N(Q) = q (since q splits completely into p-1 distinct primes)
    If Q_1, ..., Q_{p-1} are the primes above q:
    v_{Q_j}(z - ζy) is related to v_q(z - ζ^j y)... actually it's more subtle.

    σ_j(z - ζy) = z - ζ^j y, and σ_j(Q_1) might not be Q_j.

  The key point: the norm of (z-ζy) over Q gives:
    Π_{j=1}^{p-1} (z - ζ^j y) = GN = p s^p

  Each (z - ζ^j y) in Z[ζ_p] has the property:
    v_{Q_{j_0}}(z - ζ^j y) ≥ p for the "right" prime Q above q
    v_{Q_other}(z - ζ^j y) = 0 for other primes above q

  Wait, this needs care. Let me be more precise.

  For a single factor (z - ζ y) (j=1):
    Its q-adic valuation structure:
    q splits as (q) = Q_1 · Q_2 · ... · Q_{p-1} in Z[ζ_p]
    Q_j corresponds to the embedding ζ ↦ ω^j mod q

    v_{Q_j}(z - ζ y) = v_q((z - ω^j y) in Z_q)

    From Hensel: v_q(z - R_{j_0} y) ≥ p for ONE j_0
                  v_q(z - R_j y) = 0 for j ≠ j_0

    So: v_{Q_{j_0}}(z - ζ y) ≥ p
        v_{Q_j}(z - ζ y) = 0 for j ≠ j_0

  OK this tells us: in the ideal factorization of (z - ζy):
    (z - ζy) = P · Q_{j_0}^{≥p} · (stuff coprime to q)

  Taking the ideal norm:
    N(z - ζy) = p · q^{≥p} · ...

  But N(z - ζy) = GN = p · s^p.

  If q appears exactly once in s (v_q(s) = 1):
    v_q(GN) = v_q(p · s^p) = p
    → q^p exactly in the norm
    → v_{Q_{j_0}}(z - ζy) = p exactly

  The ideal (z - ζy) then contains Q_{j_0}^p.

  Since ideals in Z[ζ_p] have unique factorization:
    (z - ζy) = P · Q_{j_0}^p · (other primes)^{p-th powers} · ...

  If all the prime factors of (z - ζy) appear with exponents that are multiples of p
  (except possibly P):
    (z - ζy) / (1-ζ) = unit · (something)^p
    in the ideal sense → A = B^p where A = (z - ζy)/(1-ζ) ideal.

  THIS IS KUMMER'S ARGUMENT!

  If A = B^p and the class group has no p-torsion:
    B is principal → B = (β) → A = (β^p) → z - ζy = ε(1-ζ)β^p

  This gives the descent: β determines a smaller solution.

NOW: Can we express this in ELEMENTARY terms using the Cosmic Formula?

The Cosmic Formula gives: GN = Σ C(p,k+1) gap^k y^{p-1-k}
The cyclotomic gives: GN = Π_{j=1}^{p-1} (z - ζ^j y)

The NORM-PRODUCT equivalence: GN = Π (z - ζ^j y) = polynomial in (z, y) over Z.

The descent condition:
  ∃ β ∈ Z[ζ_p] s.t. z - ζy = ε(1-ζ) β^p

This β has:
  N(β^p) = N(β)^p and N(z - ζy) = GN
  N(ε) = ±1, N(1-ζ) = p
  → N(β)^p = GN/p = s^p → N(β) = s

So β is a Z[ζ_p]-integer with norm s.

And: z - ζy = ε(1-ζ) β^p
  Expanding and comparing real/imaginary parts gives:
  z = Re(ε(1-ζ) β^p) under the appropriate embedding...

  Actually, this is better done by taking the "trace":
  Tr(z - ζy) = (p-1)z - y·Tr(ζ) = (p-1)z - y·(-1) = (p-1)z + y = ...
  Hmm, Tr(ζ) = sum of all primitive p-th roots = -1.
  So Tr(z - ζy) = (p-1)z + y.

  And: Tr(z - ζy) = Tr(ε(1-ζ)β^p)

  This gives an equation involving the trace of β^p.

ELEMENTARY REFORMULATION:
  Define β = a_0 + a_1 ζ + ... + a_{p-2} ζ^{p-2} ∈ Z[ζ_p]
  (using the power basis, with a_i ∈ Z)

  N(β) = s (a single diophantine equation in p-1 variables)
  z - ζy = ε(1-ζ) β^p (a system of p-1 equations comparing coefficients)

  This system has p-1 unknowns (a_0, ..., a_{p-2}) and p equations
  (norm condition + coefficient comparison).
  For p = 5: 4 equations, 3 unknowns → overdetermined → usually no solution.

  WAIT: p-1 equations from coefficient comparison + 1 norm equation.
  But the norm equation is algebraically dependent on the coefficient equations.
  So: p-1 independent equations in p-1 unknowns → 0-dimensional system → finitely many solutions.

  The question: does this system have a solution in Z^{p-1}?

  For REGULAR primes: yes, always (Kummer).
  For IRREGULAR primes: generally no (except for special values of (z,y)).

  BUT: we're supposed to be proving that no (x,y,z) counterexample EXISTS.
  So: IF the system β exists → descent → smaller counterexample → contradiction.
  And: IF no β exists → ... the counterexample is "stuck" (no descent possible).

  For the proof to work: we need descent to ALWAYS be possible.
  classical Kummer theory handles this for regular primes.

  FOR THE COSMIC FORMULA APPROACH:
  Can we show β EXISTS using the Cosmic polynomial structure?

  The GN polynomial Σ C(p,k+1) gap^k y^{p-1-k} = Π (z - ζ^j y)
  is a very SPECIFIC polynomial. Not every polynomial over Z is a product of cyclotomic factors.
  The special structure: it's SYMMETRIC in z and y (up to relabeling).
  More importantly: C(p,k+1) are BINOMIAL coefficients, which have special divisibility.

  Could the binomial coefficient structure force β to exist?

  For p=5: GN = 5y^4 + 10·gap·y^3 + 10·gap²·y² + 5·gap³·y + gap^4
           = Π_{j=1}^{4} (z - ζ^j y)

  In Z[ζ_5]: z - ζy is a 4th degree norm = GN.
  z - ζy = ε(1-ζ)β^5 requires β ∈ Z[ζ_5] of norm s with β^5 matching.
"""

# Let's compute the norm of z - ζy concretely for p=5
# and see if β can be found.

from sympy import Matrix, symbols, solve, Rational, sqrt

p = 5

# In Q(ζ_5): basis {1, ζ, ζ², ζ³}
# Minimal polynomial: ζ^4 + ζ^3 + ζ^2 + ζ + 1 = 0
# So ζ^4 = -ζ^3 - ζ^2 - ζ - 1

# z - ζy in the basis {1, ζ, ζ², ζ³}:
# = z - yζ
# = z·1 + (-y)·ζ + 0·ζ² + 0·ζ³

# (1 - ζ) in the basis:
# = 1·1 + (-1)·ζ + 0·ζ² + 0·ζ³

# β = a + bζ + cζ² + dζ³

# We need: z - ζy = ε·(1-ζ)·β^5
# For ε = 1 (simplest case):

# First, let's just verify the norm computation
# N(z - ζy) = Π_{j=1}^{4} (z - ζ^j y)

import numpy as np


def zeta_power(j, p=5):
    """Return ζ^j as e^{2πij/p}"""
    return np.exp(2j * np.pi * j / p)


# For specific z, y:
z, y_val = 100, 3
GN_val = sum(z**i * y_val ** (p - 1 - i) for i in range(p))
norm_val = 1.0
for j in range(1, p):
    factor = z - zeta_power(j, p) * y_val
    norm_val *= factor

print(f"z={z}, y={y_val}:")
print(f"  GN = Σ z^i y^{{p-1-i}} = {GN_val}")
print(f"  Π(z - ζ^j y) = {norm_val.real:.0f} + {norm_val.imag:.6f}i")
print(f"  Match: {abs(GN_val - norm_val.real) < 1 and abs(norm_val.imag) < 1}")

print()
print("=" * 60)
print("KUMMER DESCENT VIABILITY CHECK")
print("=" * 60)

# For the descent to work with the Cosmic Formula:
# 1. GN = p·s^p
# 2. z - ζy = ε·(1-ζ)·β^5 for some β ∈ Z[ζ_5]
# 3. N(β) = s

# Can we find β?
# For p=5: β = a + bζ + cζ^2 + dζ^3
# N(β) = Π_{j=1}^{4} σ_j(β) = Π_{j=1}^{4} (a + b·ζ^j + c·ζ^{2j} + d·ζ^{3j})

# And z - ζy = (1-ζ)(a + bζ + cζ^2 + dζ^3)^5

# This is a system of 4 equations (coefficients of 1, ζ, ζ^2, ζ^3)
# in 4 unknowns (a, b, c, d), plus the integer constraint.

# For small examples, try to find β numerically:


def multiply_in_cyclotomic(A, B, p=5):
    """Multiply two elements of Z[ζ_p] represented as coefficient lists."""
    # A = [a0, a1, ..., a_{p-2}], B = [b0, b1, ..., b_{p-2}]
    n = p - 1
    C = [0] * (2 * n - 1)
    for i in range(n):
        for j in range(n):
            C[i + j] += A[i] * B[j]
    # Reduce using ζ^{p-1} = -ζ^{p-2} - ... - ζ - 1
    result = list(C[:n])
    for k in range(n, len(C)):
        # ζ^k = ζ^{k mod cycle} but need reduction
        # ζ^{p-1} = -1 - ζ - ζ^2 - ... - ζ^{p-2}
        # More generally: ζ^{p-1+m} = ζ^m · ζ^{p-1} = -ζ^m (1 + ζ + ... + ζ^{p-2})
        # Actually simpler: just reduce one step at a time
        # ζ^{p-1} = -(1 + ζ + ... + ζ^{p-2})
        excess = C[k]
        for i in range(n):
            result[i] -= excess
    return result


def power_in_cyclotomic(A, exp, p=5):
    """Compute A^exp in Z[ζ_p]."""
    n = p - 1
    result = [0] * n
    result[0] = 1  # identity = 1
    base = list(A)
    while exp > 0:
        if exp % 2 == 1:
            result = multiply_in_cyclotomic(result, base, p)
        base = multiply_in_cyclotomic(base, base, p)
        exp //= 2
    return result


def norm_in_cyclotomic(A, p=5):
    """Compute N(A) = Π σ_j(A) for j=1,...,p-1."""
    n = p - 1
    val = 1.0 + 0j
    for j in range(1, p):
        zeta_j = zeta_power(j, p)
        sigma_A = sum(A[k] * zeta_j**k for k in range(n))
        val *= sigma_A
    return round(val.real)


# Test: element (1 - ζ)
one_minus_zeta = [1, -1, 0, 0]
print(f"\nN(1-ζ) = {norm_in_cyclotomic(one_minus_zeta)}")  # Should be p=5

# Compute (1-ζ) · β^5 for small β and check if it matches z - ζy

print("\nSearching for β with (1-ζ)β^5 = z - ζy...")
print("(Only checking small coefficients)")

found_any = False
# Try z - ζy = (1-ζ) β^5
# β = [a, b, c, d]
for a in range(-3, 4):
    for b in range(-3, 4):
        for c in range(-3, 4):
            for d in range(-3, 4):
                if a == 0 and b == 0 and c == 0 and d == 0:
                    continue
                beta = [a, b, c, d]
                beta5 = power_in_cyclotomic(beta, 5)
                product = multiply_in_cyclotomic(one_minus_zeta, beta5)
                # product should be [z, -y, 0, 0] for some z, y > 0
                if product[2] == 0 and product[3] == 0:
                    z_found = product[0]
                    y_found = -product[1]
                    if z_found > 0 and y_found > 0 and z_found > y_found:
                        s_val = norm_in_cyclotomic(beta)
                        gap = z_found - y_found
                        gn = sum(z_found**i * y_found ** (5 - 1 - i) for i in range(5))
                        # Check if GN = 5 * s^5
                        if gn == 5 * abs(s_val) ** 5:
                            print(f"  β = {beta}, N(β) = {s_val}")
                            print(f"  (1-ζ)β^5 gives z={z_found}, y={y_found}")
                            print(f"  gap = {gap}, GN = {gn}")
                            print(f"  5·s^5 = {5 * abs(s_val)**5}")
                            print(f"  GN == 5·s^5: {gn == 5 * abs(s_val)**5}")
                            x_cand = round((gap * gn) ** (1 / 5))
                            for xc in range(max(0, x_cand - 2), x_cand + 3):
                                if xc**5 == gap * gn:
                                    print(
                                        f"  x = {xc}, FLT check: {xc**5 + y_found**5 == z_found**5}"
                                    )
                                    break
                            found_any = True
                        elif (
                            product[2] == 0
                            and product[3] == 0
                            and y_found > 0
                            and z_found > y_found
                        ):
                            # Still interesting: these are potential descent targets
                            pass

if not found_any:
    print("  No β found with small coefficients. Expected for FLT!")

print("\n" + "=" * 60)
print("IMPORTANT REALIZATION")
print("=" * 60)
print(
    """
The search for β with (1-ζ)β^5 = z - ζy finding NO results is EXACTLY
what FLT predicts: there are no counterexamples, so no valid (z, y) pairs,
so no β to find.

The mathematical structure is:
1. IF counterexample (x,y,z) exists
2. THEN z - ζy = ε(1-ζ)β^p for some β (← this is what needs proof)
3. THEN N(β) = s and β determines a smaller counterexample
4. CONTRADICTION with minimality

Step 2 is the KEY: it's the class-group regularity condition.

FOR THE COSMIC FORMULA APPROACH:
  Instead of proving step 2 via class groups,
  can we prove it using the polynomial structure of GN?

  GN = Σ C(p,k+1) gap^k y^{p-1-k} = Π (z - ζ^j y)

  The BINOMIAL coefficients C(p,k+1) are not arbitrary: they satisfy:
  - C(p,k+1) ≡ 0 (mod p) for 0 ≤ k ≤ p-2  (since p is prime)
  - The p-divisibility is EXACTLY 1: v_p(C(p,k+1)) = 1

  This gives: GN ≡ 0 (mod p), and GN/p = Σ C(p,k+1)/p · gap^k · y^{p-1-k}
  where C(p,k+1)/p are integers.

  Can the structure of GN/p as a polynomial force it to be a perfect p-th power
  ONLY when the counterexample satisfies the descent condition?

  For p=5:
  GN/5 = y^4 + 2·gap·y^3 + 2·gap²·y² + gap³·y + (gap^4)/5
  Wait: C(5,1)=5, C(5,2)=10, C(5,3)=10, C(5,4)=5, C(5,5)=1
  GN/5 = y^4 + 2·gap·y^3 + 2·gap²·y² + gap³·y + gap^4/5
  
  But gap^4/5 needs to be integer! 
  gap = 5^4·t^5, so gap^4 = 5^{16}·t^{20}, gap^4/5 = 5^{15}·t^{20}. ✓

  GN/5 = y^4 + 2·(5^4·t^5)·y^3 + 2·(5^4·t^5)²·y² + (5^4·t^5)³·y + 5^{15}·t^{20}
  
  For this to be s^5: requires very specific divisibility patterns.
  
  The FIRST term is y^4. The LAST term is 5^{15}·t^{20}.
  If gcd(y, 5t) = 1: gcd(first, last) = 1.
  
  For s^5 = (relatively prime product):
  s = A·B where A | y^{4·something} and B | t^{20·something}·5^{15·something}?
  No, this is too crude.

  KEY INSIGHT from the cyclotomic factorization:
  GN/5 = (1/5) · Π_{j=1}^{4} (z - ζ^j y) in Z

  The factor 1/5 distributes into the product:
  (1-ζ_5)^4 has norm 5 in Z[ζ_5], and
  Π (z - ζ^j y) / 5 = [Π (z - ζ^j y)] / N(1-ζ)
  
  This can be written as a product of "symmetrized" factors,
  but the exact form depends on how the prime P = (1-ζ) factors.
"""
)

print("=" * 60)
print("CONCRETE NEXT STEP: NORM-PRODUCT DECOMPOSITION")
print("=" * 60)
print(
    """
Instead of the full Kummer descent, prove a WEAKER result elementarily:

PROPOSITION (Cyclotomic Norm-Product):
  If z^p = x^p + y^p with gcd(x,y) = 1, p ≥ 5 prime,
  and gap = z - y, GN = p·s^p:
  
  Then GN = Π_{j=1}^{p-1} (z - ζ^j·y) in Z[ζ_p],
  where z - ζ^j·y are pairwise "almost coprime" 
  (sharing only the prime (1-ζ) above p).

This can be proven ENTIRELY ELEMENTARILY:
  z^p - y^p = Π_{j=0}^{p-1} (z - ζ^j·y) is algebraic identity.
  z - ζ^0·y = gap, so Π_{j=1}^{p-1} (z - ζ^j·y) = (z^p - y^p)/gap = GN.
  
  Coprimality: for j ≠ k:
    gcd(z - ζ^j·y, z - ζ^k·y) | (ζ^k - ζ^j)·y
    And |(ζ^k - ζ^j)·y| generates an ideal dividing p·(y) in Z[ζ_p]

THIS PROPOSITION IS FORMALIZABLE IN LEAN using:
  1. Mathlib's Polynomial.cyclotomic API
  2. ZMod arithmetic for the reduction mod q
  3. The existing CyclotomicProduct.lean infrastructure

Once formalized, it gives a CLEAN interface for:
  - The q-adic valuation analysis (§20)
  - The Hensel factorization structure
  - The descent existence question (formulated as N(β) = s)
"""
)
