#!/usr/bin/env python3
"""
GNReducedGapTarget の数学的構造を数値的に分析する。

GN(p, u, y) = sum_{k=0}^{p-1} C(p, k+1) * u^k * y^{p-1-k}
            = ((u+y)^p - y^p) / u

GNReducedGapTarget:
  Given: gap·GN(p,gap,y) = x^p where gap = p^{p-1}*t^p, GN = p*s^p, x = p*(t*s)
  Given: q | s, q∤t, q≠p, q prime, q^p | GN, p|(q-1)
  Given: ω^p = 1 in ZMod q, ω ≠ 1
  Show:  ∃ g', g' * GN(p, g', y) = p^p * (t * s/q)^p

Equivalently: (x/q)^p + y^p = z'^p for some z'.

We analyze the structure of GN modulo q, and what ω tells us about z mod q.
"""

from sympy import (
    binomial,
    factorint,
    isprime,
    gcd,
    primitive_root,
    Mod,
    nextprime,
    isprime,
    primerange,
)
from sympy.ntheory import n_order
import sys


def GN(p, u, y):
    """Compute GN(p, u, y) = sum_{k=0}^{p-1} C(p,k+1) * u^k * y^{p-1-k}"""
    return sum(binomial(p, k + 1) * u**k * y ** (p - 1 - k) for k in range(p))


def verify_GN_identity(p, u, y):
    """Verify: u * GN(p, u, y) = (u+y)^p - y^p"""
    lhs = u * GN(p, u, y)
    rhs = (u + y) ** p - y**p
    assert lhs == rhs, f"Identity failed: {lhs} != {rhs}"


def find_primitive_primes(p, a, b):
    """Find primitive prime factors of a^p - b^p (i.e., q∤(a-b), q|(a^p-b^p))"""
    diff = a**p - b**p
    gap = a - b
    factors = factorint(diff)
    primitives = []
    for q, e in factors.items():
        if gap % q != 0:
            primitives.append((q, e))
    return primitives


def analyze_gnreducedgap(p, y_val, t_val, s_val):
    """
    Analyze GNReducedGap for specific values.

    Setup:
      gap = p^{p-1} * t^p
      GN = p * s^p  (from the normal form)
      x = p * t * s
      z = gap + y

    Check: x^p + y^p = z^p (this won't hold for arbitrary values,
           but the structure is what matters)
    """
    gap = p ** (p - 1) * t_val**p
    z_val = gap + y_val
    x_val = p * t_val * s_val

    # Compute actual GN
    gn_actual = GN(p, gap, y_val)
    gn_normal = p * s_val**p

    # Check if the normal form holds
    # gap * GN = x^p is the ideal condition
    # In reality, gap * gn_actual = z^p - y^p
    lhs = gap * gn_actual
    rhs = z_val**p - y_val**p

    print(f"\n=== p={p}, y={y_val}, t={t_val}, s={s_val} ===")
    print(f"  gap = {gap}")
    print(f"  z = {z_val}")
    print(f"  x = {x_val}")
    print(f"  GN(p, gap, y) = {gn_actual}")
    print(f"  p * s^p = {gn_normal}")
    print(f"  gap * GN = {lhs}")
    print(f"  z^p - y^p = {rhs}")
    print(f"  z^p = {z_val**p}")
    print(f"  x^p + y^p = {x_val**p + y_val**p}")
    print(
        f"  z^p vs x^p+y^p: {'MATCH' if z_val**p == x_val**p + y_val**p else 'NO MATCH'}"
    )

    # Find primitive primes of GN
    if gn_actual > 0:
        gn_factors = factorint(gn_actual)
        print(f"  GN factorization: {gn_factors}")

        # Find q that divides s but not t
        s_factors = factorint(s_val) if s_val > 1 else {}
        for q in s_factors:
            if t_val % q != 0 and q != p and isprime(q):
                print(f"\n  --- Analyzing q = {q} ---")
                vq_GN = gn_factors.get(q, 0)
                vq_s = s_factors[q]
                s_prime = s_val // q
                print(f"  v_q(GN) = {vq_GN}")
                print(f"  v_q(s) = {vq_s}")
                print(f"  s' = s/q = {s_prime}")
                print(f"  p^p * (t*s')^p = {p**p * (t_val * s_prime)**p}")

                # Check ω existence: p | (q-1)?
                if (q - 1) % p == 0:
                    print(f"  p | (q-1): YES ({q}-1 = {q-1} = {p}*{(q-1)//p})")
                    # Find ω
                    g = primitive_root(q)
                    omega = pow(g, (q - 1) // p, q)
                    print(f"  ω = {omega} (primitive root of unity)")
                    print(f"  ω^p mod q = {pow(omega, p, q)}")

                    # z mod q
                    z_mod_q = z_val % q
                    y_mod_q = y_val % q
                    print(f"  z mod q = {z_mod_q}")
                    print(f"  y mod q = {y_mod_q}")
                    if y_mod_q != 0:
                        y_inv = pow(y_mod_q, q - 2, q)
                        r = (z_mod_q * y_inv) % q
                        print(f"  z/y mod q = {r}")
                        print(f"  r^p mod q = {pow(r, p, q)}")
                        # Find which power of ω gives r
                        for j in range(p):
                            if pow(omega, j, q) == r:
                                print(f"  z/y ≡ ω^{j} mod q")
                                break
                else:
                    print(f"  p | (q-1): NO")


print("=" * 60)
print("GNReducedGapTarget Numerical Analysis")
print("=" * 60)

# Basic identity verification
for p in [5, 7]:
    for u, y in [(2, 3), (1, 1), (3, 2)]:
        verify_GN_identity(p, u, y)
print("GN identity verified for all test cases ✓")

# Analyze structure for various parameters
# Note: these are NOT FLT counterexamples (none exist!)
# We're studying the algebraic structure of GN
for p in [5, 7]:
    for y_val in [1, 2, 3]:
        for t_val in [1, 2]:
            for s_val in [2, 3, 6, 10]:
                if gcd(t_val, s_val) == 1 and gcd(s_val, y_val) == 1:
                    if s_val % p != 0 and t_val % p != 0:
                        analyze_gnreducedgap(p, y_val, t_val, s_val)

print("\n" + "=" * 60)
print("DEEPER: GN structure in ZMod q")
print("=" * 60)


# Study GN(p, u, y) mod q^k for primitive q
def study_GN_modular(p, u, y, q, max_k=5):
    """Study v_q(GN(p, u, y)) and GN mod q^k"""
    gn = GN(p, u, y)
    if gn == 0:
        return
    print(f"\n  GN({p}, {u}, {y}) = {gn}")
    factors = factorint(gn)
    print(f"  Factorization: {factors}")
    vq = 0
    temp = gn
    while temp % q == 0:
        vq += 1
        temp //= q
    print(f"  v_{q}(GN) = {vq}")
    for k in range(1, min(vq + 2, max_k + 1)):
        print(f"  GN mod q^{k} = {gn % q**k}")


# Study: when does v_q(GN(p, u, y)) = 1 vs > 1?
print("\n--- v_q(GN) analysis for p=5 ---")
p = 5
for y in range(1, 20):
    for u in range(1, 50):
        gn = GN(p, u, y)
        if gn == 0:
            continue
        factors = factorint(gn)
        for q, e in factors.items():
            if u % q != 0 and q != p and e >= 2:
                # primitive q with v_q >= 2
                print(f"  p={p}, u={u}, y={y}: GN={gn}, q={q}, v_q={e}")
                # Check if this is consistent with gap*GN = x^p
                # i.e., is gap*GN a perfect p-th power?
                product = u * gn
                # Is product a p-th power?
                root = round(product ** (1 / p))
                for r in range(max(1, root - 2), root + 3):
                    if r**p == product:
                        print(f"    u*GN = {product} = {r}^{p} ← PERFECT p-th POWER!")
                        break

print("\n" + "=" * 60)
print("KEY: When is u*GN(p,u,y) a perfect p-th power?")
print("=" * 60)
# u*GN(p,u,y) = (u+y)^p - y^p
# So u*GN is a perfect p-th power IFF (u+y)^p - y^p = x^p IFF x^p + y^p = (u+y)^p
# This is FLT! If FLT is true, then u*GN is NEVER a perfect p-th power (for u,y > 0, p >= 3).
# Conversely, if u*GN = x^p then x^p + y^p = (u+y)^p is an FLT counterexample.

print("u*GN(p,u,y) = (u+y)^p - y^p")
print("This is a perfect p-th power IFF x^p + y^p = (u+y)^p")
print("Which is PRECISELY the FLT equation!")
print()
print("Therefore: GNReducedGapTarget asks for something that")
print("is false if FLT is true (in the non-counterexample context).")
print()
print("But in the DESCENT context:")
print("  We have gap·GN = x^p (from the counterexample)")
print("  We want: gap·(GN/q^p) to also be a 'body' for some gap g'")
print()
print("The key insight is that gap·GN = x^p already encodes FLT structure,")
print("and we need to show that dividing by q^p preserves this structure.")
print()
print("Specifically: gap·GN/q^p = (p*t*s/q)^p where x = p*t*s, q|s")
print("  = p^p * t^p * (s/q)^p")
print("  gap·GN/q^p = p^{p-1}*t^p * GN/(q^p)")
print("  But GN = p*s^p, so GN/q^p = p*s^p/q^p = p*(s/q)^p")
print("  So gap·GN/q^p = p^{p-1}*t^p * p*(s/q)^p = p^p * t^p * (s/q)^p")
print("  = p^p * (t * s/q)^p")
print()
print("The equation g'*GN(p,g',y) = p^p*(t*s')^p means:")
print("  (g'+y)^p - y^p = p^p*(t*s')^p")
print("  (g'+y)^p = p^p*(t*s')^p + y^p")
print("  Let z' = g'+y, x' = p*t*s'")
print("  Then z'^p = x'^p + y^p")
print()
print("So GNReducedGap iff ∃z' s.t. (x/q)^p + y^p = z'^p")
print()
print("IN THE COUNTEREXAMPLE CONTEXT: x^p + y^p = z^p")
print("  (x/q)^p + y^p = z^p - x^p + (x/q)^p + y^p")
print("               = z^p - x^p(1 - 1/q^p) + y^p")
print()
print("This is NOT automatically a perfect p-th power!")
print("The descent needs genuine arithmetic — this is the hard part.")

print("\n" + "=" * 60)
print("ω-based construction of g'")
print("=" * 60)

# In Z[ζ_p]: z^p - y^p = ∏_{i=0}^{p-1} (z - ζ^i * y)
# In ZMod q: z ≡ ω^j * y (some j, j≠0 since q∤(z-y))
# So z - ζ^j*y ≡ 0 mod q (in some sense)
# The ideal (z - ζ^j*y) absorbs most of q's contribution

# Elementary version: We know z ≡ ω^j*y mod q
# Define z' ≡ ω^j'*y mod q where we "remove one factor of q"
# More precisely: z' = z - (some correction term) that removes q from the gap

# KEY IDEA: If z ≡ ω^j * y (mod q), then
# z - ω^j*y ≡ 0 mod q
# gap = z - y, and z - y ≡ (ω^j - 1)*y mod q
# If ω^j ≠ 1 (which is guaranteed), then gap ≢ 0 mod q iff ω^j ≠ 1 in ZMod q

# The correction:
# z' should be such that (x/q)^p + y^p = z'^p
# In mod q: z'^p ≡ (x/q)^p + y^p mod q
# Since q|x: (x/q)^p ≡ 0 mod q iff p >= 1 and v_q(x/q) >= 1
# Wait: x = p*t*s, q|s, so x/q = p*t*(s/q)
# If v_q(s) = 1: x/q has no factor of q → (x/q)^p ≢ 0 mod q (unless q | p*t*(s/q))
# Since q∤t, q≠p, and (s/q) might or might not have q factor...
# If s has exactly one factor of q: v_q(s)=1, then s/q is coprime to q
# So x/q = p*t*(s/q) is coprime to q
# Then (x/q)^p + y^p ≡ (p*t*(s/q))^p + y^p mod q
# z'^p ≡ (p*t*(s/q))^p + y^p mod q

# And z^p ≡ x^p + y^p ≡ (p*t*s)^p + y^p ≡ y^p mod q (since q|x)
# Wait no: z^p = x^p + y^p, q|x → z^p ≡ y^p mod q → z ≡ ω^j*y mod q (some j)

# For z': z'^p ≡ (x/q)^p + y^p mod q
# (x/q) not divisible by q, so let a = (x/q)^p mod q
# z'^p ≡ a + y^p mod q
# a = ((p*t*s')^p mod q where s'=s/q
# This determines z' mod q (as a p-th root of a + y^p)

# The EXISTENCE of z' as a natural number such that z'^p = (x/q)^p + y^p
# is equivalent to (x/q)^p + y^p being a perfect p-th power.
# This is the hard part.

# Let's verify: for the classical Kummer descent, what structure is used?
print("\nClassical approach sketch:")
print("In Z[ζ_p]: x^p = (z-y)(z-ζy)(z-ζ²y)...(z-ζ^{p-1}y)")
print("If these ideals are coprime: each (z-ζ^i*y) = I_i^p for some ideal I_i")
print("Since Z[ζ_p] is a PID for regular p: I_i = (α_i) for some α_i")
print("So z - ζ^i*y = unit * α_i^p")
print()
print("The descent removes one prime ideal from the factorization.")
print("Elementary: we need to show the factorization is 'separable' mod q")
print()
print("The IDEA behind ω: z ≡ ω^j*y mod q means q divides (z - ω^j*y)")
print("in the sense of the cyclotomic factorization evaluated at ω.")
print()
print("CRITICAL QUESTION: Can we construct g' purely from ω and the given data?")
print()
print("If z = gap + y and z ≡ ω^j*y mod q:")
print("  gap ≡ (ω^j - 1)*y mod q")
print("  gap' (the new gap for z') = z' - y")
print("  z'^p = (x/q)^p + y^p")
print()
print("We need: gap'*GN(p,gap',y) = (x/q)^p = p^p*(t*s')^p")
print("This is a highly constrained Diophantine equation.")

# Let's try to understand what happens mod q for specific examples
print("\n" + "=" * 60)
print("MODULAR ANALYSIS: GN mod q for p=5")
print("=" * 60)

p = 5
for q in [11, 31, 41, 61, 71, 101]:
    if not isprime(q) or (q - 1) % p != 0:
        continue
    g = primitive_root(q)
    omega = pow(g, (q - 1) // p, q)
    print(f"\nq={q}, ω={omega}")

    # For each y coprime to q, find what GN looks like mod q
    for y in [1, 2, 3]:
        if y % q == 0:
            continue
        # GN(p, u, y) mod q as u varies
        # We know: u*GN(p,u,y) = (u+y)^p - y^p
        # mod q: u*GN ≡ (u+y)^p - y^p mod q
        # If q | GN: then (u+y)^p ≡ y^p mod q → (u+y)/y ≡ ω^j mod q for some j
        # i.e., u ≡ (ω^j - 1)*y mod q for some j ≠ 0

        for j in range(1, p):
            u_j = ((pow(omega, j, q) - 1) * y) % q
            gn_mod_q = GN(p, u_j, y) % q
            ugn_mod_q = (u_j * GN(p, u_j, y)) % q
            actual_ugn = (u_j + y) ** p - y**p
            print(
                f"  y={y}, j={j}: u≡{u_j} mod {q}, GN mod q = {gn_mod_q}, u*GN mod q = {ugn_mod_q}"
            )

            # Now compute v_q(GN(p, u, y)) for this specific u
            # u = u_j + q*k for various k
            for k in range(0, 3):
                u_full = u_j + q * k
                if u_full == 0:
                    continue
                gn_full = GN(p, u_full, y)
                if gn_full == 0:
                    continue
                vq = 0
                temp = gn_full
                while temp % q == 0:
                    vq += 1
                    temp //= q
                if vq >= 1:
                    print(f"    u={u_full}: v_{q}(GN) = {vq}, GN = {gn_full}")
