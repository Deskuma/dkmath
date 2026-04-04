#!/usr/bin/env python3
"""
PacketFromError 分析: peel descent (p | t) の核心

BranchA: x^p + y^p = z^p
- gap = p^{p-1} * t^p
- GN = p * s^p
- x = p * t * s

Peel case: p | t, so t = p * t1
- gap = p^{p-1} * (p*t1)^p = p^{2p-1} * t1^p
- x = p * (p*t1) * s = p^2 * t1 * s

Question: does the smaller packet with t1 give a valid counterexample?

gap' = p^{p-1} * t1^p  (reduced gap)
z' = gap' + y
x' = p * t1 * s  (reduced x)

Check: does gap' * GN(p, gap', y) = x'^p?

gap' * GN(p, gap', y) = (z')^p - y^p where z' = gap' + y
x'^p = (p * t1 * s)^p = p^p * t1^p * s^p

gap' * GN(p, gap', y) = p^{p-1} * t1^p * GN(p, gap', y)

For this to equal x'^p:
  p^{p-1} * t1^p * GN(p, gap', y) = p^p * t1^p * s^p
  GN(p, gap', y) = p * s^p  ?

But GN(p, gap', y) depends on gap' and y, NOT on s!
s was determined by the original counterexample: GN(p, gap, y) = p * s^p
Now with gap' ≠ gap, GN(p, gap', y) is different.

So the question: does GN(p, gap', y) = p * s'^p for some s'?
And does this give a valid normal form packet?
"""

from sympy import binomial, factorint, isprime, gcd


def GN(p, u, y):
    return sum(binomial(p, k + 1) * u**k * y ** (p - 1 - k) for k in range(p))


print("=" * 60)
print("PacketFromError: Peel Descent Analysis")
print("=" * 60)

p = 5

# Compare GN(p, gap, y) vs GN(p, gap', y)
# where gap = p^{2p-1} * t1^p and gap' = p^{p-1} * t1^p

for t1 in [1, 2, 3]:
    for y in [1, 2, 3, 7]:
        if gcd(y, p) != 1:
            continue

        gap = p ** (2 * p - 1) * t1**p  # original gap (with t = p*t1)
        gap_prime = p ** (p - 1) * t1**p  # reduced gap (with t1)

        gn_orig = GN(p, gap, y)
        gn_reduced = GN(p, gap_prime, y)

        # Check if GN is divisible by p
        if gn_orig % p != 0:
            print(f"t1={t1}, y={y}: GN_orig NOT divisible by p!")
            continue
        if gn_reduced % p != 0:
            print(f"t1={t1}, y={y}: GN_reduced NOT divisible by p!")
            continue

        s_orig_p = gn_orig // p
        s_reduced_p = gn_reduced // p

        # Check if they're perfect p-th powers
        def check_pth_power(n, p):
            s = round(n ** (1 / p))
            for s_try in range(max(0, s - 2), s + 3):
                if s_try**p == n:
                    return s_try
            return None

        s_orig = check_pth_power(s_orig_p, p)
        s_reduced = check_pth_power(s_reduced_p, p)

        print(f"\nt1={t1}, y={y}:")
        print(f"  gap  = {gap} (= 5^9 * {t1}^5)")
        print(f"  gap' = {gap_prime} (= 5^4 * {t1}^5)")
        print(f"  GN(p, gap, y) = {gn_orig}")
        print(f"  GN(p, gap', y) = {gn_reduced}")
        print(f"  GN_orig/p = {s_orig_p}, s = {s_orig}")
        print(f"  GN_reduced/p = {s_reduced_p}, s' = {s_reduced}")

        # Ratio
        ratio = gn_orig / gn_reduced
        print(f"  GN_orig / GN_reduced ≈ {ratio:.6f}")
        print(f"  (gap/gap')^{p-1} = {(gap/gap_prime)**(p-1):.6f}")

        # Key: what does peel actually DO?
        # Original: gap * GN = x^p = (p * (p*t1) * s)^p = p^{2p} * t1^p * s^p
        # Reduced: gap' * GN(p, gap', y) = z'^p - y^p where z' = gap' + y

        z_prime = gap_prime + y
        z_orig = gap + y

        lhs_reduced = gap_prime * gn_reduced
        rhs_check = z_prime**p - y**p

        print(f"  z  = {z_orig}")
        print(f"  z' = {z_prime}")
        print(f"  gap' * GN(p,gap',y) = {lhs_reduced}")
        print(f"  z'^p - y^p = {rhs_check}")
        print(f"  Match: {lhs_reduced == rhs_check}")

        # Is lhs_reduced a perfect p-th power?
        x_prime_cand = round(lhs_reduced ** (1 / p))
        is_pth_power = False
        for xc in range(max(0, x_prime_cand - 2), x_prime_cand + 3):
            if xc**p == lhs_reduced:
                x_prime_cand = xc
                is_pth_power = True
                break

        print(f"  gap' * GN_reduced = x'^p? {is_pth_power}", end="")
        if is_pth_power:
            print(f" (x' = {x_prime_cand})")
            # Check normal form: x' = p * t1 * s'?
            if x_prime_cand % p == 0:
                x_over_p = x_prime_cand // p
                print(f"  x'/p = {x_over_p}")
                if x_over_p % t1 == 0:
                    s_from_x = x_over_p // t1
                    print(f"  x'/(p*t1) = {s_from_x}")
                    if s_reduced and s_from_x == s_reduced:
                        print(f"  ★ Normal form matches! s' = {s_from_x}")
                    else:
                        print(f"  s_from_x = {s_from_x}, s_reduced = {s_reduced}")
        else:
            print()

print("\n" + "=" * 60)
print("Peel effect on GN: Taylor expansion")
print("=" * 60)

print(
    """
gap = p^{2p-1} * t1^p = p^p * gap'  where gap' = p^{p-1} * t1^p

GN(p, gap, y) = Σ C(p,k+1) * gap^k * y^{p-1-k}
             = Σ C(p,k+1) * (p^p * gap')^k * y^{p-1-k}
             = Σ C(p,k+1) * p^{pk} * (gap')^k * y^{p-1-k}
             
GN(p, gap', y) = Σ C(p,k+1) * (gap')^k * y^{p-1-k}

So: GN(p, gap, y) = Σ p^{pk} * [C(p,k+1) * (gap')^k * y^{p-1-k}]

This is NOT simply p^{p*m} * GN(p, gap', y) for any m!
Each term has a different power of p.

More carefully:
k=0: C(p,1) * y^{p-1} = p * y^{p-1}          -- p^0 factor
k=1: C(p,2) * p^p * gap' * y^{p-2}           -- p^p factor  
k=2: C(p,3) * p^{2p} * (gap')^2 * y^{p-3}   -- p^{2p} factor
...
k=p-1: C(p,p) * p^{p(p-1)} * (gap')^{p-1}    -- p^{p(p-1)} factor

For large p and gap' >> 1, the dominant term is k=p-1:
  GN ≈ p^{p(p-1)} * (gap')^{p-1}

So: GN(p, gap, y) ≈ p^{p(p-1)} * GN(p, gap', y) 
    ONLY if the BIG terms dominate (gap' >> y).

But the key relationship is:
  gap * GN(p, gap, y) = (gap + y)^p - y^p = z^p - y^p = x^p
  gap' * GN(p, gap', y) = (gap' + y)^p - y^p = z'^p - y^p

These are INDEPENDENT Cosmic identities. The peel doesn't directly transfer.

THE ERROR TERM:
  x^p = gap * GN = p^p * gap' * GN(p, p^p * gap', y)
  x'^p := gap' * GN(p, gap', y)
  
  x^p / x'^p = p^p * GN(p, p^p*gap', y) / GN(p, gap', y)
  
  This ratio ≠ p^{pp} in general.
"""
)

# Let's understand the error term E in the PacketFromError definition:
# p * B = C + (p^{p-1} * t1^p) * E
# What are B, C, E?
print("=" * 60)
print("Understanding the error term structure")
print("=" * 60)

# From the peel route:
# t = p * t1, gap = p^{2p-1} * t1^p
# GN(p, gap, y) = p * s^p
#
# gap' = p^{p-1} * t1^p
# z' = gap' + y
# GN(p, gap', y) = ?
#
# The peel operation:
# gap = p^p * gap'
# z = p^p * gap' + y
# z' = gap' + y
#
# GN(p, gap, y) = Σ C(p,k+1) * (p^p * gap')^k * y^{p-1-k}
# = C(p,1)*y^{p-1} + Σ_{k≥1} C(p,k+1) * p^{pk} * (gap')^k * y^{p-1-k}
#
# GN(p, gap', y) = C(p,1)*y^{p-1} + Σ_{k≥1} C(p,k+1) * (gap')^k * y^{p-1-k}
#
# Difference: GN(p, gap, y) - GN(p, gap', y)
# = Σ_{k≥1} C(p,k+1) * (gap')^k * y^{p-1-k} * (p^{pk} - 1)
#
# The p^{pk} - 1 factor: for k=1: p^p - 1, for k=2: p^{2p} - 1, etc.

p = 5
for t1 in [1]:
    for y in [1, 2, 3]:
        if gcd(y, p) != 1:
            continue
        gap_prime = p ** (p - 1) * t1**p
        gap = p**p * gap_prime

        gn_orig = GN(p, gap, y)
        gn_reduced = GN(p, gap_prime, y)

        print(f"\nt1={t1}, y={y}:")
        print(f"  GN(p, gap, y) = {gn_orig}")
        print(f"  GN(p, gap', y) = {gn_reduced}")

        # The k=0 term is the same
        k0_term = p * y ** (p - 1)
        print(f"  k=0 term: {k0_term}")

        # Difference by k
        for k in range(p):
            coeff = int(binomial(p, k + 1))
            term_orig = coeff * (gap) ** k * y ** (p - 1 - k)
            term_reduced = coeff * (gap_prime) ** k * y ** (p - 1 - k)
            diff = term_orig - term_reduced
            print(f"  k={k}: orig={term_orig}, reduced={term_reduced}, diff={diff}")
            if k >= 1:
                factor = p ** (p * k) - 1
                expected_diff = coeff * (gap_prime) ** k * y ** (p - 1 - k) * factor
                print(
                    f"         expected diff = {expected_diff}, match: {diff == expected_diff}"
                )

        # The error term E relates to these differences
        # In the BranchA normal form:
        # Original: GN = p * s^p → s^p = GN/p
        # Reduced: GN' = p * s'^p + ???

        # Actually: GN(p, gap', y) / p
        gn_div_p = gn_reduced // p
        remainder = gn_reduced % p
        print(f"  GN_reduced / p = {gn_div_p}, remainder = {remainder}")
        if remainder == 0:
            sp = check_pth_power(gn_div_p, p)
            if sp:
                print(f"  ★ GN_reduced = p * {sp}^{p}")
            else:
                print(f"  GN_reduced/p = {gn_div_p} is NOT a perfect {p}-th power")
                # Factor it
                factors = factorint(gn_div_p)
                print(f"  Factorization: {factors}")

print("\n" + "=" * 60)
print("KEY INSIGHT: v_p analysis of GN(p, gap', y)")
print("=" * 60)

# GN(p, gap', y) where gap' = p^{p-1} * t1^p
# k=0 term: p * y^{p-1}  → v_p = 1
# k=1 term: C(p,2) * gap' * y^{p-2} = C(p,2) * p^{p-1} * t1^p * y^{p-2} → v_p ≥ p (since C(p,2) = p(p-1)/2 has v_p = 1)
#   v_p(C(p,2)) = 1, v_p(gap') = p-1 → v_p = p ≥ 5
# k=2 term: C(p,3) * (gap')^2 * y^{p-3} → v_p ≥ 1 + 2(p-1) = 2p-1 ≥ 9
# ...
# So the k=0 term DOMINATES v_p: v_p(GN) = 1 (from k=0 term, since k≥1 terms all have v_p ≥ p)

# If gcd(y, p) = 1: y^{p-1} is coprime to p.
# So GN(p, gap', y) = p * y^{p-1} + (terms with v_p ≥ p)
# → v_p(GN) = 1 ✓ (consistent with GN = p * s'^p)

# Furthermore: GN / p = y^{p-1} + (terms with v_p ≥ p-1)
# → GN/p ≡ y^{p-1} mod p^{p-1}
# And by FLT: y^{p-1} ≡ 1 mod p
# So GN/p ≡ 1 mod p → s'^p ≡ 1 mod p → s' ≡ 1 mod p

print("v_p analysis for gap' = p^{p-1}*t1^p:")
for t1 in [1, 2]:
    for y in [1, 2, 3, 7]:
        if gcd(y, p) != 1:
            continue
        gap_prime = p ** (p - 1) * t1**p
        gn = GN(p, gap_prime, y)
        vp_gn = 0
        temp = gn
        while temp % p == 0:
            vp_gn += 1
            temp //= p
        gn_div_p = gn // p
        print(f"  t1={t1}, y={y}: v_p(GN) = {vp_gn}, GN/p mod p = {gn_div_p % p}")

print("\n" + "=" * 60)
print("PEEL DESCENT: The actual mathematical content")
print("=" * 60)

print(
    """
PacketFromError の数学:

Original: x^p + y^p = z^p with t = p*t1 (p|t)
  gap = p^{2p-1} * t1^p
  GN = p * s^p
  x = p^2 * t1 * s

Peeled gap: gap' = p^{p-1} * t1^p  (= gap / p^p)
  z' = gap' + y
  z'^p = (gap' + y)^p = y^p + gap' * GN(p, gap', y)

gap' * GN(p, gap', y) = z'^p - y^p

Question: is z'^p - y^p = some x'^p?

If yes: (x'^p + y^p = z'^p with z' = gap' + y < z)
  → smaller counterexample (since gap' = gap/p^p < gap → z' < z)
  → contradicts minimality

The peel doesn't need to produce x' = p*t1*s' directly!
It needs: z'^p - y^p is a perfect p-th power, i.e.,
  gap' * GN(p, gap', y) = x'^p for some x'.

Note: gap' * GN(p, gap', y) = (gap'+y)^p - y^p = z'^p - y^p

For this to be x'^p: z'^p = x'^p + y^p
Which is... ANOTHER FLT EQUATION!

So the peel descent also reduces to showing that 
z'^p - y^p is a perfect p-th power.

The ERROR TERM is about:
  z'^p - y^p = gap' * GN(p, gap', y)
  We need this = (x')^p for some x'.
  
  From the original: gap * GN(p, gap, y) = x^p
  x^p = p^p * gap' * GN(p, gap, y)
  
  If GN(p, gap, y) = p^{p(p-1)} * GN(p, gap', y) + ERROR:
  Then z'^p - y^p = gap' * GN(p, gap', y)
                  = gap' * (GN(p, gap, y) - ERROR) / p^{p(p-1)}
                  ... this doesn't simplify nicely.

ALTERNATIVE VIEW: 
  The peel is fundamentally about p-adic structure.
  With t = p*t1:
    v_p(x) = v_p(p^2 * t1 * s) = 2 + v_p(t1)  (since p∤s)
    v_p(gap) = 2p-1 + p*v_p(t1)  
    v_p(z) = v_p(gap + y). If gcd(y, p) = 1: v_p(z) = 0 (since gap ≡ 0 mod p but y ≢ 0)
    Wait: z = gap + y, gap ≡ 0 mod p, y ≢ 0 mod p → z ≡ y ≢ 0 mod p → v_p(z) = 0
    
    z^p = x^p + y^p
    v_p(z^p) = 0 (since v_p(z) = 0)
    v_p(x^p) = p * v_p(x) ≥ 2p ≥ 10
    v_p(y^p) = 0
    
    z^p = x^p + y^p → 0 = v_p(z^p) = v_p(x^p + y^p)
    x^p ≡ 0 mod p^{2p}, y^p ≢ 0 mod p
    → z^p ≡ y^p mod p → z ≡ y mod p (by Fermat? No, that's not right for p-th powers)
    Actually z^p ≡ y^p + x^p where x^p ≡ 0 mod p → z^p ≡ y^p mod p
    And since gcd(z,p) = gcd(y,p) = 1: z^p ≡ z mod p, y^p ≡ y mod p (Fermat)
    So z ≡ y mod p. ✓ (consistent with gap = z-y ≡ 0 mod p)

  The peel operation: reduce v_p(t) by 1.
  If t = p*t1: remove one factor of p from t.
  gap' = p^{p-1} * t1^p 
  v_p(gap') = p-1 + p*v_p(t1)
  
  z' = gap' + y
  v_p(z') = 0 (same argument: gap' ≡ 0 mod p, y ≢ 0)

  The question is: does the smaller (gap', y) pair give a valid counterexample?
  i.e., is z'^p - y^p a perfect p-th power?

THIS IS THE SAME TYPE OF QUESTION AS GNReducedGap!
Both ask: given (gap, y) satisfying the Cosmic normal form,
and a "reduced" gap gap' gotten by dividing by some p-th power factor,
is gap' * GN(p, gap', y) also a perfect p-th power?

The difference:
- GNReducedGap: divide GN by q^p (primitive prime reduction)
- PacketFromError: divide gap by p^p (p-adic peel)

Both reduce to: (x')^p + y^p = z'^p for some x' < x, z' < z.

IN BOTH CASES, the mathematical difficulty is the same:
showing that a "reduced" FLT-like expression remains a perfect p-th power.
"""
)

print("=" * 60)
print("UNIFIED VIEW: Both open kernels are descent existence problems")
print("=" * 60)

print(
    """
Open Kernel 1: GNReducedGap
  ∃ z', z'^p = (x/q)^p + y^p   (q: primitive prime, q ∤ gap)

Open Kernel 2: PacketFromError  
  ∃ z', z'^p = gap'/p^{p-1} * GN(p, gap', y) + y^p  where gap' = gap/p^p
  
  But gap' * GN(p, gap', y) = z'^p - y^p, and if this = (x')^p:
  z'^p = (x')^p + y^p

  What is x'? x' = (gap' * GN(p, gap', y))^{1/p}
  In the original: x = (gap * GN)^{1/p} = (p * gap' * p^{p-1} * ... hm)
  
  Actually let's be precise:
  gap * GN(p, gap, y) = x^p
  gap = p^{2p-1} * t1^p (since t = p*t1)
  x = p^2 * t1 * s
  
  gap' = p^{p-1} * t1^p
  x' should satisfy: gap' * GN(p, gap', y) = x'^p
  
  This x' is NOT simply x/p. It's determined by the new Cosmic identity.

UNIFIED MATHEMATICAL STRUCTURE:
  Both kernels are instances of the question:
  "Given a valid counterexample (x, y, z) with z^p = x^p + y^p,
   produce a SMALLER counterexample (x', y, z') with z'^p = x'^p + y^p
   by factoring out some prime power from x or gap."

  This is INFINITE DESCENT on the Fermat equation.
  The classical obstruction is the class number of Q(ζ_p).
  
  For regular primes (p ∤ h(Q(ζ_p))): descent works → FLT(p) proven (Kummer 1850)
  For irregular primes: more work needed (Vandiver, Iwasawa, ... Wiles)

IMPLICATION FOR OUR CODEBASE:
  The 2 open kernels are REALLY just 1 kernel in 2 flavors:
  "descent existence" — proving that the reduced equation has a solution.
  
  If we can prove descent for ONE flavor, the other likely follows by similar methods.
  The q-adic (primitive) version has more algebraic structure (via ω and Hensel),
  so it's the better attack point.
"""
)
