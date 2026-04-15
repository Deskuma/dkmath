#!/usr/bin/env python3
"""
核心分析: FLT反例文脈で x'^p + y^p が p-th power mod q になるか？

FLT 文脈の制約:
1. x^p + y^p = z^p
2. q | x (primitive prime)
3. x' = x/q
4. z ≡ ω^j · y (mod q)
5. q ≡ 1 (mod p)

これらの制約がどう x'^p + y^p mod q を決めるか分析する。
"""

from sympy import isprime, primitive_root, gcd


def pow_mod(base, exp, mod):
    return pow(base, exp, mod)


print("=" * 60)
print("FLT 文脈における x'^p + y^p mod q の解析")
print("=" * 60)

p = 5

for q in [11, 31, 41, 61, 71, 101, 131, 151, 181, 191]:
    if not isprime(q) or (q - 1) % p != 0:
        continue

    g = primitive_root(q)
    omega = pow(g, (q - 1) // p, q)

    # p-th powers mod q
    pth_powers = set()
    for a in range(q):
        pth_powers.add(pow(a, p, q))

    print(f"\n{'='*50}")
    print(f"q = {q}, p = {p}, ω = {omega}")
    print(f"p-th powers mod q: {sorted(pth_powers)}")

    # FLT constraints:
    # z ≡ ω^j · y mod q (some j ∈ {1,...,p-1})
    # x ≡ 0 mod q
    # x^p + y^p = z^p
    # → (ω^j·y)^p ≡ y^p mod q (since x^p ≡ 0)
    # → ω^{jp}·y^p ≡ y^p mod q
    # → ω^{jp} ≡ 1 mod q
    # This is automatic: ω^p = 1, so ω^{jp} = (ω^p)^j = 1. ✓

    # Now: x' = x/q, and x' mod q determines everything
    # From x = p*t*s, q|s, s = q*s':
    #   x' = p*t*s'
    #   x' mod q = (p*t*s') mod q

    # Key constraint from FLT:
    # x^p + y^p = z^p
    # x = q * x'
    # (q*x')^p + y^p = z^p
    # q^p * x'^p + y^p = z^p
    # z^p - y^p = q^p * x'^p
    # gap * GN = q^p * x'^p  (where gap = z - y, GN = x^p/gap)

    # Mod q: z^p ≡ y^p → z ≡ ω^j*y
    # z - y ≡ (ω^j - 1)*y mod q
    # gap ≡ (ω^j - 1)*y mod q
    # Since q ∤ gap: ω^j ≠ 1 → j ≠ 0 ✓

    # Mod q: z^p - y^p ≡ 0, and this equals q^p * x'^p
    # So q^p * x'^p ≡ 0 mod q → trivially true since q^p ≡ 0 mod q

    # Mod q²: z^p ≡ y^p + q^p*x'^p
    # But q^p ≡ 0 mod q² (since p ≥ 5 ≥ 2)
    # So z^p ≡ y^p mod q²
    # And z ≡ ω^j*y mod q, so (ω^j*y)^p ≡ y^p mod q² → trivially true in this ring

    # Actually let's be more precise:
    # z = ω_lift^j * y + q * c for some integer c
    # where ω_lift is some integer lifting of ω

    # z^p = (ω_lift^j * y + q*c)^p
    #      = (ω_lift^j * y)^p + p * (ω_lift^j * y)^{p-1} * q*c + O(q²)
    # z^p ≡ (ω_lift^j)^p * y^p + p * (ω_lift^j)^{p-1} * y^{p-1} * q*c mod q²

    # Also z^p = q^p * x'^p + y^p
    # mod q²: z^p ≡ y^p (since q^p ≡ 0 mod q² for p≥2)

    # So: (ω_lift^j)^p * y^p + p * (ω_lift^j)^{p-1} * y^{p-1} * q*c ≡ y^p mod q²
    # → (ω_lift^{jp} - 1) * y^p ≡ -p * (ω_lift^j)^{p-1} * y^{p-1} * q * c mod q²

    # ω^p = 1 mod q, so ω_lift^p = 1 + q*d for some d
    # ω_lift^{jp} = (1 + q*d)^j = 1 + j*q*d + O(q²) ≡ 1 + j*q*d mod q²

    # So: j*q*d * y^p ≡ -p * ω_lift^{j(p-1)} * y^{p-1} * q * c mod q²
    # → j*d * y^p ≡ -p * ω_lift^{j(p-1)} * y^{p-1} * c mod q
    # → j*d * y ≡ -p * ω_lift^{j(p-1)} * c mod q

    # This gives a relation between c and d.
    # c = z_mod_q2_remainder, d = (ω_lift^p - 1)/q

    # The key point: x' mod q is NOT determined by mod-q data alone.
    # It depends on the q-adic structure of x, z, y.

    # But we can ask: GIVEN the FLT constraints, what values can x'^p + y^p take mod q?

    # In FLT context:
    # z^p = (q*x')^p + y^p → z^p - y^p = q^p * x'^p
    # z ≡ ω^j * y mod q

    # x'^p + y^p = z^p / q^p ... but z^p/q^p is not z^p in ZMod q!
    # We need z'^p = x'^p + y^p where z' is the NEW value.

    # The question: does z' exist?
    # x'^p + y^p mod q = x'^p + y^p mod q
    # For this to be z'^p, we need x'^p + y^p to be a p-th power mod q.

    # In FLT: q|x → x ≡ 0 → x^p ≡ 0 → z^p ≡ y^p
    # x' is coprime to q. What is x' mod q?

    # From gap * GN = x^p and gap * GN = q^p * x'^p:
    # gap * GN / q^p = x'^p
    # x'^p mod q = (gap * GN / q^p) mod q

    # But q^p | GN (from the structure), and q ∤ gap:
    # GN / q^p mod q = ?
    # GN = q^p * (GN/q^p), and GN/q^p might or might not be divisible by q

    # In normal form: GN = p * s^p, q | s, so GN = p * q^p * (s/q)^p
    # GN/q^p = p * (s/q)^p
    # If v_q(s) = 1: GN/q^p = p * (s')^p where gcd(s', q) = 1
    # So GN/q^p mod q = p * (s')^p mod q

    # x'^p = gap * GN/q^p = gap * p * (s')^p
    # = p^{p-1} * t^p * p * (s')^p = p^p * t^p * (s')^p = p^p * (t*s')^p
    # So x' = p * t * s' (this is just x/q)

    # x'^p mod q = (p * t * s')^p mod q
    # This is a NONZERO p-th power mod q (since gcd(x', q) = 1)

    # So x'^p mod q is automatically a p-th power.
    # And y^p mod q is automatically a p-th power.
    # But their SUM may not be!

    print(
        f"\nChecking: a^p + b^p where a,b coprime to q — is it always a p-th power mod q?"
    )

    # Count: how many (a^p, b^p) pairs give a p-th power sum?
    nonzero_pp = sorted(pth_powers - {0})
    total = 0
    success = 0
    for ap in nonzero_pp:
        for bp in nonzero_pp:
            total += 1
            s = (ap + bp) % q
            if s in pth_powers:
                success += 1

    print(f"  Nonzero p-th powers: {nonzero_pp}")
    print(f"  a^p + b^p ∈ p-th powers: {success}/{total}")

    # In FLT context: a^p + b^p ≡ 0 mod q (since z^p ≡ y^p + x^p ≡ y^p mod q)
    # Wait NO! z^p = x^p + y^p where x = q*x'
    # z'^p = x'^p + y^p
    # z'^p mod q: we need to compute this DIFFERENTLY.

    # The key: in FLT, z^p = (q*x')^p + y^p
    # z ≡ ω^j * y mod q
    # So z^p mod q^{p+1}:
    # z = ω_lift^j * y + q * α (for some α)
    # z^p = (ω_lift^j * y)^p + p*(ω_lift^j * y)^{p-1}*q*α + ... (mod q²)

    # Actually, let me think about this more carefully.
    # z^p = q^p * x'^p + y^p
    # This means z^p - y^p = q^p * x'^p

    # z' does NOT need to satisfy z'^p = x'^p + y^p in the SAME ring!
    # z' needs to BE a natural number. Not just exist mod q.

    # The local-global principle for p-th powers:
    # z' exists as a natural number iff z'^p = x'^p + y^p for some z'
    # This is an EXISTENTIAL claim over N, not a modular claim!

    # But: if z' does NOT exist mod q (i.e., x'^p + y^p is not a p-th power mod q),
    # then z' cannot exist as a natural number either.
    # So x'^p + y^p being a p-th power mod q is NECESSARY (but not sufficient).

    # QUESTION: Does the FLT assumption x^p + y^p = z^p force x'^p + y^p
    # to be a p-th power mod q?

    # Answer: NOT OBVIOUS! The FLT structure only tells us:
    # (q*x')^p + y^p = z^p, so q^p * x'^p + y^p = z^p
    # This tells us something mod q: y^p ≡ z^p mod q → z ≡ ω^j*y
    # But x'^p + y^p mod q is a DIFFERENT quantity from z^p mod q!

    # x'^p + y^p ≡ (p*t*s')^p + y^p mod q — this depends on p*t*s' mod q

    print(f"\n  DETAILED: In FLT context, x'^p + y^p mod q")
    print(f"  x' = p*t*s', x'^p = (p*t*s')^p")
    print(f"  For x'^p + y^p to be a p-th power mod q:")

    # Let's check: among nonzero p-th powers a^p mod q,
    # how many (a^p + b^p) are p-th powers?
    # If gcd(p, q-1) = p (which is our case since p | q-1),
    # then p-th powers form a subgroup of index p in (ZMod q)*

    # The sum a^p + b^p can be written as b^p * ((a/b)^p + 1)
    # Since b^p is a p-th power, a^p + b^p is a p-th power iff (a/b)^p + 1 is a p-th power

    print(f"\n  Key: (a/b)^p + 1 must be a p-th power mod q")
    print(f"  Let r = a/b mod q, then r^p + 1 must be a p-th power")

    for r in range(1, q):
        val = (pow(r, p, q) + 1) % q
        is_pp = val in pth_powers
        if not is_pp:
            # This r gives a non-p-th-power
            pass  # too many to print

    # Count: how many r ∈ {1,...,q-1} give r^p + 1 as p-th power?
    count = 0
    for r in range(1, q):
        val = (pow(r, p, q) + 1) % q
        if val in pth_powers:
            count += 1
    print(f"  r^p + 1 is a p-th power for {count} out of {q-1} values of r mod {q}")

    # In FLT context: a = x', b = y, so r = x'/y mod q
    # r is arbitrary (depends on specifics of the counter-example)
    # So for SOME counter-examples, x'^p + y^p is NOT a p-th power mod q!

    # BUT WAIT: that means z' doesn't exist mod q, which means
    # z' doesn't exist AT ALL, which means GNReducedGap is FALSE for that case!

    # UNLESS: the FLT structure forces r = x'/y to be one of the "good" values.
    # Let's investigate.

print("\n" + "=" * 60)
print("CRITICAL: Does FLT force x'/y mod q to be 'good'?")
print("=" * 60)

print(
    """
In the counterexample:
  x = q * x' = p * t * s, where q | s, s = q * s'
  x' = p * t * s'
  
  x'/y mod q = (p * t * s') / y mod q
  
  We need: (x'/y)^p + 1 is a p-th power mod q ??
  
  From the FLT equation: z^p = (q*x')^p + y^p
  z ≡ ω^j * y mod q
  
  Does this constrain x'/y mod q in any way?
  
  z = gap + y = p^{p-1}*t^p + y (in BranchA)
  z mod q = (p^{p-1}*t^p + y) mod q = (p^{p-1}*t^p) mod q + y mod q
  
  And z ≡ ω^j*y mod q, so:
  p^{p-1}*t^p ≡ (ω^j - 1)*y mod q
  
  This gives: t^p ≡ (ω^j - 1)*y / p^{p-1} mod q
  
  And x' = p*t*s' so:
  x'^p = p^p * t^p * s'^p 
  
  x'^p mod q = p^p * ((ω^j-1)*y/p^{p-1})^... 
  
  This is getting complicated. Let me just numerically check.
"""
)

# Let's be very concrete: for q=11, p=5
p = 5
q = 11
g = primitive_root(q)
omega = pow(g, (q - 1) // p, q)

pth_powers_q = set(pow(a, p, q) for a in range(q))
print(f"q={q}, p={p}, ω={omega}")
print(f"p-th powers mod {q}: {sorted(pth_powers_q)}")

# For each j ∈ {1,...,p-1} and each y coprime to q:
# gap_mod_q = (ω^j - 1)*y mod q
# t^p mod q is constrained by: p^{p-1}*t^p = gap mod q (in BranchA)
# i.e., t^p ≡ gap / p^{p-1} mod q

# p = 5, p^{p-1} = 5^4 = 625 ≡ 625 mod 11 ≡ 625 - 56*11 = 625 - 616 = 9
p_pow = pow(p, p - 1, q)
print(f"p^(p-1) mod q = {p_pow}")
p_pow_inv = pow(p_pow, q - 2, q)

for j in range(1, p):
    omega_j = pow(omega, j, q)
    print(f"\n  j={j}: ω^j = {omega_j}")

    for y in range(1, q):
        gap_mod = (omega_j - 1) * y % q

        # t^p ≡ gap / p^{p-1} mod q
        tp_mod = (gap_mod * p_pow_inv) % q

        # Is tp_mod a p-th power mod q?
        # If not, there's no valid t → this combination doesn't occur

        if tp_mod not in pth_powers_q:
            # This (j, y) combination cannot arise in BranchA
            continue

        # t mod q: find t such that t^p ≡ tp_mod mod q
        t_mods = [t for t in range(q) if pow(t, p, q) == tp_mod]

        for t_mod in t_mods:
            # s has q as a factor: s = q * s' so s mod q = 0 → s' is free
            # x' = p * t * s', x' mod q = p * t_mod * s'_mod

            for s_prime_mod in range(1, q):
                x_prime_mod = (p * t_mod * s_prime_mod) % q
                if x_prime_mod == 0:
                    continue  # x' should be coprime to q

                # Now check: is x'^p + y^p a p-th power mod q?
                xp_mod = pow(x_prime_mod, p, q)
                yp_mod = pow(y, p, q)
                sum_mod = (xp_mod + yp_mod) % q

                is_pth = sum_mod in pth_powers_q
                if not is_pth:
                    print(
                        f"    FAIL: j={j}, y={y}, t≡{t_mod}, s'≡{s_prime_mod}: "
                        f"x'≡{x_prime_mod}, x'^p+y^p ≡ {sum_mod} NOT p-th power"
                    )

print("\n" + "=" * 60)
print("INTERPRETATION")
print("=" * 60)

print(
    """
If FAIL cases exist, it means:
  For SOME valid combinations of (j, y, t, s') mod q,
  x'^p + y^p is NOT a p-th power mod q.
  
  This would mean z' cannot exist even mod q,
  so GNReducedGap would be FALSE for those cases.
  
BUT: there's one more constraint we haven't used!
  gcd(t, s) = 1, gcd(s, y) = 1, gcd(t, y) = 1
  s' = s/q, and s' might have additional constraints.

Also: s' mod q is NOT free. s = q*s', and the original s 
satisfies many conditions. Specifically:
  GN(p, gap, y) = p * s^p determines s uniquely (up to sign)
  So s is determined by (p, gap, y), and s' = s/q.

Actually the constraint is even stronger:
  x = p * t * s, and x^p + y^p = z^p
  So ALL the variables are determined by the counterexample.
  s' mod q is NOT a free parameter — it's determined.
"""
)

# Let's try another approach: does the FLT equation itself constrain things?
print("=" * 60)
print("FERMAT'S LITTLE THEOREM APPROACH")
print("=" * 60)

print(
    """
In FLT context with q | x:
  z^p = x^p + y^p
  z^p ≡ y^p mod q
  
  We want to show: z'^p = (x/q)^p + y^p has a solution z' ∈ N.
  
  Key: z^p = q^p * (x/q)^p + y^p
  So z^p - y^p = q^p * (x/q)^p
  
  And z'^p - y^p = (x/q)^p (the DESIRED equation)
  
  Compare: z^p - y^p = q^p * (z'^p - y^p) if z' exists.
  
  So z^p - y^p = q^p * z'^p - q^p * y^p
  z^p = q^p * z'^p - q^p * y^p + y^p
  z^p = q^p * z'^p - (q^p - 1) * y^p
  z^p = q^p * z'^p - (q^p - 1) * y^p ... (*)
  
  This is a new Diophantine relation between z, z', y, q, p.
  
  Alternatively: z^p - y^p = q^p * (z'^p - y^p)
  z^p - y^p = q^p * z'^p - q^p * y^p
  z^p + (q^p - 1)*y^p = q^p * z'^p
  z'^p = [z^p + (q^p - 1)*y^p] / q^p
  z'^p = z^p/q^p + y^p*(1 - 1/q^p)
  
  For z' to exist as a natural number:
  [z^p + (q^p - 1)*y^p] must be divisible by q^p
  AND the quotient must be a perfect p-th power.
  
  Divisibility: 
  z^p + (q^p-1)*y^p ≡ z^p - y^p mod q^p 
  = gap * GN 
  = q^p * (x')^p (since q^p | GN in FLT context, and gap coprime to q)
  Wait: z^p - y^p = gap * GN = x^p = (q*x')^p = q^p * x'^p
  So z^p ≡ y^p mod q^p
  → z^p + (q^p-1)*y^p ≡ y^p + (q^p-1)*y^p = q^p * y^p mod q^p
  So: [z^p + (q^p-1)*y^p] / q^p ≡ y^p mod ... (not quite)
  
  More carefully:
  z^p = q^p * x'^p + y^p
  z^p + (q^p-1)*y^p = q^p * x'^p + y^p + (q^p-1)*y^p = q^p * x'^p + q^p * y^p
  = q^p * (x'^p + y^p)
  
  So z'^p = (x'^p + y^p) ← this is just the definition!
  
  We need x'^p + y^p to be a perfect p-th power.
  
  Equivalent reformulation:
  z'^p = x'^p + y^p
  where x' = x/q.
"""
)

print("=" * 60)
print("APPROACH: Minkowski/Hasse local-global for Fermat curves")
print("=" * 60)

print(
    """
The question "does x'^p + y^p = z'^p have a solution in N" is exactly FLT again.
If FLT is true, the answer is NO — and that's the contradiction we want!

But wait: in the descent, we need z' to EXIST (as a counterexample)
to contradict the MINIMALITY of z.

So the logic is:
1. Assume minimal counterexample (x, y, z) with z minimal
2. Find primitive q with q | x
3. IF (x/q)^p + y^p = z'^p for some z':
   - Then z' < z (since x/q < x)
   - (x/q, y, z') is a SMALLER counterexample → contradicts minimality
4. So we need to PROVE (x/q)^p + y^p = z'^p has a solution

But (x/q)^p + y^p = z'^p says ANOTHER Fermat triple exists...
which is FALSE if FLT is true.

THIS IS THE FUNDAMENTAL CIRCULARITY:
  The Kummer-style descent tries to produce a smaller counterexample
  from a given one. BUT producing a smaller counterexample IS false
  (since there are none). The contradiction comes from "there are infinitely
  many counterexamples descending", which is impossible since z is positive.

  The ASSUMPTION that a counterexample exists MUST lead to a contradiction
  at the bottom of the descent. But the descent step itself requires
  CONSTRUCTING the smaller counterexample — i.e., SHOWING that
  x'^p + y^p is indeed a perfect p-th power in the counterexample world.

  This construction is what Z[ζ_p] provides:
  In Z[ζ_p], x^p = ∏(z - ζ^i*y), and each factor is (unit)*α_i^p.
  Removing one prime from α_i gives α_i' with α_i'^p corresponding to x'.
  The KEY is that this gives INTEGERS (not just elements of Z[ζ_p]).
  
  For IRREGULAR primes, this fails: the ideals are p-th powers but
  the ELEMENTS may not be. This is EXACTLY where Kummer's proof breaks down.

  Our codebase works with REGULAR-prime-like assumptions (PthRootCore)
  that ASSUME the descent step works.

  THE BOTTOM LINE:
  GNReducedGap is the ELEMENTARY version of "ideals are principal and p-th powers",
  which is the class-number-one condition for Z[ζ_p].
  This is FALSE for irregular primes in general, but TRUE in the FLT context
  (since Wiles proved FLT for all primes).
"""
)

print("=" * 60)
print("CONSTRUCTIVE APPROACH: What Z[ζ_p] gives us")
print("=" * 60)

print(
    """
In Z[ζ_p] (cyclotomic integers), for p prime:

Factorization: z^p - y^p = ∏_{i=0}^{p-1} (z - ζ^i * y)

Case 1 (p ∤ z-y, i.e., BranchB):
  The factors are pairwise coprime ideals.
  Each (z - ζ^i*y) = I_i^p for some ideal I_i.
  
  If the CLASS NUMBER h of Q(ζ_p) satisfies gcd(h, p) = 1 ("regular prime"):
    I_i = (α_i) for some α_i ∈ Z[ζ_p]
    So z - ζ^i*y = ε_i * α_i^p for some unit ε_i
    
    From this: z - ζ*y = ε * α^p (taking i=1)
    z - y = ε₀ * α₀^p (taking i=0)
    
    Subtracting: (ζ-1)*y = ε*α^p - ε₀*α₀^p + ... ← HARD to use
    
    Better: the IDEAL (z - ζ^j*y) captures all the q-power.
    If q ramifies in Z[ζ_p] as (q) = (Q₁·Q₂·...·Qₘ):
    Since p|(q-1) and q splits completely: each Q_i has norm q.
    v_{Q}(z - ζ^{j₀}*y) ≥ p where Q corresponds to the embedding ζ → ω.
    
    Descent: α_{j₀} = β * (generator of Q)
    So z - ζ^{j₀}*y = ε * (β * π_Q)^p where π_Q generates Q
    
    New: z' - ζ^{j₀}*y = ε' * β^p (removing π_Q^p)
    
    Taking "norm down to Z": z' is an integer iff β has the right Galois-invariance.

Case 2 (p | z-y, i.e., BranchA):
  The factor z - y has extra p-divisibility.
  (z - y) absorbs the ramification at p.
  The coprimality fails at the p-factor.
  More delicate analysis needed.

THE ELEMENTARY CHALLENGE:
  Reproduce the "remove one prime ideal" step WITHOUT using:
  - Z[ζ_p] 
  - ideal class groups
  - Kummer theory
  
  Only using: ω ∈ ZMod q, polynomial factorization of GN mod q^k,
  and elementary number theory.
  
  This is essentially asking for an ELEMENTARY proof of the Kummer descent,
  which is what makes this genuinely hard.
"""
)

# Final: Can we break down the problem into smaller sub-targets?
print("=" * 60)
print("SUB-TARGET DECOMPOSITION for GNReducedGap")
print("=" * 60)

print(
    """
GNReducedGap: ∃ g', g'·GN(p,g',y) = C  where C = p^p·(t·s')^p

This is equivalent to: 
  (g'+y)^p - y^p = C
  (g'+y)^p = C + y^p
  
Let W = C + y^p = p^p*(t*s')^p + y^p = x'^p + y^p
GNReducedGap ⟺ W is a perfect p-th power

Sub-target decomposition:

(A) LOCAL EXISTENCE: For each prime ℓ, W is a p-th power in Z_ℓ (ℓ-adic integers)
    - For ℓ ∤ W: automatic (W is a unit, and unit p-th roots exist if p ∤ ℓ-1... no, not always)
    - For ℓ | W: need v_ℓ(W) ≡ 0 mod p
    - For ℓ = q: THIS IS WHERE ω COMES IN
    
(B) GLOBAL EXISTENCE: Local p-th powers → global p-th power
    - The Hasse-Minkowski theorem works for QUADRATIC forms but NOT for higher powers
    - So local → global fails in general for p ≥ 3
    - This is why GNReducedGap is genuinely hard

(C) SIZE BOUND: z' = W^{1/p} satisfies z' < z
    - This follows from x' < x → x'^p < x^p → W < z^p → z' < z

KEY INSIGHT: Sub-target (A) for ℓ = q IS what ω provides.
  ω gives a p-th root of unity in ZMod q, allowing Hensel lifting.
  But (A) for ALL primes ℓ requires more.

ALTERNATIVE DECOMPOSITION (more elementary):

(A') ARITHMETIC CONSISTENCY: GN(p, gap, y) ≡ 0 (mod q^p) and gap ≡ (ω^j-1)y (mod q^p)
     [We know this from the structure]
     
(B') GAP TRANSFER: There exists g' with g' ≡ some value (mod q^{p-1}) such that
     v_q(g'·GN(p,g',y)) = 0 and g'·GN(p,g',y) = C
     
(C') INTEGRALITY: g' is a positive natural number (not just a p-adic number)

The genuine difficulty is (C'): showing the p-adic number is actually a positive integer.
This is where the non-archimedean (local) and archimedean (W > 0) conditions must combine.
"""
)
