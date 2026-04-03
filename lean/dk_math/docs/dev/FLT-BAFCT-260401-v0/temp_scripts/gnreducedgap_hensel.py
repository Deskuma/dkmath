#!/usr/bin/env python3
"""
核心発見: v_q(Φ_p(r)) ≥ p の解の一意性分析

mod q^p で v_q(Φ_p(r)) ≥ p を満たす r ≡ ω^j mod q は各 j に対して唯一。
この一意性を使って descent を構成できないか？

FLT 文脈: z/y ≡ r (mod q^p) where v_q(Φ_p(r)) = v_q(GN) ≥ p
z/y は「超 Wieferich 零点」mod q^p に一意に定まる。

Descent の核心:
  z'/y mod q^{p-1} は何か？
  z' が存在するなら、z'/y は Φ_p(r') = 0 mod q^{p-1}(?) を満たす?
"""

from sympy import isprime, primitive_root, binomial, gcd


def phi_p(r, p):
    """Φ_p(r) = r^{p-1} + r^{p-2} + ... + 1 = (r^p - 1)/(r - 1) for r ≠ 1"""
    return sum(r**i for i in range(p))


def v_q(n, q):
    """q-adic valuation of n"""
    if n == 0:
        return float("inf")
    v = 0
    while n % q == 0:
        v += 1
        n //= q
    return v


def GN(p, u, y):
    return sum(binomial(p, k + 1) * u**k * y ** (p - 1 - k) for k in range(p))


p = 5

print("=" * 60)
print(f"UNIQUENESS ANALYSIS: v_q(Φ_{p}(r)) ≥ k for r ≡ ω^j mod q")
print("=" * 60)

for q in [11, 31, 41]:
    if not isprime(q) or (q - 1) % p != 0:
        continue

    omega = pow(primitive_root(q), (q - 1) // p, q)

    print(f"\nq = {q}, ω = {omega}")
    print(
        f"{'j':>3} | {'r mod q':>8} | {'r mod q² (v≥2)':>15} | {'r mod q³ (v≥3)':>15} | {'r mod q⁴ (v≥4)':>15} | {'r mod q⁵ (v≥5)':>15}"
    )
    print("-" * 90)

    for j in range(1, p):
        r_j = pow(omega, j, q)

        results = {}
        for k in range(2, p + 1):
            qk = q**k
            solutions = []
            for r in range(r_j, qk, q):
                phi = phi_p(r, p)
                if v_q(phi, q) >= k:
                    solutions.append(r)
            results[k] = solutions

        # Display
        def fmt(sols, qk):
            if len(sols) == 0:
                return "NONE"
            elif len(sols) == 1:
                return f"{sols[0]} (unique!)"
            else:
                return f"{len(sols)} solutions"

        print(
            f"{j:>3} | {r_j:>8} | {fmt(results[2], q**2):>15} | {fmt(results[3], q**3):>15} | {fmt(results[4], q**4):>15} | {fmt(results[5], q**5):>15}"
        )

print("\n" + "=" * 60)
print("HENSEL LIFTING CHAIN: exact r values mod q^k")
print("=" * 60)

q = 11
omega = pow(primitive_root(q), (q - 1) // p, q)
print(f"\nq = {q}, p = {p}, ω = {omega}")

for j in range(1, p):
    r_j = pow(omega, j, q)
    print(f"\n--- j = {j}, ω^j = {r_j} ---")

    # Track Hensel lifting
    prev_sols = [r_j]
    for k in range(1, p + 2):
        qk = q**k
        new_sols = []
        for r_base in prev_sols:
            for c in range(q):
                r = r_base + q ** (k - 1) * c if k > 1 else r_base
                if k == 1:
                    r = r_base
                    phi = phi_p(r, p)
                    vr = v_q(phi, q)
                    if vr >= 1:
                        new_sols.append(r)
                    break
                else:
                    r2 = r_base + q ** (k - 1) * c
                    phi = phi_p(r2, p)
                    vr = v_q(phi, q)
                    if vr >= k:
                        new_sols.append(r2)

        print(f"  mod q^{k} = {qk}: v_q ≥ {k} solutions = {new_sols}")
        prev_sols = new_sols
        if not new_sols:
            print(f"  ★ Hensel lifting FAILS at level k={k}!")
            break

print("\n" + "=" * 60)
print("CRITICAL CHECK: Derivative analysis for Hensel")
print("=" * 60)

# For Hensel lifting: we need Φ_p'(r₀) ≢ 0 mod q where r₀ is the root
# Φ_p(x) = x^{p-1} + x^{p-2} + ... + 1
# Φ_p'(x) = (p-1)x^{p-2} + (p-2)x^{p-3} + ... + 1


def phi_p_deriv(r, p):
    return sum((p - 1 - i) * r ** (p - 2 - i) for i in range(p - 1))


q = 11
omega = pow(primitive_root(q), (q - 1) // p, q)

print(f"\nq = {q}, p = {p}")
for j in range(1, p):
    r_j = pow(omega, j, q)
    phi_val = phi_p(r_j, p) % q
    phi_deriv = phi_p_deriv(r_j, p) % q
    print(
        f"  j={j}: Φ_{p}({r_j}) ≡ {phi_val} mod {q}, Φ'_{p}({r_j}) ≡ {phi_deriv} mod {q}"
    )
    if phi_val == 0 and phi_deriv != 0:
        print(f"    → Simple zero, Hensel CAN lift uniquely to any q^k")
    elif phi_val == 0 and phi_deriv == 0:
        print(f"    → DOUBLE ZERO! Hensel may not lift!")

print("\n" + "=" * 60)
print("KEY INSIGHT: SIMPLE ZEROS → UNIQUE LIFT → SUPER-WIEFERICH UNIQUENESS")
print("=" * 60)

print(
    """
If Φ_p has SIMPLE zeros at ω^j mod q (i.e., Φ_p'(ω^j) ≢ 0 mod q),
then by Hensel's lemma:
  Each zero lifts uniquely: ω^j → R_j mod q^2 → R_j mod q^3 → ... → R_j mod q^k
  And v_q(Φ_p(R_j)) = 1 at each level (simple zero).

BUT: in FLT context, v_q(Φ_p(z/y)) ≥ p.
  If the zeros are simple, the only way to get v_q ≥ p is if
  z/y ≡ R_j (mod q^p) where R_j is the Hensel lift.
  
  Since R_j is UNIQUE mod q^p, this gives:
  z ≡ R_j · y (mod q^p)
  z - R_j·y ≡ 0 (mod q^p)

But wait: Claim: Φ_p'(ω^j) ≡ 0 mod q for roots of Φ_p!? Let's check.

Φ_p(x) = (x^p - 1)/(x - 1)
Φ_p'(x) = [p·x^{p-1}·(x-1) - (x^p-1)] / (x-1)²

At x = ω^j (a root of Φ_p mod q):
  x^p ≡ 1 mod q
  Φ_p'(x) = [p·x^{p-1}·(x-1) - 0] / (x-1)² = p·x^{p-1} / (x-1)

  Since x = ω^j and x^{p-1} = ω^{j(p-1)} = ω^{-j} (since ω^p = 1):
  Φ_p'(ω^j) = p · ω^{-j} / (ω^j - 1)
  
  This is ≢ 0 mod q iff p · ω^{-j} · (ω^j - 1)^{-1} ≢ 0 mod q
  iff p ≢ 0 mod q (since ω^{-j} and (ω^j-1) are units mod q)
  iff q ≠ p.
  
  Since q ≡ 1 mod p and q ≠ p: Φ_p'(ω^j) ≢ 0 mod q. ✓
  
  CONCLUSION: ALL zeros of Φ_p mod q are SIMPLE!
  → Hensel lifting gives UNIQUE R_j mod q^k for each k.
  → v_q(Φ_p(R_j)) = 1 for the lifted root.
"""
)

# Verify the derivative formula
print("Verification: Φ_p'(ω^j) = p·ω^{-j}/(ω^j - 1) mod q")
q = 11
omega = pow(primitive_root(q), (q - 1) // p, q)

for j in range(1, p):
    w = pow(omega, j, q)
    w_inv = pow(w, q - 2, q)  # ω^{-j} mod q
    w_m1_inv = pow((w - 1) % q, q - 2, q)  # (ω^j - 1)^{-1} mod q

    formula_val = (p * w_inv * w_m1_inv) % q
    actual_val = phi_p_deriv(w, p) % q

    print(
        f"  j={j}: formula = {formula_val}, actual = {actual_val}, match = {formula_val == actual_val}"
    )

print("\n" + "=" * 60)
print("THE REAL QUESTION: What does v_q(Φ_p(z/y)) ≥ p mean?")
print("=" * 60)

print(
    """
Since zeros of Φ_p mod q are all SIMPLE:
  Hensel lifting gives unique R_j ∈ Z_q (q-adic integers) with Φ_p(R_j) = 0.
  
  For any integer r with r ≡ ω^j mod q:
    r = R_j + (r - R_j) where r - R_j ≡ 0 mod q but might not be 0 mod q².
    
    Φ_p(r) = Φ_p(R_j + (r - R_j))
            = Φ_p(R_j) + Φ_p'(R_j)·(r - R_j) + O((r-R_j)²)
    
    Φ_p(R_j) = 0 (exactly, in Z_q)
    So Φ_p(r) = Φ_p'(R_j)·(r - R_j) + O((r-R_j)²)
    
    v_q(Φ_p(r)) = v_q(Φ_p'(R_j)) + v_q(r - R_j) + ... 
    
    Since Φ_p'(R_j) ≢ 0 mod q (simple root): v_q(Φ_p'(R_j)) = 0
    
    So v_q(Φ_p(r)) = v_q(r - R_j) (for small enough r - R_j)
    
    More precisely: v_q(Φ_p(r)) = v_q(r - R_j) when v_q(r - R_j) ≥ 1!
    
    (The Taylor expansion error is O((r-R_j)²), which has v_q ≥ 2·v_q(r-R_j))

THEREFORE (critical):
  v_q(Φ_p(z/y)) ≥ p
  ⟺ v_q(z/y - R_j) ≥ p (where j is the index with z ≡ ω^j·y mod q)
  ⟺ z/y ≡ R_j (mod q^p)
  ⟺ z ≡ R_j · y (mod q^p)

But... z/y is not necessarily an integer!
We work with z and y as integers, and GN is computed from (z-y, y).

Actually: v_q(GN(p, gap, y)) where gap = z-y:
  GN(p, gap, y) = Φ_p(z/y) · y^{p-1} ... wait, this needs care.
  
  GN(p, u, y) = [(u+y)^p - y^p]/u
  With u = gap, u+y = z:
  GN = (z^p - y^p)/(z-y) = Σ_{i=0}^{p-1} z^i · y^{p-1-i}
  
  This is NOT exactly Φ_p(z/y) · y^{p-1}. Let me check:
  Σ z^i y^{p-1-i} = y^{p-1} Σ (z/y)^i = y^{p-1} · Φ_p(z/y)
  
  YES! GN = y^{p-1} · Φ_p(z/y).
  
  So v_q(GN) = (p-1)·v_q(y) + v_q(Φ_p(z/y))
  Since gcd(q, y) = 1: v_q(y) = 0
  → v_q(GN) = v_q(Φ_p(z/y))
  
  And Φ_p(z/y) = Φ_p((z/y mod q^k)) in Z_q (when q ∤ y).
  
  So: v_q(GN) = v_q(z/y - R_{j₀}) = v_q(z - R_{j₀}·y) (since q ∤ y)

  In FLT context: v_q(GN) = p·v_q(x) ≥ p
  → v_q(z - R_{j₀}·y) ≥ p

THIS IS THE KEY EQUATION:
  z ≡ R_{j₀} · y (mod q^p)
  
  where R_{j₀} is the unique Hensel lift of ω^{j₀} such that Φ_p(R_{j₀}) = 0 in Z_q.
"""
)

# Let's compute R_j for q=11, p=5
print("Computing Hensel lifts R_j for q=11, p=5:")
q = 11
omega = pow(primitive_root(q), (q - 1) // p, q)

# R_j is the unique element of Z_q (represented mod q^N for large N)
# such that Φ_p(R_j) = 0 and R_j ≡ ω^j mod q

N = 10  # compute mod q^10
qN = q**N

for j in range(1, p):
    r_j = pow(omega, j, q)
    # Hensel lift
    r = r_j
    for k in range(1, N):
        # Current: Φ_p(r) ≡ 0 mod q^k
        # Want: Φ_p(r + c*q^k) ≡ 0 mod q^{k+1}
        # Taylor: Φ_p(r + c*q^k) ≈ Φ_p(r) + Φ_p'(r) * c * q^k
        # Need: Φ_p(r) + Φ_p'(r) * c * q^k ≡ 0 mod q^{k+1}
        # c ≡ -Φ_p(r)/(q^k * Φ_p'(r)) mod q

        phi_val = phi_p(r, p)
        phi_deriv_val = phi_p_deriv(r, p)

        assert phi_val % q**k == 0, f"Φ_p(r) not divisible by q^{k}"

        residue = (phi_val // q**k) % q
        deriv_mod = phi_deriv_val % q
        deriv_inv = pow(deriv_mod, q - 2, q)

        c = (-residue * deriv_inv) % q
        r = r + c * q**k

    # Verify
    phi_final = phi_p(r, p)
    v_final = v_q(phi_final, q)
    print(f"  j={j}: R_j mod q^{N} = {r}, v_q(Φ_p(R_j)) = {v_final}")

    # Also show R_j mod smaller powers
    for k in [1, 2, 3, 5, 10]:
        print(f"    R_j mod q^{k} = {r % q**k}")

print("\n" + "=" * 60)
print("THE DESCENT PLAN using Hensel lifts")
print("=" * 60)

print(
    """
We have established:

1. GN(p, gap, y) = y^{p-1} · Φ_p(z/y) where z = gap + y

2. Φ_p has p-1 simple zeros at ω^j mod q, each lifting uniquely to R_j in Z_q

3. v_q(GN) = v_q(z - R_{j₀}·y) where j₀ is the index with z ≡ ω^{j₀}·y mod q

4. In FLT context: v_q(GN) = p·v_q(x) ≥ p → z ≡ R_{j₀}·y mod q^p

NOW FOR THE DESCENT:
  
  We want g' such that g'·GN(p, g', y) = gap·GN/q^p = x^p/q^p = (x/q)^p

  g'·GN(p, g', y) = g' · y^{p-1} · Φ_p((g'+y)/y)
  
  Let z' = g'+y. Then:
  (z'-y) · y^{p-1} · Φ_p(z'/y) = (x/q)^p
  
  We need: (z'-y) · Φ_p(z'/y) = (x/q)^p / y^{p-1}

  Q-ADIC PERSPECTIVE:
  Original: (z-y) · Φ_p(z/y) = x^p / y^{p-1}
  Descent:  (z'-y) · Φ_p(z'/y) = x^p / (q^p · y^{p-1})

  The ratio: 
  [(z-y)·Φ_p(z/y)] / [(z'-y)·Φ_p(z'/y)] = q^p

  v_q of left side = v_q(z-y) + v_q(Φ_p(z/y)) - v_q(z'-y) - v_q(Φ_p(z'/y))
  = 0 + v_q(z - R·y) - v_q(z'-y) - v_q(z'/y - R) (since q∤gap, q∤y)
  = v_q(z - R·y) - v_q(z'-y) - v_q(z' - R·y)

  And this should equal p.

  Natural candidate: z' such that v_q(z' - R·y) = v_q(z - R·y) - p
                     AND v_q(z' - y) = 0 (so q ∤ gap')

  If v_q(z - R·y) = p (minimal FLT case), then v_q(z' - R·y) = 0.
  This means z'/y ≢ R mod q, i.e., z' is NOT at the Hensel root.
  Then v_q(Φ_p(z'/y)) = 0.
  And v_q(z'-y) = ?
  
  Wait: v_q(z-y) + v_q(Φ_p(z/y)) = p (from v_q(x^p) = p*v_q(x) = p for v_q(x)=1)
  v_q(z-y) = 0, v_q(Φ_p(z/y)) = p → ✓
  
  For z': v_q((z'-y)·Φ_p(z'/y)) = 0 (since q ∤ (x/q)^p when v_q(x)=1)
  So v_q(z'-y) + v_q(Φ_p(z'/y)) = 0
  Both are ≥ 0, so both = 0.
  
  v_q(Φ_p(z'/y)) = 0 means z'/y is NOT ≡ ω^j mod q for any j.
  This is simply: q ∤ Φ_p(z'/y).
  I.e., Σ (z'/y)^i ≢ 0 mod q.

INTERPRETATION:
  The descent z → z' removes ALL the q-adic structure from z.
  z was at a Hensel root of Φ_p: z ≡ R·y mod q^p
  z' is NOT at any Hensel root: Φ_p(z'/y) ≢ 0 mod q

  This is consistent! The descent "peels off" the q-factor completely.
  
  But... does z' exist? That's still the question.
  We've only characterized WHAT z' must look like mod q if it exists.
  We haven't shown it EXISTS as a natural number.
"""
)

print("=" * 60)
print("Deeper: The multiplicative structure")
print("=" * 60)

print(
    """
In Z_q (q-adic integers), Φ_p factors completely:
  Φ_p(x) = ∏_{j=1}^{p-1} (x - R_j)

So: Φ_p(z/y) = ∏_{j=1}^{p-1} (z/y - R_j)

And GN = y^{p-1} · ∏_{j=1}^{p-1} (z/y - R_j)
       = ∏_{j=1}^{p-1} (z - R_j·y) / y^{0}  ... wait:
       
y^{p-1} · ∏(z/y - R_j) = y^{p-1} · ∏(z - R_j·y)/y^{p-1} = ∏(z - R_j·y)

So GN = ∏_{j=1}^{p-1} (z - R_j·y) in Z_q.

And gap·GN = (z-y)·∏_{j=1}^{p-1}(z - R_j·y) = x^p in Z_q.

Note: (z-y) = (z - R_0·y) where R_0 = 1 (not a root of Φ_p, but the "trivial" factor).

Actually: z^p - y^p = ∏_{j=0}^{p-1} (z - ζ^j·y) in Z[ζ_p]
In Z_q: z^p - y^p = (z-y) · ∏_{j=1}^{p-1} (z - R_j·y) where R_j are Hensel lifts of ω^j

x^p = (z-y) · ∏_{j=1}^{p-1} (z - R_j·y)

Each factor (z - R_j·y) is in Z_q.
In FLT: v_q(z - R_{j₀}·y) = p·v_q(x) and all other factors have v_q = 0.

So the q-adic factorization is:
  x^p = (z-y) · (z - R_{j₀}·y) · ∏_{j≠j₀} (z - R_j·y)
  
  v_q: 0 + p·v_q(x) + 0 + ... + 0 = p·v_q(x) ✓

THE q-ADIC DESCENT:
  Replace (z - R_{j₀}·y) by (z - R_{j₀}·y)/q^p:
  
  (x/q)^p = (z-y) · [(z - R_{j₀}·y)/q^p] · ∏_{j≠j₀} (z - R_j·y)
  
  But this should equal (z'-y) · ∏_{j=1}^{p-1} (z' - R_j·y) for some z'.
  
  So the question reduces to:
  
  Does there exist z' ∈ N such that:
  (z'-y) · ∏_{j=1}^{p-1} (z' - R_j·y) = (z-y) · [(z-R_{j₀}·y)/q^p] · ∏_{j≠j₀} (z-R_j·y)?

  In Z_q this is solvable (by p-adic analysis).
  The question is whether the q-adic solution is ALSO a positive integer.
  
  This is the LOCAL-GLOBAL gap. And this is EXACTLY what makes FLT hard.

HOWEVER: we have information from ALL primes q simultaneously!
  For each primitive q_i: z ≡ R_{j_i} · y mod q_i^p
  These congruences (CRT) determine z modulo ∏ q_i^p.
  
  Similarly, z' must satisfy congruences from its own primitive primes.
  
  The point: z' has FEWER primitive primes (we removed q).
  So z' is LESS constrained by CRT.
  
  Does this help? In some sense, the descent RELAXES the constraints,
  making z' easier to exist. But this doesn't prove existence.
"""
)

print("\n" + "=" * 60)
print("COMPLETELY NEW APPROACH: Use Hensel factorization for embedding")
print("=" * 60)

print(
    """
Instead of trying to CONSTRUCT z' directly, consider:

THEOREM (if provable): The factorization
  x^p = (z-y) · ∏_{j=1}^{p-1} (z - R_j·y)
in Z_q determines z mod q^p.

And the FLT constraint forces z ≡ R_{j₀}·y mod q^{something}.

ALTERNATIVE APPROACH to GNReducedGap:
Instead of descent, derive a DIRECT contradiction from the q-adic structure.

Specifically: for p ≥ 5, the system of congruences
  z ≡ R_{j_i}·y mod q_i^p  for ALL primitive primes q_i
  z = gap + y where gap = p^{p-1}·t^p
  
  combined with SIZE constraints (z ≤ ...) might be incompatible.

This is a DIRECT attack, not a descent.

Let's check: how many congruences do we get?

For the counterexample: s = ∏ q_i^{a_i}, each q_i ≡ 1 mod p
∏ q_i^p = large modulus
Combined CRT modulus: M = ∏ q_i^p

z ≡ R_{j_i}·y mod q_i^p for each i
By CRT: z ≡ Z_0 mod M for a unique Z_0

AND: z = p^{p-1}·t^p + y

So: p^{p-1}·t^p + y ≡ Z_0 mod M
    p^{p-1}·t^p ≡ Z_0 - y mod M
    t^p ≡ (Z_0 - y)/p^{p-1} mod M

Since M = ∏ q_i^p ≥ ∏ q_i^5 ≥ (∏ q_i)^5 = s^5·(some)...

Actually s = ∏ q_i^{a_i}, so s^p = ∏ q_i^{p·a_i} 
and M = ∏ q_i^p.
If each a_i = 1: M = s^p.
And x = p·t·s, gap = p^{p-1}·t^p, z = gap + y.

Size: z = p^{p-1}·t^p + y < z^p is trivially true but doesn't help.
More useful: z ≈ gap ≈ p^{p-1}·t^p (for large t)
And M = s^p (if a_i = 1).
And x = p·t·s, so gap·GN = x^p = p^p·t^p·s^p.
GN = p·s^p. So gap = x^p/GN = p^{p-1}·t^p. ✓

The CRT modulus M = s^p gives t^p ≡ const mod s^p.
But t and s are coprime. And t is much smaller than s (or not?).

Actually there's no size relation between t and s in general.
The descent tries to REDUCE s, not prove a size contradiction.

Bottom line: DIRECT contradiction from CRT seems hard without more structure.

Let's instead focus on what CAN be done: 
formalizing the Hensel factorization structure in Lean.
"""
)

# Compute the Hensel lifts as concrete numbers
print("\n" + "=" * 60)
print("Concrete Hensel lifts for small q")
print("=" * 60)

for q in [11, 31]:
    omega = pow(primitive_root(q), (q - 1) // p, q)
    print(f"\nq={q}, p={p}, ω={omega}")

    N = 8
    for j in range(1, p):
        r = pow(omega, j, q)
        for k in range(1, N):
            phi_val = phi_p(r, p)
            phi_deriv_val = phi_p_deriv(r, p)
            residue = (phi_val // q**k) % q
            deriv_mod = phi_deriv_val % q
            deriv_inv = pow(deriv_mod, q - 2, q)
            c = (-residue * deriv_inv) % q
            r = r + c * q**k

        v_check = v_q(phi_p(r, p), q)
        print(f"  R_{j} (mod q^{N}) = {r}, v_q(Φ_p(R_j)) ≥ {v_check}")

        # Key: R_j * R_{p-j} ≡ ? mod q^N
        # Since ω^j · ω^{p-j} = ω^p = 1:
        # At mod q level: R_j · R_{p-j} ≡ 1 mod q
        # Does this lift? R_j · R_{p-j} ≡ 1 mod q^k?
