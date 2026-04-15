#!/usr/bin/env python3
"""
Kummer descent を elementary に言い換える試み。

GN(p, gap, y) = Σ_{i=0}^{p-1} z^i · y^{p-1-i}  (= geom_sum₂)

Z[ζ_p] 上では: GN = Π_{j=1}^{p-1} (z - ζ^j · y)

FLT 反例文脈で q primitive prime (q ≡ 1 mod p):
  v_q(GN) = p · v_q(x) ≥ p

Kummer の key insight: ζ ∈ ZMod q (since p | q-1)
  GN ≡ Π (z - ζ^j·y) (mod q)
  各因子は distinct (ζ^j are distinct) → 高々1つの因子が q で割れる
  → v_q(z - ζ^{j₀}·y) = v_q(GN) ≥ p

この「1因子への集中」が descent の核心。
Elementary に: z ≡ ζ^{j₀}·y (mod q^p)

今回の実験: この集中とサイズ制約にから矛盾が出ないか？
"""

from math import gcd, isqrt
from itertools import product


def find_primitive_root(q, p):
    """Find ω such that ω^p ≡ 1 (mod q), ω ≠ 1."""
    # q ≡ 1 (mod p) is required
    if (q - 1) % p != 0:
        return None
    g = None
    for a in range(2, q):
        # Check if a is a primitive root mod q
        ok = True
        for d in range(1, q - 1):
            if (q - 1) % d == 0 and d < q - 1:
                if pow(a, d, q) == 1:
                    ok = False
                    break
        if ok:
            g = a
            break
    if g is None:
        return None
    return pow(g, (q - 1) // p, q)


def hensel_lift(f, fp, root, q, target_exp):
    """
    Hensel lift root mod q to root mod q^target_exp.
    f: function, fp: derivative
    """
    r = root % q
    modulus = q
    for _ in range(1, target_exp):
        fr = f(r) % (modulus * q)
        fpr = fp(r) % modulus
        # Newton step: r' = r - f(r)/f'(r)  (mod modulus*q)
        # f'(r) must be invertible mod q
        inv = pow(fpr, -1, q)  # inverse of f'(r) mod q
        correction = (fr * inv) % (modulus * q)
        r = (r - correction) % (modulus * q)
        modulus *= q
    return r % modulus


def analyze_kummer_structure(p, q):
    """
    Analyze the Kummer structure for FLT descent.
    """
    print(f"\n{'='*70}")
    print(f"KUMMER DESCENT ANALYSIS: p={p}, q={q}")
    print(f"{'='*70}")

    omega = find_primitive_root(q, p)
    if omega is None:
        print(f"  No primitive p-th root mod q found")
        return

    print(f"  ω = {omega} (primitive {p}-th root of unity mod {q})")
    roots = [pow(omega, j, q) for j in range(1, p)]
    print(f"  Roots ω^j mod {q}: {roots}")

    # Hensel lift each root to mod q^p
    qp = q**p
    print(f"\n  Hensel lifting to mod q^p = {qp}:")
    lifted = {}
    for j in range(1, p):
        r = pow(omega, j, q)
        # Φ_p(x) = Σ x^i for i=0..p-1
        f = lambda x, pp=p: sum(pow(x, i, qp * q) for i in range(pp)) % (qp * q)
        fp = lambda x, pp=p: sum(i * pow(x, i - 1, qp * q) for i in range(1, pp)) % (
            qp * q
        )
        R_j = hensel_lift(f, fp, r, q, p)
        lifted[j] = R_j
        # Verify
        val = sum(pow(R_j, i, qp) for i in range(p)) % qp
        print(f"    j={j}: R_{j} = {R_j} (mod q^p), Φ_p(R_{j}) mod q^p = {val}")

    # KEY ANALYSIS: In FLT context, z ≡ R_j · y (mod q^p)
    # Gap = z - y, so gap ≡ (R_j - 1) · y (mod q^p)
    # gap = p^{p-1} · t^p, so p^{p-1} · t^p ≡ (R_j - 1) · y (mod q^p)
    print(f"\n  FLT CONTEXT ANALYSIS:")
    print(f"  gap = p^(p-1) · t^p = {p**(p-1)} · t^p")
    print(f"  z ≡ R_j · y (mod q^p), gap = z - y ≡ (R_j - 1)·y (mod q^p)")

    for j in range(1, p):
        R_j = lifted[j]
        delta = (R_j - 1) % qp
        print(f"\n  j={j}: R_j - 1 = {delta} (mod q^p)")
        # v_q(R_j - 1) tells us about gap structure
        v = 0
        temp = delta
        while temp % q == 0 and temp > 0:
            v += 1
            temp //= q
        print(f"    v_q(R_j - 1) = {v}")

        # For FLT: p^{p-1} · t^p ≡ delta · y (mod q^p)
        # Since gcd(q, y) = 1, y is invertible mod q^p
        # So: p^{p-1} · t^p ≡ delta · y (mod q^p)
        # This constrains (t, y) pairs modulo q^p

        # v_q(delta) = v_q(R_j - 1)
        # v_q(gap) = 0 (primitive: q ∤ gap)
        # So v_q(delta · y) = v_q(delta) since gcd(q, y) = 1
        # Constraint: v_q(p^{p-1} · t^p) = v_q(delta · y) = v_q(delta)
        # If p ≠ q: v_q(p^{p-1} · t^p) = p · v_q(t) = v_q(delta)

        if v > 0:
            print(f"    !! v_q(R_j - 1) = {v} > 0")
            print(f"    This means v_q(gap) ≥ {v} from z ≡ R_j·y, gap = z-y")
            print(f"    But q ∤ gap (primitive!) → CONTRADICTION if v ≥ 1")
            print(f"    → j={j} is EXCLUDED from candidates!")
        else:
            print(f"    v_q(R_j - 1) = 0 → gap ≢ 0 (mod q) ✓ (compatible)")

    # SECOND KEY ANALYSIS: Interaction between multiple primes
    print(f"\n\n  MULTI-PRIME INTERACTION:")
    print(f"  If q₁, q₂ are both primitive primes with q_i ≡ 1 (mod p):")
    print(f"  Then z ≡ R_j₁ · y (mod q₁^p) AND z ≡ R_j₂ · y (mod q₂^p)")
    print(f"  By CRT: z is constrained mod (q₁^p · q₂^p)")
    print(f"  This severely constrains the possible z values.")

    # TEST: For small primes q₁, q₂, compute CRT constraints
    if p == 5:
        primes_1mod5 = [
            q2 for q2 in [11, 31, 41, 61, 71, 101, 131, 151, 181, 191] if q2 != q
        ]
        print(f"\n  Primes ≡ 1 (mod 5): {[q] + primes_1mod5[:5]}")

        if len(primes_1mod5) >= 1:
            q2 = primes_1mod5[0]
            omega2 = find_primitive_root(q2, p)
            if omega2:
                q2p = q2**p
                print(f"\n  PAIR: q₁={q}, q₂={q2}")
                print(f"  CRT modulus: q₁^p · q₂^p = {qp} · {q2p} = {qp * q2p}")

                # For each j₁, j₂ combination:
                count_compatible = 0
                for j1 in range(1, p):
                    R1 = lifted[j1]
                    # Check if R1 - 1 is coprime to q
                    if (R1 - 1) % q == 0:
                        continue  # excluded

                    # Hensel lift for q2
                    f2 = lambda x, pp=p: sum(pow(x, i, q2p * q2) for i in range(pp)) % (
                        q2p * q2
                    )
                    fp2 = lambda x, pp=p: sum(
                        i * pow(x, i - 1, q2p * q2) for i in range(1, pp)
                    ) % (q2p * q2)
                    R2j = {}
                    for j2 in range(1, p):
                        r2 = pow(omega2, j2, q2)
                        R2 = hensel_lift(f2, fp2, r2, q2, p)
                        R2j[j2] = R2

                    for j2 in range(1, p):
                        R2 = R2j[j2]
                        if (R2 - 1) % q2 == 0:
                            continue  # excluded
                        count_compatible += 1

                print(f"  Compatible (j₁, j₂) pairs: {count_compatible}")
                print(f"  (out of {(p-1)**2} total)")

    # THIRD KEY ANALYSIS: Size bound from GN asymptotic
    print(f"\n\n  SIZE BOUND ANALYSIS:")
    print(f"  GN(p, gap, y) ≥ gap^(p-1)  (from gnAtZero)")
    print(f"  In FLT: gap·GN = x^p = (p·t·s)^p")
    print(f"  → gap · gap^(p-1) ≤ gap·GN = x^p")
    print(f"  → gap^p ≤ x^p → gap ≤ x = p·t·s")
    print(f"  Since gap = p^(p-1)·t^p: p^(p-1)·t^p ≤ p·t·s")
    print(f"  → p^(p-2)·t^(p-1) ≤ s")
    print(f"  For p=5: 125·t^4 ≤ s")
    print(f"  Since s = Π q_i^(a_i) where all q_i ≡ 1 mod p:")
    print(f"  smallest s with ≥ k primes ≡ 1 mod 5:")
    if p == 5:
        primes_mod5 = [
            11,
            31,
            41,
            61,
            71,
            101,
            131,
            151,
            181,
            191,
            211,
            241,
            251,
            271,
            281,
        ]
        cumulative = 1
        for i, pr in enumerate(primes_mod5):
            cumulative *= pr
            threshold = 125 * (1**4)  # t=1
            print(
                f"    s ≥ {pr}^1 = {pr}, cumulative product = {cumulative}, threshold = {threshold}"
            )
            if cumulative >= threshold:
                print(f"    → First feasible at {i+1} primes (t=1)")
                break

    # FOURTH: Norm constraint from cyclotomic field
    print(f"\n\n  NORM CONSTRAINT (Cyclotomic Field Perspective):")
    print(f"  In Z[ζ_p]: z - ζ^j·y for j=1,...,p-1 are 'conjugate factors'")
    print(f"  Norm: N(z - ζ^j·y) = Π_{{j=1}}^{{p-1}} (z - ζ^j·y) = GN(p, gap, y)")
    print(f"  FLT: GN = p · s^p")
    print(f"  If p ∤ class number h(Q(ζ_p)): each (z - ζ^j·y) = (unit)·α_j^p")
    print(f"  → Kummer's 'first case' proof for regular primes")
    print(f"")
    print(f"  For p=3: h=1 (regular) → Euler/Kummer proof works")
    print(f"  For p=5: h=1 (regular) → Kummer proof works")
    print(f"  For p=7: h=1 (regular)")
    print(f"  For p=37: h=37 (irregular!) → needs additional work")
    print(f"")
    print(f"  KEY: For regular primes, each factor (z - ζ^j·y) is 'p-th power'")
    print(f"  in the ring of integers Z[ζ_p]. This gives MUCH stronger constraints")
    print(f"  than just knowing v_q(factor) for individual primes q.")

    # FIFTH: The "elementary Kummer lemma" approach
    print(f"\n\n  ELEMENTARY KUMMER LEMMA APPROACH:")
    print(f"  Instead of cyclotomic fields, use the CONSEQUENCE:")
    print(f"")
    print(f"  If gcd(z - ζ^i·y, z - ζ^j·y) | p for all i ≠ j,")
    print(f"  then from GN = p · s^p, each factor has norm ≈ s^p/(p-1).")
    print(f"")
    print(f"  Elementarized: for any prime q ≡ 1 (mod p), q ≠ p:")
    print(f"    v_q(GN) = v_q(z - ζ^j₀·y)  for unique j₀")
    print(f"    (all other factors are q-coprime)")
    print(f"")
    print(f"  This is ALREADY what we have in §20 Hensel analysis!")
    print(f"  The missing piece: how to go from v_q information to SIZE constraints")
    print(f"  that create a contradiction.")

    # EXPERIMENT: Size consistency check
    print(f"\n\n  SIZE CONSISTENCY EXPERIMENT (p={p}, small examples):")
    # For p=5, gap = 5^4·t^5 = 625·t^5
    # GN ≥ gap^4 = 625^4·t^20
    # x^5 = gap·GN ≥ 625^5·t^25 = (625·t^5)^5 = gap^5
    # So: x ≥ gap = 625·t^5 (trivially)
    # Better: x = 5·t·s, so s^5 = GN/5
    # GN minimum at y=0: GN(5, gap, 0) = gap^4
    # s^5 = gap^4/5 = (625·t^5)^4/5 = 5^15·t^20
    # s = 5^3·t^4 = 125·t^4
    # EXACT at y=0!
    # For y > 0: GN > gap^4, so s > 125·t^4

    if p == 5:
        print(f"  gap = 625·t^5")
        print(f"  At y=0: s = 125·t^4 (exact)")
        print(f"  At y > 0: s > 125·t^4 (strictly)")
        print(f"")

        # Check: does s being forced > 125·t^4 with all prime factors ≡ 1 mod 5
        # create any contradiction?
        for t in range(1, 4):
            s_min = 125 * t**4
            gap = 625 * t**5
            print(f"  t={t}: s_min = {s_min}, gap = {gap}")
            print(f"    x_min = 5·t·s_min = {5*t*s_min}")
            print(f"    z_min ≈ x_min (for large x/y) = {5*t*s_min}")

            # Required: all prime factors of s are ≡ 1 mod 5
            # Find prime factorization constraints
            # s ≥ 125 = 5^3 but 5 ≢ 1 mod 5!
            # Wait: s is composed of primes ≡ 1 mod p ONLY?
            # No! s = GN/p, and primitive primes q|s satisfy q ≡ 1 mod p.
            # But s could also have factors with q ≢ 1 mod p.
            # Those would go to the "peel" side (p | v_q(s) etc.)

            # Actually: s factors into primitive (q ≡ 1 mod p) and non-primitive parts
            # The descent deals with PRIMITIVE factors only

    print(f"\n\n  CRITICAL INSIGHT:")
    print(
        f"  The descent chain works by removing primitive factors q from s one at a time."
    )
    print(f"  Each removal: s → s/q, x → x/q, z → z' (new)")
    print(f"  After removing ALL primitive factors: s has no factors ≡ 1 mod p")
    print(f"  → s is composed entirely of p and primes ≢ 1 mod p")
    print(f"  → GN has no factors q with q ≡ 1 mod p, q ∤ gap")
    print(f"  → This is the 'FRINGE' condition!")
    print(f"  → BranchA fringe refutation closes this case ✓")
    print(f"")
    print(f"  So the descent IS logically sound IF each step can be taken.")
    print(f"  The open kernel is EXACTLY: 'can each descent step be taken?'")
    print(f"  = GNReducedGap = ∃ z', z'^p = (x/q)^p + y^p")


def analyze_norm_product_constraint(p, q):
    """
    Norm product constraint:
    GN = Π_{j=1}^{p-1} (z - ζ^j·y) in Z[ζ_p]
    = p · s^p in N

    Pairwise coprimality of factors (mod p):
    gcd(z - ζ^i·y, z - ζ^j·y) | (ζ^i - ζ^j)·y | p·y
    (since ζ^i - ζ^j | p in Z[ζ_p] for regular p)

    So away from p: each factor (z - ζ^j·y) contributes independently to s^p.
    """
    print(f"\n{'='*70}")
    print(f"NORM PRODUCT CONSTRAINT: p={p}")
    print(f"{'='*70}")

    # Concrete test: p=5, try small solutions of x^5 + y^5 mod large N
    # to see if GN structure creates obstructions

    # For p=5, Z[ζ_5] = Z[i√5 + stuff], class number = 1
    # So every ideal is principal → Kummer's argument applies
    print(f"  Class number h(Q(ζ_{p})):")
    class_numbers = {
        3: 1,
        5: 1,
        7: 1,
        11: 1,
        13: 1,
        17: 1,
        19: 1,
        23: 3,
        29: 8,
        31: 9,
        37: 37,
        41: 121,
        43: 211,
    }
    if p in class_numbers:
        h = class_numbers[p]
        print(f"    h = {h}")
        if h % p == 0:
            print(
                f"    IRREGULAR: p | h → Kummer's basic argument needs Kummerreich extension"
            )
        else:
            print(f"    REGULAR: p ∤ h → Kummer's argument works directly!")

    # For regular primes (p ∤ h):
    # Each ideal factor (z - ζ^j·y)·Z[ζ_p] is a p-th power ideal
    # Since h is coprime to p, p-th power ideal ↔ p-th power element (up to unit)
    # (z - ζ^j·y) = ε_j · α_j^p  for some unit ε_j and α_j ∈ Z[ζ_p]

    # This gives: z - ζ^j·y = ε_j · α_j^p
    # Taking z - ζ·y = ε · α^p, z - ζ²·y = ε' · β^p
    # Subtracting: (ζ² - ζ)·y = ε'·β^p - ε·α^p
    # This is a UNIT EQUATION in Z[ζ_p]

    # For p=5: units of Z[ζ_5] = <ζ, η> where η = (1+√5)/2 (golden ratio related)
    # The unit equation ε₁·α₁^5 - ε₂·α₂^5 = (ζ^j₁ - ζ^j₂)·y
    # has very rigid structure

    print(f"\n  UNIT EQUATION ANALYSIS (for regular p={p}):")
    print(f"  z - ζ^j·y = ε_j · α_j^p  (Kummer's lemma for regular primes)")
    print(f"  Taking j=1, j=2:")
    print(f"    (ζ - ζ²)·y = ε₁·α₁^p - ε₂·α₂^p")
    print(f"  This is a THUE EQUATION over Z[ζ_p]")
    print(f"  Finitely many solutions → descent terminates")
    print(f"")
    print(f"  BUT: Formalizing Z[ζ_p] in Lean is heavy machinery.")
    print(f"  Can we extract the NUMBER THEORY content without the algebra?")

    # ELEMENTARY EXTRACTION:
    # The key content of "each factor is a p-th power" translates to:
    # For EVERY prime q ≡ 1 (mod p), q ≠ p:
    #   v_q(z - ζ^j·y) ≡ 0 (mod p)  for all j
    # (since α_j^p has all valuations divisible by p)

    # In particular: v_q(GN) = v_q(z - ζ^{j₀}·y) ≡ 0 (mod p)
    # This is ALREADY implied by v_q(GN) = p·v_q(x) (from gap·GN = x^p)!

    # So the p-divisibility of valuations is AUTOMATIC in FLT context.
    # The EXTRA information from Kummer is about non-prime-valuation structure.

    print(f"\n  ELEMENTARY EXTRACTION:")
    print(f"  v_q(z - ζ^j₀·y) ≡ 0 (mod p) is AUTOMATIC from FLT normal form.")
    print(f"  What Kummer adds: the factors (z - ζ^j·y) are p-th powers AS ELEMENTS,")
    print(f"  not just in valuations. This constrains the UNIT part.")
    print(f"")
    print(f"  In elementary terms: z ≡ ζ^j·y + c_j·q^a (mod q^(a+1))")
    print(f"  where a = v_q(z - ζ^j·y) is divisible by p.")
    print(f"  The coefficient c_j is constrained to be a p-th power residue mod q.")

    # THIS is the key: the leading coefficient in the q-adic expansion
    # of (z - ζ^j·y) must be a p-th residue mod q.

    # For q ≡ 1 (mod p), p | (q-1), so p-th power residues mod q
    # form a subgroup of index p in (Z/qZ)*.
    # Probability of being a p-th residue: 1/p.

    # For EACH primitive prime q:
    #   P(leading coeff is p-th residue) = 1/p
    # For k independent primes:
    #   P(all leading coeffs are p-th residues) = 1/p^k

    # With k primitive primes, probability → 0 exponentially.
    # This is the PROBABILISTIC argument for why descent works.

    print(f"\n  PROBABILISTIC ARGUMENT (heuristic):")
    print(f"  Each primitive prime q contributes a 1/p probability filter.")
    print(f"  With k primitive primes: total probability = 1/p^k")
    print(f"  For p=5, k=3 primes: 1/125 ≈ 0.8%")
    print(f"  For p=5, k=5 primes: 1/3125 ≈ 0.03%")
    print(f"  This heuristic suggests solutions don't exist, but is not a proof.")


def analyze_pth_power_residue_constraint(p, q):
    """
    The p-th power residue constraint:
    For primitive prime q, the 'leading coefficient' of z - R·y in q-adic expansion
    must be a p-th power residue mod q.

    If z = R·y + c·q^a + ... where a = v_q(z - R·y):
    then c must be a p-th power residue mod q.

    This is a CONCRETE, VERIFIABLE constraint.
    """
    print(f"\n{'='*70}")
    print(f"P-TH POWER RESIDUE CONSTRAINT: p={p}, q={q}")
    print(f"{'='*70}")

    # p-th power residues mod q
    residues = set()
    for a in range(q):
        residues.add(pow(a, p, q))
    print(f"  p-th power residues mod {q}: {sorted(residues)}")
    print(f"  Count: {len(residues)} out of {q} (ratio = {len(residues)/q:.3f})")
    print(f"  Non-zero residues: {len(residues) - 1} out of {q-1}")

    # In FLT context:
    # z - R·y = c · q^a where p | a
    # z^p - y^p factors in Z[ζ_p] as Π (z - ζ^j·y)
    # Each factor: z - ζ^j·y = ε_j · α_j^p (for regular p)
    # So: leading coeff c_j is a p-th power residue mod q ✓

    # But ALSO: the OTHER factors z - ζ^j·y for j ≠ j₀ must have
    # v_q(z - ζ^j·y) = 0 (since v_q concentrates on j₀).
    # Their leading coefficients (= z - ζ^j·y mod q) are NONZERO.

    # If p is regular: these j ≠ j₀ factors, reduced mod q, must also
    # have some structure (they are p-th powers of elements of Z[ζ_p]/q).

    # But Z[ζ_p]/(q) ≅ (F_q)^{p-1} for q ≡ 1 (mod p)!
    # (q splits completely in Q(ζ_p))

    # So the constraint is: in EACH copy of F_q,
    # the image of α_j^p is the image of (z - ζ^j·y).
    # For the j₀ component: α_{j₀}^p has q-valuation, handled separately.
    # For j ≠ j₀: (z - ζ^j·y) mod q_{(j)} must be a p-th power in F_q.

    omega = find_primitive_root(q, p)
    if omega is None:
        return

    print(f"\n  In F_{q}: ω = {omega}")

    # For given (z,y) with z ≡ ω^{j₀}·y (mod q):
    # z - ω^j·y ≡ (ω^{j₀} - ω^j)·y (mod q) for j ≠ j₀
    # This must be a p-th power residue mod q for ALL j ≠ j₀

    print(
        f"\n  CONSTRAINT: (ω^j₀ - ω^j) · y must be p-th power residue mod q, ∀ j ≠ j₀"
    )
    print(f"  Since y is coprime to q, y is invertible.")
    print(f"  Equivalent: (ω^j₀ - ω^j) must be p-th power residue mod q, ∀ j ≠ j₀")
    print(f"  (after absorbing y^{p-1} into the unit)")

    non_zero_residues = residues - {0}

    for j0 in range(1, p):
        print(f"\n  j₀ = {j0}: z ≡ ω^{j0}·y ≡ {pow(omega, j0, q)}·y (mod q)")
        all_residue = True
        for j in range(1, p):
            if j == j0:
                continue
            diff = (pow(omega, j0, q) - pow(omega, j, q)) % q
            is_pth_power = diff in non_zero_residues
            status = "✓ p-th power" if is_pth_power else "✗ NOT p-th power"
            print(f"    j={j}: ω^{j0} - ω^{j} ≡ {diff} (mod {q})  {status}")
            if not is_pth_power:
                all_residue = False

        if all_residue:
            print(
                f"    → ALL differences are p-th power residues! Compatible with FLT."
            )
        else:
            print(f"    → SOME differences are NOT p-th power residues!")
            print(f"    → If Kummer's lemma applies, this j₀ is EXCLUDED!")


# Main execution
if __name__ == "__main__":
    p = 5
    q = 11

    analyze_kummer_structure(p, q)
    analyze_norm_product_constraint(p, q)
    analyze_pth_power_residue_constraint(p, q)

    # Also test with q = 31
    print(f"\n\n{'#'*70}")
    print(f"# SECOND PRIME TEST")
    print(f"{'#'*70}")
    analyze_pth_power_residue_constraint(p, 31)
    analyze_pth_power_residue_constraint(p, 41)
