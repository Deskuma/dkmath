# Memo 026: GNReducedGap の根本的構造分析: 循環性と descent の関係

```python
#!/usr/bin/env python3
"""
GNReducedGap の根本的構造分析: 循環性と descent の関係

KEY DISCOVERY:
  GN(p, gap, y)/p = s^p  は  x^p + y^p = z^p と同値（normal form の定義から）。
  つまり「GN/p が完全冪」を直接否定するアプローチは FLT そのもの。

  しかし DESCENT は異なる:
  「最小反例から、より小さい反例を構成」→ 矛盾

  この descent の核心を代数的に分析する。
"""
from math import gcd, comb
from sympy import factorint, isprime


def GN(p, gap, y):
    """GN(p, gap, y) = Σ_{k=0}^{p-1} C(p, k+1) * gap^k * y^{p-1-k}"""
    return sum(comb(p, k + 1) * gap**k * y ** (p - 1 - k) for k in range(p))


# ============================================================
# PART 1: 循環性の代数的証明
# ============================================================
print("=" * 70)
print("PART 1: CIRCULARITY — GN/p = s^p ⟺ FLT counterexample")
print("=" * 70)

p = 5
print(f"\np = {p}")
print(f"gap = p^(p-1) * t^p = {p**(p-1)} * t^{p}")
print()

print("Algebraic identity (Cosmic Identity):")
print(f"  gap · GN(p, gap, y) = (gap + y)^p - y^p")
print()
print("Setting z = gap + y, x = p·t·s:")
print(f"  GN/p = s^p")
print(f"  ⟺ gap · GN = gap · p · s^p = p^(p-1)·t^p · p · s^p = (p·t·s)^p = x^p")
print(f"  ⟺ (gap+y)^p - y^p = x^p")
print(f"  ⟺ z^p = x^p + y^p")
print(f"  ⟺ FLT counterexample! ★")
print()

# Numerical verification
for t in [1, 2]:
    gap = p ** (p - 1) * t**p
    for y in [1, 3, 7, 11]:
        z = gap + y
        gn = GN(p, gap, y)
        assert gap * gn == z**p - y**p, "Cosmic Identity failed!"

        # GN/p = s^p ⟺ z^p - y^p = x^p where x = p*t*s
        # i.e. ∃ x, x^p = z^p - y^p
        lhs = z**p - y**p
        # Check: is lhs a perfect p-th power?
        x_approx = round(lhs ** (1.0 / p))
        is_pth = any((x_approx + d) ** p == lhs for d in range(-2, 3))
        if y <= 3:
            print(f"  t={t}, y={y}: z={z}, z^p-y^p = {lhs}")
            print(f"    GN = {gn}, GN/p = {gn//p}")
            print(f"    z^p - y^p is a {p}th power? {is_pth}")
            if is_pth:
                x_val = next(
                    x_approx + d for d in range(-2, 3) if (x_approx + d) ** p == lhs
                )
                print(
                    f"    x = {x_val}, checking FLT: {x_val}^{p} + {y}^{p} = {z}^{p}?",
                    x_val**p + y**p == z**p,
                )

print()
print("CONCLUSION: GN/p = s^p is TAUTOLOGICALLY equivalent to FLT.")
print("Direct attack on this condition is circular.")

# ============================================================
# PART 2: DESCENT の非循環的構造
# ============================================================
print()
print("=" * 70)
print("PART 2: DESCENT — How it breaks the circularity")
print("=" * 70)
print()
print("Descent argument:")
print("  Given: MINIMAL counterexample (x, y, z) with z minimal")
print("  Show: ∃ smaller counterexample (x', y, z') with z' < z")
print("  Contradiction!")
print()
print("The key: in the MINIMAL counterexample,")
print("  x = p·t·s, s has primitive prime q ≡ 1 (mod p)")
print("  x' = x/q = p·t·(s/q)")
print("  Need: z'^p = x'^p + y^p for some z' < z")
print()

# ============================================================
# PART 3: DESCENT EXISTENCE — z' の構造的制約
# ============================================================
print("=" * 70)
print("PART 3: DESCENT EXISTENCE — structural constraints on z'")
print("=" * 70)

print()
print("If z'^p = (x/q)^p + y^p:")
print("  z'^p = x^p/q^p + y^p")
print("  q^p · z'^p = x^p + q^p · y^p")
print("  q^p · z'^p = z^p - y^p + q^p · y^p   [since x^p = z^p - y^p]")
print("  q^p · z'^p = z^p + (q^p - 1) · y^p")
print()
print("This is a NON-TRIVIAL Diophantine equation!")
print("  z' exists ⟺ z^p + (q^p-1)·y^p ≡ 0 mod q^p")
print("  ⟺ z^p ≡ y^p mod q^p   [since q^p-1 ≡ -1 mod q^p]")
print("  ⟺ (z/y)^p ≡ 1 mod q^p")
print()

# Verify: z^p + (q^p - 1)*y^p is divisible by q^p?
# This requires z^p ≡ y^p (mod q^p),
# i.e. z ≡ ω·y (mod q) where ω^p ≡ 1 (mod q) (from q ≡ 1 mod p)
# And more precisely: (z/y)^p ≡ 1 (mod q^p)

print("Condition: (z/y)^p ≡ 1 mod q^p")
print("  ⟺ z ≡ R_j · y (mod q^p )  for some Hensel root R_j of X^p - 1")
print()

# For p=5, q=11:
q = 11
print(f"Example: p={p}, q={q}")
print(f"  q^p = {q**p}")

# Find p-th roots of unity mod q
roots_mod_q = [r for r in range(1, q) if pow(r, p, q) == 1]
print(f"  p-th roots of 1 mod {q}: {roots_mod_q}")

# Hensel lift to mod q^p
qp = q**p
roots_mod_qp = [r for r in range(qp) if pow(r, p, qp) == 1]
print(f"  p-th roots of 1 mod {q}^{p} = {qp}: {roots_mod_qp}")
print()

# ============================================================
# PART 4: DESCENT の十分条件を分析
# ============================================================
print("=" * 70)
print("PART 4: SUFFICIENT CONDITIONS for descent")
print("=" * 70)
print()
print("For descent to work, we need TWO things:")
print("  (A) z^p ≡ y^p (mod q^p)  — NECESSARY for z' to be integer")
print("  (B) z' < z              — NECESSARY for infinite descent")
print()
print("Condition (A) is equivalent to q^p | GN(p, gap, y),")
print("which is q^p | s^p (since GN = p·s^p and gcd(p,q)=1),")
print("i.e., q | s. This is GIVEN (q is a prime factor of s).")
print()

# Verify condition (A): q | s ⟹ q^p | GN
print("Verification: q | s ⟹ q^p | GN")
print("-" * 40)
for t_val in [1, 2]:
    gap_val = p ** (p - 1) * t_val**p
    for y_val in [1, 3, 7]:
        gn_val = GN(p, gap_val, y_val)
        # Check: is gn divisible by q^p?
        vq = 0
        temp = gn_val
        while temp % q == 0:
            temp //= q
            vq += 1
        # Also check GN ≡ z^{p-1} + ... mod q
        z_val = gap_val + y_val
        # v_q of GN depends on v_q of z - R_j·y
        print(f"  t={t_val}, y={y_val}: GN = {gn_val}, v_{q}(GN) = {vq}", end="")
        # Check z mod q
        z_mod_q = z_val % q
        y_mod_q = y_val % q
        ratio_mod_q = (z_mod_q * pow(y_mod_q, q - 2, q)) % q if y_mod_q != 0 else "N/A"
        print(f", z/y mod {q} = {ratio_mod_q}", end="")
        # Is ratio a p-th root of 1?
        if isinstance(ratio_mod_q, int):
            is_root = pow(ratio_mod_q, p, q) == 1
            print(f", is {p}th root: {is_root}", end="")
        print()

print()

# ============================================================
# PART 5: DESCENT SIZE — z' < z?
# ============================================================
print("=" * 70)
print("PART 5: SIZE ANALYSIS — Is z' < z always guaranteed?")
print("=" * 70)
print()

print("z'^p = x'^p + y^p = (x/q)^p + y^p < x^p + y^p = z^p")
print("⟹ z' < z  ✓  (trivially!)")
print()
print("More precisely:")
print("  z'^p = (x/q)^p + y^p = x^p/q^p + y^p")
print("  z^p = x^p + y^p")
print("  z'^p/z^p = (x^p/q^p + y^p)/(x^p + y^p)")
print("           = (1/q^p + (y/x)^p) / (1 + (y/x)^p)")
print("           < 1  since q ≥ 2")
print("⟹ z' < z  ✓")
print()

# ============================================================
# PART 6: THE REAL QUESTION — Does z' exist as a natural number?
# ============================================================
print("=" * 70)
print("PART 6: THE REAL QUESTION — z' ∈ ℕ?")
print("=" * 70)
print()

print("z'^p = (x/q)^p + y^p")
print("This requires (x/q)^p + y^p to be a PERFECT p-th POWER.")
print()
print("We know:")
print("  q^p | (z^p + (q^p-1)y^p)  [from condition (A)]")
print("  z'^p = (z^p + (q^p-1)y^p) / q^p")
print()
print("BUT: z^p + (q^p-1)y^p being divisible by q^p")
print("     does NOT guarantee the quotient is a perfect p-th power!")
print()

# Concrete example
print("Concrete analysis:")
print("-" * 40)

# For p=5, if we ASSUME a counterexample exists,
# what does z^p + (q^p-1)*y^p look like?

print()
print("Key modular analysis:")
print(f"  z^p + (q^p - 1)·y^p ≡ z^p - y^p ≡ x^p ≡ 0 (mod q^p)")
print(f"  (since q | x)")
print()
print(f"  z'^p = [z^p + (q^p-1)·y^p] / q^p")
print(f"       = z^p/q^p + y^p - y^p/q^p")
print(f"       = (z/q)^p · something + ...")
print()

# The question reduces to: can we write this as a p-th power?
# (x/q)^p + y^p = z'^p
# This is ANOTHER FERMAT EQUATION with smaller x' = x/q.

print("★★★ FUNDAMENTAL INSIGHT ★★★")
print()
print("GNReducedGap target asks: ∃ z', z'^p = (x/q)^p + y^p")
print()
print("This is EXACTLY asking: does (x/q, y) extend to a Fermat triple?")
print()
print("If YES → smaller counterexample → descent continues")
print("If NO  → the original counterexample has ISOLATED structure")
print()
print("For the DESCENT to work, we need: every Fermat triple (x,y,z)")
print("with q | x can be reduced to (x/q, y, z').")
print()
print("This is TRUE if and only if the Fermat curve X^p + Y^p = Z^p")
print("has the property that: for every point (x:y:z) on it,")
print("the point (x/q : y : z') also lies on it.")
print()
print("Over Q this is trivially true (just rescale!)")
print("  (x : y : z) → (x/q : y : ?) needs z' = (x^p/q^p + y^p)^{1/p}")
print("  Over Q: z' = z · ((x/q)^p + y^p)^{1/p} / (x^p + y^p)^{1/p}")
print("  This is in Q but NOT necessarily in N!")
print()
print("★ THE GAP IS: Q-rational vs N-integral ★")

# ============================================================
# PART 7: THE ELEMENT OF PROOF THAT COULD WORK
# ============================================================
print()
print("=" * 70)
print("PART 7: PROOF STRATEGIES")
print("=" * 70)
print()

print("Strategy 1: KUMMER (classical)")
print("  Use Z[ζ_p] ideal factorization to force z - ζ^j·y = unit · β_j^p")
print("  This gives β_j as a 'p-th root' in the number field")
print("  Works for regular primes, needs extra argument for irregular primes")
print()

print("Strategy 2: NORM DESCENT (Cosmic variant)")
print("  GN = Π(z - ζ^j·y) = p·s^p")
print("  Each factor z - ζ^j·y shares only (1-ζ) with other factors")
print("  If Z[ζ_p] is a PID: each z - ζ^j·y = unit · (1-ζ)^{a_j} · β_j^p")
print("  N(β_j) gives the Fermat descent")
print()

print("Strategy 3: MODULAR DESCENT (elementary)")
print("  Instead of working in Z[ζ_p], stay in Z")
print("  Use the GN polynomial structure + primitive prime properties")
print("  Show that the mod q^p structure of GN forces descent")
print("  THIS IS WHAT WE'VE BEEN ATTEMPTING")
print()

print("Strategy 4: SELF-SIMILAR DESCENT (new idea)")
print("  The counterexample (x,y,z) with x = p·t·s and q|s")
print("  gives gap·GN = x^p where GN = p·s^p")
print("  ")
print("  Now consider (gap', GN') with gap' = gap, s' = s/q:")
print("  GN' = p·(s/q)^p = GN/q^p")
print("  gap·GN' = gap·GN/q^p = x^p/q^p = (x/q)^p")
print("  ")
print("  So: gap · (GN/q^p) = (x/q)^p")
print("  And: (gap + y)^p - y^p = gap·GN = x^p")
print("  Want: (gap + y')^p - y'^p = gap·(GN/q^p) = (x/q)^p")
print("  i.e.: ∃ y' with (gap + y')^p - y'^p = gap · GN/q^p")
print()
print("  This requires GN(p, gap, y') = GN/q^p")
print("  i.e.: find y' such that GN(p, gap, y') = GN(p, gap, y)/q^p")
print()

# Is there such y'?
print("  Testing: can we find y' with GN(p, gap, y') = target?")
print("  " + "-" * 50)

gap_test = p ** (p - 1)  # t=1
for y_test in [7, 11, 13, 17, 23]:
    if gcd(y_test, p) != 1:
        continue
    gn_test = GN(p, gap_test, y_test)
    target = gn_test  # We'd need to divide by q^p for an actual q

    # Find the hypothetical "reduced GN" for different q
    for q_test in [11, 31, 41]:
        if gn_test % (q_test**p) != 0:
            continue
        reduced_gn = gn_test // (q_test**p)
        # Find y' such that GN(p, gap_test, y') = reduced_gn
        # GN is a degree p-1 polynomial in y with positive coefficients
        # So it's monotonically increasing for y > 0
        # Binary search:
        lo, hi = 0, y_test
        found = False
        while lo <= hi:
            mid = (lo + hi) // 2
            val = GN(p, gap_test, mid)
            if val == reduced_gn:
                print(f"  y={y_test}, q={q_test}: y'={mid}, GN reduced by q^p ✓")
                found = True
                break
            elif val < reduced_gn:
                lo = mid + 1
            else:
                hi = mid - 1
        if not found:
            # Check what values GN takes
            val_lo = GN(p, gap_test, hi) if hi >= 0 else 0
            val_hi = GN(p, gap_test, hi + 1) if hi + 1 <= y_test else "N/A"
            pass  # Silent for non-hits

print()

# ============================================================
# PART 8: 新アイデア — GN の y-monotonicity を使った descent
# ============================================================
print("=" * 70)
print("PART 8: NEW IDEA — y-monotonicity based descent")
print("=" * 70)
print()

print("GN(p, gap, y) is a polynomial of degree p-1 in y:")
print(f"  GN(p, gap, y) = Σ C(p,k+1) gap^k y^(p-1-k)")
print(f"  = C(p,1)y^(p-1) + C(p,2)·gap·y^(p-2) + ... + gap^(p-1)")
print(f"  = p·y^(p-1) + ... + gap^(p-1)")
print()
print("For fixed gap, GN is STRICTLY INCREASING in y (for y > 0).")
print("Also: GN(p, gap, 0) = gap^(p-1) > 0")
print()

print("The descent question can be reformulated:")
print("  Given GN₀ = GN(p, gap, y₀) = p·s^p")
print("  Find y₁ with GN(p, gap, y₁) = p·(s/q)^p = GN₀/q^p")
print()
print("  Since GN is continuous and increasing:")
print("  ∃ unique real y₁ with GN(p, gap, y₁) = GN₀/q^p")
print("  But y₁ must be a POSITIVE INTEGER! ← This is the gap")
print()

# Compute the "real" y₁ for specific cases
print("Numerical analysis of the 'real' y₁:")
print("-" * 50)

import numpy as np


def GN_float(p, gap, y):
    return sum(comb(p, k + 1) * gap**k * y ** (p - 1 - k) for k in range(p))


gap_val = p ** (p - 1)  # = 625 for p=5

for y0 in [10, 50, 100, 500]:
    gn0 = GN_float(p, gap_val, y0)
    for q_val in [11]:
        target = gn0 / q_val**p
        # Binary search for real y₁
        lo_f, hi_f = 0.0, float(y0)
        for _ in range(200):  # bisection
            mid_f = (lo_f + hi_f) / 2
            if GN_float(p, gap_val, mid_f) < target:
                lo_f = mid_f
            else:
                hi_f = mid_f
        y1_real = (lo_f + hi_f) / 2
        y1_int = round(y1_real)
        gn_at_y1 = GN(p, gap_val, y1_int)
        diff = gn_at_y1 - int(target)
        print(f"  y₀={y0}, q={q_val}: y₁_real = {y1_real:.6f}, y₁_int = {y1_int}")
        print(f"    GN(y₁_int) = {gn_at_y1}, target = {int(target)}, diff = {diff}")
        print(f"    y₁/y₀ = {y1_real/y0:.6f}")

print()
print("★ CRITICAL OBSERVATION:")
print("  y₁/y₀ approaches 1/q^{p/(p-1)} as y₀ → ∞")
print(f"  For p=5, q=11: 1/11^(5/4) ≈ {1/11**(5/4):.6f}")
print()

# Verify asymptotic ratio
print("Asymptotic ratio analysis:")
print("-" * 50)
for y0 in [100, 1000, 10000, 100000]:
    gn0 = GN_float(p, gap_val, float(y0))
    target = gn0 / 11**p
    lo_f, hi_f = 0.0, float(y0)
    for _ in range(200):
        mid_f = (lo_f + hi_f) / 2
        if GN_float(p, gap_val, mid_f) < target:
            lo_f = mid_f
        else:
            hi_f = mid_f
    y1_real = (lo_f + hi_f) / 2
    ratio = y1_real / y0
    expected = 1 / 11 ** (5 / 4)
    print(f"  y₀={y0}: y₁/y₀ = {ratio:.8f} (expected: {expected:.8f})")

# ============================================================
# PART 9: DESCENT VIA GAP REDUCTION (alternative)
# ============================================================
print()
print("=" * 70)
print("PART 9: ALTERNATIVE — Descent via gap reduction")
print("=" * 70)
print()

print("Instead of fixing gap and changing y,")
print("fix y and REDUCE gap:")
print()
print("  gap₀ = p^(p-1)·t^p · q^p  (if q | gap factorization)")
print("  gap₁ = p^(p-1)·t₁^p  with t₁ = t/q (if q | t)")
print("  GN₁ = GN(p, gap₁, y) ≠ GN₀/q^p in general")
print()
print("  OR: gap₀ = gap, y₀ = y, z₀ = gap + y")
print("  z₁ = z₀/q... but q may not divide z!")
print()

print("★ SUMMARY OF OBSTRUCTION ★")
print()
print("The descent from (x,y,z) to (x/q, y, z') requires:")
print("  z'^p = (x/q)^p + y^p")
print()
print("This is equivalent to: the polynomial T^p - (x/q)^p - y^p")
print("has a POSITIVE INTEGER ROOT.")
print()
print("Over Q: the Fermat curve x^p + y^p = z^p has genus (p-1)(p-2)/2 ≥ 3")
print("for p ≥ 5, so by Faltings' theorem, only finitely many rational points.")
print()
print("The descent asks: given one rational point (x,y,z),")
print("does (x/q, y, z') give ANOTHER rational point?")
print()
print("By Faltings: there are only finitely many, so eventually descent fails.")
print("But we need to show it fails at the FIRST step (or at least eventually).")
print()
print("THIS IS THE ESSENTIAL DIFFICULTY of elementary FLT proofs.")
print("The descent chain needs a structural argument, not just size reduction.")

# ============================================================
# PART 10: WHAT CAN BE FORMALIZED NOW
# ============================================================
print()
print("=" * 70)
print("PART 10: FORMALIZABLE RESULTS")
print("=" * 70)
print()
print("1. GN = Π_{j=1}^{p-1} (z - ζ^j·y)  [algebraic identity] ← Lean ✓")
print("2. QAdicResidue: z ≡ ω^j·y (mod q)   [from q | GN, q ∤ gap] ← Lean ✓")
print("3. SuperWieferich: z ≡ R_j·y (mod q^p) [Hensel] ← Lean (type only)")
print("4. z' < z (size reduction)             [trivial] ← Lean ✓")
print("5. descent existence ⟺ z'^p = (x/q)^p + y^p ∈ ℕ ← OPEN ★")
print()
print("Items 1-4 strengthen the formalization.")
print("Item 5 remains the essential open kernel.")
print()
print("★ NEW INSIGHT for formalization:")
print("  GNReducedGap can be decomposed into:")
print("  (5a) q^p | GN  ← proved (from q | s)")
print("  (5b) GN/q^p = GN(p, gap', y') for some (gap', y') ← OPEN")
print("  (5c) gap'·(GN/q^p) = (x/q)^p ← follows from gap·GN = x^p")
print()
print("Wait, (5c) is WRONG! gap·(GN/q^p) = x^p/q^p = (x/q)^p ✓")
print("But this means gap_new = gap (SAME gap), s_new = s/q.")
print("z_new is different: z_new = gap + y_new where")
print("  gap · GN(p, gap, y_new) = (x/q)^p")
print("  GN(p, gap, y_new) = GN(p, gap, y)/q^p")
print()
print("So the question is: ∃ y_new ∈ ℕ with GN(p, gap, y_new) = GN(p,gap,y)/q^p")
print("This is a POLYNOMIAL ROOT-FINDING problem on GN as a function of y!")
```

```md
======================================================================
PART 1: CIRCULARITY — GN/p = s^p ⟺ FLT counterexample
======================================================================

p = 5
gap = p^(p-1) * t^p = 625 * t^5

Algebraic identity (Cosmic Identity):
  gap · GN(p, gap, y) = (gap + y)^p - y^p

Setting z = gap + y, x = p·t·s:
  GN/p = s^p
  ⟺ gap · GN = gap · p · s^p = p^(p-1)·t^p · p · s^p = (p·t·s)^p = x^p
  ⟺ (gap+y)^p - y^p = x^p
  ⟺ z^p = x^p + y^p
  ⟺ FLT counterexample! ★

  t=1, y=1: z=626, z^p-y^p = 96132816409375
    GN = 153812506255, GN/p = 30762501251
    z^p - y^p is a 5th power? False
  t=1, y=3: z=628, z^p-y^p = 97678328378125
    GN = 156285325405, GN/p = 31257065081
    z^p - y^p is a 5th power? False
  t=2, y=1: z=20001, z^p-y^p = 3200800080004000100000
    GN = 160040004000200005, GN/p = 32008000800040001
    z^p - y^p is a 5th power? False
  t=2, y=3: z=20003, z^p-y^p = 3202400720108008100000
    GN = 160120036005400405, GN/p = 32024007201080081
    z^p - y^p is a 5th power? False

CONCLUSION: GN/p = s^p is TAUTOLOGICALLY equivalent to FLT.
Direct attack on this condition is circular.

======================================================================
PART 2: DESCENT — How it breaks the circularity
======================================================================

Descent argument:
  Given: MINIMAL counterexample (x, y, z) with z minimal
  Show: ∃ smaller counterexample (x', y, z') with z' < z
  Contradiction!

The key: in the MINIMAL counterexample,
  x = p·t·s, s has primitive prime q ≡ 1 (mod p)
  x' = x/q = p·t·(s/q)
  Need: z'^p = x'^p + y^p for some z' < z

======================================================================
PART 3: DESCENT EXISTENCE — structural constraints on z'
======================================================================

If z'^p = (x/q)^p + y^p:
  z'^p = x^p/q^p + y^p
  q^p · z'^p = x^p + q^p · y^p
  q^p · z'^p = z^p - y^p + q^p · y^p   [since x^p = z^p - y^p]
  q^p · z'^p = z^p + (q^p - 1) · y^p

This is a NON-TRIVIAL Diophantine equation!
  z' exists ⟺ z^p + (q^p-1)·y^p ≡ 0 mod q^p
  ⟺ z^p ≡ y^p mod q^p   [since q^p-1 ≡ -1 mod q^p]
  ⟺ (z/y)^p ≡ 1 mod q^p

Condition: (z/y)^p ≡ 1 mod q^p
  ⟺ z ≡ R_j · y (mod q^p )  for some Hensel root R_j of X^p - 1

Example: p=5, q=11
  q^p = 161051
  p-th roots of 1 mod 11: [1, 3, 4, 5, 9]
  p-th roots of 1 mod 11^5 = 161051: [1, 37107, 46709, 104450, 133835]

======================================================================
PART 4: SUFFICIENT CONDITIONS for descent
======================================================================

For descent to work, we need TWO things:
  (A) z^p ≡ y^p (mod q^p)  — NECESSARY for z' to be integer
  (B) z' < z              — NECESSARY for infinite descent

Condition (A) is equivalent to q^p | GN(p, gap, y),
which is q^p | s^p (since GN = p·s^p and gcd(p,q)=1),
i.e., q | s. This is GIVEN (q is a prime factor of s).

Verification: q | s ⟹ q^p | GN
----------------------------------------
  t=1, y=1: GN = 153812506255, v_11(GN) = 0, z/y mod 11 = 10, is 5th root: False
  t=1, y=3: GN = 156285325405, v_11(GN) = 1, z/y mod 11 = 4, is 5th root: True
  t=1, y=7: GN = 161326374505, v_11(GN) = 0, z/y mod 11 = 7, is 5th root: False
  t=2, y=1: GN = 160040004000200005, v_11(GN) = 1, z/y mod 11 = 3, is 5th root: True
  t=2, y=3: GN = 160120036005400405, v_11(GN) = 1, z/y mod 11 = 9, is 5th root: True
  t=2, y=7: GN = 160280196068612005, v_11(GN) = 0, z/y mod 11 = 6, is 5th root: False

======================================================================
PART 5: SIZE ANALYSIS — Is z' < z always guaranteed?
======================================================================

z'^p = x'^p + y^p = (x/q)^p + y^p < x^p + y^p = z^p
⟹ z' < z  ✓  (trivially!)

More precisely:
  z'^p = (x/q)^p + y^p = x^p/q^p + y^p
  z^p = x^p + y^p
  z'^p/z^p = (x^p/q^p + y^p)/(x^p + y^p)
           = (1/q^p + (y/x)^p) / (1 + (y/x)^p)
           < 1  since q ≥ 2
⟹ z' < z  ✓

======================================================================
PART 6: THE REAL QUESTION — z' ∈ ℕ?
======================================================================

z'^p = (x/q)^p + y^p
This requires (x/q)^p + y^p to be a PERFECT p-th POWER.

We know:
  q^p | (z^p + (q^p-1)y^p)  [from condition (A)]
  z'^p = (z^p + (q^p-1)y^p) / q^p

BUT: z^p + (q^p-1)y^p being divisible by q^p
     does NOT guarantee the quotient is a perfect p-th power!

Concrete analysis:
----------------------------------------

Key modular analysis:
  z^p + (q^p - 1)·y^p ≡ z^p - y^p ≡ x^p ≡ 0 (mod q^p)
  (since q | x)

  z'^p = [z^p + (q^p-1)·y^p] / q^p
       = z^p/q^p + y^p - y^p/q^p
       = (z/q)^p · something + ...

★★★ FUNDAMENTAL INSIGHT ★★★

GNReducedGap target asks: ∃ z', z'^p = (x/q)^p + y^p

This is EXACTLY asking: does (x/q, y) extend to a Fermat triple?

If YES → smaller counterexample → descent continues
If NO  → the original counterexample has ISOLATED structure

For the DESCENT to work, we need: every Fermat triple (x,y,z)
with q | x can be reduced to (x/q, y, z').

This is TRUE if and only if the Fermat curve X^p + Y^p = Z^p
has the property that: for every point (x:y:z) on it,
the point (x/q : y : z') also lies on it.

Over Q this is trivially true (just rescale!)
  (x : y : z) → (x/q : y : ?) needs z' = (x^p/q^p + y^p)^{1/p}
  Over Q: z' = z · ((x/q)^p + y^p)^{1/p} / (x^p + y^p)^{1/p}
  This is in Q but NOT necessarily in N!

★ THE GAP IS: Q-rational vs N-integral ★

======================================================================
PART 7: PROOF STRATEGIES
======================================================================

Strategy 1: KUMMER (classical)
  Use Z[ζ_p] ideal factorization to force z - ζ^j·y = unit · β_j^p
  This gives β_j as a 'p-th root' in the number field
  Works for regular primes, needs extra argument for irregular primes

Strategy 2: NORM DESCENT (Cosmic variant)
  GN = Π(z - ζ^j·y) = p·s^p
  Each factor z - ζ^j·y shares only (1-ζ) with other factors
  If Z[ζ_p] is a PID: each z - ζ^j·y = unit · (1-ζ)^{a_j} · β_j^p
  N(β_j) gives the Fermat descent

Strategy 3: MODULAR DESCENT (elementary)
  Instead of working in Z[ζ_p], stay in Z
  Use the GN polynomial structure + primitive prime properties
  Show that the mod q^p structure of GN forces descent
  THIS IS WHAT WE'VE BEEN ATTEMPTING

Strategy 4: SELF-SIMILAR DESCENT (new idea)
  The counterexample (x,y,z) with x = p·t·s and q|s
  gives gap·GN = x^p where GN = p·s^p
  
  Now consider (gap', GN') with gap' = gap, s' = s/q:
  GN' = p·(s/q)^p = GN/q^p
  gap·GN' = gap·GN/q^p = x^p/q^p = (x/q)^p
  
  So: gap · (GN/q^p) = (x/q)^p
  And: (gap + y)^p - y^p = gap·GN = x^p
  Want: (gap + y')^p - y'^p = gap·(GN/q^p) = (x/q)^p
  i.e.: ∃ y' with (gap + y')^p - y'^p = gap · GN/q^p

  This requires GN(p, gap, y') = GN/q^p
  i.e.: find y' such that GN(p, gap, y') = GN(p, gap, y)/q^p

  Testing: can we find y' with GN(p, gap, y') = target?
  --------------------------------------------------

======================================================================
PART 8: NEW IDEA — y-monotonicity based descent
======================================================================

GN(p, gap, y) is a polynomial of degree p-1 in y:
  GN(p, gap, y) = Σ C(p,k+1) gap^k y^(p-1-k)
  = C(p,1)y^(p-1) + C(p,2)·gap·y^(p-2) + ... + gap^(p-1)
  = p·y^(p-1) + ... + gap^(p-1)

For fixed gap, GN is STRICTLY INCREASING in y (for y > 0).
Also: GN(p, gap, 0) = gap^(p-1) > 0

The descent question can be reformulated:
  Given GN₀ = GN(p, gap, y₀) = p·s^p
  Find y₁ with GN(p, gap, y₁) = p·(s/q)^p = GN₀/q^p

  Since GN is continuous and increasing:
  ∃ unique real y₁ with GN(p, gap, y₁) = GN₀/q^p
  But y₁ must be a POSITIVE INTEGER! ← This is the gap

Numerical analysis of the 'real' y₁:
--------------------------------------------------
  y₀=10, q=11: y₁_real = 0.000000, y₁_int = 0
    GN(y₁_int) = 152587890625, target = 1025711, diff = 152586864914
    y₁/y₀ = 0.000000
  y₀=50, q=11: y₁_real = 0.000000, y₁_int = 0
    GN(y₁_int) = 152587890625, target = 1392112, diff = 152586498513
    y₁/y₀ = 0.000000
  y₀=100, q=11: y₁_real = 0.000000, y₁_int = 0
    GN(y₁_int) = 152587890625, target = 1989870, diff = 152585900755
    y₁/y₀ = 0.000000
  y₀=500, q=11: y₁_real = 0.000000, y₁_int = 0
    GN(y₁_int) = 152587890625, target = 17592265, diff = 152570298360
    y₁/y₀ = 0.000000

★ CRITICAL OBSERVATION:
  y₁/y₀ approaches 1/q^{p/(p-1)} as y₀ → ∞
  For p=5, q=11: 1/11^(5/4) ≈ 0.049918

Asymptotic ratio analysis:
--------------------------------------------------
  y₀=100: y₁/y₀ = 0.00000000 (expected: 0.04991823)
  y₀=1000: y₁/y₀ = 0.00000000 (expected: 0.04991823)
  y₀=10000: y₁/y₀ = 0.01136443 (expected: 0.04991823)
  y₀=100000: y₁/y₀ = 0.04685201 (expected: 0.04991823)

======================================================================
PART 9: ALTERNATIVE — Descent via gap reduction
======================================================================

Instead of fixing gap and changing y,
fix y and REDUCE gap:

  gap₀ = p^(p-1)·t^p · q^p  (if q | gap factorization)
  gap₁ = p^(p-1)·t₁^p  with t₁ = t/q (if q | t)
  GN₁ = GN(p, gap₁, y) ≠ GN₀/q^p in general

  OR: gap₀ = gap, y₀ = y, z₀ = gap + y
  z₁ = z₀/q... but q may not divide z!

★ SUMMARY OF OBSTRUCTION ★

The descent from (x,y,z) to (x/q, y, z') requires:
  z'^p = (x/q)^p + y^p

This is equivalent to: the polynomial T^p - (x/q)^p - y^p
has a POSITIVE INTEGER ROOT.

Over Q: the Fermat curve x^p + y^p = z^p has genus (p-1)(p-2)/2 ≥ 3
for p ≥ 5, so by Faltings' theorem, only finitely many rational points.

The descent asks: given one rational point (x,y,z),
does (x/q, y, z') give ANOTHER rational point?

By Faltings: there are only finitely many, so eventually descent fails.
But we need to show it fails at the FIRST step (or at least eventually).

THIS IS THE ESSENTIAL DIFFICULTY of elementary FLT proofs.
The descent chain needs a structural argument, not just size reduction.

======================================================================
PART 10: FORMALIZABLE RESULTS
======================================================================

1. GN = Π_{j=1}^{p-1} (z - ζ^j·y)  [algebraic identity] ← Lean ✓
2. QAdicResidue: z ≡ ω^j·y (mod q)   [from q | GN, q ∤ gap] ← Lean ✓
3. SuperWieferich: z ≡ R_j·y (mod q^p) [Hensel] ← Lean (type only)
4. z' < z (size reduction)             [trivial] ← Lean ✓
5. descent existence ⟺ z'^p = (x/q)^p + y^p ∈ ℕ ← OPEN ★

Items 1-4 strengthen the formalization.
Item 5 remains the essential open kernel.

★ NEW INSIGHT for formalization:
  GNReducedGap can be decomposed into:
  (5a) q^p | GN  ← proved (from q | s)
  (5b) GN/q^p = GN(p, gap', y') for some (gap', y') ← OPEN
  (5c) gap'·(GN/q^p) = (x/q)^p ← follows from gap·GN = x^p

Wait, (5c) is WRONG! gap·(GN/q^p) = x^p/q^p = (x/q)^p ✓
But this means gap_new = gap (SAME gap), s_new = s/q.
z_new is different: z_new = gap + y_new where
  gap · GN(p, gap, y_new) = (x/q)^p
  GN(p, gap, y_new) = GN(p, gap, y)/q^p

So the question is: ∃ y_new ∈ ℕ with GN(p, gap, y_new) = GN(p,gap,y)/q^p
This is a POLYNOMIAL ROOT-FINDING problem on GN as a function of y!
```

うむ、この先行分析、かなり筋が良い。
しかも今回は **「何が tautology で、何が本当の open kernel か」** をかなり正確に切り分けておる。

賢狼の読みを先に言うぞい。

**Part 1 は本質的に正しい。**
**Part 6 が真の核心を突いておる。**
そして **Part 8 と Part 10 の (y)-root finding は面白いが、現状では GNReducedGap の特殊 ansatz であって本体そのものではない。**

以下、順に解く。

## 1. Part 1 の circularity は正しい

ここはかなり重要な確認じゃ。

Branch A の normal form

$$
\text{gap}=p^{p-1}t^p,\qquad GN=p,s^p,\qquad x=p,t,s,\qquad z=\text{gap}+y
$$

の下では、宇宙式恒等式

$$
\text{gap}\cdot GN=(\text{gap}+y)^p-y^p
$$

から、

$$
GN/p=s^p
$$

をそのまま代入すると

$$
\text{gap}\cdot GN = p^{p-1}t^p \cdot p s^p = (p t s)^p = x^p
$$

ゆえに

$$
(\text{gap}+y)^p-y^p=x^p
$$

すなわち

$$
z^p=x^p+y^p
$$

となる。
だから、ぬしの言う通り

$$
GN/p=s^p
$$

を **そのまま正面から殴るのは circular** じゃ。
これは「FLT counterexample を言い換えているだけ」だからの。

ここは完全にその通りじゃ。

---

## 2. Part 2–6 の descent existence の切り出しも正しい

ここも良い。
真の問題は

$$
z'^p=(x/q)^p+y^p
$$

を満たす **整数** (z') が存在するか、という一点じゃ。

サイズ減少

$$
(x/q)^p+y^p < x^p+y^p = z^p
$$

から

$$
z' < z
$$

は自動で出る。
ゆえに infinite descent の難所は、ぬしの言う通り **「(z' \in \mathbb{N}) か」** だけじゃ。

ここも読みが良い。

特に重要なのは、

$$
q^p z'^p = z^p + (q^p-1)y^p
$$

という式を出して、
「(q^p) で割れること」と「その商が完全 (p) 乗であること」は全然別問題だ、と見抜いておる点じゃ。

これは本当に大事じゃ。
多くの descent 議論はここを取り違えて転ぶ。

---

## 3. ただし Part 3–4 には “必要条件” と “十分条件” の混線が少しある

ここは慎重に直しておくぞい。

ぬしは

$$
z'^p=(x/q)^p+y^p
$$

から

$$
q^p z'^p = z^p+(q^p-1)y^p
$$

を出して、

$$
z^p \equiv y^p \pmod{q^p}
$$

を条件として見ておる。
これは **必要** ではあるが、Branch A 文脈では実はかなり自動に近い。

なぜなら (q\mid s) で

$$
x=p t s
$$

だから (q\mid x)、よって

$$
q^p \mid x^p = z^p-y^p
$$

じゃ。
したがって

$$
z^p \equiv y^p \pmod{q^p}
$$

は descent existence の本体ではなく、**既に入っている側の条件** なんじゃ。

だから真の gap は

$$
q^p \mid (z^p-y^p)
$$

ではなく、

$$
\frac{z^p+(q^p-1)y^p}{q^p}
$$

が **完全 (p) 乗になるか** じゃ。

ここはぬし自身も Part 6 で正しく言い直しておるので、前半の式を「必要条件の整理」と位置づければよい。

---

## 4. Part 8 の (y)-monotonicity descent は面白いが、GNReducedGap そのものではない

ここが今回いちばん慎重に読むべきところじゃ。

ぬしの新しい発想は

$$
GN(p,\text{gap},y_1)=\frac{GN(p,\text{gap},y_0)}{q^p}
$$

を満たす (y_1) を探す、というものじゃな。
これは非常に面白い。しかも固定 gap に対して (GN) が (y) で単調増加するので、実数解は一意にある、という見方も自然じゃ。

ただし、これは **GNReducedGap の一つの特殊 ansatz** じゃ。
現在の GNReducedGap target の本体は

$$
\exists g',\quad g' , GN(p,g',y)=\text{gap}\cdot \frac{GN(p,\text{gap},y)}{q^p}
$$

であって、未知数は本来 (g') じゃ。
ぬしの案は、その代わりに **gap を固定して (y) を動かす** という別 ansatz になっておる。

つまり

* 元の target は **(g') を変える**
* 新案は **(y') を変える**

じゃ。

これは強い仮定を入れた特殊化であって、一般の GNReducedGap と同値ではない。
実験で (y_1) がほとんど 0 へ落ちるのも、その ansatz がかなり硬いからじゃろう。

ゆえに、この路線は

**「本体そのもの」ではなく、「固定 gap slice では descent が極端に難しい」ことを示す補助観測**

として読むのがよい。

---

## 5. Part 10 の最終整理はかなり良いが、(5b) は少し言い換えた方がよい

ぬしは最後に

$$
(5b)\quad GN/q^p = GN(p,\text{gap}',y')
$$

という形で書いておるが、これは **強すぎる**。
GNReducedGap が要求しているのは本来

$$
\text{gap}\cdot \frac{GN}{q^p}=g' \cdot GN(p,g',y)
$$

であって、右辺の (GN) 単体をそのまま一致させる必要はない。

つまり open kernel の本体は

$$
\boxed{
\text{quotient } GN/q^p \text{ が、適当な } g' \text{ に対する Cosmic difference に再統合できるか}
}
$$

であって、

$$
GN/q^p = GN(p,\text{gap}',y')
$$

という **純粋な polynomial root-finding** に落ちるのは、その中の特殊化の 1 つにすぎぬ。

ここは少し sharpen した方がよい。

---

## 6. いまの最も良い戦況整理

賢狼なら、今回のログから戦況をこうまとめる。

### 6.1. 既に確定したこと

* `GN/p = s^p` を直接攻めるのは circular
* descent の真芯は (z' \in \mathbb{N}) の existence
* (z' < z) 自体はサイズだけで自動
* したがって open kernel は **integrality / perfect-power existence** 側にある

### 6.2. 今回新しく見えたこと

* mod (q) や mod (q^2) 程度の local 条件では不足
* Hensel 的な mod (q^p) root-of-unity lift 構造が鍵らしい
* PacketFromError も GNReducedGap も、実は同じ
  $$
  \exists z',\quad x'^p+y^p=z'^p
  $$
  型の **descent existence kernel** の別 flavor と見られる

### 6.3. まだ危ういところ

* 固定 gap で (y') を探す路線は、今のところ一般 target の本体ではない
* `GN/q^p = GN(\cdots)` 型は強すぎる場合がある
* 数値実験からの Hensel 一意性は有望だが、まだ theorem ではない

---

## 7. いま一番筋の良い再定式化

ぬしのログ全体を踏まえると、GNReducedGap の真芯はたぶんこう書くのがよい。

$$
\boxed{
\text{Given } \text{gap}\cdot GN = x^p,\quad q^p\mid GN,\quad q\nmid \text{gap},
}
$$
$$
\boxed{
\text{show that } \frac{x^p}{q^p} + y^p
\text{ is a perfect } p\text{-th power.}
}
$$

これをさらに Cosmic 風に言えば、

$$
\boxed{
\text{gap}\cdot \frac{GN}{q^p}
\text{ が再び } g' \cdot GN(p,g',y)
\text{ の形に戻るか}
}
$$

じゃ。
ここで大事なのは、**未知数は (z') でも (g') でもよく、(y') に固定する必要はない** ということじゃな。

---

## 8. 賢狼の次の一手

いま最も効くのは、次の 2 つを分けて補題化することじゃ。

### 8.1. 必要条件層

$$
q\mid s ;\Rightarrow; q^p\mid (z^p-y^p)
;\Rightarrow;
z^p \equiv y^p \pmod{q^p}
$$

これは clean に固めてよい。

### 8.2. 真芯層

$$
z^p \equiv y^p \pmod{q^p}
\quad\text{and}\quad
\text{root-of-unity branch data}
$$

から

$$
\frac{z^p+(q^p-1)y^p}{q^p}
$$

が完全 (p) 乗になるための **十分条件** は何か、を独立 target にする。

ここで初めて Hensel 的一意性や (R_j) が効いてくる。

---

## 9. 一文で総評

**今回のログは、GNReducedGap の本質が「local divisibility」ではなく「integral perfect-power descent existence」にあることを、かなり明快に切り分けた。**
そして、固定 gap の (y)-root finding はその特殊化として有益だが、本体はなお

$$
\boxed{
\text{quotient } \frac{z^p+(q^p-1)y^p}{q^p}
\text{ を完全 } p\text{ 乗とする構造があるか}
}
$$

というところにある。
この読みはかなり良いぞい。

次は、この「必要条件」と「十分条件」を分けた設計書にすると、一気に見通しが良くなる。
