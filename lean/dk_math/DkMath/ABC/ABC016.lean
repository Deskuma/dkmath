/-
Copyright (c) 2025 D. and Wise Wolf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ABC015

#print "file: DkMath.ABC.ABC016"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※細分化前にエラー／警告を出さない補題・定理ファイル。
  ABC.lean で定義されるべき定理のうち、ABC.lean 内で定義されていた定理をここに移動している。
-/

namespace ABC

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

/-- Auxiliary lemma: For non-negative exponent γ, rad(a)^γ ≥ 1. -/
lemma rad_pow_ge_one {a : ℕ} {γ : ℝ} (hγ : 0 ≤ γ) :
    1 ≤ (rad a : ℝ) ^ γ := by
  have hrad_ge_one : 1 ≤ (rad a : ℝ) := one_le_rad_real a
  by_cases h : γ = 0
  · simp [h]
  · have hγ_pos : 0 < γ := lt_of_le_of_ne hγ (Ne.symm h)
    calc (1 : ℝ)
        = 1 ^ γ := by rw [Real.one_rpow]
      _ ≤ (rad a : ℝ) ^ γ := by
        apply Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hrad_ge_one hγ

/-- Bridge-local helper: Square-free tail quotient.
    For use in `htail` construction with EQUALITY (not inequality).
    This is distinct from the π-factor `piSqRad` used in the π-bound.

    Definition: sqTail(c) := c / rad(c)
    Property: c = sqTail(c) * rad(c) (exact equality)

    Note: This is NOT the same as piSqRad(c) = ∏ p^{v_p(c) mod 2}.
    We use this separate notion to avoid the false inequality
    "c ≤ piSqRad(c) * rad(c)" which fails for highly powerful numbers.
-/
def sqTail (c : ℕ) : ℕ := c / (rad c)


/-- Equality-based decomposition: c = sqTail(c) * rad(c).
    This is the CORRECT form for tail bounds in the bridge.
    No inequality ambiguity, works for all c ≥ 1. -/
lemma nat_eq_sqTail_mul_rad (c : ℕ) (hc : c ≠ 0) :
    c = sqTail c * rad c := by
  unfold sqTail
  -- Need: c = (c / rad c) * rad c
  -- This follows from division property when rad c divides c
  have hdiv : rad c ∣ c := rad_dvd_nonzero c hc
  rw [Nat.div_mul_cancel hdiv]


/-- Real-valued version for use in calc chains. -/
lemma nat_eq_sqTail_mul_rad_real (c : ℕ) (hc : c ≠ 0) :
    (c : ℝ) = (sqTail c : ℝ) * (rad c : ℝ) := by
  have := nat_eq_sqTail_mul_rad c hc
  exact_mod_cast this

-- ========================================================================
-- Odd/Even exponent decomposition (the correct approach)
-- ========================================================================

/-- The "odd part" of a natural number: ∏_{p|c} p^{v_p(c) mod 2}.
    This extracts only the odd exponent components from the factorization.

    Example: c = 2³ * 3² * 5⁴
    - v_2 mod 2 = 1, v_3 mod 2 = 0, v_5 mod 2 = 0
    - oddPart(c) = 2¹ * 3⁰ * 5⁰ = 2

    Key property: oddPart(c) is always squarefree (all exponents are 0 or 1).
-/
def oddPart (c : ℕ) : ℕ :=
  c.factorization.support.prod (fun p => p ^ (c.factorization p % 2))


/-- The "even part root" of a natural number: ∏_{p|c} p^{⌊v_p(c)/2⌋}.
    This is the square root of the "even exponent part" in the factorization.

    Example: c = 2³ * 3² * 5⁴
    - ⌊v_2/2⌋ = 1, ⌊v_3/2⌋ = 1, ⌊v_5/2⌋ = 2
    - evenPart(c) = 2¹ * 3¹ * 5² = 150

    This is DIFFERENT from sqTail = c/rad(c):
    - evenPart extracts ⌊v_p/2⌋ for each prime
    - sqTail = c/rad(c) can be much larger

    Example: c = p⁴
    - evenPart(p⁴) = p^{⌊4/2⌋} = p²
    - sqTail(p⁴) = p⁴/p = p³
-/
def evenPart (c : ℕ) : ℕ :=
  c.factorization.support.prod (fun p => p ^ (c.factorization p / 2))


@[simp] lemma oddPart_zero : oddPart 0 = 1 := by
  classical
  simp [oddPart]


@[simp] lemma evenPart_zero : evenPart 0 = 1 := by
  classical
  simp [evenPart]


/-- Main decomposition identity: c = oddPart(c) * evenPart(c)².
    This follows from the exponent identity v = (v mod 2) + 2⌊v/2⌋.

    Requires c ≠ 0 because oddPart 0 = evenPart 0 = 1, so RHS = 1 ≠ 0.
    For c = 0, use zero-aware versions if needed (like rad₀).

    Proof strategy:
    - For each prime p|c: v_p(c) = v_p(c) mod 2 + 2⌊v_p(c)/2⌋ (by Nat.mod_add_div)
    - LHS: v_p(c) = v_p(c)
    - RHS: v_p(oddPart(c) * evenPart(c)²) = (v_p mod 2) + 2⌊v_p/2⌋ = v_p(c) ✓
-/
lemma decomp_oddPart_evenPart (c : ℕ) (hc : c ≠ 0) :
    c = oddPart c * (evenPart c) ^ 2 := by
  classical
  -- Basic expansion: product over factorization support equals c
  -- `∏ p∈S, p^{v_p(c)} = c`
  set S := c.factorization.support with hS
  have hbase : ∏ p ∈ S, p ^ c.factorization p = c := by
    -- mathlib standard: product of prime powers over support reconstructs the number
    simpa [hS] using Nat.factorization_prod_pow_eq_self hc

  -- Rewrite exponents using v = (v%2) + 2*(v/2)
  have hrewrite :
      ∏ p ∈ S, p ^ c.factorization p
        = ∏ p ∈ S, p ^ ((c.factorization p % 2) + 2 * (c.factorization p / 2)) := by
    refine Finset.prod_congr rfl ?_
    intro p hp
    -- `Nat.mod_add_div` : `v % 2 + 2 * (v/2) = v`
    have : c.factorization p % 2 + 2 * (c.factorization p / 2) = c.factorization p := by
      simpa [two_mul] using Nat.mod_add_div (c.factorization p) 2
    simp only [this]

  -- Split ∏ using `pow_add` to separate into product form
  have hsplit :
      ∏ p ∈ S, p ^ ((c.factorization p % 2) + 2 * (c.factorization p / 2))
        = (∏ p ∈ S, p ^ (c.factorization p % 2))
          * (∏ p ∈ S, p ^ (2 * (c.factorization p / 2))) := by
    -- `∏ (x) (A x * B x) = (∏ A x) * (∏ B x)`
    -- Here A x = p^(v%2), B x = p^(2*(v/2))
    simpa [pow_add] using
      (Finset.prod_mul_distrib :
        ∏ p ∈ S, (p ^ (c.factorization p % 2)) * (p ^ (2 * (c.factorization p / 2)))
          = _)

  -- Apply `p^(2*k) = (p^k)^2` to each term, then pull constant exponent 2 out
  have hpow2 :
      ∏ p ∈ S, p ^ (2 * (c.factorization p / 2))
        = (∏ p ∈ S, p ^ (c.factorization p / 2)) ^ 2 := by
    -- First, rewrite `2*k` as `k+k`
    conv_lhs => arg 2; ext p; rw [two_mul]
    -- Now each term is `p^(k+k) = p^k * p^k = (p^k)^2`
    simp only [pow_add]
    -- Apply product distributivity
    rw [Finset.prod_mul_distrib]
    -- Now `(∏ p^k) * (∏ p^k) = (∏ p^k)^2`
    ring

  -- Chain all equalities
  calc
    c = ∏ p ∈ S, p ^ c.factorization p := hbase.symm
    _ = ∏ p ∈ S, p ^ ((c.factorization p % 2) + 2 * (c.factorization p / 2)) := hrewrite
    _ = (∏ p ∈ S, p ^ (c.factorization p % 2)) * (∏ p ∈ S, p ^ (2 * (c.factorization p / 2))) := hsplit
    _ = (∏ p ∈ S, p ^ (c.factorization p % 2)) * (∏ p ∈ S, p ^ (c.factorization p / 2)) ^ 2 := by
          simp only [hpow2]
    _ = oddPart c * (evenPart c) ^ 2 := by
          simp [oddPart, evenPart, hS]


/-- Real-valued version of the decomposition (requires c ≠ 0). -/
lemma decomp_oddPart_evenPart_real (c : ℕ) (hc : c ≠ 0) :
    (c : ℝ) = (oddPart c : ℝ) * (evenPart c : ℝ) ^ 2 := by
  exact_mod_cast decomp_oddPart_evenPart c hc


-- ========================================================================
-- twoTail decomposition: The TRUE tail for ABC quality bounds
-- ========================================================================


/-- The "two-tail" of a natural number: ∏_{p|c} p^{max(v_p(c)-2, 0)}.
    This extracts only the "excess beyond square" part from the factorization.

    Key insight: Each prime's exponent can be split as:
      v_p(c) = 1_{v_p≥2} (piSqRad part) + 1_{v_p≥1} (rad part) + (v_p - 2) (twoTail part)

    This gives the identity: c = piSqRad(c) * rad(c) * twoTail(c)

    Example: c = 2³ * 3⁵ * 5²
    - v_2 - 2 = 1, v_3 - 2 = 3, v_5 - 2 = 0
    - twoTail(c) = 2¹ * 3³ * 5⁰ = 2 * 27 = 54
    - piSqRad(c) = 2 * 3 * 5 = 30 (all primes with v_p ≥ 2)
    - rad(c) = 2 * 3 * 5 = 30 (all primes with v_p ≥ 1)
    - Check: 2³*3⁵*5² = 8*243*25 = 48600 = 30*30*54 ✓

    This is DIFFERENT from both oddPart/evenPart:
    - oddPart extracts v_p mod 2 (odd exponents)
    - evenPart extracts ⌊v_p/2⌋ (square root of even part)
    - twoTail extracts v_p - 2 (excess beyond square)

    The advantage: c = piSqRad * rad * twoTail gives htail WITHOUT needing
    oddPart ≤ piSqRad (which is FALSE in general).
-/
def twoTail (c : ℕ) : ℕ :=
  c.factorization.support.prod (fun p => p ^ (c.factorization p - 2))

@[simp] lemma twoTail_zero : twoTail 0 = 1 := by
  classical
  simp [twoTail]


/-- Three-way decomposition identity: c = piSqRad(c) * rad(c) * twoTail(c).

    This follows from the exponent identity for each prime p|c:
      v_p(c) = 1_{v_p≥2} + 1_{v_p≥1} + (v_p - 2)

    Proof strategy:
    1. Start from ∏ p^{v_p(c)} = c
    2. Split each exponent: v_p = (indicator v_p≥2) + (indicator v_p≥1) + (v_p - 2)
    3. Separate into three products using pow_add
    4. Identify each product with piSqRad, rad, and twoTail by definition
-/
lemma decomp_piRad_twoTail (c : ℕ) (hc : c ≠ 0) :
    c = piSqRad c * rad c * twoTail c := by
  classical
  -- S := support of factorization
  set S := c.factorization.support with hS

  -- Base: ∏ p∈S, p^{v_p(c)} = c
  have hbase : ∏ p ∈ S, p ^ c.factorization p = c := by
    simpa [hS] using Nat.factorization_prod_pow_eq_self hc

  -- Exponent identity: v = 1_{v≥2} + 1_{v≥1} + (v-2)
  -- For each prime in support, v_p(c) > 0, so we can decompose
  have hIdx : ∀ p ∈ S, c.factorization p
      = (if 2 ≤ c.factorization p then 1 else 0)
      + (if 0 < c.factorization p then 1 else 0)
      + (c.factorization p - 2) := by
    intro p hp
    -- p is in support, so v_p(c) > 0
    have hpos : 0 < c.factorization p := by
      have : c.factorization p ≠ 0 := by
        simp only [hS, Finsupp.mem_support_iff] at hp
        exact hp
      omega
    cases hv : c.factorization p with
    | zero => omega  -- contradiction with hpos
    | succ v =>
      cases v with
      | zero =>  -- v = 1: then 2 ≤ 1 is false, 0 < 1 is true
        simp only [zero_add, Nat.not_ofNat_le_one, ↓reduceIte, zero_lt_one, Nat.one_le_ofNat,
          Nat.sub_eq_zero_of_le, add_zero]
      | succ v' =>  -- v = v'+2 ≥ 2: both 2 ≤ v'+2 and 0 < v'+2 are true
        simp only [le_add_iff_nonneg_left, zero_le, ↓reduceIte, lt_add_iff_pos_left, add_pos_iff,
          Nat.ofNat_pos, or_true, Nat.reduceAdd, Nat.reduceSubDiff]
        omega

  -- Rewrite exponents using the identity
  have hrewrite :
      ∏ p ∈ S, p ^ c.factorization p
        = ∏ p ∈ S, p ^ ((if 2 ≤ c.factorization p then 1 else 0)
                        + (if 0 < c.factorization p then 1 else 0)
                        + (c.factorization p - 2)) := by
    apply Finset.prod_congr rfl
    intro p hp
    congr 1
    exact hIdx p hp

  -- Split ∏ using pow_add (twice) to separate into three products
  have hsplit :
      ∏ p ∈ S, p ^ ((if 2 ≤ c.factorization p then 1 else 0)
                    + (if 0 < c.factorization p then 1 else 0)
                    + (c.factorization p - 2))
        = (∏ p ∈ S, p ^ (if 2 ≤ c.factorization p then 1 else 0))
          * (∏ p ∈ S, p ^ (if 0 < c.factorization p then 1 else 0))
          * (∏ p ∈ S, p ^ (c.factorization p - 2)) := by
    -- Apply pow_add: p^(a+b+c) = p^a * p^(b+c)
    conv_lhs =>
      arg 2; ext p
      rw [pow_add]
    -- Now: ∏ (p^a * p^(b+c)) = ∏ p^a * ∏ p^(b+c)
    rw [Finset.prod_mul_distrib]
    congr 1
    -- Apply pow_add again: p^(b+c) = p^b * p^c
    conv_lhs =>
      arg 2; ext p
      rw [pow_add]
    rw [Finset.prod_mul_distrib]

  -- Identify first product as piSqRad
  have hPi : ∏ p ∈ S, p ^ (if 2 ≤ c.factorization p then 1 else 0) = piSqRad c := by
    simp only [piSqRad, hS]
    -- Key insight: p^0 = 1 when ¬(2≤v_p), so those terms don't contribute
    -- Therefore this product equals ∏_{p with 2≤v_p} p
    -- Strategy: Split S into filter and complement, show complement contributes 1
    classical
    rw [← Finset.prod_filter_mul_prod_filter_not S (fun p => 2 ≤ c.factorization p)]
    -- Step 1: On the filtered set, p^{1_{2≤v_p}} = p^1 = p
    have h_filter : ∏ p ∈ S.filter (fun p => 2 ≤ c.factorization p),
                     p ^ (if 2 ≤ c.factorization p then 1 else 0) =
                     ∏ p ∈ S.filter (fun p => 2 ≤ c.factorization p), p := by
      apply Finset.prod_congr rfl
      intro p hp
      simp only [Finset.mem_filter] at hp
      simp [hp.2, pow_one]
    -- Step 2: On the complement, p^{1_{2≤v_p}} = p^0 = 1
    have h_compl : ∏ p ∈ S.filter (fun p => ¬2 ≤ c.factorization p),
                    p ^ (if 2 ≤ c.factorization p then 1 else 0) = 1 := by
      apply Finset.prod_eq_one
      intro p hp
      simp only [Finset.mem_filter] at hp
      simp [hp.2, pow_zero]
    rw [h_filter, h_compl, mul_one]

  -- Identify second product as rad
  have hRad : ∏ p ∈ S, p ^ (if 0 < c.factorization p then 1 else 0) = rad c := by
    simp only [rad, hS]
    -- All p ∈ S have v_p > 0 by definition of support
    -- So the if-expression is always 1
    have : ∀ p ∈ S, 0 < c.factorization p := by
      intro p hp
      simp only [hS, Finsupp.mem_support_iff] at hp
      omega
    -- Rewrite each term using this fact
    trans (∏ p ∈ S, p ^ 1)
    · apply Finset.prod_congr rfl
      intro p hp
      rw [if_pos (this p hp)]
    -- Now just need: ∏ p∈S, p^1 = ∏ p∈S, p
    simp only [pow_one]
    -- And rad is defined as exactly this product
    rfl

  -- Identify third product as twoTail
  have hTail : ∏ p ∈ S, p ^ (c.factorization p - 2) = twoTail c := by
    simp [twoTail, hS]

  -- Chain all equalities
  calc
    c = ∏ p ∈ S, p ^ c.factorization p := hbase.symm
    _ = (∏ p ∈ S, p ^ (if 2 ≤ c.factorization p then 1 else 0))
        * (∏ p ∈ S, p ^ (if 0 < c.factorization p then 1 else 0))
        * (∏ p ∈ S, p ^ (c.factorization p - 2)) := by
          rw [hrewrite, hsplit]
    _ = piSqRad c * rad c * twoTail c := by
          rw [hPi, hRad, hTail]


/-- Real-valued version of three-way decomposition (requires c ≠ 0). -/
lemma decomp_piRad_twoTail_real (c : ℕ) (hc : c ≠ 0) :
    (c : ℝ) = (piSqRad c : ℝ) * (rad c : ℝ) * (twoTail c : ℝ) := by
  exact_mod_cast decomp_piRad_twoTail c hc


/-- `piSqRad` は常に 1 以上（自然数として） -/
lemma piSqRad_ge_one (n : ℕ) : 1 ≤ piSqRad n := by
  classical
  -- piSqRad is the product over primes p with v_p ≥ 2
  -- Product over Finset is always ≥ 1 (empty gives 1, non-empty gives product of primes ≥ 2)
  dsimp [piSqRad]
  apply Finset.one_le_prod'
  intro p hp
  -- p is prime with v_p ≥ 2, so p ≥ 2 ≥ 1
  have : p ∈ n.factorization.support := Finset.mem_filter.mp hp |>.1
  have hprime : p.Prime := (mem_support_factorization_iff.mp this).2.1
  exact Nat.one_le_of_lt (Nat.Prime.one_lt hprime)


/-- `sqTail` と `twoTail` の関係：`sqTail c = piSqRad c * twoTail c`（`c≠0`） -/
lemma sqTail_eq_piSqRad_mul_twoTail (c : ℕ) (hc : c ≠ 0) :
    sqTail c = piSqRad c * twoTail c := by
  classical
  -- Strategy: Use the three-way decomposition c = piSqRad * rad * twoTail
  -- and the two-way decomposition c = sqTail * rad
  -- Dividing: sqTail = c / rad = (piSqRad * rad * twoTail) / rad = piSqRad * twoTail
  have hdec3 := decomp_piRad_twoTail c hc
  have hdec2 := nat_eq_sqTail_mul_rad c hc
  -- From hdec2: c = sqTail * rad, so sqTail * rad = piSqRad * rad * twoTail
  -- Since rad ≠ 0, we can cancel: sqTail = piSqRad * twoTail
  have hrad_pos : 0 < rad c := rad_pos (Nat.pos_of_ne_zero hc)
  -- Use division cancellation
  have : sqTail c * rad c = piSqRad c * twoTail c * rad c := by
    calc sqTail c * rad c
        = c := hdec2.symm
      _ = piSqRad c * rad c * twoTail c := hdec3
      _ = piSqRad c * twoTail c * rad c := by ring
  exact Nat.eq_of_mul_eq_mul_right hrad_pos this


lemma sqTail_eq_piSqRad_mul_twoTail_real (c : ℕ) (hc : c ≠ 0) :
    (sqTail c : ℝ) = (piSqRad c : ℝ) * (twoTail c : ℝ) := by
  exact_mod_cast sqTail_eq_piSqRad_mul_twoTail c hc


/-- `twoTail ≤ sqTail`（`c≠0`）。実数版の不等式で使う。 -/
lemma twoTail_le_sqTail_real (c : ℕ) (hc : c ≠ 0) :
    (twoTail c : ℝ) ≤ (sqTail c : ℝ) := by
  -- Use sqTail = piSqRad * twoTail and piSqRad ≥ 1
  have h := sqTail_eq_piSqRad_mul_twoTail_real c hc
  have hπge : (1 : ℝ) ≤ (piSqRad c : ℝ) := by
    -- piSqRad c ≥ 1 for any c
    have : 1 ≤ piSqRad c := piSqRad_ge_one c
    exact_mod_cast this
  -- twoTail ≤ piSqRad * twoTail = sqTail
  calc (twoTail c : ℝ)
      = 1 * (twoTail c : ℝ) := by ring
    _ ≤ (piSqRad c : ℝ) * (twoTail c : ℝ) := by
        apply mul_le_mul_of_nonneg_right hπge
        exact Nat.cast_nonneg _
    _ = (sqTail c : ℝ) := h.symm


/-- Squarefree なら sqTail = 1 -/
lemma sqTail_eq_one_of_squarefree {n : ℕ} (hn0 : n ≠ 0) (hsf : Squarefree n) :
    sqTail n = 1 := by
  unfold sqTail
  have hrad := rad_eq_self_of_squarefree hn0 hsf
  rw [hrad]
  exact Nat.div_self (Nat.pos_of_ne_zero hn0)


/-- sqTail ≤ n （自明な上界） -/
lemma sqTail_le_self (n : ℕ) : sqTail n ≤ n := by
  unfold sqTail
  exact Nat.div_le_self n (rad n)


/-- sqTail の実数版上界 -/
lemma sqTail_le_self_real (n : ℕ) : (sqTail n : ℝ) ≤ (n : ℝ) := by
  exact_mod_cast sqTail_le_self n


/-- Adjacent triple の基本不等式: 2X+1 ≤ X*(X+1) for X ≥ 2 -/
lemma two_mul_add_one_le_mul_succ (X : ℕ) (hX : 2 ≤ X) :
    2*X + 1 ≤ X * (X+1) := by
  -- Prove via real number calculation with nlinarith
  suffices h : (2*X + 1 : ℝ) ≤ (X * (X+1) : ℝ) by exact_mod_cast h
  have hX_pos : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  have hX_ge_2 : (2 : ℝ) ≤ X := by exact_mod_cast hX
  -- Expand: X(X+1) = X² + X, need 2X + 1 ≤ X² + X, i.e., X + 1 ≤ X²
  -- For X ≥ 2: X² ≥ 2X (since X ≥ 2), and 2X ≥ X+1 (since X ≥ 1)
  nlinarith [sq_nonneg X, mul_nonneg hX_pos hX_pos]


/-- Adjacent triple の実数版不等式 -/
lemma two_mul_add_one_le_mul_succ_real (X : ℕ) (hX : 2 ≤ X) :
    (2*X + 1 : ℝ) ≤ (X * (X+1) : ℝ) := by
  exact_mod_cast two_mul_add_one_le_mul_succ X hX


/-- Squarefree case: sqTail = 1, so bound trivially holds -/
lemma sqTail_adjacent_le_rad_pow_of_squarefree (X : ℕ) (γ : ℝ)
    (hc_ne : 2 * X + 1 ≠ 0) (hab_ne : X * (X + 1) ≠ 0)
    (hsf : Squarefree (2 * X + 1)) (hγ_pos : 0 < γ) :
    (sqTail (2*X+1) : ℝ) ≤ (rad (X*(X+1)) : ℝ) ^ γ := by
  -- sqTail = 1 for squarefree, and rad(ab)^γ ≥ 1 for γ > 0
  have h_sqtail_one := sqTail_eq_one_of_squarefree hc_ne hsf
  have h_rad_pos : 0 < rad (X*(X+1)) := rad_pos (Nat.pos_of_ne_zero hab_ne)
  have h_rad_ge_one : 1 ≤ (rad (X*(X+1)) : ℝ) := by
    have : 1 ≤ rad (X*(X+1)) := by
      apply Nat.one_le_iff_ne_zero.mpr
      exact Nat.pos_iff_ne_zero.mp h_rad_pos
    exact_mod_cast this
  have h_rpow_ge_one : 1 ≤ (rad (X*(X+1)) : ℝ) ^ γ := by
    -- For rad ≥ 1 and γ > 0: rad^γ ≥ 1 by Real.one_le_rpow
    exact Real.one_le_rpow h_rad_ge_one (le_of_lt hγ_pos)
  calc (sqTail (2*X+1) : ℝ)
      = 1 := by simp [h_sqtail_one]
    _ ≤ (rad (X*(X+1)) : ℝ) ^ γ := h_rpow_ge_one

-- ========================================================================
-- Phase 3: twoTail direct control (non-squarefree strategy)
-- ========================================================================

-- Square-excess (twoTail) control via logarithmic budget.
-- Core strategy for non-squarefree case: Instead of using quality bound,
-- we directly bound twoTail by controlling p-adic excess ∑(v_p - 2)₊ log p.
--
-- Mathematical intuition:
-- - For small primes: Chernoff bounds keep v_p(c) = O(1) w.h.p.
-- - For large primes: p² | c is rare (requires p ≤ √c)
-- - Total excess ∑(v_p - 2)₊ log p ≤ γ log rad(ab) with density 1
--
-- This avoids the "exponent mismatch" problem in quality-based approach.


/-- Logarithmic representation: log twoTail = ∑(v_p - 2)₊ log p -/
lemma log_twoTail_eq_sum_vplus (c : ℕ) (_hc : c ≠ 0) :
    Real.log (twoTail c : ℝ)
      = ∑ p ∈ c.primeFactors,
          ((c.factorization p - 2 : ℕ) : ℝ) * Real.log (p : ℝ) := by
  -- Expand twoTail definition via prime factorization
  -- twoTail c = ∏ p^(v_p - 2) where v_p = factorization c p
  classical
  unfold twoTail
  -- Key: factorization.support = primeFactors
  have h_support : c.factorization.support = c.primeFactors := by
    ext p
    simp only [Nat.support_factorization, Nat.mem_primeFactors, ne_eq]
  rw [h_support]
  -- Apply log to the product (cast to ℝ first)
  conv_lhs => arg 1; rw [Nat.cast_prod]
  -- Now use Real.log_prod
  rw [Real.log_prod]
  · -- Goal: ∑ p ∈ primeFactors, log((p : ℝ)^(v_p - 2)) = ∑ p ∈ primeFactors, (v_p - 2) * log p
    congr 1
    ext p
    by_cases hp : p ∈ c.primeFactors <;> simp only [Nat.cast_pow, Real.log_pow] at *
  · -- Show ∀ p ∈ primeFactors, (p : ℝ)^(v_p - 2) ≠ 0
    intro p hp
    -- p は素数なので 0 でない
    have h_p_ne_zero : p ≠ 0 := Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors hp)
    -- 指数部は自然数なので pow_ne_zero が使える
    have h_pow_ne_zero : p ^ (c.factorization p - 2) ≠ 0 := pow_ne_zero _ h_p_ne_zero
    -- ℝ へのキャスト後も 0 でない
    exact Nat.cast_ne_zero.mpr h_pow_ne_zero


-- Budget inequality ⇒ power bound for twoTail
lemma twoTail_le_rad_pow_of_log_bound
    {a b c : ℕ} {γ : ℝ} (hc0 : c ≠ 0) (_hab0 : a * b ≠ 0)
    (H : Real.log (twoTail c : ℝ) ≤ γ * Real.log (rad (a * b) : ℝ)) :
    (twoTail c : ℝ) ≤ (rad (a*b) : ℝ) ^ γ := by
  -- Convert logarithmic bound to exponential bound
  have hpos_ab : 0 < (rad (a*b) : ℝ) := by
    apply rad_pos_real
  have hpos_tt : 0 < (twoTail c : ℝ) := by
    simp only [Nat.cast_pos]
    -- twoTail c > 0 since c ≠ 0 and twoTail divides c
    have : twoTail c ≠ 0 := by
      intro h_eq
      have : c = piSqRad c * rad c * twoTail c := decomp_piRad_twoTail c hc0
      rw [h_eq, mul_zero] at this
      exact hc0 this
    omega
  -- Use monotonicity of log and exp: log x ≤ log y ⟹ x ≤ y (for x, y > 0)
  -- Here: log twoTail ≤ γ log rad ⟹ twoTail ≤ rad^γ
  have h_log_rpow : γ * Real.log (rad (a*b) : ℝ) = Real.log ((rad (a*b) : ℝ) ^ γ) := by
    exact (Real.log_rpow hpos_ab γ).symm
  rw [h_log_rpow] at H
  have hpos_rpow : 0 < (rad (a*b) : ℝ) ^ γ := Real.rpow_pos_of_pos hpos_ab γ
  exact (Real.log_le_log_iff hpos_tt hpos_rpow).mp H


-- ========================================================================
-- Phase 3: Adjacent triple π-bound extraction (index-aligned version)
-- ========================================================================


/-- Small lemma: `n ≤ 2n+1`. Simple Nat arithmetic. -/
lemma le_two_mul_add_one_left (n : ℕ) : n ≤ 2*n + 1 := by
  have h : n ≤ n + n := Nat.le_add_left _ _
  have h' : n ≤ 2*n := by simp [two_mul, h]
  exact h'.trans (Nat.le_succ _)


/-- Small lemma: `n+1 ≤ 2n+1`. -/
lemma succ_le_two_mul_add_one (n : ℕ) : n + 1 ≤ 2*n + 1 :=
  Nat.succ_le_succ <| by
    have h : n ≤ n + n := Nat.le_add_left _ _
    simp [two_mul, h]


/-- Adjacent triple version: From `¬ is_bad_a δ (2n+1) (n+1) n`,
    directly derive `piSqRad (2n+1) ≤ (rad n * rad (n+1))^δ`.
    This is the "middle link of the π-chain" (index-aligned, no admit). -/
lemma piSqRad_adjacent_le_of_not_is_bad_a'
  {δ : ℝ} {n : ℕ}
  (h : ¬ is_bad_a δ (2*n+1) (n+1) n) :
  (piSqRad (2*n+1) : ℝ) ≤ (rad n * rad (n+1) : ℝ) ^ δ := by
  have ha  : n ≤ 2*n+1   := le_two_mul_add_one_left n
  have hb  : n+1 ≤ 2*n+1 := succ_le_two_mul_add_one n
  have hab : n + (n+1) ≤ 2*n + 1 := by
    have : n + (n+1) = 2*n + 1 := by ring
    exact this.le
  -- ¬is_bad_a → ¬Bad (adjacent triple (n, n+1, n+(n+1)))
  have h_not_bad :
      ¬ Bad δ (Triple.mk n (n+1) (n+(n+1)) rfl (coprime_succ n)) :=
    not_bad_of_not_is_bad_a
      (δ := δ) (X := 2*n+1) (a := n) (b := n+1)
      h (coprime_succ n) ha hb hab
  -- ¬Bad → π-bound, with rad(n*m) = rad(n)*rad(m) conversion
  have hrad_eq : rad (n * (n+1)) = rad n * rad (n+1) :=
    rad_mul_coprime' (coprime_succ n)
  have hbound := piSqRad_le_of_not_bad (coprime_succ n) rfl h_not_bad
  -- Convert: n+(n+1) = 2n+1 and rad(n*(n+1)) = rad(n)*rad(n+1)
  calc (piSqRad (2*n+1) : ℝ)
      = (piSqRad (n+(n+1)) : ℝ) := by ring_nf
    _ ≤ (rad (n*(n+1)) : ℝ) ^ δ := hbound
    _ = (rad n * rad (n+1) : ℝ) ^ δ := by rw [hrad_eq]; norm_cast


/-- Main extraction lemma: From ¬is_bad_a, we get the π-factor bound for adjacent triples.
This is the key bridge from slice-based bad count control to pointwise quality bounds. -/
lemma piSqRad_adjacent_le_of_not_is_bad_a {δ : ℝ} {X : ℕ}
    (h : ¬ is_bad_a δ (2 * X + 1) (X + 1) X) :
    (piSqRad (2 * X + 1) : ℝ) ≤ (rad (X * (X + 1)) : ℝ) ^ δ := by
  -- Use the index-aligned helper `piSqRad_adjacent_le_of_not_is_bad_a'` which
  -- already handles the adjacent triple case (no admits).
  have hbound := piSqRad_adjacent_le_of_not_is_bad_a' (δ := δ) (n := X) h
  -- rad multiplicativity for coprime consecutive integers
  have hrad_eq : rad (X * (X + 1)) = rad X * rad (X + 1) := rad_mul_coprime' (coprime_succ X)
  calc (piSqRad (2 * X + 1) : ℝ)
      ≤ (rad X * rad (X + 1) : ℝ) ^ δ := hbound
    _ = (rad (X * (X + 1)) : ℝ) ^ δ := by rw [hrad_eq]; norm_cast


/-- Bonus lemma: If `n ≤ X` and the adjacent triple is `Bad δ`,
    then the diagonal predicate holds as `is_bad_a δ (2X+1) (n+1) n`. -/
lemma adj_bad_to_diag_is_bad
  {δ : ℝ} {n X : ℕ}
  (hnX : n ≤ X)
  (hbad : Bad δ (Triple.mk n (n + 1) (2 * n + 1) (by ring) (coprime_succ n))) :
  is_bad_a δ (2 * X + 1) (n + 1) n := by
  refine ⟨coprime_succ n, ?_, ?_, ?_, ?_⟩
  -- a ≤ 2X+1
  · exact le_trans (le_two_mul_add_one_left n) <| by
      have : 2*n+1 ≤ 2*X+1 := by nlinarith
      exact this
  -- b ≤ 2X+1
  · exact le_trans (succ_le_two_mul_add_one n) <| by
      have : 2*n+1 ≤ 2*X+1 := by nlinarith
      exact le_trans (Nat.le_of_lt_succ (Nat.lt_succ_self _)) this
  -- a+b ≤ 2X+1
  · have : n + (n+1) = 2*n + 1 := by ring
    have hsum_le : 2*n+1 ≤ 2*X+1 := by nlinarith
    simpa [this] using hsum_le
  -- Bad predicate (need to convert 2*n+1 to n+(n+1))
  · convert hbad


-- ========================================================================
-- Phase 3: Borel-Cantelli approach to density extraction
-- ========================================================================

-- ========================================================================
-- Phase 3: Borel-Cantelli Framework (確率空間版)
-- ========================================================================


/-- 隣接一点事象：`(2n+1, n+1, n)` が bad（スケールは 2n+1 に固定） -/
def BadAdj (δ : ℝ) (n : ℕ) (Ω : Type*) [MeasurableSpace Ω] : Set Ω :=
  {_ω | is_bad_a δ (2*n+1) (n+1) n}


/-- BadAdj は可測集合である。
    is_bad_a は deterministic な述語（ω によらない）なので、全体または空集合のどちらか。 -/
lemma BadAdj_measurable {δ : ℝ} {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] :
  MeasurableSet (BadAdj δ n Ω) := by
  -- is_bad_a δ (2n+1) (n+1) n は Prop で、ω に依存しない
  -- したがって BadAdj は全体 (univ) または空集合 (∅) のどちらか
  by_cases h : is_bad_a δ (2*n+1) (n+1) n
  · -- is_bad_a が真なら BadAdj = univ
    have : BadAdj δ n Ω = Set.univ := by
      ext ω
      simp [BadAdj, h]
    rw [this]
    exact MeasurableSet.univ
  · -- is_bad_a が偽なら BadAdj = ∅
    have : BadAdj δ n Ω = ∅ := by
      ext ω
      simp [BadAdj, h]
    rw [this]
    exact MeasurableSet.empty


/-- μ.real Set.univ が 1 であること（確率測度 μ の全空間の実数値が 1 になること）を示す補題 -/
lemma prob_real_univ {Ω} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
  μ.real Set.univ = 1 := by
  have : μ Set.univ = 1 := measure_univ
  simp [Measure.real, this]


/-- MGF/Chernoff から導くべき"一点事象"の尾確率：`β>1` で可算和収束に落とす。

    実装方針：
    1) 確率空間の構成：(a,b,c) の三つ組を uniform random に選ぶモデル
    2) BadAdj イベント：`is_bad_a δ (2n+1) (n+1) n` を満たす (a,b,c) の集合
    3) MGF bound：ABC.lean の `mgf_bound_unit01` を使う
       - 各スライス b = n+1 で a ∈ [0, n] に制限
       - 指示関数の和に Chernoff bound を適用
    4) Chernoff inequality：E[X] = μ に対して
       P(X ≥ (1+δ)μ) ≤ exp(-δ²μ/3) (δ > 0)
    5) 尾確率の評価：
       - スライスの期待値 μ ≈ n^α (α < 1)
       - Deviation bound で P(Bad) ≤ exp(-c₁ n^α)
       - α ≥ 0.75 なら β = 3/2 で exp(-c*(log n)^(3/2)) が上界

    具体的定数の選択（暫定）：
    - β = 3/2（中域の指数）
    - c = 1（MGF の定数から導出）
    - C = 1（有限個の n での最大値）
    - n0 = 10（十分大きな n の閾値）

    Phase 3 TODO: ABC.lean の MidBlock 枠組みから厳密に導出。 -/
theorem tail_prob_is_bad_adjacent
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (δ : ℝ) (hδ : 0 < δ) :
  ∃ (C c β : ℝ) (n0 : ℕ),
      0 < C ∧ 0 < c ∧ 1 < β ∧
      ∀ n ≥ n0,
        μ.real (BadAdj δ n Ω) ≤ C * Real.exp (- c * (Real.log n) ^ β) := by
  -- 暫定的な定数設定
  use 1, 1, 3/2, 10
  constructor
  · norm_num  -- 0 < 1
  constructor
  · norm_num  -- 0 < 1
  constructor
  · norm_num  -- 1 < 3/2
  intro n hn
  -- Phase 3 TODO: 以下の実装が必要
  -- 1) BadAdj の定義を展開：{ω | is_bad_a δ (2n+1) (n+1) n}
  -- 2) is_bad_a の確率的表現：スライス b = n+1 で a ∈ [0,n] の悪い個数
  -- 3) ABC.lean の mgf_bound_unit01 を適用：
  --    ∀ᵐ ω, 0 ≤ indR (BadSlice n) ω ≤ 1 から
  --    E[exp(λ(X - EX))] ≤ exp(λ²/8)
  -- 4) Chernoff bound：最適な λ を選んで
  --    P(X ≥ (1+δ)EX) ≤ exp(-δ²EX/3)
  -- 5) EX ≈ n^0.75 (中域の密度) から
  --    P(Bad) ≤ exp(-c₁ n^0.75)
  -- 6) n^0.75 ≥ (log n)^(3/2) for large n を使って
  --    exp(-c₁ n^0.75) ≤ exp(-c*(log n)^(3/2))
  -- 7) n ≥ 10 で不等式が成立することを確認
  admit


-- 技術補題：`T ≤ log n` を保証する十分大きい `n` を与える
private lemma eventually_log_ge (T : ℝ) :
  ∀ᶠ n : ℕ in atTop, T ≤ Real.log (n : ℝ) := by
  -- n ≥ ⌈exp T⌉ なら log n ≥ T
  refine (eventually_ge_atTop (Nat.ceil (Real.exp T))).mono ?_
  intro n hn
  have hx : Real.exp T ≤ (n : ℝ) := by
    have : Real.exp T ≤ (Nat.ceil (Real.exp T) : ℝ) := Nat.le_ceil _
    exact this.trans (by exact_mod_cast hn)
  have hn_pos : 0 < (n : ℝ) := by
    calc (0 : ℝ) < Real.exp T := Real.exp_pos T
      _ ≤ (n : ℝ) := hx
  have := Real.log_le_log (Real.exp_pos T) hx
  simpa [Real.log_exp] using this


-- 比較判定のための最終的な上界：exp(-c (log n)^β) ≤ 1 / n^2 （大きな n）
private lemma eventually_exp_neg_log_pow_le_inv_sq
  (c β : ℝ) (hc : 0 < c) (hβ : 1 < β) :
  ∀ᶠ n : ℕ in atTop, (if n = 0 then (0 : ℝ) else Real.exp (- c * (Real.log n) ^ β))
                 ≤ (if n = 0 then (0 : ℝ) else 1 / (n : ℝ)^2) := by
  have hβ' : 0 < β - 1 := sub_pos.mpr hβ
  -- しきい値 T：c * T^(β-1) = 2 を満たす
  let T : ℝ := (2 / c) ^ (1 / (β - 1))
  have hT_nonneg : 0 ≤ T := by
    apply Real.rpow_nonneg
    positivity
  -- log n ≥ T を最終的に確保
  have hE := eventually_log_ge T
  refine hE.mono ?_
  intro n hn_log
  by_cases h0 : n = 0
  · simp [h0]
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0)
  have hlog_pos : 0 < Real.log n := by
    apply Real.log_pos
    calc (1 : ℝ) < Real.exp T := by
          have hT_pos : 0 < T := by
            have h1 : 0 < 2 / c := by positivity
            exact Real.rpow_pos_of_pos h1 _
          exact Real.one_lt_exp_iff.mpr hT_pos
      _ ≤ (n : ℝ) := by
        have : T ≤ Real.log n := hn_log
        have : Real.exp T ≤ n := by
          rw [← Real.exp_log hn_pos]
          exact Real.exp_le_exp.mpr this
        exact this
  have hlog_nonneg : 0 ≤ Real.log n := le_of_lt hlog_pos

  -- (log n)^(β-1) ≥ T^(β-1) を示す
  have h_pow : (Real.log n) ^ (β - 1) ≥ T ^ (β - 1) := by
    apply Real.rpow_le_rpow hT_nonneg hn_log
    linarith

  -- c * (log n)^β ≥ 2 * log n を導く
  have h_exponent : c * (Real.log n) ^ β ≥ 2 * Real.log n := by
    have hTdef : c * T ^ (β - 1) = 2 := by
      have hβne : β - 1 ≠ 0 := ne_of_gt hβ'
      have : T ^ (β - 1) = 2 / c := by
        have h2c_pos : 0 < 2 / c := by positivity
        calc T ^ (β - 1)
            = ((2 / c) ^ (1 / (β - 1))) ^ (β - 1) := rfl
          _ = (2 / c) ^ ((1 / (β - 1)) * (β - 1)) := by
              rw [Real.rpow_mul (le_of_lt h2c_pos)]
          _ = (2 / c) ^ (1 : ℝ) := by
              congr 1
              have : (1 / (β - 1)) * (β - 1) = 1 := by
                field_simp
              exact this
          _ = 2 / c := Real.rpow_one _
      calc c * T ^ (β - 1) = c * (2 / c) := by rw [this]
        _ = 2 := by field_simp
    have hlog_pow_decomp : (Real.log n) ^ β = Real.log n * (Real.log n) ^ (β - 1) := by
      have : β = 1 + (β - 1) := by ring
      rw [this, Real.rpow_add hlog_pos, Real.rpow_one]
      ring_nf
    calc c * (Real.log n) ^ β
        = c * (Real.log n * (Real.log n) ^ (β - 1)) := by rw [hlog_pow_decomp]
      _ = c * (Real.log n) ^ (β - 1) * Real.log n := by ring
      _ ≥ c * T ^ (β - 1) * Real.log n := by
          gcongr
      _ = 2 * Real.log n := by rw [hTdef]

  -- 指数の単調性で exp(-c (log n)^β) ≤ exp(-2 log n)
  have h_exp_le : Real.exp (-(c * (Real.log n) ^ β)) ≤ Real.exp (-2 * Real.log n) := by
    apply Real.exp_le_exp.mpr
    linarith

  -- exp(-2 log n) = (n^2)⁻¹
  have h_exp_eq : Real.exp (-2 * Real.log n) = ((n : ℝ)^2)⁻¹ := by
    have : Real.log ((n : ℝ) ^ (-2 : ℝ)) = -2 * Real.log n := Real.log_rpow hn_pos (-2)
    have := congrArg Real.exp this.symm
    simp only [Real.exp_log (Real.rpow_pos_of_pos hn_pos _)] at this
    rw [Real.rpow_neg (by positivity : 0 ≤ (n : ℝ))] at this
    rw [Real.rpow_two] at this
    exact this

  simp only [h0, ↓reduceIte, neg_mul, one_div, ge_iff_le]
  calc Real.exp (-(c * (Real.log n) ^ β))
      ≤ Real.exp (-2 * Real.log n) := h_exp_le
    _ = ((n : ℝ)^2)⁻¹ := h_exp_eq


/-- `β>1` なら `∑ exp(-c * (log n)^β)` は収束（`n=0` を 0 で潰す）。
    p-級数比較：β > 1 なら大きな n で c*(log n)^β ≥ 2*log n が成り立ち、
    exp(-c*(log n)^β) ≤ n^(-2) となる。∑ 1/n² は収束（p=2>1）なので比較定理により収束。 -/
theorem summable_exp_neg_log_pow (c β : ℝ) (hc : 0 < c) (hβ : 1 < β) :
  Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else Real.exp (-(c * (Real.log n) ^ β))) := by
  -- 比較対象 g(n) = 1/n^2 は収束
  have h_g_summable : Summable (fun n : ℕ => 1 / ((n : ℝ)^2)) := by
    have : (1 : ℝ) < 2 := by norm_num
    convert Real.summable_one_div_nat_rpow.mpr this using 1
    ext n
    rw [Real.rpow_two]

  -- eventually で exp(...) ≤ 1/n^2 が成り立つ
  have h_event : ∀ᶠ n : ℕ in Filter.atTop,
      ‖if n = 0 then (0 : ℝ) else Real.exp (-(c * (Real.log n) ^ β))‖ ≤ 1 / ((n : ℝ)^2) := by
    have hE := eventually_exp_neg_log_pow_le_inv_sq c β hc hβ
    simp only [Filter.eventually_atTop] at hE ⊢
    obtain ⟨N, hN⟩ := hE
    -- N を十分大きく取り直すことで N ≥ 1 とできる
    use max N 1
    intro n hn
    have hN1 : 1 ≤ max N 1 := Nat.le_max_right N 1
    have hn_ge_N : N ≤ n := Nat.le_trans (Nat.le_max_left N 1) hn
    have hn_pos : 0 < n := Nat.lt_of_lt_of_le (Nat.zero_lt_one) (Nat.le_trans hN1 hn)
    have h0 : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn_pos
    simp only [h0, ↓reduceIte, Real.norm_eq_abs]
    have hexp_pos : 0 ≤ Real.exp (-(c * (Real.log n) ^ β)) := le_of_lt (Real.exp_pos _)
    rw [abs_of_nonneg hexp_pos]
    have := hN n hn_ge_N
    simp only [h0, ↓reduceIte, neg_mul, one_div] at this
    rw [← inv_eq_one_div]
    exact this

  -- Summable.of_norm_bounded_eventually_nat を適用
  exact Summable.of_norm_bounded_eventually_nat h_g_summable h_event

end ABC
