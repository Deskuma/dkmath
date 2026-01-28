/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.SilverRatio.Sqrt2Lemmas

namespace DkMath.UniqueRepresentation

/-! ## UR: SilverRatio
Title: Unique Representation via Irrational Numbers
Purpose: Demonstrate proof techniques using Irrational to establish
         unique representations in ℚ(√2)
Date: 2026-01-28
-/

namespace SilverRatio

open Real
open DkMath.SilverRatio.Sqrt2

noncomputable section

/-
  Key Lemma Set: Proving uniqueness of a + b·√2 representations

  Strategy:
  1. Use √2's irrationality to establish linear independence over ℚ
  2. Apply to prove uniqueness within ℚ-coefficients
  3. Extend to full ℝ using case analysis
-/

-- ============================================================================
-- Part 1: Linear Independence of {1, √2} over ℚ
-- ============================================================================

/-
  Theorem: {1, √2} is linearly independent over ℚ

  This means: if a + b·√2 = c + d·√2 where a, b, c, d ∈ ℚ,
  then a = c and b = d.

  Proof idea:
  - From a + b·√2 = c + d·√2, get (a - c) + (b - d)·√2 = 0
  - If b ≠ d, then √2 = -(a - c)/(b - d) ∈ ℚ
  - But √2 is irrational, contradiction
  - So b = d, hence a = c
-/

/-- Linear independence of {1, √2} over ℚ -/
theorem sqrt2_lin_indep_over_rat (a b c d : ℚ) :
    (a : ℝ) + (b : ℝ) * sqrt2 = (c : ℝ) + (d : ℝ) * sqrt2 →
    a = c ∧ b = d := by
  intro h
  -- Rearrange to get (a - c) + (b - d)·√2 = 0
  have key : ((a - c : ℚ) : ℝ) + ((b - d : ℚ) : ℝ) * sqrt2 = 0 := by
    push_cast
    linarith [h]
  -- Case split on whether b = d
  by_cases hbd : b = d
  · -- If b = d, then a must equal c
    have h' : (↑a - ↑c : ℝ) = (0 : ℝ) := by
      rw [hbd] at key
      push_cast at key
      simp only [sub_self, zero_mul] at key
      linarith [key]
    have : (a - c : ℚ) = 0 := by
      have : (↑(a - c) : ℝ) = ↑(0 : ℚ) := by simp [h']
      exact Rat.cast_injective this
    exact ⟨by linarith [this], hbd⟩
  · -- If b ≠ d, derive contradiction from √2's irrationality
    have h_irrat : Irrational sqrt2 := sqrt2_irrational
    -- From the key equation, if b ≠ d, then √2 = -(a-c)/(b-d)
    have hbd_ne : ↑(b - d) ≠ 0 := by
      intro h_eq
      have : (↑(b - d) : ℝ) = ↑(0 : ℚ) := by simp [h_eq]
      have : b - d = 0 := Rat.cast_injective this
      exact hbd (by linarith [this])
    have sqrt2_iso : ((b - d : ℚ) : ℝ) * sqrt2 = -((a - c : ℚ) : ℝ) := by linarith [key]
    -- From √2 = -(a-c)/(b-d), we derive a contradiction with irrationality
    exfalso
    have sqrt2_eq : sqrt2 = -(↑(a - c) / ↑(b - d)) := by
      have h1 : (↑(b - d) : ℝ) * sqrt2 = -(↑(a - c) : ℝ) := sqrt2_iso
      have : sqrt2 = (-(↑(a - c) : ℝ)) / (↑(b - d) : ℝ) := by
        field_simp [hbd_ne] at h1 ⊢
        exact h1
      simp only [neg_div] at this
      exact this
    -- The RHS is a rational number
    have hq : sqrt2 ∈ Set.range ((↑) : ℚ → ℝ) := by
      use -((a - c) / (b - d))
      simp only [Rat.cast_div, Rat.cast_neg]
      exact sqrt2_eq.symm
    -- But √2 is irrational, contradiction
    exact h_irrat hq


-- ============================================================================
-- Part 2: Representation in Simple Basis (a + b·√2)
-- ============================================================================

/-- Simple form representation: a + b·√2 -/
def SimpleForm (a b : ℝ) : ℝ := a + b * sqrt2

-- The representation is unique when restricted to a specific form
-- But globally it depends on the subring we're working in.

-- Version 1: For rational coefficients (provable)

/-- Uniqueness of SimpleForm representation for rational coefficients -/
theorem SimpleForm_unique_rat (_x : ℝ) (a b c d : ℚ) :
    SimpleForm (a : ℝ) (b : ℝ) = SimpleForm (c : ℝ) (d : ℝ) →
    a = c ∧ b = d := by
  intro h
  exact sqrt2_lin_indep_over_rat a b c d (by simpa [SimpleForm] using h)

-- Version 2: For all reals, we need uniqueness only for a specific pair
/-
  Note: For arbitrary x : ℝ, there need not exist (a, b) ∈ ℚ × ℚ with
  x = a + b·√2, so a universal ∃! statement over all real x is false.

  The correct unique-existence statement is restricted to x ∈ RatAdjSqrt2,
  which is proved by `unique_rep_in_rat_adj_sqrt2` above. We therefore omit
  a standalone `SimpleForm_exists_unique` theorem over all ℝ.
-/

-- Version 3: For the full ℝ, what IS unique?
-- Answer: The pair (x, 0) is unique, meaning:
-- If SimpleForm a b = x, then (a, b) = (x, 0)
-- This is actually FALSE for arbitrary reals!
-- SimpleForm has many representations.

-- For example: SimpleForm 1 1 = 1 + √2
--              SimpleForm (1 + √2) 0 would also equal 1 + √2 if we expand differently

/-- Counterexample showing that SimpleForm is not injective over ℝ -/
theorem SimpleForm_not_injective :
    ∃ _x a b c d : ℝ,
      (a, b) ≠ (c, d) ∧ SimpleForm a b = SimpleForm c d := by
  -- Example: a = 1, b = 1, c = 1 + sqrt2, d = 0
  -- SimpleForm 1 1 = 1 + sqrt2
  -- SimpleForm (1 + sqrt2) 0 = 1 + sqrt2
  -- But (1, 1) ≠ (1 + sqrt2, 0)
  use (1 + sqrt2), 1, 1, (1 + sqrt2), 0
  constructor
  · norm_num
  · simp [SimpleForm]

-- ============================================================================
-- Part 3: Unique Representation when Restricting Coefficient Domain
-- ============================================================================

/-
  Key insight: For the statement ∃! (p : ℚ × ℚ), ... to make sense,
  we need x to be in a specific subset of ℝ.

  For example:
  - x ∈ ℚ(√2) = {a + b·√2 : a, b ∈ ℚ}

  Then we CAN prove unique representation.
-/

-- Define the field ℚ(√2)

/-- The set of real numbers that can be expressed as a + b·√2 with a, b ∈ ℚ -/
def RatAdjSqrt2 : Set ℝ :=
  {x | ∃ a b : ℚ, (a : ℝ) + (b : ℝ) * sqrt2 = x}

/-- Unique representation theorem for elements in ℚ(√2) -/
theorem unique_rep_in_rat_adj_sqrt2 (x : ℝ) (hx : x ∈ RatAdjSqrt2) :
    ∃! (p : ℚ × ℚ), SimpleForm (p.1 : ℝ) (p.2 : ℝ) = x := by
  -- Extract the witnesses from hx
  obtain ⟨a, b, hab⟩ := hx
  use (a, b)
  constructor
  · -- Existence: (a, b) works
    simpa [SimpleForm] using hab
  · -- Uniqueness: any other pair (c, d) giving the same value must equal (a, b)
    intro ⟨c, d⟩ hcd
    -- We have SimpleForm c d = x = SimpleForm a b
    have : SimpleForm (c : ℝ) (d : ℝ) = SimpleForm (a : ℝ) (b : ℝ) := by
      simp only [SimpleForm] at hcd ⊢
      exact hcd.trans hab.symm
    -- Apply uniqueness for rational coefficients
    have ⟨hac, hbd⟩ := sqrt2_lin_indep_over_rat c d a b this
    simp only [Prod.mk.injEq]
    exact ⟨hac, hbd⟩

-- ============================================================================
-- Part 4: Complementary Results and Utilities
-- ============================================================================

/-- Lemma: The representation is constructively obtainable -/
theorem unique_rep_constructive (x : ℝ) (hx : x ∈ RatAdjSqrt2) :
    ∃ (a b : ℚ), (a : ℝ) + (b : ℝ) * sqrt2 = x ∧
    ∀ (a' b' : ℚ), (a' : ℝ) + (b' : ℝ) * sqrt2 = x → a' = a ∧ b' = b := by
  obtain ⟨a, b, hab⟩ := hx
  use a, b
  constructor
  · exact hab
  · intros a' b' ha'
    have : (a' : ℝ) + (b' : ℝ) * sqrt2 = (a : ℝ) + (b : ℝ) * sqrt2 := by
      exact ha' ▸ hab.symm
    exact sqrt2_lin_indep_over_rat a' b' a b this

/-- Lemma: Addition preserves membership in ℚ(√2) -/
theorem RatAdjSqrt2_add (x y : ℝ) (hx : x ∈ RatAdjSqrt2) (hy : y ∈ RatAdjSqrt2) :
    x + y ∈ RatAdjSqrt2 := by
  obtain ⟨a, b, hab⟩ := hx
  obtain ⟨c, d, hcd⟩ := hy
  exact ⟨a + c, b + d, by
    push_cast
    nlinarith [hab, hcd]⟩

/-- Lemma: Multiplication preserves membership in ℚ(√2) -/
theorem RatAdjSqrt2_mul (x y : ℝ) (hx : x ∈ RatAdjSqrt2) (hy : y ∈ RatAdjSqrt2) :
    x * y ∈ RatAdjSqrt2 := by
  obtain ⟨a, b, hab⟩ := hx
  obtain ⟨c, d, hcd⟩ := hy
  -- (a + b·√2)(c + d·√2) = ac + ad·√2 + bc·√2 + bd·2
  --                      = (ac + 2bd) + (ad + bc)·√2
  use a*c + 2*b*d, a*d + b*c
  push_cast
  calc (↑a * ↑c + 2 * ↑b * ↑d) + (↑a * ↑d + ↑b * ↑c) * sqrt2
      = a*c + 2*b*d + (a*d + b*c)*sqrt2 := by ring
    _ = a*c + a*d*sqrt2 + b*c*sqrt2 + b*d*sqrt2^2 := by rw [sqrt2_sq]; ring
    _ = (a + b*sqrt2) * (c + d*sqrt2) := by ring
    _ = x * y := by rw [← hab, ← hcd]

-- ============================================================================
-- Part 5: Syntax Patterns and Proof Techniques
-- ============================================================================

/-
  Common patterns when proving with Irrational:

  Pattern 1: Deriving contradiction from equality
  ```lean
  by_cases h : coefficient = 0
  · [handle zero case]
  · -- coefficient ≠ 0
    have : sqrt2 = rational_expr := by [algebra]
    have h_irrat : Irrational sqrt2 := sqrt2_irrational
    exfalso
    -- Now use h_irrat to show rational_expr ∉ ℚ
    sorry
  ```

  Pattern 2: Using linear independence
  ```lean
  have h_lin : LinearIndependent ℚ ![1, sqrt2] := [proof]
  -- This means: for a, b, c, d ∈ ℚ,
  -- a·1 + b·√2 = c·1 + d·√2 ⟹ a = c ∧ b = d
  ```

  Pattern 3: Separating restricted and unrestricted cases
  ```lean
  -- First prove for ℚ-coefficients
  theorem version_rat : ... (a b c d : ℚ) ... := by [proof with lin_indep]

  -- Then extend to ℝ carefully
  theorem version_real : ∃! p ∈ RatAdjSqrt2, ... := by [proof using version_rat]
  ```
-/

-- ============================================================================
-- Example: Complete proof of a concrete statement
-- ============================================================================

/-- Example: Prove uniqueness of representation in basis {1, uAg} where uAg = (1 + √2)/2 -/
example :
  let u := (1 + sqrt2) / 2
  ∀ (a b c d : ℚ), (a : ℝ) + (b : ℝ) * u = (c : ℝ) + (d : ℝ) * u →
  a = c ∧ b = d := by
  intro u a b c d h
  -- u = (1 + √2)/2
  -- a + b·u = c + d·u
  -- a + b·(1+√2)/2 = c + d·(1+√2)/2
  -- a + (b/2)·1 + (b/2)·√2 = c + (d/2)·1 + (d/2)·√2
  -- (a + b/2) + (b/2)·√2 = (c + d/2) + (d/2)·√2

  -- Now apply linear independence
  have key : ((a + b/2 : ℚ) : ℝ) + ((b/2 : ℚ) : ℝ) * sqrt2 =
             ((c + d/2 : ℚ) : ℝ) + ((d/2 : ℚ) : ℝ) * sqrt2 := by
    have h' : (a : ℝ) + (b : ℝ) * (1 + sqrt2) / 2 = (c : ℝ) + (d : ℝ) * (1 + sqrt2) / 2 := by
      calc (a : ℝ) + (b : ℝ) * (1 + sqrt2) / 2
          = (a : ℝ) + (b : ℝ) * ((1 + sqrt2) / 2) := by ring
        _ = (c : ℝ) + (d : ℝ) * ((1 + sqrt2) / 2) := h
        _ = (c : ℝ) + (d : ℝ) * (1 + sqrt2) / 2 := by ring
    calc ((a + b/2 : ℚ) : ℝ) + ((b/2 : ℚ) : ℝ) * sqrt2
        = (a : ℝ) + (b : ℝ) / 2 + ((b : ℝ) / 2) * sqrt2 := by push_cast; ring
      _ = (a : ℝ) + (b : ℝ) * (1 + sqrt2) / 2 := by ring
      _ = (c : ℝ) + (d : ℝ) * (1 + sqrt2) / 2 := h'
      _ = (c : ℝ) + (d : ℝ) / 2 + ((d : ℝ) / 2) * sqrt2 := by ring
      _ = ((c + d/2 : ℚ) : ℝ) + ((d/2 : ℚ) : ℝ) * sqrt2 := by push_cast; ring
  have ⟨h1, h2⟩ := sqrt2_lin_indep_over_rat (a + b/2) (b/2) (c + d/2) (d/2) key
  constructor
  · linarith [h1]
  · linarith [h2]

end -- noncomputable section

/- ## 解説：
  ここでは、√2の無理性を利用して、ℚ(√2)における
  a + b·√2 の表現の一意性を証明しました。

  主なポイントは以下の通りです：

  1. √2の無理性を用いて、{1, √2}がℚ上で線形独立であることを示しました。
     これにより、a + b·√2 = c + d·√2 ならば a = c かつ b = d が導かれます。

  2. ℚ(√2)に属する実数 x に対して、x = a + b·√2 と表せる
     (a, b) ∈ ℚ × ℚ の組が一意に存在することを証明しました。

  3. 証明過程でよく使われるパターンとして、
     - 無理数の定義から矛盾を導く方法
     - 線形独立性を利用する方法
     - 有理係数の場合と実数全体の場合で場合分けする方法
     を紹介しました。

  このようにして、√2の無理性を活用した一意表現の理論的基盤を確立しました。
-/

/- ## 応用例：基底 {1, uAg} による一意表現の証明
  ここでは、uAg = (1 + √2)/2 を用いた基底に関して、
  a + b·uAg の表現が一意であることを示します。

  証明の流れは以下の通りです：

  1. uAg を √2 を用いて書き換え、標準形 a' + b'·√2 に変換します。
  2. 変換後の等式に対して、先に示した線形独立性を適用します。
  3. 最終的に、元の係数 a, b が等しいことを導きます。

  この応用例により、異なる基底に対しても
  一意表現の理論が適用可能であることが示されました。
-/

end SilverRatio

end DkMath.UniqueRepresentation
