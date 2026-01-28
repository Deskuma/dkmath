/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

namespace DkMath

/-
  Silver Ratio Unit formalization (core lemmas)

  Notation policy:
    σ     := 1 + √2
    uAg   := σ / 2
    ΔAg   := uAg^2 - uAg = 1/4
    e     := Real.exp 1
-/

namespace SilverRatioUnit

open Real

/-- silver ratio: σ := 1 + √2 -/
noncomputable def sigma : ℝ := 1 + Real.sqrt 2

/-- silver ratio unit: uAg := σ / 2 = (1 + √2)/2 -/
noncomputable def uAg : ℝ := sigma / 2

/-- ΔAg := uAg^2 - uAg (the constant "gap" in the uAg-world) -/
noncomputable def deltaAg : ℝ := uAg^2 - uAg

@[simp] lemma uAg_eq : uAg = (1 + Real.sqrt 2) / 2 := by
  simp [uAg, sigma, div_eq_mul_inv]

/-- helper: (√2)^2 = 2 -/
lemma sq_sqrt_two : (Real.sqrt 2)^2 = (2 : ℝ) := by
  -- `Real.sq_sqrt` returns (sqrt x)^2 = x for 0 ≤ x, up to simp normalization.
  -- Different Mathlib versions may prefer `by simp [pow_two]`.
  simp only [pow_two, Nat.ofNat_nonneg, mul_self_sqrt]

/--
Main closure law for the silver ratio unit:
uAg^2 = uAg + 1/4.
-/
theorem uAg_sq_eq : uAg^2 = uAg + (1/4 : ℝ) := by
  -- reduce to a pure algebraic identity using (√2)^2 = 2
  -- Start from the concrete form uAg = (1 + √2)/2
  have hs : (Real.sqrt 2)^2 = (2 : ℝ) := sq_sqrt_two
  -- rewrite uAg and clear denominators
  -- goal becomes: ((1+√2)/2)^2 = (1+√2)/2 + 1/4
  -- Multiply by 4 and expand; it reduces to hs.
  -- `field_simp` works well here.
  -- (If `field_simp` complains, replace 2 with (2:ℝ) etc.)
  simp [uAg_eq, pow_two]  -- puts the goal in terms of (1+√2)/2
  -- Now:
  -- ⊢ ((1 + √2) / 2) * ((1 + √2) / 2) = (1 + √2) / 2 + 1/4
  field_simp [pow_two]    -- clears denominators (×4)
  -- goal: (1 + √2)^2 * 4 = 2 * ((1 + √2) * 4 + 2)
  -- expand and use hs
  have : (1 + Real.sqrt 2)^2 * 4 = 2 * ((1 + Real.sqrt 2) * 4 + 2) := by
    ring_nf
    rw [hs]
    ring
  exact this

/-- The gap is constant: ΔAg = 1/4. -/
theorem deltaAg_eq : deltaAg = (1/4 : ℝ) := by
  -- ΔAg := uAg^2 - uAg
  -- use uAg_sq_eq
  rw [deltaAg, uAg_sq_eq]
  ring

/-- e/4 = e * ΔAg, where e := exp 1. -/
theorem e_div_four_eq_e_mul_delta :
    (Real.exp 1) / 4 = (Real.exp 1) * deltaAg := by
  -- substitute ΔAg = 1/4
  simp only [div_eq_mul_inv, mul_comm, deltaAg_eq, one_mul]

/-- Observed coefficient: α := 4/e. -/
noncomputable def alpha : ℝ := 4 / (Real.exp 1)

/-- α⁻¹ = e * ΔAg (so α⁻¹ = e/4). -/
theorem inv_alpha_eq_e_mul_delta :
    (alpha)⁻¹ = (Real.exp 1) * deltaAg := by
  -- alpha⁻¹ = (4 / e)⁻¹ = e / 4, then use the previous theorem.
  -- In a field, `(a / b)⁻¹ = b / a` holds by simp.
  -- If simp fails in your Mathlib, rewrite with `div_eq_mul_inv` and group laws.
  have : (alpha)⁻¹ = (Real.exp 1) / 4 := by
    -- `(4 / e)⁻¹ = e / 4`
    simp [alpha]
  -- now replace (exp 1)/4 with exp 1 * ΔAg
  simpa [this] using (e_div_four_eq_e_mul_delta)

end SilverRatioUnit

end DkMath
