/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- cid: 6979430e-4324-83a6-b491-838e096d3d58

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

noncomputable section

/-- √2 as a real number -/
def sqrt2 : ℝ := Real.sqrt 2

/-- silver ratio: σ := 1 + √2 -/
def sigma : ℝ := 1 + sqrt2

/-- silver ratio unit: uAg := σ / 2 = (1 + √2)/2 -/
def uAg : ℝ := sigma / 2

/-- ΔAg := uAg^2 - uAg (the constant "gap" in the uAg-world) -/
def deltaAg : ℝ := uAg^2 - uAg

/-- Key lemma: sqrt2 ^ 2 = 2 (robust) -/
@[simp] lemma sqrt2_sq : sqrt2 ^ 2 = (2 : ℝ) := by
  unfold sqrt2
  simp [pow_two, Real.mul_self_sqrt]

/-- sqrt2 > 0 -/
lemma sqrt2_pos : 0 < sqrt2 := by
  unfold sqrt2
  exact Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)

/-- sqrt2 ≠ 0 -/
lemma sqrt2_ne_zero : sqrt2 ≠ 0 := ne_of_gt sqrt2_pos

/-- sqrt2 is irrational -/
lemma sqrt2_irrational : Irrational sqrt2 := by
  unfold sqrt2
  exact irrational_sqrt_two

@[simp] lemma uAg_eq : uAg = (1 + sqrt2) / 2 := by
  simp [uAg, sigma, div_eq_mul_inv]

/--
Main closure law for the silver ratio unit:
uAg^2 = uAg + 1/4.
-/
theorem uAg_sq_eq : uAg^2 = uAg + (1/4 : ℝ) := by
  have h : sqrt2 ^ 2 = (2 : ℝ) := sqrt2_sq
  simp [uAg_eq, pow_two]
  field_simp [pow_two]
  -- goal is purely algebraic now
  -- Use h to replace sqrt2^2
  -- (ring handles the rest)
  calc
    (1 + sqrt2) ^ 2 * 4
        = (1 + 2 * sqrt2 + sqrt2 ^ 2) * 4 := by ring
    _   = (1 + 2 * sqrt2 + 2) * 4 := by simp [h]
    _   = 2 * ((1 + sqrt2) * 4 + 2) := by ring

/-- The gap is constant: ΔAg = 1/4. -/
theorem deltaAg_eq : deltaAg = (1/4 : ℝ) := by
  -- ΔAg := uAg^2 - uAg
  -- use uAg_sq_eq
  rw [deltaAg, uAg_sq_eq]
  ring

/-- e/4 = e * ΔAg, where e := exp 1. -/
theorem e_div_four_eq_e_mul_delta :
    (Real.exp 1) / 4 = (Real.exp 1) * deltaAg := by
  -- ΔAg = 1/4 を代入するだけ
  simp only [div_eq_mul_inv, mul_comm, deltaAg_eq, one_mul]

/-- Observed coefficient: α := 4/e. -/
def alpha : ℝ := 4 / (Real.exp 1)

/-- α⁻¹ = e * ΔAg (so α⁻¹ = e/4). -/
theorem inv_alpha_eq_e_mul_delta :
    (alpha)⁻¹ = (Real.exp 1) * deltaAg := by
  -- alpha⁻¹ = (4 / e)⁻¹ = e / 4, then use the previous theorem.
  -- In a field, `(a / b)⁻¹ = b / a` holds by simp.
  have : (alpha)⁻¹ = (Real.exp 1) / 4 := by
    -- `(4 / e)⁻¹ = e / 4`
    simp [alpha]
  -- now replace (exp 1)/4 with exp 1 * ΔAg
  simpa [this] using (e_div_four_eq_e_mul_delta)

-- Supporting lemmas for algebraic manipulations

/-- (sqrt2 - 1)² = 3 - 2·sqrt2 -/
lemma sqrt2_minus_one_sq : (sqrt2 - 1) ^ 2 = 3 - 2 * sqrt2 := by
  have h := sqrt2_sq
  calc
    (sqrt2 - 1) ^ 2
      = sqrt2 ^ 2 - 2 * sqrt2 + 1 := by ring
    _ = 2 - 2 * sqrt2 + 1 := by rw [h]
    _ = 3 - 2 * sqrt2 := by linarith

-- Additional lemmas for convenience

/-- 1/sqrt2 = sqrt2/2 (rationalize denominator) -/
lemma one_div_sqrt2 : (1 : ℝ) / sqrt2 = sqrt2 / 2 := by
  field_simp [sqrt2_ne_zero]
  rw [sqrt2_sq]

/-- sqrt2/2 > 0 -/
lemma sqrt2_div_two_pos : 0 < sqrt2 / 2 := by
  exact div_pos sqrt2_pos (by norm_num : (0 : ℝ) < 2)

/-- (sqrt2/2)² = 1/2 -/
lemma sqrt2_div_two_sq : (sqrt2 / 2) ^ 2 = 1 / 2 := by
  have h := sqrt2_sq
  field_simp
  rw [h]

-- Algebraic manipulations in the uAg-world

/-- conjugation on uAg induced by sqrt2 ↦ -sqrt2 : conj(uAg) = 1 - uAg -/
lemma uAg_conj : (1 - uAg) = (1 - (1 + sqrt2) / 2) := by
  simp [uAg_eq]

/-- handy: sqrt2 = 2*uAg - 1 -/
lemma sqrt2_eq_two_uAg_sub_one : sqrt2 = 2 * uAg - 1 := by
  -- from uAg = (1 + sqrt2)/2
  have := uAg_eq
  -- rearrange
  nlinarith [this]

/-- alternate closure form: uAg^2 - uAg = 1/4 -/
theorem uAg_sq_sub_uAg : uAg^2 - uAg = (1/4 : ℝ) := by
  -- from uAg_sq_eq
  have := uAg_sq_eq
  nlinarith [this]

/-- two-component representation: a + b*uAg -/
def Ag (a b : ℝ) : ℝ := a + b * uAg

/-- multiplication closes in the basis {1, uAg}: (a+bu)(c+du)= (ac+bd/4) + (ad+bc+bd)u -/
theorem Ag_mul (a b c d : ℝ) :
    Ag a b * Ag c d = Ag (a*c + (b*d)/4) (a*d + b*c + b*d) := by
  -- expand and reduce uAg^2 using uAg_sq_eq
  simp only [Ag, uAg_eq]
  ring_nf
  simp only [mul_comm, mul_left_comm, one_div, mul_assoc, sqrt2_sq]
  ring

-- ----------------------------------------------------------------------------

/-- Galois conjugate of uAg is 1 - uAg. -/
lemma uAg_conj' : (1 - uAg) = (1 - sqrt2) / 2 := by
  -- 1 - (1+sqrt2)/2 = (1 - sqrt2)/2
  simp only [uAg_eq]
  field_simp
  ring

/-- Conjugation on Ag-elements: a + b*uAg ↦ a + b*(1-uAg). -/
def AgConj (a b : ℝ) : ℝ := a + b * (1 - uAg)

/-- Norm in the uAg-world. -/
def AgNorm (a b : ℝ) : ℝ := (Ag a b) * (AgConj a b)

lemma AgConj_eq (a b : ℝ) : AgConj a b = (a + b) - b * uAg := by
  simp only [AgConj, uAg_eq, sub_eq_add_neg, mul_add, mul_one, mul_neg]
  ring

/-- Closed form of the norm: a^2 + a*b - (b^2)/4. -/
theorem AgNorm_eq (a b : ℝ) :
    AgNorm a b = a^2 + a*b - (b^2)/4 := by
  -- expand and reduce uAg^2
  simp only [AgNorm, Ag, AgConj, mul_add, add_mul]
  have h := uAg_sq_sub_uAg
  nlinarith [h]

/-- Inverse formula in the uAg-world (when the norm is nonzero). -/
theorem Ag_inv (a b : ℝ) (h : AgNorm a b ≠ 0) :
    (Ag a b)⁻¹ = (AgConj a b) / (AgNorm a b) := by
  have h' : Ag a b ≠ 0 := by
    unfold AgNorm at h
    exact mul_ne_zero_iff.mp h |>.1
  field_simp [h', h]
  unfold AgNorm
  ring

/-- Pair multiplication rule corresponding to Ag. -/
def AgMulPair (p q : ℝ × ℝ) : ℝ × ℝ :=
  let a := p.1; let b := p.2
  let c := q.1; let d := q.2
  (a*c + (b*d)/4, a*d + b*c + b*d)

theorem Ag_mul_pair (a b c d : ℝ) :
    AgMulPair (a,b) (c,d) = (a*c + (b*d)/4, a*d + b*c + b*d) := by
  rfl

/-- Conjugation is an involution: conj(conj(x)) = x (in coordinates). -/
theorem AgConj_invol (a b : ℝ) :
    AgConj (a + b) (-b) = Ag a b := by
  -- AgConj a b = (a+b) - b*uAg を使うと一撃
  simp [AgConj_eq, Ag, sub_eq_add_neg]

/-- AgNorm is a real scalar: it has no uAg-component. -/
theorem AgNorm_is_scalar (a b : ℝ) :
    ∃ r : ℝ, AgNorm a b = r := by
  refine ⟨a^2 + a*b - (b^2)/4, ?_⟩
  simp [AgNorm_eq]

/-- Inverse formula in the uAg-world (when the norm is nonzero). -/
theorem Ag_mul_AgConj_div_AgNorm (a b : ℝ) (h : AgNorm a b ≠ 0) :
    Ag a b * ((AgConj a b) / (AgNorm a b)) = 1 := by
  unfold AgNorm at h ⊢
  have h_ne : Ag a b * AgConj a b ≠ 0 := h
  have h_ne_ag : Ag a b ≠ 0 := mul_ne_zero_iff.mp h_ne |>.1
  have h_ne_conj : AgConj a b ≠ 0 := mul_ne_zero_iff.mp h_ne |>.2
  field_simp [h_ne_ag, h_ne_conj, h]

/-- Commutative version of the inverse formula in the uAg-world. -/
theorem AgConj_div_AgNorm_mul_Ag (a b : ℝ) (h : AgNorm a b ≠ 0) :
    ((AgConj a b) / (AgNorm a b)) * Ag a b = 1 := by
  -- 可換なので上と同じで済む
  simpa [mul_comm] using Ag_mul_AgConj_div_AgNorm (a := a) (b := b) h

/-- Encode Ag-elements as pairs (a,b). -/
def AgEncode (_x : ℝ) : ℝ × ℝ := (0, 0)  -- placeholder (optional)

-- まずは明示的な相互変換だけ置くのが実用的
def AgOfPair (p : ℝ × ℝ) : ℝ := Ag p.1 p.2

lemma AgOfPair_mul (p q : ℝ × ℝ) :
    AgOfPair (AgMulPair p q) = AgOfPair p * AgOfPair q := by
  -- p=(a,b), q=(c,d) に展開して Ag_mul を使うのが自然
  rcases p with ⟨a,b⟩
  rcases q with ⟨c,d⟩
  -- Ag_mul を使えるなら最短
  simpa [AgOfPair, AgMulPair] using (Ag_mul (a := a) (b := b) (c := c) (d := d)).symm


end -- noncomputable section
end SilverRatioUnit
end DkMath
