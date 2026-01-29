/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- cid: 6979430e-4324-83a6-b491-838e096d3d58
-- cid: 697a85c0-f920-8323-9204-b9c2877e3025

import Mathlib
import DkMath.SilverRatio.Sqrt2Lemmas

/-!
  Silver Ratio Unit formalization (core lemmas)

  Notation policy:
    σ     := 1 + √2
    uAg   := σ / 2
    ΔAg   := uAg^2 - uAg = 1/4
    e     := Real.exp 1
-/

namespace DkMath.SilverRatio.Unit

open Real
open DkMath.SilverRatio.Sqrt2

noncomputable section

#check sqrt2  -- Real.sqrt 2
#check sigma  -- 1 + sqrt2
#check sqrt2_sq  -- sqrt2 ^ 2 = 2
#check sqrt2_pos  -- 0 < sqrt2
#check sqrt2_ne_zero  -- sqrt2 ≠ 0
#check sqrt2_irrational  -- Irrational sqrt2

/-- silver ratio unit: uAg := σ / 2 = (1 + √2)/2 -/
def uAg : ℝ := sigma / 2

/-- ΔAg := uAg^2 - uAg (the constant "gap" in the uAg-world) -/
def deltaAg : ℝ := uAg^2 - uAg

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

-- ----------------------------------------------------------------------------
/-- Geometry in the silver ratio unit world -/
theorem AgNorm_eq_zero_iff (a b : ℝ) :
    AgNorm a b = 0 ↔ a^2 + a*b - (b^2)/4 = 0 := by
  simp [AgNorm_eq]

-- ----------------------------------------------------------------------------
/- Additional derived constants -/

/-- Unicode alias for the core constant `deltaAg := uAg^2 - uAg`. -/
def ΔAg : ℝ := deltaAg

/-- ΔAg = 1/4. -/
@[simp] lemma ΔAg_eq : ΔAg = (1/4 : ℝ) := by
  -- unfold through the canonical ASCII name `deltaAg`
  simpa [ΔAg, deltaAg] using uAg_sq_sub_uAg

/-- Gap function: Gap(u) = u^2 - u -/
def Gap (u : ℝ) : ℝ := u^2 - u   -- 「二乗で混ぜて、一次へ戻す」としてのギャップ

/-- Gap(uAg) = 1/4. -/
lemma Gap_uAg : Gap uAg = (1/4 : ℝ) := by
  -- Gap uAg = uAg^2 - uAg = 1/4
  unfold Gap
  exact uAg_sq_sub_uAg

/-- Gap(uAg) = ΔAg. -/
lemma Gap_uAg_eq_ΔAg : Gap uAg = ΔAg := by
  simp only [Gap, uAg_eq, ΔAg, deltaAg]

/-- Mixed term in Ag multiplication: mixTerm(b,d) = b*d -/
def mixTerm (b d : ℝ) : ℝ := b*d
-- Ag_mul の第2成分に mixTerm が現れる、みたいな補題を作ると読み物として強い

/-- AgNorm = 0 ならば (a + b/2)² = (b²)/2 である（平方完成版） -/
theorem AgNorm_eq_zero_iff_sq (a b : ℝ) :
    AgNorm a b = 0 ↔ (a + b/2)^2 = (b^2)/2 := by
  -- まず AgNorm_eq_zero_iff で二次式へ
  -- そこから ring で平方完成へ
  have := (AgNorm_eq_zero_iff (a := a) (b := b))
  -- 右辺を変形
  constructor
  · intro h
    have h' : a^2 + a*b - (b^2)/4 = 0 := (this.mp h)
    -- ring で整形
    -- nlinarith が通りやすい
    nlinarith
  · intro h
    -- 逆向きも nlinarith で行けることが多い
    have h_eq : a^2 + a*b - (b^2)/4 = 0 := by nlinarith
    exact this.mpr h_eq

-- ============================================================================

/-- Summary of core results in the silver ratio unit world -/
theorem SilverRatioUnit_core_summary :
    Gap uAg = (1/4 : ℝ) ∧ ΔAg = (1/4 : ℝ) ∧ (∀ a b, AgNorm a b = a^2 + a*b - (b^2)/4) := by
  constructor
  · exact Gap_uAg
  constructor
  · exact ΔAg_eq
  · intro a b
    simp [AgNorm_eq]

/-- mixTerm appears as the extra term in the uAg-component of Ag multiplication. -/
lemma Ag_mul_mixTerm (a b c d : ℝ) :
    Ag a b * Ag c d = Ag (a*c + (mixTerm b d)/4) (a*d + b*c + mixTerm b d) := by
  -- mixTerm = b*d を畳むだけ
  simpa [mixTerm] using (Ag_mul (a := a) (b := b) (c := c) (d := d))

/-- e/4 = e * Gap(uAg), where e := exp 1. -/
theorem e_div_four_eq_e_mul_Gap_uAg :
    (Real.exp 1) / 4 = (Real.exp 1) * Gap uAg := by
  -- Gap uAg = 1/4 を使うだけ
  rw [Gap_uAg]
  ring

-- ----------------------------------------------------------------------------

/-- AgNorm is multiplicative (pair form). -/
theorem AgNorm_mul (a b c d : ℝ) :
    AgNorm (a*c + (b*d)/4) (a*d + b*c + b*d)
      = (AgNorm a b) * (AgNorm c d) := by
  -- 左辺は Ag_mul で作られる積の係数
  -- 右辺は定義どおり
  -- ここは最終的に ring_nf / nlinarith で倒せるはず
  simp [AgNorm_eq]  -- ノルムの閉形式へ落とす
  ring

-- ----------------------------------------------------------------------------

/-
New theorems for SilverRatioUnit: Unique representation in Q(√2)

Key insight: The naive statement "∃! (p : ℝ × ℝ), Ag p.1 p.2 = x" is NOT true
for all x ∈ ℝ. However, it IS true when x ∈ ℚ(√2) and (a,b) ∈ ℚ².

This is because {1, √2} is ℚ-linearly independent (from √2's irrationality),
which makes uAg = (1 + √2)/2 generate a unique representation system.
-/

/-- Linear independence of {1, √2} over ℚ.
   Key lemma: If a + b*√2 = c + d*√2 where a,b,c,d ∈ ℚ, then a=c and b=d.
   This follows from √2 being irrational.
-/
lemma sqrt2_Q_lin_indep (a b c d : ℚ) :
    (a : ℝ) + (b : ℝ) * sqrt2 = (c : ℝ) + (d : ℝ) * sqrt2 → a = c ∧ b = d := by
  intro h
  by_cases hbd : b = d
  · have : (a : ℝ) = (c : ℝ) := by
      rw [hbd] at h
      have : (a : ℝ) + (d : ℝ) * sqrt2 = (c : ℝ) + (d : ℝ) * sqrt2 := h
      linarith
    exact ⟨Rat.cast_injective this, hbd⟩
  · have hbd_ne : ((b - d : ℚ) : ℝ) ≠ 0 := by
      intro heq
      have hq : b - d = 0 := by
        apply Rat.cast_injective (α := ℝ)
        simpa using heq
      have : b = d := by
        linarith
      exact hbd this
    have h_diff : ((a - c : ℚ) : ℝ) + ((b - d : ℚ) : ℝ) * sqrt2 = 0 := by
      have : (a : ℝ) + (b : ℝ) * sqrt2 = (c : ℝ) + (d : ℝ) * sqrt2 := h
      have : (a : ℝ) - (c : ℝ) + ((b : ℝ) - (d : ℝ)) * sqrt2
           = (a : ℝ) + (b : ℝ) * sqrt2 - ((c : ℝ) + (d : ℝ) * sqrt2) := by ring
      calc ((a - c : ℚ) : ℝ) + ((b - d : ℚ) : ℝ) * sqrt2
           = (a : ℝ) - (c : ℝ) + ((b : ℝ) - (d : ℝ)) * sqrt2 := by push_cast; ring
         _ = (a : ℝ) + (b : ℝ) * sqrt2 - ((c : ℝ) + (d : ℝ) * sqrt2) := this
         _ = 0 := by rw [h]; ring
    have h_sqrt2 : sqrt2 = -((a - c : ℚ) : ℝ) / ((b - d : ℚ) : ℝ) := by
      field_simp [hbd_ne]
      have : ((a - c : ℚ) : ℝ) + ((b - d : ℚ) : ℝ) * sqrt2 = 0 := h_diff
      nlinarith [this]
    have : sqrt2 ∈ Set.range ((↑) : ℚ → ℝ) := by
      use (-(a - c) : ℚ) / (b - d)
      simp only [Rat.cast_div, Rat.cast_neg]
      exact h_sqrt2.symm
    exact absurd this (sqrt2_irrational)

/-- Definition: Elements of ℚ(√2) expressed via uAg basis.
   InQAdjSqrt2Ag x means x = a + b*uAg for some rational a, b.
   Since uAg = (1 + √2)/2, this is equivalent to x ∈ ℚ(√2).
-/
def InQAdjSqrt2Ag (x : ℝ) : Prop := ∃ a b : ℚ, (a : ℝ) + (b : ℝ) * uAg = x

/-- THEOREM: In ℚ(√2), the representation with basis {1, uAg} is UNIQUE.
   This is the correct and precise form of the "unique representation" result,
   with the restricted domain x ∈ ℚ(√2) and codomain (a,b) ∈ ℚ × ℚ.
-/
theorem Ag_rep_unique_in_Q_ext (x : ℝ) (hx : InQAdjSqrt2Ag x) :
    ∃! (p : ℚ × ℚ), (p.1 : ℝ) + (p.2 : ℝ) * uAg = x := by
  obtain ⟨a₀, b₀, h₀⟩ := hx
  use (a₀, b₀)
  refine ⟨h₀, fun ⟨a, b⟩ hab ↦ ?_⟩
  simp only [Prod.mk.injEq]
  -- Both (a, b) and (a₀, b₀) satisfy the equation
  have h_diff : (a : ℝ) + (b : ℝ) * uAg = (a₀ : ℝ) + (b₀ : ℝ) * uAg := by rw [hab, h₀]
  rw [uAg_eq] at h_diff
  -- Rewrite in standard form: (2a + b) + b*√2 = (2a₀ + b₀) + b₀*√2
  have h_canonical : ((2 * a + b : ℚ) : ℝ) + ((b : ℚ) : ℝ) * sqrt2
                   = ((2 * a₀ + b₀ : ℚ) : ℝ) + ((b₀ : ℚ) : ℝ) * sqrt2 := by
    have h_eq : (a : ℝ) + (b : ℝ) * ((1 + sqrt2) / 2)
              = (a₀ : ℝ) + (b₀ : ℝ) * ((1 + sqrt2) / 2) := h_diff
    field_simp at h_eq
    push_cast at h_eq ⊢
    linarith [h_eq]
  -- Apply Q-linear independence
  have ⟨heq1, heq2⟩ := sqrt2_Q_lin_indep (2*a + b) b (2*a₀ + b₀) b₀ h_canonical
  constructor
  · have h2a : (2 : ℚ) * (a - a₀) = 0 := by linarith [heq1]
    have : (a : ℚ) - a₀ = 0 := by linarith [h2a]
    linarith
  · exact heq2


end -- noncomputable section

end DkMath.SilverRatio.Unit
