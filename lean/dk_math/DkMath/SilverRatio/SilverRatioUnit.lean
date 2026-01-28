/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- cid: 6979430e-4324-83a6-b491-838e096d3d58

import Mathlib
import DkMath.SilverRatio.Sqrt2Lemmas

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
open DkMath.SilverRatio.Sqrt2

noncomputable section

#check sqrt2  -- Real.sqrt 2
#check sigma  -- 1 + sqrt2
#check sqrt2_sq  -- sqrt2 ^ 2 = 2
#check sqrt2_pos  -- 0 < sqrt2
#check sqrt2_ne_zero  -- sqrt2 ≠ 0

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

/-- Encode Ag-elements as pairs (a,b). -/
def AgEncode (_x : ℝ) : ℝ × ℝ := (0, 0)  -- placeholder (optional)

/- Meta-note (D., 2026/01/28 10:58)
1) AgEncode を “ダミー” から卒業させる（本命：係数抽出）

いま AgEncode が placeholder じゃが、これをちゃんと定義できると、構造が一気に締まる。
そのために必要なのは「{1,uAg} が Q-線形独立」みたいな議論……ではなく、
実は 2 の無理性を使って 実数係数でも一意性を取れる。

最短の実用路線はこう：

Ag の世界を「R×R を表現する 構文」として扱い

逆方向 encode は “定義” せず、必要なときだけ ∃!（存在一意）で取り出す

つまり：
-/
theorem Ag_rep_exists_unique (x : ℝ) :
    ∃! (p : ℝ × ℝ), Ag p.1 p.2 = x := by
  use (x, 0)
  constructor
  · simp [Ag]
  · intro ⟨a, b⟩ hab
    simp only [Ag] at hab ⊢
    -- hab : a + b * uAg = x
    -- Goal : a = x ∧ b = 0

    -- Key insight: √2 is irrational, so if b ≠ 0, we can derive a contradiction
    by_cases hb : b = 0
    · -- Case b = 0
      simp [hb] at hab
      exact ⟨hab, hb⟩
    · -- Case b ≠ 0, we show a contradiction
      -- From a + b * (1 + √2) / 2 = x:
      -- 2*a + b + b*√2 = 2*x
      -- b*√2 = 2*x - 2*a - b
      -- √2 = (2*x - 2*a - b) / b

      have h_eq : b * sqrt2 = 2*x - 2*a - b := by
        have : a + b * (1 + sqrt2) / 2 = x := hab
        nlinarith [mul_comm b sqrt2]

      -- Divide both sides by b
      have h_sqrt2 : sqrt2 = (2*x - 2*a - b) / b := by
        field_simp [hb]
        exact h_eq

      -- Now we show that the right side being rational contradicts √2 being irrational
      -- Rearrange: b * √2 = 2*x - 2*a - b
      -- If we think of this as a linear combination of 1 and √2:
      -- (2*a + b - 2*x) + b*√2 = 0

      -- The irrationality of √2 means: ∀ q : ℚ, sqrt2 ≠ ↑q
      have h_irrat : Irrational sqrt2 := sqrt2_irrational

      -- The RHS (2*x - 2*a - b) / b can be thought of as a specific value
      -- But more directly: if b*√2 = c for some c, then either b = 0 or √2 = c/b ∈ ℝ
      -- Since √2 is irrational (not in ℚ), we'd need b = 0

      -- Use a different approach: appeal to linear independence of {1, √2}
      -- For ℚ-vector space structure
      have h_indep : ∀ q : ℚ, sqrt2 ≠ (q : ℝ) := fun q => h_irrat q

      -- From hab, we can write:
      -- a + b/2 + (b/2)*√2 = x
      -- (a + b/2 - x) + (b/2)*√2 = 0

      have h_combo : (a + b/2 - x) + (b/2)*sqrt2 = 0 := by
        have : a + b * (1 + sqrt2) / 2 = x := hab
        nlinarith [mul_comm b sqrt2]

      -- Now, express this as: (a + b/2 - x) = -(b/2)*√2
      -- If b/2 ≠ 0, then √2 = -(a + b/2 - x) / (b/2) = (x - a - b/2) / (b/2)
      -- which would be a rational number (contradicting irrationality of √2)

      have hb_half : b/2 ≠ 0 := by nlinarith [hb]

      have h_sqrt2_alt : sqrt2 = (x - a - b/2) / (b/2) := by
        field_simp [hb_half]
        nlinarith [h_combo]

      -- Now we have sqrt2 equal to (x - a - b/2) / (b/2), which is a real number
      -- For a contradiction, we'd need to show this is rational
      -- Actually, a more elegant approach: use the linear independence directly

      -- Let's use Irrational more carefully
      -- Irrational x means: ∀ q : ℚ, ↑q ≠ x
      -- So sqrt2 ≠ ↑q for any rational q

      -- From h_combo: (a + b/2 - x) + (b/2)*sqrt2 = 0
      -- Rearrange: (a + b/2 - x) = -(b/2)*sqrt2

      -- If we work in ℚ[√2], {1, √2} is a basis.
      -- This means if c + d*√2 = 0 where c, d ∈ ℚ, then c = d = 0.

      -- But here, c and d may not be rational.
      -- However, we can derive a contradiction using irrationality:

      -- From h_combo: (a + b/2 - x) = -(b/2)*sqrt2
      -- Since b ≠ 0, we have b/2 ≠ 0
      -- So sqrt2 = -(a + b/2 - x) / (b/2)

      -- The value (a + b/2 - x) / (b/2) is some real number r
      -- So sqrt2 = -r
      -- This contradicts sqrt2 > 0 (unless we're more careful)

      -- Let me reconsider: Actually the key is that no non-zero real multiple
      -- of √2 can equal a real number in a non-trivial way that we can exploit

      -- More direct proof: using the definition of Irrational
      -- and properties specific to √2

      exfalso  -- derive False

      -- From (a + b/2 - x) + (b/2)*sqrt2 = 0 and b ≠ 0:
      -- We have: -(a + b/2 - x) / (b/2) = sqrt2

      -- Now use a key algebraic fact: if r + s*√2 = 0 where r, s ∈ ℝ,
      -- and √2 ∉ ℚ, then we must have s = 0 and r = 0
      -- (This follows from the linear independence of {1, √2} over ℚ)

      -- To use irrationality properly, we note:
      -- sqrt2_irrational : Irrational sqrt2
      -- means: ∀ (q : ℚ), (q : ℝ) ≠ sqrt2

      -- From h_combo we have (a + b/2 - x) = -(b/2)*sqrt2
      -- Taking absolute values: |a + b/2 - x| = |b/2|*sqrt2

      -- If a + b/2 - x ≠ 0, then sqrt2 = |a + b/2 - x| / |b/2|
      -- which is a positive real number

      -- Now the key: can |a + b/2 - x| / |b/2| be rational?
      -- If both a, x are "generic" reals, this could be any real
      -- So this approach doesn't immediately give contradiction

      -- Let me reconsider the structure. We need a finer argument.
      -- The fact is: {1, √2} are ℚ-linearly independent
      -- This means if c₀·1 + c₁·√2 = 0 with c₀, c₁ ∈ ℚ, then c₀ = c₁ = 0

      -- From h_combo: (a + b/2 - x) + (b/2)*√2 = 0
      -- This is in the form c₀ + c₁*√2 = 0 but c₀, c₁ are not necessarily in ℚ

      -- However, we can use this fact: suppose b ≠ 0
      -- Then b/2 ≠ 0, so sqrt2 = (x - a - b/2) / (b/2)
      -- Let's call this value q := (x - a - b/2) / (b/2)
      -- Then sqrt2 = q

      -- Now, is q necessarily irrational? Not obviously, unless we constrain a, x

      -- Hmm, I think the issue is that the statement ∃! (p : ℝ × ℝ), Ag p.1 p.2 = x
      -- should NOT require a, b to satisfy any constraints
      -- In that case, we NEED to show that for ANY choice of different a,b,
      -- if both satisfy Ag a b = x, then a = a' and b = b'

      -- The right argument is:
      -- If Ag a b = x and Ag a' b' = x, then Ag a b = Ag a' b'
      -- => a + b*uAg = a' + b'*uAg
      -- => (a - a') + (b - b')*uAg = 0
      -- => (a - a') + (b - b')*(1 + √2)/2 = 0
      -- => 2(a - a') + (b - b') + (b - b')*√2 = 0

      -- Now, if we write this as C + D*√2 = 0 where:
      -- C = 2(a - a') + (b - b')
      -- D = b - b'

      -- The irrationality of √2 implies:
      -- If C + D*√2 = 0, then D = 0 (since √2 ∉ ℚ wouldn't directly apply)

      -- Actually, the precise lemma we need is:
      -- ∀ r s : ℝ, (r + s*√2 = 0 ∧ s ≠ 0) ⟹ False
      -- because otherwise √2 would be rational

      have key : ∀ r s : ℝ, (r + s * sqrt2 = 0 ∧ s ≠ 0) ⟹ False := by
        intro r s ⟨h_sum, hs_ne⟩
        -- From r + s*√2 = 0, we get √2 = -r/s
        have : sqrt2 = -r / s := by field_simp [hs_ne]; linarith [h_sum]
        -- Now -r/s is some real number; we'd need it to be irrational
        -- But wait, that's not automatic from h_irrat
        -- Actually, h_irrat says √2 ∉ ℚ, not that it's algebraically irrational

        -- Let me think differently: if √2 = -r/s, then
        -- √2 would be the quotient of two reals, which is just another real
        -- This doesn't give us a contradiction directly

        -- UNLESS we use the fact that √2 satisfies x² = 2 in a special way
        -- Specifically: √2 is the unique positive solution to x² = 2
        -- And any algebraic equation satisfied by √2 over ℚ is such that
        -- √2 ∉ ℚ

        -- The proper way: use that √2 is irrational over ℚ[√2]
        -- i.e., it doesn't lie in ℚ

        -- From √2 = -r/s, either:
        -- (1) Both r and s are 0 (contradiction with hs_ne)
        -- (2) Or √2 = -r/s is a well-defined real that equals √2

        -- For a contradiction from Irrational sqrt2, we'd need
        -- -r/s ∈ ℚ, which we can't assume

        sorry

      -- Okay, I need to rethink. Let me look at the actual definition of Irrational
      -- and what tools Mathlib provides

      sorry


-- まずは明示的な相互変換だけ置くのが実用的
def AgOfPair (p : ℝ × ℝ) : ℝ := Ag p.1 p.2

lemma AgOfPair_mul (p q : ℝ × ℝ) :
    AgOfPair (AgMulPair p q) = AgOfPair p * AgOfPair q := by
  -- p=(a,b), q=(c,d) に展開して Ag_mul を使うのが自然
  rcases p with ⟨a,b⟩
  rcases q with ⟨c,d⟩
  -- Ag_mul を使えるなら最短
  simpa [AgOfPair, AgMulPair] using (Ag_mul (a := a) (b := b) (c := c) (d := d)).symm

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


end -- noncomputable section
end SilverRatioUnit
end DkMath
