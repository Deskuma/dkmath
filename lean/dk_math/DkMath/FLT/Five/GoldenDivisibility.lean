/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.GoldenOrder

#print "file: DkMath.FLT.Five.GoldenDivisibility"

namespace DkMath.FLT.Five

/-- Explicit golden divisibility, definitionally compatible with ring divisibility. -/
def GoldenDivides (d x : GoldenInt) : Prop :=
  ∃ q : GoldenInt, x = goldenMul d q

theorem goldenDivides_iff_dvd {d x : GoldenInt} : GoldenDivides d x ↔ d ∣ x := by
  constructor <;> rintro ⟨q, hq⟩
  · exact ⟨q, by simpa using hq⟩
  · exact ⟨q, by simpa using hq⟩

theorem goldenDivides_refl (x : GoldenInt) : GoldenDivides x x := by
  rw [goldenDivides_iff_dvd]

theorem goldenDivides_trans {d x y : GoldenInt}
    (hdx : GoldenDivides d x) (hxy : GoldenDivides x y) :
    GoldenDivides d y := by
  rw [goldenDivides_iff_dvd] at hdx hxy ⊢
  exact dvd_trans hdx hxy

theorem goldenDivides_sub {d x y : GoldenInt}
    (hdx : GoldenDivides d x) (hdy : GoldenDivides d y) :
    GoldenDivides d (x - y) := by
  rw [goldenDivides_iff_dvd] at hdx hdy ⊢
  exact dvd_sub hdx hdy

/-- Norm carries golden divisibility to integer divisibility. -/
theorem goldenNorm_dvd_of_goldenDivides {d x : GoldenInt}
    (h : GoldenDivides d x) : goldenNorm d ∣ goldenNorm x := by
  rcases h with ⟨q, rfl⟩
  rw [goldenNorm_mul]
  exact dvd_mul_right _ _

theorem goldenConj_add (x y : GoldenInt) :
    goldenConj (x + y) = goldenConj x + goldenConj y := by
  ext <;> simp [goldenConj] <;> ring

theorem goldenConj_neg (x : GoldenInt) :
    goldenConj (-x) = -goldenConj x := by
  ext <;> simp [goldenConj, add_comm]

theorem goldenConj_sub (x y : GoldenInt) :
    goldenConj (x - y) = goldenConj x - goldenConj y := by
  calc
    goldenConj (x - y) = goldenConj (x + -y) := by rfl
    _ = goldenConj x + goldenConj (-y) := goldenConj_add _ _
    _ = goldenConj x + -goldenConj y := by rw [goldenConj_neg]
    _ = goldenConj x - goldenConj y := by rw [sub_eq_add_neg]

theorem goldenConj_pow (x : GoldenInt) (n : ℕ) :
    goldenConj (x ^ n) = goldenConj x ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ]
      change goldenConj (goldenMul (x ^ n) x) = _
      rw [goldenConj_mul, ih]
      rw [pow_succ, ← golden_mul_eq]

theorem goldenNorm_pow (x : GoldenInt) (n : ℕ) :
    goldenNorm (x ^ n) = goldenNorm x ^ n := by
  induction n with
  | zero => norm_num [goldenNorm]
  | succ n ih =>
      rw [pow_succ]
      change goldenNorm (goldenMul (x ^ n) x) = _
      rw [goldenNorm_mul, ih, pow_succ]

/-- A two-sided unit for the explicit golden-order multiplication API. -/
def GoldenUnit (epsilon : GoldenInt) : Prop :=
  ∃ eta : GoldenInt,
    goldenMul epsilon eta = goldenOne ∧ goldenMul eta epsilon = goldenOne

theorem goldenUnit_of_norm_eq_one {x : GoldenInt} (h : goldenNorm x = 1) :
    GoldenUnit x := by
  refine ⟨goldenConj x, ?_, ?_⟩
  · simpa [h, goldenOfInt, goldenOne] using golden_mul_conj x
  · have hc : goldenMul (goldenConj x) x =
        goldenMul x (goldenConj x) := by
      change goldenConj x * x = x * goldenConj x
      exact mul_comm _ _
    rw [hc]
    simpa [h, goldenOfInt, goldenOne] using golden_mul_conj x

theorem goldenUnit_of_norm_eq_neg_one {x : GoldenInt} (h : goldenNorm x = -1) :
    GoldenUnit x := by
  refine ⟨-goldenConj x, ?_, ?_⟩
  · have hm : goldenMul x (-goldenConj x) =
        -(goldenMul x (goldenConj x)) := by
      change x * (-goldenConj x) = -(x * goldenConj x)
      exact mul_neg _ _
    rw [hm, golden_mul_conj, h]
    rfl
  · have hc : goldenMul (-goldenConj x) x =
        goldenMul x (-goldenConj x) := by
      change (-goldenConj x) * x = x * (-goldenConj x)
      exact mul_comm _ _
    rw [hc]
    have hm : goldenMul x (-goldenConj x) =
        -(goldenMul x (goldenConj x)) := by
      change x * (-goldenConj x) = -(x * goldenConj x)
      exact mul_neg _ _
    rw [hm, golden_mul_conj, h]
    rfl

theorem goldenUnit_of_norm_eq_one_or_neg_one {x : GoldenInt}
    (h : goldenNorm x = 1 ∨ goldenNorm x = -1) : GoldenUnit x :=
  h.elim goldenUnit_of_norm_eq_one goldenUnit_of_norm_eq_neg_one

theorem goldenNorm_eq_one_or_neg_one_of_unit {x : GoldenInt}
    (h : GoldenUnit x) : goldenNorm x = 1 ∨ goldenNorm x = -1 := by
  rcases h with ⟨y, hxy, _⟩
  have hn : goldenNorm x * goldenNorm y = 1 := by
    rw [← goldenNorm_mul, hxy]
    norm_num [goldenNorm, goldenOne]
  exact Int.eq_one_or_neg_one_of_mul_eq_one hn

/-- Relatively prime means that every common golden divisor is a unit. -/
def GoldenRelPrime (x y : GoldenInt) : Prop :=
  ∀ d : GoldenInt, GoldenDivides d x → GoldenDivides d y → GoldenUnit d

end DkMath.FLT.Five
