/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.SignedGoldenUnitClasses

/-!
# Elementary classification of units in the golden order

Multiplication by `phi` or its integral inverse strictly decreases a coordinate
measure until a base unit is reached. Reversing that descent expresses every
unit as a signed power of `phi`, hence as `phi^i * delta^5` for `i : Fin 5`.
This proves existence of a fifth-power class representative; no uniqueness
claim is needed downstream.
-/

#print "file: DkMath.FLT.Five.GoldenUnitClassification"

namespace DkMath.FLT.Five

/-- The integral inverse `phi - 1` of `phi` in the coordinate model. -/
def goldenPhiInv : GoldenInt := ⟨-1, 1⟩

theorem golden_phi_mul_inv :
    goldenMul goldenPhi goldenPhiInv = goldenOne := by decide

theorem golden_inv_mul_phi :
    goldenMul goldenPhiInv goldenPhi = goldenOne := by decide

theorem goldenUnit_phiInv : GoldenUnit goldenPhiInv := by
  exact ⟨goldenPhi, golden_inv_mul_phi, golden_phi_mul_inv⟩

theorem golden_mul_phi_coords (x : GoldenInt) :
    goldenMul x goldenPhi = ⟨x.snd, x.fst + x.snd⟩ := by
  ext <;> simp [goldenMul, goldenPhi]

theorem golden_mul_phiInv_coords (x : GoldenInt) :
    goldenMul x goldenPhiInv = ⟨x.snd - x.fst, x.fst⟩ := by
  ext <;> simp [goldenMul, goldenPhiInv]
  all_goals ring

/-- Coordinate size used for the elementary unit descent. -/
def goldenUnitMeasure (x : GoldenInt) : ℕ :=
  x.fst.natAbs + x.snd.natAbs

theorem goldenUnitMeasure_pos {x : GoldenInt} (hx : GoldenUnit x) :
    0 < goldenUnitMeasure x := by
  have hn := goldenNorm_eq_one_or_neg_one_of_unit hx
  simp only [goldenUnitMeasure]
  by_contra h
  have hz : x.fst.natAbs + x.snd.natAbs = 0 := Nat.eq_zero_of_not_pos h
  have haf : x.fst.natAbs = 0 := by omega
  have hbf : x.snd.natAbs = 0 := by omega
  have ha : x.fst = 0 := Int.natAbs_eq_zero.mp haf
  have hb : x.snd = 0 := Int.natAbs_eq_zero.mp hbf
  rcases hn with hn | hn <;> simp [goldenNorm, ha, hb] at hn

theorem goldenUnit_measure_one_cases {x : GoldenInt} (_hx : GoldenUnit x)
    (hm : goldenUnitMeasure x = 1) :
    x = goldenOne ∨ x = -goldenOne ∨
      x = goldenPhi ∨ x = -goldenPhi := by
  have hsum : x.fst.natAbs + x.snd.natAbs = 1 := hm
  have hcases :
      (x.fst.natAbs = 0 ∧ x.snd.natAbs = 1) ∨
      (x.fst.natAbs = 1 ∧ x.snd.natAbs = 0) := by omega
  rcases hcases with h | h
  · have ha0 : x.fst = 0 := Int.natAbs_eq_zero.mp h.1
    have hb : x.snd = 1 ∨ x.snd = -1 := by
      simpa using (Int.natAbs_eq_iff.mp h.2)
    rcases hb with hb | hb
    · right; right; left; ext <;> simp [goldenPhi, ha0, hb]
    · right; right; right; ext <;> simp [goldenPhi, ha0, hb]
  · have ha : x.fst = 1 ∨ x.fst = -1 := by
      simpa using (Int.natAbs_eq_iff.mp h.1)
    have hb0 : x.snd = 0 := Int.natAbs_eq_zero.mp h.2
    rcases ha with ha | ha
    · left; ext <;> simp [goldenOne, ha, hb0]
    · right; left; ext <;> simp [goldenOne, ha, hb0]

private theorem unit_order_pos_pos {a b : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hn : a ^ 2 + a * b - b ^ 2 = 1 ∨
      a ^ 2 + a * b - b ^ 2 = -1) : a ≤ b := by
  by_contra h
  have hab : b + 1 ≤ a := by omega
  rcases hn with hn | hn <;> nlinarith [sq_nonneg (a - b)]

private theorem unit_order_pos_neg {a b : ℤ}
    (ha : 0 < a) (hb : b < 0)
    (hn : a ^ 2 + a * b - b ^ 2 = 1 ∨
      a ^ 2 + a * b - b ^ 2 = -1) : -b ≤ a := by
  by_contra h
  have hab : a + 1 ≤ -b := by omega
  rcases hn with hn | hn <;> nlinarith [sq_nonneg (a + b)]

/-- Every non-base golden unit can be shortened by one multiplication by `phi`
or its integral inverse. -/
theorem goldenUnit_descent {x : GoldenInt} (hx : GoldenUnit x)
    (hlarge : 1 < goldenUnitMeasure x) :
    ∃ y : GoldenInt,
      GoldenUnit y ∧
      goldenUnitMeasure y < goldenUnitMeasure x ∧
      (x = goldenMul y goldenPhi ∨
        x = goldenMul y goldenPhiInv) := by
  have hn : x.fst ^ 2 + x.fst * x.snd - x.snd ^ 2 = 1 ∨
      x.fst ^ 2 + x.fst * x.snd - x.snd ^ 2 = -1 := by
    simpa [goldenNorm] using goldenNorm_eq_one_or_neg_one_of_unit hx
  have ha0 : x.fst ≠ 0 := by
    intro ha
    have hb2 : x.snd ^ 2 = 1 := by
      rcases hn with hn | hn
      · rw [ha] at hn
        norm_num at hn
        nlinarith [sq_nonneg x.snd]
      · rw [ha] at hn
        norm_num at hn ⊢
        exact hn
    have hb : x.snd = 1 ∨ x.snd = -1 := sq_eq_one_iff.mp hb2
    rcases hb with hb | hb <;> simp [goldenUnitMeasure, ha, hb] at hlarge
  have hb0 : x.snd ≠ 0 := by
    intro hb
    have ha2 : x.fst ^ 2 = 1 := by
      rcases hn with hn | hn
      · simpa [hb] using hn
      · simp [hb] at hn
        nlinarith [sq_nonneg x.fst]
    have ha : x.fst = 1 ∨ x.fst = -1 := sq_eq_one_iff.mp ha2
    rcases ha with ha | ha <;> simp [goldenUnitMeasure, ha, hb] at hlarge
  rcases lt_or_gt_of_ne ha0 with ha | ha <;>
    rcases lt_or_gt_of_ne hb0 with hb | hb
  · -- both coordinates are negative
    have hord : -x.fst ≤ -x.snd := by
      apply unit_order_pos_pos (a := -x.fst) (b := -x.snd) <;> try omega
      simpa only [neg_sq, neg_mul_neg] using hn
    let y := goldenMul x goldenPhiInv
    refine ⟨y, goldenUnit_mul hx goldenUnit_phiInv, ?_, ?_⟩
    · dsimp [y]
      change goldenUnitMeasure (goldenMul x goldenPhiInv) < goldenUnitMeasure x
      rw [golden_mul_phiInv_coords]
      simp only [goldenUnitMeasure]
      have hba : x.snd - x.fst ≤ 0 := by omega
      have h1 := Int.natAbs_of_nonneg (show 0 ≤ x.fst - x.snd by omega)
      rw [show (x.snd - x.fst).natAbs = (x.fst - x.snd).natAbs by
        rw [show x.snd - x.fst = -(x.fst - x.snd) by ring, Int.natAbs_neg]]
      have h2 := Int.natAbs_of_nonneg (show 0 ≤ -x.fst by omega)
      rw [show x.fst.natAbs = (-x.fst).natAbs by rw [Int.natAbs_neg]]
      omega
    · left
      dsimp [y]
      rw [mul_assoc, show goldenPhiInv * goldenPhi = 1 by exact golden_inv_mul_phi]
      simp
  · -- negative, positive
    have hord : x.snd ≤ -x.fst := by
      have h := unit_order_pos_neg (a := -x.fst) (b := -x.snd)
        (by omega) (by omega) (by simpa only [neg_sq, neg_mul_neg] using hn)
      omega
    let y := goldenMul x goldenPhi
    refine ⟨y, goldenUnit_mul hx goldenUnit_phi, ?_, ?_⟩
    · dsimp [y]
      change goldenUnitMeasure (goldenMul x goldenPhi) < goldenUnitMeasure x
      rw [golden_mul_phi_coords]
      simp only [goldenUnitMeasure]
      have h1 := Int.natAbs_of_nonneg hb.le
      have h2 := Int.natAbs_of_nonneg (show 0 ≤ -(x.fst + x.snd) by omega)
      rw [show (x.fst + x.snd).natAbs = (-(x.fst + x.snd)).natAbs by
        rw [Int.natAbs_neg]]
      have h3 := Int.natAbs_of_nonneg (show 0 ≤ -x.fst by omega)
      rw [show x.fst.natAbs = (-x.fst).natAbs by rw [Int.natAbs_neg]]
      omega
    · right
      dsimp [y]
      rw [mul_assoc, show goldenPhi * goldenPhiInv = 1 by exact golden_phi_mul_inv]
      simp
  · -- positive, negative
    have hord : -x.snd ≤ x.fst := unit_order_pos_neg ha hb hn
    let y := goldenMul x goldenPhi
    refine ⟨y, goldenUnit_mul hx goldenUnit_phi, ?_, ?_⟩
    · dsimp [y]
      change goldenUnitMeasure (goldenMul x goldenPhi) < goldenUnitMeasure x
      rw [golden_mul_phi_coords]
      simp only [goldenUnitMeasure]
      have h1 := Int.natAbs_of_nonneg (show 0 ≤ -x.snd by omega)
      rw [show x.snd.natAbs = (-x.snd).natAbs by rw [Int.natAbs_neg]]
      have h2 := Int.natAbs_of_nonneg (show 0 ≤ x.fst + x.snd by omega)
      have h3 := Int.natAbs_of_nonneg ha.le
      omega
    · right
      dsimp [y]
      rw [mul_assoc, show goldenPhi * goldenPhiInv = 1 by exact golden_phi_mul_inv]
      simp
  · -- both coordinates are positive
    have hord : x.fst ≤ x.snd := unit_order_pos_pos ha hb hn
    let y := goldenMul x goldenPhiInv
    refine ⟨y, goldenUnit_mul hx goldenUnit_phiInv, ?_, ?_⟩
    · dsimp [y]
      change goldenUnitMeasure (goldenMul x goldenPhiInv) < goldenUnitMeasure x
      rw [golden_mul_phiInv_coords]
      simp only [goldenUnitMeasure]
      have h1 := Int.natAbs_of_nonneg (sub_nonneg.mpr hord)
      have h2 := Int.natAbs_of_nonneg ha.le
      have h3 := Int.natAbs_of_nonneg hb.le
      omega
    · left
      dsimp [y]
      rw [mul_assoc, show goldenPhiInv * goldenPhi = 1 by exact golden_inv_mul_phi]
      simp

/-- Existence of `i < 5` and `delta` with `x = phi^i * delta^5`. -/
def GoldenUnitFifthClass (x : GoldenInt) : Prop :=
  ∃ i : Fin 5, ∃ delta : GoldenInt,
    x = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)

private theorem golden_phi_four_mul_inv_five :
    goldenPhi ^ 4 * goldenPhiInv ^ 5 = goldenPhiInv := by
  decide

private theorem golden_sector_zero_mul_phiInv (delta : GoldenInt) :
    (goldenPhi ^ 0 * delta ^ 5) * goldenPhiInv =
      goldenPhi ^ 4 * (goldenPhiInv * delta) ^ 5 := by
  rw [mul_pow]
  calc
    (goldenPhi ^ 0 * delta ^ 5) * goldenPhiInv =
        goldenPhiInv * delta ^ 5 := by ring
    _ = (goldenPhi ^ 4 * goldenPhiInv ^ 5) * delta ^ 5 := by
      rw [golden_phi_four_mul_inv_five]
    _ = goldenPhi ^ 4 * (goldenPhiInv ^ 5 * delta ^ 5) := by ring

private theorem golden_sector_succ_mul_phiInv (delta : GoldenInt) (n : ℕ) :
    (goldenPhi ^ (n + 1) * delta ^ 5) * goldenPhiInv =
      goldenPhi ^ n * delta ^ 5 := by
  calc
    (goldenPhi ^ (n + 1) * delta ^ 5) * goldenPhiInv =
        goldenPhi ^ n * delta ^ 5 * (goldenPhi * goldenPhiInv) := by
      rw [pow_succ]
      ring
    _ = goldenPhi ^ n * delta ^ 5 := by
      rw [show goldenPhi * goldenPhiInv = 1 by exact golden_phi_mul_inv, mul_one]

theorem goldenUnitFifthClass_mul_phi {x : GoldenInt}
    (hx : GoldenUnitFifthClass x) :
    GoldenUnitFifthClass (goldenMul x goldenPhi) := by
  rcases hx with ⟨i, delta, hx⟩
  fin_cases i
  · refine ⟨⟨1, by decide⟩, delta, ?_⟩
    rw [hx]
    simp only [golden_mul_eq, golden_pow_eq]
    ring
  · refine ⟨⟨2, by decide⟩, delta, ?_⟩
    rw [hx]
    simp only [golden_mul_eq, golden_pow_eq]
    ring
  · refine ⟨⟨3, by decide⟩, delta, ?_⟩
    rw [hx]
    simp only [golden_mul_eq, golden_pow_eq]
    ring
  · refine ⟨⟨4, by decide⟩, delta, ?_⟩
    rw [hx]
    simp only [golden_mul_eq, golden_pow_eq]
    ring
  · refine ⟨⟨0, by decide⟩, goldenMul goldenPhi delta, ?_⟩
    rw [hx]
    simp only [golden_mul_eq, golden_pow_eq]
    ring

theorem goldenUnitFifthClass_mul_phiInv {x : GoldenInt}
    (hx : GoldenUnitFifthClass x) :
    GoldenUnitFifthClass (goldenMul x goldenPhiInv) := by
  rcases hx with ⟨i, delta, hx⟩
  fin_cases i
  · refine ⟨⟨4, by decide⟩, goldenMul goldenPhiInv delta, ?_⟩
    rw [hx]
    simpa only [golden_mul_eq, golden_pow_eq] using
      golden_sector_zero_mul_phiInv delta
  · refine ⟨⟨0, by decide⟩, delta, ?_⟩
    rw [hx]
    simpa only [golden_mul_eq, golden_pow_eq] using
      golden_sector_succ_mul_phiInv delta 0
  · refine ⟨⟨1, by decide⟩, delta, ?_⟩
    rw [hx]
    simpa only [golden_mul_eq, golden_pow_eq] using
      golden_sector_succ_mul_phiInv delta 1
  · refine ⟨⟨2, by decide⟩, delta, ?_⟩
    rw [hx]
    simpa only [golden_mul_eq, golden_pow_eq] using
      golden_sector_succ_mul_phiInv delta 2
  · refine ⟨⟨3, by decide⟩, delta, ?_⟩
    rw [hx]
    simpa only [golden_mul_eq, golden_pow_eq] using
      golden_sector_succ_mul_phiInv delta 3

private theorem goldenUnitFifthClass_one : GoldenUnitFifthClass goldenOne := by
  refine ⟨⟨0, by decide⟩, goldenOne, ?_⟩
  decide

private theorem goldenUnitFifthClass_neg_one :
    GoldenUnitFifthClass (-goldenOne) := by
  refine ⟨⟨0, by decide⟩, -goldenOne, ?_⟩
  decide

private theorem goldenUnitFifthClass_phi : GoldenUnitFifthClass goldenPhi := by
  refine ⟨⟨1, by decide⟩, goldenOne, ?_⟩
  decide

private theorem goldenUnitFifthClass_neg_phi :
    GoldenUnitFifthClass (-goldenPhi) := by
  refine ⟨⟨1, by decide⟩, -goldenOne, ?_⟩
  decide

/-- The direct coordinate descent classifies every golden unit modulo fifth powers. -/
theorem goldenUnitFifthClass_of_unit (x : GoldenInt) (hx : GoldenUnit x) :
    GoldenUnitFifthClass x := by
  generalize hm : goldenUnitMeasure x = n
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
      have hpos : 0 < n := by rw [← hm]; exact goldenUnitMeasure_pos hx
      rcases eq_or_lt_of_le (show 1 ≤ n by omega) with hn | hn
      · have hm1 : goldenUnitMeasure x = 1 := by omega
        rcases goldenUnit_measure_one_cases hx hm1 with h | h | h | h
        · simpa [h] using goldenUnitFifthClass_one
        · simpa [h] using goldenUnitFifthClass_neg_one
        · simpa [h] using goldenUnitFifthClass_phi
        · simpa [h] using goldenUnitFifthClass_neg_phi
      · obtain ⟨y, hy, hylt, hrec⟩ := goldenUnit_descent hx (by omega)
        have hyClass : GoldenUnitFifthClass y :=
          ih (goldenUnitMeasure y) (by omega) y hy rfl
        rcases hrec with hrec | hrec
        · rw [hrec]
          exact goldenUnitFifthClass_mul_phi hyClass
        · rw [hrec]
          exact goldenUnitFifthClass_mul_phiInv hyClass

/-- Every golden unit has a representative among five classes modulo fifth powers. -/
theorem goldenUnitClassesModFifth : GoldenUnitClassesModFifth := by
  intro epsilon hepsilon
  exact goldenUnitFifthClass_of_unit epsilon hepsilon

end DkMath.FLT.Five
