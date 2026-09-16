/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseLiftIndexReflection
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseLiftIndexNormalForm"

/-!
# Fresh-prime lift-index affine normal form

The phase pair has a radius `a / M` on the fresh-prime index circle, where
`M` is the old period.  Thus the deleted center and this radius give the
normal form `center + radius`, `center`, `center - radius`.  The result is
finite provider-side congruence geometry and does not assert prime existence
or an escape conclusion.
-/

namespace DkMath.NumberTheory.PrimorialUniverse

/-! ## Phase radius -/

/-- The phase radius is the anchor residue times the inverse old period.

This is the `ZMod q` realization of `a / M`; the inverse-multiplication
presentation keeps the definition available before a prime-field instance is
introduced.  The public multiplication theorem below supplies its semantic
characterization.
-/
noncomputable def freshPrimePhaseRadius
    (S : Finset ℕ) (q a : ℕ) : ZMod q :=
  (a : ZMod q) * (finitePrimeBasisProduct S : ZMod q)⁻¹

/-- The phase radius multiplied by the old period recovers the anchor. -/
theorem freshPrimePhaseRadius_mul_period
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q a : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) :
    freshPrimePhaseRadius S q a *
        (finitePrimeBasisProduct S : ZMod q) = (a : ZMod q) := by
  let : Fact (Nat.Prime q) := ⟨hq⟩
  have hM : (finitePrimeBasisProduct S : ZMod q) ≠ 0 :=
    finitePrimeBasisProduct_cast_ne_zero_of_freshPrime hS hq hqS
  simp [freshPrimePhaseRadius, hM]

/-- The phase radius is the unique coordinate whose period product is `a`. -/
theorem freshPrimePhaseRadius_unique
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q a : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S)
    {d : ZMod q}
    (hd : d * (finitePrimeBasisProduct S : ZMod q) = (a : ZMod q)) :
    d = freshPrimePhaseRadius S q a := by
  let : Fact (Nat.Prime q) := ⟨hq⟩
  have hM : (finitePrimeBasisProduct S : ZMod q) ≠ 0 :=
    finitePrimeBasisProduct_cast_ne_zero_of_freshPrime hS hq hqS
  apply mul_right_cancel₀ hM
  calc
    d * (finitePrimeBasisProduct S : ZMod q) = (a : ZMod q) := hd
    _ = freshPrimePhaseRadius S q a *
        (finitePrimeBasisProduct S : ZMod q) :=
      (freshPrimePhaseRadius_mul_period hS hq hqS).symm

/-- A coprime anchor has nonzero phase radius modulo a fresh prime. -/
theorem freshPrimePhaseRadius_ne_zero
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q a : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S)
    (hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S))) :
    freshPrimePhaseRadius S q a ≠ 0 := by
  let : Fact (Nat.Prime q) := ⟨hq⟩
  have hS' : IsFinitePrimeBasis (insert q S) := by
    intro p hp
    simp only [Finset.mem_insert] at hp
    rcases hp with rfl | hpS
    · exact hq
    · exact hS p hpS
  have ha0 : (a : ZMod q) ≠ 0 :=
    prime_anchor_cast_ne_zero hS' hcop (Finset.mem_insert_self q S)
  intro hr
  apply ha0
  calc
    (a : ZMod q) = freshPrimePhaseRadius S q a *
        (finitePrimeBasisProduct S : ZMod q) :=
      (freshPrimePhaseRadius_mul_period hS hq hqS).symm
    _ = 0 := by rw [hr, zero_mul]

/-! ## Explicit center/radius coordinates -/

/-- The plus phase index is the deleted center plus the phase radius. -/
theorem freshPrime_plus_index_eq_center_add_radius
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q a b jplus jzero : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hplus : IsFreshPrimePlusLiftIndex S q a b jplus)
    (hzero : IsFreshPrimeDeletedLiftIndex S q b jzero) :
    (jplus : ZMod q) = (jzero : ZMod q) + freshPrimePhaseRadius S q a := by
  let : Fact (Nat.Prime q) := ⟨hq⟩
  have hplus' := hplus.2
  have hzero' : ((primeBasisWheelLift S b jzero : ℕ) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hzero.2
  rw [primeBasisWheelLift_cast_freshPrime] at hplus' hzero'
  have hM : (finitePrimeBasisProduct S : ZMod q) ≠ 0 :=
    finitePrimeBasisProduct_cast_ne_zero_of_freshPrime hS hq hqS
  have hdiff : ((jplus : ZMod q) - (jzero : ZMod q)) *
      (finitePrimeBasisProduct S : ZMod q) = (a : ZMod q) := by
    linear_combination hplus' - hzero'
  have hdiff' : (jplus : ZMod q) - (jzero : ZMod q) =
      freshPrimePhaseRadius S q a := by
    apply mul_right_cancel₀ hM
    calc
      ((jplus : ZMod q) - (jzero : ZMod q)) *
          (finitePrimeBasisProduct S : ZMod q) = (a : ZMod q) := hdiff
      _ = freshPrimePhaseRadius S q a *
          (finitePrimeBasisProduct S : ZMod q) :=
        (freshPrimePhaseRadius_mul_period hS hq hqS).symm
  have hEq : (jplus : ZMod q) =
      freshPrimePhaseRadius S q a + (jzero : ZMod q) :=
    sub_eq_iff_eq_add.mp hdiff'
  simpa [add_comm] using hEq

/-- The minus phase index is the deleted center minus the phase radius. -/
theorem freshPrime_minus_index_eq_center_sub_radius
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q a b jminus jzero : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hminus : IsFreshPrimeMinusLiftIndex S q a b jminus)
    (hzero : IsFreshPrimeDeletedLiftIndex S q b jzero) :
    (jminus : ZMod q) = (jzero : ZMod q) - freshPrimePhaseRadius S q a := by
  let : Fact (Nat.Prime q) := ⟨hq⟩
  have hminus' := hminus.2
  have hzero' : ((primeBasisWheelLift S b jzero : ℕ) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hzero.2
  rw [primeBasisWheelLift_cast_freshPrime] at hminus' hzero'
  have hM : (finitePrimeBasisProduct S : ZMod q) ≠ 0 :=
    finitePrimeBasisProduct_cast_ne_zero_of_freshPrime hS hq hqS
  have hdiff : ((jminus : ZMod q) - (jzero : ZMod q)) *
      (finitePrimeBasisProduct S : ZMod q) = -(a : ZMod q) := by
    linear_combination hminus' - hzero'
  have hdiff' : (jminus : ZMod q) - (jzero : ZMod q) =
      -freshPrimePhaseRadius S q a := by
    apply mul_right_cancel₀ hM
    calc
      ((jminus : ZMod q) - (jzero : ZMod q)) *
          (finitePrimeBasisProduct S : ZMod q) = -(a : ZMod q) := hdiff
      _ = (-freshPrimePhaseRadius S q a) *
          (finitePrimeBasisProduct S : ZMod q) := by
        rw [neg_mul, freshPrimePhaseRadius_mul_period hS hq hqS]
  have hEq : (jminus : ZMod q) =
      (-freshPrimePhaseRadius S q a) + (jzero : ZMod q) :=
    sub_eq_iff_eq_add.mp hdiff'
  simpa [sub_eq_add_neg, add_comm] using hEq

/-- The phase separation is twice the constant phase radius. -/
theorem freshPrime_phase_index_separation
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q a b jplus jminus jzero : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hplus : IsFreshPrimePlusLiftIndex S q a b jplus)
    (hminus : IsFreshPrimeMinusLiftIndex S q a b jminus)
    (hzero : IsFreshPrimeDeletedLiftIndex S q b jzero) :
    (jplus : ZMod q) - (jminus : ZMod q) =
      2 * freshPrimePhaseRadius S q a := by
  have hp := freshPrime_plus_index_eq_center_add_radius hS hq hqS hplus hzero
  have hm := freshPrime_minus_index_eq_center_sub_radius hS hq hqS hminus hzero
  linear_combination hp - hm

/-! ## Constant-radius comparison -/

/-- Changing the old representative changes the center, not the phase radius. -/
theorem freshPrime_plus_offsets_eq_across_old_representatives
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q a b₁ b₂ jplus₁ jminus₁ jzero₁ jplus₂ jminus₂ jzero₂ : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hplus₁ : IsFreshPrimePlusLiftIndex S q a b₁ jplus₁)
    (hzero₁ : IsFreshPrimeDeletedLiftIndex S q b₁ jzero₁)
    (hplus₂ : IsFreshPrimePlusLiftIndex S q a b₂ jplus₂)
    (hzero₂ : IsFreshPrimeDeletedLiftIndex S q b₂ jzero₂)
    (hminus₁ : IsFreshPrimeMinusLiftIndex S q a b₁ jminus₁)
    (hminus₂ : IsFreshPrimeMinusLiftIndex S q a b₂ jminus₂)
    (_hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S))) :
    (jplus₁ : ZMod q) - (jzero₁ : ZMod q) =
        (jplus₂ : ZMod q) - (jzero₂ : ZMod q) ∧
      (jminus₁ : ZMod q) - (jzero₁ : ZMod q) =
        (jminus₂ : ZMod q) - (jzero₂ : ZMod q) := by
  have hp₁ := freshPrime_plus_index_eq_center_add_radius hS hq hqS hplus₁ hzero₁
  have hp₂ := freshPrime_plus_index_eq_center_add_radius hS hq hqS hplus₂ hzero₂
  have hm₁ := freshPrime_minus_index_eq_center_sub_radius hS hq hqS hminus₁ hzero₁
  have hm₂ := freshPrime_minus_index_eq_center_sub_radius hS hq hqS hminus₂ hzero₂
  constructor
  · linear_combination hp₁ - hp₂
  · linear_combination hm₁ - hm₂

/-! ## Concrete `6 -> 30` regression -/

/--
The `S = {2, 3}`, `q = 5`, `a = b = 1` example has radius `1` and the
three distinguished indices are `0 = 4 + 1`, `4`, and `3 = 4 - 1` in
`ZMod 5`.  The final equality records their center-free separation.
-/
theorem freshPrimeLiftIndexNormalForm_two_three_five_regression :
    freshPrimePhaseRadius ({2, 3} : Finset ℕ) 5 1 = (1 : ZMod 5) ∧
      (0 : ZMod 5) = 4 + freshPrimePhaseRadius ({2, 3} : Finset ℕ) 5 1 ∧
      (3 : ZMod 5) = 4 - freshPrimePhaseRadius ({2, 3} : Finset ℕ) 5 1 ∧
      (0 : ZMod 5) - 3 =
        2 * freshPrimePhaseRadius ({2, 3} : Finset ℕ) 5 1 := by
  have hS : IsFinitePrimeBasis ({2, 3} : Finset ℕ) := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> norm_num
  have hqS : 5 ∉ ({2, 3} : Finset ℕ) := by simp
  have hcop : Nat.Coprime 1 (finitePrimeBasisProduct (insert 5 ({2, 3} : Finset ℕ))) := by
    norm_num
  have hradius : freshPrimePhaseRadius ({2, 3} : Finset ℕ) 5 1 = (1 : ZMod 5) := by
    have hM : finitePrimeBasisProduct ({2, 3} : Finset ℕ) = 6 := by
      norm_num [finitePrimeBasisProduct]
    have h6 : ((6 : ℕ) : ZMod 5) = ((1 : ℕ) : ZMod 5) :=
      (ZMod.natCast_eq_natCast_iff 6 1 5).mpr (by norm_num)
    rw [freshPrimePhaseRadius, hM, h6]
    simp
  rcases freshPrimeLiftIndex_two_three_five_regression with
    ⟨_, _, _, _, _, hplus, hminus, hzero, _, _, _⟩
  have hp := freshPrime_plus_index_eq_center_add_radius hS (q := 5) (a := 1)
    (b := 1) (jplus := 0) (jzero := 4) (by norm_num) hqS hplus hzero
  have hm := freshPrime_minus_index_eq_center_sub_radius hS (q := 5) (a := 1)
    (b := 1) (jminus := 3) (jzero := 4) (by norm_num) hqS hminus hzero
  have hs := freshPrime_phase_index_separation hS (q := 5) (a := 1)
    (b := 1) (jplus := 0) (jminus := 3) (jzero := 4) (by norm_num) hqS
    hplus hminus hzero
  refine ⟨hradius, ?_, ?_, ?_⟩
  · simpa [hradius] using hp
  · simpa [hradius] using hm
  · simpa [hradius] using hs

end DkMath.NumberTheory.PrimorialUniverse
