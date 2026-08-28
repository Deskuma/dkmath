/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseLiftIndexNormalForm
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseLiftIndexCenterTransport"

/-!
# Fresh-prime deleted-center transport

The affine normal form from PUU-L025 separates the moving deleted center from
the fixed phase radius.  This module gives the center the canonical coordinate
`-b / M` in `ZMod q`, proves its zero-residue characterization and uniqueness,
and records the translation of both phase sheets when the old representative
changes.  The results remain finite provider-side congruence geometry.
-/

namespace DkMath.NumberTheory.PrimorialUniverse

/-! ## Canonical deleted-center coordinate -/

/-- The deleted center determined by an old representative `b` and period `M`. -/
noncomputable def freshPrimeDeletedCenterCoord
    (S : Finset ℕ) (q b : ℕ) : ZMod q :=
  -(b : ZMod q) * (finitePrimeBasisProduct S : ZMod q)⁻¹

/-- The canonical center has zero raw fresh-prime residue. -/
theorem freshPrimeDeletedCenterCoord_zero_residue
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q b : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) :
    (b : ZMod q) + freshPrimeDeletedCenterCoord S q b *
        (finitePrimeBasisProduct S : ZMod q) = 0 := by
  let : Fact (Nat.Prime q) := ⟨hq⟩
  have hM : (finitePrimeBasisProduct S : ZMod q) ≠ 0 :=
    finitePrimeBasisProduct_cast_ne_zero_of_freshPrime hS hq hqS
  simp [freshPrimeDeletedCenterCoord, hM]

/-- The zero-residue equation uniquely determines the deleted center. -/
theorem freshPrimeDeletedCenterCoord_unique
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q b : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S)
    {z : ZMod q}
    (hz : (b : ZMod q) + z * (finitePrimeBasisProduct S : ZMod q) = 0) :
    z = freshPrimeDeletedCenterCoord S q b := by
  let : Fact (Nat.Prime q) := ⟨hq⟩
  have hM : (finitePrimeBasisProduct S : ZMod q) ≠ 0 :=
    finitePrimeBasisProduct_cast_ne_zero_of_freshPrime hS hq hqS
  apply mul_right_cancel₀ hM
  calc
    z * (finitePrimeBasisProduct S : ZMod q) = -(b : ZMod q) := by
      linear_combination hz
    _ = freshPrimeDeletedCenterCoord S q b *
        (finitePrimeBasisProduct S : ZMod q) := by
      rw [freshPrimeDeletedCenterCoord]
      simp [hM]

/-- A deleted raw lift index is the canonical deleted-center coordinate. -/
theorem freshPrime_deleted_index_eq_centerCoord
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q b jzero : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hzero : IsFreshPrimeDeletedLiftIndex S q b jzero) :
    (jzero : ZMod q) = freshPrimeDeletedCenterCoord S q b := by
  let : Fact (Nat.Prime q) := ⟨hq⟩
  have hzero' : (primeBasisWheelLift S b jzero : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hzero.2
  rw [primeBasisWheelLift_cast_freshPrime] at hzero'
  exact freshPrimeDeletedCenterCoord_unique hS hq hqS hzero'

/-! ## Translation of the deleted center -/

/-- Changing `b` translates the canonical center by `(b₁ - b₂) / M`. -/
theorem freshPrime_deleted_center_transport
    {S : Finset ℕ} {q b₁ b₂ : ℕ} :
    freshPrimeDeletedCenterCoord S q b₂ -
        freshPrimeDeletedCenterCoord S q b₁ =
      ((b₁ : ZMod q) - (b₂ : ZMod q)) *
        (finitePrimeBasisProduct S : ZMod q)⁻¹ := by
  simp only [freshPrimeDeletedCenterCoord]
  ring

/-- The deleted natural indices obey the same center-translation law. -/
theorem freshPrime_deleted_center_transport_indices
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q b₁ b₂ jzero₁ jzero₂ : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hzero₁ : IsFreshPrimeDeletedLiftIndex S q b₁ jzero₁)
    (hzero₂ : IsFreshPrimeDeletedLiftIndex S q b₂ jzero₂) :
    (jzero₂ : ZMod q) - (jzero₁ : ZMod q) =
      ((b₁ : ZMod q) - (b₂ : ZMod q)) *
        (finitePrimeBasisProduct S : ZMod q)⁻¹ := by
  have hz₁ := freshPrime_deleted_index_eq_centerCoord hS hq hqS hzero₁
  have hz₂ := freshPrime_deleted_index_eq_centerCoord hS hq hqS hzero₂
  rw [hz₁, hz₂]
  exact freshPrime_deleted_center_transport

/-! ## Center/radius coordinates -/

/-- The plus phase index is the canonical center plus the fixed radius. -/
theorem freshPrime_plus_index_eq_centerCoord_add_radius
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q a b jplus jzero : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hplus : IsFreshPrimePlusLiftIndex S q a b jplus)
    (hzero : IsFreshPrimeDeletedLiftIndex S q b jzero) :
    (jplus : ZMod q) = freshPrimeDeletedCenterCoord S q b +
      freshPrimePhaseRadius S q a := by
  have hcenter := freshPrime_deleted_index_eq_centerCoord hS hq hqS hzero
  have hphase := freshPrime_plus_index_eq_center_add_radius hS hq hqS hplus hzero
  rw [hcenter] at hphase
  exact hphase

/-- The minus phase index is the canonical center minus the fixed radius. -/
theorem freshPrime_minus_index_eq_centerCoord_sub_radius
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q a b jminus jzero : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hminus : IsFreshPrimeMinusLiftIndex S q a b jminus)
    (hzero : IsFreshPrimeDeletedLiftIndex S q b jzero) :
    (jminus : ZMod q) = freshPrimeDeletedCenterCoord S q b -
      freshPrimePhaseRadius S q a := by
  have hcenter := freshPrime_deleted_index_eq_centerCoord hS hq hqS hzero
  have hphase := freshPrime_minus_index_eq_center_sub_radius hS hq hqS hminus hzero
  rw [hcenter] at hphase
  exact hphase

/-! ## Rigid phase-pair translation -/

/-- Both phase sheets translate by the same displacement as their center. -/
theorem freshPrime_phase_pair_translates_with_center
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q a b₁ b₂ jplus₁ jminus₁ jzero₁ jplus₂ jminus₂ jzero₂ : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hplus₁ : IsFreshPrimePlusLiftIndex S q a b₁ jplus₁)
    (hzero₁ : IsFreshPrimeDeletedLiftIndex S q b₁ jzero₁)
    (hminus₁ : IsFreshPrimeMinusLiftIndex S q a b₁ jminus₁)
    (hplus₂ : IsFreshPrimePlusLiftIndex S q a b₂ jplus₂)
    (hzero₂ : IsFreshPrimeDeletedLiftIndex S q b₂ jzero₂)
    (hminus₂ : IsFreshPrimeMinusLiftIndex S q a b₂ jminus₂) :
    ((jplus₂ : ZMod q) - (jplus₁ : ZMod q) =
        freshPrimeDeletedCenterCoord S q b₂ -
          freshPrimeDeletedCenterCoord S q b₁) ∧
      ((jminus₂ : ZMod q) - (jminus₁ : ZMod q) =
        freshPrimeDeletedCenterCoord S q b₂ -
          freshPrimeDeletedCenterCoord S q b₁) := by
  have hp₁ := freshPrime_plus_index_eq_centerCoord_add_radius hS hq hqS
    hplus₁ hzero₁
  have hp₂ := freshPrime_plus_index_eq_centerCoord_add_radius hS hq hqS
    hplus₂ hzero₂
  have hm₁ := freshPrime_minus_index_eq_centerCoord_sub_radius hS hq hqS
    hminus₁ hzero₁
  have hm₂ := freshPrime_minus_index_eq_centerCoord_sub_radius hS hq hqS
    hminus₂ hzero₂
  constructor
  · linear_combination hp₂ - hp₁
  · linear_combination hm₂ - hm₁

/-! ## Concrete `6 -> 30` two-representative regression -/

/--
For `b₁ = 1` and `b₂ = 5`, the centers are `4` and `0` in `ZMod 5`.
The public transport and center/radius APIs identify the corresponding phase
pairs as `{0, 3}` and `{1, 4}` at the index level.
-/
theorem freshPrimeDeletedCenterTransport_two_three_five_regression :
    freshPrimeDeletedCenterCoord ({2, 3} : Finset ℕ) 5 1 = (4 : ZMod 5) ∧
      freshPrimeDeletedCenterCoord ({2, 3} : Finset ℕ) 5 5 = (0 : ZMod 5) ∧
      freshPrimeDeletedCenterCoord ({2, 3} : Finset ℕ) 5 5 -
          freshPrimeDeletedCenterCoord ({2, 3} : Finset ℕ) 5 1 =
        ((1 : ZMod 5) - (5 : ZMod 5)) *
          (finitePrimeBasisProduct ({2, 3} : Finset ℕ) : ZMod 5)⁻¹ ∧
      (0 : ZMod 5) =
        freshPrimeDeletedCenterCoord ({2, 3} : Finset ℕ) 5 1 +
          freshPrimePhaseRadius ({2, 3} : Finset ℕ) 5 1 ∧
      (3 : ZMod 5) =
        freshPrimeDeletedCenterCoord ({2, 3} : Finset ℕ) 5 1 -
          freshPrimePhaseRadius ({2, 3} : Finset ℕ) 5 1 ∧
      (1 : ZMod 5) =
        freshPrimeDeletedCenterCoord ({2, 3} : Finset ℕ) 5 5 +
          freshPrimePhaseRadius ({2, 3} : Finset ℕ) 5 1 ∧
      (4 : ZMod 5) =
        freshPrimeDeletedCenterCoord ({2, 3} : Finset ℕ) 5 5 -
          freshPrimePhaseRadius ({2, 3} : Finset ℕ) 5 1 ∧
      (1 : ZMod 5) - 0 =
        freshPrimeDeletedCenterCoord ({2, 3} : Finset ℕ) 5 5 -
          freshPrimeDeletedCenterCoord ({2, 3} : Finset ℕ) 5 1 ∧
      (4 : ZMod 5) - 3 =
        freshPrimeDeletedCenterCoord ({2, 3} : Finset ℕ) 5 5 -
          freshPrimeDeletedCenterCoord ({2, 3} : Finset ℕ) 5 1 := by
  have hS : IsFinitePrimeBasis ({2, 3} : Finset ℕ) := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> norm_num
  have hqS : 5 ∉ ({2, 3} : Finset ℕ) := by simp
  have hM : finitePrimeBasisProduct ({2, 3} : Finset ℕ) = 6 := by
    norm_num [finitePrimeBasisProduct]
  have h6 : ((6 : ℕ) : ZMod 5) = ((1 : ℕ) : ZMod 5) :=
    (ZMod.natCast_eq_natCast_iff 6 1 5).mpr (by norm_num)
  have h4neg : ((4 : ℕ) : ZMod 5) = -((1 : ℕ) : ZMod 5) := by decide
  have h5zero : ((5 : ℕ) : ZMod 5) = 0 := by
    exact (ZMod.natCast_eq_zero_iff 5 5).mpr (dvd_refl 5)
  have h11 : ((11 : ℕ) : ZMod 5) = ((1 : ℕ) : ZMod 5) :=
    (ZMod.natCast_eq_natCast_iff 11 1 5).mpr (by norm_num)
  have h29 : ((29 : ℕ) : ZMod 5) = ((4 : ℕ) : ZMod 5) :=
    (ZMod.natCast_eq_natCast_iff 29 4 5).mpr (by norm_num)
  have hcenter₁ : freshPrimeDeletedCenterCoord ({2, 3} : Finset ℕ) 5 1 =
      (4 : ZMod 5) := by
    rw [freshPrimeDeletedCenterCoord, hM, h6]
    norm_num
    exact h4neg.symm
  have hcenter₂ : freshPrimeDeletedCenterCoord ({2, 3} : Finset ℕ) 5 5 =
      (0 : ZMod 5) := by
    rw [freshPrimeDeletedCenterCoord, hM, h6]
    norm_num
    exact h5zero
  have hraw := freshPrimeLiftIndex_two_three_five_regression
  have hplus₁ : IsFreshPrimePlusLiftIndex ({2, 3} : Finset ℕ) 5 1 1 0 :=
    hraw.2.2.2.2.2.1
  have hminus₁ : IsFreshPrimeMinusLiftIndex ({2, 3} : Finset ℕ) 5 1 1 3 :=
    hraw.2.2.2.2.2.2.1
  have hzero₁ : IsFreshPrimeDeletedLiftIndex ({2, 3} : Finset ℕ) 5 1 4 :=
    hraw.2.2.2.2.2.2.2.1
  have hplus₂ : IsFreshPrimePlusLiftIndex ({2, 3} : Finset ℕ) 5 1 5 1 := by
    constructor
    · norm_num
    · norm_num [primeBasisWheelLift, finitePrimeBasisProduct]
      exact h11
  have hminus₂ : IsFreshPrimeMinusLiftIndex ({2, 3} : Finset ℕ) 5 1 5 4 := by
    constructor
    · norm_num
    · norm_num [primeBasisWheelLift, finitePrimeBasisProduct]
      exact h29.trans h4neg
  have hzero₂ : IsFreshPrimeDeletedLiftIndex ({2, 3} : Finset ℕ) 5 5 0 := by
    constructor
    · norm_num
    · norm_num [primeBasisWheelLift, finitePrimeBasisProduct]
  have hplus₁' := freshPrime_plus_index_eq_centerCoord_add_radius hS
    (q := 5) (a := 1) (b := 1) (jplus := 0) (jzero := 4)
    (by norm_num) hqS hplus₁ hzero₁
  have hminus₁' := freshPrime_minus_index_eq_centerCoord_sub_radius hS
    (q := 5) (a := 1) (b := 1) (jminus := 3) (jzero := 4)
    (by norm_num) hqS hminus₁ hzero₁
  have hplus₂' := freshPrime_plus_index_eq_centerCoord_add_radius hS
    (q := 5) (a := 1) (b := 5) (jplus := 1) (jzero := 0)
    (by norm_num) hqS hplus₂ hzero₂
  have hminus₂' := freshPrime_minus_index_eq_centerCoord_sub_radius hS
    (q := 5) (a := 1) (b := 5) (jminus := 4) (jzero := 0)
    (by norm_num) hqS hminus₂ hzero₂
  have ht := freshPrime_deleted_center_transport (S := ({2, 3} : Finset ℕ))
    (q := 5) (b₁ := 1) (b₂ := 5)
  have htidx := freshPrime_deleted_center_transport_indices hS
    (q := 5) (b₁ := 1) (b₂ := 5) (jzero₁ := 4) (jzero₂ := 0)
    (by norm_num) hqS hzero₁ hzero₂
  have hpair := freshPrime_phase_pair_translates_with_center hS
    (q := 5) (a := 1) (b₁ := 1) (b₂ := 5)
    (jplus₁ := 0) (jminus₁ := 3) (jzero₁ := 4)
    (jplus₂ := 1) (jminus₂ := 4) (jzero₂ := 0)
    (by norm_num) hqS hplus₁ hzero₁ hminus₁ hplus₂ hzero₂ hminus₂
  refine ⟨hcenter₁, hcenter₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ht
  · exact hplus₁'
  · exact hminus₁'
  · exact hplus₂'
  · exact hminus₂'
  · exact hpair.1
  · exact hpair.2

end DkMath.NumberTheory.PrimorialUniverse
