/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.PowerGapBeam
import DkMath.CosmicFormula.CosmicFormulaBinom
import DkMath.NumberTheory.PrimitiveBeam

#print "file: DkMath.CosmicFormula.PowerGapBeamGN"

/-!
# Bridge from Power Beam to GN

This file keeps the heavier `GN` dependency out of the pure `PowerGapBeam`
module and records explicit low-degree bridges.
-/

namespace DkMath.CosmicFormula.PowerGapBeam

/-- In degree 3, the shifted Power Beam agrees with the existing cubic `GN`
    beam expression. -/
theorem powerBeam_three_shift_eq_GN {R : Type*} [CommRing R] (x u : R) :
    powerBeam 3 x (x + u) = DkMath.CosmicFormulaBinom.GN 3 u x := by
  rw [powerBeam_three]
  rw [DkMath.CosmicFormulaBinom.GN_eq_sum]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num
  ring

/-- In degree 4, the shifted Power Beam agrees with the existing quartic `GN`
    beam expression. -/
theorem powerBeam_four_shift_eq_GN {R : Type*} [CommRing R] (x u : R) :
    powerBeam 4 x (x + u) = DkMath.CosmicFormulaBinom.GN 4 u x := by
  rw [powerBeam_four]
  rw [DkMath.CosmicFormulaBinom.GN_eq_sum]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose]
  ring

/-- In degree 3, the endpoint Power Beam agrees with `GN` at the endpoint gap. -/
theorem powerBeam_three_eq_GN_of_gap {R : Type*} [CommRing R] (a b : R) :
    powerBeam 3 b a = DkMath.CosmicFormulaBinom.GN 3 (a - b) b := by
  rw [powerBeam_three]
  rw [DkMath.CosmicFormulaBinom.GN_eq_sum]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num
  ring

/-- In degree 4, the endpoint Power Beam agrees with `GN` at the endpoint gap. -/
theorem powerBeam_four_eq_GN_of_gap {R : Type*} [CommRing R] (a b : R) :
    powerBeam 4 b a = DkMath.CosmicFormulaBinom.GN 4 (a - b) b := by
  rw [powerBeam_four]
  rw [DkMath.CosmicFormulaBinom.GN_eq_sum]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose]
  ring

/-- Divisibility transfers from the cubic `GN` gap expression to the endpoint
    Power Beam. -/
theorem dvd_powerBeam_three_of_dvd_GN_gap {R : Type*} [CommRing R]
    {q a b : R}
    (h : q ∣ DkMath.CosmicFormulaBinom.GN 3 (a - b) b) :
    q ∣ powerBeam 3 b a := by
  rwa [powerBeam_three_eq_GN_of_gap]

/-- The cubic endpoint bridge preserves `padicValNat` after taking integer
    absolute values. -/
theorem powerBeam_three_padicValNat_eq_GN_gap (p : ℕ) (a b : ℤ) :
    padicValNat p (powerBeam 3 b a).natAbs =
      padicValNat p (DkMath.CosmicFormulaBinom.GN 3 (a - b) b).natAbs := by
  rw [powerBeam_three_eq_GN_of_gap]

/-- A cubic `GN` valuation upper bound transfers to the endpoint Power Beam. -/
theorem powerBeam_three_padicValNat_le_one_of_GN_le_one
    {p : ℕ} {a b : ℤ}
    (hGN :
      padicValNat p (DkMath.CosmicFormulaBinom.GN 3 (a - b) b).natAbs ≤ 1) :
    padicValNat p (powerBeam 3 b a).natAbs ≤ 1 := by
  simpa [powerBeam_three_padicValNat_eq_GN_gap] using hGN

/-- Cubic squarefreeness transfers from the `GN` gap expression to the endpoint
    Power Beam. -/
theorem powerBeam_three_squarefree_of_GN_squarefree
    {a b : ℤ}
    (hGN :
      Squarefree (DkMath.CosmicFormulaBinom.GN 3 (a - b) b).natAbs) :
    Squarefree (powerBeam 3 b a).natAbs := by
  simpa [powerBeam_three_eq_GN_of_gap] using hGN

/-- Primitive-prime divisibility from the Nat `GN` API, transported to the
    integer endpoint Power Beam used by the valuation engine. -/
theorem primitive_prime_dvd_powerBeam_three_natAbs
    {q a b : ℕ}
    (hq : DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow q a b 3)
    (hab_lt : b < a) :
    q ∣ (powerBeam 3 (b : ℤ) (a : ℤ)).natAbs := by
  have hGN_nat :
      q ∣ DkMath.CosmicFormulaBinom.GN 3 (a - b) b :=
    DkMath.NumberTheory.PrimitiveBeam.primitive_prime_dvd_GN
      (q := q) (a := a) (b := b) (d := 3)
      hq (by norm_num) (by norm_num) hab_lt
  have hbeam_nat :
      q ∣ (DkMath.CosmicFormulaBinom.GN 3 ((a : ℤ) - (b : ℤ)) (b : ℤ)).natAbs := by
    have hsub_cast : ((a - b : ℕ) : ℤ) = (a : ℤ) - (b : ℤ) :=
      Nat.cast_sub (Nat.le_of_lt hab_lt)
    have hGN_cast :
        ((DkMath.CosmicFormulaBinom.GN 3 (a - b) b : ℕ) : ℤ) =
          DkMath.CosmicFormulaBinom.GN 3 ((a : ℤ) - (b : ℤ)) (b : ℤ) := by
      rw [← hsub_cast]
      simp
    have hGN_int :
        (q : ℤ) ∣
          DkMath.CosmicFormulaBinom.GN 3 ((a : ℤ) - (b : ℤ)) (b : ℤ) := by
      rw [← hGN_cast]
      exact_mod_cast hGN_nat
    exact Int.natCast_dvd.mp hGN_int
  simpa [powerBeam_three_eq_GN_of_gap] using hbeam_nat

end DkMath.CosmicFormula.PowerGapBeam
