/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExcessRealizedMoment
import DkMath.ABC.GNCubicBoundaryWeight

#print "file: DkMath.ABC.GNExcessCubicRealizedBoundary"

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom DkMath.NumberTheory

/-! ## Positive witnesses for the canonical realized large shell -/

/-- A realized canonical cubic large profile has a positive interval witness.
The zero endpoint has non-exceptional repeated part one, hence cannot pass the
large-modulus test. -/
theorem GNExcessRealizedLargeProfileSpace_exists_positive_point
    {X : ℕ}
    {excess : ∀ q ∈ GNNonExceptionalIntervalPrimeFamily 3 1 X, ℕ}
    (h : excess ∈ GNExcessRealizedLargeProfileSpace
      (GNNonExceptionalIntervalPrimeFamily 3 1 X) 3 1 X) :
    ∃ a, 0 < a ∧ a ∈ GNExactExcessProfileEvent
      (GNNonExceptionalIntervalPrimeFamily 3 1 X) excess 3 1 X := by
  obtain ⟨a, haE⟩ := (mem_realizedLargeProfileSpace_realized h).exists_point
  refine ⟨a, ?_, haE⟩
  by_contra hapos
  have ha0 : a = 0 := Nat.eq_zero_of_not_pos hapos
  subst a
  have hlarge := mem_realizedLargeProfileSpace_large h
  have hmod := (Finset.mem_filter.mp hlarge).2
  obtain ⟨haI, haProfile⟩ := Finset.mem_filter.mp haE
  rw [← haProfile,
    GNExcessJointDepthModulus_target_eq_repeatedPart Nat.prime_three
      haI (by simp)] at hmod
  have hsupport : GNNonExceptionalSupport 3 0 1 = ∅ := by
    ext q
    constructor
    · intro hq
      have hq' := Finset.mem_filter.mp hq
      have hqprime := (mem_support_factorization_iff.mp hq'.1).2.1
      have hgn : GN 3 0 1 = 3 := by
        rw [DkMath.NumberTheory.GN_three_dual_explicit]
        norm_num
      have hqdvd : q ∣ 3 := by
        rw [← hgn]
        exact (mem_support_factorization_iff.mp hq'.1).2.2
      have hqeq : q = 3 := by
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hqdvd with
          hqone | hqeq
        · exact False.elim (hqprime.ne_one hqone)
        · exact hqeq
      have hqdiv : q ∣ 3 := by simp [hqeq]
      exact False.elim (hq'.2 hqdiv)
    · simp
  have hrep : GNNonExceptionalRepeatedPart 3 0 1 = 1 := by
    unfold GNNonExceptionalRepeatedPart GNNonExceptionalPart
    rw [hsupport]
    simp [repeatedPrimePowerPart]
  rw [hrep] at hmod
  omega

/-! ## Profile and fiber boundary transfer -/

/-- The cubic target boundary weight transfers from the positive witness to
the realized profile's exact joint modulus. -/
theorem GNExcess_cubic_realizedLarge_boundaryWeight_le_modulus_three_eighths
    {X : ℕ}
    {excess : ∀ q ∈ GNNonExceptionalIntervalPrimeFamily 3 1 X, ℕ}
    (h : excess ∈ GNExcessRealizedLargeProfileSpace
      (GNNonExceptionalIntervalPrimeFamily 3 1 X) 3 1 X) :
    (GNExcessRootAddressCharge
      (GNNonExceptionalIntervalPrimeFamily 3 1 X) 3 excess : ℝ) *
        Real.exp ((3 / 8 : ℝ) *
          GNExcessActiveProfileMass
            (GNNonExceptionalIntervalPrimeFamily 3 1 X) excess) ≤
      (GNExcessJointDepthModulus
        (GNNonExceptionalIntervalPrimeFamily 3 1 X) excess : ℝ) ^
          (3 / 8 : ℝ) := by
  obtain ⟨a, ha, haE⟩ :=
    GNExcessRealizedLargeProfileSpace_exists_positive_point h
  obtain ⟨haI, haProfile⟩ := Finset.mem_filter.mp haE
  have htarget :=
    GNExcess_cubic_target_boundaryWeight_le_repeatedPart_three_eighths
      (a := a) (b := 1) (X := X) ha (by norm_num) haI (by simp)
  rw [haProfile] at htarget
  have hmod :
      GNExcessJointDepthModulus
          (GNNonExceptionalIntervalPrimeFamily 3 1 X) excess =
        GNNonExceptionalRepeatedPart 3 a 1 := by
    rw [← haProfile]
    exact GNExcessJointDepthModulus_target_eq_repeatedPart
      (p := 3) (b := 1) (a := a) (X := X) Nat.prime_three haI (by simp)
  calc
    _ ≤ (GNNonExceptionalRepeatedPart 3 a 1 : ℝ) ^ (3 / 8 : ℝ) := htarget
    _ = _ := by rw [← hmod]

/-- The whole exact fiber obeys the same cubic boundary-modulus bound. -/
theorem GNExcess_cubic_realizedLarge_fiberMoment_le_modulus_three_eighths
    {X : ℕ}
    {excess : ∀ q ∈ GNNonExceptionalIntervalPrimeFamily 3 1 X, ℕ}
    (h : excess ∈ GNExcessRealizedLargeProfileSpace
      (GNNonExceptionalIntervalPrimeFamily 3 1 X) 3 1 X) :
    ((GNExactExcessProfileEvent
      (GNNonExceptionalIntervalPrimeFamily 3 1 X) excess 3 1 X).card : ℝ) *
        Real.exp ((3 / 8 : ℝ) *
          GNExcessActiveProfileMass
            (GNNonExceptionalIntervalPrimeFamily 3 1 X) excess) ≤
      (GNExcessJointDepthModulus
        (GNNonExceptionalIntervalPrimeFamily 3 1 X) excess : ℝ) ^
          (3 / 8 : ℝ) := by
  have hcard :=
    card_GNExactExcessProfileEvent_le_largeBoundary
      (Q := GNNonExceptionalIntervalPrimeFamily 3 1 X)
      (excess := excess) (p := 3) (b := 1) (X := X)
      (by norm_num)
      (fun q hq => GNNonExceptionalIntervalPrimeFamily_prime hq)
      (fun q hq => GNNonExceptionalIntervalPrimeFamily_not_dvd_exponent hq)
      (fun q hq => GNNonExceptionalIntervalPrimeFamily_not_dvd_boundary hq)
      ((mem_realizedLargeProfileSpace_iff_realized_and_large
        (Q := GNNonExceptionalIntervalPrimeFamily 3 1 X)
        (p := 3) (b := 1) (X := X) (excess := excess) (by norm_num)).mp h).2
  calc
    _ ≤ (GNExcessRootAddressCharge
        (GNNonExceptionalIntervalPrimeFamily 3 1 X) 3 excess : ℝ) *
          Real.exp ((3 / 8 : ℝ) *
            GNExcessActiveProfileMass
              (GNNonExceptionalIntervalPrimeFamily 3 1 X) excess) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hcard
      · exact (Real.exp_pos _).le
    _ ≤ _ := GNExcess_cubic_realizedLarge_boundaryWeight_le_modulus_three_eighths h

/-! ## Cubic realized modulus moment -/

/-- The cubic modulus moment over realized large profiles. -/
noncomputable def GNExcessCubicRealizedLargeModulusMoment (X : ℕ) : ℝ :=
  ∑ excess ∈ GNExcessRealizedLargeProfileSpace
      (GNNonExceptionalIntervalPrimeFamily 3 1 X) 3 1 X,
    (GNExcessJointDepthModulus
      (GNNonExceptionalIntervalPrimeFamily 3 1 X) excess : ℝ) ^
        (3 / 8 : ℝ)

/-- The realized large boundary profile sum is bounded by its cubic modulus
moment. -/
theorem GNExcessRealizedLargeBoundaryProfileSum_cubic_three_eighths_le_modulusMoment
    {X : ℕ} :
    GNExcessRealizedLargeBoundaryProfileSum
      (GNNonExceptionalIntervalPrimeFamily 3 1 X) 3 1 X (3 / 8 : ℝ) ≤
      GNExcessCubicRealizedLargeModulusMoment X := by
  classical
  unfold GNExcessRealizedLargeBoundaryProfileSum
    GNExcessCubicRealizedLargeModulusMoment
  apply Finset.sum_le_sum
  intro excess hexcess
  simpa [GNExcessRootAddressCharge] using
    (GNExcess_cubic_realizedLarge_boundaryWeight_le_modulus_three_eighths
      hexcess)

/-- Cubic height diagnostic for one realized large profile. -/
theorem GNExcess_cubic_realizedLarge_modulus_rpow_le_height_rpow
    {X : ℕ}
    {excess : ∀ q ∈ GNNonExceptionalIntervalPrimeFamily 3 1 X, ℕ}
    (h : excess ∈ GNExcessRealizedLargeProfileSpace
      (GNNonExceptionalIntervalPrimeFamily 3 1 X) 3 1 X) :
    (GNExcessJointDepthModulus
      (GNNonExceptionalIntervalPrimeFamily 3 1 X) excess : ℝ) ^
        (3 / 8 : ℝ) ≤
      ((3 * (X + 1)^2 : ℕ) : ℝ) ^ (3 / 8 : ℝ) := by
  apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ (by norm_num)
  exact_mod_cast mem_realizedLargeProfileSpace_cubic_heightAdmissible h

/-! ## Final LUNA-005 composition -/

/-- The LUNA-004 finite-Euler bridge with the realized cubic modulus moment. -/
theorem exp_GNExcessMassAt_sum_cubic_three_eighths_le_finiteEuler_add_modulusMoment
    {X : ℕ} :
    ∑ a ∈ Finset.Icc 0 X,
        Real.exp ((3 / 8 : ℝ) * GNExcessMassAt
          (GNNonExceptionalIntervalPrimeFamily 3 1 X) 3 1 a) ≤
      2 * (X + 1 : ℝ) *
          GNExcessFiniteEulerDensity
            (GNNonExceptionalIntervalPrimeFamily 3 1 X) 3 1 X
            (3 / 8 : ℝ) +
        GNExcessCubicRealizedLargeModulusMoment X := by
  have hbridge :=
    exp_GNExcessMassAt_sum_le_finiteEuler_add_realizedLarge_cubic
      (X := X) (t := (3 / 8 : ℝ))
  exact hbridge.trans (add_le_add (le_refl _) (
    GNExcessRealizedLargeBoundaryProfileSum_cubic_three_eighths_le_modulusMoment
      (X := X)))

end DkMath.ABC
