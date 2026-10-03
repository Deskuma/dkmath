/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.CurrentCarrierRamifiedObstruction
import DkMath.FLT.Kummer.CyclotomicPrincipalization
import Mathlib.FieldTheory.KummerExtension

/-! Complete current phase aggregation after removing the necessary ramified
uniformizer. The raw carrier retains that factor; units and the original
Fermat equation remain explicit in the element receiver. -/

namespace DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierPower
open SevenRealCubicInt SevenCyclotomicDegreeSixInt
open CurrentCarrierRamification IsDedekindDomain
open DkMath.Lib.NumberTheory.FiniteIdealPowerAggregation
open scoped BigOperators
noncomputable section

private theorem six_current_factors_product {R : Type*} [CommRing R] [IsDomain R]
    (ζ : R) (hζ : IsPrimitiveRoot ζ 7) (X Y : R) :
    (∏ j ∈ Finset.range 6, (X - ζ ^ (j + 1) * Y)) =
      X ^ 6 + X ^ 5 * Y + X ^ 4 * Y ^ 2 + X ^ 3 * Y ^ 3 + X ^ 2 * Y ^ 4 + X * Y ^ 5 + Y ^ 6 := by
  have hpoly := X_pow_sub_C_eq_prod hζ
    (α := Y) (a := Y ^ 7) (by decide : 0 < 7) rfl
  rw [Finset.prod_range_succ'] at hpoly
  simp only [pow_zero, one_mul] at hpoly
  have hfac : (Polynomial.X : Polynomial R) ^ 7 - Polynomial.C (Y ^ 7) =
    (Polynomial.X - Polynomial.C Y) *
    (Polynomial.X ^ 6 + Polynomial.X ^ 5 * Polynomial.C Y + Polynomial.X ^ 4 * Polynomial.C Y ^ 2 +
      Polynomial.X ^ 3 * Polynomial.C Y ^ 3 + Polynomial.X ^ 2 * Polynomial.C Y ^ 4 +
      Polynomial.X * Polynomial.C Y ^ 5 + Polynomial.C Y ^ 6) := by
    simp only [map_pow]
    ring
  rw [hfac] at hpoly
  rw [mul_comm (Polynomial.X - Polynomial.C Y)] at hpoly
  have he := mul_right_cancel₀ (Polynomial.X_sub_C_ne_zero Y) hpoly
  have heval := congrArg (Polynomial.eval X) he
  simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_prod,
    Polynomial.eval_sub] using heval.symm

variable {x y z : ℕ} {source : CounterexamplePack x y z}
variable {r : PrimitiveCounterexampleRamifiedProvenance source}
variable {p : DirectRealCubicRootPacket source r}

theorem six_current_factors_product_direct (p : DirectRealCubicRootPacket source r) :
    (∏ j ∈ Finset.range 6, (ofReal (SevenRealCubicInt.rotateEquiv p.rho) -
      zeta ^ (j + 1) * ofReal p.rho)) = ofReal (directOrbitQuotient p) := by
  rw [six_current_factors_product zeta zeta_isPrimitiveRoot]
  simp [directOrbitQuotient, seventhQuotient, map_add, map_mul, map_pow]

theorem prime_eq_ramified_of_mem_current_phases
    (p : DirectRealCubicRootPacket source r)
    {P : Ideal SevenCyclotomicDegreeSixInt.Ring} (hP : P.IsPrime)
    {i j : ℕ} (hij : i ≠ j) (hi : i < 7) (hj : j < 7)
    (hfi : ofReal (SevenRealCubicInt.rotateEquiv p.rho) - zeta ^ i * ofReal p.rho ∈ P)
    (hfj : ofReal (SevenRealCubicInt.rotateEquiv p.rho) - zeta ^ j * ofReal p.rho ∈ P) :
    P = ramifiedPrime := by
  have hy : ofReal p.rho ≠ 0 := by
    intro hz
    have hzero := ofReal_injective hz
    exact p.thetaResidue_ne_zero (by rw [hzero]; exact map_zero _)
  have hspan := linearFactorDiffSpanEqSubOneSpan zeta_isPrimitiveRoot
    (by decide : Nat.Prime 7) hy i j hij hi hj
  have hdiff : zeta ^ j * ofReal p.rho - zeta ^ i * ofReal p.rho ∈ P := by
    convert P.sub_mem hfi hfj using 1; ring
  have hspanle : Ideal.span {zeta ^ j * ofReal p.rho - zeta ^ i * ofReal p.rho} ≤ P :=
    (Ideal.span_singleton_le_iff_mem _).mpr hdiff
  rw [hspan] at hspanle
  have hmul : (zeta - 1) * ofReal p.rho ∈ P := hspanle (Ideal.subset_span (by simp))
  rcases hP.mem_or_mem hmul with hlambda | hρ
  · have huniformizer : ramifiedUniformizer ∈ P := by
      simpa [ramifiedUniformizer] using P.neg_mem hlambda
    have hle : ramifiedPrime ≤ P := by
      rw [ramifiedPrime_eq_span_uniformizer]
      exact (Ideal.span_singleton_le_iff_mem _).mpr huniformizer
    exact (ramifiedPrime_isMaximal.eq_of_le hP.ne_top hle).symm
  · have hrot : ofReal (SevenRealCubicInt.rotateEquiv p.rho) ∈ P := by
      have hm := P.mul_mem_left (zeta ^ i) hρ
      simpa only [sub_add_cancel] using P.add_mem hfi hm
    obtain ⟨a, b, hab⟩ := (directOrbit_roots_isCoprime p).map ofReal
    have hone : (1 : SevenCyclotomicDegreeSixInt.Ring) ∈ P := by
      rw [← hab]
      exact P.add_mem (P.mul_mem_left a hρ) (P.mul_mem_left b hrot)
    exact False.elim (hP.ne_top ((Ideal.eq_top_iff_one _).mpr hone))

/-- Removing one ramified uniformizer separates all six current phases. -/
theorem normalizedPhaseIdeals_pairwise
    (p : DirectRealCubicRootPacket source r) :
    Set.Pairwise (↑(Finset.range 6)) fun i j =>
      IsCoprime (Ideal.span {phaseCarrierQuotient p (i + 1)})
        (Ideal.span {phaseCarrierQuotient p (j + 1)}) := by
  intro i hi j hj hij
  have hi6 := Finset.mem_range.mp hi
  have hj6 := Finset.mem_range.mp hj
  refine spanSingletons_isCoprime_of_noCommonPrime ?_
  intro P hP hqi hqj
  have hfi : phaseCarrier p (i + 1) ∈ P := by
    rw [phaseCarrier_eq_uniformizer_mul_quotient]
    exact P.mul_mem_left ramifiedUniformizer hqi
  have hfj : phaseCarrier p (j + 1) ∈ P := by
    rw [phaseCarrier_eq_uniformizer_mul_quotient]
    exact P.mul_mem_left ramifiedUniformizer hqj
  have heq := prime_eq_ramified_of_mem_current_phases p hP
    (i := i + 1) (j := j + 1) (by omega) (by omega) (by omega) hfi hfj
  rw [heq] at hqi
  exact phaseCarrierQuotient_not_mem_ramifiedPrime p (i + 1) (by omega) hqi

/-- The complete six-phase normalized product keeps the residual unit. -/
theorem normalizedPhaseProduct_unit_mul_fourteenth_power
    (h : DirectOrbitCanonicalCommonFactorPacket p) :
    ∃ u : SevenCyclotomicDegreeSixInt.Ring, IsUnit u ∧
      (∏ j ∈ Finset.range 6, phaseCarrierQuotient p (j + 1)) =
        u * ofReal h.squareRefinement.quotientSquareRoot ^ 14 := by
  obtain ⟨U, hu⟩ := directOrbitQuotient_eq_currentAxis_cube_unit_mul_squareRoot_pow
    h.squareRefinement
  have hraw := six_current_factors_product_direct p
  change (∏ j ∈ Finset.range 6, phaseCarrier p (j + 1)) =
    ofReal (directOrbitQuotient p) at hraw
  have hfac : (∏ j ∈ Finset.range 6, phaseCarrier p (j + 1)) =
      ramifiedUniformizer ^ 6 * (∏ j ∈ Finset.range 6, phaseCarrierQuotient p (j + 1)) := by
    simp_rw [phaseCarrier_eq_uniformizer_mul_quotient]
    rw [Finset.prod_mul_distrib]
    simp
  have hu' : ofReal (directOrbitQuotient p) = ramifiedUniformizer ^ 6 *
      ((zetaInv ^ 3 * ofReal (U : SevenRealCubicInt)) *
        ofReal h.squareRefinement.quotientSquareRoot ^ 14) := by
    rw [hu, map_mul, map_mul, map_pow, map_pow, ofReal_eisensteinAxis_eq]
    ring
  rw [hfac, hu'] at hraw
  refine ⟨zetaInv ^ 3 * ofReal (U : SevenRealCubicInt), ?_, ?_⟩
  · have hz : IsUnit zetaInv := ⟨zetaUnit⁻¹, rfl⟩
    exact (hz.pow 3).mul (U.isUnit.map ofReal)
  · exact mul_left_cancel₀ (pow_ne_zero 6 ramifiedUniformizer_ne_zero) hraw

/-- The full product of normalized current phase ideals is a seventh power. -/
theorem normalizedPhaseIdealProduct_seventh_power
    (h : DirectOrbitCanonicalCommonFactorPacket p) :
    (∏ j ∈ Finset.range 6, Ideal.span {phaseCarrierQuotient p (j + 1)}) =
      (Ideal.span {ofReal h.squareRefinement.quotientSquareRoot} ^ 2) ^ 7 := by
  obtain ⟨u, hu, heq⟩ := normalizedPhaseProduct_unit_mul_fourteenth_power h
  rw [span_singleton_finset_prod, heq]
  rw [← Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_eq_top.mpr hu]
  rw [← Ideal.one_eq_top, one_mul, ← Ideal.span_singleton_pow, ← pow_mul]

/-- Each normalized current phase is an ideal seventh power, using all six
phases rather than a selected residue row. -/
theorem normalizedPhaseIdeal_seventh_power
    (h : DirectOrbitCanonicalCommonFactorPacket p) (j : ℕ) (hjpos : 0 < j) (hjlt : j < 7) :
    ∃ J : Ideal SevenCyclotomicDegreeSixInt.Ring,
      Ideal.span {phaseCarrierQuotient p j} = J ^ 7 := by
  have hne : ∀ i ∈ Finset.range 6,
      Ideal.span ({phaseCarrierQuotient p (i + 1)} : Set SevenCyclotomicDegreeSixInt.Ring) ≠ ⊥ := by
    intro i hi he
    have hz := Ideal.span_singleton_eq_bot.mp he
    apply phaseCarrierQuotient_not_mem_ramifiedPrime p (i + 1) (by
      have hi6 := Finset.mem_range.mp hi
      omega)
    rw [hz]
    exact Ideal.zero_mem _
  have hall := dedekindIdealEqPowOfProdEqPowOfPairwise
    (normalizedPhaseIdeals_pairwise p) hne (normalizedPhaseIdealProduct_seventh_power h)
  have hjmem : j-1 ∈ Finset.range 6 := by simp only [Finset.mem_range]; omega
  have hj : j-1 + 1=j := by omega
  simpa only [hj] using hall (j-1) hjmem

private theorem phaseInverseExponent_bounds (i : Fin 3) :
    0 < phaseInverseExponent i ∧ phaseInverseExponent i < 7 := by
  fin_cases i <;> norm_num [phaseInverseExponent]

variable {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}

/-- The actual phase-corrected current carrier with one uniformizer removed. -/
def normalizedCarrierIdeal (c : CurrentCommonPrimeCyclotomicPacket h q) :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  Ideal.span {phaseCarrierQuotient p (phaseInverseExponent c.phase)}

theorem normalizedCarrierIdeal_ne_zero (c : CurrentCommonPrimeCyclotomicPacket h q) :
    normalizedCarrierIdeal c ≠ 0 := by
  intro he
  have hz := Ideal.span_singleton_eq_bot.mp he
  apply phaseCarrierQuotient_not_mem_ramifiedPrime p _
    (phaseInverseExponent_not_seven_dvd c.phase)
  rw [hz]
  exact Ideal.zero_mem _

theorem normalizedCarrierIdeal_seventh_power (c : CurrentCommonPrimeCyclotomicPacket h q) :
    ∃ J : Ideal SevenCyclotomicDegreeSixInt.Ring, normalizedCarrierIdeal c = J ^ 7 := by
  have hp := phaseInverseExponent_bounds c.phase
  exact normalizedPhaseIdeal_seventh_power h _ hp.1 hp.2

/-- Every prime exponent of the normalized carrier is divisible by seven. -/
theorem normalizedCarrier_exponent_seven_dvd (c : CurrentCommonPrimeCyclotomicPacket h q)
    (v : HeightOneSpectrum SevenCyclotomicDegreeSixInt.Ring) :
    7 ∣ exponent (normalizedCarrierIdeal c) v := by
  obtain ⟨J, hJ⟩ := normalizedCarrierIdeal_seventh_power c
  have hJ0 : J ≠ 0 := by
    intro hz
    apply normalizedCarrierIdeal_ne_zero c
    simpa only [hz, zero_pow (by decide : 7 ≠ 0)] using hJ
  rw [exponent, hJ, Associates.mk_pow]
  rw [Associates.count_pow (Associates.mk_ne_zero.mpr hJ0)
    (Associates.irreducible_mk.mpr v.irreducible) 7]
  exact dvd_mul_right _ _

/-- The complete-support hypothesis of the checked receiver is discharged
for the explicitly normalized carrier. -/
theorem normalized_completeSupport_seventh_divisibility
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    ∀ v ∈ support (normalizedCarrierIdeal c) (normalizedCarrierIdeal_ne_zero c),
      7 ∣ exponent (normalizedCarrierIdeal c) v := by
  intro v _
  exact normalizedCarrier_exponent_seven_dvd c v

/-- The phase-corrected current ideal includes its necessary ramified factor. -/
theorem currentCarrier_ramifiedIdeal_mul_seventh_power
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    ∃ J : Ideal SevenCyclotomicDegreeSixInt.Ring,
      CurrentAggregation.carrierIdeal c = ramifiedPrime * J ^ 7 := by
  have hp := phaseInverseExponent_bounds c.phase
  obtain ⟨J, hJ⟩ := normalizedPhaseIdeal_seventh_power h _ hp.1 hp.2
  refine ⟨J, ?_⟩
  rw [CurrentAggregation.carrierIdeal, currentLinearCarrier_eq_phaseCarrier,
    phaseCarrier_eq_uniformizer_mul_quotient, ← Ideal.span_singleton_mul_span_singleton,
    ← ramifiedPrime_eq_span_uniformizer, hJ]

/-- The current carrier is a ramified uniformizer times a unit times a
seventh power. The original Fermat equation is retained verbatim. -/
theorem currentCarrier_ramified_element_receiver
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    ∃ u beta : SevenCyclotomicDegreeSixInt.Ring, IsUnit u ∧
      currentLinearCarrier c = ramifiedUniformizer * u * beta ^ 7 ∧ Fermat7Equation x y z := by
  have hp := phaseInverseExponent_bounds c.phase
  obtain ⟨J, hJ⟩ := normalizedPhaseIdeal_seventh_power h _ hp.1 hp.2
  obtain ⟨u, hu, heq⟩ := unitMulPowOfSpanEqPow hJ
  refine ⟨u, Submodule.IsPrincipal.generator J, hu, ?_, source.hEq⟩
  rw [currentLinearCarrier_eq_phaseCarrier, phaseCarrier_eq_uniformizer_mul_quotient, heq]
  ring

end
end DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierPower
