/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.CurrentFiniteAggregation
import Mathlib.Algebra.Ring.GeomSum

/-! The current linear carrier has ramified multiplicity one. Consequently
complete-support seventh divisibility for the raw carrier is impossible. The
quotient after extracting the ramified uniformizer is exposed separately. -/

namespace DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierRamification

open SevenRealCubicInt SevenCyclotomicDegreeSixInt IsDedekindDomain
open DkMath.Lib.NumberTheory.FiniteIdealPowerAggregation
open scoped NumberField

noncomputable section

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- A first-order ramified perturbation always belongs to the ramified prime. -/
theorem linear_ramified_mem {b w : SevenCyclotomicDegreeSixInt.Ring}
    (k : ℕ) (hb : b ∈ ramifiedPrime ^ 2) :
    b + (1 - zeta ^ k) * w ∈ ramifiedPrime := by
  have hpi : ramifiedUniformizer ∈ ramifiedPrime := by
    change ramifiedEval ramifiedUniformizer = 0
    exact ramifiedEval_uniformizer
  have hg : (1 - zeta ^ k) * w ∈ ramifiedPrime := by
    rw [← mul_neg_geom_sum zeta k]
    exact ramifiedPrime.mul_mem_right _ (ramifiedPrime.mul_mem_right _ hpi)
  exact ramifiedPrime.add_mem (Ideal.pow_le_self (by omega) hb) hg

/-- The first-order coefficient cannot cancel when its residue is nonzero. -/
theorem linear_ramified_not_mem_sq {b w : SevenCyclotomicDegreeSixInt.Ring}
    (k : ℕ) (hb : b ∈ ramifiedPrime ^ 2)
    (hw : w ∉ ramifiedPrime) (hk : (k : ZMod 7) ≠ 0) :
    b + (1 - zeta ^ k) * w ∉ ramifiedPrime ^ 2 := by
  intro hm
  have hd := (ramifiedPrime ^ 2).sub_mem hm hb
  have hd' : (1 - zeta ^ k) * w ∈ ramifiedPrime ^ 2 := by
    simpa only [add_sub_cancel_left] using hd
  rw [← mul_neg_geom_sum zeta k, mul_assoc] at hd'
  have hg : (∑ i ∈ Finset.range k, zeta ^ i) * w ∈ ramifiedPrime :=
    (uniformizer_mul_mem_ramifiedPrime_sq_iff _).mp hd'
  change ramifiedEval ((∑ i ∈ Finset.range k, zeta ^ i) * w) = 0 at hg
  simp only [map_mul, map_sum, map_pow, ramifiedEval_zeta, one_pow,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hg
  have hw' : ramifiedEval w ≠ 0 := hw
  exact (mul_ne_zero hk hw') hg

variable {x y z : ℕ} {source : CounterexamplePack x y z}
variable {r : PrimitiveCounterexampleRamifiedProvenance source}

theorem gapAxis_dvd (p : DirectRealCubicRootPacket source r) :
    eisensteinAxis ∣ directOrbitGap p :=
  dvd_trans (dvd_pow_self _ (by omega : 32 ≠ 0)) (directOrbit_gap_axis_pow32_dvd p)

/-- The current orbit gap divided by its real-cubic axis. -/
def gapAxisQuotient (p : DirectRealCubicRootPacket source r) : SevenRealCubicInt :=
  Classical.choose (gapAxis_dvd p)

theorem gapAxisQuotient_spec (p : DirectRealCubicRootPacket source r) :
    rotateEquiv p.rho - p.rho = eisensteinAxis * gapAxisQuotient p :=
  Classical.choose_spec (gapAxis_dvd p)

/-- All six nontrivial phase carriers share the same current real-cubic roots. -/
def phaseCarrier (p : DirectRealCubicRootPacket source r) (j : ℕ) :
    SevenCyclotomicDegreeSixInt.Ring :=
  ofReal (rotateEquiv p.rho) - zeta ^ j * ofReal p.rho

/-- The quotient after removing exactly one current ramified uniformizer. -/
def phaseCarrierQuotient (p : DirectRealCubicRootPacket source r) (j : ℕ) :
    SevenCyclotomicDegreeSixInt.Ring :=
  zetaInv * ramifiedUniformizer * ofReal (gapAxisQuotient p) +
    (∑ i ∈ Finset.range j, zeta ^ i) * ofReal p.rho

theorem phaseCarrier_eq_uniformizer_mul_quotient
    (p : DirectRealCubicRootPacket source r) (j : ℕ) :
    phaseCarrier p j = ramifiedUniformizer * phaseCarrierQuotient p j := by
  have hg : ofReal (rotateEquiv p.rho - p.rho) =
      zetaInv * ramifiedUniformizer ^ 2 * ofReal (gapAxisQuotient p) := by
    rw [gapAxisQuotient_spec, map_mul, ofReal_eisensteinAxis_eq]
  have hs : ramifiedUniformizer * (∑ i ∈ Finset.range j, zeta ^ i) =
      1 - zeta ^ j := mul_neg_geom_sum zeta j
  calc
    phaseCarrier p j = ofReal (rotateEquiv p.rho - p.rho) +
        (1 - zeta ^ j) * ofReal p.rho := by
      simp only [phaseCarrier, map_sub]
      ring
    _ = zetaInv * ramifiedUniformizer ^ 2 * ofReal (gapAxisQuotient p) +
        (ramifiedUniformizer * (∑ i ∈ Finset.range j, zeta ^ i)) * ofReal p.rho := by
      rw [hg, hs]
    _ = ramifiedUniformizer * phaseCarrierQuotient p j := by
      simp only [phaseCarrierQuotient]
      ring

theorem ramifiedEval_phaseCarrierQuotient
    (p : DirectRealCubicRootPacket source r) (j : ℕ) :
    ramifiedEval (phaseCarrierQuotient p j) = (j : ZMod 7) * thetaResidue p.rho := by
  simp [phaseCarrierQuotient, map_sum]

theorem phaseCarrierQuotient_not_mem_ramifiedPrime
    (p : DirectRealCubicRootPacket source r) (j : ℕ) (hj : ¬ 7 ∣ j) :
    phaseCarrierQuotient p j ∉ ramifiedPrime := by
  change ramifiedEval (phaseCarrierQuotient p j) ≠ 0
  rw [ramifiedEval_phaseCarrierQuotient]
  exact mul_ne_zero (fun he => hj ((ZMod.natCast_eq_zero_iff j 7).mp he))
    p.thetaResidue_ne_zero

theorem phaseCarrier_mem_ramifiedPrime
    (p : DirectRealCubicRootPacket source r) (j : ℕ) :
    phaseCarrier p j ∈ ramifiedPrime := by
  rw [phaseCarrier_eq_uniformizer_mul_quotient]
  change ramifiedEval (ramifiedUniformizer * phaseCarrierQuotient p j) = 0
  rw [map_mul, ramifiedEval_uniformizer, zero_mul]

theorem phaseCarrier_not_mem_ramifiedPrime_sq
    (p : DirectRealCubicRootPacket source r) (j : ℕ) (hj : ¬ 7 ∣ j) :
    phaseCarrier p j ∉ ramifiedPrime ^ 2 := by
  rw [phaseCarrier_eq_uniformizer_mul_quotient]
  exact fun hm => phaseCarrierQuotient_not_mem_ramifiedPrime p j hj
    ((uniformizer_mul_mem_ramifiedPrime_sq_iff _).mp hm)

variable {p : DirectRealCubicRootPacket source r}
variable {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}

theorem phaseInverseExponent_not_seven_dvd (i : Fin 3) :
    ¬ 7 ∣ phaseInverseExponent i := by
  fin_cases i <;> norm_num [phaseInverseExponent]

theorem currentLinearCarrier_eq_phaseCarrier (c : CurrentCommonPrimeCyclotomicPacket h q) :
    currentLinearCarrier c = phaseCarrier p (phaseInverseExponent c.phase) := rfl

theorem currentLinearCarrier_mem_ramifiedPrime (c : CurrentCommonPrimeCyclotomicPacket h q) :
    currentLinearCarrier c ∈ ramifiedPrime :=
  phaseCarrier_mem_ramifiedPrime p _

theorem currentLinearCarrier_not_mem_ramifiedPrime_sq
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    currentLinearCarrier c ∉ ramifiedPrime ^ 2 :=
  phaseCarrier_not_mem_ramifiedPrime_sq p _ (phaseInverseExponent_not_seven_dvd c.phase)

end
end DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierRamification
