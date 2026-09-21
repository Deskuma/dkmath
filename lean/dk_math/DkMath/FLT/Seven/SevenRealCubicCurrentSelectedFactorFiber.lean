/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRealCubicCurrentPhaseCorrectedCarrier

#print "file: DkMath.FLT.Seven.SevenRealCubicCurrentSelectedFactorFiber"

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt
open SevenCyclotomicDegreeSixInt
open scoped NumberField

namespace SevenRealCubic

set_option linter.style.longLine false
set_option linter.style.haveILetI false

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

section CurrentSelectedFactor

variable {x y z : ℕ} {source : CounterexamplePack x y z}
variable {r : PrimitiveCounterexampleRamifiedProvenance source}
variable {p : DirectRealCubicRootPacket source r}
variable {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}

private theorem zetaInv_eq_pow_six :
    zetaInv = zeta ^ 6 := by
  calc
    zetaInv = 1 * zetaInv := by simp
    _ = (zeta ^ 7) * zetaInv := by rw [zeta_pow_seven]
    _ = zeta ^ 6 * (zeta * zetaInv) := by ring
    _ = zeta ^ 6 := by rw [zeta_mul_zetaInv]; simp

private theorem zeta_pow_four_add_inv_pow_four :
    zeta ^ 4 + zetaInv ^ 4 =
      ofReal (-alpha ^ 2 + alpha + 1) := by
  let t : SevenCyclotomicDegreeSixInt.Ring := ofReal (alpha - 1)
  have hq : zeta ^ 2 - t * zeta + 1 = 0 := by
    simpa [t] using zeta_quadratic_relation
  have ht : t ^ 3 + t ^ 2 - 2 * t - 1 = 0 := by
    simpa [t] using ofReal_alphaSubOne_cubic_relation
  have hrhs : ofReal (-alpha ^ 2 + alpha + 1) =
      1 - t ^ 2 - t := by
    simp only [t, map_pow, map_neg, map_add, map_sub, map_one]
    ring
  rw [zetaInv_eq_pow_six, ← pow_mul]
  rw [show 6 * 4 = 7 * 3 + 3 by norm_num,
    pow_add, pow_mul, zeta_pow_seven]
  simp only [one_pow, one_mul]
  rw [hrhs]
  linear_combination
    (zeta ^ 2 + (t + 1) * zeta + (t ^ 2 + t - 1)) * hq + zeta * ht

private theorem zeta_pow_five_add_inv_pow_five :
    zeta ^ 5 + zetaInv ^ 5 =
      ofReal (alpha ^ 2 - 2 * alpha - 1) := by
  let t : SevenCyclotomicDegreeSixInt.Ring := ofReal (alpha - 1)
  have hq : zeta ^ 2 - t * zeta + 1 = 0 := by
    simpa [t] using zeta_quadratic_relation
  have ht : t ^ 3 + t ^ 2 - 2 * t - 1 = 0 := by
    simpa [t] using ofReal_alphaSubOne_cubic_relation
  have hrhs : ofReal (alpha ^ 2 - 2 * alpha - 1) =
      t ^ 2 - 2 := by
    rw [show 2 * alpha = alpha * 2 by ring]
    simp only [t, map_pow, map_sub, map_one, map_mul, map_ofNat]
    ring
  rw [zetaInv_eq_pow_six, ← pow_mul]
  rw [show 6 * 5 = 7 * 4 + 2 by norm_num,
    pow_add, pow_mul, zeta_pow_seven]
  simp only [one_pow, one_mul]
  rw [hrhs]
  linear_combination
    (zeta ^ 3 + t * zeta ^ 2 + (t ^ 2 - 1) * zeta +
        (t ^ 3 - 2 * t) + 1) * hq +
      ((t - 1) * zeta - 1) * ht

theorem CurrentCommonPrimeCyclotomicPacket.currentPhaseTrace_identity
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    currentPhaseZeta c +
        zetaInv ^ phaseInverseExponent c.phase =
      ofReal (currentCyclicAlpha (phaseTraceIndex c.phase) - 1) := by
  by_cases h0 : c.phase = 0
  · simp [h0, currentPhaseZeta, phaseInverseExponent,
      phaseTraceIndex, currentCyclicAlpha, zeta_add_zetaInv]
  by_cases h1 : c.phase = 1
  · simp [h1, currentPhaseZeta, phaseInverseExponent,
      phaseTraceIndex, currentCyclicAlpha,
      zeta_pow_four_add_inv_pow_four, ofReal,
      Algebra.algebraMap_eq_smul_one]
    ring
  · have h2 : c.phase = 2 := by
      apply Fin.eq_of_val_eq
      omega
    simp [h2, currentPhaseZeta, phaseInverseExponent,
      phaseTraceIndex, currentCyclicAlpha,
      zeta_pow_five_add_inv_pow_five]

def selectedRealPairCarrier
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    SevenRealCubicInt :=
  currentRealPairCarrier (phaseTraceIndex c.phase)
    (rotateEquiv p.rho) p.rho

private theorem currentPhaseZeta_mul_inverse_phaseZeta
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    currentPhaseZeta c * zetaInv ^ phaseInverseExponent c.phase = 1 := by
  rw [currentPhaseZeta, ← mul_pow, zeta_mul_zetaInv, one_pow]

theorem CurrentCommonPrimeCyclotomicPacket.currentLinearCarrier_mul_conjugate
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    currentLinearCarrier c * currentConjugateLinearCarrier c =
      ofReal (selectedRealPairCarrier c) := by
  rw [c.currentConjugateLinearCarrier_eq]
  have hsum := c.currentPhaseTrace_identity
  have hprod := currentPhaseZeta_mul_inverse_phaseZeta c
  simp only [currentLinearCarrier]
  simp only [selectedRealPairCarrier, currentRealPairCarrier]
  calc
    (ofReal (rotateEquiv p.rho) -
        currentPhaseZeta c * ofReal p.rho) *
        (ofReal (rotateEquiv p.rho) -
          zetaInv ^ phaseInverseExponent c.phase * ofReal p.rho) =
      ofReal (rotateEquiv p.rho) ^ 2 -
        (currentPhaseZeta c + zetaInv ^ phaseInverseExponent c.phase) *
          (ofReal (rotateEquiv p.rho) * ofReal p.rho) +
        (currentPhaseZeta c *
          zetaInv ^ phaseInverseExponent c.phase) *
          ofReal p.rho ^ 2 := by
            ring
    _ = ofReal (selectedRealPairCarrier c) := by
      rw [hprod, hsum]
      simp [selectedRealPairCarrier, currentRealPairCarrier]
      ring

theorem CurrentCommonPrimeCyclotomicPacket.currentLinearCarrier_norm
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    QuadraticAlgebra.norm (currentLinearCarrier c) =
      selectedRealPairCarrier c := by
  have hnorm :=
    QuadraticAlgebra.algebraMap_norm_eq_mul_star
      (currentLinearCarrier c)
  change ofReal (QuadraticAlgebra.norm (currentLinearCarrier c)) =
    currentLinearCarrier c * currentConjugateLinearCarrier c at hnorm
  rw [c.currentLinearCarrier_mul_conjugate] at hnorm
  exact ofReal_injective hnorm

theorem CurrentCommonPrimeCyclotomicPacket.selectedRealPairCarrier_eval_eq_zero
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    c.residue.evalReal (selectedRealPairCarrier c) = 0 := by
  have hzero := congrArg c.address.currentLocalEval
    c.currentLinearCarrier_mul_conjugate
  rw [map_mul, c.currentLinearCarrier_eq_zero, zero_mul] at hzero
  rw [c.address.currentLocalEval_ofReal, c.address_evalReal_eq] at hzero
  exact hzero.symm

theorem CurrentCommonPrimeCyclotomicPacket.selectedRealPairCarrier_mem_Q
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    modelEquivRingOfIntegers (selectedRealPairCarrier c) ∈ c.residue.Q := by
  exact (c.residue.evalReal_zero_iff _).mp
    c.selectedRealPairCarrier_eval_eq_zero

theorem currentRealPairCarrier_product_direct
    (p : DirectRealCubicRootPacket source r) :
    currentRealPairCarrier 0 (rotateEquiv p.rho) p.rho *
        currentRealPairCarrier 1 (rotateEquiv p.rho) p.rho *
        currentRealPairCarrier 2 (rotateEquiv p.rho) p.rho =
      directOrbitQuotient p := by
  exact currentRealPairCarrier_product _ _

end CurrentSelectedFactor

namespace CurrentMuSevenResidueAddress

variable {q : ℕ} (a : CurrentMuSevenResidueAddress q)

def realPrimeFiberIdeal :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  Ideal.map SevenCyclotomicDegreeSixInt.ofReal
    (RingHom.ker a.evalReal)

theorem ratio_val_ne_inv :
    (a.ratio : ZMod q) ≠
      ((a.ratio⁻¹ : (ZMod q)ˣ) : ZMod q) := by
  intro hratioVal
  have hratioUnits : a.ratio = a.ratio⁻¹ := Units.ext hratioVal
  have hsq : a.ratio ^ 2 = 1 := by
    rw [pow_two]
    exact (congrArg (fun u => a.ratio * u) hratioUnits).trans
      (mul_inv_cancel a.ratio)
  have hdiv := orderOf_dvd_of_pow_eq_one hsq
  rw [a.ratio_orderOf] at hdiv
  norm_num at hdiv

theorem currentKernel_ne_conjugateKernel :
    a.currentKernel ≠ a.conjugate.currentKernel := by
  letI : Fact (Nat.Prime q) := ⟨a.prime⟩
  let carrier : SevenCyclotomicDegreeSixInt.Ring :=
    zeta - ofReal (a.ratio.val.val : SevenRealCubicInt)
  have hmem : carrier ∈ a.currentKernel := by
    change a.currentLocalEval carrier = 0
    change a.currentLocalEval
      (zeta - ofReal (a.ratio.val.val : SevenRealCubicInt)) = 0
    rw [map_sub, a.currentLocalEval_zeta,
      a.currentLocalEval_ofReal, map_natCast]
    exact sub_eq_zero.mpr (ZMod.natCast_zmod_val a.ratio.val).symm
  have hnot : carrier ∉ a.conjugate.currentKernel := by
    intro hmem
    change a.conjugate.currentLocalEval carrier = 0 at hmem
    change a.conjugate.currentLocalEval
      (zeta - ofReal (a.ratio.val.val : SevenRealCubicInt)) = 0 at hmem
    rw [map_sub, a.currentLocalEval_conjugate_zeta,
      a.conjugate.currentLocalEval_ofReal, map_natCast] at hmem
    have hzero :
        ((a.ratio⁻¹ : (ZMod q)ˣ) : ZMod q) =
          (a.ratio : ZMod q) := by
      calc
        ((a.ratio⁻¹ : (ZMod q)ˣ) : ZMod q) =
            ↑(a.ratio.val).val := sub_eq_zero.mp hmem
        _ = (a.ratio : ZMod q) :=
          ZMod.natCast_zmod_val a.ratio.val
    exact a.ratio_val_ne_inv hzero.symm
  intro heq
  exact hnot (heq ▸ hmem)

theorem currentKernel_sup_conjugateKernel :
    a.currentKernel ⊔ a.conjugate.currentKernel = ⊤ :=
  a.currentKernel_isMaximal.coprime_of_ne
    a.conjugate.currentKernel_isMaximal
    a.currentKernel_ne_conjugateKernel

theorem realPrimeFiberIdeal_le_conjugateProduct :
    a.realPrimeFiberIdeal ≤
      a.currentKernel * a.conjugate.currentKernel := by
  have hleft : a.realPrimeFiberIdeal ≤ a.currentKernel := by
    rw [realPrimeFiberIdeal, Ideal.map_le_iff_le_comap,
      a.currentKernel_comap_ofReal]
  have hright : a.realPrimeFiberIdeal ≤ a.conjugate.currentKernel := by
    rw [realPrimeFiberIdeal, Ideal.map_le_iff_le_comap,
      a.currentKernel_conjugate_comap_ofReal]
  rw [Ideal.mul_eq_inf_of_coprime a.currentKernel_sup_conjugateKernel]
  exact le_inf hleft hright

theorem conjugatePrimeProduct_le_realPrimeFiberIdeal :
    a.currentKernel * a.conjugate.currentKernel ≤
      a.realPrimeFiberIdeal := by
  letI : Fact (Nat.Prime q) := ⟨a.prime⟩
  rw [Ideal.mul_eq_inf_of_coprime a.currentKernel_sup_conjugateKernel]
  intro u hu
  have hcurrent : a.currentLocalEval u = 0 :=
    (RingHom.mem_ker.mp hu.1)
  have hconjugate : a.conjugate.currentLocalEval u = 0 :=
    (RingHom.mem_ker.mp hu.2)
  change a.evalReal u.re + (a.ratio : ZMod q) *
      a.evalReal u.im = 0 at hcurrent
  change a.evalReal u.re +
      ((a.ratio⁻¹ : (ZMod q)ˣ) : ZMod q) *
        a.evalReal u.im = 0 at hconjugate
  have himEq :
      ((a.ratio : ZMod q) -
          ((a.ratio⁻¹ : (ZMod q)ˣ) : ZMod q)) *
        a.evalReal u.im = 0 := by
    have hmul :
        (a.ratio : ZMod q) * a.evalReal u.im =
          ((a.ratio⁻¹ : (ZMod q)ˣ) : ZMod q) *
            a.evalReal u.im := by
      exact add_left_cancel (hcurrent.trans hconjugate.symm)
    rw [sub_mul, hmul, sub_self]
  have him : a.evalReal u.im = 0 :=
    (mul_eq_zero.mp himEq).resolve_left
      (sub_ne_zero.mpr a.ratio_val_ne_inv)
  have hre : a.evalReal u.re = 0 := by
    rw [him, mul_zero, add_zero] at hcurrent
    exact hcurrent
  rw [realPrimeFiberIdeal]
  have hreMap : ofReal u.re ∈
      Ideal.map ofReal (RingHom.ker a.evalReal) :=
    Ideal.mem_map_of_mem ofReal hre
  have himMap : ofReal u.im ∈
      Ideal.map ofReal (RingHom.ker a.evalReal) :=
    Ideal.mem_map_of_mem ofReal him
  rw [show u = ofReal u.re + zeta * ofReal u.im by
    ext <;> simp [ofReal, zeta]]
  exact Ideal.add_mem _ hreMap
    (Ideal.mul_mem_left _ zeta himMap)

theorem realPrimeFiberIdeal_eq_conjugateProduct :
    a.realPrimeFiberIdeal =
      a.currentKernel * a.conjugate.currentKernel :=
  le_antisymm a.realPrimeFiberIdeal_le_conjugateProduct
    a.conjugatePrimeProduct_le_realPrimeFiberIdeal

end CurrentMuSevenResidueAddress

section CurrentPacketFiberAndOwnership

variable {x y z : ℕ} {source : CounterexamplePack x y z}
variable {r : PrimitiveCounterexampleRamifiedProvenance source}
variable {p : DirectRealCubicRootPacket source r}
variable {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}

theorem CurrentCommonPrimeCyclotomicPacket.realPrimeFiberIdeal_eq_currentConjugateProduct
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    c.address.realPrimeFiberIdeal =
      c.address.currentKernel * c.address.conjugate.currentKernel :=
  c.address.realPrimeFiberIdeal_eq_conjugateProduct

theorem CurrentCommonPrimeCyclotomicPacket.residueFiberIdeal_eq_currentConjugateProduct
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    Ideal.map ofReal (RingHom.ker c.residue.evalReal) =
      c.address.currentKernel * c.address.conjugate.currentKernel := by
  simpa [CurrentMuSevenResidueAddress.realPrimeFiberIdeal,
    c.address_evalReal_eq] using
    c.realPrimeFiberIdeal_eq_currentConjugateProduct

theorem CurrentCommonPrimeCyclotomicPacket.currentKernel_dvd_span_currentLinearCarrier
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    c.address.currentKernel ∣
      Ideal.span {currentLinearCarrier c} := by
  rw [Ideal.dvd_iff_le]
  exact (Ideal.span_singleton_le_iff_mem _).mpr
    c.currentLinearCarrier_mem_currentKernel

theorem CurrentCommonPrimeCyclotomicPacket.conjugateKernel_dvd_span_currentConjugateLinearCarrier
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    c.address.conjugate.currentKernel ∣
      Ideal.span {currentConjugateLinearCarrier c} := by
  rw [Ideal.dvd_iff_le]
  exact (Ideal.span_singleton_le_iff_mem _).mpr
    c.currentConjugateLinearCarrier_mem_conjugateKernel

end CurrentPacketFiberAndOwnership

end SevenRealCubic
end
end DkMath.FLT.Seven
