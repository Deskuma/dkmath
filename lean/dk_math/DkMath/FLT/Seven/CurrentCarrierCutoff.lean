/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRealCubicCurrentSelectedFactorUniqueness
import DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicDegreeSixPID
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

#print "file: DkMath.FLT.Seven.CurrentCarrierCutoff"

/-! Exact upper cutoff for the current carrier, using its own conjugate
address and checked real-prime fibre. No historical carrier is identified. -/
namespace DkMath.FLT.Seven.SevenRealCubic
open SevenRealCubicInt SevenCyclotomicDegreeSixInt
open scoped NumberField
noncomputable section

namespace CurrentMuSevenResidueAddress
variable {q : ℕ} (a : CurrentMuSevenResidueAddress q)

theorem currentLocalEval_conjugate_star (w : SevenCyclotomicDegreeSixInt.Ring) :
    a.conjugate.currentLocalEval (star w) = a.currentLocalEval w := by
  change a.evalReal (star w).re + (↑a.ratio⁻¹ : ZMod q) * a.evalReal (star w).im =
    a.evalReal w.re + (↑a.ratio : ZMod q) * a.evalReal w.im
  simp only [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star,
    map_add, map_mul, map_sub, map_one, map_neg]
  rw [a.eval_alpha]
  ring

theorem map_star_currentKernel :
    Ideal.map (starRingEnd SevenCyclotomicDegreeSixInt.Ring) a.currentKernel =
      a.conjugate.currentKernel := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro w hw
    change a.conjugate.currentLocalEval (star w) = 0
    rw [a.currentLocalEval_conjugate_star]
    exact hw
  · intro w hw
    have hs : star w ∈ a.currentKernel := by
      change a.currentLocalEval (star w) = 0
      change a.conjugate.currentLocalEval w = 0 at hw
      have he := a.currentLocalEval_conjugate_star (star w)
      rw [star_star] at he
      exact he.symm.trans hw
    have hm := Ideal.mem_map_of_mem (starRingEnd SevenCyclotomicDegreeSixInt.Ring) hs
    change star (star w) ∈ _ at hm
    simpa only [star_star] using hm

end CurrentMuSevenResidueAddress

variable {x y z : ℕ} {source : CounterexamplePack x y z}
variable {r : PrimitiveCounterexampleRamifiedProvenance source}
variable {p : DirectRealCubicRootPacket source r}
variable {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}

private theorem realKernel_eq_map_Q (c : CurrentCommonPrimeCyclotomicPacket h q) :
    RingHom.ker c.residue.evalReal = Ideal.map modelEquivRingOfIntegers.symm.toRingHom c.residue.Q := by
  change RingHom.ker c.residue.evalReal =
    Ideal.map (modelEquivRingOfIntegers.symm : _ →+* _) c.residue.Q
  rw [Ideal.map_comap_of_equiv]
  ext w
  exact c.residue.evalReal_zero_iff w

/-- The star action sends powers of the current kernel to powers of the
current conjugate kernel. -/
theorem CurrentCommonPrimeCyclotomicPacket.current_star_mem_conjugate_power
    (c : CurrentCommonPrimeCyclotomicPacket h q) (k : ℕ)
    (hm : currentLinearCarrier c ∈ c.address.currentKernel ^ k) :
    currentConjugateLinearCarrier c ∈ c.address.conjugate.currentKernel ^ k := by
  have ht := Ideal.mem_map_of_mem (starRingEnd SevenCyclotomicDegreeSixInt.Ring) hm
  rw [Ideal.map_pow, c.address.map_star_currentKernel] at ht
  exact ht

/-- Orientation places the complete real exponent on the current linear factor. -/
theorem CurrentCommonPrimeCyclotomicPacket.currentLinearCarrier_mem_power
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    currentLinearCarrier c ∈ c.address.currentKernel ^
      (14 * currentIdealPrimeMultiplicity c.residue.Q
        (currentPrincipalIdeal h.squareRefinement.quotientSquareRoot)) := by
  let k := 14 * currentIdealPrimeMultiplicity c.residue.Q
    (currentPrincipalIdeal h.squareRefinement.quotientSquareRoot)
  have hf : selectedRealPairCarrier c ∈ (RingHom.ker c.residue.evalReal) ^ k := by
    rw [realKernel_eq_map_Q c, ← Ideal.map_pow]
    have hm := Ideal.mem_map_of_mem modelEquivRingOfIntegers.symm.toRingHom
      c.selectedRealPairCarrier_mem_Q_pow
    simpa only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.symm_apply_apply] using hm
  have hm := Ideal.mem_map_of_mem ofReal hf
  rw [Ideal.map_pow, c.residueFiberIdeal_eq_currentConjugateProduct, mul_pow] at hm
  have hp : ofReal (selectedRealPairCarrier c) ∈ c.address.currentKernel ^ k :=
    Ideal.mul_le_left hm
  rw [← c.currentLinearCarrier_mul_conjugate] at hp
  let := c.address.currentKernel_isMaximal
  exact (Ideal.IsPrime.mem_pow_mul c.address.currentKernel hp).resolve_right
    c.currentConjugateLinearCarrier_not_mem_currentKernel

/-- The real exact exponent is an upper cutoff in the actual current
oriented kernel, by conjugation and faithful-flat contraction. -/
theorem CurrentCommonPrimeCyclotomicPacket.currentLinearCarrier_not_mem_power_succ
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    currentLinearCarrier c ∉ c.address.currentKernel ^
      (14 * currentIdealPrimeMultiplicity c.residue.Q
        (currentPrincipalIdeal h.squareRefinement.quotientSquareRoot) + 1) := by
  intro hm
  let k := 14 * currentIdealPrimeMultiplicity c.residue.Q
    (currentPrincipalIdeal h.squareRefinement.quotientSquareRoot) + 1
  have hc := c.current_star_mem_conjugate_power k hm
  have hp := Ideal.mul_mem_mul hm hc
  have he : currentLinearCarrier c * currentConjugateLinearCarrier c ∈
      Ideal.map ofReal ((RingHom.ker c.residue.evalReal) ^ k) := by
    rw [Ideal.map_pow, c.residueFiberIdeal_eq_currentConjugateProduct, mul_pow]
    exact hp
  rw [c.currentLinearCarrier_mul_conjugate] at he
  have hf : selectedRealPairCarrier c ∈ (RingHom.ker c.residue.evalReal) ^ k := by
    change selectedRealPairCarrier c ∈ Ideal.comap ofReal
      (Ideal.map ofReal ((RingHom.ker c.residue.evalReal) ^ k)) at he
    simpa only [ofReal, Ideal.comap_map_eq_self_of_faithfullyFlat] using he
  rw [realKernel_eq_map_Q c, ← Ideal.map_pow] at hf
  have hf' : modelEquivRingOfIntegers (selectedRealPairCarrier c) ∈ c.residue.Q ^ k := by
    have heq := Ideal.mem_map_of_equiv modelEquivRingOfIntegers.symm (I := c.residue.Q ^ k) (selectedRealPairCarrier c)
    obtain ⟨w, hw, hew⟩ := heq.mp hf
    have hw' : w = modelEquivRingOfIntegers (selectedRealPairCarrier c) := by
      apply modelEquivRingOfIntegers.symm.injective
      rw [RingEquiv.symm_apply_apply]
      exact hew
    simpa only [hw'] using hw
  exact c.selectedRealPairCarrier_not_mem_Q_pow_succ hf'

/-- Exact current oriented valuation, expressed without identifying a historical carrier. -/
theorem CurrentCommonPrimeCyclotomicPacket.currentLinearCarrier_mem_power_iff
    (c : CurrentCommonPrimeCyclotomicPacket h q) (k : ℕ) :
    currentLinearCarrier c ∈ c.address.currentKernel ^ k ↔
      k ≤ 14 * currentIdealPrimeMultiplicity c.residue.Q
        (currentPrincipalIdeal h.squareRefinement.quotientSquareRoot) := by
  constructor
  · intro hm
    by_contra hn
    have hk : 14 * currentIdealPrimeMultiplicity c.residue.Q
        (currentPrincipalIdeal h.squareRefinement.quotientSquareRoot) + 1 ≤ k := by omega
    exact c.currentLinearCarrier_not_mem_power_succ (Ideal.pow_le_pow_right hk hm)
  · intro hk
    exact Ideal.pow_le_pow_right hk c.currentLinearCarrier_mem_power

end
end DkMath.FLT.Seven.SevenRealCubic
