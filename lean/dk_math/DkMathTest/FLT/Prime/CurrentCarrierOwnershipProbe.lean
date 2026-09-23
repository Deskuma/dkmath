/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRealCubicCurrentSelectedFactorUniqueness
import DkMath.Lib.NumberTheory.ConjugatePrimeIdealOwnership

#print "file: DkMathTest.FLT.Prime.CurrentCarrierOwnershipProbe"

open DkMath DkMath.FLT.Seven DkMath.FLT.Seven.SevenRealCubic
open scoped NumberField

namespace DkMathTest.FLT.Prime

noncomputable section

namespace SevenRealCubic

open DkMath.FLT.Seven.SevenRealCubicInt
open DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

section Probe

variable {x y z : ℕ} {source : CounterexamplePack x y z}
variable {r : PrimitiveCounterexampleRamifiedProvenance source}
variable {p : DirectRealCubicRootPacket source r}
variable {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}

private theorem currentLocalEval_conjugate_star_local
    (a : CurrentMuSevenResidueAddress q)
    (u : SevenCyclotomicDegreeSixInt.Ring) :
    a.conjugate.currentLocalEval (star u) = a.currentLocalEval u := by
  change
    a.evalReal (u.re + (alpha - 1) * u.im) +
        ((a.ratio⁻¹ : (ZMod q)ˣ) : ZMod q) * a.evalReal (-u.im) =
      a.evalReal u.re + (a.ratio : ZMod q) * a.evalReal u.im
  rw [map_add, map_mul, map_sub, map_neg, a.eval_alpha, map_one]
  ring

private theorem map_star_currentKernel_eq_conjugateKernel_local
    (a : CurrentMuSevenResidueAddress q) :
    Ideal.map (starRingEnd SevenCyclotomicDegreeSixInt.Ring) a.currentKernel =
      a.conjugate.currentKernel := by
  have hsurjective : Function.Surjective
      (starRingEnd SevenCyclotomicDegreeSixInt.Ring) := by
    intro u
    refine ⟨star u, ?_⟩
    simp only [starRingEnd_apply, star_star]
  ext u
  rw [Ideal.mem_map_iff_of_surjective _ hsurjective]
  constructor
  · rintro ⟨v, hv, rfl⟩
    change a.currentLocalEval v = 0 at hv
    change a.conjugate.currentLocalEval (star v) = 0
    rw [currentLocalEval_conjugate_star_local]
    exact hv
  · intro hu
    change a.conjugate.currentLocalEval u = 0 at hu
    refine ⟨star u, ?_, ?_⟩
    · change a.currentLocalEval (star u) = 0
      have hstar := currentLocalEval_conjugate_star_local a (star u)
      rw [star_star] at hstar
      rw [← hstar]
      exact hu
    · simp only [starRingEnd_apply, star_star]

private theorem currentConjugateLinearCarrier_mem_conjugateKernel_pow_of_mem_current_local
    (c : CurrentCommonPrimeCyclotomicPacket h q) {k : ℕ}
    (hmem : currentLinearCarrier c ∈ c.address.currentKernel ^ k) :
    currentConjugateLinearCarrier c ∈ c.address.conjugate.currentKernel ^ k := by
  have hmap := Ideal.mem_map_of_mem
    (starRingEnd SevenCyclotomicDegreeSixInt.Ring) hmem
  change star (currentLinearCarrier c) ∈
    Ideal.map (starRingEnd SevenCyclotomicDegreeSixInt.Ring)
      (c.address.currentKernel ^ k) at hmap
  rw [Ideal.map_pow, map_star_currentKernel_eq_conjugateKernel_local] at hmap
  simpa only [currentConjugateLinearCarrier] using hmap

private theorem selectedRealPairCarrier_not_mem_evalRealKernel_pow_succ_local
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    selectedRealPairCarrier c ∉ (RingHom.ker c.residue.evalReal) ^
      (14 * currentIdealPrimeMultiplicity c.residue.Q
        (currentPrincipalIdeal h.squareRefinement.quotientSquareRoot) + 1) := by
  intro hmem
  have hmap := Ideal.mem_map_of_mem modelEquivRingOfIntegers hmem
  have hmapEq :
      Ideal.map modelEquivRingOfIntegers
          ((RingHom.ker c.residue.evalReal) ^
            (14 * currentIdealPrimeMultiplicity c.residue.Q
              (currentPrincipalIdeal h.squareRefinement.quotientSquareRoot) + 1)) =
        c.residue.Q ^
          (14 * currentIdealPrimeMultiplicity c.residue.Q
            (currentPrincipalIdeal h.squareRefinement.quotientSquareRoot) + 1) := by
    rw [Ideal.map_pow, c.residue.evalReal_kernel_eq,
      Ideal.map_comap_eq_self_of_equiv]
  rw [hmapEq] at hmap
  exact c.selectedRealPairCarrier_not_mem_Q_pow_succ hmap

theorem currentLinearCarrier_not_mem_currentKernel_pow_succ
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    currentLinearCarrier c ∉ c.address.currentKernel ^
      (14 * currentIdealPrimeMultiplicity c.residue.Q
        (currentPrincipalIdeal h.squareRefinement.quotientSquareRoot) + 1) := by
  apply DkMath.Lib.NumberTheory.not_mem_primePower_succ_of_conjugate_norm_cutoff
    SevenCyclotomicDegreeSixInt.ofReal
    (RingHom.ker c.residue.evalReal)
    c.address.currentKernel c.address.conjugate.currentKernel
    (currentLinearCarrier c) (currentConjugateLinearCarrier c)
    (selectedRealPairCarrier c)
    (14 * currentIdealPrimeMultiplicity c.residue.Q
      (currentPrincipalIdeal h.squareRefinement.quotientSquareRoot))
  · intro hmem
    exact currentConjugateLinearCarrier_mem_conjugateKernel_pow_of_mem_current_local c hmem
  · exact c.currentLinearCarrier_mul_conjugate
  · rw [Ideal.map_pow, c.residueFiberIdeal_eq_currentConjugateProduct, mul_pow]
  · simp only [SevenCyclotomicDegreeSixInt.ofReal,
      Ideal.comap_map_eq_self_of_faithfullyFlat]
  · exact selectedRealPairCarrier_not_mem_evalRealKernel_pow_succ_local c

#print axioms DkMath.Lib.NumberTheory.not_mem_primePower_succ_of_conjugate_norm_cutoff
#print axioms DkMathTest.FLT.Prime.SevenRealCubic.currentLinearCarrier_not_mem_currentKernel_pow_succ

end Probe

end SevenRealCubic

end

end DkMathTest.FLT.Prime
