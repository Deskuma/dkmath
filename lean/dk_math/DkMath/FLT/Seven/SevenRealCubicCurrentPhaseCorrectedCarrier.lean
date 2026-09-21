/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRealCubicCurrentOrientationRatio
import DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicDegreeSixCarrier

#print "file: DkMath.FLT.Seven.SevenRealCubicCurrentPhaseCorrectedCarrier"

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt
open SevenCyclotomicDegreeSixInt
open scoped NumberField

namespace SevenRealCubic

set_option linter.style.longLine false
set_option linter.style.haveILetI false

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

section CurrentCarrier

variable {x y z : ℕ} {source : CounterexamplePack x y z}
variable {r : PrimitiveCounterexampleRamifiedProvenance source}
variable {p : DirectRealCubicRootPacket source r}
variable {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}

def phaseInverseExponent (i : Fin 3) : ℕ :=
  if i = 0 then 1 else if i = 1 then 4 else 5

theorem phaseInverseExponent_mul_mod_seven (i : Fin 3) :
    (i.val + 1) * phaseInverseExponent i ≡ 1 [MOD 7] := by
  fin_cases i <;> norm_num [phaseInverseExponent]

theorem CurrentCommonPrimeCyclotomicPacket.ratio_pow_phaseInverse
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    c.ratio ^ phaseInverseExponent c.phase = c.tau := by
  rw [c.ratio_eq, ← pow_mul]
  by_cases h0 : c.phase = 0
  · simp [h0, phaseInverseExponent]
  by_cases h1 : c.phase = 1
  · norm_num [h1, phaseInverseExponent]
    rw [show 8 = 7 + 1 by norm_num, pow_succ, c.tau_pow_seven]
    simp
  · have h2 : c.phase = 2 := by
      apply Fin.eq_of_val_eq
      omega
    norm_num [h2, phaseInverseExponent]
    rw [show 15 = 7 * 2 + 1 by norm_num, pow_add, pow_mul,
      c.tau_pow_seven]
    simp

def currentPhaseZeta
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    SevenCyclotomicDegreeSixInt.Ring :=
  zeta ^ phaseInverseExponent c.phase

theorem CurrentCommonPrimeCyclotomicPacket.currentPhaseZeta_eval
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    c.address.currentLocalEval (currentPhaseZeta c) =
      (c.tau : ZMod q) := by
  rw [currentPhaseZeta, map_pow, c.address.currentLocalEval_zeta]
  rw [c.address_ratio_eq]
  exact congrArg (fun u : (ZMod q)ˣ => (u : ZMod q))
    c.ratio_pow_phaseInverse

theorem CurrentCommonPrimeCyclotomicPacket.currentPhaseZeta_conjugate_eval
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    c.address.conjugate.currentLocalEval (currentPhaseZeta c) =
      ((c.tau⁻¹ : (ZMod q)ˣ) : ZMod q) := by
  rw [currentPhaseZeta, map_pow,
    c.address.currentLocalEval_conjugate_zeta]
  have hu : (c.ratio⁻¹) ^ phaseInverseExponent c.phase = c.tau⁻¹ := by
    rw [inv_pow, c.ratio_pow_phaseInverse]
  rw [c.address_ratio_eq]
  exact congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) hu

theorem CurrentCommonPrimeCyclotomicPacket.currentPhaseZeta_pow_seven
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    (currentPhaseZeta c) ^ 7 = 1 := by
  rw [currentPhaseZeta, ← pow_mul, Nat.mul_comm, pow_mul,
    zeta_pow_seven, one_pow]

theorem CurrentCommonPrimeCyclotomicPacket.currentPhaseZeta_ne_one
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    currentPhaseZeta c ≠ 1 := by
  intro hz
  have hdvd := orderOf_dvd_of_pow_eq_one hz
  rw [← zeta_isPrimitiveRoot.eq_orderOf] at hdvd
  by_cases h0 : c.phase = 0
  · norm_num [h0, currentPhaseZeta, phaseInverseExponent] at hdvd
  by_cases h1 : c.phase = 1
  · norm_num [h1, currentPhaseZeta, phaseInverseExponent] at hdvd
  · have h2 : c.phase = 2 := by
      apply Fin.eq_of_val_eq
      omega
    norm_num [h2, currentPhaseZeta, phaseInverseExponent] at hdvd

private theorem current_star_zeta :
    star (zeta : SevenCyclotomicDegreeSixInt.Ring) = zetaInv := by
  ext <;> simp [zeta, zetaInv]

private theorem current_star_ofReal (u : SevenRealCubicInt) :
    star (ofReal u) = ofReal u := by
  ext <;> simp [ofReal, QuadraticAlgebra.algebraMap_eq]

theorem CurrentCommonPrimeCyclotomicPacket.currentPhaseZeta_pow_star
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    star (currentPhaseZeta c) = zetaInv ^ phaseInverseExponent c.phase := by
  have hpow (n : ℕ) :
      star (zeta ^ n) = zetaInv ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
        simp [pow_succ, ih, mul_comm]
  exact hpow _

private theorem CurrentMuSevenResidueAddress.currentLocalEval_zetaInv
    (a : CurrentMuSevenResidueAddress q) :
    a.currentLocalEval zetaInv =
      ((a.ratio⁻¹ : (ZMod q)ˣ) : ZMod q) := by
  have hz : zetaInv = ofReal (alpha - 1) - zeta := by
    linear_combination zeta_add_zetaInv
  rw [hz, map_sub, a.currentLocalEval_ofReal,
    a.currentLocalEval_zeta]
  rw [map_sub, map_one, a.eval_alpha]
  have hinv : (a.ratio : ZMod q) *
      ((a.ratio⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := by
    exact congrArg (fun u : (ZMod q)ˣ => (u : ZMod q))
      (mul_inv_cancel a.ratio)
  ring

def currentLinearCarrier
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    SevenCyclotomicDegreeSixInt.Ring :=
  ofReal (rotateEquiv p.rho) -
    currentPhaseZeta c * ofReal p.rho

def currentConjugateLinearCarrier
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    SevenCyclotomicDegreeSixInt.Ring :=
  star (currentLinearCarrier c)

theorem CurrentCommonPrimeCyclotomicPacket.currentLinearCarrier_eq_zero
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    c.address.currentLocalEval (currentLinearCarrier c) = 0 := by
  letI : Fact (Nat.Prime q) := ⟨c.residue.q_prime⟩
  rw [currentLinearCarrier, map_sub, map_mul,
    c.address.currentLocalEval_ofReal,
    c.currentPhaseZeta_eval,
    c.address.currentLocalEval_ofReal,
    c.address_evalReal_eq]
  have hval := congrArg Units.val c.tau_eq
  change (c.tau : ZMod q) =
    c.residue.evalReal (rotateEquiv p.rho) /
      c.residue.evalReal p.rho at hval
  have hrel := (div_eq_iff c.residue.rho_ne_zero).mp hval.symm
  exact sub_eq_zero.mpr hrel

theorem CurrentCommonPrimeCyclotomicPacket.currentConjugateLinearCarrier_eq
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    currentConjugateLinearCarrier c =
      ofReal (rotateEquiv p.rho) -
        zetaInv ^ phaseInverseExponent c.phase * ofReal p.rho := by
  simp only [currentConjugateLinearCarrier, currentLinearCarrier,
    star_sub, star_mul, current_star_ofReal,
    c.currentPhaseZeta_pow_star]
  rw [mul_comm]

theorem CurrentCommonPrimeCyclotomicPacket.currentConjugateLinearCarrier_eq_zero
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    c.address.conjugate.currentLocalEval
        (currentConjugateLinearCarrier c) = 0 := by
  letI : Fact (Nat.Prime q) := ⟨c.residue.q_prime⟩
  rw [c.currentConjugateLinearCarrier_eq, map_sub, map_mul,
    map_pow, c.address.conjugate.currentLocalEval_zetaInv]
  simp only [CurrentMuSevenResidueAddress.currentLocalEval_ofReal]
  rw [show c.address.conjugate.ratio = c.address.ratio⁻¹ from rfl,
    inv_inv, c.address_ratio_eq]
  have hpowval :
      ((c.ratio : (ZMod q)ˣ) : ZMod q) ^ phaseInverseExponent c.phase =
        (c.tau : ZMod q) := by
    have h := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q))
      c.ratio_pow_phaseInverse
    change ((c.ratio : (ZMod q)ˣ) : ZMod q) ^
      phaseInverseExponent c.phase = (c.tau : ZMod q) at h
    exact h
  rw [hpowval]
  have haddr : c.address.conjugate.evalReal = c.address.evalReal := rfl
  rw [haddr, c.address_evalReal_eq]
  have hval := congrArg Units.val c.tau_eq
  change (c.tau : ZMod q) =
    c.residue.evalReal (rotateEquiv p.rho) /
      c.residue.evalReal p.rho at hval
  have hrel := (div_eq_iff c.residue.rho_ne_zero).mp hval.symm
  exact sub_eq_zero.mpr hrel

private theorem CurrentCommonPrimeCyclotomicPacket.tau_val_ne_inv
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    (c.tau : ZMod q) ≠
      ((c.tau⁻¹ : (ZMod q)ˣ) : ZMod q) := by
  letI : Fact (Nat.Prime q) := ⟨c.residue.q_prime⟩
  intro hval
  have hu : c.tau = c.tau⁻¹ := Units.ext hval
  have hsq : c.tau ^ 2 = 1 := by
    rw [pow_two]
    exact (congrArg (fun u : (ZMod q)ˣ => c.tau * u) hu).trans
      (mul_inv_cancel c.tau)
  have hdvd := orderOf_dvd_of_pow_eq_one hsq
  rw [c.tau_orderOf] at hdvd
  norm_num at hdvd

theorem CurrentCommonPrimeCyclotomicPacket.currentLinearCarrier_not_mem_conjugateKernel
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    currentLinearCarrier c ∉ c.address.conjugate.currentKernel := by
  letI : Fact (Nat.Prime q) := ⟨c.residue.q_prime⟩
  change c.address.conjugate.currentLocalEval
      (currentLinearCarrier c) ≠ 0
  rw [currentLinearCarrier, map_sub, map_mul,
    c.address.conjugate.currentLocalEval_ofReal,
    c.currentPhaseZeta_conjugate_eval,
    c.address.conjugate.currentLocalEval_ofReal,
    show c.address.conjugate.evalReal = c.address.evalReal from rfl,
    c.address_evalReal_eq]
  have hval := congrArg Units.val c.tau_eq
  change (c.tau : ZMod q) =
    c.residue.evalReal (rotateEquiv p.rho) /
      c.residue.evalReal p.rho at hval
  have hrel := (div_eq_iff c.residue.rho_ne_zero).mp hval.symm
  rw [hrel, ← sub_mul]
  exact mul_ne_zero (sub_ne_zero.mpr c.tau_val_ne_inv)
    c.residue.rho_ne_zero

theorem CurrentCommonPrimeCyclotomicPacket.currentConjugateLinearCarrier_not_mem_currentKernel
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    currentConjugateLinearCarrier c ∉ c.address.currentKernel := by
  letI : Fact (Nat.Prime q) := ⟨c.residue.q_prime⟩
  change c.address.currentLocalEval
      (currentConjugateLinearCarrier c) ≠ 0
  rw [c.currentConjugateLinearCarrier_eq, map_sub, map_mul,
    c.address.currentLocalEval_ofReal, map_pow,
    c.address.currentLocalEval_zetaInv]
  simp only [CurrentMuSevenResidueAddress.currentLocalEval_ofReal]
  rw [c.address_ratio_eq]
  have hu : c.ratio⁻¹ ^ phaseInverseExponent c.phase = c.tau⁻¹ := by
    rw [inv_pow, c.ratio_pow_phaseInverse]
  have hpowval :
      ((c.ratio⁻¹ : (ZMod q)ˣ) : ZMod q) ^ phaseInverseExponent c.phase =
        ((c.tau⁻¹ : (ZMod q)ˣ) : ZMod q) := by
    have h := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) hu
    change ((c.ratio⁻¹ : (ZMod q)ˣ) : ZMod q) ^
      phaseInverseExponent c.phase =
        ((c.tau⁻¹ : (ZMod q)ˣ) : ZMod q) at h
    exact h
  rw [hpowval, c.address_evalReal_eq]
  have hval := congrArg Units.val c.tau_eq
  change (c.tau : ZMod q) =
    c.residue.evalReal (rotateEquiv p.rho) /
      c.residue.evalReal p.rho at hval
  have hrel := (div_eq_iff c.residue.rho_ne_zero).mp hval.symm
  rw [hrel, ← sub_mul]
  exact mul_ne_zero (sub_ne_zero.mpr c.tau_val_ne_inv)
    c.residue.rho_ne_zero

theorem CurrentCommonPrimeCyclotomicPacket.currentLinearCarrier_mem_currentKernel
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    currentLinearCarrier c ∈ c.address.currentKernel :=
  c.currentLinearCarrier_eq_zero

theorem CurrentCommonPrimeCyclotomicPacket.currentConjugateLinearCarrier_mem_conjugateKernel
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    currentConjugateLinearCarrier c ∈ c.address.conjugate.currentKernel :=
  c.currentConjugateLinearCarrier_eq_zero

def currentCyclicAlpha (i : Fin 3) : SevenRealCubicInt :=
  if i = 0 then alpha
  else if i = 1 then alpha ^ 2 - 2 * alpha
  else -alpha ^ 2 + alpha + 2

def currentRealPairCarrier (i : Fin 3)
    (x y : SevenRealCubicInt) : SevenRealCubicInt :=
  x ^ 2 + x * y + y ^ 2 - currentCyclicAlpha i * (x * y)

theorem currentRealPairCarrier_product
    (x y : SevenRealCubicInt) :
    currentRealPairCarrier 0 x y * currentRealPairCarrier 1 x y *
        currentRealPairCarrier 2 x y = seventhQuotient x y := by
  rw [show (seventhQuotient x y : SevenRealCubicInt) =
      x ^ 6 + x ^ 5 * y + x ^ 4 * y ^ 2 + x ^ 3 * y ^ 3 +
        x ^ 2 * y ^ 4 + x * y ^ 5 + y ^ 6 by
      simp [seventhQuotient]]
  have halpha : alpha ^ 3 - 2 * alpha ^ 2 - alpha + 1 = 0 := by
    rw [alpha_cube]
    ring
  simp only [currentRealPairCarrier, currentCyclicAlpha,
    Fin.isValue, Fin.reduceEq, ↓reduceIte]
  linear_combination
    (y ^ 2 * x ^ 2 *
      (alpha ^ 2 * y * x - alpha * y ^ 2 - 2 * alpha * y * x -
        alpha * x ^ 2 + y ^ 2 + x ^ 2)) * halpha

def phaseTraceIndex (i : Fin 3) : Fin 3 :=
  if i = 0 then 0 else if i = 1 then 2 else 1

end CurrentCarrier

end SevenRealCubic
end
end DkMath.FLT.Seven
