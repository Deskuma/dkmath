/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicCommonPrimeResidueOne
import DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicDegreeSixCarrier

#print "file: DkMath.FLT.Seven.SevenRealCubicCurrentCyclotomicAddress"

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt
open SevenCyclotomicDegreeSixInt
open scoped NumberField

namespace SevenRealCubic

set_option linter.style.longLine false

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-! ## Part A: a neutral current residue address -/

structure CurrentMuSevenResidueAddress (q : ℕ) where
  prime : q.Prime
  evalReal : SevenRealCubicInt →+* ZMod q
  ratio : (ZMod q)ˣ
  ratio_pow_seven : ratio ^ 7 = 1
  ratio_ne_one : ratio ≠ 1
  eval_alpha : evalReal alpha =
    1 + (ratio : ZMod q) + ((ratio⁻¹ : (ZMod q)ˣ) : ZMod q)

namespace CurrentMuSevenResidueAddress

variable {q : ℕ} (a : CurrentMuSevenResidueAddress q)

theorem ratio_orderOf : orderOf a.ratio = 7 := by
  exact orderOf_eq_prime a.ratio_pow_seven a.ratio_ne_one

private theorem ratio_quadratic_relation :
    (a.ratio : ZMod q) ^ 2 =
      -1 + (a.evalReal alpha - 1) * (a.ratio : ZMod q) := by
  have hinv : (a.ratio : ZMod q) *
      ((a.ratio⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := by
    exact congrArg Units.val (mul_inv_cancel a.ratio)
  rw [a.eval_alpha]
  linear_combination -hinv

/-! ## Part B: neutral degree-six evaluation -/

def currentLocalEval :
    SevenCyclotomicDegreeSixInt.Ring →+* ZMod q where
  toFun x :=
    a.evalReal x.re + (a.ratio : ZMod q) * a.evalReal x.im
  map_zero' := by
    change a.evalReal 0 + (a.ratio : ZMod q) * a.evalReal 0 = 0
    simp
  map_one' := by
    change a.evalReal 1 + (a.ratio : ZMod q) * a.evalReal 0 = 1
    simp
  map_add' x y := by
    simp only [QuadraticAlgebra.re_add,
      QuadraticAlgebra.im_add, map_add]
    ring
  map_mul' x y := by
    have hquad := a.ratio_quadratic_relation
    simp only [QuadraticAlgebra.re_mul,
      QuadraticAlgebra.im_mul, map_add, map_mul, map_neg,
      map_sub, map_one]
    linear_combination
      -(a.evalReal x.im * a.evalReal y.im) * hquad

@[simp] theorem currentLocalEval_ofReal
    (x : SevenRealCubicInt) :
      a.currentLocalEval (SevenCyclotomicDegreeSixInt.ofReal x) =
      a.evalReal x := by
  change a.evalReal x + (a.ratio : ZMod q) * a.evalReal 0 =
    a.evalReal x
  simp

@[simp] theorem currentLocalEval_zeta :
    a.currentLocalEval SevenCyclotomicDegreeSixInt.zeta =
      (a.ratio : ZMod q) := by
  change a.evalReal 0 + (a.ratio : ZMod q) * a.evalReal 1 =
    (a.ratio : ZMod q)
  simp

theorem currentLocalEval_surjective :
    Function.Surjective a.currentLocalEval := by
  let : Fact (Nat.Prime q) := ⟨a.prime⟩
  intro z
  refine ⟨SevenCyclotomicDegreeSixInt.ofReal
      (z.val : SevenRealCubicInt), ?_⟩
  rw [a.currentLocalEval_ofReal]
  simpa only [map_natCast] using ZMod.natCast_zmod_val z

def currentKernel :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  RingHom.ker a.currentLocalEval

theorem currentKernel_isMaximal : a.currentKernel.IsMaximal := by
  let : Fact (Nat.Prime q) := ⟨a.prime⟩
  exact RingHom.ker_isMaximal_of_surjective
    a.currentLocalEval a.currentLocalEval_surjective

theorem currentKernel_comap_ofReal :
    Ideal.comap SevenCyclotomicDegreeSixInt.ofReal a.currentKernel =
      RingHom.ker a.evalReal := by
  ext x
  change a.currentLocalEval (SevenCyclotomicDegreeSixInt.ofReal x) = 0 ↔
    a.evalReal x = 0
  rw [a.currentLocalEval_ofReal]

theorem currentKernel_comap_intCast :
    Ideal.comap
        (Int.castRingHom SevenCyclotomicDegreeSixInt.Ring)
        a.currentKernel =
      Ideal.span ({(q : ℤ)} : Set ℤ) := by
  ext z
  rw [Ideal.mem_comap, Ideal.mem_span_singleton]
  change a.currentLocalEval
      (SevenCyclotomicDegreeSixInt.ofReal
        (z : SevenRealCubicInt)) = 0 ↔
    (q : ℤ) ∣ z
  rw [a.currentLocalEval_ofReal, map_intCast,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

/-! The inverse ratio gives the conjugate current address. -/

def conjugate : CurrentMuSevenResidueAddress q where
  prime := a.prime
  evalReal := a.evalReal
  ratio := a.ratio⁻¹
  ratio_pow_seven := by
    rw [inv_pow, a.ratio_pow_seven, inv_one]
  ratio_ne_one := by
    intro h
    apply a.ratio_ne_one
    exact inv_eq_one.mp h
  eval_alpha := by
    rw [a.eval_alpha]
    simp [add_left_comm, add_comm]

theorem currentKernel_conjugate_comap_ofReal :
    Ideal.comap SevenCyclotomicDegreeSixInt.ofReal
        a.conjugate.currentKernel = RingHom.ker a.evalReal := by
  exact a.conjugate.currentKernel_comap_ofReal

theorem currentLocalEval_conjugate_zeta :
    a.conjugate.currentLocalEval SevenCyclotomicDegreeSixInt.zeta =
      ((a.ratio⁻¹ : (ZMod q)ˣ) : ZMod q) := by
  exact a.conjugate.currentLocalEval_zeta

end CurrentMuSevenResidueAddress

end SevenRealCubic
end
end DkMath.FLT.Seven
