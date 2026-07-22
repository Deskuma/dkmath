/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.KernelPower

#print "file: DkMath.CosmicFormula.Rotation.CF2D.CycleDivision"

/-!
# Abstract cycle division for CF2D kernel families

This file turns an additive parameter division into finite kernel and action
return.  Its hypotheses keep the three logical layers explicit:

* `k • step = period` is a statement in the additive parameter;
* `F.kernel period = 1` declares that the period has neutral kernel;
* the conclusions are kernel-power and action-iterate return.

No real number, trigonometric function, angle, circle, or polygon is used.
-/

namespace DkMath.CosmicFormula.Rotation.CF2D

namespace KernelFamily

variable {T : Type u} {R : Type v} [AddMonoid T] [CommRing R]

/--
A step whose `k`-fold additive repetition reaches a neutral-kernel period has
neutral `k`th kernel power.

Positivity of `k` is not required at this abstract layer: once the repetition
equation and neutral-period hypothesis are supplied, the conclusion is purely
algebraic.
-/
theorem kernel_pow_eq_one_of_nsmul_eq_period
    (F : KernelFamily T R) {k : ℕ} {step period : T}
    (hstep : k • step = period)
    (hperiod : F.kernel period = 1) :
    (F.kernel step) ^ k = 1 := by
  rw [← F.kernel_nsmul k step, hstep, hperiod]

/--
Finite iteration of a kernel-family action is action by the kernel at the
corresponding natural additive repetition.
-/
theorem iterate_act_eq_act_nsmul
    (F : KernelFamily T R) (n : ℕ) (t : T) (z : Vec R) :
    (UnitKernel.act (F.kernel t))^[n] z =
      UnitKernel.act (F.kernel (n • t)) z := by
  rw [← UnitKernel.pow_act, F.kernel_nsmul]

/--
An abstract cycle division returns every two-component state after `k`
iterations of the one-step action.
-/
theorem iterate_act_eq_id_of_nsmul_eq_period
    (F : KernelFamily T R) {k : ℕ} {step period : T}
    (hstep : k • step = period)
    (hperiod : F.kernel period = 1) :
    (UnitKernel.act (F.kernel step))^[k] = id := by
  funext z
  rw [← UnitKernel.pow_act,
    F.kernel_pow_eq_one_of_nsmul_eq_period hstep hperiod]
  simp

/--
Finite iteration of the induced action on a square-mass level set is the
level-set action at the naturally repeated parameter.
-/
theorem iterate_actLevel_eq_actLevel_nsmul
    (F : KernelFamily T R) (n : ℕ) (t : T) {rho2 : R}
    (z : LevelSet R rho2) :
    (F.actLevel t)^[n] z = F.actLevel (n • t) z := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih, ← F.actLevel_add, succ_nsmul]

/--
The abstract cycle division returns every point of every square-mass level set
after `k` induced action steps.
-/
theorem iterate_actLevel_eq_id_of_nsmul_eq_period
    (F : KernelFamily T R) {k : ℕ} {step period : T}
    (hstep : k • step = period)
    (hperiod : F.kernel period = 1) {rho2 : R} :
    (F.actLevel step : LevelSet R rho2 → LevelSet R rho2)^[k] = id := by
  funext z
  rw [F.iterate_actLevel_eq_actLevel_nsmul, hstep]
  apply Subtype.ext
  simp [actLevel, hperiod]

end KernelFamily

section InterfaceChecks

#check KernelFamily.kernel_pow_eq_one_of_nsmul_eq_period
#check KernelFamily.iterate_act_eq_id_of_nsmul_eq_period
#check KernelFamily.iterate_actLevel_eq_id_of_nsmul_eq_period

end InterfaceChecks

end DkMath.CosmicFormula.Rotation.CF2D
