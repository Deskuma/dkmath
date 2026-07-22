/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.Trig

#print "file: DkMath.CosmicFormula.Rotation.CF2D.KernelPower"

/-!
# Standard multiplicative interface for CF2D unit kernels

This module exposes the existing unit-kernel operations through Lean's standard
commutative-group interface.  The mathematical implementation remains the
pre-geometric CF2D algebra:

* multiplication is `UnitKernel.star`;
* the neutral element is `UnitKernel.one`;
* inversion is `UnitKernel.conj`.

Keeping this interface in a separate module lets existing code continue to use
the explicit CF2D vocabulary while later finite-order arguments can use powers,
`orderOf`, and the ordinary group API.
-/

namespace DkMath.CosmicFormula.Rotation.CF2D

namespace UnitKernel

variable {R : Type u}

/--
CF2D unit kernels form a commutative group under the preservation-kernel
product.  Conjugation is the inverse because square mass is exactly one.
-/
instance [CommRing R] : CommGroup (UnitKernel R) where
  mul := star
  one := one R
  inv := conj
  mul_assoc := star_assoc
  one_mul := one_star
  mul_one := star_one
  inv_mul_cancel := conj_star
  mul_comm := star_comm

/-- Standard multiplication is definitionally the CF2D kernel product. -/
@[simp]
theorem mul_eq_star [CommRing R] (r s : UnitKernel R) :
    r * s = star r s := rfl

/-- The standard neutral element is definitionally the neutral CF2D kernel. -/
@[simp]
theorem one_eq_unitKernelOne [CommRing R] :
    (1 : UnitKernel R) = one R := rfl

/-- Standard inversion is definitionally CF2D kernel conjugation. -/
@[simp]
theorem inv_eq_conj [CommRing R] (r : UnitKernel R) :
    r⁻¹ = conj r := rfl

end UnitKernel

namespace UnitKernel

variable {R : Type u} [CommRing R]

/--
Action by the `n`th kernel power is the `n`-fold iterate of action by the
original kernel.

This is the generic algebraic bridge from finite kernel products to repeated
boundary actions.  It does not use coordinates or a geometric interpretation.
-/
theorem pow_act (r : UnitKernel R) (n : ℕ) (z : Vec R) :
    act (r ^ n) z = (act r)^[n] z := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, mul_eq_star, act_star, ih, Function.iterate_succ_apply]

end UnitKernel

namespace KernelFamily

variable {T : Type u} {R : Type v} [AddMonoid T] [CommRing R]

/--
Natural additive repetition of a parameter is carried to the corresponding
natural power of its unit kernel.

This is the finite-repetition law `K(n • t) = K(t) ^ n`.  It follows only
from the additive kernel-family axioms and the CF2D preservation-kernel group;
no trigonometric or Euclidean input is present.
-/
theorem kernel_nsmul (F : KernelFamily T R) (n : ℕ) (t : T) :
    F.kernel (n • t) = (F.kernel t) ^ n := by
  induction n with
  | zero => simpa using F.kernel_zero_one
  | succ n ih =>
      rw [succ_nsmul, F.kernel_add_star, ih, pow_succ, UnitKernel.mul_eq_star]

end KernelFamily

section InterfaceChecks

#check (1 : UnitKernel ℝ)
#check fun r : UnitKernel ℝ => r ^ 5
#check fun r : UnitKernel ℝ => orderOf r
#check KernelFamily.kernel_nsmul
#check UnitKernel.pow_act

end InterfaceChecks

end DkMath.CosmicFormula.Rotation.CF2D
