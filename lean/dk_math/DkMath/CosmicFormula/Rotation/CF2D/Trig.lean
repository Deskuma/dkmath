/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.Basic

#print "file: DkMath.CosmicFormula.Rotation.CF2D.Trig"

/-!
# Coordinate functions of a 2D unit-kernel family

This file captures the "trigonometric functions arise from conservation"
part of the construction.

Instead of importing or using `Real.sin` and `Real.cos`, we start from an
abstract additive family of unit kernels. Its first and second coordinates are
named `C` and `S`, and their basic identities follow from the unit condition
and the kernel product law.
-/

namespace DkMath
namespace CosmicFormula
namespace Rotation
namespace CF2D

/--
An additive-monoid family of square-mass-one kernels.

The parameter type `T` can later be instantiated by `ℝ`, `ℤ`, a formal time
monoid, or another additive parameter space. Continuity or analytic structure is
deliberately not part of this algebraic layer.
-/
structure KernelFamily (T : Type u) (R : Type v) [AddMonoid T] [CommRing R] where
  kernel : T → UnitKernel R
  map_zero : ((kernel 0 : UnitKernel R) : Vec R) = Vec.one R
  map_add : ∀ t s, ((kernel (t + s) : UnitKernel R) : Vec R)
    = Vec.star ((kernel t : UnitKernel R) : Vec R) ((kernel s : UnitKernel R) : Vec R)

namespace KernelFamily

variable {T : Type u} {R : Type v} [AddMonoid T] [CommRing R]

/-- Core coordinate of a unit-kernel family. -/
def C (F : KernelFamily T R) (t : T) : R :=
  ((F.kernel t : UnitKernel R) : Vec R).core

/-- Beam coordinate of a unit-kernel family. -/
def S (F : KernelFamily T R) (t : T) : R :=
  ((F.kernel t : UnitKernel R) : Vec R).beam

@[simp]
theorem kernel_q2 (F : KernelFamily T R) (t : T) :
    Vec.q2 (((F.kernel t : UnitKernel R) : Vec R)) = 1 :=
  UnitKernel.coe_q2 (F.kernel t)

theorem kernel_zero (F : KernelFamily T R) :
    ((F.kernel 0 : UnitKernel R) : Vec R) = Vec.one R :=
  F.map_zero

@[simp]
theorem C_zero (F : KernelFamily T R) : F.C 0 = 1 := by
  have h := congrArg Vec.core F.kernel_zero
  simpa [C, Vec.one] using h

@[simp]
theorem S_zero (F : KernelFamily T R) : F.S 0 = 0 := by
  have h := congrArg Vec.beam F.kernel_zero
  simpa [S, Vec.one] using h

@[simp]
theorem C_add_zero (F : KernelFamily T R) (t : T) : F.C (t + 0) = F.C t := by
  simp

@[simp]
theorem S_add_zero (F : KernelFamily T R) (t : T) : F.S (t + 0) = F.S t := by
  simp

@[simp]
theorem C_zero_add (F : KernelFamily T R) (t : T) : F.C (0 + t) = F.C t := by
  simp

@[simp]
theorem S_zero_add (F : KernelFamily T R) (t : T) : F.S (0 + t) = F.S t := by
  simp

/--
The basic identity for the coordinate functions:
`C(t)^2 + S(t)^2 = 1`.
-/
theorem C_sq_add_S_sq (F : KernelFamily T R) (t : T) :
    F.C t ^ 2 + F.S t ^ 2 = 1 := by
  simpa [C, S, Vec.q2] using F.kernel_q2 t

/-- Kernel composition law in coordinate form. -/
theorem kernel_add (F : KernelFamily T R) (t s : T) :
    ((F.kernel (t + s) : UnitKernel R) : Vec R)
      = Vec.star (((F.kernel t : UnitKernel R) : Vec R))
          (((F.kernel s : UnitKernel R) : Vec R)) :=
  F.map_add t s

/--
Core addition law:
`C(t+s) = C(t) * C(s) - S(t) * S(s)`.
-/
theorem C_add (F : KernelFamily T R) (t s : T) :
    F.C (t + s) = F.C t * F.C s - F.S t * F.S s := by
  have h := congrArg Vec.core (F.kernel_add t s)
  simpa [C, S, Vec.star] using h

/--
Beam addition law:
`S(t+s) = C(t) * S(s) + S(t) * C(s)`.
-/
theorem S_add (F : KernelFamily T R) (t s : T) :
    F.S (t + s) = F.C t * F.S s + F.S t * F.C s := by
  have h := congrArg Vec.beam (F.kernel_add t s)
  simpa [C, S, Vec.star] using h

end KernelFamily

end CF2D
end Rotation
end CosmicFormula
end DkMath
