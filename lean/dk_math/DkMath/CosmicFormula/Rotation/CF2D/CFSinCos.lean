/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.Trig

#print "file: DkMath.CosmicFormula.Rotation.CF2D.CFSinCos"

/-!
# Cosmic-formula sine and cosine

This file gives user-facing cosmic-formula names to the two coordinate
functions of a unit-kernel family.

The functions are not defined from `Real.cos` or `Real.sin`.  They are the core
and beam coordinates of an abstract square-mass-preserving kernel family.
-/

namespace DkMath
namespace CosmicFormula
namespace Rotation
namespace CF2D

namespace KernelFamily

variable {T : Type u} {R : Type v} [AddMonoid T] [CommRing R]

/-- Cosmic-formula cosine: the core coordinate of a unit-kernel family. -/
def cfcos (F : KernelFamily T R) (t : T) : R :=
  F.C t

/-- Cosmic-formula sine: the beam coordinate of a unit-kernel family. -/
def cfsin (F : KernelFamily T R) (t : T) : R :=
  F.S t

@[simp]
theorem cfcos_eq_C (F : KernelFamily T R) (t : T) :
    F.cfcos t = F.C t := rfl

@[simp]
theorem cfsin_eq_S (F : KernelFamily T R) (t : T) :
    F.cfsin t = F.S t := rfl

@[simp]
theorem cfcos_zero (F : KernelFamily T R) : F.cfcos 0 = 1 := by
  simp [cfcos]

@[simp]
theorem cfsin_zero (F : KernelFamily T R) : F.cfsin 0 = 0 := by
  simp [cfsin]

theorem cfcos_sq_add_cfsin_sq (F : KernelFamily T R) (t : T) :
    F.cfcos t ^ 2 + F.cfsin t ^ 2 = 1 := by
  simpa [cfcos, cfsin] using F.C_sq_add_S_sq t

theorem cfcos_add (F : KernelFamily T R) (t s : T) :
    F.cfcos (t + s)
      = F.cfcos t * F.cfcos s - F.cfsin t * F.cfsin s := by
  simpa [cfcos, cfsin] using F.C_add t s

theorem cfsin_add (F : KernelFamily T R) (t s : T) :
    F.cfsin (t + s)
      = F.cfcos t * F.cfsin s + F.cfsin t * F.cfcos s := by
  simpa [cfcos, cfsin] using F.S_add t s

theorem cfcos_add_self (F : KernelFamily T R) (t : T) :
    F.cfcos (t + t) = F.cfcos t ^ 2 - F.cfsin t ^ 2 := by
  simpa [cfcos, cfsin] using F.C_add_self t

theorem cfsin_add_self (F : KernelFamily T R) (t : T) :
    F.cfsin (t + t) = 2 * F.cfcos t * F.cfsin t := by
  simpa [cfcos, cfsin] using F.S_add_self t

section AddGroup

variable {T : Type u} {R : Type v} [AddGroup T] [CommRing R]

theorem cfcos_neg (F : KernelFamily T R) (t : T) :
    F.cfcos (-t) = F.cfcos t := by
  simpa [cfcos] using F.C_neg t

theorem cfsin_neg (F : KernelFamily T R) (t : T) :
    F.cfsin (-t) = -F.cfsin t := by
  simpa [cfsin] using F.S_neg t

theorem cfcos_sub (F : KernelFamily T R) (t s : T) :
    F.cfcos (t - s)
      = F.cfcos t * F.cfcos s + F.cfsin t * F.cfsin s := by
  simpa [cfcos, cfsin] using F.C_sub t s

theorem cfsin_sub (F : KernelFamily T R) (t s : T) :
    F.cfsin (t - s)
      = F.cfsin t * F.cfcos s - F.cfcos t * F.cfsin s := by
  simpa [cfcos, cfsin] using F.S_sub t s

end AddGroup

end KernelFamily

end CF2D
end Rotation
end CosmicFormula
end DkMath
