/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.Trig

#print "file: DkMath.CosmicFormula.Rotation.CF2D.Real"

/-!
# Real bridge for the CF2D trigonometric kernel

The algebraic CF2D layer does not depend on the analytic trigonometric API.
This bridge shows that the usual real `cos` and `sin` form a concrete
`KernelFamily ℝ ℝ`.
-/

noncomputable section

namespace DkMath
namespace CosmicFormula
namespace Rotation
namespace CF2D

/-- The usual real `(cos t, sin t)` pair as a CF2D unit-kernel family. -/
noncomputable def realTrigKernelFamily : KernelFamily ℝ ℝ where
  kernel t :=
    { val := ⟨Real.cos t, Real.sin t⟩
      q2_eq_one := by
        simp [Vec.q2, Real.cos_sq_add_sin_sq t] }
  map_zero := by
    simp [Vec.one]
  map_add := by
    intro t s
    simp [Vec.star, Real.cos_add, Real.sin_add]
    ring

@[simp]
theorem realTrigKernelFamily_C (t : ℝ) :
    realTrigKernelFamily.C t = Real.cos t := rfl

@[simp]
theorem realTrigKernelFamily_S (t : ℝ) :
    realTrigKernelFamily.S t = Real.sin t := rfl

@[simp]
theorem realTrigKernelFamily_kernel_val (t : ℝ) :
    ((realTrigKernelFamily.kernel t : UnitKernel ℝ) : Vec ℝ)
      = ⟨Real.cos t, Real.sin t⟩ := rfl

end CF2D
end Rotation
end CosmicFormula
end DkMath
