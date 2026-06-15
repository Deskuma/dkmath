/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.Basic

#print "file: DkMath.CosmicFormula.Rotation.CF2D.Failure"

/-!
# Failure examples for the CF2D rotation kernel

This file records what breaks when the sign pattern of the two-component kernel
is changed.  The correct kernel cancels the opposite beam terms.  The plus-plus
kernel leaves a residual `4 * a * b * x * y`, so it does not preserve `q2` in
general.
-/

namespace DkMath
namespace CosmicFormula
namespace Rotation
namespace CF2D

namespace Vec

variable {R : Type u}

/--
A deliberately wrong two-component product.

The sign in the first coordinate is changed from `a*x - b*y` to `a*x + b*y`.
-/
def badStarPlus [Ring R] (r z : Vec R) : Vec R :=
  ⟨r.core * z.core + r.beam * z.beam,
    r.core * z.beam + r.beam * z.core⟩

@[simp]
theorem badStarPlus_core [Ring R] (r z : Vec R) :
    (badStarPlus r z).core = r.core * z.core + r.beam * z.beam := rfl

@[simp]
theorem badStarPlus_beam [Ring R] (r z : Vec R) :
    (badStarPlus r z).beam = r.core * z.beam + r.beam * z.core := rfl

/--
The wrong sign pattern leaves a residual beam term.

For the correct `star`, this residual is absent and `q2` is multiplicative.
-/
theorem q2_badStarPlus [CommRing R] (a b x y : R) :
    q2 (badStarPlus (Vec.mk a b) (Vec.mk x y))
      = (a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) + 4 * a * b * x * y := by
  simp [q2, badStarPlus]
  ring

theorem q2_badStarPlus_eq_q2_mul_add_residual [CommRing R] (r z : Vec R) :
    q2 (badStarPlus r z) = q2 r * q2 z + 4 * r.core * r.beam * z.core * z.beam := by
  cases r with
  | mk a b =>
      cases z with
      | mk x y =>
          simpa [q2] using q2_badStarPlus (R := R) a b x y

end Vec

end CF2D
end Rotation
end CosmicFormula
end DkMath

