/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.Basic

#print "file: DkMath.CosmicFormula.Rotation.CF2D.Failure"

/-!
# Failure examples for the CF2D rotation kernel

This file records what happens when the sign pattern of the two-component
kernel is changed.  The correct kernel cancels the opposite beam terms.  Some
nearby sign patterns preserve `q2`; others leave a residual
`± 4 * a * b * x * y`.
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

/--
A second wrong sign pattern.

Here both beam cross terms have the negative sign, so the residual is
`-4 * a * b * x * y`.
-/
def badStarMinus [Ring R] (r z : Vec R) : Vec R :=
  ⟨r.core * z.core - r.beam * z.beam,
    r.core * z.beam - r.beam * z.core⟩

@[simp]
theorem badStarMinus_core [Ring R] (r z : Vec R) :
    (badStarMinus r z).core = r.core * z.core - r.beam * z.beam := rfl

@[simp]
theorem badStarMinus_beam [Ring R] (r z : Vec R) :
    (badStarMinus r z).beam = r.core * z.beam - r.beam * z.core := rfl

theorem q2_badStarMinus [CommRing R] (a b x y : R) :
    q2 (badStarMinus (Vec.mk a b) (Vec.mk x y))
      = (a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) - 4 * a * b * x * y := by
  simp [q2, badStarMinus]
  ring

theorem q2_badStarMinus_eq_q2_mul_sub_residual [CommRing R] (r z : Vec R) :
    q2 (badStarMinus r z) = q2 r * q2 z - 4 * r.core * r.beam * z.core * z.beam := by
  cases r with
  | mk a b =>
      cases z with
      | mk x y =>
          simpa [q2] using q2_badStarMinus (R := R) a b x y

/--
The plus-minus sign pattern also preserves `q2`.

It is a nearby preserving kernel, distinct from the chosen `Vec.star` sign
convention.  Recording it keeps the failure file from implying that every sign
change necessarily breaks square-mass preservation.
-/
def starPlusMinus [Ring R] (r z : Vec R) : Vec R :=
  ⟨r.core * z.core + r.beam * z.beam,
    r.core * z.beam - r.beam * z.core⟩

@[simp]
theorem starPlusMinus_core [Ring R] (r z : Vec R) :
    (starPlusMinus r z).core = r.core * z.core + r.beam * z.beam := rfl

@[simp]
theorem starPlusMinus_beam [Ring R] (r z : Vec R) :
    (starPlusMinus r z).beam = r.core * z.beam - r.beam * z.core := rfl

theorem q2_starPlusMinus [CommRing R] (r z : Vec R) :
    q2 (starPlusMinus r z) = q2 r * q2 z := by
  cases r with
  | mk a b =>
      cases z with
      | mk x y =>
          simp [q2, starPlusMinus]
          ring

theorem starPlusMinus_eq_star_conj_left [CommRing R] (r z : Vec R) :
    starPlusMinus r z = star (conj r) z := by
  cases r with
  | mk a b =>
      cases z with
      | mk x y =>
          simp [starPlusMinus, star, conj]
          ring

end Vec

end CF2D
end Rotation
end CosmicFormula
end DkMath
