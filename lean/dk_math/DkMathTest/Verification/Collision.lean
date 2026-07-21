/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Verification

namespace DkMathTest.Verification

/-- A concrete noninjective function used to exercise the generic API. -/
def constantBool : Bool → Bool := fun _ ↦ false

/-- The two Boolean inputs give an explicit collision for `constantBool`. -/
def constantBoolCollision :
    DkMath.Verification.CollisionCertificate constantBool where
  left := false
  right := true
  left_ne_right := by decide
  map_eq := rfl

example : ¬ Function.Injective constantBool :=
  constantBoolCollision.notInjective

example :
    ¬ ∃ g : Bool → Bool, Function.LeftInverse g constantBool :=
  constantBoolCollision.noLeftInverse

end DkMathTest.Verification

#print "file: DkMathTest.Verification.Collision"

#print axioms DkMath.Verification.CollisionCertificate.notInjective
#print axioms DkMath.Verification.CollisionCertificate.noLeftInverse
