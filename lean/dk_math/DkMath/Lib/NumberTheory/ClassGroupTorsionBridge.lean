/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.IdealPowerFactor

#print "file: DkMath.Lib.NumberTheory.ClassGroupTorsionBridge"

/-!
# Structural class-group torsion discharge

This module supplies the small structural bridge needed by conditional ideal
power arguments.  It does not assert any arithmetic class-number statement:
the bridge applies when the class group is already subsingleton, in particular
when the coefficient ring is a principal ideal ring.
-/

namespace DkMath.Lib.NumberTheory

/-- A subsingleton class group has no nontrivial `p`-torsion, for every `p`. -/
theorem classGroupPTorsionFreeAt_of_subsingleton_classGroup
    {R : Type*} [CommRing R] [IsDomain R]
    [Subsingleton (ClassGroup R)] (p : ℕ) :
    classGroupPTorsionFreeAt R p := by
  intro a _
  exact Subsingleton.elim _ _

/-- A principal ideal ring has a subsingleton ideal class group. -/
theorem subsingleton_classGroup_of_isPrincipalIdealRing
    {R : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] : Subsingleton (ClassGroup R) := by
  rcases Fintype.card_eq_one_iff.mp (card_classGroup_eq_one (R := R)) with ⟨x, hx⟩
  exact ⟨fun a b => (hx a).trans (hx b).symm⟩

/-- Principal ideal structure discharges the class-group torsion hypothesis. -/
theorem classGroupPTorsionFreeAt_of_isPrincipalIdealRing
    {R : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] (p : ℕ) :
    classGroupPTorsionFreeAt R p := by
  have hsub : Subsingleton (ClassGroup R) :=
    subsingleton_classGroup_of_isPrincipalIdealRing (R := R)
  exact @classGroupPTorsionFreeAt_of_subsingleton_classGroup R _ _ hsub p

end DkMath.Lib.NumberTheory
