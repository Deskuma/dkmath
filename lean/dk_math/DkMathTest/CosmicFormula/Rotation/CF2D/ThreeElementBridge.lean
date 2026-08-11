/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.ThreeElementBridge

#print "file: DkMathTest.CosmicFormula.Rotation.CF2D.ThreeElementBridge"

namespace DkMathTest
namespace CosmicFormula
namespace Rotation
namespace CF2D

open DkMath.CosmicFormula.ThreeElement
open DkMath.CosmicFormula.Rotation.CF2D

example (z : Vec ℝ) :
    squareMass z.core z.beam = Vec.q2 z :=
  cf2d_squareMass_eq_q2 z

example (r z : Vec ℝ) :
    squareMass (Vec.star r z).core (Vec.star r z).beam =
      squareMass r.core r.beam * squareMass z.core z.beam :=
  cf2d_squareMass_star r z

example (r : UnitKernel ℝ) (z : Vec ℝ) :
    squareMass
        (UnitKernel.act r z).core
        (UnitKernel.act r z).beam =
      squareMass z.core z.beam :=
  cf2d_q2_act_preserved r z

example (z : Vec ℝ) :
    squareMass
        (UnitKernel.act (UnitKernel.one ℝ) z).core
        (UnitKernel.act (UnitKernel.one ℝ) z).beam =
      squareMass z.core z.beam :=
  cf2d_q2_act_preserved (UnitKernel.one ℝ) z

example (z : Vec ℝ) :
    cf2dCoreTerm (Vec.conj z) = cf2dCoreTerm z := by
  simp

example (z : Vec ℝ) :
    cf2dGapTerm (Vec.conj z) = cf2dGapTerm z := by
  simp

example (z : Vec ℝ) :
    cf2dInteractionBeam (Vec.conj z) =
      -cf2dInteractionBeam z := by
  simp

example (z : Vec ℝ) :
    cf2dPlusWhole (Vec.conj z) = cf2dMinusWhole z := by
  simp

example (z : Vec ℝ) :
    cf2dMinusWhole (Vec.conj z) = cf2dPlusWhole z := by
  simp

example :
    cf2dInteractionBeam (Vec.mk 3 4 : Vec ℝ) = 24 := by
  norm_num [cf2dInteractionBeam, interactionBeam]

example :
    cf2dInteractionBeam (Vec.conj (Vec.mk 3 4 : Vec ℝ)) = -24 := by
  norm_num [cf2dInteractionBeam, interactionBeam, Vec.conj]

example (z : ℕ → Vec ℝ) (i : ℕ) :
    (cf2dThreeElementFlow z).squareMass i = Vec.q2 (z i) := by
  simp [cf2d_squareMass_eq_q2]

example (z : ℕ → Vec ℝ) (i : ℕ) :
    (cf2dThreeElementFlow z).interaction i =
      interactionBeam (z i).core (z i).beam :=
  rfl

#print axioms cf2d_squareMass_eq_q2
#print axioms cf2d_squareMass_star
#print axioms cf2d_q2_act_preserved
#print axioms cf2dCoreTerm_conj
#print axioms cf2dGapTerm_conj
#print axioms cf2dInteractionBeam_conj
#print axioms cf2dPlusWhole_conj_eq_minusWhole
#print axioms cf2dMinusWhole_conj_eq_plusWhole
#print axioms cf2dThreeElementFlow
#print axioms cf2dThreeElementFlow_squareMass_eq_q2

end CF2D
end Rotation
end CosmicFormula
end DkMathTest
