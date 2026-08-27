/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.ThreeElement.Assimilation
import DkMath.CosmicFormula.Rotation.CF2D.Basic

#print "file: DkMath.CosmicFormula.Rotation.CF2D.ThreeElementBridge"

/-!
# CF2D bridge for three-element assimilation

This module interprets the two coordinates of `CF2D.Vec` as the base values of
the general three-element algebra.

`Vec.beam` remains the second CF2D coordinate. The distinct quantity
`interactionBeam` is the quadratic cross term `2 * z.core * z.beam` generated
from both coordinates. The two notions are never identified.

The bridge connects CF2D square-mass preservation and conjugation to the
general Core/interaction-Beam/Gap API. It contains no RH-, zeta-, complex
phase-, angle-, or trigonometric-specific assumption.
-/

namespace DkMath
namespace CosmicFormula
namespace Rotation
namespace CF2D

open DkMath.CosmicFormula.ThreeElement

/-- The Core term read from the first CF2D coordinate. -/
def cf2dCoreTerm (z : Vec ℝ) : ℝ :=
  coreTerm z.core

/--
The interaction Beam generated from both CF2D coordinates.

This is not the coordinate `Vec.beam`; it is the cross term `2*core*beam`.
-/
def cf2dInteractionBeam (z : Vec ℝ) : ℝ :=
  interactionBeam z.core z.beam

/-- The Gap term read from the second CF2D coordinate. -/
def cf2dGapTerm (z : Vec ℝ) : ℝ :=
  gapTerm z.beam

/-- The plus whole attached to a CF2D state. -/
def cf2dPlusWhole (z : Vec ℝ) : ℝ :=
  plusWhole z.core z.beam

/-- The minus whole attached to a CF2D state. -/
def cf2dMinusWhole (z : Vec ℝ) : ℝ :=
  minusWhole z.core z.beam

/-- The general three-element square mass is exactly the existing CF2D `q2`. -/
theorem cf2d_squareMass_eq_q2 (z : Vec ℝ) :
    squareMass z.core z.beam = Vec.q2 z :=
  rfl

/-- CF2D `star` transports the multiplicative `q2` law to square mass. -/
theorem cf2d_squareMass_star (r z : Vec ℝ) :
    squareMass (Vec.star r z).core (Vec.star r z).beam =
      squareMass r.core r.beam * squareMass z.core z.beam := by
  calc
    squareMass (Vec.star r z).core (Vec.star r z).beam =
        Vec.q2 (Vec.star r z) :=
      cf2d_squareMass_eq_q2 (Vec.star r z)
    _ = Vec.q2 r * Vec.q2 z := Vec.q2_star r z
    _ = squareMass r.core r.beam * squareMass z.core z.beam := by
      rw [← cf2d_squareMass_eq_q2 r, ← cf2d_squareMass_eq_q2 z]

/-- A CF2D unit-kernel action preserves the general three-element square mass. -/
theorem cf2d_q2_act_preserved
    (r : UnitKernel ℝ) (z : Vec ℝ) :
    squareMass
        (UnitKernel.act r z).core
        (UnitKernel.act r z).beam =
      squareMass z.core z.beam := by
  calc
    squareMass
        (UnitKernel.act r z).core
        (UnitKernel.act r z).beam =
        Vec.q2 (UnitKernel.act r z) :=
      cf2d_squareMass_eq_q2 (UnitKernel.act r z)
    _ = Vec.q2 z := UnitKernel.q2_act r z
    _ = squareMass z.core z.beam :=
      (cf2d_squareMass_eq_q2 z).symm

/-- CF2D conjugation leaves the Core term unchanged. -/
@[simp]
theorem cf2dCoreTerm_conj (z : Vec ℝ) :
    cf2dCoreTerm (Vec.conj z) = cf2dCoreTerm z := by
  simp [cf2dCoreTerm, coreTerm]

/-- CF2D conjugation leaves the Gap term unchanged. -/
@[simp]
theorem cf2dGapTerm_conj (z : Vec ℝ) :
    cf2dGapTerm (Vec.conj z) = cf2dGapTerm z := by
  simp [cf2dGapTerm, gapTerm, pow_two]

/-- CF2D conjugation flips only the sign of the interaction Beam. -/
@[simp]
theorem cf2dInteractionBeam_conj (z : Vec ℝ) :
    cf2dInteractionBeam (Vec.conj z) =
      -cf2dInteractionBeam z := by
  simp [cf2dInteractionBeam, interactionBeam]

/-- Conjugation exchanges the plus whole with the minus whole. -/
@[simp]
theorem cf2dPlusWhole_conj_eq_minusWhole (z : Vec ℝ) :
    cf2dPlusWhole (Vec.conj z) =
      cf2dMinusWhole z := by
  simp [cf2dPlusWhole, cf2dMinusWhole, plusWhole, minusWhole,
    sub_eq_add_neg]

/-- Conjugation exchanges the minus whole with the plus whole. -/
@[simp]
theorem cf2dMinusWhole_conj_eq_plusWhole (z : Vec ℝ) :
    cf2dMinusWhole (Vec.conj z) =
      cf2dPlusWhole z := by
  simp [cf2dPlusWhole, cf2dMinusWhole, plusWhole, minusWhole,
    sub_eq_add_neg]

/-- Build the general three-element flow from a sequence of CF2D states. -/
def cf2dThreeElementFlow
    {ι : Type*} (z : ι → Vec ℝ) :
    ThreeElementFlow ι :=
  quadraticFlow
    (fun i => (z i).core)
    (fun i => (z i).beam)

@[simp]
theorem cf2dThreeElementFlow_core
    {ι : Type*} (z : ι → Vec ℝ) (i : ι) :
    (cf2dThreeElementFlow z).core i = cf2dCoreTerm (z i) :=
  rfl

@[simp]
theorem cf2dThreeElementFlow_interaction
    {ι : Type*} (z : ι → Vec ℝ) (i : ι) :
    (cf2dThreeElementFlow z).interaction i =
      cf2dInteractionBeam (z i) :=
  rfl

@[simp]
theorem cf2dThreeElementFlow_gap
    {ι : Type*} (z : ι → Vec ℝ) (i : ι) :
    (cf2dThreeElementFlow z).gap i = cf2dGapTerm (z i) :=
  rfl

@[simp]
theorem cf2dThreeElementFlow_squareMass
    {ι : Type*} (z : ι → Vec ℝ) (i : ι) :
    (cf2dThreeElementFlow z).squareMass i =
      squareMass (z i).core (z i).beam :=
  rfl

@[simp]
theorem cf2dThreeElementFlow_squareMass_eq_q2
    {ι : Type*} (z : ι → Vec ℝ) (i : ι) :
    (cf2dThreeElementFlow z).squareMass i = Vec.q2 (z i) :=
  cf2d_squareMass_eq_q2 (z i)

@[simp]
theorem cf2dThreeElementFlow_plusWhole
    {ι : Type*} (z : ι → Vec ℝ) (i : ι) :
    (cf2dThreeElementFlow z).plusWhole i = cf2dPlusWhole (z i) :=
  rfl

@[simp]
theorem cf2dThreeElementFlow_minusWhole
    {ι : Type*} (z : ι → Vec ℝ) (i : ι) :
    (cf2dThreeElementFlow z).minusWhole i = cf2dMinusWhole (z i) :=
  rfl

end CF2D
end Rotation
end CosmicFormula
end DkMath
