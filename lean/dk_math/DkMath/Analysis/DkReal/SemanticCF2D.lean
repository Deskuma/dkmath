/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.DkReal.Semantic
import DkMath.CosmicFormula.Rotation.CF2D.Basic

#print "file: DkMath.Analysis.DkReal.SemanticCF2D"

/-!
# Semantic CF2D bridge for nonnegative DkMath reals

This module is the first CF2D consumer of the semantic real interpretation.
It maps both coordinates of a nonnegative DkMath vector to Mathlib `Real` and
shows that the quadratic invariant

`q2(core, beam) = core^2 + beam^2`

is preserved by that interpretation.

The bridge uses only the semiring laws already proved for `semanticValue`.
It does not require subtraction, decidable comparison, order reflection, or
any analytic theorem about trigonometric functions.

At the bridge boundary, squares are normalized to products. This avoids
identifying CF2D's abstract `Semiring` power instance with the representation
power operation used to construct DkMath interval powers.
-/

namespace DkMath.Analysis.DkNNRealQ

open DkMath.CosmicFormula.Rotation.CF2D

noncomputable section

/-- Interpret both coordinates of a CF2D vector as Mathlib real numbers. -/
def semanticVec (z : Vec DkNNRealQ) : Vec ℝ :=
  ⟨semanticValue z.core, semanticValue z.beam⟩

/-- Semantic interpretation of the core coordinate. -/
@[simp]
theorem semanticVec_core (z : Vec DkNNRealQ) :
    (semanticVec z).core = semanticValue z.core := rfl

/-- Semantic interpretation of the beam coordinate. -/
@[simp]
theorem semanticVec_beam (z : Vec DkNNRealQ) :
    (semanticVec z).beam = semanticValue z.beam := rfl

/--
Semantic evaluation preserves the CF2D quadratic invariant.

Thus the internal square mass and the ordinary real square mass describe the
same quantity after interpretation.
-/
theorem semanticValue_q2 (z : Vec DkNNRealQ) :
    semanticValue (Vec.q2 z) = Vec.q2 (semanticVec z) := by
  simp only [Vec.q2, semanticVec, semanticValue_add, pow_two,
    semanticValue_mul]

/-- Coordinate form of semantic preservation of the quadratic invariant. -/
theorem semanticValue_q2_eq (z : Vec DkNNRealQ) :
    semanticValue (Vec.q2 z) =
      semanticValue z.core ^ 2 + semanticValue z.beam ^ 2 := by
  simpa [Vec.q2, semanticVec] using semanticValue_q2 z

/--
A nonnegative DkMath unit kernel determines a real CF2D unit kernel by
coordinatewise semantic interpretation.
-/
def semanticUnitKernel (r : UnitKernel DkNNRealQ) : UnitKernel ℝ :=
  ⟨semanticVec (r : Vec DkNNRealQ), by
    rw [← semanticValue_q2]
    simp⟩

/-- The underlying vector of a semantic unit kernel is the semantic vector. -/
@[simp]
theorem semanticUnitKernel_val (r : UnitKernel DkNNRealQ) :
    (semanticUnitKernel r : Vec ℝ) = semanticVec (r : Vec DkNNRealQ) := rfl

/-- The interpreted core coordinate remains nonnegative. -/
theorem semanticUnitKernel_core_nonneg (r : UnitKernel DkNNRealQ) :
    0 ≤ (semanticUnitKernel r : Vec ℝ).core :=
  semanticValue_nonneg (r : Vec DkNNRealQ).core

/-- The interpreted beam coordinate remains nonnegative. -/
theorem semanticUnitKernel_beam_nonneg (r : UnitKernel DkNNRealQ) :
    0 ≤ (semanticUnitKernel r : Vec ℝ).beam :=
  semanticValue_nonneg (r : Vec DkNNRealQ).beam

/--
The coordinates of an interpreted nonnegative unit kernel satisfy the real
Pythagorean identity.
-/
theorem semanticUnitKernel_sq_add_sq (r : UnitKernel DkNNRealQ) :
    semanticValue (r : Vec DkNNRealQ).core ^ 2
      + semanticValue (r : Vec DkNNRealQ).beam ^ 2 = 1 := by
  simpa [Vec.q2, semanticVec] using
    (UnitKernel.coe_q2 (semanticUnitKernel r))

/--
Act on a real CF2D vector by first interpreting a nonnegative DkMath unit
kernel as a real unit kernel.

Subtraction enters only in this real-side action. It is not added to
`DkNNRealQ`.
-/
def semanticAct (r : UnitKernel DkNNRealQ) (z : Vec ℝ) : Vec ℝ :=
  UnitKernel.act (semanticUnitKernel r) z

/-- Core-coordinate formula for the transported real action. -/
@[simp]
theorem semanticAct_core (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    (semanticAct r z).core =
      semanticValue (r : Vec DkNNRealQ).core * z.core
        - semanticValue (r : Vec DkNNRealQ).beam * z.beam := rfl

/-- Beam-coordinate formula for the transported real action. -/
@[simp]
theorem semanticAct_beam (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    (semanticAct r z).beam =
      semanticValue (r : Vec DkNNRealQ).core * z.beam
        + semanticValue (r : Vec DkNNRealQ).beam * z.core := rfl

/--
The transported real action preserves the CF2D quadratic invariant.

This is the first direct consumer of an existing real-side CF2D action
theorem. No new analytic argument is needed after the unit-kernel transport.
-/
theorem semanticAct_q2 (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    Vec.q2 (semanticAct r z) = Vec.q2 z :=
  UnitKernel.q2_act (semanticUnitKernel r) z

/-- The transported action is a square-mass-preserving real map. -/
theorem semanticAct_preservesQ2 (r : UnitKernel DkNNRealQ) :
    PreservesQ2 (semanticAct r) :=
  semanticAct_q2 r

/--
Real-side product of two independently interpreted nonnegative DkMath
kernels.

The product is deliberately formed after semantic transport, where signed
coordinates and subtraction are already available.
-/
def semanticKernelProduct
    (r s : UnitKernel DkNNRealQ) : UnitKernel ℝ :=
  UnitKernel.star (semanticUnitKernel r) (semanticUnitKernel s)

/--
Successive transported actions are action by the real-side product kernel.

This records composition without asserting that a corresponding source-level
product exists in the nonnegative semiring.
-/
theorem semanticAct_comp
    (r s : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    semanticAct r (semanticAct s z) =
      UnitKernel.act (semanticKernelProduct r s) z := by
  exact
    (UnitKernel.act_star
      (semanticUnitKernel r) (semanticUnitKernel s) z).symm

/-- Transported action restricted to a real square-mass level set. -/
def semanticActLevel
    (r : UnitKernel DkNNRealQ) {rho2 : ℝ}
    (z : LevelSet ℝ rho2) : LevelSet ℝ rho2 :=
  LevelSet.act (semanticUnitKernel r) z

/-- The value of a transported level-set action is the ordinary semantic action. -/
@[simp]
theorem semanticActLevel_val
    (r : UnitKernel DkNNRealQ) {rho2 : ℝ}
    (z : LevelSet ℝ rho2) :
    (semanticActLevel r z).1 = semanticAct r z.1 := rfl

/-- Successive transported actions compose on every real level set. -/
theorem semanticActLevel_comp
    (r s : UnitKernel DkNNRealQ) {rho2 : ℝ}
    (z : LevelSet ℝ rho2) :
    semanticActLevel r (semanticActLevel s z) =
      LevelSet.act (semanticKernelProduct r s) z := by
  apply Subtype.ext
  exact semanticAct_comp r s z.1

/--
Real-side inverse kernel of an interpreted nonnegative DkMath kernel.

The inverse generally leaves the first quadrant, so it is intentionally not
claimed to come from a `DkNNRealQ` unit kernel.
-/
def semanticInverseKernel (r : UnitKernel DkNNRealQ) : UnitKernel ℝ :=
  UnitKernel.conj (semanticUnitKernel r)

/-- Real-side action by the inverse kernel. -/
def semanticInverseAct (r : UnitKernel DkNNRealQ) (z : Vec ℝ) : Vec ℝ :=
  UnitKernel.act (semanticInverseKernel r) z

/-- The inverse action cancels a transported action on the left. -/
@[simp]
theorem semanticInverseAct_semanticAct
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    semanticInverseAct r (semanticAct r z) = z := by
  rw [semanticInverseAct, semanticAct, ← UnitKernel.act_star]
  rw [semanticInverseKernel, UnitKernel.conj_star]
  exact UnitKernel.act_one z

/-- The inverse action cancels a transported action on the right. -/
@[simp]
theorem semanticAct_semanticInverseAct
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    semanticAct r (semanticInverseAct r z) = z := by
  rw [semanticInverseAct, semanticAct, ← UnitKernel.act_star]
  rw [semanticInverseKernel, UnitKernel.star_conj]
  exact UnitKernel.act_one z

/-- Every transported action is a bijection of the real CF2D plane. -/
theorem semanticAct_bijective (r : UnitKernel DkNNRealQ) :
    Function.Bijective (semanticAct r) := by
  refine Function.bijective_iff_has_inverse.mpr ?_
  exact ⟨semanticInverseAct r, semanticInverseAct_semanticAct r,
    semanticAct_semanticInverseAct r⟩

/-- Real-side inverse action restricted to a square-mass level set. -/
def semanticInverseActLevel
    (r : UnitKernel DkNNRealQ) {rho2 : ℝ}
    (z : LevelSet ℝ rho2) : LevelSet ℝ rho2 :=
  LevelSet.act (semanticInverseKernel r) z

/-- The inverse level-set action cancels the transported level-set action. -/
@[simp]
theorem semanticInverseActLevel_semanticActLevel
    (r : UnitKernel DkNNRealQ) {rho2 : ℝ}
    (z : LevelSet ℝ rho2) :
    semanticInverseActLevel r (semanticActLevel r z) = z := by
  apply Subtype.ext
  exact semanticInverseAct_semanticAct r z.1

/-- The transported level-set action cancels its inverse. -/
@[simp]
theorem semanticActLevel_semanticInverseActLevel
    (r : UnitKernel DkNNRealQ) {rho2 : ℝ}
    (z : LevelSet ℝ rho2) :
    semanticActLevel r (semanticInverseActLevel r z) = z := by
  apply Subtype.ext
  exact semanticAct_semanticInverseAct r z.1

/-- Every transported action is a bijection of each real square-mass level set. -/
theorem semanticActLevel_bijective
    (r : UnitKernel DkNNRealQ) {rho2 : ℝ} :
    Function.Bijective (semanticActLevel r : LevelSet ℝ rho2 → LevelSet ℝ rho2) := by
  refine Function.bijective_iff_has_inverse.mpr ?_
  exact ⟨semanticInverseActLevel r,
    semanticInverseActLevel_semanticActLevel r,
    semanticActLevel_semanticInverseActLevel r⟩

/-- The transported action bundled as an equivalence of the real CF2D plane. -/
def semanticActEquiv (r : UnitKernel DkNNRealQ) : Vec ℝ ≃ Vec ℝ where
  toFun := semanticAct r
  invFun := semanticInverseAct r
  left_inv := semanticInverseAct_semanticAct r
  right_inv := semanticAct_semanticInverseAct r

/-- Applying the bundled plane equivalence is semantic action. -/
@[simp]
theorem semanticActEquiv_apply
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    semanticActEquiv r z = semanticAct r z := rfl

/-- The transported action bundled as an equivalence of a real level set. -/
def semanticActLevelEquiv
    (r : UnitKernel DkNNRealQ) {rho2 : ℝ} :
    LevelSet ℝ rho2 ≃ LevelSet ℝ rho2 where
  toFun := semanticActLevel r
  invFun := semanticInverseActLevel r
  left_inv := semanticInverseActLevel_semanticActLevel r
  right_inv := semanticActLevel_semanticInverseActLevel r

/-- Applying the bundled level-set equivalence is semantic level-set action. -/
@[simp]
theorem semanticActLevelEquiv_apply
    (r : UnitKernel DkNNRealQ) {rho2 : ℝ}
    (z : LevelSet ℝ rho2) :
    semanticActLevelEquiv r z = semanticActLevel r z := rfl

/-- Every finite iterate of a transported action preserves square mass. -/
theorem semanticAct_iterate_q2
    (r : UnitKernel DkNNRealQ) (n : ℕ) (z : Vec ℝ) :
    Vec.q2 ((semanticAct r)^[n] z) = Vec.q2 z := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (semanticAct_q2 r _).trans ih

/-- Every finite iterate of a transported action is bijective. -/
theorem semanticAct_iterate_bijective
    (r : UnitKernel DkNNRealQ) (n : ℕ) :
    Function.Bijective ((semanticAct r)^[n]) :=
  (semanticAct_bijective r).iterate n

/-- Every finite iterate of a level-set action is bijective. -/
theorem semanticActLevel_iterate_bijective
    (r : UnitKernel DkNNRealQ) {rho2 : ℝ} (n : ℕ) :
    Function.Bijective
      ((semanticActLevel r : LevelSet ℝ rho2 → LevelSet ℝ rho2)^[n]) :=
  (semanticActLevel_bijective r).iterate n

/-- Forward orbit of a real vector under a transported DkMath kernel. -/
def semanticOrbit
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (n : ℕ) : Vec ℝ :=
  (semanticAct r)^[n] z

/-- Every point of a transported orbit has the initial square mass. -/
theorem semanticOrbit_q2
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (n : ℕ) :
    Vec.q2 (semanticOrbit r z n) = Vec.q2 z :=
  semanticAct_iterate_q2 r n z

/-- Forward orbit of a point inside a fixed real square-mass level set. -/
def semanticLevelOrbit
    (r : UnitKernel DkNNRealQ) {rho2 : ℝ}
    (z : LevelSet ℝ rho2) (n : ℕ) : LevelSet ℝ rho2 :=
  (semanticActLevel r)^[n] z

/-- The underlying vector of a level-set orbit is the corresponding plane orbit. -/
theorem semanticLevelOrbit_val
    (r : UnitKernel DkNNRealQ) {rho2 : ℝ}
    (z : LevelSet ℝ rho2) (n : ℕ) :
    (semanticLevelOrbit r z n).1 = semanticOrbit r z.1 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [semanticLevelOrbit, semanticOrbit,
        Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact congrArg (semanticAct r) ih

/-- A real vector is periodic when a finite semantic orbit returns to it. -/
def SemanticPeriodic
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (n : ℕ) : Prop :=
  Function.IsPeriodicPt (semanticAct r) n z

/-- Periodicity is exactly return of the explicitly named semantic orbit. -/
theorem semanticPeriodic_iff
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (n : ℕ) :
    SemanticPeriodic r z n ↔ semanticOrbit r z n = z :=
  Iff.rfl

/-- A point of a real level set is periodic under the restricted action. -/
def SemanticLevelPeriodic
    (r : UnitKernel DkNNRealQ) {rho2 : ℝ}
    (z : LevelSet ℝ rho2) (n : ℕ) : Prop :=
  Function.IsPeriodicPt (semanticActLevel r) n z

/--
Level-set periodicity is equivalent to periodicity of the underlying plane
orbit.
-/
theorem semanticLevelPeriodic_iff
    (r : UnitKernel DkNNRealQ) {rho2 : ℝ}
    (z : LevelSet ℝ rho2) (n : ℕ) :
    SemanticLevelPeriodic r z n ↔ SemanticPeriodic r z.1 n := by
  constructor
  · intro h
    change (semanticActLevel r)^[n] z = z at h
    change semanticOrbit r z.1 n = z.1
    rw [← semanticLevelOrbit_val]
    exact congrArg Subtype.val h
  · intro h
    change semanticOrbit r z.1 n = z.1 at h
    change (semanticActLevel r)^[n] z = z
    apply Subtype.ext
    change (semanticLevelOrbit r z n).1 = z.1
    rw [semanticLevelOrbit_val]
    exact h

/--
A transported kernel has finite action order `n` when its `n`-fold real
action is the identity on the whole plane.
-/
def SemanticFiniteOrder
    (r : UnitKernel DkNNRealQ) (n : ℕ) : Prop :=
  (semanticAct r)^[n] = id

/-- Finite action order is equivalent to every real vector being periodic. -/
theorem semanticFiniteOrder_iff
    (r : UnitKernel DkNNRealQ) (n : ℕ) :
    SemanticFiniteOrder r n ↔ ∀ z : Vec ℝ, SemanticPeriodic r z n := by
  constructor
  · intro h z
    rw [SemanticPeriodic, Function.IsPeriodicPt, h]
    rfl
  · intro h
    funext z
    exact h z

/-- A finite-order transported kernel makes every level-set point periodic. -/
theorem semanticLevelPeriodic_of_finiteOrder
    {r : UnitKernel DkNNRealQ} {n : ℕ}
    (h : SemanticFiniteOrder r n) {rho2 : ℝ}
    (z : LevelSet ℝ rho2) :
    SemanticLevelPeriodic r z n := by
  rw [semanticLevelPeriodic_iff]
  exact (semanticFiniteOrder_iff r n).mp h z.1

/-- Periodicity persists at every multiple of a known period. -/
theorem semanticPeriodic_of_dvd
    {r : UnitKernel DkNNRealQ} {z : Vec ℝ} {m n : ℕ}
    (h : SemanticPeriodic r z m) (hmn : m ∣ n) :
    SemanticPeriodic r z n :=
  Function.IsPeriodicPt.trans_dvd h hmn

/-
[TODO: semantic-cf2d/signed-kernel] Source-level `Vec.star` and
`KernelFamily` require a ring because their core coordinate uses subtraction.
Keep the source in the nonnegative semiring until a signed DkReal layer is
introduced; do not manufacture subtraction merely to mirror the real target.
-/

end

end DkMath.Analysis.DkNNRealQ
