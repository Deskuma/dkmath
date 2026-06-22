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

The logical order of this file is deliberately pre-geometric:

1. `q2` is a boundary detector selecting a conserved level set;
2. `star` specifies how kernels compose;
3. `act_star` represents that composition as successive actions;
4. faithfulness recovers kernel equality from equality of actions;
5. coordinate nonnegativity removes roots outside the transported boundary.

At this stage no circle, orthogonal coordinate frame, angle, full turn, or
degree measure has been defined. In particular, the primary exact-order-four
result is an algebraic statement about a `q2`-preserving action. Its later
interpretation as a quarter-turn on a Euclidean circle is an additional model
of the already-proved structure, not an assumption used by the proof.

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

/-
The boundary-and-action layer comes first. Geometric terminology belongs to a
later interpretation layer:

  conserved q2 boundary -> composable action -> finite-order classification
  -> optional Euclidean reading as circles and angles.

Nothing below requires the two coordinates to have been declared orthogonal
axes or requires a convention measuring one full turn by 360 degrees.
-/

/-
## Semantic transport and boundary detection

Coordinates are transported independently. The first structure recorded after
transport is the conserved `q2` boundary, without a geometric interpretation.
-/

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

/-
## Boundary-preserving action

The action is introduced only after transport to the signed real target. This
is the first layer that needs subtraction.
-/

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

/-
## Composition, inverse, and level-set actions

Products and inverse kernels remain on the real side. Source preimages for
these signed kernels are neither required nor asserted.
-/

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

/-
## Iteration, orbit, and point period

Period parameters in this section are iterate counts, not angle measures.
-/

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

/--
A real vector is periodic when a finite semantic orbit returns to it.

The supplied `n` need not be positive or minimal. This is Mathlib's ordinary
iterate-period predicate, not an angle period.
-/
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

/-- Finite action order persists at every multiple. -/
theorem semanticFiniteOrder_of_dvd
    {r : UnitKernel DkNNRealQ} {m n : ℕ}
    (h : SemanticFiniteOrder r m) (hmn : m ∣ n) :
    SemanticFiniteOrder r n := by
  rw [semanticFiniteOrder_iff] at h ⊢
  intro z
  exact semanticPeriodic_of_dvd (h z) hmn

/--
Minimal positive return time of a point under the transported action.

Mathlib assigns value zero when the point has no positive period.
-/
noncomputable def semanticMinimalPeriod
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) : ℕ :=
  Function.minimalPeriod (semanticAct r) z

/-- Every point returns at its Mathlib minimal period. -/
theorem semanticPeriodic_minimalPeriod
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    SemanticPeriodic r z (semanticMinimalPeriod r z) :=
  Function.isPeriodicPt_minimalPeriod (semanticAct r) z

/-- Periodicity at `n` is divisibility by the minimal period. -/
theorem semanticPeriodic_iff_minimalPeriod_dvd
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (n : ℕ) :
    SemanticPeriodic r z n ↔ semanticMinimalPeriod r z ∣ n :=
  Function.isPeriodicPt_iff_minimalPeriod_dvd

/-- Any finite action order is divisible by every point's minimal period. -/
theorem semanticMinimalPeriod_dvd_of_finiteOrder
    {r : UnitKernel DkNNRealQ} {n : ℕ}
    (h : SemanticFiniteOrder r n) (z : Vec ℝ) :
    semanticMinimalPeriod r z ∣ n := by
  rw [← semanticPeriodic_iff_minimalPeriod_dvd]
  exact (semanticFiniteOrder_iff r n).mp h z

/-- Positive periodicity forces a positive minimal period. -/
theorem semanticMinimalPeriod_pos
    {r : UnitKernel DkNNRealQ} {z : Vec ℝ} {n : ℕ}
    (hn : 0 < n) (h : SemanticPeriodic r z n) :
    0 < semanticMinimalPeriod r z :=
  Function.IsPeriodicPt.minimalPeriod_pos hn h

/-- A fixed point of the transported real action. -/
def SemanticFixed
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) : Prop :=
  Function.IsFixedPt (semanticAct r) z

/-- Fixed points are exactly period-one points. -/
theorem semanticFixed_iff_periodic_one
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    SemanticFixed r z ↔ SemanticPeriodic r z 1 := by
  rfl

/-- Fixed points are exactly points of minimal period one. -/
theorem semanticFixed_iff_minimalPeriod_eq_one
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    SemanticFixed r z ↔ semanticMinimalPeriod r z = 1 := by
  exact Function.minimalPeriod_eq_one_iff_isFixedPt.symm

/-- A fixed point is periodic at every iterate count. -/
theorem semanticPeriodic_of_fixed
    {r : UnitKernel DkNNRealQ} {z : Vec ℝ}
    (h : SemanticFixed r z) (n : ℕ) :
    SemanticPeriodic r z n :=
  Function.IsFixedPt.isPeriodicPt h n

/-- The origin is fixed by every transported linear CF2D action. -/
theorem semanticFixed_zero (r : UnitKernel DkNNRealQ) :
    SemanticFixed r (Vec.mk 0 0) := by
  simp [SemanticFixed, Function.IsFixedPt, semanticAct, UnitKernel.act,
    Vec.star]

/--
Positive finite action order excludes the vacuous zero-iterate witness.

This still records an exhibited positive order, not necessarily the least
positive order of the action.
-/
def SemanticPositiveFiniteOrder
    (r : UnitKernel DkNNRealQ) (n : ℕ) : Prop :=
  0 < n ∧ SemanticFiniteOrder r n

/-- Positive finite action order supplies positive periodicity of every point. -/
theorem semanticPeriodic_of_positiveFiniteOrder
    {r : UnitKernel DkNNRealQ} {n : ℕ}
    (h : SemanticPositiveFiniteOrder r n) (z : Vec ℝ) :
    0 < n ∧ SemanticPeriodic r z n :=
  ⟨h.1, (semanticFiniteOrder_iff r n).mp h.2 z⟩

/-- Positive finite action order persists at every positive multiple. -/
theorem semanticPositiveFiniteOrder_of_dvd
    {r : UnitKernel DkNNRealQ} {m n : ℕ}
    (h : SemanticPositiveFiniteOrder r m) (hmn : m ∣ n) (hn : 0 < n) :
    SemanticPositiveFiniteOrder r n :=
  ⟨hn, semanticFiniteOrder_of_dvd h.2 hmn⟩

/-- Under positive finite order, every point has positive minimal period. -/
theorem semanticMinimalPeriod_pos_of_positiveFiniteOrder
    {r : UnitKernel DkNNRealQ} {n : ℕ}
    (h : SemanticPositiveFiniteOrder r n) (z : Vec ℝ) :
    0 < semanticMinimalPeriod r z :=
  semanticMinimalPeriod_pos h.1
    ((semanticFiniteOrder_iff r n).mp h.2 z)

/-
## Identity and fixed-point classification

The classification uses only the unit equation and a two-variable linear
system. No continuity or angular parameterization enters.
-/

/-- The transported kernel is the neutral real unit kernel. -/
def SemanticIdentityKernel (r : UnitKernel DkNNRealQ) : Prop :=
  semanticUnitKernel r = UnitKernel.one ℝ

/--
For a transported first-quadrant unit kernel, core coordinate one forces the
beam coordinate to vanish.
-/
theorem semanticUnitKernel_beam_eq_zero_of_core_eq_one
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 1) :
    semanticValue (r : Vec DkNNRealQ).beam = 0 := by
  have hq := semanticUnitKernel_sq_add_sq r
  nlinarith [sq_nonneg (semanticValue (r : Vec DkNNRealQ).beam)]

/-- Identity-kernel status is characterized by semantic core coordinate one. -/
theorem semanticIdentityKernel_iff_core_eq_one
    (r : UnitKernel DkNNRealQ) :
    SemanticIdentityKernel r ↔
      semanticValue (r : Vec DkNNRealQ).core = 1 := by
  constructor
  · intro h
    have hv := congrArg (fun k : UnitKernel ℝ => (k : Vec ℝ).core) h
    simpa [SemanticIdentityKernel, semanticUnitKernel, semanticVec,
      UnitKernel.one, Vec.one] using hv
  · intro hcore
    have hbeam := semanticUnitKernel_beam_eq_zero_of_core_eq_one hcore
    apply UnitKernel.ext
    cases r with
    | mk val hq =>
        cases val with
        | mk core beam =>
            simp_all [semanticUnitKernel, semanticVec, UnitKernel.one, Vec.one]

/-- An identity transported kernel fixes every real vector. -/
theorem semanticFixed_of_identityKernel
    {r : UnitKernel DkNNRealQ} (h : SemanticIdentityKernel r)
    (z : Vec ℝ) :
    SemanticFixed r z := by
  rw [SemanticIdentityKernel] at h
  simp [SemanticFixed, Function.IsFixedPt, semanticAct, h]

/--
If the semantic core coordinate is not one, the transported action has only
the origin as a fixed point.
-/
theorem eq_zero_of_semanticFixed_of_core_ne_one
    {r : UnitKernel DkNNRealQ} {z : Vec ℝ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core ≠ 1)
    (hz : SemanticFixed r z) :
    z = Vec.mk 0 0 := by
  let C := semanticValue (r : Vec DkNNRealQ).core
  let S := semanticValue (r : Vec DkNNRealQ).beam
  have hq : C ^ 2 + S ^ 2 = 1 := by
    simpa [C, S] using semanticUnitKernel_sq_add_sq r
  have hfix := hz
  rw [SemanticFixed, Function.IsFixedPt] at hfix
  have hx :
      C * z.core - S * z.beam = z.core := by
    simpa [semanticAct, C, S] using congrArg Vec.core hfix
  have hy :
      C * z.beam + S * z.core = z.beam := by
    simpa [semanticAct, C, S] using congrArg Vec.beam hfix
  have hdet : (C - 1) ^ 2 + S ^ 2 ≠ 0 := by
    intro hzero
    have : C = 1 := by nlinarith [sq_nonneg (C - 1), sq_nonneg S]
    exact hcore (by simpa [C] using this)
  have hdx : ((C - 1) ^ 2 + S ^ 2) * z.core = 0 := by
    linear_combination (C - 1) * hx + S * hy
  have hdy : ((C - 1) ^ 2 + S ^ 2) * z.beam = 0 := by
    linear_combination (C - 1) * hy - S * hx
  have zx : z.core = 0 :=
    (mul_eq_zero.mp hdx).resolve_left hdet
  have zy : z.beam = 0 :=
    (mul_eq_zero.mp hdy).resolve_left hdet
  cases z
  simp_all

/-- A nonidentity transported kernel fixes exactly the origin. -/
theorem semanticFixed_iff_eq_zero_of_not_identity
    {r : UnitKernel DkNNRealQ} (h : ¬SemanticIdentityKernel r)
    (z : Vec ℝ) :
    SemanticFixed r z ↔ z = Vec.mk 0 0 := by
  have hcore :
      semanticValue (r : Vec DkNNRealQ).core ≠ 1 := by
    intro hcore
    exact h ((semanticIdentityKernel_iff_core_eq_one r).2 hcore)
  exact ⟨eq_zero_of_semanticFixed_of_core_ne_one hcore,
    fun hz => hz ▸ semanticFixed_zero r⟩

/-
## Real-side powers and low-order classification

Finite powers turn repeated action into polynomial coordinate identities.
Orders one through three collapse to identity in the transported first
quadrant; order four introduces the nonidentity boundary case.
-/

/--
The `n`-fold product of a transported kernel, formed entirely in the real
unit-kernel monoid.

The successor convention
`semanticUnitKernel r ⋆ semanticKernelPower r n` matches the convention for
function iteration: the new action is applied after the previous `n` actions.
-/
def semanticKernelPower
    (r : UnitKernel DkNNRealQ) : ℕ → UnitKernel ℝ
  | 0 => UnitKernel.one ℝ
  | n + 1 =>
      UnitKernel.star (semanticUnitKernel r) (semanticKernelPower r n)

/-- The action of the real-side kernel power is the corresponding orbit term. -/
theorem semanticKernelPower_act
    (r : UnitKernel DkNNRealQ) (n : ℕ) (z : Vec ℝ) :
    UnitKernel.act (semanticKernelPower r n) z = semanticOrbit r z n := by
  induction n with
  | zero =>
      simp [semanticKernelPower, semanticOrbit]
  | succ n ih =>
      simp [semanticKernelPower, UnitKernel.act_star, semanticOrbit,
        semanticAct, Function.iterate_succ_apply', ih]

/--
An action by a real unit kernel is faithful: if it acts as the identity on
the plane, then the kernel itself is the neutral kernel.
-/
theorem unitKernel_eq_one_of_act_eq_id
    {k : UnitKernel ℝ} (h : UnitKernel.act k = id) :
    k = UnitKernel.one ℝ := by
  apply UnitKernel.ext
  have hone := congrFun h (Vec.one ℝ)
  simpa [UnitKernel.act] using hone

/--
The transported kernel has product order dividing `n` when its `n`-fold
real-side product is the neutral kernel.

This predicate makes no assertion that a corresponding product exists in the
nonnegative source semiring.
-/
def SemanticKernelFiniteOrder
    (r : UnitKernel DkNNRealQ) (n : ℕ) : Prop :=
  semanticKernelPower r n = UnitKernel.one ℝ

/--
Real-side kernel order and finite order of the transported plane action are
equivalent.

The forward implication is the action law for the repeated kernel product.
The reverse implication uses faithfulness, detected by evaluating the action
at the multiplicative unit vector.
-/
theorem semanticKernelFiniteOrder_iff
    (r : UnitKernel DkNNRealQ) (n : ℕ) :
    SemanticKernelFiniteOrder r n ↔ SemanticFiniteOrder r n := by
  constructor
  · intro h
    change semanticKernelPower r n = UnitKernel.one ℝ at h
    change (semanticAct r)^[n] = id
    funext z
    calc
      (semanticAct r)^[n] z =
          UnitKernel.act (semanticKernelPower r n) z := by
            symm
            simpa [semanticOrbit] using semanticKernelPower_act r n z
      _ = UnitKernel.act (UnitKernel.one ℝ) z := by rw [h]
      _ = id z := by simp
  · intro h
    change (semanticAct r)^[n] = id at h
    apply unitKernel_eq_one_of_act_eq_id
    funext z
    calc
      UnitKernel.act (semanticKernelPower r n) z =
          (semanticAct r)^[n] z := by
            simpa [semanticOrbit] using semanticKernelPower_act r n z
      _ = id z := congrFun h z

/-- The first real-side kernel power is the transported kernel itself. -/
@[simp]
theorem semanticKernelPower_one (r : UnitKernel DkNNRealQ) :
    semanticKernelPower r 1 = semanticUnitKernel r := by
  simp [semanticKernelPower]

/--
The core coordinate of the second kernel power is the quadratic difference
`C^2 - S^2`.

This is the algebraic double-angle polynomial, obtained solely by expanding
the CF2D product.
-/
theorem semanticKernelPower_two_core (r : UnitKernel DkNNRealQ) :
    (semanticKernelPower r 2 : Vec ℝ).core =
      semanticValue (r : Vec DkNNRealQ).core ^ 2 -
        semanticValue (r : Vec DkNNRealQ).beam ^ 2 := by
  simp [semanticKernelPower, semanticUnitKernel, semanticVec, UnitKernel.star,
    Vec.star, UnitKernel.one, Vec.one, pow_two]

/--
The beam coordinate of the second kernel power is the quadratic cross term
`2*C*S`.
-/
theorem semanticKernelPower_two_beam (r : UnitKernel DkNNRealQ) :
    (semanticKernelPower r 2 : Vec ℝ).beam =
      2 * semanticValue (r : Vec DkNNRealQ).core *
        semanticValue (r : Vec DkNNRealQ).beam := by
  simp [semanticKernelPower, semanticUnitKernel, semanticVec, UnitKernel.star,
    Vec.star, UnitKernel.one, Vec.one]
  ring

/--
The core coordinate of the third kernel power is `C^3 - 3*C*S^2`.

This is the triple-angle polynomial as a finite CF2D product identity; no
angle parameter or trigonometric theorem is used.
-/
theorem semanticKernelPower_three_core (r : UnitKernel DkNNRealQ) :
    (semanticKernelPower r 3 : Vec ℝ).core =
      semanticValue (r : Vec DkNNRealQ).core ^ 3 -
        3 * semanticValue (r : Vec DkNNRealQ).core *
          semanticValue (r : Vec DkNNRealQ).beam ^ 2 := by
  simp [semanticKernelPower, semanticUnitKernel, semanticVec, UnitKernel.star,
    Vec.star, UnitKernel.one, Vec.one]
  ring

/--
The beam coordinate of the third kernel power is `3*C^2*S - S^3`.
-/
theorem semanticKernelPower_three_beam (r : UnitKernel DkNNRealQ) :
    (semanticKernelPower r 3 : Vec ℝ).beam =
      3 * semanticValue (r : Vec DkNNRealQ).core ^ 2 *
          semanticValue (r : Vec DkNNRealQ).beam -
        semanticValue (r : Vec DkNNRealQ).beam ^ 3 := by
  simp [semanticKernelPower, semanticUnitKernel, semanticVec, UnitKernel.star,
    Vec.star, UnitKernel.one, Vec.one]
  ring

/--
The core coordinate of the fourth kernel power is
`C^4 - 6*C^2*S^2 + S^4`.
-/
theorem semanticKernelPower_four_core (r : UnitKernel DkNNRealQ) :
    (semanticKernelPower r 4 : Vec ℝ).core =
      semanticValue (r : Vec DkNNRealQ).core ^ 4 -
        6 * semanticValue (r : Vec DkNNRealQ).core ^ 2 *
          semanticValue (r : Vec DkNNRealQ).beam ^ 2 +
        semanticValue (r : Vec DkNNRealQ).beam ^ 4 := by
  simp [semanticKernelPower, semanticUnitKernel, semanticVec, UnitKernel.star,
    Vec.star, UnitKernel.one, Vec.one]
  ring

/--
The beam coordinate of the fourth kernel power is
`4*C*S*(C^2 - S^2)`.
-/
theorem semanticKernelPower_four_beam (r : UnitKernel DkNNRealQ) :
    (semanticKernelPower r 4 : Vec ℝ).beam =
      4 * semanticValue (r : Vec DkNNRealQ).core *
        semanticValue (r : Vec DkNNRealQ).beam *
        (semanticValue (r : Vec DkNNRealQ).core ^ 2 -
          semanticValue (r : Vec DkNNRealQ).beam ^ 2) := by
  simp [semanticKernelPower, semanticUnitKernel, semanticVec, UnitKernel.star,
    Vec.star, UnitKernel.one, Vec.one]
  ring

/-- Product order dividing one is exactly semantic identity-kernel status. -/
theorem semanticKernelFiniteOrder_one_iff_identity
    (r : UnitKernel DkNNRealQ) :
    SemanticKernelFiniteOrder r 1 ↔ SemanticIdentityKernel r := by
  simp [SemanticKernelFiniteOrder, SemanticIdentityKernel]

/-- Product order dividing one is characterized by semantic core coordinate one. -/
theorem semanticKernelFiniteOrder_one_iff_core_eq_one
    (r : UnitKernel DkNNRealQ) :
    SemanticKernelFiniteOrder r 1 ↔
      semanticValue (r : Vec DkNNRealQ).core = 1 := by
  rw [semanticKernelFiniteOrder_one_iff_identity,
    semanticIdentityKernel_iff_core_eq_one]

/--
For a transported first-quadrant kernel, product order dividing two already
forces the neutral kernel.

Over all real unit kernels the square equation also admits `(-1, 0)`. That
case is excluded here because both semantic coordinates transported from
`DkNNRealQ` are nonnegative.
-/
theorem semanticKernelFiniteOrder_two_iff_identity
    (r : UnitKernel DkNNRealQ) :
    SemanticKernelFiniteOrder r 2 ↔ SemanticIdentityKernel r := by
  let C := semanticValue (r : Vec DkNNRealQ).core
  let S := semanticValue (r : Vec DkNNRealQ).beam
  constructor
  · intro h
    change semanticKernelPower r 2 = UnitKernel.one ℝ at h
    have hcore := congrArg (fun k : UnitKernel ℝ => (k : Vec ℝ).core) h
    have hC : 0 ≤ C := by
      simpa [C] using semanticUnitKernel_core_nonneg r
    have hS : 0 ≤ S := by
      simpa [S] using semanticUnitKernel_beam_nonneg r
    have hq : C ^ 2 + S ^ 2 = 1 := by
      simpa [C, S] using semanticUnitKernel_sq_add_sq r
    have hsquare : C ^ 2 - S ^ 2 = 1 := by
      calc
        C ^ 2 - S ^ 2 =
            (semanticKernelPower r 2 : Vec ℝ).core := by
              symm
              simpa [C, S] using semanticKernelPower_two_core r
        _ = 1 := by simpa [UnitKernel.one, Vec.one] using hcore
    apply (semanticIdentityKernel_iff_core_eq_one r).2
    change C = 1
    nlinarith [sq_nonneg (C - 1)]
  · intro h
    change semanticKernelPower r 2 = UnitKernel.one ℝ
    rw [SemanticIdentityKernel] at h
    simp [semanticKernelPower, h]

/-- Product order dividing two is also characterized by semantic core one. -/
theorem semanticKernelFiniteOrder_two_iff_core_eq_one
    (r : UnitKernel DkNNRealQ) :
    SemanticKernelFiniteOrder r 2 ↔
      semanticValue (r : Vec DkNNRealQ).core = 1 := by
  rw [semanticKernelFiniteOrder_two_iff_identity,
    semanticIdentityKernel_iff_core_eq_one]

/--
For a transported first-quadrant kernel, product order dividing three also
forces the neutral kernel.

The cubic beam equation factors as `S * (3*C^2 - S^2) = 0`. The branch
`S = 0` gives `C = 1`. In the other branch the unit-square equation forces
`C^2 = 1/4` and `S^2 = 3/4`, which contradicts the cubic core equation.
No square root or angle parameter is introduced.
-/
theorem semanticKernelFiniteOrder_three_iff_identity
    (r : UnitKernel DkNNRealQ) :
    SemanticKernelFiniteOrder r 3 ↔ SemanticIdentityKernel r := by
  let C := semanticValue (r : Vec DkNNRealQ).core
  let S := semanticValue (r : Vec DkNNRealQ).beam
  constructor
  · intro h
    change semanticKernelPower r 3 = UnitKernel.one ℝ at h
    have hcore := congrArg (fun k : UnitKernel ℝ => (k : Vec ℝ).core) h
    have hbeam := congrArg (fun k : UnitKernel ℝ => (k : Vec ℝ).beam) h
    have hC : 0 ≤ C := by
      simpa [C] using semanticUnitKernel_core_nonneg r
    have hS : 0 ≤ S := by
      simpa [S] using semanticUnitKernel_beam_nonneg r
    have hq : C ^ 2 + S ^ 2 = 1 := by
      simpa [C, S] using semanticUnitKernel_sq_add_sq r
    have hcubic : C ^ 3 - 3 * C * S ^ 2 = 1 := by
      calc
        C ^ 3 - 3 * C * S ^ 2 =
            (semanticKernelPower r 3 : Vec ℝ).core := by
              symm
              simpa [C, S] using semanticKernelPower_three_core r
        _ = 1 := by simpa [UnitKernel.one, Vec.one] using hcore
    have hbeamCubic : 3 * C ^ 2 * S - S ^ 3 = 0 := by
      calc
        3 * C ^ 2 * S - S ^ 3 =
            (semanticKernelPower r 3 : Vec ℝ).beam := by
              symm
              simpa [C, S] using semanticKernelPower_three_beam r
        _ = 0 := by simpa [UnitKernel.one, Vec.one] using hbeam
    have hfactor : S * (3 * C ^ 2 - S ^ 2) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hfactor with hSzero | hrelation
    · apply (semanticIdentityKernel_iff_core_eq_one r).2
      change C = 1
      nlinarith [sq_nonneg (C - 1)]
    · have hCsq : C ^ 2 = 1 / 4 := by
        nlinarith
      have hCeq : C = 1 / 2 := by
        nlinarith [sq_nonneg (C - 1 / 2)]
      have hSsq : S ^ 2 = 3 / 4 := by
        nlinarith
      exfalso
      nlinarith
  · intro h
    change semanticKernelPower r 3 = UnitKernel.one ℝ
    rw [SemanticIdentityKernel] at h
    simp [semanticKernelPower, h]

/-- Product order dividing three is characterized by semantic core one. -/
theorem semanticKernelFiniteOrder_three_iff_core_eq_one
    (r : UnitKernel DkNNRealQ) :
    SemanticKernelFiniteOrder r 3 ↔
      semanticValue (r : Vec DkNNRealQ).core = 1 := by
  rw [semanticKernelFiniteOrder_three_iff_identity,
    semanticIdentityKernel_iff_core_eq_one]

/--
Product order dividing four is characterized by a boundary core coordinate:
the transported kernel has semantic core `1` or semantic core `0`.

The `core = 1` branch is the neutral kernel. The `core = 0` branch has beam
`1` by the unit-square equation and coordinate nonnegativity; it is the first
nonidentity finite-order kernel admitted by the transported first quadrant.
-/
theorem semanticKernelFiniteOrder_four_iff_core_eq_one_or_zero
    (r : UnitKernel DkNNRealQ) :
    SemanticKernelFiniteOrder r 4 ↔
      semanticValue (r : Vec DkNNRealQ).core = 1 ∨
        semanticValue (r : Vec DkNNRealQ).core = 0 := by
  let C := semanticValue (r : Vec DkNNRealQ).core
  let S := semanticValue (r : Vec DkNNRealQ).beam
  have hC : 0 ≤ C := by
    simpa [C] using semanticUnitKernel_core_nonneg r
  have hS : 0 ≤ S := by
    simpa [S] using semanticUnitKernel_beam_nonneg r
  have hq : C ^ 2 + S ^ 2 = 1 := by
    simpa [C, S] using semanticUnitKernel_sq_add_sq r
  constructor
  · intro h
    change semanticKernelPower r 4 = UnitKernel.one ℝ at h
    have hcore := congrArg (fun k : UnitKernel ℝ => (k : Vec ℝ).core) h
    have hfour :
        C ^ 4 - 6 * C ^ 2 * S ^ 2 + S ^ 4 = 1 := by
      calc
        C ^ 4 - 6 * C ^ 2 * S ^ 2 + S ^ 4 =
            (semanticKernelPower r 4 : Vec ℝ).core := by
              symm
              simpa [C, S] using semanticKernelPower_four_core r
        _ = 1 := by simpa [UnitKernel.one, Vec.one] using hcore
    have hqSquare : (C ^ 2 + S ^ 2) ^ 2 = 1 := by rw [hq]; norm_num
    have hprod : C ^ 2 * S ^ 2 = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hprod with hCsq | hSsq
    · right
      change C = 0
      nlinarith [sq_nonneg C]
    · left
      change C = 1
      nlinarith [sq_nonneg (C - 1), sq_nonneg S]
  · rintro (hCeq | hCeq)
    · have hid : semanticUnitKernel r = UnitKernel.one ℝ :=
        (semanticIdentityKernel_iff_core_eq_one r).2 hCeq
      change semanticKernelPower r 4 = UnitKernel.one ℝ
      simp [semanticKernelPower, hid]
    · have hSeq : S = 1 := by
        change C = 0 at hCeq
        nlinarith [sq_nonneg (S - 1)]
      change semanticKernelPower r 4 = UnitKernel.one ℝ
      apply UnitKernel.ext
      have hcore :
          (semanticKernelPower r 4 : Vec ℝ).core = 1 := by
        simpa [C, S, hCeq, hSeq] using semanticKernelPower_four_core r
      have hbeam :
          (semanticKernelPower r 4 : Vec ℝ).beam = 0 := by
        simpa [C, S, hCeq, hSeq] using semanticKernelPower_four_beam r
      cases hp : (semanticKernelPower r 4 : Vec ℝ) with
      | mk core beam =>
          simp_all [UnitKernel.one, Vec.one]

/--
Semantic core zero determines semantic beam one for a transported unit
kernel in the first quadrant.
-/
theorem semanticUnitKernel_beam_eq_one_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0) :
    semanticValue (r : Vec DkNNRealQ).beam = 1 := by
  have hbeam :
      0 ≤ semanticValue (r : Vec DkNNRealQ).beam := by
    simpa [semanticUnitKernel, semanticVec] using
      semanticUnitKernel_beam_nonneg r
  have hq := semanticUnitKernel_sq_add_sq r
  nlinarith [sq_nonneg
    (semanticValue (r : Vec DkNNRealQ).beam - 1)]

/-- Semantic core zero supplies product order dividing four. -/
theorem semanticKernelFiniteOrder_four_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0) :
    SemanticKernelFiniteOrder r 4 :=
  (semanticKernelFiniteOrder_four_iff_core_eq_one_or_zero r).2 (Or.inr hcore)

/-- Semantic core zero excludes product order dividing one. -/
theorem not_semanticKernelFiniteOrder_one_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0) :
    ¬SemanticKernelFiniteOrder r 1 := by
  rw [semanticKernelFiniteOrder_one_iff_core_eq_one]
  intro hone
  linarith

/-- Semantic core zero excludes product order dividing two. -/
theorem not_semanticKernelFiniteOrder_two_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0) :
    ¬SemanticKernelFiniteOrder r 2 := by
  rw [semanticKernelFiniteOrder_two_iff_core_eq_one]
  intro hone
  linarith

/-- Semantic core zero excludes product order dividing three. -/
theorem not_semanticKernelFiniteOrder_three_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0) :
    ¬SemanticKernelFiniteOrder r 3 := by
  rw [semanticKernelFiniteOrder_three_iff_core_eq_one]
  intro hone
  linarith

/--
The transported kernel has exact product order four: its fourth power is
neutral, while none of its first three positive powers is neutral.
-/
def SemanticExactKernelOrderFour (r : UnitKernel DkNNRealQ) : Prop :=
  SemanticKernelFiniteOrder r 4 ∧
    ¬SemanticKernelFiniteOrder r 1 ∧
    ¬SemanticKernelFiniteOrder r 2 ∧
    ¬SemanticKernelFiniteOrder r 3

/--
Exact product order four is characterized by semantic core zero.

The unit-square equation then also determines semantic beam one, so this is
precisely the transported boundary kernel `(0,1)`.
-/
theorem semanticExactKernelOrderFour_iff_core_eq_zero
    (r : UnitKernel DkNNRealQ) :
    SemanticExactKernelOrderFour r ↔
      semanticValue (r : Vec DkNNRealQ).core = 0 := by
  constructor
  · intro h
    rcases (semanticKernelFiniteOrder_four_iff_core_eq_one_or_zero r).1 h.1 with
      hone | hzero
    · exact False.elim (h.2.1
        ((semanticKernelFiniteOrder_one_iff_core_eq_one r).2 hone))
    · exact hzero
  · intro hzero
    exact ⟨semanticKernelFiniteOrder_four_of_core_eq_zero hzero,
      not_semanticKernelFiniteOrder_one_of_core_eq_zero hzero,
      not_semanticKernelFiniteOrder_two_of_core_eq_zero hzero,
      not_semanticKernelFiniteOrder_three_of_core_eq_zero hzero⟩

/--
The transported plane action has exact order four: its fourth iterate is the
identity function, while none of its first three positive iterates is.

This is the primary statement. Calling the action a 90-degree rotation would
require a later Euclidean interpretation and an angle-measure convention.
-/
def SemanticExactActionOrderFour (r : UnitKernel DkNNRealQ) : Prop :=
  SemanticFiniteOrder r 4 ∧
    ¬SemanticFiniteOrder r 1 ∧
    ¬SemanticFiniteOrder r 2 ∧
    ¬SemanticFiniteOrder r 3

/--
Exact order four is invariant under passage from the real-side kernel product
to its action on the CF2D plane.

This is the finite-order form of the CF2D addition law: kernel multiplication
is represented faithfully by composition of the associated actions.
-/
theorem semanticExactKernelOrderFour_iff_exactActionOrderFour
    (r : UnitKernel DkNNRealQ) :
    SemanticExactKernelOrderFour r ↔ SemanticExactActionOrderFour r := by
  simp only [SemanticExactKernelOrderFour, SemanticExactActionOrderFour,
    semanticKernelFiniteOrder_iff]

/-- Exact action order four is characterized by semantic core zero. -/
theorem semanticExactActionOrderFour_iff_core_eq_zero
    (r : UnitKernel DkNNRealQ) :
    SemanticExactActionOrderFour r ↔
      semanticValue (r : Vec DkNNRealQ).core = 0 := by
  rw [← semanticExactKernelOrderFour_iff_exactActionOrderFour,
    semanticExactKernelOrderFour_iff_core_eq_zero]

/--
Semantic core zero gives a plane action whose fourth iterate is the identity
and whose first three positive iterates are not the identity.
-/
theorem semanticExactActionOrderFour_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0) :
    SemanticExactActionOrderFour r :=
  (semanticExactActionOrderFour_iff_core_eq_zero r).2 hcore

/-
## Pre-geometric four-phase boundary action

The following results expose the four-step orbit and its point periods. A
Euclidean circle and angle measure have not been chosen.
-/

/--
At the exact-order-four boundary, the transported action exchanges the two
coordinates with one sign change.

This coordinate law is proved before assigning any geometric meaning to the
coordinates. Its later Euclidean reading as a quarter-turn is optional.
-/
theorem semanticAct_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    semanticAct r z = Vec.mk (-z.beam) z.core := by
  have hbeam := semanticUnitKernel_beam_eq_one_of_core_eq_zero hcore
  cases z with
  | mk x y =>
      simp [semanticAct, UnitKernel.act, semanticUnitKernel, semanticVec,
        Vec.star, hcore, hbeam]

/-- Two boundary actions negate both coordinates. -/
theorem semanticAct_twice_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    semanticAct r (semanticAct r z) = Vec.mk (-z.core) (-z.beam) := by
  calc
    semanticAct r (semanticAct r z) =
        Vec.mk (-(semanticAct r z).beam) (semanticAct r z).core :=
      semanticAct_of_core_eq_zero hcore (semanticAct r z)
    _ = Vec.mk (-z.core) (-z.beam) := by
      rw [semanticAct_of_core_eq_zero hcore]

/-- Three boundary actions reverse the first exchange law. -/
theorem semanticAct_thrice_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    semanticAct r (semanticAct r (semanticAct r z)) =
      Vec.mk z.beam (-z.core) := by
  calc
    semanticAct r (semanticAct r (semanticAct r z)) =
        Vec.mk (-(semanticAct r (semanticAct r z)).beam)
          (semanticAct r (semanticAct r z)).core :=
      semanticAct_of_core_eq_zero hcore
        (semanticAct r (semanticAct r z))
    _ = Vec.mk z.beam (-z.core) := by
      rw [semanticAct_twice_of_core_eq_zero hcore]
      simp

/-- A nonzero vector cannot return after one boundary action. -/
theorem not_semanticPeriodic_one_of_core_eq_zero_of_ne_zero
    {r : UnitKernel DkNNRealQ} {z : Vec ℝ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (hz : z ≠ Vec.mk 0 0) :
    ¬SemanticPeriodic r z 1 := by
  intro hperiodic
  change semanticAct r z = z at hperiodic
  rw [semanticAct_of_core_eq_zero hcore] at hperiodic
  cases z with
  | mk x y =>
      simp only [Vec.mk.injEq] at hperiodic
      apply hz
      simp only [Vec.mk.injEq]
      constructor <;> linarith [hperiodic.1, hperiodic.2]

/-- A nonzero vector cannot return after two boundary actions. -/
theorem not_semanticPeriodic_two_of_core_eq_zero_of_ne_zero
    {r : UnitKernel DkNNRealQ} {z : Vec ℝ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (hz : z ≠ Vec.mk 0 0) :
    ¬SemanticPeriodic r z 2 := by
  intro hperiodic
  change semanticAct r (semanticAct r z) = z at hperiodic
  rw [semanticAct_twice_of_core_eq_zero hcore] at hperiodic
  cases z with
  | mk x y =>
      simp only [Vec.mk.injEq] at hperiodic
      apply hz
      simp only [Vec.mk.injEq]
      constructor <;> linarith [hperiodic.1, hperiodic.2]

/-- A nonzero vector cannot return after three boundary actions. -/
theorem not_semanticPeriodic_three_of_core_eq_zero_of_ne_zero
    {r : UnitKernel DkNNRealQ} {z : Vec ℝ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (hz : z ≠ Vec.mk 0 0) :
    ¬SemanticPeriodic r z 3 := by
  intro hperiodic
  change semanticAct r (semanticAct r (semanticAct r z)) = z at hperiodic
  rw [semanticAct_thrice_of_core_eq_zero hcore] at hperiodic
  cases z with
  | mk x y =>
      simp only [Vec.mk.injEq] at hperiodic
      apply hz
      simp only [Vec.mk.injEq]
      constructor <;> linarith [hperiodic.1, hperiodic.2]

/--
Every nonzero vector has minimal period four under the boundary action.

The origin remains fixed, so exact order of the whole action does not mean
that every point has point period four.
-/
theorem semanticMinimalPeriod_eq_four_of_core_eq_zero_of_ne_zero
    {r : UnitKernel DkNNRealQ} {z : Vec ℝ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (hz : z ≠ Vec.mk 0 0) :
    semanticMinimalPeriod r z = 4 := by
  have horder := semanticExactActionOrderFour_of_core_eq_zero hcore
  have hperiodic : SemanticPeriodic r z 4 :=
    (semanticFiniteOrder_iff r 4).mp horder.1 z
  have hpos : 0 < semanticMinimalPeriod r z :=
    semanticMinimalPeriod_pos (by norm_num) hperiodic
  have hle : semanticMinimalPeriod r z ≤ 4 :=
    Function.IsPeriodicPt.minimalPeriod_le (by norm_num) hperiodic
  have hneOne : semanticMinimalPeriod r z ≠ 1 := by
    intro hperiod
    apply not_semanticPeriodic_one_of_core_eq_zero_of_ne_zero hcore hz
    rw [semanticPeriodic_iff_minimalPeriod_dvd, hperiod]
  have hneTwo : semanticMinimalPeriod r z ≠ 2 := by
    intro hperiod
    apply not_semanticPeriodic_two_of_core_eq_zero_of_ne_zero hcore hz
    rw [semanticPeriodic_iff_minimalPeriod_dvd, hperiod]
  have hneThree : semanticMinimalPeriod r z ≠ 3 := by
    intro hperiod
    apply not_semanticPeriodic_three_of_core_eq_zero_of_ne_zero hcore hz
    rw [semanticPeriodic_iff_minimalPeriod_dvd, hperiod]
  omega

/-
[TODO: semantic-cf2d/signed-kernel] Source-level `Vec.star` and
`KernelFamily` require a ring because their core coordinate uses subtraction.
Keep the source in the nonnegative semiring until a signed DkReal layer is
introduced; do not manufacture subtraction merely to mirror the real target.

[IMPLEMENTED: semantic-cf2d-phase/master-edge] `SemanticCF2DPhase` fills one
transition affinely in the semantic real target, from `z` to `semanticAct r z`.

[IMPLEMENTED: semantic-cf2d-phase/four-translates] All transition edges are
generated by applying action iterates to the one master edge. Their endpoints
form exact seams, and the family is four-periodic under a core-zero kernel.

[IMPLEMENTED: semantic-cf2d-phase/half-fold-profile] The affine edge has `q2`
profile `((1-t)^2 + t^2) * q2 z`, symmetric under `t ↦ 1-t`, with a positive
lower bound of one half.

[IMPLEMENTED: semantic-cf2d-phase/path-concatenation] `SemanticCF2DPath`
packages each compatible edge as a Mathlib `Path` and concatenates four edges
into a closed piecewise-affine loop. It is not yet a fixed-`q2` boundary path.

[IMPLEMENTED: semantic-cf2d-phase/boundary-normalization]
`SemanticCF2DNormalize` normalizes one affine edge by the positive square root
of its `q2` profile and proves that the resulting continuous edge stays on the
original boundary.

[IMPLEMENTED: semantic-cf2d-phase/normalized-four-path] The normalized edge is
transported through all four action phases. The resulting fixed-`q2` paths
have exact seams and concatenate to a closed path.

[IMPLEMENTED: semantic-cf2d-phase/levelset-path] The normalized phases and
their closed four-phase concatenation are packaged directly in
`LevelSet Real (q2 z)`, making boundary membership part of the target type.

[IMPLEMENTED: semantic-cf2d-phase/euclidean-levelset-bridge]
`CF2D.EuclideanPhase` identifies every real `q2` level set with the explicit
two-coordinate Euclidean circle equation of squared radius `rho2`. It
separates the zero one-point boundary and maps the existing closed path
through this interpretation.

[TODO: semantic-cf2d-phase/standard-euclidean-space] Relate the explicit
coordinate circle equation to the standard `EuclideanSpace Real (Fin 2)`
metric sphere, keeping the zero and positive-radius cases separate.

[TODO: semantic-cf2d-phase/euclidean-interpretation] Only after normalization,
identify the fixed-`q2` path with the standard Euclidean circle model and
extract angular terminology.
-/

end

end DkMath.Analysis.DkNNRealQ
