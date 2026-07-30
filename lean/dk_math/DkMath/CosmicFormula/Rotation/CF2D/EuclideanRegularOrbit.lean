/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.RegularOrbit
import DkMath.CosmicFormula.Rotation.CF2D.EuclideanPhase

#print "file: DkMath.CosmicFormula.Rotation.CF2D.EuclideanRegularOrbit"

/-!
# Euclidean interpretation of finite CF2D regular orbits

This module transports the already-constructed finite CF2D orbit to Mathlib's
oriented Euclidean plane.  The algebraic action becomes the standard oriented
rotation with the same real parameter.  Consequently, the transported states
form a finite, distinct, equal-step orbit on the unit sphere.

The construction still contains no polygon edges, convex hull, or polygon
interior.  Those geometric structures are downstream interpretations of this
finite orbit, not inputs to its periodicity or distinctness.
-/

namespace DkMath.CosmicFormula.Rotation.CF2D

noncomputable section

local instance euclideanRegularOrbitFinrankTwo :
    Fact (Module.finrank ℝ EuclideanPlane = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

/--
The real trigonometric CF2D action is Mathlib's oriented Euclidean rotation
after transporting the two coordinates to the standard Euclidean plane.
-/
theorem realTrigKernel_act_euclidean_eq_rotation
    (theta : ℝ) (z : Vec ℝ) :
    pairToEuclideanPlane (Vec.toProd (UnitKernel.act
      (realTrigKernelFamily.kernel theta) z)) =
    euclideanPlaneOrientation.rotation theta
      (pairToEuclideanPlane (Vec.toProd z)) := by
  rw [euclideanPlaneOrientation.rotation_apply,
    rightAngleRotation_eq_quarterTurn]
  ext i
  fin_cases i <;>
    simp [pairToEuclideanPlane, quarterTurnLinearIsometry,
      quarterTurnLinearEquiv, euclideanPlaneToPair,
      Vec.toProd, realTrigKernelFamily_act_eq]
  all_goals ring

/-- The `j`th algebraic regular-orbit state in the standard Euclidean plane. -/
def euclideanRegularVertex (k : ℕ) (j : Fin k) : EuclideanPlane :=
  pairToEuclideanPlane (Vec.toProd (regularVertex k j))

/-- Every transported regular-orbit state has Euclidean norm one. -/
@[simp]
theorem norm_euclideanRegularVertex (k : ℕ) (j : Fin k) :
    ‖euclideanRegularVertex k j‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [euclideanRegularVertex, pairToEuclideanPlane_norm_sq]
  simpa [Vec.toProd, Vec.q2] using regularVertex_q2 k j

/-- Every transported regular-orbit state lies on the unit metric sphere. -/
theorem euclideanRegularVertex_mem_unitSphere (k : ℕ) (j : Fin k) :
    euclideanRegularVertex k j ∈ Metric.sphere (0 : EuclideanPlane) 1 := by
  rw [Metric.mem_sphere, dist_zero_right, norm_euclideanRegularVertex]

/-- One normalized `k`-division step is the real angle `2 * pi / k`. -/
theorem regularStepAngle_eq_two_pi_div (k : ℕ) :
    normalizedPhaseAngle (regularPhaseStep k) =
      (2 * Real.pi) / (k : ℝ) := by
  simp only [normalizedPhaseAngle, regularPhaseStep,
    DkMath.Analysis.DkNNRealQ.normalizedCycleStep]
  ring

/--
Cyclic succession in the finite orbit is oriented rotation by one normalized
`k`-division angle, including the final wrap back to index zero.
-/
theorem euclideanRegularVertex_next {k : ℕ} (hk : 0 < k) (j : Fin k) :
    euclideanRegularVertex k (regularVertexNext hk j) =
      euclideanPlaneOrientation.rotation
        (normalizedPhaseAngle (regularPhaseStep k))
        (euclideanRegularVertex k j) := by
  rw [euclideanRegularVertex, regularVertex_next hk]
  exact realTrigKernel_act_euclidean_eq_rotation
    (normalizedPhaseAngle (regularPhaseStep k)) (regularVertex k j)

/-- Cyclic succession is ordinary oriented rotation by `2 * pi / k`. -/
theorem euclideanRegularVertex_next_two_pi_div {k : ℕ}
    (hk : 0 < k) (j : Fin k) :
    euclideanRegularVertex k (regularVertexNext hk j) =
      euclideanPlaneOrientation.rotation ((2 * Real.pi) / (k : ℝ))
        (euclideanRegularVertex k j) := by
  simpa [regularStepAngle_eq_two_pi_div] using
    euclideanRegularVertex_next hk j

/-- Positive regular divisions give pairwise distinct Euclidean vertices. -/
theorem euclideanRegularVertex_injective {k : ℕ} (hk : 0 < k) :
    Function.Injective (euclideanRegularVertex k) := by
  intro i j hij
  apply regularVertex_injective hk
  have hp : Vec.toProd (regularVertex k i) =
      Vec.toProd (regularVertex k j) := by
    simpa [euclideanRegularVertex] using
      congrArg euclideanPlaneToPair hij
  simpa only [Vec.ofProd_toProd] using congrArg Vec.ofProd hp

/-- The Euclidean image of a positive regular orbit has exactly `k` states. -/
theorem euclideanRegularVertex_ncard_range {k : ℕ} (hk : 0 < k) :
    (Set.range (euclideanRegularVertex k)).ncard = k := by
  rw [Set.ncard_range_of_injective (euclideanRegularVertex_injective hk),
    Nat.card_fin]

section InterfaceChecks

#check realTrigKernel_act_euclidean_eq_rotation
#check euclideanRegularVertex
#check norm_euclideanRegularVertex
#check euclideanRegularVertex_mem_unitSphere
#check regularStepAngle_eq_two_pi_div
#check euclideanRegularVertex_next
#check euclideanRegularVertex_next_two_pi_div
#check euclideanRegularVertex_injective
#check euclideanRegularVertex_ncard_range

end InterfaceChecks

end

end DkMath.CosmicFormula.Rotation.CF2D
