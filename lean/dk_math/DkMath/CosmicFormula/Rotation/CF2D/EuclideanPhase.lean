/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.DkReal.SemanticCF2DNormalize
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Homeomorph.Defs

#print "file: DkMath.CosmicFormula.Rotation.CF2D.EuclideanPhase"

/-!
# Euclidean interpretation of the CF2D square-mass boundary

This module does not construct a new path. It interprets the already-built
`q2` level-set path as a path in the coordinate equation

`x^2 + y^2 = rho2`.

The radius is represented by its square, so the bridge remains valid for the
degenerate zero boundary. Positive square mass later yields the ordinary
positive-radius circle with radius `sqrt rho2`.

No angle coordinate or trigonometric parametrization is introduced here.
-/

namespace DkMath.CosmicFormula.Rotation.CF2D

noncomputable section

/--
The two-coordinate Euclidean circle equation with squared radius `rho2`.

For `rho2 = 0` this is the degenerate one-point boundary.
-/
def EuclideanCircleSq (rho2 : ℝ) :=
  {p : ℝ × ℝ // p.1 ^ 2 + p.2 ^ 2 = rho2}

instance (rho2 : ℝ) : TopologicalSpace (EuclideanCircleSq rho2) :=
  inferInstanceAs
    (TopologicalSpace {p : ℝ × ℝ // p.1 ^ 2 + p.2 ^ 2 = rho2})

/-- The standard two-dimensional real Euclidean space. -/
abbrev EuclideanPlane :=
  EuclideanSpace ℝ (Fin 2)

/--
The standard L2 metric sphere whose radius is the square root of `rho2`.

For `rho2 = 0`, Mathlib's sphere is the singleton origin.
-/
def EuclideanSphereSq (rho2 : ℝ) :=
  {v : EuclideanPlane // v ∈ Metric.sphere 0 (Real.sqrt rho2)}

instance (rho2 : ℝ) : TopologicalSpace (EuclideanSphereSq rho2) :=
  inferInstanceAs
    (TopologicalSpace
      {v : EuclideanPlane // v ∈ Metric.sphere 0 (Real.sqrt rho2)})

namespace Vec

/-- Real CF2D square mass is always nonnegative. -/
theorem q2_nonneg (z : Vec ℝ) :
    0 ≤ q2 z := by
  exact add_nonneg (sq_nonneg z.core) (sq_nonneg z.beam)

/-- Real square mass vanishes exactly at the zero state. -/
theorem q2_eq_zero_iff (z : Vec ℝ) :
    q2 z = 0 ↔ z = Vec.mk 0 0 := by
  cases z with
  | mk x y =>
      simp only [q2, Vec.mk.injEq]
      constructor
      · intro h
        have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
        have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
        exact ⟨hx, hy⟩
      · rintro ⟨rfl, rfl⟩
        norm_num

/-- A nonzero real CF2D state has strictly positive square mass. -/
theorem q2_pos_iff_ne_zero (z : Vec ℝ) :
    0 < q2 z ↔ z ≠ Vec.mk 0 0 := by
  constructor
  · intro h hz
    rw [hz] at h
    norm_num [q2] at h
  · intro hz
    have hq : q2 z ≠ 0 := by
      intro hzero
      exact hz ((q2_eq_zero_iff z).1 hzero)
    exact lt_of_le_of_ne (q2_nonneg z) hq.symm

end Vec

/--
The abstract CF2D level set is homeomorphic to its explicit two-coordinate
Euclidean circle equation.

This is an interpretation theorem: both sides contain the same coordinates
and the same quadratic boundary equation.
-/
def levelSetHomeomorphEuclideanCircleSq (rho2 : ℝ) :
    LevelSet ℝ rho2 ≃ₜ EuclideanCircleSq rho2 where
  toFun z := ⟨Vec.toProd z.1, z.2⟩
  invFun p := ⟨Vec.ofProd p.1, by simpa [Vec.q2, Vec.ofProd] using p.2⟩
  left_inv z := by
    apply Subtype.ext
    exact Vec.ofProd_toProd z.1
  right_inv p := by
    apply Subtype.ext
    exact Vec.toProd_ofProd p.1
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_vecToProd.comp (continuous_levelSet_val rho2)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact
      (Continuous.vec_mk continuous_fst continuous_snd).comp
        continuous_subtype_val

/-- The zero squared-radius Euclidean circle contains only the origin. -/
theorem euclideanCircleSq_zero_eq_origin
    (p : EuclideanCircleSq 0) :
    p = ⟨(0, 0), by norm_num⟩ := by
  apply Subtype.ext
  rcases p with ⟨⟨x, y⟩, h⟩
  have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  simp [hx, hy]

/-!
## Standard Euclidean-space bridge

The coordinate equation is now transported to Mathlib's L2 Euclidean plane.
Unlike the ordinary product norm on `Real × Real`, this norm has square equal
to the sum of the two coordinate squares.
-/

/-- Insert a coordinate pair into the standard two-dimensional Euclidean space. -/
def pairToEuclideanPlane (p : ℝ × ℝ) : EuclideanPlane :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm
    ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm p)

/-- Read the two standard coordinates of the Euclidean plane. -/
def euclideanPlaneToPair (v : EuclideanPlane) : ℝ × ℝ :=
  ContinuousLinearEquiv.finTwoArrow ℝ ℝ
    (EuclideanSpace.equiv (Fin 2) ℝ v)

@[simp]
theorem euclideanPlaneToPair_pairToEuclideanPlane (p : ℝ × ℝ) :
    euclideanPlaneToPair (pairToEuclideanPlane p) = p := by
  simp [euclideanPlaneToPair, pairToEuclideanPlane]

@[simp]
theorem pairToEuclideanPlane_euclideanPlaneToPair (v : EuclideanPlane) :
    pairToEuclideanPlane (euclideanPlaneToPair v) = v := by
  ext i
  fin_cases i <;> rfl

/-- The coordinate insertion into the Euclidean plane is continuous. -/
theorem continuous_pairToEuclideanPlane :
    Continuous pairToEuclideanPlane := by
  exact
    (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.continuous

/-- Reading the two Euclidean coordinates is continuous. -/
theorem continuous_euclideanPlaneToPair :
    Continuous euclideanPlaneToPair := by
  exact
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).continuous.comp
      (EuclideanSpace.equiv (Fin 2) ℝ).continuous

/-- The L2 norm square of an inserted pair is its coordinate square sum. -/
theorem pairToEuclideanPlane_norm_sq (p : ℝ × ℝ) :
    ‖pairToEuclideanPlane p‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  rcases p with ⟨x, y⟩
  rfl

/--
For a nonnegative squared radius, the coordinate-circle equation is
homeomorphic to Mathlib's standard L2 metric sphere.
-/
def euclideanCircleSqHomeomorphSphere
    {rho2 : ℝ} (hrho : 0 ≤ rho2) :
    EuclideanCircleSq rho2 ≃ₜ EuclideanSphereSq rho2 where
  toFun p := ⟨pairToEuclideanPlane p.1, by
    rw [Metric.mem_sphere, dist_zero_right]
    apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [pairToEuclideanPlane_norm_sq, Real.sq_sqrt hrho]
    exact p.2⟩
  invFun v := ⟨euclideanPlaneToPair v.1, by
    have hnorm : ‖v.1‖ = Real.sqrt rho2 := by
      have h := v.2
      rw [Metric.mem_sphere, dist_zero_right] at h
      exact h
    calc
      (euclideanPlaneToPair v.1).1 ^ 2
          + (euclideanPlaneToPair v.1).2 ^ 2 =
          ‖v.1‖ ^ 2 := by
            rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
            rfl
      _ = rho2 := by rw [hnorm, Real.sq_sqrt hrho]⟩
  left_inv p := by
    apply Subtype.ext
    exact euclideanPlaneToPair_pairToEuclideanPlane p.1
  right_inv v := by
    apply Subtype.ext
    exact pairToEuclideanPlane_euclideanPlaneToPair v.1
  continuous_toFun :=
    Continuous.subtype_mk
      (continuous_pairToEuclideanPlane.comp continuous_subtype_val) _
  continuous_invFun :=
    Continuous.subtype_mk
      (continuous_euclideanPlaneToPair.comp continuous_subtype_val) _

/-- A positive squared radius gives a genuinely positive metric-sphere radius. -/
theorem sqrt_pos_of_sqRadius_pos {rho2 : ℝ} (hrho : 0 < rho2) :
    0 < Real.sqrt rho2 :=
  Real.sqrt_pos.2 hrho

/-!
## Quarter-turn as a linear isometry

The terminology is introduced only after reaching the standard Euclidean
plane. The construction itself remains the coordinate map `(x,y) ↦ (-y,x)`.
-/

/-- The coordinate quarter-turn as a linear equivalence of the Euclidean plane. -/
def quarterTurnLinearEquiv : EuclideanPlane ≃ₗ[ℝ] EuclideanPlane where
  toFun v :=
    pairToEuclideanPlane
      (-(euclideanPlaneToPair v).2, (euclideanPlaneToPair v).1)
  invFun v :=
    pairToEuclideanPlane
      ((euclideanPlaneToPair v).2, -(euclideanPlaneToPair v).1)
  left_inv v := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
    ext i
    fin_cases i <;>
      simp [pairToEuclideanPlane, euclideanPlaneToPair]
  right_inv v := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
    ext i
    fin_cases i <;>
      simp [pairToEuclideanPlane, euclideanPlaneToPair]
  map_add' u v := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
    ext i
    fin_cases i <;> simp [pairToEuclideanPlane, euclideanPlaneToPair]
    ring
  map_smul' c v := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
    ext i
    fin_cases i <;> simp [pairToEuclideanPlane, euclideanPlaneToPair]

/-- The coordinate quarter-turn preserves the Euclidean L2 norm. -/
theorem quarterTurnLinearEquiv_norm (v : EuclideanPlane) :
    ‖quarterTurnLinearEquiv v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_two, Fin.sum_univ_two]
  simp [quarterTurnLinearEquiv, pairToEuclideanPlane, euclideanPlaneToPair]
  ring

/-- The standard coordinate quarter-turn as a Euclidean linear isometry equivalence. -/
def quarterTurnLinearIsometry :
    EuclideanPlane ≃ₗᵢ[ℝ] EuclideanPlane :=
  LinearIsometryEquiv.mk quarterTurnLinearEquiv quarterTurnLinearEquiv_norm

/-- Coordinate form of the standard quarter-turn linear isometry. -/
theorem euclideanPlaneToPair_quarterTurn (v : EuclideanPlane) :
    euclideanPlaneToPair (quarterTurnLinearIsometry v) =
      (-(euclideanPlaneToPair v).2, (euclideanPlaneToPair v).1) := by
  simp [quarterTurnLinearIsometry, quarterTurnLinearEquiv]

end

end DkMath.CosmicFormula.Rotation.CF2D

namespace DkMath.Analysis.DkNNRealQ

open DkMath.CosmicFormula.Rotation.CF2D

noncomputable section

/--
The normalized closed level-set path interpreted in the explicit Euclidean
circle equation with squared radius `q2 z`.
-/
def normalizedClosedEuclideanCircleSqPath
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    Path
      (levelSetHomeomorphEuclideanCircleSq (Vec.q2 z)
        (semanticPhaseLevelPoint r z 0))
      (levelSetHomeomorphEuclideanCircleSq (Vec.q2 z)
        (semanticPhaseLevelPoint r z 0)) :=
  (normalizedClosedLevelFourPhasePath hcore z).map
    (levelSetHomeomorphEuclideanCircleSq (Vec.q2 z)).continuous

/--
The normalized closed path interpreted in Mathlib's standard two-dimensional
L2 metric sphere of radius `sqrt (q2 z)`.
-/
def normalizedClosedEuclideanSpherePath
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    Path
      (euclideanCircleSqHomeomorphSphere (Vec.q2_nonneg z)
        (levelSetHomeomorphEuclideanCircleSq (Vec.q2 z)
          (semanticPhaseLevelPoint r z 0)))
      (euclideanCircleSqHomeomorphSphere (Vec.q2_nonneg z)
        (levelSetHomeomorphEuclideanCircleSq (Vec.q2 z)
          (semanticPhaseLevelPoint r z 0))) :=
  (normalizedClosedEuclideanCircleSqPath hcore z).map
    (euclideanCircleSqHomeomorphSphere
      (rho2 := Vec.q2 z) (Vec.q2_nonneg z)).continuous

/--
Under the Euclidean coordinate bridge, the semantic core-zero action is the
standard quarter-turn linear isometry.
-/
theorem pairToEuclideanPlane_semanticAct_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    pairToEuclideanPlane (Vec.toProd (semanticAct r z)) =
      quarterTurnLinearIsometry
        (pairToEuclideanPlane (Vec.toProd z)) := by
  rw [semanticAct_of_core_eq_zero hcore]
  apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
  ext i
  fin_cases i <;>
    simp [pairToEuclideanPlane, quarterTurnLinearIsometry,
      quarterTurnLinearEquiv, euclideanPlaneToPair, Vec.toProd]

end

end DkMath.Analysis.DkNNRealQ
