/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.DkReal.SemanticCF2DNormalize
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
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

/-- Coordinate insertion commutes with negation. -/
theorem pairToEuclideanPlane_neg (p : ℝ × ℝ) :
    pairToEuclideanPlane (-p.1, -p.2) = -pairToEuclideanPlane p := by
  apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
  ext i
  fin_cases i <;> simp [pairToEuclideanPlane]

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

/-!
## Oriented angle interpretation

The standard orientation is pulled back from Mathlib's complex-plane
orientation through the orthonormal basis equivalence. This fixes the sign
convention before mentioning `pi / 2`.
-/

/-- Standard Euclidean-plane coordinates interpreted as a complex number. -/
def euclideanPlaneComplexIsometry : EuclideanPlane ≃ₗᵢ[ℝ] ℂ :=
  (EuclideanSpace.basisFun (Fin 2) ℝ).equiv
    Complex.orthonormalBasisOneI (Equiv.refl (Fin 2))

local instance euclideanPlaneFinrankTwo :
    Fact (Module.finrank ℝ EuclideanPlane = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- The orientation whose positive quarter-turn agrees with multiplication by `I`. -/
def euclideanPlaneOrientation : Orientation ℝ EuclideanPlane (Fin 2) :=
  (Orientation.map (Fin 2) euclideanPlaneComplexIsometry.toLinearEquiv).symm
    Complex.orientation

/-- The chosen orientation transports to Mathlib's standard complex orientation. -/
theorem euclideanPlaneOrientation_map_complex :
    Orientation.map (Fin 2) euclideanPlaneComplexIsometry.toLinearEquiv
      euclideanPlaneOrientation = Complex.orientation := by
  exact Equiv.apply_symm_apply _ _

/-- Complex coordinates of the explicit quarter-turn are multiplication by `I`. -/
theorem euclideanPlaneComplexIsometry_quarterTurn (v : EuclideanPlane) :
    euclideanPlaneComplexIsometry (quarterTurnLinearIsometry v) =
      Complex.I * euclideanPlaneComplexIsometry v := by
  simp only [euclideanPlaneComplexIsometry, OrthonormalBasis.equiv, quarterTurnLinearIsometry,
    quarterTurnLinearEquiv, pairToEuclideanPlane, euclideanPlaneToPair,
    ContinuousLinearEquiv.finTwoArrow_apply, Fin.isValue, PiLp.continuousLinearEquiv_apply,
    ContinuousLinearEquiv.finTwoArrow_symm_apply, PiLp.continuousLinearEquiv_symm_apply,
    LinearIsometryEquiv.coe_mk, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    LinearIsometryEquiv.trans_apply, Complex.orthonormalBasisOneI_repr_symm_apply,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_refl, Equiv.refl_apply,
    EuclideanSpace.basisFun_repr, Matrix.cons_val_zero, Complex.ofReal_neg, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
/- original simp
  simp [euclideanPlaneComplexIsometry, quarterTurnLinearIsometry,
    quarterTurnLinearEquiv, pairToEuclideanPlane, euclideanPlaneToPair,
    OrthonormalBasis.equiv]
-/
  change
    (-(v 1 : ℂ) + (v 0 : ℂ) * Complex.I) =
      Complex.I * ((v 0 : ℂ) + (v 1 : ℂ) * Complex.I)
  rw [mul_add, ← mul_assoc,
    show Complex.I * (v 1 : ℂ) = (v 1 : ℂ) * Complex.I by ring,
    mul_assoc, Complex.I_mul_I]
  ring

/-- The chosen orientation's right-angle rotation is the explicit quarter-turn. -/
theorem rightAngleRotation_eq_quarterTurn :
    euclideanPlaneOrientation.rightAngleRotation =
      quarterTurnLinearIsometry := by
  apply LinearIsometryEquiv.ext
  intro v
  apply euclideanPlaneComplexIsometry.injective
  rw [euclideanPlaneOrientation.rightAngleRotation_map_complex
    euclideanPlaneComplexIsometry euclideanPlaneOrientation_map_complex]
  exact (euclideanPlaneComplexIsometry_quarterTurn v).symm

/--
The explicit quarter-turn is Mathlib's oriented rotation by `pi / 2` for the
chosen standard orientation.
-/
theorem rotation_pi_div_two_eq_quarterTurn :
    euclideanPlaneOrientation.rotation (Real.pi / 2 : ℝ) =
      quarterTurnLinearIsometry := by
  rw [euclideanPlaneOrientation.rotation_pi_div_two,
    rightAngleRotation_eq_quarterTurn]

/--
The first Euclidean angle attached to the semantic four-state action.

This is not an intrinsic construction of `pi`. It is the external Euclidean
interpretation of one already-proved quarter-turn transition. The definition
is intentionally transparent so that later intrinsic normalization constants
can be compared against this standard angle by bridge theorems.
-/
def semanticQuarterTurnAngle : ℝ :=
  Real.pi / 2

@[simp]
theorem semanticQuarterTurnAngle_eq :
    semanticQuarterTurnAngle = Real.pi / 2 :=
  rfl

/--
The Euclidean angle read from `k` semantic quarter-turn phases.

This is the additive angle vocabulary for the symmetry route. It does not
assert that the intrinsic DkMath normalization constant has already been
constructed; it only records how the standard Euclidean model reads repeated
quarter-turn actions.
-/
def semanticPhaseAngle (k : ℕ) : ℝ :=
  (k : ℝ) * semanticQuarterTurnAngle

/-- The angle read from two semantic quarter-turns. -/
def semanticHalfTurnAngle : ℝ :=
  semanticPhaseAngle 2

/-- The angle read from four semantic quarter-turns. -/
def semanticFullTurnAngle : ℝ :=
  semanticPhaseAngle 4

@[simp]
theorem semanticPhaseAngle_zero :
    semanticPhaseAngle 0 = 0 := by
  simp [semanticPhaseAngle]

@[simp]
theorem semanticPhaseAngle_one :
    semanticPhaseAngle 1 = semanticQuarterTurnAngle := by
  simp [semanticPhaseAngle]

@[simp]
theorem semanticPhaseAngle_two :
    semanticPhaseAngle 2 = semanticHalfTurnAngle :=
  rfl

@[simp]
theorem semanticPhaseAngle_three :
    semanticPhaseAngle 3 = 3 * Real.pi / 2 := by
  simp [semanticPhaseAngle, semanticQuarterTurnAngle]
  ring

@[simp]
theorem semanticPhaseAngle_four :
    semanticPhaseAngle 4 = semanticFullTurnAngle :=
  rfl

/--
Semantic phase angles add by adding their phase indices.

This is the Euclidean angle-side vocabulary for the later theorem that
successive semantic actions correspond to angle addition.
-/
theorem semanticPhaseAngle_add (m n : ℕ) :
    semanticPhaseAngle (m + n) =
      semanticPhaseAngle m + semanticPhaseAngle n := by
  simp [semanticPhaseAngle]
  ring

@[simp]
theorem semanticHalfTurnAngle_eq_pi :
    semanticHalfTurnAngle = Real.pi := by
  simp [semanticHalfTurnAngle, semanticPhaseAngle, semanticQuarterTurnAngle]
  ring_nf

@[simp]
theorem semanticFullTurnAngle_eq_two_pi :
    semanticFullTurnAngle = 2 * Real.pi := by
  simp [semanticFullTurnAngle, semanticPhaseAngle, semanticQuarterTurnAngle]
  ring

/--
Rotating by the semantic quarter-turn angle is the explicit coordinate
quarter-turn.

The theorem packages the first `theta` value for the Euclidean interpretation:
the pre-geometric action supplies the operation, while the Euclidean model
reads that operation as angle `pi / 2`.
-/
theorem rotation_semanticQuarterTurnAngle_eq_quarterTurn :
    euclideanPlaneOrientation.rotation semanticQuarterTurnAngle =
      quarterTurnLinearIsometry := by
  simp [semanticQuarterTurnAngle, rotation_pi_div_two_eq_quarterTurn]

/--
Rotating by the semantic half-turn angle is negation on the Euclidean plane.

This is the `theta = pi` reading of two semantic quarter-turns.
-/
theorem rotation_semanticHalfTurnAngle_eq_neg :
    euclideanPlaneOrientation.rotation semanticHalfTurnAngle =
      LinearIsometryEquiv.neg ℝ := by
  simp [semanticHalfTurnAngle_eq_pi]

/--
Rotating by the semantic full-turn angle is the identity on the Euclidean
plane.

This is the `theta = 2 * pi` reading of four semantic quarter-turns. It is the
Euclidean angle counterpart of exact order four.
-/
theorem rotation_semanticFullTurnAngle_eq_refl :
    euclideanPlaneOrientation.rotation semanticFullTurnAngle =
      LinearIsometryEquiv.refl ℝ EuclideanPlane := by
  ext v
  simp [semanticFullTurnAngle_eq_two_pi]

/--
Rotating by three semantic quarter-turns is the inverse coordinate
quarter-turn.

This completes the Euclidean angle reading of the four-state table at the
operation level: `0` is identity, `1` is quarter-turn, `2` is negation, and
`3` is the reverse quarter-turn.
-/
theorem rotation_semanticPhaseAngle_three (v : EuclideanPlane) :
    euclideanPlaneOrientation.rotation (semanticPhaseAngle 3) v =
      pairToEuclideanPlane
        ((euclideanPlaneToPair v).2, -(euclideanPlaneToPair v).1) := by
  have hangle :
      (semanticPhaseAngle 3 : Real.Angle) =
        ((Real.pi + Real.pi / 2 : ℝ) : Real.Angle) := by
    have hreal : semanticPhaseAngle 3 = Real.pi + Real.pi / 2 := by
      rw [semanticPhaseAngle_three]
      ring
    exact congrArg (fun x : ℝ => (x : Real.Angle)) hreal
  rw [hangle]
  rw [Real.Angle.coe_add]
  rw [← euclideanPlaneOrientation.rotation_rotation
    (Real.pi : Real.Angle) ((Real.pi / 2 : ℝ) : Real.Angle) v]
  rw [euclideanPlaneOrientation.rotation_pi_div_two,
    rightAngleRotation_eq_quarterTurn]
  rw [euclideanPlaneOrientation.rotation_pi_apply]
  apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
  ext i
  fin_cases i <;> simp [quarterTurnLinearIsometry,
    quarterTurnLinearEquiv, pairToEuclideanPlane, euclideanPlaneToPair]

end

end DkMath.CosmicFormula.Rotation.CF2D

namespace DkMath.Analysis.DkNNRealQ

open DkMath.CosmicFormula.Rotation.CF2D

noncomputable section

local instance euclideanPlaneFinrankTwo :
    Fact (Module.finrank ℝ EuclideanPlane = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

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

/--
Under the Euclidean coordinate bridge, the semantic core-zero action is
Mathlib's oriented rotation by `pi / 2`.

This theorem composes the pre-geometric semantic-action bridge with the
chosen Euclidean orientation. It is an external interpretation of the action,
not an intrinsic construction of `pi`.
-/
theorem pairToEuclideanPlane_semanticAct_eq_rotation_pi_div_two
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    pairToEuclideanPlane (Vec.toProd (semanticAct r z)) =
      euclideanPlaneOrientation.rotation (Real.pi / 2 : ℝ)
        (pairToEuclideanPlane (Vec.toProd z)) := by
  rw [pairToEuclideanPlane_semanticAct_of_core_eq_zero hcore,
    rotation_pi_div_two_eq_quarterTurn]

/--
Under the Euclidean coordinate bridge, one semantic core-zero action is
rotation by the DkMath semantic quarter-turn angle.

This is the main-line angle bridge for the present stage. The algebraic
four-state transition is already available before circles or polar
coordinates are introduced; the Euclidean model later reads that transition
as the angle `theta = pi / 2`.
-/
theorem pairToEuclideanPlane_semanticAct_eq_rotation_semanticQuarterTurnAngle
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    pairToEuclideanPlane (Vec.toProd (semanticAct r z)) =
      euclideanPlaneOrientation.rotation semanticQuarterTurnAngle
        (pairToEuclideanPlane (Vec.toProd z)) := by
  simpa [semanticQuarterTurnAngle] using
    pairToEuclideanPlane_semanticAct_eq_rotation_pi_div_two hcore z

/--
Iterate notation for the zero-action identity bridge.

This is the first row of the four-state angle table.
-/
theorem pairToEuclideanPlane_semanticActIter_zero_eq_rotation_semanticPhaseAngle
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    pairToEuclideanPlane (Vec.toProd (semanticActIter r 0 z)) =
      euclideanPlaneOrientation.rotation (semanticPhaseAngle 0)
        (pairToEuclideanPlane (Vec.toProd z)) := by
  simp [semanticPhaseAngle_zero]

/--
Iterate notation for the one-action quarter-turn bridge.
-/
theorem pairToEuclideanPlane_semanticActIter_one_eq_rotation_semanticPhaseAngle
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    pairToEuclideanPlane (Vec.toProd (semanticActIter r 1 z)) =
      euclideanPlaneOrientation.rotation (semanticPhaseAngle 1)
        (pairToEuclideanPlane (Vec.toProd z)) := by
  simpa [semanticPhaseAngle_one] using
    pairToEuclideanPlane_semanticAct_eq_rotation_semanticQuarterTurnAngle
      hcore z

/--
Under the Euclidean coordinate bridge, two semantic core-zero actions are
rotation by the semantic half-turn angle.

This is the first action-iteration bridge: the algebraic two-step action is
negation of both coordinates, and the Euclidean angle reading is
`theta = pi`.
-/
theorem pairToEuclideanPlane_semanticAct_twice_eq_rotation_semanticHalfTurnAngle
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    pairToEuclideanPlane (Vec.toProd (semanticAct r (semanticAct r z))) =
      euclideanPlaneOrientation.rotation semanticHalfTurnAngle
        (pairToEuclideanPlane (Vec.toProd z)) := by
  rw [semanticAct_twice_of_core_eq_zero hcore,
    rotation_semanticHalfTurnAngle_eq_neg]
  cases z with
  | mk x y =>
      exact pairToEuclideanPlane_neg (x, y)

/--
Iterate notation for the two-action half-turn bridge.
-/
theorem pairToEuclideanPlane_semanticActIter_two_eq_rotation_semanticPhaseAngle
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    pairToEuclideanPlane (Vec.toProd (semanticActIter r 2 z)) =
      euclideanPlaneOrientation.rotation (semanticPhaseAngle 2)
        (pairToEuclideanPlane (Vec.toProd z)) := by
  simpa [semanticPhaseAngle_two] using
    pairToEuclideanPlane_semanticAct_twice_eq_rotation_semanticHalfTurnAngle
      hcore z

/--
Under the Euclidean coordinate bridge, three semantic core-zero actions are
rotation by `semanticPhaseAngle 3`.

This fills the remaining nontrivial state in the order-four table. Algebraic
threefold action is the reverse coordinate exchange, and the Euclidean model
reads it as three quarter-turns.
-/
theorem pairToEuclideanPlane_semanticActIter_three_eq_rotation_semanticPhaseAngle
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    pairToEuclideanPlane (Vec.toProd (semanticActIter r 3 z)) =
      euclideanPlaneOrientation.rotation (semanticPhaseAngle 3)
        (pairToEuclideanPlane (Vec.toProd z)) := by
  rw [semanticActIter_three_of_core_eq_zero hcore,
    rotation_semanticPhaseAngle_three]
  cases z with
  | mk x y =>
      simp [Vec.toProd, euclideanPlaneToPair_pairToEuclideanPlane]

/--
Under the Euclidean coordinate bridge, four semantic core-zero actions are
rotation by the semantic full-turn angle.

This is the finite-order bridge for the present stage: exact order four on
the semantic side is read as the Euclidean identity rotation by `2 * pi`.
-/
theorem pairToEuclideanPlane_semanticAct_four_eq_rotation_semanticFullTurnAngle
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    pairToEuclideanPlane
        (Vec.toProd
          (semanticAct r (semanticAct r (semanticAct r (semanticAct r z))))) =
      euclideanPlaneOrientation.rotation semanticFullTurnAngle
        (pairToEuclideanPlane (Vec.toProd z)) := by
  rw [semanticAct_four_of_core_eq_zero hcore,
    rotation_semanticFullTurnAngle_eq_refl]
  rfl

/--
Iterate notation for the four-action full-turn bridge.
-/
theorem pairToEuclideanPlane_semanticActIter_four_eq_rotation_semanticPhaseAngle
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    pairToEuclideanPlane (Vec.toProd (semanticActIter r 4 z)) =
      euclideanPlaneOrientation.rotation (semanticPhaseAngle 4)
        (pairToEuclideanPlane (Vec.toProd z)) := by
  rw [semanticActIter_four_of_core_eq_zero hcore,
    semanticPhaseAngle_four, rotation_semanticFullTurnAngle_eq_refl]
  rfl

/--
Modulo-four Euclidean angle reading of the semantic action iterate.

The semantic side first reduces the iterate index to `k % 4`. The remaining
four cases are exactly the finite rotation table: identity, quarter-turn,
half-turn, and reverse quarter-turn.
-/
theorem pairToEuclideanPlane_semanticActIter_eq_rotation_semanticPhaseAngle_mod_four
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (k : ℕ) (z : Vec ℝ) :
    pairToEuclideanPlane (Vec.toProd (semanticActIter r k z)) =
      euclideanPlaneOrientation.rotation (semanticPhaseAngle (k % 4))
        (pairToEuclideanPlane (Vec.toProd z)) := by
  let n := k % 4
  have hnlt : n < 4 := by
    dsimp [n]
    exact Nat.mod_lt k (by norm_num)
  have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by
    omega
  rw [semanticActIter_eq_mod_four_of_core_eq_zero hcore]
  rcases hcases with hzero | hone | htwo | hthree
  · have hkmod : k % 4 = 0 := by
      simpa [n] using hzero
    rw [hkmod]
    exact pairToEuclideanPlane_semanticActIter_zero_eq_rotation_semanticPhaseAngle
      r z
  · have hkmod : k % 4 = 1 := by
      simpa [n] using hone
    rw [hkmod]
    exact pairToEuclideanPlane_semanticActIter_one_eq_rotation_semanticPhaseAngle
      hcore z
  · have hkmod : k % 4 = 2 := by
      simpa [n] using htwo
    rw [hkmod]
    exact pairToEuclideanPlane_semanticActIter_two_eq_rotation_semanticPhaseAngle
      hcore z
  · have hkmod : k % 4 = 3 := by
      simpa [n] using hthree
    rw [hkmod]
    exact pairToEuclideanPlane_semanticActIter_three_eq_rotation_semanticPhaseAngle
      hcore z

end

end DkMath.Analysis.DkNNRealQ
