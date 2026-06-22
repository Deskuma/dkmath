/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.DkReal.SemanticCF2DNormalize
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

/--
The two-coordinate Euclidean circle equation with squared radius `rho2`.

For `rho2 = 0` this is the degenerate one-point boundary.
-/
def EuclideanCircleSq (rho2 : ℝ) :=
  {p : ℝ × ℝ // p.1 ^ 2 + p.2 ^ 2 = rho2}

instance (rho2 : ℝ) : TopologicalSpace (EuclideanCircleSq rho2) :=
  inferInstanceAs
    (TopologicalSpace {p : ℝ × ℝ // p.1 ^ 2 + p.2 ^ 2 = rho2})

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

end

end DkMath.Analysis.DkNNRealQ
