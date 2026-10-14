/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2

namespace DkMath.NumberGeometry
noncomputable section

/-!
# Two-point Euclidean geometry

This is the neutral core of the NumberGeometry layer.  A point is a vector in
Mathlib's two-dimensional real Euclidean space; later modules may interpret a
nonzero pair as a relative gauge, but this file only defines the pair gap and
its square mass.
-/

/-- The v0 point representation: the standard real Euclidean plane. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/--
The oriented gap from source `A` to target `B`.

The direction is source-to-target: the gap of `A → B` is `B - A`.
-/
def pairVec (A B : Point) : Point := B - A

/--
The squared Euclidean distance of a pair, interpreted later as its two-point
square mass.  The ordinary distance remains Mathlib's `dist`.
-/
def pairMass (A B : Point) : ℝ := ‖pairVec A B‖ ^ 2

/-- A two-point kernel stores its pair only, including the degenerate case. -/
structure TwoPointKernel where
  source : Point
  target : Point

namespace TwoPointKernel

/-- A kernel is active exactly when its two points are separated. -/
def Active (K : TwoPointKernel) : Prop := K.source ≠ K.target

end TwoPointKernel

/-- The oriented gap of a point with itself is the zero vector. -/
@[simp]
theorem pairVec_self (A : Point) :
    pairVec A A = 0 := by
  simp [pairVec]

/-- The two-point square mass of a point with itself is zero. -/
@[simp]
theorem pairMass_self (A : Point) :
    pairMass A A = 0 := by
  simp [pairMass]

/-- The oriented gap vanishes exactly when the two points coincide. -/
theorem pairVec_eq_zero_iff (A B : Point) :
    pairVec A B = 0 ↔ A = B := by
  constructor
  · intro h
    exact (sub_eq_zero.mp h).symm
  · intro h
    subst B
    simp [pairVec]

/-- The pair mass is definitionally the squared norm of the coordinate gap. -/
theorem pairMass_eq_norm_sq (A B : Point) :
    pairMass A B = ‖B - A‖ ^ 2 := rfl

/-- The two-point square mass is always nonnegative. -/
theorem pairMass_nonneg (A B : Point) :
    0 ≤ pairMass A B := by
  exact sq_nonneg _

/-- The pair mass vanishes exactly for a degenerate pair. -/
@[simp]
theorem pairMass_eq_zero_iff (A B : Point) :
    pairMass A B = 0 ↔ A = B := by
  constructor
  · intro h
    have hmul : ‖pairVec A B‖ * ‖pairVec A B‖ = 0 := by
      simpa [pairMass, pow_two] using h
    have hnorm : ‖pairVec A B‖ = 0 := by
      rcases mul_eq_zero.mp hmul with hnorm | hnorm
      · exact hnorm
      · exact hnorm
    exact (pairVec_eq_zero_iff A B).mp (norm_eq_zero.mp hnorm)
  · intro h
    subst B
    exact pairMass_self A

/-- The pair mass is positive exactly when the two points are distinct. -/
theorem pairMass_pos_iff (A B : Point) :
    0 < pairMass A B ↔ A ≠ B := by
  constructor
  · intro h hAB
    subst B
    rw [pairMass_self A] at h
    exact (lt_irrefl 0) h
  · intro h
    have hne : pairMass A B ≠ 0 := by
      intro hzero
      exact h ((pairMass_eq_zero_iff A B).mp hzero)
    exact lt_of_le_of_ne (pairMass_nonneg A B) hne.symm

/-- Reversing the pair does not change its square mass. -/
theorem pairMass_comm (A B : Point) :
    pairMass A B = pairMass B A := by
  have hgap : B - A = -(A - B) := by
    simp [sub_eq_add_neg]
  calc
    pairMass A B = ‖B - A‖ ^ 2 := pairMass_eq_norm_sq A B
    _ = ‖-(A - B)‖ ^ 2 := by rw [hgap]
    _ = ‖A - B‖ ^ 2 := by rw [norm_neg]
    _ = pairMass B A := (pairMass_eq_norm_sq B A).symm

/-- The pair mass agrees with the squared Euclidean distance. -/
theorem pairMass_eq_dist_sq (A B : Point) :
    pairMass A B = dist A B ^ 2 := by
  have hgap : B - A = -(A - B) := by
    simp [sub_eq_add_neg]
  calc
    pairMass A B = ‖B - A‖ ^ 2 := pairMass_eq_norm_sq A B
    _ = ‖-(A - B)‖ ^ 2 := by rw [hgap]
    _ = ‖A - B‖ ^ 2 := by rw [norm_neg]
    _ = dist A B ^ 2 := by rw [dist_eq_norm]

/-- A kernel has zero pair mass exactly when it is degenerate. -/
theorem pairMass_kernel_eq_zero_iff (K : TwoPointKernel) :
    pairMass K.source K.target = 0 ↔ K.source = K.target :=
  pairMass_eq_zero_iff K.source K.target

/-- A kernel has positive pair mass exactly when it is active. -/
theorem pairMass_kernel_pos_iff_active (K : TwoPointKernel) :
    0 < pairMass K.source K.target ↔ K.Active := by
  simpa [TwoPointKernel.Active] using
    (pairMass_pos_iff K.source K.target)

end
end DkMath.NumberGeometry
