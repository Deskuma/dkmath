/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberGeometry.Radical
import DkMath.SilverRatio.SilverRatioCircle

namespace DkMath.NumberGeometry.Bridge.SilverRatio

open scoped InnerProductSpace
noncomputable section

open DkMath.NumberGeometry

/-!
# NumberGeometry calibration for the SilverRatio circle

This module gives one explicit coordinate conversion and transports the
checked SilverRatio four-point calculation into square-mass language.
-/

/-- Coordinate order is `0 ↦ p.1` and `1 ↦ p.2`. -/
def ofPair (p : ℝ × ℝ) : Point :=
  EuclideanSpace.single 0 p.1 + EuclideanSpace.single 1 p.2

/-- The NumberGeometry square mass agrees with the old coordinate formula. -/
theorem pairMass_ofPair_eq_dist_sq (p q : ℝ × ℝ) :
    pairMass (ofPair p) (ofPair q) =
      DkMath.SilverRatio.Circle.dist_sq p q := by
  rw [pairMass, pairVec, EuclideanSpace.real_norm_sq_eq]
  simp [ofPair, DkMath.SilverRatio.Circle.dist_sq]
  ring

/-- The four checked SilverRatio points lie on one NumberGeometry mass level. -/
theorem bcfg_common_massLevel :
    ∃ (O' : Point) (rho : ℝ),
      ofPair DkMath.SilverRatio.Circle.B ∈ MassLevelSet O' rho ∧
      ofPair DkMath.SilverRatio.Circle.C ∈ MassLevelSet O' rho ∧
      ofPair DkMath.SilverRatio.Circle.F ∈ MassLevelSet O' rho ∧
      ofPair DkMath.SilverRatio.Circle.G ∈ MassLevelSet O' rho := by
  rcases DkMath.SilverRatio.Circle.bcfg_concyclic with ⟨O, rho, hB, hC, hF, hG⟩
  refine ⟨ofPair O, rho, ?_, ?_, ?_, ?_⟩
  · rw [mem_massLevelSet]
    rw [pairMass_ofPair_eq_dist_sq]
    exact hB
  · rw [mem_massLevelSet]
    rw [pairMass_ofPair_eq_dist_sq]
    exact hC
  · rw [mem_massLevelSet]
    rw [pairMass_ofPair_eq_dist_sq]
    exact hF
  · rw [mem_massLevelSet]
    rw [pairMass_ofPair_eq_dist_sq]
    exact hG

end
end DkMath.NumberGeometry.Bridge.SilverRatio
