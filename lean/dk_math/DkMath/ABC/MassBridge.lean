/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.Square
import DkMath.ABC.Rad
import DkMath.CosmicFormula.Mass.Decompose

#print "file: DkMath.ABC.MassBridge"

namespace DkMath.ABC

open DkMath.CosmicFormula.Mass

/--
Canonical support-mass alias on the ABC side.

At this stage the bridge reads support mass simply as the radical `rad`.
-/
def supportMass (n : ℕ) : ℕ :=
  DkMath.ABC.Rad.rad n

theorem supportMass_eq_abc_rad (n : ℕ) :
    supportMass n = ABC.rad n := by
  simp [supportMass, DkMath.ABC.Rad.rad, ABC.rad]

/-- `Big = Body + Gap` re-exported on the ABC side. -/
theorem abc_big_eq_body_add_gap_mass (d x u : ℕ) :
    CosmicResidualMassAPI.ofResidualNat.massBig d x u =
      CosmicResidualMassAPI.ofResidualNat.massBody d x u +
        CosmicResidualMassAPI.ofResidualNat.massGap d x u := by
  exact mass_big_eq_mass_body_add_mass_gap_of_residualNat d x u

/-- The gap mass is bounded above by the big mass. -/
theorem abc_gap_mass_le_big_mass (d x u : ℕ) :
    CosmicResidualMassAPI.ofResidualNat.massGap d x u ≤
      CosmicResidualMassAPI.ofResidualNat.massBig d x u := by
  simpa [CosmicResidualMassAPI.ofResidualNat] using
    DkMath.CosmicFormula.gap_le_big d x u

/-- On the `Nat` residual side, the residual mass is exactly the gap mass. -/
theorem abc_residual_eq_gap_mass (d x u : ℕ) :
    CosmicResidualMassAPI.ofResidualNat.massResidual d x u =
      CosmicResidualMassAPI.ofResidualNat.massGap d x u := by
  exact mass_residual_eq_mass_gap_of_residualNat d x u

/--
For squarefree `n`, the support mass already captures all of `n`.

The theorem is stated as a lower bound because later bridge users often read
`supportMass` as a coarse mass that should not fall below the squarefree part.
-/
theorem abc_squarefree_support_lower_bound
    {n : ℕ} (hn0 : n ≠ 0) (hsq : Squarefree n) :
    n ≤ supportMass n := by
  have hrad : ABC.rad n = n := by
    simpa [ABC.squarefree] using ABC.rad_eq_self_of_squarefree hn0 hsq
  have hsupp : supportMass n = n := by
    rw [supportMass_eq_abc_rad]
    exact hrad
  exact le_of_eq hsupp.symm

/-- The support mass still divides the original natural mass. -/
theorem abc_supportMass_dvd_self {n : ℕ} (hn0 : n ≠ 0) :
    supportMass n ∣ n := by
  simpa [supportMass] using DkMath.ABC.Rad.rad_dvd_nonzero n hn0

end DkMath.ABC
