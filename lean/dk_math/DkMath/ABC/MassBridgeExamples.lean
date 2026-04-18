/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.MassBridge

#print "file: DkMath.ABC.MassBridgeExamples"

namespace DkMath.ABC.MassBridgeExamples

open DkMath.ABC
open DkMath.CosmicFormula.Mass

/-- Concrete check of the bridge identity `Big = Body + Gap`. -/
example :
    CosmicResidualMassAPI.ofResidualNat.massBig 2 3 1 =
      CosmicResidualMassAPI.ofResidualNat.massBody 2 3 1 +
        CosmicResidualMassAPI.ofResidualNat.massGap 2 3 1 := by
  exact abc_big_eq_body_add_gap_mass 2 3 1

/-- Concrete check of the bridge inequality `Gap ≤ Big`. -/
example :
    CosmicResidualMassAPI.ofResidualNat.massGap 2 3 1 ≤
      CosmicResidualMassAPI.ofResidualNat.massBig 2 3 1 := by
  exact abc_gap_mass_le_big_mass 2 3 1

/-- Concrete check of the bridge identity `residual = gap`. -/
example :
    CosmicResidualMassAPI.ofResidualNat.massResidual 2 3 1 =
      CosmicResidualMassAPI.ofResidualNat.massGap 2 3 1 := by
  exact abc_residual_eq_gap_mass 2 3 1

/-- For the prime sample `31`, support mass already captures the full mass. -/
example : 31 ≤ supportMass 31 := by
  exact abc_squarefree_support_lower_bound
    (n := 31)
    (by decide)
    (show Nat.Prime 31 by decide).squarefree

/-- The support mass still divides the original mass for a non-squarefree sample. -/
example : supportMass 12 ∣ 12 := by
  exact abc_supportMass_dvd_self (n := 12) (by decide)

end DkMath.ABC.MassBridgeExamples
