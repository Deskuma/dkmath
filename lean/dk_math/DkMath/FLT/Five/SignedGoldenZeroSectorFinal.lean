/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.SignedGoldenZeroSectorFactorization
import DkMath.FLT.Five.SignedGoldenZeroSectorDescent
import DkMath.FLT.Five.SignedGoldenClosure

#print "file: DkMath.FLT.Five.SignedGoldenZeroSectorFinal"

namespace DkMath.FLT.Five

/-- Infinite descent excludes each of the three certified factor branches. -/
theorem goldenZeroSectorFactorExclusion : GoldenZeroSectorFactorExclusion := by
  intro packet
  exact goldenZeroSectorCandidate_false packet.inversion.source

/-- The factor-packet receiver has exactly the public zero-sector contract. -/
theorem goldenZeroSectorArithmeticExclusion_of_factorExclusion
    (hFactor : GoldenZeroSectorFactorExclusion) :
    GoldenZeroSectorArithmeticExclusion :=
  goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion hFactor

/-- Infinite descent discharges the exact arithmetic receiver left by closure. -/
theorem goldenZeroSectorArithmeticExclusion :
    GoldenZeroSectorArithmeticExclusion :=
  goldenZeroSectorArithmeticExclusion_of_factorExclusion
    goldenZeroSectorFactorExclusion

end DkMath.FLT.Five
