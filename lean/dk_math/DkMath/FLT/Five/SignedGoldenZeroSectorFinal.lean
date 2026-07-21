/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.SignedGoldenZeroSectorFactorization
import DkMath.FLT.Five.SignedGoldenZeroSectorDescent
import DkMath.FLT.Five.SignedGoldenClosure

/-!
# Closing the zero-sector receiver

Every exact factor packet retains its inversion source. That source produces a
descent packet, and strict infinite descent proves it impossible. The resulting
factor exclusion is converted back to the source-level arithmetic contract
used by `SignedGoldenClosure`.
-/

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

/-- Infinite descent proves the public zero-sector arithmetic exclusion. -/
theorem goldenZeroSectorArithmeticExclusion :
    GoldenZeroSectorArithmeticExclusion :=
  goldenZeroSectorArithmeticExclusion_of_factorExclusion
    goldenZeroSectorFactorExclusion

end DkMath.FLT.Five
