/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionCenteredImage589
import DkMathTest.FLT.Seven.SevenRamifiedFusionModFortyTwoCheapAllocation

#print "file: DkMathTest.FLT.Seven.SevenRamifiedFusionCenteredImage589"

namespace DkMathTest.FLT.Seven

open DkMath.FLT.Seven

example : centeredSevenSextic (7 ^ 27) 52382010648825907313680 < 448 * 589 ^ 49 :=
  centeredSevenSextic_589_bracket.1
example : 448 * 589 ^ 49 < centeredSevenSextic (7 ^ 27) (52382010648825907313680 + 1) :=
  centeredSevenSextic_589_bracket.2
example : ¬ ∃ q : ℕ, centeredSevenSextic (7 ^ 27) q = 448 * 589 ^ 49 :=
  centeredSevenSextic_589_no_image
example : ¬ (NestedGNAllocationCondition 589 1 ∨ NestedRHSAllocationCondition 589 1) :=
  nestedAllocation_589_one_excluded
example : ¬ SixthPowerSievedNestedCondition 589 := sixthPowerSievedNestedCondition_589_excluded

-- The cheap candidate survives even though every exact allocation is excluded.
example : HasModFortyTwoCheapAllocation 589 ∧ ¬ SixthPowerSievedNestedCondition 589 :=
  ⟨⟨1, candidate589_passes⟩, sixthPowerSievedNestedCondition_589_excluded⟩

open RamifiedSignedRootRoutingPacket.QuotientPrimeSupport
example (p : RamifiedSignedRootRoutingPacket)
    (hcore : internalDepthFourSeventhCore p = 589) :
    ¬ InternalDepthFourCounterexampleReconstructionObligation p :=
  no_reconstruction_of_core_eq_589 p hcore

#print axioms DkMath.FLT.Seven.centeredSevenSextic_589_bracket
#print axioms DkMath.FLT.Seven.centeredSevenSextic_589_no_image
#print axioms DkMath.FLT.Seven.nestedAllocation_589_one_excluded
#print axioms DkMath.FLT.Seven.sixthPowerSievedNestedCondition_589_excluded
#print axioms DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.no_reconstruction_of_core_eq_589

end DkMathTest.FLT.Seven
