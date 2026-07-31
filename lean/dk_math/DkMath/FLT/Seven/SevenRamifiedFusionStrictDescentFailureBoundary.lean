/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicAdditiveChartBoundary
import DkMath.FLT.Seven.AwayValuationTransfer

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionStrictDescentFailureBoundary"

namespace DkMath.FLT.Seven

noncomputable section

set_option linter.style.longLine false

namespace RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

/-- The depth-four integer carrier already present inside the ramified
quadratic extraction.

This is an internal algebraic coordinate.  The definition does not claim that
it is the exceptional carrier of a new Fermat counterexample. -/
def internalDepthFourCarrier
    (p : RamifiedSignedRootRoutingPacket) : ℕ :=
  Int.natAbs
    p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.quadratic.innerRoot.snd

/-- The preceding depth-five summit carrier from which the inner quadratic
root was extracted. -/
def outerDepthFiveCarrier
    (p : RamifiedSignedRootRoutingPacket) : ℕ :=
  Int.natAbs
    p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.quadratic.canonical.terminal.summit.root.snd

/-- The extracted inner carrier has exact seven-adic depth four. -/
theorem padicValNat_internalDepthFourCarrier
    (p : RamifiedSignedRootRoutingPacket) :
    padicValNat 7 (internalDepthFourCarrier p) = 4 :=
  p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.quadratic.innerRootSnd_depth_eq_four

/-- The summit carrier immediately preceding the inner extraction has exact
seven-adic depth five. -/
theorem padicValNat_outerDepthFiveCarrier
    (p : RamifiedSignedRootRoutingPacket) :
    padicValNat 7 (outerDepthFiveCarrier p) = 5 :=
  p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.quadratic.canonical.terminal.rootSnd_depth_eq_five

/-- The ramified extraction already contains a genuine strict seven-adic depth
drop from five to four.  This is not yet a descent of Fermat
counterexamples. -/
theorem internalDepthFourCarrier_strictly_decreases
    (p : RamifiedSignedRootRoutingPacket) :
    padicValNat 7 (internalDepthFourCarrier p) <
      padicValNat 7 (outerDepthFiveCarrier p) := by
  rw [padicValNat_internalDepthFourCarrier,
    padicValNat_outerDepthFiveCarrier]
  omega

/-- Exact reconstruction obligation needed to turn the internal depth-four
coordinate into an input accepted by the existing away-counterexample
descent API.

An `AwayValuationTransferPacket` already contains a positive primitive
natural FLT7 counterexample, its away normal form, its exceptional carrier,
and the valuation-transfer equation.  The only added requirement here is the
provenance equality identifying that carrier with the extracted inner
coordinate.  This proposition is named but not inhabited. -/
def InternalDepthFourCounterexampleReconstructionObligation
    (p : RamifiedSignedRootRoutingPacket) : Prop :=
  ∃ (x y z : ℕ) (route : AwayValuationTransferPacket x y z),
    route.carrier = internalDepthFourCarrier p

/-- The same reconstruction target with the strict depth inequality displayed
explicitly. -/
def InternalDepthFourStrictDescentCandidate
    (p : RamifiedSignedRootRoutingPacket) : Prop :=
  ∃ (x y z : ℕ) (route : AwayValuationTransferPacket x y z),
    route.carrier = internalDepthFourCarrier p ∧
      padicValNat 7 route.carrier <
        padicValNat 7 (outerDepthFiveCarrier p)

/-- The strict inequality contributes no additional arithmetic obligation:
once the internal coordinate is reconstructed as the carrier of an actual
away FLT7 counterexample, the already proved depth `4 < 5` supplies the drop.

Thus the exact U1.6 failure boundary is counterexample reconstruction, not a
missing valuation inequality. -/
theorem internalDepthFourCounterexampleReconstructionObligation_iff_strictDescentCandidate
    (p : RamifiedSignedRootRoutingPacket) :
    InternalDepthFourCounterexampleReconstructionObligation p ↔
      InternalDepthFourStrictDescentCandidate p := by
  constructor
  · rintro ⟨x, y, z, route, hcarrier⟩
    refine ⟨x, y, z, route, hcarrier, ?_⟩
    rw [hcarrier]
    exact internalDepthFourCarrier_strictly_decreases p
  · rintro ⟨x, y, z, route, hcarrier, _⟩
    exact ⟨x, y, z, route, hcarrier⟩

/-- Display form of the conditional route comparison.  The reconstructed
route really contains a positive primitive natural Fermat-seven
counterexample, and its carrier has smaller seven-adic depth than the
preceding ramified summit carrier.

This is still not a recursive descent theorem: a later bridge must index the
ramified state by its source counterexample and transport the new away route
back into the same well-founded transition system. -/
theorem exists_strict_awayCounterexample_of_internalDepthFourReconstruction
    (p : RamifiedSignedRootRoutingPacket)
    (h : InternalDepthFourCounterexampleReconstructionObligation p) :
    ∃ (x y z : ℕ) (route : AwayValuationTransferPacket x y z),
      CounterexamplePack x y z ∧
        route.carrier = internalDepthFourCarrier p ∧
        padicValNat 7 route.carrier <
          padicValNat 7 (outerDepthFiveCarrier p) := by
  have hstrict :
      InternalDepthFourStrictDescentCandidate p :=
    (internalDepthFourCounterexampleReconstructionObligation_iff_strictDescentCandidate p).mp h
  rcases hstrict with ⟨x, y, z, route, hcarrier, hdrop⟩
  exact
    ⟨x, y, z, route, route.normal.counterexample,
      hcarrier, hdrop⟩

/-- Combined terminal boundary after the U1.5 additive-chart audit.

The internal seven-adic depth drops, but the visible signed endpoints cannot
form a Fermat chart.  Consequently the strict candidate can only be inhabited
by a genuinely new counterexample reconstruction, exactly the named
obligation above.  A recursive descent still needs an indexed state/measure
bridge back from that new away route. -/
theorem strictDescentFailureBoundary
    (p : RamifiedSignedRootRoutingPacket) :
    padicValNat 7 (internalDepthFourCarrier p) = 4 ∧
      padicValNat 7 (outerDepthFiveCarrier p) = 5 ∧
      padicValNat 7 (internalDepthFourCarrier p) <
        padicValNat 7 (outerDepthFiveCarrier p) ∧
      (¬ ∃ c : ℤ,
        SignedFermatSevenChart
          p.signedDepth.signedRightRoot
          (-p.signedDepth.signedLeftRoot) c) ∧
      (InternalDepthFourCounterexampleReconstructionObligation p ↔
        InternalDepthFourStrictDescentCandidate p) := by
  exact
    ⟨padicValNat_internalDepthFourCarrier p,
      padicValNat_outerDepthFiveCarrier p,
      internalDepthFourCarrier_strictly_decreases p,
      p.signedDepth.no_direct_signedFermatSevenChart,
      internalDepthFourCounterexampleReconstructionObligation_iff_strictDescentCandidate p⟩

end RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

#print axioms
  RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.internalDepthFourCarrier_strictly_decreases
#print axioms
  RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.internalDepthFourCounterexampleReconstructionObligation_iff_strictDescentCandidate
#print axioms
  RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.exists_strict_awayCounterexample_of_internalDepthFourReconstruction
#print axioms
  RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.strictDescentFailureBoundary

end

end DkMath.FLT.Seven
