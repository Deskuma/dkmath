/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionSourcePermutationPrimeObstruction
import DkMath.FLT.Seven.SevenRamifiedFusionLoadedBranchRecovery

#print "file: DkMathTest.FLT.Seven.SevenRamifiedFusionSourcePermutationPrimeObstruction"

namespace DkMathTest.FLT.Seven
open DkMath.FLT.Seven
open DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

example (p : RamifiedSignedRootRoutingPacket) {c ℓ n : ℕ}
    (hp : Nat.Prime ℓ) (hodd : ℓ ≠ 2) (hnot7 : ℓ ≠ 7)
    (hcop : Nat.Coprime 7 (ℓ - 1)) (hc : c ≤ 7 ^ 3) (hn : 0 < n)
    (hcore : internalDepthFourSeventhCore p = c * ℓ ^ n) :
    ¬ InternalDepthFourCounterexampleReconstructionObligation p :=
  internalDepthFour_no_reconstruction_of_permutation_prime_core
    p hp hodd hnot7 hcop hc hn hcore

example (p : RamifiedSignedRootRoutingPacket) {n : ℕ} (hn : 0 < n)
    (hcore : internalDepthFourSeventhCore p = 1 * 11 ^ n) :
    ¬ InternalDepthFourCounterexampleReconstructionObligation p :=
  internalDepthFour_no_reconstruction_of_permutation_prime_core
    p (by decide) (by decide) (by decide) (by decide) (by decide) hn hcore
example (p : RamifiedSignedRootRoutingPacket) {n : ℕ} (hn : 0 < n)
    (hcore : internalDepthFourSeventhCore p = 3 * 13 ^ n) :
    ¬ InternalDepthFourCounterexampleReconstructionObligation p :=
  internalDepthFour_no_reconstruction_of_permutation_prime_core
    p (by decide) (by decide) (by decide) (by decide) (by decide) hn hcore
example (p : RamifiedSignedRootRoutingPacket) {n : ℕ} (hn : 0 < n)
    (hcore : internalDepthFourSeventhCore p = 13 * 13 ^ n) :
    ¬ (prescribedCarrierFiniteCharts (internalDepthFourCarrier p)).Nonempty :=
  internalDepthFour_no_finiteCharts_of_permutation_prime_core
    p (by decide) (by decide) (by decide) (by decide) (by decide) hn hcore
example (p : RamifiedSignedRootRoutingPacket)
    (hrec : InternalDepthFourCounterexampleReconstructionObligation p)
    {n : ℕ} (hn : 0 < n) : internalDepthFourSeventhCore p ≠ 3 * 11 ^ n :=
  reconstructed_core_ne_smallCoefficient_permutation_prime_power
    p hrec (by decide) (by decide) (by decide) (by decide) (by decide) hn

/-- Direct-use probes check these contracts do not themselves supply charts.
Their failure is a type-check observation, not a proof of logical independence. -/
example (p : RamifiedSignedRootRoutingPacket)
    (hrec : InternalDepthFourCounterexampleReconstructionObligation p) :
    (prescribedCarrierFiniteCharts (internalDepthFourCarrier p)).Nonempty := by
  fail_if_success exact internalDepthFourSummand_nested_normal_form p
  fail_if_success exact p.nonempty_realPairLoadedPowerSplit
  exact (internalDepthFourReconstruction_iff_finiteCharts p).mp hrec

example (p : RamifiedSignedRootRoutingPacket) :
    internalDepthFourCarrier p = 7 ^ 4 * internalDepthFourSeventhCore p ^ 7 :=
  internalDepthFourCarrier_eq_seven_pow_four_mul_core_pow p
example (p : RamifiedSignedRootRoutingPacket) :
    0 < internalDepthFourSeventhCore p ∧ ¬ 7 ∣ internalDepthFourSeventhCore p :=
  ⟨internalDepthFourSeventhCore_pos p, internalDepthFourSeventhCore_not_seven_dvd p⟩
example (p : RamifiedSignedRootRoutingPacket) :
    Nonempty (RamifiedSignedRootRoutingPacket.RealPairLoadedPowerSplit p) :=
  p.nonempty_realPairLoadedPowerSplit

example (p : RamifiedSignedRootRoutingPacket) {x y z : ℕ}
    (route : AwayValuationTransferPacket x y z)
    (hcarrier : route.carrier = internalDepthFourCarrier p) :
    route.normal.root ≠
      p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.quadratic.innerRoot :=
  internalDepthFourReconstructedRoute_root_ne_innerRoot p route hcarrier

-- Signature probes retain the supplied pack and conditional cell assumptions.
#check internalDepthFourSummand_nested_normal_form
#check RamifiedRealCubicNormPacket.exists_inner_complementary_seventh_root
#check RamifiedSignedRootRoutingPacket.quotientRoot_signedSeventhPower_iff_row2_cells
#check RamifiedSignedRootRoutingPacket.nonempty_realPairCoreAssociatedPowerSplit_via_loaded_absorption
#check mem_prescribedCarrierFiniteCharts
#check (fun p : RamifiedSignedRootRoutingPacket =>
  (prescribedCarrierFiniteCharts (internalDepthFourCarrier p)).Nonempty)

#print axioms DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.internalDepthFour_no_reconstruction_of_permutation_prime_core
#print axioms DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.reconstructed_core_ne_smallCoefficient_permutation_prime_power
#print axioms DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.internalDepthFour_no_finiteCharts_of_permutation_prime_core
end DkMathTest.FLT.Seven
