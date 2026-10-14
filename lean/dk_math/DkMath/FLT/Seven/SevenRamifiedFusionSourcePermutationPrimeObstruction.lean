/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionPermutationPrimeSupport

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionSourcePermutationPrimeObstruction"

namespace DkMath.FLT.Seven
namespace RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

/-- A supplied factorization of this packet's actual core obstructs reconstruction.
No such factorization or reconstruction witness is asserted to exist. -/
theorem internalDepthFour_no_reconstruction_of_permutation_prime_core
    (p : RamifiedSignedRootRoutingPacket) {c ℓ n : ℕ}
    (hp : Nat.Prime ℓ) (hodd : ℓ ≠ 2) (hnot7 : ℓ ≠ 7)
    (hcop : Nat.Coprime 7 (ℓ - 1)) (hc : c ≤ 7 ^ 3) (hn : 0 < n)
    (hcore : internalDepthFourSeventhCore p = c * ℓ ^ n) :
    ¬ InternalDepthFourCounterexampleReconstructionObligation p := by
  intro hrec
  have hs := (internalDepthFourReconstruction_iff_sixth_power_sieved p).mp hrec
  rw [hcore] at hs
  exact sixthPowerSieved_smallCoefficient_permutation_prime_excluded
    hp hodd hnot7 hcop hc hn hs

/-- Reconstruction forbids these factorizations of the same packet's actual core. -/
theorem reconstructed_core_ne_smallCoefficient_permutation_prime_power
    (p : RamifiedSignedRootRoutingPacket)
    (hrec : InternalDepthFourCounterexampleReconstructionObligation p)
    {c ℓ n : ℕ} (hp : Nat.Prime ℓ) (hodd : ℓ ≠ 2) (hnot7 : ℓ ≠ 7)
    (hcop : Nat.Coprime 7 (ℓ - 1)) (hc : c ≤ 7 ^ 3) (hn : 0 < n) :
    internalDepthFourSeventhCore p ≠ c * ℓ ^ n := by
  intro hcore
  exact internalDepthFour_no_reconstruction_of_permutation_prime_core
    p hp hodd hnot7 hcop hc hn hcore hrec

/-- The same conditional obstruction rules out finite additive certificates. -/
theorem internalDepthFour_no_finiteCharts_of_permutation_prime_core
    (p : RamifiedSignedRootRoutingPacket) {c ℓ n : ℕ}
    (hp : Nat.Prime ℓ) (hodd : ℓ ≠ 2) (hnot7 : ℓ ≠ 7)
    (hcop : Nat.Coprime 7 (ℓ - 1)) (hc : c ≤ 7 ^ 3) (hn : 0 < n)
    (hcore : internalDepthFourSeventhCore p = c * ℓ ^ n) :
    ¬ (prescribedCarrierFiniteCharts (internalDepthFourCarrier p)).Nonempty := by
  intro hchart
  exact internalDepthFour_no_reconstruction_of_permutation_prime_core
    p hp hodd hnot7 hcop hc hn hcore
    ((internalDepthFourReconstruction_iff_finiteCharts p).mpr hchart)

end RamifiedSignedRootRoutingPacket.QuotientPrimeSupport
end DkMath.FLT.Seven
