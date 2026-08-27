/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicPrimeAddress
import DkMath.FLT.Seven.SevenRamifiedFusionLoadedBranchRecovery
import DkMath.FLT.Seven.SevenRamifiedFusionLoadNorm

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionLoadedCore"

namespace DkMath.FLT.Seven

noncomputable section

set_option linter.style.longLine false

namespace RamifiedSignedRootRoutingPacket

open SevenRealCubicInt

/-- Every prime carried by the first unresolved row-two scalar cell is
one modulo fourteen. -/
theorem prime_dvd_row2Cell21_modFourteen_eq_one
    (p : RamifiedSignedRootRoutingPacket)
    {q : ℕ}
    (hq : Nat.Prime q)
    (hqc : q ∣ p.routing.c21) :
    q % 14 = 1 := by
  have hnat :
      q ∣ Int.natAbs p.signedDepth.quotientRoot :=
    hqc.trans p.routing.c21_dvd_row2
  have hint :
      (q : ℤ) ∣ p.signedDepth.quotientRoot :=
    Int.natCast_dvd.mpr hnat
  exact
    p.signedDepth.prime_dvd_quotientRoot_modFourteen_eq_one
      hq hint

/-- Every prime carried by the second unresolved row-two scalar cell has
the same split-prime congruence. -/
theorem prime_dvd_row2Cell22_modFourteen_eq_one
    (p : RamifiedSignedRootRoutingPacket)
    {q : ℕ}
    (hq : Nat.Prime q)
    (hqc : q ∣ p.routing.c22) :
    q % 14 = 1 := by
  have hnat :
      q ∣ Int.natAbs p.signedDepth.quotientRoot :=
    hqc.trans p.routing.c22_dvd_row2
  have hint :
      (q : ℤ) ∣ p.signedDepth.quotientRoot :=
    Int.natCast_dvd.mpr hnat
  exact
    p.signedDepth.prime_dvd_quotientRoot_modFourteen_eq_one
      hq hint

/-- FUSION-003F synthesis packet.  It simultaneously retains the
unconditional integral gcd-load split of the three real pair cores and the
canonical primitive-seventh-root address at every prime divisor of the signed
quotient root.

This packet does not choose one oriented degree-six cyclotomic factor and
does not reconstruct a new Fermat chart. -/
structure RamifiedFusionLoadedCorePacket
    (p : RamifiedSignedRootRoutingPacket) where
  loadedPowerSplit : RealPairLoadedPowerSplit p
  quotientPrimeAddress :
    ∀ {q : ℕ},
      (hq : Nat.Prime q) →
      (hqe : (q : ℤ) ∣ p.signedDepth.quotientRoot) →
      p.signedDepth.QuotientPrimeMuSevenAddress q

/-- Every coherent signed routing packet canonically reaches the complete
FUSION-003F loaded-core boundary. -/
theorem nonempty_ramifiedFusionLoadedCorePacket
    (p : RamifiedSignedRootRoutingPacket) :
    Nonempty (RamifiedFusionLoadedCorePacket p) := by
  rcases p.nonempty_realPairLoadedPowerSplit with ⟨split⟩
  exact ⟨{
    loadedPowerSplit := split
    quotientPrimeAddress := fun hq hqe =>
      { prime := hq
        dividesQuotientRoot := hqe } }⟩

namespace RamifiedFusionLoadedCorePacket

variable {p : RamifiedSignedRootRoutingPacket}

/-- Every quotient-prime address retained by the synthesis packet is one
modulo fourteen. -/
theorem quotientPrime_modFourteen_eq_one
    (_s : RamifiedFusionLoadedCorePacket p)
    {q : ℕ}
    (hq : Nat.Prime q)
    (hqe : (q : ℤ) ∣ p.signedDepth.quotientRoot) :
    q % 14 = 1 :=
  p.signedDepth.prime_dvd_quotientRoot_modFourteen_eq_one hq hqe

/-- The packet's canonical local evaluation kills the zeroth normalized pair
core at every quotient-prime address. -/
theorem evalAlphaRoot_realPairCore_zero
    (s : RamifiedFusionLoadedCorePacket p)
    {q : ℕ}
    (hq : Nat.Prime q)
    (hqe : (q : ℤ) ∣ p.signedDepth.quotientRoot) :
    (s.quotientPrimeAddress hq hqe).evalAlphaRoot
      (p.signedDepth.realPairCore 0) = 0 :=
  (s.quotientPrimeAddress hq hqe).evalAlphaRoot_realPairCore_zero

/-- The same canonical evaluation does not kill the ramified Eisenstein
axis, so the local address belongs to the normalized core rather than to the
prime above seven. -/
theorem eisensteinAxis_not_mem_evalAlphaRoot_ker
    (s : RamifiedFusionLoadedCorePacket p)
    {q : ℕ}
    (hq : Nat.Prime q)
    (hqe : (q : ℤ) ∣ p.signedDepth.quotientRoot) :
    eisensteinAxis ∉
      RingHom.ker
        (s.quotientPrimeAddress hq hqe).evalAlphaRoot :=
  (s.quotientPrimeAddress hq hqe).eisensteinAxis_not_mem_evalAlphaRoot_ker

/-- The first canonical scalar-load family in the synthesis packet is a
complete associated Galois cycle. -/
theorem load21_galois_cycle
    (s : RamifiedFusionLoadedCorePacket p) :
    Associated
        (rotateEquiv (s.loadedPowerSplit.load21 0))
        (s.loadedPowerSplit.load21 1) ∧
      Associated
        (rotateEquiv (s.loadedPowerSplit.load21 1))
        (s.loadedPowerSplit.load21 2) ∧
      Associated
        (rotateEquiv (s.loadedPowerSplit.load21 2))
        (s.loadedPowerSplit.load21 0) := by
  rw [s.loadedPowerSplit.load21_eq_gcd]
  exact
    ⟨p.rotate_realPairLoad21_zero_associated_one,
      p.rotate_realPairLoad21_one_associated_two,
      p.rotate_realPairLoad21_two_associated_zero⟩

/-- The second canonical scalar-load family has the identical associated
Galois-cycle coherence. -/
theorem load22_galois_cycle
    (s : RamifiedFusionLoadedCorePacket p) :
    Associated
        (rotateEquiv (s.loadedPowerSplit.load22 0))
        (s.loadedPowerSplit.load22 1) ∧
      Associated
        (rotateEquiv (s.loadedPowerSplit.load22 1))
        (s.loadedPowerSplit.load22 2) ∧
      Associated
        (rotateEquiv (s.loadedPowerSplit.load22 2))
        (s.loadedPowerSplit.load22 0) := by
  rw [s.loadedPowerSplit.load22_eq_gcd]
  exact
    ⟨p.rotate_realPairLoad22_zero_associated_one,
      p.rotate_realPairLoad22_one_associated_two,
      p.rotate_realPairLoad22_two_associated_zero⟩

/-- Every first-family load retained by the packet has exact absolute cubic
norm equal to the first unresolved scalar routing cell. -/
theorem natAbs_norm_load21
    (s : RamifiedFusionLoadedCorePacket p) (i : Fin 3) :
    Int.natAbs
        (norm (s.loadedPowerSplit.load21 i)) =
      p.routing.c21 := by
  rw [s.loadedPowerSplit.load21_eq_gcd]
  exact p.natAbs_norm_realPairLoad21 i

/-- Every second-family load has exact absolute cubic norm equal to the
second unresolved scalar routing cell. -/
theorem natAbs_norm_load22
    (s : RamifiedFusionLoadedCorePacket p) (i : Fin 3) :
    Int.natAbs
        (norm (s.loadedPowerSplit.load22 i)) =
      p.routing.c22 := by
  rw [s.loadedPowerSplit.load22_eq_gcd]
  exact p.natAbs_norm_realPairLoad22 i

/-- Branch A is recovered inside the synthesis packet by explicitly
absorbing seventh-power load factors into its residual roots. -/
theorem nonempty_corePowerSplit_of_row2_cells
    (s : RamifiedFusionLoadedCorePacket p)
    (h21 : ∃ a : ℕ, p.routing.c21 = a ^ 7)
    (h22 : ∃ b : ℕ, p.routing.c22 = b ^ 7) :
    Nonempty
      (RamifiedSignedRootDepthPacket.RealPairCoreAssociatedPowerSplit
        p.signedDepth) := by
  rcases
      s.loadedPowerSplit.nonempty_loadPowerAbsorption_of_row2_cells
        h21 h22 with
    ⟨loads⟩
  exact ⟨s.loadedPowerSplit.absorb loads⟩

end RamifiedFusionLoadedCorePacket

end RamifiedSignedRootRoutingPacket

end

end DkMath.FLT.Seven
