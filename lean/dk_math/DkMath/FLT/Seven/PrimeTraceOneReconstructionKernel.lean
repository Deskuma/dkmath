/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.AwayValuationTransfer
import DkMath.FLT.Seven.DescentClosureAudit

#print "file: DkMath.FLT.Seven.PrimeTraceOneReconstructionKernel"

namespace DkMath.FLT.Seven

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- There exists an actual primitive positive away FLT7 packet whose selected
exceptional carrier is exactly the prescribed natural number. -/
def AwayCarrierReconstruction (carrier : ℕ) : Prop :=
  ∃ (x y z : ℕ) (route : AwayValuationTransferPacket x y z),
    route.carrier = carrier

theorem awayCarrierReconstruction_iff_nonempty_descentClosureProvider
    {x y z : ℕ} (p : AwayValuationTransferPacket x y z) :
    AwayCarrierReconstruction (Int.natAbs p.normal.root.snd) ↔
      Nonempty (AwayDescentClosureProvider x y z p) := by
  constructor
  · rintro ⟨nextX, nextY, nextZ, nextRoute, hcarrier⟩
    exact ⟨{
      nextX := nextX
      nextY := nextY
      nextZ := nextZ
      nextPack := nextRoute.normal.counterexample
      nextRoute := nextRoute
      carrier_match := hcarrier }⟩
  · rintro ⟨provider⟩
    exact ⟨provider.nextX, provider.nextY, provider.nextZ,
      provider.nextRoute, provider.carrier_match⟩

namespace AwayCarrierReconstruction

theorem carrier_pos {carrier : ℕ} (h : AwayCarrierReconstruction carrier) :
    0 < carrier := by
  rcases h with ⟨x, y, z, route, hcarrier⟩
  rw [← hcarrier]
  exact route.carrier_pos

theorem one_le_carrier_depth {carrier : ℕ}
    (h : AwayCarrierReconstruction carrier) :
    1 ≤ padicValNat 7 carrier := by
  rcases h with ⟨x, y, z, route, hcarrier⟩
  rw [← hcarrier]
  exact route.one_le_carrier_depth

theorem seven_dvd_carrier {carrier : ℕ}
    (h : AwayCarrierReconstruction carrier) :
    7 ∣ carrier := by
  have hdepth : 0 < padicValNat 7 carrier := by
    exact Nat.lt_of_lt_of_le (by norm_num) (h.one_le_carrier_depth)
  exact (dvd_pow_self 7 hdepth.ne').trans pow_padicValNat_dvd

end AwayCarrierReconstruction

theorem AwayValuationTransferPacket.root_snd_depth_eq_carrier_depth_sub_one
    {x y z : ℕ} (p : AwayValuationTransferPacket x y z) :
    padicValNat 7 (Int.natAbs p.normal.root.snd) =
      padicValNat 7 p.carrier - 1 := by
  rw [p.valuation_eq]
  omega

theorem AwayValuationTransferPacket.no_reconstruction_at_depth_one
    {x y z : ℕ} (p : AwayValuationTransferPacket x y z)
    (hdepth : padicValNat 7 p.carrier = 1) :
    ¬ AwayCarrierReconstruction (Int.natAbs p.normal.root.snd) := by
  intro htarget
  have htarget_depth := htarget.one_le_carrier_depth
  rw [p.root_snd_depth_eq_carrier_depth_sub_one, hdepth] at htarget_depth
  omega

theorem AwayValuationTransferPacket.no_descentClosureProvider_at_depth_one
    {x y z : ℕ} (p : AwayValuationTransferPacket x y z)
    (hdepth : padicValNat 7 p.carrier = 1) :
    ¬ Nonempty (AwayDescentClosureProvider x y z p) := by
  intro hprovider
  exact (p.no_reconstruction_at_depth_one hdepth)
    ((awayCarrierReconstruction_iff_nonempty_descentClosureProvider p).mpr
      hprovider)

theorem AwayValuationTransferPacket.seven_dvd_root_snd_of_two_le_carrier_depth
    {x y z : ℕ} (p : AwayValuationTransferPacket x y z)
    (hdepth : 2 ≤ padicValNat 7 p.carrier) :
    7 ∣ Int.natAbs p.normal.root.snd := by
  have hroot_depth : 1 ≤ padicValNat 7 (Int.natAbs p.normal.root.snd) := by
    rw [p.root_snd_depth_eq_carrier_depth_sub_one]
    omega
  exact (@padicValNat_dvd_iff_le 7 inferInstance
    (Int.natAbs p.normal.root.snd) 1 p.root_snd_abs_pos.ne').mpr hroot_depth

end DkMath.FLT.Seven
