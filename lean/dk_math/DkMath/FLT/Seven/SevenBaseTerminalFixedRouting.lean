/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalCarrierRouting

#print "file: DkMath.FLT.Seven.SevenBaseTerminalFixedRouting"

namespace DkMath.FLT.Seven

/-- A terminal routing packet freezes one exact `3 × 3` routing together with
its quotient-core source.  Subsequent prime-placement statements can therefore
refer to one common board instead of choosing a fresh routing for each prime. -/
structure AwaySevenBaseTerminalRoutingPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z}
    (p : AwaySevenPivotDepthPacket r) : Type where
  core : AwaySevenBaseTerminalQuotientCorePacket source r p
  routing : CoprimeTripleRouting
    core.carrier.carrierUnit
    (awaySevenBaseTerminalUnselectedEndpointNat p.row y z)
    (awaySevenBaseTerminalCompanionEndpointNat p.row y z)
    r.cubic.rootTriple.vPart
    r.cubic.rootTriple.leftPart
    r.cubic.rootTriple.rightPart

/-- Every terminal quotient-core packet admits a fixed exact routing packet. -/
theorem AwaySevenBaseTerminalQuotientCorePacket.nonempty_fixed_routing_packet
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalQuotientCorePacket source r p) :
    Nonempty (AwaySevenBaseTerminalRoutingPacket (source := source) p) := by
  rcases packet.nonempty_endpoint_carrier_root_routing with ⟨routing⟩
  exact ⟨{
    core := packet
    routing := routing }⟩

/-- On a fixed terminal routing board, every prime carried by `carrierUnit`
occupies exactly one cell of the carrier row and enters the corresponding cubic
root-load column. -/
theorem AwaySevenBaseTerminalRoutingPacket.prime_dvd_carrierUnit_unique_cell
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    {q : ℕ} (hq : Nat.Prime q)
    (hqCarrier : q ∣ packet.core.carrier.carrierUnit) :
    q ≠ 7 ∧
      ((q ∣ packet.routing.c11 ∧ ¬ q ∣ packet.routing.c12 ∧
          ¬ q ∣ packet.routing.c13 ∧ q ∣ r.cubic.rootTriple.vPart) ∨
        (q ∣ packet.routing.c12 ∧ ¬ q ∣ packet.routing.c11 ∧
          ¬ q ∣ packet.routing.c13 ∧ q ∣ r.cubic.rootTriple.leftPart) ∨
        (q ∣ packet.routing.c13 ∧ ¬ q ∣ packet.routing.c11 ∧
          ¬ q ∣ packet.routing.c12 ∧ q ∣ r.cubic.rootTriple.rightPart)) := by
  refine ⟨?_, ?_⟩
  · intro hq7
    subst q
    exact packet.core.carrier.seven_not_dvd_carrierUnit hqCarrier
  · have hqRow :
        q ∣ packet.routing.c11 * packet.routing.c12 * packet.routing.c13 := by
      rw [← packet.routing.row1]
      exact hqCarrier
    have h12 : ¬ (q ∣ packet.routing.c11 ∧ q ∣ packet.routing.c12) := by
      rintro ⟨hq11, hq12⟩
      have hgcd := Nat.dvd_gcd hq11 hq12
      rw [packet.routing.row1_coprime.1] at hgcd
      exact hq.not_dvd_one hgcd
    have h13 : ¬ (q ∣ packet.routing.c11 ∧ q ∣ packet.routing.c13) := by
      rintro ⟨hq11, hq13⟩
      have hgcd := Nat.dvd_gcd hq11 hq13
      rw [packet.routing.row1_coprime.2.1] at hgcd
      exact hq.not_dvd_one hgcd
    have h23 : ¬ (q ∣ packet.routing.c12 ∧ q ∣ packet.routing.c13) := by
      rintro ⟨hq12, hq13⟩
      have hgcd := Nat.dvd_gcd hq12 hq13
      rw [packet.routing.row1_coprime.2.2] at hgcd
      exact hq.not_dvd_one hgcd
    rcases (Nat.Prime.dvd_mul hq).mp hqRow with hq12 | hq13
    · rcases (Nat.Prime.dvd_mul hq).mp hq12 with hq11 | hq12
      · left
        refine ⟨hq11, fun h => h12 ⟨hq11, h⟩,
          fun h => h13 ⟨hq11, h⟩, ?_⟩
        rw [packet.routing.col1]
        exact dvd_mul_of_dvd_left
          (dvd_mul_of_dvd_left hq11 packet.routing.c21) packet.routing.c31
      · right
        left
        refine ⟨hq12, fun h => h12 ⟨h, hq12⟩,
          fun h => h23 ⟨hq12, h⟩, ?_⟩
        rw [packet.routing.col2]
        exact dvd_mul_of_dvd_left
          (dvd_mul_of_dvd_left hq12 packet.routing.c22) packet.routing.c32
    · right
      right
      refine ⟨hq13, fun h => h13 ⟨h, hq13⟩,
        fun h => h23 ⟨h, hq13⟩, ?_⟩
      rw [packet.routing.col3]
      exact dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_left hq13 packet.routing.c23) packet.routing.c33

end DkMath.FLT.Seven
