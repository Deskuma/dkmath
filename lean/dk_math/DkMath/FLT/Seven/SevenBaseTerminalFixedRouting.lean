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

/-- A fixed routing board tied to the very same terminal quotient core, rather
than merely to another inhabitant of the same core-packet type. -/
structure AwaySevenBaseTerminalCoherentRoutingPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (terminal : AwaySevenBaseTerminalUnitSectorPacket source r p) :
    Type where
  routing : AwaySevenBaseTerminalRoutingPacket (source := source) p
  core_eq : routing.core = terminal.core

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

/-- Every terminal unit-sector packet admits a routing board whose source core
is definitionally the terminal packet's own core. -/
theorem AwaySevenBaseTerminalUnitSectorPacket.nonempty_coherent_routing_packet
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (terminal : AwaySevenBaseTerminalUnitSectorPacket source r p) :
    Nonempty (AwaySevenBaseTerminalCoherentRoutingPacket terminal) := by
  rcases terminal.core.nonempty_endpoint_carrier_root_routing with ⟨routing⟩
  exact ⟨{
    routing := {
      core := terminal.core
      routing := routing }
    core_eq := rfl }⟩

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

/-- On a fixed terminal routing board, every prime carried by the row-sensitive
unselected endpoint occupies exactly one cell of the second row and enters the
corresponding cubic root-load column. -/
theorem AwaySevenBaseTerminalRoutingPacket.prime_dvd_unselected_endpoint_unique_cell
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    {q : ℕ} (hq : Nat.Prime q)
    (hqUnselected : q ∣ awaySevenBaseTerminalUnselectedEndpointNat p.row y z) :
    q ≠ 7 ∧
      ((q ∣ packet.routing.c21 ∧ ¬ q ∣ packet.routing.c22 ∧
          ¬ q ∣ packet.routing.c23 ∧ q ∣ r.cubic.rootTriple.vPart) ∨
        (q ∣ packet.routing.c22 ∧ ¬ q ∣ packet.routing.c21 ∧
          ¬ q ∣ packet.routing.c23 ∧ q ∣ r.cubic.rootTriple.leftPart) ∨
        (q ∣ packet.routing.c23 ∧ ¬ q ∣ packet.routing.c21 ∧
          ¬ q ∣ packet.routing.c22 ∧ q ∣ r.cubic.rootTriple.rightPart)) := by
  refine ⟨?_, ?_⟩
  · intro hq7
    subst q
    have hloadEq := packet.core.endpoint_carrier_root_load_normal_form.1
    apply packet.core.seven_not_dvd_cubic_root_load
    rw [← hloadEq]
    exact dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_right hqUnselected packet.core.carrier.carrierUnit)
      (awaySevenBaseTerminalCompanionEndpointNat p.row y z)
  · have hqRow :
        q ∣ packet.routing.c21 * packet.routing.c22 * packet.routing.c23 := by
      rw [← packet.routing.row2]
      exact hqUnselected
    have h12 : ¬ (q ∣ packet.routing.c21 ∧ q ∣ packet.routing.c22) := by
      rintro ⟨hq21, hq22⟩
      have hgcd := Nat.dvd_gcd hq21 hq22
      rw [packet.routing.row2_coprime.1] at hgcd
      exact hq.not_dvd_one hgcd
    have h13 : ¬ (q ∣ packet.routing.c21 ∧ q ∣ packet.routing.c23) := by
      rintro ⟨hq21, hq23⟩
      have hgcd := Nat.dvd_gcd hq21 hq23
      rw [packet.routing.row2_coprime.2.1] at hgcd
      exact hq.not_dvd_one hgcd
    have h23 : ¬ (q ∣ packet.routing.c22 ∧ q ∣ packet.routing.c23) := by
      rintro ⟨hq22, hq23⟩
      have hgcd := Nat.dvd_gcd hq22 hq23
      rw [packet.routing.row2_coprime.2.2] at hgcd
      exact hq.not_dvd_one hgcd
    rcases (Nat.Prime.dvd_mul hq).mp hqRow with hq12 | hq23
    · rcases (Nat.Prime.dvd_mul hq).mp hq12 with hq21 | hq22
      · left
        refine ⟨hq21, fun h => h12 ⟨hq21, h⟩,
          fun h => h13 ⟨hq21, h⟩, ?_⟩
        rw [packet.routing.col1]
        exact dvd_mul_of_dvd_left
          (dvd_mul_of_dvd_right hq21 packet.routing.c11) packet.routing.c31
      · right
        left
        refine ⟨hq22, fun h => h12 ⟨h, hq22⟩,
          fun h => h23 ⟨hq22, h⟩, ?_⟩
        rw [packet.routing.col2]
        exact dvd_mul_of_dvd_left
          (dvd_mul_of_dvd_right hq22 packet.routing.c12) packet.routing.c32
    · right
      right
      refine ⟨hq23, fun h => h13 ⟨h, hq23⟩,
        fun h => h23 ⟨h, hq23⟩, ?_⟩
      rw [packet.routing.col3]
      exact dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_right hq23 packet.routing.c13) packet.routing.c33

/-- On a fixed terminal routing board, every prime carried by the row-sensitive
companion endpoint occupies exactly one cell of the third row and enters the
corresponding cubic root-load column. -/
theorem AwaySevenBaseTerminalRoutingPacket.prime_dvd_companion_endpoint_unique_cell
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    {q : ℕ} (hq : Nat.Prime q)
    (hqCompanion : q ∣ awaySevenBaseTerminalCompanionEndpointNat p.row y z) :
    q ≠ 7 ∧
      ((q ∣ packet.routing.c31 ∧ ¬ q ∣ packet.routing.c32 ∧
          ¬ q ∣ packet.routing.c33 ∧ q ∣ r.cubic.rootTriple.vPart) ∨
        (q ∣ packet.routing.c32 ∧ ¬ q ∣ packet.routing.c31 ∧
          ¬ q ∣ packet.routing.c33 ∧ q ∣ r.cubic.rootTriple.leftPart) ∨
        (q ∣ packet.routing.c33 ∧ ¬ q ∣ packet.routing.c31 ∧
          ¬ q ∣ packet.routing.c32 ∧ q ∣ r.cubic.rootTriple.rightPart)) := by
  refine ⟨?_, ?_⟩
  · intro hq7
    subst q
    have hloadEq := packet.core.endpoint_carrier_root_load_normal_form.1
    apply packet.core.seven_not_dvd_cubic_root_load
    rw [← hloadEq]
    exact dvd_mul_of_dvd_right hqCompanion
      (packet.core.carrier.carrierUnit *
        awaySevenBaseTerminalUnselectedEndpointNat p.row y z)
  · have hqRow :
        q ∣ packet.routing.c31 * packet.routing.c32 * packet.routing.c33 := by
      rw [← packet.routing.row3]
      exact hqCompanion
    have h12 : ¬ (q ∣ packet.routing.c31 ∧ q ∣ packet.routing.c32) := by
      rintro ⟨hq31, hq32⟩
      have hgcd := Nat.dvd_gcd hq31 hq32
      rw [packet.routing.row3_coprime.1] at hgcd
      exact hq.not_dvd_one hgcd
    have h13 : ¬ (q ∣ packet.routing.c31 ∧ q ∣ packet.routing.c33) := by
      rintro ⟨hq31, hq33⟩
      have hgcd := Nat.dvd_gcd hq31 hq33
      rw [packet.routing.row3_coprime.2.1] at hgcd
      exact hq.not_dvd_one hgcd
    have h23 : ¬ (q ∣ packet.routing.c32 ∧ q ∣ packet.routing.c33) := by
      rintro ⟨hq32, hq33⟩
      have hgcd := Nat.dvd_gcd hq32 hq33
      rw [packet.routing.row3_coprime.2.2] at hgcd
      exact hq.not_dvd_one hgcd
    rcases (Nat.Prime.dvd_mul hq).mp hqRow with hq12 | hq33
    · rcases (Nat.Prime.dvd_mul hq).mp hq12 with hq31 | hq32
      · left
        refine ⟨hq31, fun h => h12 ⟨hq31, h⟩,
          fun h => h13 ⟨hq31, h⟩, ?_⟩
        rw [packet.routing.col1]
        exact dvd_mul_of_dvd_right hq31
          (packet.routing.c11 * packet.routing.c21)
      · right
        left
        refine ⟨hq32, fun h => h12 ⟨h, hq32⟩,
          fun h => h23 ⟨hq32, h⟩, ?_⟩
        rw [packet.routing.col2]
        exact dvd_mul_of_dvd_right hq32
          (packet.routing.c12 * packet.routing.c22)
    · right
      right
      refine ⟨hq33, fun h => h13 ⟨h, hq33⟩,
        fun h => h23 ⟨h, hq33⟩, ?_⟩
      rw [packet.routing.col3]
      exact dvd_mul_of_dvd_right hq33
        (packet.routing.c13 * packet.routing.c23)

end DkMath.FLT.Seven
