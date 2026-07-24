/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalEndpointSeparation

#print "file: DkMath.FLT.Seven.SevenBaseTerminalCarrierRouting"

namespace DkMath.FLT.Seven

/-- After removing the unique selected factor seven, the three remaining
pairwise-coprime endpoint-side factors admit an exact `3 × 3` routing into the
three pairwise-coprime cubic root-load channels. -/
theorem AwaySevenBaseTerminalQuotientCorePacket.nonempty_endpoint_carrier_root_routing
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalQuotientCorePacket source r p) :
    Nonempty (CoprimeTripleRouting
      packet.carrier.carrierUnit
      (awaySevenBaseTerminalUnselectedEndpointNat p.row y z)
      (awaySevenBaseTerminalCompanionEndpointNat p.row y z)
      r.cubic.rootTriple.vPart
      r.cubic.rootTriple.leftPart
      r.cubic.rootTriple.rightPart) := by
  rcases packet.endpoint_carrier_root_load_normal_form with
    ⟨hprod, hunselectedCompanion, hunselectedCarrier, hcompanionCarrier⟩
  have hunselectedPos :
      0 < awaySevenBaseTerminalUnselectedEndpointNat p.row y z := by
    cases p.row <;>
      simp only [awaySevenBaseTerminalUnselectedEndpointNat]
    · exact r.cubic.endpointTriple.second_pos
    · exact r.cubic.endpointTriple.first_pos
    · exact r.cubic.endpointTriple.first_pos
  have hcompanionPos :
      0 < awaySevenBaseTerminalCompanionEndpointNat p.row y z := by
    cases p.row <;>
      simp only [awaySevenBaseTerminalCompanionEndpointNat]
    · exact r.cubic.endpointTriple.third_pos
    · exact r.cubic.endpointTriple.third_pos
    · exact r.cubic.endpointTriple.second_pos
  exact nonempty_coprimeTripleRouting
    (a₁ := packet.carrier.carrierUnit)
    (a₂ := awaySevenBaseTerminalUnselectedEndpointNat p.row y z)
    (a₃ := awaySevenBaseTerminalCompanionEndpointNat p.row y z)
    (b₁ := r.cubic.rootTriple.vPart)
    (b₂ := r.cubic.rootTriple.leftPart)
    (b₃ := r.cubic.rootTriple.rightPart)
    ⟨packet.carrier.carrierUnit_pos, hunselectedPos, hcompanionPos⟩
    ⟨r.cubic.rootTriple.vPart_pos, r.cubic.rootTriple.leftPart_pos,
      r.cubic.rootTriple.rightPart_pos⟩
    hunselectedCarrier.symm
    hcompanionCarrier.symm
    hunselectedCompanion
    r.cubic.rootTriple.coprime_v_left
    r.cubic.rootTriple.coprime_v_right
    r.cubic.rootTriple.coprime_left_right
    hprod

/-- Every prime carried by the terminal carrier unit is different from seven and
occupies exactly one cell of the carrier row in some exact terminal routing.
That cell lies in the corresponding cubic root-load column. -/
theorem AwaySevenBaseTerminalQuotientCorePacket.prime_dvd_carrierUnit_unique_routing_cell
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalQuotientCorePacket source r p)
    {q : ℕ} (hq : Nat.Prime q) (hqCarrier : q ∣ packet.carrier.carrierUnit) :
    q ≠ 7 ∧
      ∃ routing : CoprimeTripleRouting
          packet.carrier.carrierUnit
          (awaySevenBaseTerminalUnselectedEndpointNat p.row y z)
          (awaySevenBaseTerminalCompanionEndpointNat p.row y z)
          r.cubic.rootTriple.vPart
          r.cubic.rootTriple.leftPart
          r.cubic.rootTriple.rightPart,
        (q ∣ routing.c11 ∧ ¬ q ∣ routing.c12 ∧ ¬ q ∣ routing.c13 ∧
          q ∣ r.cubic.rootTriple.vPart) ∨
        (q ∣ routing.c12 ∧ ¬ q ∣ routing.c11 ∧ ¬ q ∣ routing.c13 ∧
          q ∣ r.cubic.rootTriple.leftPart) ∨
        (q ∣ routing.c13 ∧ ¬ q ∣ routing.c11 ∧ ¬ q ∣ routing.c12 ∧
          q ∣ r.cubic.rootTriple.rightPart) := by
  refine ⟨?_, ?_⟩
  · intro hq7
    subst q
    exact packet.carrier.seven_not_dvd_carrierUnit hqCarrier
  · rcases packet.nonempty_endpoint_carrier_root_routing with ⟨routing⟩
    refine ⟨routing, ?_⟩
    have hqRow : q ∣ routing.c11 * routing.c12 * routing.c13 := by
      rw [← routing.row1]
      exact hqCarrier
    have h12 : ¬ (q ∣ routing.c11 ∧ q ∣ routing.c12) := by
      rintro ⟨hq11, hq12⟩
      have hgcd := Nat.dvd_gcd hq11 hq12
      rw [routing.row1_coprime.1] at hgcd
      exact hq.not_dvd_one hgcd
    have h13 : ¬ (q ∣ routing.c11 ∧ q ∣ routing.c13) := by
      rintro ⟨hq11, hq13⟩
      have hgcd := Nat.dvd_gcd hq11 hq13
      rw [routing.row1_coprime.2.1] at hgcd
      exact hq.not_dvd_one hgcd
    have h23 : ¬ (q ∣ routing.c12 ∧ q ∣ routing.c13) := by
      rintro ⟨hq12, hq13⟩
      have hgcd := Nat.dvd_gcd hq12 hq13
      rw [routing.row1_coprime.2.2] at hgcd
      exact hq.not_dvd_one hgcd
    rcases (Nat.Prime.dvd_mul hq).mp hqRow with hq12 | hq13
    · rcases (Nat.Prime.dvd_mul hq).mp hq12 with hq11 | hq12
      · left
        refine ⟨hq11, fun h => h12 ⟨hq11, h⟩,
          fun h => h13 ⟨hq11, h⟩, ?_⟩
        rw [routing.col1]
        exact dvd_mul_of_dvd_left
          (dvd_mul_of_dvd_left hq11 routing.c21) routing.c31
      · right
        left
        refine ⟨hq12, fun h => h12 ⟨h, hq12⟩,
          fun h => h23 ⟨hq12, h⟩, ?_⟩
        rw [routing.col2]
        exact dvd_mul_of_dvd_left
          (dvd_mul_of_dvd_left hq12 routing.c22) routing.c32
    · right
      right
      refine ⟨hq13, fun h => h13 ⟨h, hq13⟩,
        fun h => h23 ⟨h, hq13⟩, ?_⟩
      rw [routing.col3]
      exact dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_left hq13 routing.c23) routing.c33

end DkMath.FLT.Seven
