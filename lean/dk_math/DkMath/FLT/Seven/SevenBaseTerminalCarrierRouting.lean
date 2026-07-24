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

end DkMath.FLT.Seven
