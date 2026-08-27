import DkMath.FLT.Seven.SevenPivotDescentAudit

open DkMath.FLT.Seven

/-- A concrete non-field top layer: `7` is nonzero modulo `49`, but its
seventh power vanishes. -/
example : (7 : ZMod 49) ≠ 0 := by decide

example : (7 : ZMod 49) ^ 7 = 0 := by decide

example {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwaySevenPivotDepthPacket r) (h : 1 < p.exponent) :
    (r.cubic.rootTriple.normal.root.snd : ZMod p.upperModulus)^7 = 0 :=
  p.rootSnd_seventh_eq_zero_of_lifted h

example {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwaySevenPivotDepthPacket r) (h : 1 < p.exponent) :
    AwaySevenLiftedUnitOrbitPacket p := p.toLiftedUnitOrbitPacket h

example {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwaySevenPivotDepthPacket r) :
    Nonempty (AwaySevenRamifiedKernelPacket p) :=
  nonempty_awaySevenRamifiedKernelPacket p

example {x y z : ℕ} (h : CounterexamplePack x y z) :
    Nonempty (SevenPivotSummitRoute x y z) := sevenPivotSummitRoute_of_pack h

#print axioms AwaySevenPivotDepthPacket.rootSnd_seventh_eq_zero_of_lifted
#print axioms AwaySevenPivotDepthPacket.toLiftedUnitOrbitPacket
#print axioms nonempty_awaySevenRamifiedKernelPacket
#print axioms sevenPivotSummitRoute_of_pack
