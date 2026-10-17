import DkMath

#print "file: docs.dev.FLT-regular-to-GN-GTail-261015-v0.evidence.SevenRealGNSmoke"

open DkMath.Lib.Algebra DkMath.FLT.Kummer.SevenRealGN

#check root_unit_gauge_identity
#check phase_target_card
#check unit_seventh_iff_obstruction
#check same_class_iff_unitObstruction_eq
#check realPrimary_seventh_iff_norm_zero
#check alphaEmbeddedUnit_not_seventh
#check PrimaryPacket
#check packetOfRealUnit
#check source_preservation
#check coefficient_ring_preservation
#check unit_class_preservation
#check iterated_invariant_preservation
#check no_ideal_measure_drop

-- The root entrance exposes actual iteration with its primary and away proofs.
example (ts : List AllowedGauge) :
    snapshot (iterate (packetOfRealUnit DkMath.FLT.Seven.SevenRealCubicInt.alphaUnit) ts) =
      snapshot (packetOfRealUnit DkMath.FLT.Seven.SevenRealCubicInt.alphaUnit) :=
  (iterated_invariant_preservation _ ts).1
