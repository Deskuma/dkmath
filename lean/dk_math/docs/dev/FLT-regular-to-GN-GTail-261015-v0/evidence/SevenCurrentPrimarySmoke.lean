import DkMath

open DkMath.FLT.Kummer.SevenRealGN DkMath.FLT.Seven
open SevenRealCubic SevenCyclotomicDegreeSixInt

#check seventh_sub_one_dvd_seven_iff_residue_one
#check factor_after_ramifier_twist
#check gap_divisible_of_primary
#check primary_of_root_residue_one
#check exists_primary_root_gauge_iff_gap_divisible
#check current_gap_uniformizer_pow64
#check current_primary_iff_root_residue_one
#check currentCarrier_primary_packet_receiver

-- The normal root exposes the fulfilled necessary condition, without a primary hypothesis.
example {a b d : ℕ} {source : CounterexamplePack a b d}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) :
    (7 : C) * (zeta ^ 4 - 1) ∣ ofReal (SevenRealCubicInt.rotateEquiv p.rho - p.rho) :=
  current_gap_seven_phase_dvd p (by decide)
