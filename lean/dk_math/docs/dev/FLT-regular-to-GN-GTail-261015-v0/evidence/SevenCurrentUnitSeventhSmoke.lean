import DkMath.FLT.Kummer

open DkMath.FLT.Seven DkMath.FLT.Seven.SevenRealCubicInt
open DkMath.FLT.Kummer.SevenRealGN

#check rotation_fixed_mod_seven_fst
#check rotation_fixed_mod_seven_integer
#check rotation_fixed_mod_seven_iff_integer
#check current_rho_congruent_integer
#check realPrimary_integer_congruence_of_rotation_fixed
#check current_primary_packet_unit_seventh
#check current_corrected_unit_seventh
#check current_primary_packet_obstruction_zero
#check currentCarrier_unit_free_factor_receiver
#check PrimaryPacket.unit_absorption_no_measure_drop
#check current_unit_free_root_not_real

-- The Kummer entrance exposes a concrete congruence witness, without an FLT packet.
example (n : ℤ) (w : SevenRealCubicInt) :
    ∃ m : ℤ, (7 : SevenRealCubicInt) ∣ (n : SevenRealCubicInt) + 7 * w - (m : SevenRealCubicInt) := by
  exact ⟨n, w, by ring⟩
