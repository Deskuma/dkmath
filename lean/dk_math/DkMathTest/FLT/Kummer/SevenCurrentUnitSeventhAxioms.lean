/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenCurrentUnitSeventh

/-! 回転固定性と current 単元七乗性について、新規公開18定理の公理を検査する。 -/

open DkMath.FLT.Seven.SevenRealCubicInt DkMath.FLT.Kummer.SevenRealGN

#print axioms rotation_fixed_mod_seven_integer
#print axioms realPrimary_seventh_of_rotation_fixed
#print axioms current_corrected_unit_seventh
#print axioms current_primary_packet_obstruction_zero
#print axioms currentCarrier_unit_free_factor_receiver
#print axioms current_unit_free_root_not_real

run_cmd do
  for n in #[
      ``DkMath.FLT.Seven.SevenRealCubicInt.seven_dvd_iff_coordinates,
      ``DkMath.FLT.Seven.SevenRealCubicInt.rotation_gap_thetaLinear_mod_seven,
      ``DkMath.FLT.Seven.SevenRealCubicInt.rotation_gap_thetaSquare_mod_seven,
      ``DkMath.FLT.Seven.SevenRealCubicInt.rotation_fixed_mod_seven_fst,
      ``DkMath.FLT.Seven.SevenRealCubicInt.rotation_fixed_mod_seven_integer,
      ``DkMath.FLT.Seven.SevenRealCubicInt.rotation_fixed_mod_seven_iff_integer,
      ``DkMath.FLT.Kummer.SevenRealGN.realPrimary_integer_congruence_of_rotation_fixed,
      ``DkMath.FLT.Kummer.SevenRealGN.realPrimary_seventh_of_rotation_fixed,
      ``DkMath.FLT.Kummer.SevenRealGN.current_rotation_gap_seven_dvd,
      ``DkMath.FLT.Kummer.SevenRealGN.current_rho_congruent_integer,
      ``DkMath.FLT.Kummer.SevenRealGN.current_primary_packet_unit_seventh,
      ``DkMath.FLT.Kummer.SevenRealGN.current_corrected_unit_seventh,
      ``DkMath.FLT.Kummer.SevenRealGN.current_primary_packet_obstruction_zero,
      ``DkMath.FLT.Kummer.SevenRealGN.PrimaryPacket.unit_absorption,
      ``DkMath.FLT.Kummer.SevenRealGN.PrimaryPacket.unit_absorption_no_measure_drop,
      ``DkMath.FLT.Kummer.SevenRealGN.currentCarrier_unit_free_factor_receiver,
      ``DkMath.FLT.Kummer.SevenRealGN.current_rotation_ne_self,
      ``DkMath.FLT.Kummer.SevenRealGN.current_unit_free_root_not_real] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {n}"
  Lean.logInfo "PASS: 18 new public theorems; standard axiom whitelist only."
