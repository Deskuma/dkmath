/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenCurrentPrimary

#print "file: DkMathTest.FLT.Kummer.SevenCurrentPrimaryAxioms"

/-! 新規公開定理の全件公理検査。必要条件、根の選択、現在の receiver を監査する。 -/

open DkMath.FLT.Kummer.SevenRealGN

#print axioms seventh_sub_one_dvd_seven_of_residue_one
#print axioms gap_divisible_of_primary
#print axioms exists_primary_root_gauge_iff_gap_divisible
#print axioms current_gap_seven_phase_dvd
#print axioms current_primary_iff_root_residue_one
#print axioms currentCarrier_primary_packet_receiver

run_cmd do
  for n in #[
      ``DkMath.FLT.Kummer.SevenRealGN.ramifiedEval_eq_zero_iff_dvd,
      ``DkMath.FLT.Kummer.SevenRealGN.ramifiedEval_eq_one_iff_dvd,
      ``DkMath.FLT.Kummer.SevenRealGN.uniformizer_six_dvd_seven,
      ``DkMath.FLT.Kummer.SevenRealGN.seven_dvd_uniformizer_six,
      ``DkMath.FLT.Kummer.SevenRealGN.seventh_sub_one_dvd_seven_of_residue_one,
      ``DkMath.FLT.Kummer.SevenRealGN.seventh_sub_one_dvd_seven_iff_residue_one,
      ``DkMath.FLT.Kummer.SevenRealGN.ramifiedEval_GNRamifierTwist,
      ``DkMath.FLT.Kummer.SevenRealGN.exists_unit_lift_ramifiedEval,
      ``DkMath.FLT.Kummer.SevenRealGN.exists_root_residue_normalizer,
      ``DkMath.FLT.Kummer.SevenRealGN.phaseRamifier_ne_zero,
      ``DkMath.FLT.Kummer.SevenRealGN.factor_after_ramifier_twist,
      ``DkMath.FLT.Kummer.SevenRealGN.factor_gap_identity,
      ``DkMath.FLT.Kummer.SevenRealGN.realPrimary_residue,
      ``DkMath.FLT.Kummer.SevenRealGN.root_residue_one_of_primary,
      ``DkMath.FLT.Kummer.SevenRealGN.gap_divisible_of_primary,
      ``DkMath.FLT.Kummer.SevenRealGN.primary_of_root_residue_one,
      ``DkMath.FLT.Kummer.SevenRealGN.primary_iff_root_residue_one,
      ``DkMath.FLT.Kummer.SevenRealGN.primary_after_root_gauge_iff,
      ``DkMath.FLT.Kummer.SevenRealGN.exists_primary_root_gauge_iff_gap_divisible,
      ``DkMath.FLT.Kummer.SevenRealGN.current_gap_uniformizer_pow64,
      ``DkMath.FLT.Kummer.SevenRealGN.phaseRamifier_dvd_uniformizer,
      ``DkMath.FLT.Kummer.SevenRealGN.current_gap_seven_phase_dvd,
      ``DkMath.FLT.Kummer.SevenRealGN.current_source_ne_zero,
      ``DkMath.FLT.Kummer.SevenRealGN.current_root_away,
      ``DkMath.FLT.Kummer.SevenRealGN.current_primary_iff_root_residue_one,
      ``DkMath.FLT.Kummer.SevenRealGN.exists_current_primary_extension,
      ``DkMath.FLT.Kummer.SevenRealGN.currentCarrier_primary_packet_receiver] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {n}"
  Lean.logInfo "PASS: 27 new public theorems; standard axiom whitelist only."
