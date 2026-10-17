/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenCurrentRootDepth

#print "file: DkMathTest.FLT.Kummer.SevenCurrentRootDepthAxioms"

/-! 新規21定理と1定義の公理 whitelist。 -/

#print axioms DkMath.FLT.Kummer.SevenRealGN.phase_root_seventh_deep
#print axioms DkMath.FLT.Kummer.SevenRealGN.phase_roots_seventh_sub_deep
#print axioms DkMath.FLT.Kummer.SevenRealGN.phase_root_residue
#print axioms DkMath.FLT.Kummer.SevenRealGN.phase_roots_local_global_data
#print axioms DkMath.FLT.Kummer.SevenRealGN.exists_common_phase_root_correction_norm
#print axioms DkMath.FLT.Kummer.SevenRealGN.phase_roots_weighted_congruence
#print axioms DkMath.FLT.Kummer.SevenRealGN.phase_root_zeta_difference_not_dvd_sq

run_cmd do
  for n in #[
      ``DkMath.FLT.Kummer.SevenRealGN.phaseRootTwist,
      ``DkMath.FLT.Kummer.SevenRealGN.phaseRootTwist_spec,
      ``DkMath.FLT.Kummer.SevenRealGN.phase_root_gap_identity,
      ``DkMath.FLT.Kummer.SevenRealGN.exists_common_phase_root_correction,
      ``DkMath.FLT.Kummer.SevenRealGN.phase_root_seventh_deep,
      ``DkMath.FLT.Kummer.SevenRealGN.phase_root_seventh_deep_of_le,
      ``DkMath.FLT.Kummer.SevenRealGN.phase_roots_seventh_sub_deep,
      ``DkMath.FLT.Kummer.SevenRealGN.phase_roots_seventh_sub_deep_of_le,
      ``DkMath.FLT.Kummer.SevenRealGN.phase_root_residue,
      ``DkMath.FLT.Kummer.SevenRealGN.phase_roots_same_residue,
      ``DkMath.FLT.Kummer.SevenRealGN.phase_root_residue_ne_zero,
      ``DkMath.FLT.Kummer.SevenRealGN.phase_roots_sub_uniformizer_dvd,
      ``DkMath.FLT.Kummer.SevenRealGN.phase_roots_local_global_data,
      ``DkMath.FLT.Kummer.SevenRealGN.phase_root_correction_ideals_eq,
      ``DkMath.FLT.Kummer.SevenRealGN.exists_common_phase_root_correction_norm,
      ``DkMath.FLT.Kummer.SevenRealGN.weighted_common_center_congruence,
      ``DkMath.FLT.Kummer.SevenRealGN.weighted_common_center_exact,
      ``DkMath.FLT.Kummer.SevenRealGN.phase_roots_weighted_congruence_of_le,
      ``DkMath.FLT.Kummer.SevenRealGN.phase_roots_weighted_congruence,
      ``DkMath.FLT.Kummer.SevenRealGN.phase_root_zeta_seventh_eq,
      ``DkMath.FLT.Kummer.SevenRealGN.phase_root_zeta_difference_not_dvd_sq,
      ``DkMath.FLT.Kummer.SevenRealGN.phase_root_correction_ne_zero] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {n}"
  Lean.logInfo "PASS: 21 new public theorems and 1 definition (22 checked); standard axiom whitelist only."
