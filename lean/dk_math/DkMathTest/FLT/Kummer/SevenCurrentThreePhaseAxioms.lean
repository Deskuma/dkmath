/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenCurrentThreePhase

/-! 公開24定理、2定義、構造体とその生成宣言を標準公理の whitelist で検査する。 -/

#print axioms DkMath.Lib.Cosmic.phaseSource_three_term_relation
#print axioms DkMath.FLT.Kummer.SevenRealGN.exists_current_phase_seventh_family
#print axioms DkMath.FLT.Kummer.SevenRealGN.current_three_phase_data_receiver
#print axioms DkMath.FLT.Kummer.SevenRealGN.CurrentPhaseSeventhFamily.real_weighted_seventh_equation
#print axioms DkMath.FLT.Kummer.SevenRealGN.no_common_unit_clears_three_phase_coefficients
#print axioms DkMath.FLT.Kummer.SevenRealGN.CurrentPhaseSeventhFamily.root_not_real

run_cmd do
  for n in #[
      ``DkMath.Lib.Cosmic.phaseSource_three_term_relation,
      ``DkMath.Lib.Cosmic.phaseSource_pow_three_term_relation,
      ``DkMath.Lib.Cosmic.phaseSource_three_consecutive_power_relation,
      ``DkMath.FLT.Kummer.SevenRealGN.phase_index_not_seven_dvd,
      ``DkMath.FLT.Kummer.SevenRealGN.phase_root_away_of_factor,
      ``DkMath.FLT.Kummer.SevenRealGN.phase_ramified_element_receiver,
      ``DkMath.FLT.Kummer.SevenRealGN.exists_phase_unit_free_root,
      ``DkMath.FLT.Kummer.SevenRealGN.CurrentPhaseSeventhFamily,
      ``DkMath.FLT.Kummer.SevenRealGN.exists_current_phase_seventh_family,
      ``DkMath.FLT.Kummer.SevenRealGN.CurrentPhaseSeventhFamily.root_ne_zero,
      ``DkMath.FLT.Kummer.SevenRealGN.CurrentPhaseSeventhFamily.root_ideal_power,
      ``DkMath.FLT.Kummer.SevenRealGN.CurrentPhaseSeventhFamily.root_ideals_pairwise,
      ``DkMath.FLT.Kummer.SevenRealGN.CurrentPhaseSeventhFamily.replaceRoot,
      ``DkMath.FLT.Kummer.SevenRealGN.CurrentPhaseSeventhFamily.replaceRoot_at,
      ``DkMath.FLT.Kummer.SevenRealGN.currentPhaseSlot,
      ``DkMath.FLT.Kummer.SevenRealGN.currentPhaseSlot_spec,
      ``DkMath.FLT.Kummer.SevenRealGN.current_phase_family_extending_root,
      ``DkMath.FLT.Kummer.SevenRealGN.current_phase_family_receiver,
      ``DkMath.FLT.Kummer.SevenRealGN.CurrentPhaseSeventhFamily.realGN_factor,
      ``DkMath.FLT.Kummer.SevenRealGN.CurrentPhaseSeventhFamily.three_term_relation,
      ``DkMath.FLT.Kummer.SevenRealGN.CurrentPhaseSeventhFamily.consecutive_phase_relation,
      ``DkMath.FLT.Kummer.SevenRealGN.CurrentPhaseSeventhFamily.real_weighted_seventh_equation,
      ``DkMath.FLT.Kummer.SevenRealGN.three_phase_coefficients_are_units,
      ``DkMath.FLT.Kummer.SevenRealGN.no_common_unit_clears_three_phase_coefficients,
      ``DkMath.FLT.Kummer.SevenRealGN.exists_current_three_phase_data,
      ``DkMath.FLT.Kummer.SevenRealGN.CurrentPhaseSeventhFamily.root_not_real,
      ``DkMath.FLT.Kummer.SevenRealGN.current_three_phase_data_receiver,
      ``DkMath.FLT.Kummer.SevenRealGN.CurrentPhaseSeventhFamily.mk,
      ``DkMath.FLT.Kummer.SevenRealGN.CurrentPhaseSeventhFamily.root,
      ``DkMath.FLT.Kummer.SevenRealGN.CurrentPhaseSeventhFamily.factor,
      ``DkMath.FLT.Kummer.SevenRealGN.CurrentPhaseSeventhFamily.root_away] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {n}"
  Lean.logInfo "PASS: 24 public theorems, 2 definitions, structure and generated declarations (31 checked); standard axiom whitelist only."
