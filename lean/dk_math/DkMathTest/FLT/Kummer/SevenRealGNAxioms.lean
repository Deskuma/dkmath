/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenRealGNConservation

/-! 全新規公開宣言の公理 whitelist。四保存定理と七乗判定を個別にも表示する。 -/

open DkMath.FLT.Kummer.SevenRealGN

#print axioms unit_seventh_iff_obstruction
#print axioms realPrimary_seventh_iff_norm_zero
#print axioms source_preservation
#print axioms coefficient_ring_preservation
#print axioms unit_class_preservation
#print axioms iterated_invariant_preservation
#print axioms no_ideal_measure_drop
#print axioms packetOfRealUnit

run_cmd do
  for n in #[
      ``DkMath.Lib.Algebra.root_unit_gauge_identity,
      ``DkMath.Lib.Algebra.dvd_unit_inv_pow_sub_one,
      ``DkMath.Lib.Algebra.dvd_regauged_unit_sub,
      ``DkMath.FLT.Kummer.SevenRealGN.R,
      ``DkMath.FLT.Kummer.SevenRealGN.C,
      ``DkMath.FLT.Kummer.SevenRealGN.unitConj,
      ``DkMath.FLT.Kummer.SevenRealGN.unitRatio,
      ``DkMath.FLT.Kummer.SevenRealGN.unitRatio_transport,
      ``DkMath.FLT.Kummer.SevenRealGN.unitRatio_signed_root,
      ``DkMath.FLT.Kummer.SevenRealGN.unitRatio_pow_fourteen,
      ``DkMath.FLT.Kummer.SevenRealGN.unitRatio_eighth_pow_seven,
      ``DkMath.FLT.Kummer.SevenRealGN.phaseCharacter,
      ``DkMath.FLT.Kummer.SevenRealGN.phase_target_card,
      ``DkMath.FLT.Kummer.SevenRealGN.normCoordinates,
      ``DkMath.FLT.Kummer.SevenRealGN.normCoordinates_mul,
      ``DkMath.FLT.Kummer.SevenRealGN.normCoordinates_seventh,
      ``DkMath.FLT.Kummer.SevenRealGN.phaseCharacter_seventh,
      ``DkMath.FLT.Kummer.SevenRealGN.unitObstruction,
      ``DkMath.FLT.Kummer.SevenRealGN.unit_square_eq_norm_ratio,
      ``DkMath.FLT.Kummer.SevenRealGN.unit_seventh_iff_obstruction,
      ``DkMath.FLT.Kummer.SevenRealGN.unitObstruction_mul_seventh,
      ``DkMath.FLT.Kummer.SevenRealGN.unitObstruction_eq_of_same_class,
      ``DkMath.FLT.Kummer.SevenRealGN.same_class_iff_unitObstruction_eq,
      ``DkMath.FLT.Kummer.SevenRealGN.RealPrimary,
      ``DkMath.FLT.Kummer.SevenRealGN.star_ofReal,
      ``DkMath.FLT.Kummer.SevenRealGN.signed_root_eq_one_of_congruent,
      ``DkMath.FLT.Kummer.SevenRealGN.unitRatio_congruent_one_of_realPrimary,
      ``DkMath.FLT.Kummer.SevenRealGN.unitRatio_eq_one_of_realPrimary,
      ``DkMath.FLT.Kummer.SevenRealGN.realPrimary_phase_eq_one,
      ``DkMath.FLT.Kummer.SevenRealGN.realPrimary_seventh_iff_norm_zero,
      ``DkMath.FLT.Kummer.SevenRealGN.relativeNorm_congruent_real,
      ``DkMath.FLT.Kummer.SevenRealGN.alphaEmbeddedUnit,
      ``DkMath.FLT.Kummer.SevenRealGN.alphaEmbeddedUnit_primary,
      ``DkMath.FLT.Kummer.SevenRealGN.alphaEmbeddedUnit_normCoordinates,
      ``DkMath.FLT.Kummer.SevenRealGN.alphaEmbeddedUnit_not_seventh,
      ``DkMath.FLT.Kummer.SevenRealGN.PrimaryPacket,
      ``DkMath.FLT.Kummer.SevenRealGN.PrimaryPacket.source,
      ``DkMath.FLT.Kummer.SevenRealGN.AllowedGauge,
      ``DkMath.FLT.Kummer.SevenRealGN.identityGauge,
      ``DkMath.FLT.Kummer.SevenRealGN.inverseGauge,
      ``DkMath.FLT.Kummer.SevenRealGN.zetaGauge,
      ``DkMath.FLT.Kummer.SevenRealGN.regauge,
      ``DkMath.FLT.Kummer.SevenRealGN.source_preservation,
      ``DkMath.FLT.Kummer.SevenRealGN.coefficient_ring_preservation,
      ``DkMath.FLT.Kummer.SevenRealGN.unit_class_preservation,
      ``DkMath.FLT.Kummer.SevenRealGN.root_ideal_preservation,
      ``DkMath.FLT.Kummer.SevenRealGN.ConservedData,
      ``DkMath.FLT.Kummer.SevenRealGN.snapshot,
      ``DkMath.FLT.Kummer.SevenRealGN.snapshot_regauge,
      ``DkMath.FLT.Kummer.SevenRealGN.iterate,
      ``DkMath.FLT.Kummer.SevenRealGN.iterated_invariant_preservation,
      ``DkMath.FLT.Kummer.SevenRealGN.no_ideal_measure_drop,
      ``DkMath.FLT.Kummer.SevenRealGN.packetOfRealUnit] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {n}"
  Lean.logInfo "PASS: 53 public declarations; standard axiom whitelist only."
