/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenCurrentCorrectionPower

#print "file: DkMathTest.FLT.Kummer.SevenCurrentCorrectionPower"

#print axioms DkMath.FLT.Kummer.SevenRealGN.correctionCommonRoot
#print axioms DkMath.FLT.Kummer.SevenRealGN.correctionPhaseUnit
#print axioms DkMath.FLT.Kummer.SevenRealGN.correction_common_root_factor
#print axioms DkMath.FLT.Kummer.SevenRealGN.correction_common_root_ideal
#print axioms DkMath.FLT.Kummer.SevenRealGN.correction_phase_unit_ratio
#print axioms DkMath.FLT.Kummer.SevenRealGN.correction_common_root_norm
#print axioms DkMath.FLT.Kummer.SevenRealGN.correction_common_root_norm_pos
#print axioms DkMath.FLT.Kummer.SevenRealGN.correction_norm_seventh
#print axioms DkMath.FLT.Kummer.SevenRealGN.CurrentCorrectionPowerPacket
#print axioms DkMath.FLT.Kummer.SevenRealGN.currentCorrectionPowerPacket

run_cmd do
  for n in #[
      ``DkMath.FLT.Kummer.SevenRealGN.correctionCommonRoot,
      ``DkMath.FLT.Kummer.SevenRealGN.correctionPhaseUnit,
      ``DkMath.FLT.Kummer.SevenRealGN.correction_common_root_factor,
      ``DkMath.FLT.Kummer.SevenRealGN.correction_common_root_ideal,
      ``DkMath.FLT.Kummer.SevenRealGN.correction_phase_unit_ratio,
      ``DkMath.FLT.Kummer.SevenRealGN.correction_common_root_norm,
      ``DkMath.FLT.Kummer.SevenRealGN.correction_common_root_norm_pos,
      ``DkMath.FLT.Kummer.SevenRealGN.correction_norm_seventh,
      ``DkMath.FLT.Kummer.SevenRealGN.CurrentCorrectionPowerPacket,
      ``DkMath.FLT.Kummer.SevenRealGN.currentCorrectionPowerPacket] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {n}"
  Lean.logInfo "PASS: 10 public declarations; standard axiom whitelist only."

open DkMath.FLT.Seven DkMath.FLT.Kummer.SevenPrimaryNorm
open DkMath.FLT.Kummer.SevenRealGN
open DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt
variable {a b d : ℕ} {source : CounterexamplePack a b d}
variable {r : PrimitiveCounterexampleRamifiedProvenance source}
variable {p : DirectRealCubicRootPacket source r}

-- Same packet witness: explicit root, six factor equations and ideal powers.
example (F : CurrentPhaseSeventhFamily p) (S : DirectOrbitSmallerNormPacket p) :
    ∃ P : CurrentCorrectionPowerPacket F S,
      P.commonRoot = ramifiedUniformizer ^ 9 * ofReal
        (SevenRealCubicInt.eisensteinAxis ^ (6 * S.powerSplit.gapSplit.k) * S.powerSplit.gapRoot) ∧
      (∀ i, F.root i ^ 7 + ofReal p.rho = (P.phaseUnit i : C) * P.commonRoot ^ 7) ∧
      (∀ i, Ideal.span ({F.root i ^ 7 + ofReal p.rho} : Set C) =
        Ideal.span ({P.commonRoot} : Set C) ^ 7) :=
  ⟨currentCorrectionPowerPacket F S, rfl,
    (currentCorrectionPowerPacket F S).factor, (currentCorrectionPowerPacket F S).ideal⟩

-- The phase ratio is unchanged when the smaller-norm packet is changed.
example (S V : DirectOrbitSmallerNormPacket p) (i j : Fin 6) :
    correctionPhaseUnit S i * (correctionPhaseUnit S j)⁻¹ =
      correctionPhaseUnit V i * (correctionPhaseUnit V j)⁻¹ := by
  rw [correction_phase_unit_ratio, correction_phase_unit_ratio]

-- Positive COMMON norm whose seventh power describes every correction.
example (F : CurrentPhaseSeventhFamily p) (S : DirectOrbitSmallerNormPacket p) :
    ∃ n : ℕ, 0 < n ∧ ∀ i : Fin 6,
      Int.natAbs (cyclotomicNormHom (F.root i ^ 7 + ofReal p.rho)) = n ^ 7 := by
  let P := currentCorrectionPowerPacket F S
  refine ⟨Int.natAbs (cyclotomicNormHom P.commonRoot), P.norm_pos, fun i => ?_⟩
  rw [P.norm]
  exact P.correctionNorm i
