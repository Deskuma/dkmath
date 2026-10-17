/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenCurrentQuotientReal

#print "file: DkMathTest.FLT.Kummer.SevenCurrentQuotientReal"

#print axioms DkMath.FLT.Kummer.SevenRealGN.common_quotient_real_spec
#print axioms DkMath.FLT.Kummer.SevenRealGN.common_quotient_eq_real
#print axioms DkMath.FLT.Kummer.SevenRealGN.common_quotient_star
#print axioms DkMath.FLT.Kummer.SevenRealGN.cyclotomicNormHom_ofReal_square
#print axioms DkMath.FLT.Kummer.SevenRealGN.cyclotomicNormHom_zeta_one
#print axioms DkMath.FLT.Kummer.SevenRealGN.common_quotient_norm_square
#print axioms DkMath.FLT.Kummer.SevenRealGN.phase_root_correction_norm_seven_square
#print axioms DkMath.FLT.Kummer.SevenRealGN.smaller_packet_real_quotient
#print axioms DkMath.FLT.Kummer.SevenRealGN.common_quotient_smaller_packet
#print axioms DkMath.FLT.Kummer.SevenRealGN.phase_root_correction_norm_smaller_packet
#print axioms DkMath.FLT.Kummer.SevenRealGN.phase_root_correction_norm_seven_square_pos
#print axioms DkMath.FLT.Kummer.SevenRealGN.phase_root_correction_norm_valuation_odd

run_cmd do
  for n in #[
      ``DkMath.FLT.Kummer.SevenRealGN.common_quotient_real_spec,
      ``DkMath.FLT.Kummer.SevenRealGN.common_quotient_eq_real,
      ``DkMath.FLT.Kummer.SevenRealGN.common_quotient_star,
      ``DkMath.FLT.Kummer.SevenRealGN.cyclotomicNormHom_ofReal_square,
      ``DkMath.FLT.Kummer.SevenRealGN.cyclotomicNormHom_zeta_one,
      ``DkMath.FLT.Kummer.SevenRealGN.common_quotient_norm_square,
      ``DkMath.FLT.Kummer.SevenRealGN.phase_root_correction_norm_seven_square,
      ``DkMath.FLT.Kummer.SevenRealGN.smaller_packet_real_quotient,
      ``DkMath.FLT.Kummer.SevenRealGN.common_quotient_smaller_packet,
      ``DkMath.FLT.Kummer.SevenRealGN.phase_root_correction_norm_smaller_packet,
      ``DkMath.FLT.Kummer.SevenRealGN.phase_root_correction_norm_seven_square_pos,
      ``DkMath.FLT.Kummer.SevenRealGN.phase_root_correction_norm_valuation_odd] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {n}"
  Lean.logInfo "PASS: 12 public theorems; standard axiom whitelist only."

open DkMath.FLT.Seven DkMath.FLT.Kummer.SevenPrimaryNorm
open DkMath.FLT.Kummer.SevenRealGN
open DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt
variable {a b d : ℕ} {source : CounterexamplePack a b d}
variable {r : PrimitiveCounterexampleRamifiedProvenance source}
variable {p : DirectRealCubicRootPacket source r}

example {w : C}
    (hg : ofReal (SevenRealCubicInt.rotateEquiv p.rho - p.rho) =
      ramifiedUniformizer ^ 64 * w) : star w = zeta * w :=
  common_quotient_star hg

example (F : CurrentPhaseSeventhFamily p) :
    ∃ M : ℕ, 0 < M ∧ ∀ i : Fin 6,
      Int.natAbs (cyclotomicNormHom (F.root i ^ 7 + ofReal p.rho)) = 7 * M ^ 2 :=
  phase_root_correction_norm_seven_square_pos F

example (F : CurrentPhaseSeventhFamily p) (i : Fin 6) :
    Odd (padicValNat 7 (Int.natAbs
      (cyclotomicNormHom (F.root i ^ 7 + ofReal p.rho)))) :=
  phase_root_correction_norm_valuation_odd F i

example (F : CurrentPhaseSeventhFamily p) (S : DirectOrbitSmallerNormPacket p)
    (i : Fin 6) :
    Int.natAbs (cyclotomicNormHom (F.root i ^ 7 + ofReal p.rho)) =
      7 * (7 ^ 31 * (7 ^ (42 * S.powerSplit.gapSplit.k) * S.normRoot ^ 7)) ^ 2 :=
  phase_root_correction_norm_smaller_packet F S i
