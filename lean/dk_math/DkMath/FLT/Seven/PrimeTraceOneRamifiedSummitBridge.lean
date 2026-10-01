/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimeTraceOneRamifiedObstruction
import DkMath.FLT.Seven.SevenBaseTerminalRamifiedDepth

#print "file: DkMath.FLT.Seven.PrimeTraceOneRamifiedSummitBridge"

namespace DkMath.FLT.Seven

open DkMath.CosmicFormulaBinom
open DkMath.NumberTheory.TraceOneQuadratic

local notation "tqNorm" => DkMath.NumberTheory.TraceOneQuadratic.norm

/-! Directly package the specialized quadratic packet into the historical
common summit.  No Row-Y/Row-Z terminal profile is reconstructed here. -/

def SevenQuadraticSeventhPowerPacket.toPrimitiveRamifiedSummitPacket
    {x y z : ℕ} (p : SevenQuadraticSeventhPowerPacket x y z) :
    PrimitiveRamifiedSummitPacket := by
  let s := p.residual.powerSplit
  let source := s.sevenAdic.counterexample
  have hyz : y ≤ z :=
    (right_lt_of_fermat7Equation source.hx source.hEq).le
  have hcyclo : cyclotomicSeven (z : ℤ) (y : ℤ) =
      7 * (s.b : ℤ) ^ 7 := by
    calc
      _ = ((GN 7 (z - y) y : ℕ) : ℤ) := by
        rw [GN_seven_sub_eq_traceOneNorm_negTwo z y hyz,
          cyclotomicSeven_eq_traceOneNorm_negTwo]
      _ = _ := by exact_mod_cast s.residual_eq
  exact {
    endpointLeft := z
    endpointRight := y
    distinguished := x
    gapRoot := s.a
    residualRoot := s.b
    root := p.root
    gapRoot_pos := s.a_pos
    residualRoot_pos := s.b_pos
    endpoint_coprime :=
      (coprime_y_z_of_counterexamplePack source).symm.isCoprime
    endpointLeft_ne_zero := by exact_mod_cast source.hz.ne'
    endpointRight_ne_zero := by exact_mod_cast source.hy.ne'
    endpointSum_ne_zero := by
      have hypos : (0 : ℤ) < y := by exact_mod_cast source.hy
      have hzpos : (0 : ℤ) < z := by exact_mod_cast source.hz
      omega
    coordinate_coprime :=
      counterexample_cyclotomicSeven_coordinates_isCoprime source
    endpointRight_not_seven_dvd := by
      intro hy
      exact s.sevenAdic.seven_not_dvd_y (Int.ofNat_dvd.mp hy)
    residualRoot_not_seven_dvd := s.seven_not_dvd_b
    fermat_eq := by
      have h := source.hEq
      unfold Fermat7Equation at h
      nlinarith
    gap_eq := by exact_mod_cast s.gap_eq
    residual_eq := hcyclo
    distinguished_eq := by exact_mod_cast s.distinguished_eq
    coordinate_eq := p.coordinate_eq
    root_norm_eq := p.root_norm_eq }

theorem SevenQuadraticSeventhPowerPacket.rootSnd_padicValNat_exact
    {x y z : ℕ} (p : SevenQuadraticSeventhPowerPacket x y z) :
    padicValNat 7 (Int.natAbs p.root.snd) =
      5 + 7 * padicValNat 7 p.residual.powerSplit.a := by
  simpa [SevenQuadraticSeventhPowerPacket.toPrimitiveRamifiedSummitPacket] using
    p.toPrimitiveRamifiedSummitPacket.rootSnd_padicValNat

end DkMath.FLT.Seven
