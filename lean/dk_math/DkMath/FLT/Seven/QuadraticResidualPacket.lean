/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenAdicPowerSplit

#print "file: DkMath.FLT.Seven.QuadraticResidualPacket"

namespace DkMath.FLT.Seven

open DkMath.CosmicFormulaBinom
open DkMath.NumberTheory.TraceOneQuadratic

local notation "tqNorm" => DkMath.NumberTheory.TraceOneQuadratic.norm

/-- The terminal discriminant-`-7` residual together with its exact natural
seventh-power norm source.  No element-level power claim is included. -/
structure SevenQuadraticResidualPacket (x y z : ℕ) : Type where
  powerSplit : SevenAdicPowerSplit x y z
  residualCore : TraceOneInt (-2)
  coordinate_eq :
    cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ) = sevenAxis * residualCore
  residual_ne_zero : residualCore ≠ 0
  residual_terminal : ¬ sevenAxis ∣ residualCore
  residual_norm_not_seven_dvd : ¬ (7 : ℤ) ∣ tqNorm residualCore
  residual_norm_eq : tqNorm residualCore = (powerSplit.b : ℤ) ^ 7
  residual_norm_pos : 1 ≤ tqNorm residualCore

theorem nonempty_sevenQuadraticResidualPacket_of_powerSplit
    {x y z : ℕ} (s : SevenAdicPowerSplit x y z) :
    Nonempty (SevenQuadraticResidualPacket x y z) := by
  have hyz := (right_lt_of_fermat7Equation
    s.sevenAdic.counterexample.hx s.sevenAdic.counterexample.hEq).le
  have hgapInt : (7 : ℤ) ∣ (z : ℤ) - (y : ℤ) := by
    have hcast : (7 : ℤ) ∣ ((z - y : ℕ) : ℤ) :=
      Int.ofNat_dvd.mpr s.sevenAdic.seven_dvd_gap
    simpa [Int.ofNat_sub hyz] using hcast
  have hyInt : ¬ (7 : ℤ) ∣ (y : ℤ) := by
    intro hy
    exact s.sevenAdic.seven_not_dvd_y (Int.ofNat_dvd.mp hy)
  rcases exists_cyclotomicSeven_terminal_core hgapInt hyInt with
    ⟨r, hcoordinate, hr0, hrTerminal, hrNorm7, hcycloNorm, hrNormPos⟩
  have hGNcyclo : ((GN 7 (z - y) y : ℕ) : ℤ) =
      cyclotomicSeven (z : ℤ) (y : ℤ) := by
    rw [GN_seven_sub_eq_traceOneNorm_negTwo z y hyz,
      ← cyclotomicSeven_eq_traceOneNorm_negTwo]
  have hsplitInt : ((GN 7 (z - y) y : ℕ) : ℤ) =
      7 * (s.b : ℤ) ^ 7 := by
    exact_mod_cast s.residual_eq
  have hnorm : tqNorm r = (s.b : ℤ) ^ 7 := by
    apply mul_left_cancel₀ (by norm_num : (7 : ℤ) ≠ 0)
    calc
      7 * tqNorm r = cyclotomicSeven (z : ℤ) (y : ℤ) := hcycloNorm.symm
      _ = ((GN 7 (z - y) y : ℕ) : ℤ) := hGNcyclo.symm
      _ = 7 * (s.b : ℤ) ^ 7 := hsplitInt
  exact ⟨{
    powerSplit := s
    residualCore := r
    coordinate_eq := hcoordinate
    residual_ne_zero := hr0
    residual_terminal := hrTerminal
    residual_norm_not_seven_dvd := hrNorm7
    residual_norm_eq := hnorm
    residual_norm_pos := hrNormPos }⟩

noncomputable def sevenQuadraticResidualPacket_of_powerSplit
    {x y z : ℕ} (s : SevenAdicPowerSplit x y z) :
    SevenQuadraticResidualPacket x y z :=
  Classical.choice (nonempty_sevenQuadraticResidualPacket_of_powerSplit s)

noncomputable def sevenQuadraticResidualPacket_of_counterexample
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : 7 ∣ z - y) : SevenQuadraticResidualPacket x y z :=
  sevenQuadraticResidualPacket_of_powerSplit
    (sevenAdicPowerSplit_of_counterexample hPack hBranch)

theorem SevenQuadraticResidualPacket.norm_is_seventh_power
    {x y z : ℕ} (q : SevenQuadraticResidualPacket x y z) :
    ∃ b : ℕ, tqNorm q.residualCore = (b : ℤ) ^ 7 :=
  ⟨q.powerSplit.b, q.residual_norm_eq⟩

theorem SevenQuadraticResidualPacket.norm_positive
    {x y z : ℕ} (q : SevenQuadraticResidualPacket x y z) :
    0 < tqNorm q.residualCore :=
  lt_of_lt_of_le (by norm_num) q.residual_norm_pos

end DkMath.FLT.Seven
