/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalRowZAlternatingPowerSplit
import Mathlib.Data.ZMod.Basic

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionModSixResidues"

/-! Primitive seventh residuals modulo six. These are necessary arithmetic
constraints only; no allocation receiver or FLT7 closure is asserted. -/

namespace DkMath.FLT.Seven
open DkMath.CosmicFormulaBinom

/-- Coprime endpoints cannot share either prime factor of six. -/
private theorem primitive_residues {x y : ℕ} (h : Nat.Coprime x y) :
    ¬ (x % 6 % 2 = 0 ∧ y % 6 % 2 = 0) ∧
    ¬ (x % 6 % 3 = 0 ∧ y % 6 % 3 = 0) := by
  constructor <;> rintro ⟨hx, hy⟩
  · rw [Nat.mod_mod_of_dvd x (by decide : 2 ∣ 6)] at hx
    rw [Nat.mod_mod_of_dvd y (by decide : 2 ∣ 6)] at hy
    exact Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 2)
      (Nat.dvd_of_mod_eq_zero hx) (Nat.dvd_of_mod_eq_zero hy) h
  · rw [Nat.mod_mod_of_dvd x (by decide : 3 ∣ 6)] at hx
    rw [Nat.mod_mod_of_dvd y (by decide : 3 ∣ 6)] at hy
    exact Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 3)
      (Nat.dvd_of_mod_eq_zero hx) (Nat.dvd_of_mod_eq_zero hy) h

/-- The natural alternating factor has residue one for primitive endpoints.
The existing integer-cast identity justifies reducing the signed polynomial. -/
theorem alternatingCyclotomicSeven_mod_six_of_coprime {x y : ℕ} (hxy : Nat.Coprime x y) :
    Nat.ModEq 6 (alternatingCyclotomicSeven x y) 1 := by
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  have hc := congrArg (fun z : ℤ => (z : ZMod 6))
    (alternatingCyclotomicSeven_intCast x y)
  simp only [Int.cast_natCast, cyclotomicSeven, Int.cast_add, Int.cast_mul,
    Int.cast_pow, Int.cast_neg] at hc
  rw [hc]
  have hp := primitive_residues hxy
  have hx := Nat.mod_lt x (by decide : 0 < 6)
  have hy := Nat.mod_lt y (by decide : 0 < 6)
  rw [← ZMod.natCast_mod x 6, ← ZMod.natCast_mod y 6]
  interval_cases x % 6 <;> interval_cases y % 6 <;> norm_num at hp <;> decide

/-- The seventh GN residual has residue one for a primitive gap/unit pair.
Its homogeneous endpoints are `D + u` and `u`. -/
theorem GN_seven_mod_six_of_coprime {D u : ℕ} (hDu : Nat.Coprime D u) : Nat.ModEq 6 (GN 7 D u) 1 := by
  rw [GN_seven_eq_gap_mul_add_seven_mul_y_pow_six]
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  push_cast
  have hp := primitive_residues hDu
  have hD := Nat.mod_lt D (by decide : 0 < 6)
  have hu := Nat.mod_lt u (by decide : 0 < 6)
  rw [← ZMod.natCast_mod D 6, ← ZMod.natCast_mod u 6]
  interval_cases D % 6 <;> interval_cases u % 6 <;> norm_num at hp <;> decide
end DkMath.FLT.Seven
