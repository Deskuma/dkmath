/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailCyclotomicTailDerivative

#print "file: DkMath.FLT.Seven.GTailCyclotomicTailTaylorLift"

namespace DkMath.FLT.Seven

open DkMath.CosmicFormula DkMath.Lib.NumberTheory Polynomial

/-- Integer derivative of the original homogeneous shell. -/
noncomputable def gtailDerivativeInt (c g : ℕ) : ℤ :=
  (tailShellPoly (c : ℤ)).derivative.eval ((c + g : ℕ) : ℤ)

/-- First-order remainder with a checked integral quotient; no prime or unit guard. -/
theorem tailShellPoly_integer_taylor (c x h : ℤ) :
    h ^ 2 ∣ (tailShellPoly c).eval (x + h) - (tailShellPoly c).eval x -
      h * (tailShellPoly c).derivative.eval x := by
  refine ⟨(15 * x ^ 4 +
    20 * x ^ 3 * h +
    10 * x ^ 3 * c +
    15 * x ^ 2 * h ^ 2 +
    10 * x ^ 2 * h * c +
    6 * x ^ 2 * c ^ 2 +
    6 * x * h ^ 3 +
    5 * x * h ^ 2 * c +
    4 * x * h * c ^ 2 +
    3 * x * c ^ 3 +
    h ^ 4 +
    h ^ 3 * c +
    h ^ 2 * c ^ 2 +
    h * c ^ 3 +
    c ^ 4), ?_⟩
  norm_num [tailShellPoly, Fin.sum_univ_succ, derivative_mul, derivative_pow, C_ofNat]
  ring

/-- The native natural Tail has the same first-order integer congruence. -/
theorem gtail_integer_taylor (q c g d : ℕ) :
    (q : ℤ) ^ 2 ∣ ((GTail 7 1 (g + q * d) c : ℕ) : ℤ) -
      ((GTail 7 1 g c : ℕ) : ℤ) - ((q * d : ℕ) : ℤ) * gtailDerivativeInt c g := by
  have h := tailShellPoly_integer_taylor (c : ℤ) ((c + g : ℕ) : ℤ) ((q * d : ℕ) : ℤ)
  have he : ((c + g : ℕ) : ℤ) + ((q * d : ℕ) : ℤ) =
      ((c + (g + q * d) : ℕ) : ℤ) := by push_cast; ring
  rw [he, tailShellPoly_eval_nat, tailShellPoly_eval_nat] at h
  obtain ⟨k, hk⟩ := h
  refine ⟨(d : ℤ) ^ 2 * k, ?_⟩
  dsimp only [gtailDerivativeInt]
  rw [hk]
  push_cast
  ring

/-- Reduction of the integer derivative to the coefficient field. -/
theorem gtailDerivativeInt_cast {q : ℕ} (c g : ℕ) :
    (gtailDerivativeInt c g : ZMod q) =
      (tailShellPoly (c : ZMod q)).derivative.eval ((c + g : ℕ) : ZMod q) := by
  simp [gtailDerivativeInt, tailShellPoly, Fin.sum_univ_succ, derivative_mul,
    derivative_pow, C_ofNat]

/-- Exact integer cancellation, with no division by q in ZMod(q²). -/
theorem gtail_lift_sq_iff_linear {q : ℕ} [Fact (Nat.Prime q)]
    (c g d : ℕ) (hT : q ∣ GTail 7 1 g c) :
    q ^ 2 ∣ GTail 7 1 (g + q * d) c ↔
      ((GTail 7 1 g c / q : ℕ) : ZMod q) + (d : ZMod q) *
        (tailShellPoly (c : ZMod q)).derivative.eval ((c + g : ℕ) : ZMod q) = 0 := by
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime q).ne_zero
  have hm : (q : ℤ) * ((GTail 7 1 g c / q : ℕ) : ℤ) =
      ((GTail 7 1 g c : ℕ) : ℤ) := by
    exact_mod_cast Nat.mul_div_cancel' hT
  obtain ⟨k, hk⟩ := gtail_integer_taylor q c g d
  have he : ((GTail 7 1 (g + q * d) c : ℕ) : ℤ) = (q : ℤ) *
      (((GTail 7 1 g c / q : ℕ) : ℤ) + (d : ℤ) * gtailDerivativeInt c g + (q : ℤ) * k) := by
    push_cast at hk
    linear_combination hk - hm
  have hd : (q : ℤ) ∣ (q : ℤ) * k := dvd_mul_right _ _
  have hi : (q : ℤ) ^ 2 ∣ ((GTail 7 1 (g + q * d) c : ℕ) : ℤ) ↔
      (q : ℤ) ∣ ((GTail 7 1 g c / q : ℕ) : ℤ) + (d : ℤ) * gtailDerivativeInt c g := by
    rw [he, pow_two, mul_dvd_mul_iff_left hq0]
    exact dvd_add_left hd
  have hn : q ^ 2 ∣ GTail 7 1 (g + q * d) c ↔
      (q : ℤ) ^ 2 ∣ ((GTail 7 1 (g + q * d) c : ℕ) : ℤ) := by
    norm_cast
  rw [hn, hi, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, gtailDerivativeInt_cast]

/-- The unique correction residue, with the starting Tail quotient explicit. -/
noncomputable def gtailFirstCorrection {q : ℕ} [Fact (Nat.Prime q)] (c g : ℕ) : ZMod q :=
  -((GTail 7 1 g c / q : ℕ) : ZMod q) /
    (tailShellPoly (c : ZMod q)).derivative.eval ((c + g : ℕ) : ZMod q)

/-- The field derivative is nonzero under the canonical native Tail guards. -/
theorem gtail_shell_derivative_ne_zero {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c) :
    (tailShellPoly (c : ZMod q)).derivative.eval ((c + g : ℕ) : ZMod q) ≠ 0 := by
  have he : gtailSelectedCofactorResidue c g hc hg hT 0 =
      (tailShellPoly (c : ZMod q)).derivative.eval ((c + g : ℕ) : ZMod q) :=
    eval_selected_cofactor_eq_tailShellPoly_derivative c g hc hg hT 0
  rw [← he]
  exact gtail_selected_cofactor_ne_zero c g hc hg hT 0

theorem gtailFirstCorrection_equation {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c) :
    ((GTail 7 1 g c / q : ℕ) : ZMod q) + gtailFirstCorrection c g *
      (tailShellPoly (c : ZMod q)).derivative.eval ((c + g : ℕ) : ZMod q) = 0 := by
  dsimp only [gtailFirstCorrection]
  rw [div_mul_cancel₀ _ (gtail_shell_derivative_ne_zero c g hc hg hT)]
  exact add_neg_cancel _

theorem gtailFirstCorrection_unique {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c)
    (d : ZMod q) (hd : ((GTail 7 1 g c / q : ℕ) : ZMod q) + d *
      (tailShellPoly (c : ZMod q)).derivative.eval ((c + g : ℕ) : ZMod q) = 0) :
    d = gtailFirstCorrection c g := by
  apply mul_right_cancel₀ (gtail_shell_derivative_ne_zero c g hc hg hT)
  have he := gtailFirstCorrection_equation c g hc hg hT
  linear_combination hd - he

/-- All natural corrections are characterized by exactly one residue class. -/
theorem gtail_lift_sq_iff_correction {q : ℕ} [Fact (Nat.Prime q)]
    (c g d : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c) :
    q ^ 2 ∣ GTail 7 1 (g + q * d) c ↔ (d : ZMod q) = gtailFirstCorrection c g := by
  rw [gtail_lift_sq_iff_linear c g d hT]
  constructor
  · exact gtailFirstCorrection_unique c g hc hg hT _
  · intro hd
    rw [hd]
    exact gtailFirstCorrection_equation c g hc hg hT

/-- The canonical natural representative gives one verified lift to q². -/
theorem gtail_first_correction_lifts {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c) :
    q ^ 2 ∣ GTail 7 1 (g + q * (gtailFirstCorrection (q := q) c g).val) c := by
  apply (gtail_lift_sq_iff_correction c g _ hc hg hT).mpr
  exact ZMod.natCast_zmod_val _

theorem gtail_shift_cast {q : ℕ} (g d : ℕ) :
    ((g + q * d : ℕ) : ZMod q) = (g : ZMod q) := by
  simp

theorem gtail_shift_gap_unit {q : ℕ} (g d : ℕ) (hg : ¬ q ∣ g) :
    ¬ q ∣ g + q * d := by
  intro h
  have hz := (ZMod.natCast_eq_zero_iff (g + q * d) q).mpr h
  rw [gtail_shift_cast] at hz
  exact hg ((ZMod.natCast_eq_zero_iff g q).mp hz)

theorem gtail_shift_ratio {q : ℕ} [Fact (Nat.Prime q)] (c g d : ℕ) :
    gtailSevenTailRatio q c (g + q * d) = gtailSevenTailRatio q c g := by
  simp [gtailSevenTailRatio, Nat.cast_add, Nat.cast_mul]

theorem gtail_shift_derivative {q : ℕ} (c g d : ℕ) :
    (tailShellPoly (c : ZMod q)).derivative.eval ((c + (g + q * d) : ℕ) : ZMod q) =
      (tailShellPoly (c : ZMod q)).derivative.eval ((c + g : ℕ) : ZMod q) := by
  simp

theorem gtail_shift_tail_support {q : ℕ} (c g d : ℕ) (hT : q ∣ GTail 7 1 g c) :
    q ∣ GTail 7 1 (g + q * d) c := by
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  rw [← tailShellPoly_eval_nat]
  have hz := (ZMod.natCast_eq_zero_iff (GTail 7 1 g c) q).mpr hT
  rw [← tailShellPoly_eval_nat] at hz
  simpa using hz

end DkMath.FLT.Seven
