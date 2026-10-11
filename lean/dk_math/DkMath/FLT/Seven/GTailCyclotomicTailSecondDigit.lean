/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailCyclotomicTailTaylorLift
import DkMath.Lib.NumberTheory.PolynomialHenselDigit

#print "file: DkMath.FLT.Seven.GTailCyclotomicTailSecondDigit"

namespace DkMath.FLT.Seven

open DkMath.CosmicFormula DkMath.Lib.NumberTheory Polynomial

/-- Exact native evaluation at the second-digit shift, including zero endpoints. -/
theorem gtail_second_shift_eval (q c g d : ℕ) :
    (tailShellPoly (c : ℤ)).eval (((c + g : ℕ) : ℤ) + (q : ℤ) ^ 2 * (d : ℤ)) =
      ((GTail 7 1 (g + q ^ 2 * d) c : ℕ) : ℤ) := by
  have he : ((c + g : ℕ) : ℤ) + (q : ℤ) ^ 2 * (d : ℤ) =
      ((c + (g + q ^ 2 * d) : ℕ) : ℤ) := by push_cast; ring
  rw [he, tailShellPoly_eval_nat]

/-- Scalar second-level support supplies the original Tail support premise. -/
theorem gtail_support_of_square {q : ℕ} (c g : ℕ) (hT2 : q ^ 2 ∣ GTail 7 1 g c) :
    q ∣ GTail 7 1 g c := (dvd_pow_self q (by decide : 2 ≠ 0)).trans hT2

/-- Transport second-level support to the existing integer polynomial API. -/
theorem gtail_integer_square_support {q : ℕ} (c g : ℕ)
    (hT2 : q ^ 2 ∣ GTail 7 1 g c) :
    (q : ℤ) ^ 2 ∣ (tailShellPoly (c : ℤ)).eval ((c + g : ℕ) : ℤ) := by
  rw [tailShellPoly_eval_nat]
  exact_mod_cast hT2

/-- The derivative guard is transported through the checked integer-to-field cast. -/
theorem gtail_integer_derivative_not_dvd {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT2 : q ^ 2 ∣ GTail 7 1 g c) :
    ¬ (q : ℤ) ∣ (tailShellPoly (c : ℤ)).derivative.eval ((c + g : ℕ) : ℤ) := by
  intro hd
  have hz : (gtailDerivativeInt c g : ZMod q) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd
  rw [gtailDerivativeInt_cast] at hz
  exact gtail_shell_derivative_ne_zero c g hc hg (gtail_support_of_square c g hT2) hz

/-- Per-digit predicate transport from integer evaluation to native natural GTail. -/
theorem gtail_second_lift_predicate (q c g d : ℕ) :
    (q : ℤ) ^ 3 ∣ (tailShellPoly (c : ℤ)).eval
      (((c + g : ℕ) : ℤ) + (q : ℤ) ^ 2 * (d : ℤ)) ↔
    q ^ 3 ∣ GTail 7 1 (g + q ^ 2 * d) c := by
  rw [gtail_second_shift_eval]
  norm_cast

/-- The existing finite polynomial digit theorem, specialized at k=2 to native GTail. -/
theorem existsUnique_gtail_second_digit {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT2 : q ^ 2 ∣ GTail 7 1 g c) :
    ∃! t : Fin q, q ^ 3 ∣ GTail 7 1 (g + q ^ 2 * t.val) c := by
  have h := existsUnique_polynomial_powLift_digit (tailShellPoly (c : ℤ))
    (q := q) (k := 2) ((c + g : ℕ) : ℤ) (Fact.out : Nat.Prime q) (by decide)
    (gtail_integer_square_support c g hT2) (gtail_integer_derivative_not_dvd c g hc hg hT2)
  have h' : ∃! t : Fin q, (q : ℤ) ^ 3 ∣ (tailShellPoly (c : ℤ)).eval
      (((c + g : ℕ) : ℤ) + (q : ℤ) ^ 2 * (t.val : ℤ)) := h
  simpa only [gtail_second_lift_predicate] using h'

/-- Existing k=2 integer lift criterion, transported to the native field readout. -/
theorem gtail_second_lift_iff_linear {q : ℕ} [Fact (Nat.Prime q)]
    (c g d : ℕ) (hT2 : q ^ 2 ∣ GTail 7 1 g c) :
    q ^ 3 ∣ GTail 7 1 (g + q ^ 2 * d) c ↔
      ((GTail 7 1 g c / q ^ 2 : ℕ) : ZMod q) + (d : ZMod q) *
        (tailShellPoly (c : ZMod q)).derivative.eval ((c + g : ℕ) : ZMod q) = 0 := by
  have h := polynomial_powLift_iff (tailShellPoly (c : ℤ)) (q := q) (k := 2)
    ((c + g : ℕ) : ℤ) (d : ℤ) (Fact.out : Nat.Prime q).pos (by decide)
    (gtail_integer_square_support c g hT2)
  have heq : (tailShellPoly (c : ℤ)).eval ((c + g : ℕ) : ℤ) / (q : ℤ) ^ 2 =
      ((GTail 7 1 g c / q ^ 2 : ℕ) : ℤ) := by
    rw [tailShellPoly_eval_nat, Int.natCast_ediv, Nat.cast_pow]
  calc
    q ^ 3 ∣ GTail 7 1 (g + q ^ 2 * d) c ↔
        (q : ℤ) ^ 3 ∣ (tailShellPoly (c : ℤ)).eval
          (((c + g : ℕ) : ℤ) + (q : ℤ) ^ 2 * (d : ℤ)) :=
      (gtail_second_lift_predicate q c g d).symm
    _ ↔ (q : ℤ) ∣ (tailShellPoly (c : ℤ)).eval ((c + g : ℕ) : ℤ) / (q : ℤ) ^ 2 +
        (d : ℤ) * (tailShellPoly (c : ℤ)).derivative.eval ((c + g : ℕ) : ℤ) := h
    _ ↔ _ := by
      rw [heq, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      change ((((GTail 7 1 g c / q ^ 2 : ℕ) : ℤ) +
        (d : ℤ) * gtailDerivativeInt c g : ℤ) : ZMod q) = 0 ↔ _
      simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, gtailDerivativeInt_cast]

/-- A second-level increment still preserves the gap residue unit. -/
theorem gtail_second_shift_gap_unit {q : ℕ} (g d : ℕ) (hg : ¬ q ∣ g) :
    ¬ q ∣ g + q ^ 2 * d := by
  simpa only [pow_two, mul_assoc] using gtail_shift_gap_unit g (q * d) hg

/-- The receiving canonical ratio is unchanged by a second-level increment. -/
theorem gtail_second_shift_ratio {q : ℕ} [Fact (Nat.Prime q)] (c g d : ℕ) :
    gtailSevenTailRatio q c (g + q ^ 2 * d) = gtailSevenTailRatio q c g := by
  simpa only [pow_two, mul_assoc] using gtail_shift_ratio c g (q * d)

/-- The finite-field derivative is unchanged by a second-level increment. -/
theorem gtail_second_shift_derivative {q : ℕ} (c g d : ℕ) :
    (tailShellPoly (c : ZMod q)).derivative.eval ((c + (g + q ^ 2 * d) : ℕ) : ZMod q) =
      (tailShellPoly (c : ZMod q)).derivative.eval ((c + g : ℕ) : ZMod q) := by
  simpa only [pow_two, mul_assoc] using gtail_shift_derivative c g (q * d)

end DkMath.FLT.Seven
