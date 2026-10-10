/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailCyclotomicTailDepthTwo
import Mathlib.Algebra.Polynomial.Derivative

#print "file: DkMath.FLT.Seven.GTailCyclotomicTailDerivative"

namespace DkMath.FLT.Seven

open DkMath.CosmicFormula DkMath.Lib.NumberTheory SevenCyclotomicDegreeSixInt
open Polynomial

/-- The degree-six homogeneous shell of the original depth-one GTail, with c held constant. -/
noncomputable def tailShellPoly {A : Type*} [CommRing A] (c : A) : Polynomial A :=
  ∑ j : Fin 7, X ^ (6 - j.val) * C (c ^ j.val)

theorem tailShellPoly_eval {A : Type*} [CommRing A] (c x : A) :
    (tailShellPoly c).eval x = ∑ j : Fin 7, x ^ (6 - j.val) * c ^ j.val := by
  simp [tailShellPoly, Polynomial.eval_finsetSum]

/-- Typed bridge to the original natural GTail, rather than a replacement polynomial. -/
theorem tailShellPoly_eval_nat {A : Type*} [CommRing A] (c g : ℕ) :
    (tailShellPoly (c : A)).eval ((c + g : ℕ) : A) = ((GTail 7 1 g c : ℕ) : A) := by
  rw [tailShellPoly_eval, GTail_seven_one_eq_homogeneous_sum]
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]

/-- Formal polynomial identity; no cancellation of a gap or of X minus c. -/
theorem tailShellPoly_mul {A : Type*} [CommRing A] (c : A) :
    (X - C c) * tailShellPoly c = X ^ 7 - C (c ^ 7) := by
  simp [tailShellPoly, Fin.sum_univ_succ, C_pow]
  ring

/-- Formal derivative in the shell variable X, keeping c constant. -/
theorem tailShellPoly_derivative_identity {A : Type*} [CommRing A] (c : A) :
    tailShellPoly c + (X - C c) * (tailShellPoly c).derivative = 7 * X ^ 6 := by
  have h := congrArg Polynomial.derivative (tailShellPoly_mul c)
  simpa [derivative_mul, derivative_pow, C_ofNat] using h

theorem tailShellPoly_derivative_at_zero {A : Type*} [CommRing A] (c x : A)
    (hx : (tailShellPoly c).eval x = 0) :
    (x - c) * (tailShellPoly c).derivative.eval x = 7 * x ^ 6 := by
  have h := congrArg (Polynomial.eval x) (tailShellPoly_derivative_identity c)
  simpa [hx] using h

/-- Specialization uses Tail divisibility only; division by g is deferred. -/
theorem gtail_shell_derivative_balance {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hT : q ∣ GTail 7 1 g c) :
    (g : ZMod q) * (tailShellPoly (c : ZMod q)).derivative.eval ((c + g : ℕ) : ZMod q) =
      7 * ((c + g : ℕ) : ZMod q) ^ 6 := by
  have hx : (tailShellPoly (c : ZMod q)).eval ((c + g : ℕ) : ZMod q) = 0 := by
    rw [tailShellPoly_eval_nat]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr hT
  simpa only [Nat.cast_add, add_sub_cancel_left] using
    tailShellPoly_derivative_at_zero (c : ZMod q) ((c + g : ℕ) : ZMod q) hx

/-- The formal shell derivative quotient requires only the gap unit and Tail support. -/
theorem gtail_shell_derivative_formula {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c) :
    (tailShellPoly (c : ZMod q)).derivative.eval ((c + g : ℕ) : ZMod q) =
      7 * ((c + g : ℕ) : ZMod q) ^ 6 / (g : ZMod q) := by
  have hg0 : (g : ZMod q) ≠ 0 := fun hz => hg ((ZMod.natCast_eq_zero_iff g q).mp hz)
  apply (eq_div_iff hg0).mpr
  simpa only [mul_comm] using gtail_shell_derivative_balance c g hT

private theorem homogeneous_product_certificate {A : Type*} [CommRing A] (z X Y : A)
    (h : 1 + z + z ^ 2 + z ^ 3 + z ^ 4 + z ^ 5 + z ^ 6 = 0) :
    (∏ i : Fin 6, (X - z ^ (i.val + 1) * Y)) =
      ∑ j : Fin 7, X ^ (6 - j.val) * Y ^ j.val := by
  simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ]
  norm_num
  linear_combination
    (z ^ 15 * Y ^ 6 - z ^ 14 * X * Y ^ 5 - z ^ 14 * Y ^ 6 +
      z ^ 12 * X ^ 2 * Y ^ 4 + z ^ 10 * X ^ 2 * Y ^ 4 - z ^ 9 * X ^ 3 * Y ^ 3 +
      z ^ 8 * X ^ 2 * Y ^ 4 + z ^ 8 * X * Y ^ 5 + z ^ 8 * Y ^ 6 -
      z ^ 7 * X ^ 3 * Y ^ 3 - z ^ 7 * X ^ 2 * Y ^ 4 - z ^ 7 * X * Y ^ 5 -
      z ^ 7 * Y ^ 6 - z ^ 6 * X ^ 3 * Y ^ 3 + z ^ 5 * X ^ 4 * Y ^ 2 +
      z ^ 3 * X ^ 4 * Y ^ 2 + z * X ^ 4 * Y ^ 2 + z * X ^ 3 * Y ^ 3 +
      z * X ^ 2 * Y ^ 4 + z * X * Y ^ 5 + z * Y ^ 6 - X ^ 5 * Y -
      X ^ 4 * Y ^ 2 - X ^ 3 * Y ^ 3 - X ^ 2 * Y ^ 4 - X * Y ^ 5 - Y ^ 6) * h

/-- A genuine polynomial factorization, obtained in the polynomial ring itself. -/
theorem tailShellPoly_eq_root_product {A : Type*} [CommRing A] (s c : A)
    (hs : 1 + s + s ^ 2 + s ^ 3 + s ^ 4 + s ^ 5 + s ^ 6 = 0) :
    tailShellPoly c = ∏ h : Fin 6, (X - C (s ^ (h.val + 1) * c)) := by
  have hC : 1 + C s + C s ^ 2 + C s ^ 3 + C s ^ 4 + C s ^ 5 + C s ^ 6 =
      (0 : Polynomial A) := by
    simpa only [C_add, C_pow, C_1, C_0] using congrArg (C : A → Polynomial A) hs
  simpa only [tailShellPoly, C_pow, C_mul] using
    (homogeneous_product_certificate (C s) X (C c) hC).symm

/-- Derivative at a zero linear factor is the evaluated product of the other factors. -/
theorem tailShellPoly_derivative_eq_erased_product {A : Type*} [CommRing A]
    (s c x : A) (hs : 1 + s + s ^ 2 + s ^ 3 + s ^ 4 + s ^ 5 + s ^ 6 = 0)
    (i : Fin 6) (hi : x - s ^ (i.val + 1) * c = 0) :
    (tailShellPoly c).derivative.eval x =
      ∏ h ∈ Finset.univ.erase i, (x - s ^ (h.val + 1) * c) := by
  rw [tailShellPoly_eq_root_product s c hs,
    ← Finset.prod_erase_mul Finset.univ
      (fun h : Fin 6 => (X - C (s ^ (h.val + 1) * c) : Polynomial A)) (Finset.mem_univ i)]
  simp only [derivative_mul, derivative_X_sub_C, eval_add, eval_mul, eval_sub,
    eval_X, eval_C, hi, mul_zero, mul_one, zero_add, eval_prod]

/-- The selected actual source cofactor is the formal derivative of the native Tail shell. -/
theorem eval_selected_cofactor_eq_tailShellPoly_derivative {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c)
    (i : Fin 6) :
    evalCyclotomicFromSeventhRoot
      (sixSlotRoot (gtailSevenTailRatio q c g) (sixInverseSlot i))
      (sixSlotRoot_ne_zero _ (gtailSevenTailRatio_ne_zero hc hT) _)
      (sixSlotRoot_pow_seven _ (gtailSevenTailRatio_pow_seven hc hT) _)
      (sixSlotRoot_ne_one _ (gtailSevenTailRatio_pow_seven hc hT)
        (gtailSevenTailRatio_ne_one hc hg) _) (gtailCyclotomicCofactor c g i) =
    (tailShellPoly (c : ZMod q)).derivative.eval ((c + g : ℕ) : ZMod q) := by
  let s := sixSlotRoot (gtailSevenTailRatio q c g) (sixInverseSlot i)
  have hs7 : s ^ 7 = 1 := sixSlotRoot_pow_seven _ (gtailSevenTailRatio_pow_seven hc hT) _
  have hs1 : s ≠ 1 := sixSlotRoot_ne_one _ (gtailSevenTailRatio_pow_seven hc hT)
    (gtailSevenTailRatio_ne_one hc hg) _
  have hs : 1 + s + s ^ 2 + s ^ 3 + s ^ 4 + s ^ 5 + s ^ 6 = 0 := by
    linear_combination seven_geom_sum_eq_zero_of_pow_eq_one s hs7 hs1
  have hi : ((c + g : ℕ) : ZMod q) - s ^ (i.val + 1) * (c : ZMod q) = 0 := by
    have hm := (gtailCyclotomicFactor_unique_slot c g hc hg hT i (sixInverseSlot i)).mpr rfl
    rw [mem_sixRootKernel_iff, evalCyclotomic_gtailFactor] at hm
    exact hm
  rw [tailShellPoly_derivative_eq_erased_product s (c : ZMod q) _ hs i hi]
  simp only [gtailCyclotomicCofactor, map_prod, evalCyclotomic_gtailFactor]
  rfl


/-- A nonidentity seventh root cannot occur in the characteristic-seven scalar field. -/
theorem nontrivial_seventh_root_prime_ne_seven {q : ℕ} (r : ZMod q)
    (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) : q ≠ 7 := by
  intro hq
  subst q
  have h : ∀ s : ZMod 7, s ^ 7 = s := by decide
  exact hr1 ((h r).symm.trans hr7)

/-- Canonical evaluation of the actual five-factor source cofactor. -/
def gtailSelectedCofactorResidue {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c)
    (i : Fin 6) : ZMod q :=
  evalCyclotomicFromSeventhRoot
    (sixSlotRoot (gtailSevenTailRatio q c g) (sixInverseSlot i))
    (sixSlotRoot_ne_zero _ (gtailSevenTailRatio_ne_zero hc hT) _)
    (sixSlotRoot_pow_seven _ (gtailSevenTailRatio_pow_seven hc hT) _)
    (sixSlotRoot_ne_one _ (gtailSevenTailRatio_pow_seven hc hT)
      (gtailSevenTailRatio_ne_one hc hg) _) (gtailCyclotomicCofactor c g i)

/-- The product derivative balance determines every selected actual cofactor residue. -/
theorem gtail_selected_cofactor_balance {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c)
    (i : Fin 6) :
    (g : ZMod q) * gtailSelectedCofactorResidue c g hc hg hT i =
      7 * ((c + g : ℕ) : ZMod q) ^ 6 := by
  rw [gtailSelectedCofactorResidue,
    eval_selected_cofactor_eq_tailShellPoly_derivative c g hc hg hT i]
  exact gtail_shell_derivative_balance c g hT

/-- Division is performed only after the nonzero gap residue has been proved. -/
theorem gtail_selected_cofactor_formula {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c)
    (i : Fin 6) :
    gtailSelectedCofactorResidue c g hc hg hT i =
      7 * ((c + g : ℕ) : ZMod q) ^ 6 / (g : ZMod q) := by
  have hg0 : (g : ZMod q) ≠ 0 := fun hz => hg ((ZMod.natCast_eq_zero_iff g q).mp hz)
  apply (eq_div_iff hg0).mpr
  simpa only [mul_comm] using gtail_selected_cofactor_balance c g hc hg hT i

/-- Uniformity is a field readout equality, independent of the factor index. -/
theorem gtail_selected_cofactor_uniform {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c)
    (i j : Fin 6) :
    gtailSelectedCofactorResidue c g hc hg hT i =
      gtailSelectedCofactorResidue c g hc hg hT j := by
  rw [gtail_selected_cofactor_formula, gtail_selected_cofactor_formula]

/-- Nonvanishing follows from the derivative formula and the explicit residue guards. -/
theorem gtail_selected_cofactor_ne_zero {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c)
    (i : Fin 6) : gtailSelectedCofactorResidue c g hc hg hT i ≠ 0 := by
  have hg0 : (g : ZMod q) ≠ 0 := fun hz => hg ((ZMod.natCast_eq_zero_iff g q).mp hz)
  have hc0 : (c : ZMod q) ≠ 0 := fun hz => hc ((ZMod.natCast_eq_zero_iff c q).mp hz)
  have hq7 : q ≠ 7 := nontrivial_seventh_root_prime_ne_seven (gtailSevenTailRatio q c g)
    (gtailSevenTailRatio_pow_seven hc hT) (gtailSevenTailRatio_ne_one hc hg)
  have h70 : (7 : ZMod q) ≠ 0 := by
    intro hz
    have hd : q ∣ 7 := (ZMod.natCast_eq_zero_iff 7 q).mp hz
    rcases (Nat.dvd_prime (by decide : Nat.Prime 7)).mp hd with h | h
    · exact (Fact.out : Nat.Prime q).ne_one h
    · exact hq7 h
  have he : ((c + g : ℕ) : ZMod q) = gtailSevenTailRatio q c g * (c : ZMod q) := by
    dsimp [gtailSevenTailRatio]
    push_cast
    exact (div_mul_cancel₀ _ hc0).symm
  have hx : ((c + g : ℕ) : ZMod q) ≠ 0 := by
    rw [he]
    exact mul_ne_zero (gtailSevenTailRatio_ne_zero hc hT) hc0
  rw [gtail_selected_cofactor_formula]
  exact div_ne_zero (mul_ne_zero h70 (pow_ne_zero _ hx)) hg0

end DkMath.FLT.Seven
