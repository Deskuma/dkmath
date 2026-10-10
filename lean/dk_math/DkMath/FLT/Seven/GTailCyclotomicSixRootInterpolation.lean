/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailCyclotomicSixRootOrbit

#print "file: DkMath.FLT.Seven.GTailCyclotomicSixRootInterpolation"

namespace DkMath.FLT.Seven

open DkMath.Lib.NumberTheory SevenCyclotomicDegreeSixInt

/-- Integral change from the existing six coordinates to the power coefficients. -/
def sixPowerCoefficients {A : Type*} [CommRing A] (v : Fin 6 → A) : Fin 6 → A :=
  ![v 0 + v 2 + v 4 + v 5, v 3 + v 4 + 2 * v 5,
    -v 1 - v 2 + v 4 + v 5, -v 1 - 2 * v 2,
    -v 1 - 2 * v 2 - v 5, -v 1 - v 2 - v 5]

/-- The explicit integral inverse, valid without characteristic restrictions. -/
def sixPowerCoordinates {A : Type*} [CommRing A] (w : Fin 6 → A) : Fin 6 → A :=
  ![w 0 - w 2 + w 3, -w 3 + 2 * w 4 - 2 * w 5, -w 4 + w 5,
    w 1 - w 2 + w 5, w 2 - 2 * w 3 + 2 * w 4 - w 5, w 3 - w 4]

theorem sixPowerCoordinates_coefficients {A : Type*} [CommRing A] (v : Fin 6 → A) :
    sixPowerCoordinates (sixPowerCoefficients v) = v := by
  funext i
  fin_cases i <;> simp [sixPowerCoordinates, sixPowerCoefficients] <;> ring

theorem sixPowerCoefficients_coordinates {A : Type*} [CommRing A] (w : Fin 6 → A) :
    sixPowerCoefficients (sixPowerCoordinates w) = w := by
  funext i
  fin_cases i <;> simp [sixPowerCoordinates, sixPowerCoefficients] <;> ring

theorem sixPowerCoefficients_intCast (q : ℕ) (v : Fin 6 → ℤ) (i : Fin 6) :
    ((sixPowerCoefficients v i : ℤ) : ZMod q) =
      sixPowerCoefficients (fun j => (v j : ZMod q)) i := by
  fin_cases i <;> simp [sixPowerCoefficients, Int.cast_add, Int.cast_sub, Int.cast_mul]

/-- The degree-at-most-five polynomial associated with the actual integral carrier. -/
noncomputable def sixPowerPolynomial (q : ℕ) (z : SevenCyclotomicDegreeSixInt.Ring) : Polynomial (ZMod q) :=
  ∑ j : Fin 6, Polynomial.monomial j.val ((sixPowerCoefficients (coordinates z) j : ℤ) : ZMod q)

theorem sixPowerPolynomial_coeff (q : ℕ) (z : SevenCyclotomicDegreeSixInt.Ring) (j : Fin 6) :
    (sixPowerPolynomial q z).coeff j.val = ((sixPowerCoefficients (coordinates z) j : ℤ) : ZMod q) := by
  classical
  simp only [sixPowerPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  simp only [Fin.val_inj]
  simp

theorem sixPowerPolynomial_natDegree_le (q : ℕ) (z : SevenCyclotomicDegreeSixInt.Ring) :
    (sixPowerPolynomial q z).natDegree ≤ 5 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_monomial_le _).trans (by omega)

/-- Verified value identity for arbitrary signed coordinates in the existing degree-six ring. -/
theorem evalCyclotomic_eq_sixPowerPolynomial {q : ℕ} [Fact (Nat.Prime q)]
    (s : ZMod q) (hs0 : s ≠ 0) (hs7 : s ^ 7 = 1) (hs1 : s ≠ 1)
    (z : SevenCyclotomicDegreeSixInt.Ring) :
    evalCyclotomicFromSeventhRoot s hs0 hs7 hs1 z = (sixPowerPolynomial q z).eval s := by
  have hi : s⁻¹ = s ^ 6 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', hs7]
  have hsum := seven_geom_sum_eq_zero_of_pow_eq_one s hs7 hs1
  simp [evalCyclotomicFromSeventhRoot, evalRealFromSeventhRoot, seventhRootBeta, hi,
    sixPowerPolynomial, Fin.sum_univ_succ, Polynomial.eval_monomial,
    sixPowerCoefficients, coordinates, Int.cast_add, Int.cast_sub, Int.cast_mul]
  linear_combination
    (s ^ 6 * (z.im.thd : ZMod q) + s ^ 5 * (z.re.thd : ZMod q) +
      2 * s * (z.im.thd : ZMod q) + 2 * (z.re.thd : ZMod q) +
      (z.im.snd : ZMod q) + 2 * (z.im.thd : ZMod q)) * hs7 +
    ((z.re.snd : ZMod q) + 2 * (z.re.thd : ZMod q) + (z.im.thd : ZMod q)) * hsum

/-- Vanishing at the six distinct slots forces all original integral residues to vanish. -/
theorem mem_all_sixRootKernel_iff_coordinates_zero {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1)
    (z : SevenCyclotomicDegreeSixInt.Ring) :
    (∀ i : Fin 6, z ∈ sixRootKernel r hr0 hr7 hr1 i) ↔
      ∀ j : Fin 6, (coordinates z j : ZMod q) = 0 := by
  constructor
  · intro h
    have hp : sixPowerPolynomial q z = 0 :=
      Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _
        (sixSlotRoot_injective r hr7 hr1)
        (fun i => by
          rw [← evalCyclotomic_eq_sixPowerPolynomial]
          exact (mem_sixRootKernel_iff r hr0 hr7 hr1 i z).mp (h i))
        (by have hd := sixPowerPolynomial_natDegree_le q z; simpa using Nat.lt_succ_of_le hd)
    have hw (j : Fin 6) : ((sixPowerCoefficients (coordinates z) j : ℤ) : ZMod q) = 0 := by
      rw [← sixPowerPolynomial_coeff, hp, Polynomial.coeff_zero]
    have hv : sixPowerCoefficients (fun j => (coordinates z j : ZMod q)) = 0 := by
      funext j
      rw [← sixPowerCoefficients_intCast, hw]
      rfl
    have hinv := sixPowerCoordinates_coefficients (fun j => (coordinates z j : ZMod q))
    rw [hv] at hinv
    intro j
    rw [← congrFun hinv j]
    fin_cases j <;> simp [sixPowerCoordinates]
  · intro h i
    rw [mem_sixRootKernel_iff, evalCyclotomic_eq_sixPowerPolynomial]
    have hw (j : Fin 6) : ((sixPowerCoefficients (coordinates z) j : ℤ) : ZMod q) = 0 := by
      rw [sixPowerCoefficients_intCast]
      simp only [show (fun j => (coordinates z j : ZMod q)) = 0 from funext h]
      fin_cases j <;> simp [sixPowerCoefficients]
    simp [sixPowerPolynomial, hw]

/-- The principal scalar ideal in the degree-six source, distinct from integer contraction. -/
def cyclotomicScalarIdeal (q : ℕ) : Ideal SevenCyclotomicDegreeSixInt.Ring :=
  Ideal.span ({(q : SevenCyclotomicDegreeSixInt.Ring)} : Set SevenCyclotomicDegreeSixInt.Ring)

/-- The additive coordinate equivalence respects multiplication by integer scalars. -/
theorem coordinates_natCast_mul (q : ℕ) (z : SevenCyclotomicDegreeSixInt.Ring) (j : Fin 6) :
    coordinates ((q : SevenCyclotomicDegreeSixInt.Ring) * z) j = (q : ℤ) * coordinates z j := by
  fin_cases j <;> simp [coordinates, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
    SevenRealCubicInt.fst_mul, SevenRealCubicInt.snd_mul, SevenRealCubicInt.thd_mul]

/-- Coordinate-wise integer quotients give an actual scalar divisor in the degree-six ring. -/
theorem mem_cyclotomicScalarIdeal_iff (q : ℕ) (z : SevenCyclotomicDegreeSixInt.Ring) :
    z ∈ cyclotomicScalarIdeal q ↔ ∀ j : Fin 6, (q : ℤ) ∣ coordinates z j := by
  rw [cyclotomicScalarIdeal, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨w, hw⟩ j
    refine ⟨coordinates w j, ?_⟩
    rw [hw, coordinates_natCast_mul]
  · intro h
    choose v hv using h
    refine ⟨coordinates.symm v, ?_⟩
    apply coordinates.injective
    funext j
    rw [coordinates_natCast_mul, coordinates.apply_symm_apply]
    exact hv j

/-- Exact recovery of the scalar principal ideal from all six distinct residue kernels. -/
theorem iInf_sixRootKernel_eq_scalarIdeal {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    (⨅ i : Fin 6, sixRootKernel r hr0 hr7 hr1 i) = cyclotomicScalarIdeal q := by
  ext z
  rw [Ideal.mem_iInf, mem_all_sixRootKernel_iff_coordinates_zero, mem_cyclotomicScalarIdeal_iff]
  simp only [ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- After exact intersection recovery, finite comaximality gives the conditional splitting product. -/
theorem prod_sixRootKernel_eq_scalarIdeal {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    (∏ i : Fin 6, sixRootKernel r hr0 hr7 hr1 i) = cyclotomicScalarIdeal q := by
  have h := Ideal.prod_eq_iInf_of_pairwise_isCoprime
    (s := Finset.univ) (J := sixRootKernel r hr0 hr7 hr1)
    (by
      intro i _ j _ hij
      exact Ideal.isCoprime_iff_sup_eq.mpr (sixRootKernel_sup_eq_top r hr0 hr7 hr1 i j hij))
  simpa only [Finset.mem_univ, iInf_true] using
    h.trans (by simpa using iInf_sixRootKernel_eq_scalarIdeal r hr0 hr7 hr1)

end DkMath.FLT.Seven
