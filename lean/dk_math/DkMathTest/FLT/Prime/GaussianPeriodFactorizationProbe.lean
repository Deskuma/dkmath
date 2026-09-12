/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.QuadraticConjugateFactor
import DkMath.NumberTheory.TraceOneDiscriminantAxis

#print "file: DkMathTest.FLT.Prime.GaussianPeriodFactorizationProbe"

namespace DkMathTest.FLT.Prime

open scoped BigOperators

open DkMath.NumberTheory.QuadraticConjugateFactor
open DkMath.NumberTheory.TraceOneQuadratic

/-! ## Part A: the neutral factor-to-norm connection -/

theorem traceOne_norm_from_conjugate_form
    {s A U V C R D S : ℤ}
    (hR : R = U + V)
    (hC : C = U * V)
    (hDiff : (U - V) ^ 2 = D * S ^ 2)
    (hD : discr s = D)
    (hTrace : R = 2 * A + S) :
    norm (⟨A, S⟩ : TraceOneInt s) = C := by
  apply norm_eq_of_gauss_coordinates hTrace
  exact four_mul_product_eq_sum_sq_sub_discriminant_mul hR hC hDiff hD

/-! ## Part B: a bounded signed-prime discriminant representation -/

/-- The sign convention determined by the prime residue class modulo four. -/
def signedPrimeDiscriminant (p : ℕ) : ℤ :=
  if p % 4 = 1 then (p : ℤ) else -(p : ℤ)

theorem signedPrimeDiscriminant_eq_or_neg (p : ℕ) :
    signedPrimeDiscriminant p = (p : ℤ) ∨
      signedPrimeDiscriminant p = -(p : ℤ) := by
  by_cases h : p % 4 = 1 <;> simp [signedPrimeDiscriminant, h]

theorem signedPrimeDiscriminant_natAbs (p : ℕ) :
    Int.natAbs (signedPrimeDiscriminant p) = p := by
  by_cases h : p % 4 = 1 <;> simp [signedPrimeDiscriminant, h]

theorem signedPrimeDiscriminant_mod_four
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    signedPrimeDiscriminant p % 4 = 1 := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hcases : p % 4 = 1 ∨ p % 4 = 3 := by
    rcases hodd with ⟨k, hk⟩
    omega
  rcases hcases with h | h
  · rw [signedPrimeDiscriminant, if_pos h]
    exact_mod_cast h
  · have hpmod : (p : ℤ) % 4 = 3 := by
      exact_mod_cast h
    have hpnot : ¬(4 : ℤ) ∣ (p : ℤ) := by
      intro hdiv
      have hz : (p : ℤ) % 4 = 0 := Int.emod_eq_zero_of_dvd hdiv
      omega
    rw [signedPrimeDiscriminant, if_neg (by omega), Int.neg_emod]
    simp [hpnot, hpmod]

def signedPrimeParameter (p : ℕ) : ℤ :=
  (signedPrimeDiscriminant p - 1) / 4

theorem discr_signedPrimeParameter
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    discr (signedPrimeParameter p) = signedPrimeDiscriminant p := by
  have hmod := signedPrimeDiscriminant_mod_four hp hp2
  have hdecomp := Int.mul_ediv_add_emod (signedPrimeDiscriminant p - 1) 4
  simp only [signedPrimeParameter, discr]
  omega

/-! The bounded sign convention agrees with the existing small-prime samples. -/

example : signedPrimeDiscriminant 3 = -3 := by
  norm_num [signedPrimeDiscriminant]

example : signedPrimeDiscriminant 5 = 5 := by
  norm_num [signedPrimeDiscriminant]

example : signedPrimeDiscriminant 7 = -7 := by
  norm_num [signedPrimeDiscriminant]

example : signedPrimeDiscriminant 11 = -11 := by
  norm_num [signedPrimeDiscriminant]

example : signedPrimeDiscriminant 13 = 13 := by
  norm_num [signedPrimeDiscriminant]

example : discr (signedPrimeParameter 3) = -3 := by
  exact discr_signedPrimeParameter (by norm_num) (by norm_num)

example : discr (signedPrimeParameter 5) = 5 := by
  exact discr_signedPrimeParameter (by norm_num) (by norm_num)

example : discr (signedPrimeParameter 7) = -7 := by
  exact discr_signedPrimeParameter (by norm_num) (by norm_num)

example : discr (signedPrimeParameter 11) = -11 := by
  exact discr_signedPrimeParameter (by norm_num) (by norm_num)

example : discr (signedPrimeParameter 13) = 13 := by
  exact discr_signedPrimeParameter (by norm_num) (by norm_num)

/-! ## Part C1/C2: a finite QR/QNR split and product recombination -/

def nonzeroResidues (p : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  Finset.univ.erase 0

def qrFinset (p : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  (nonzeroResidues p).filter IsSquare

def qnrFinset (p : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  (nonzeroResidues p).filter (fun a => ¬IsSquare a)

theorem qr_qnr_disjoint (p : ℕ) [Fact p.Prime] :
    Disjoint (qrFinset p) (qnrFinset p) := by
  classical
  rw [Finset.disjoint_left]
  intro a ha hb
  exact (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp ha).2

theorem qr_qnr_union (p : ℕ) [Fact p.Prime] :
    qrFinset p ∪ qnrFinset p = nonzeroResidues p := by
  classical
  ext a
  by_cases ha : a = 0
  · simp [qrFinset, qnrFinset, nonzeroResidues, ha]
  · have hchar := quadraticChar_dichotomy (F := ZMod p) ha
    rcases hchar with hchar | hchar
    · have hsquare : IsSquare a :=
        (quadraticChar_one_iff_isSquare ha).mp hchar
      simp [qrFinset, qnrFinset, hsquare]
    · have hnonsquare : ¬IsSquare a :=
        (quadraticChar_neg_one_iff_not_isSquare).mp hchar
      simp [qrFinset, qnrFinset, hnonsquare]

theorem qr_card_add_qnr_card (p : ℕ) [Fact p.Prime] :
    (qrFinset p).card + (qnrFinset p).card = p - 1 := by
  calc
    (qrFinset p).card + (qnrFinset p).card =
        (qrFinset p ∪ qnrFinset p).card :=
      (Finset.card_union_of_disjoint (qr_qnr_disjoint p)).symm
    _ = (nonzeroResidues p).card := by rw [qr_qnr_union p]
    _ = p - 1 := by simp [nonzeroResidues, ZMod.card]

theorem qr_card_eq_half (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    (qrFinset p).card = (p - 1) / 2 := by
  classical
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  have hsum : ∑ a : ZMod p, quadraticChar (ZMod p) a = 0 :=
    quadraticChar_sum_zero hchar
  have hsplit_zero :=
    Finset.add_sum_erase (Finset.univ : Finset (ZMod p))
      (fun a => quadraticChar (ZMod p) a) (Finset.mem_univ 0)
  rw [quadraticChar_zero, hsum] at hsplit_zero
  have hsum_nonzero :
      (nonzeroResidues p).sum (quadraticChar (ZMod p)) = 0 := by
    simpa [nonzeroResidues] using hsplit_zero
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not (nonzeroResidues p)
      (fun a : ZMod p => IsSquare a) (quadraticChar (ZMod p))
  have hsplit' :
      (qrFinset p).sum (quadraticChar (ZMod p)) +
          (qnrFinset p).sum (quadraticChar (ZMod p)) =
        (nonzeroResidues p).sum (quadraticChar (ZMod p)) := by
    simpa [qrFinset, qnrFinset] using hsplit
  have hqr_sum :
      (qrFinset p).sum (quadraticChar (ZMod p)) = (qrFinset p).card := by
    calc
      (qrFinset p).sum (quadraticChar (ZMod p)) =
          (qrFinset p).sum (fun _ => (1 : ℤ)) := by
        apply Finset.sum_congr rfl
        intro a ha
        have ha0 : a ≠ 0 :=
          (Finset.mem_erase.mp (Finset.mem_filter.mp ha).1).1
        exact (quadraticChar_one_iff_isSquare ha0).mpr
          (Finset.mem_filter.mp ha).2
      _ = (qrFinset p).card := by simp
  have hqnr_sum :
      (qnrFinset p).sum (quadraticChar (ZMod p)) =
        -((qnrFinset p).card : ℤ) := by
    calc
      (qnrFinset p).sum (quadraticChar (ZMod p)) =
          (qnrFinset p).sum (fun _ => (-1 : ℤ)) := by
        apply Finset.sum_congr rfl
        intro a ha
        exact (quadraticChar_neg_one_iff_not_isSquare).mpr
          (Finset.mem_filter.mp ha).2
      _ = -((qnrFinset p).card : ℤ) := by simp
  rw [hqr_sum, hqnr_sum, hsum_nonzero] at hsplit'
  have hsum_cards :
      (qrFinset p).card = (qnrFinset p).card := by
    have hsum_cards' :
        (qrFinset p).card + -((qnrFinset p).card : ℤ) = 0 := by
      exact hsplit'
    have hcards_int :
        ((qrFinset p).card : ℤ) = ((qnrFinset p).card : ℤ) := by
      linarith [hsum_cards']
    exact_mod_cast hcards_int
  have hcard_sum := qr_card_add_qnr_card p
  omega

theorem qnr_card_eq_half (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    (qnrFinset p).card = (p - 1) / 2 := by
  have hp : p.Prime := Fact.out
  have hpmod : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr hp2
  have hqr := qr_card_eq_half p hp2
  have hsum := qr_card_add_qnr_card p
  omega

theorem qr_product_mul_qnr_product
    {R : Type*} [CommMonoid R]
    (p : ℕ) [Fact p.Prime] (f : ZMod p → R) :
    (qrFinset p).prod f * (qnrFinset p).prod f =
      (nonzeroResidues p).prod f := by
  rw [← Finset.prod_union (qr_qnr_disjoint p), qr_qnr_union p]

/-! The shell and Galois/coefficient-descent stages are intentionally not
defined here: the preceding theorem is only the abstract finite-product
recombination required at C2. -/

#print axioms traceOne_norm_from_conjugate_form
#print axioms signedPrimeDiscriminant_mod_four
#print axioms discr_signedPrimeParameter
#print axioms qr_product_mul_qnr_product

end DkMathTest.FLT.Prime
