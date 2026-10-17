/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.RegularDescentState
import DkMath.Lib.NumberTheory.PrincipalIdealPower
import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits

#print "file: DkMath.FLT.Kummer.RegularDescentPowers"

/-!
# Coprime phase powers without a PID assumption

Primitive endpoints give pairwise coprime normalized factors. Ideal power
extraction and class-group p-torsion elimination then recover unit times powers.
The class-group argument explicitly checks that each ideal root is nonzero.
Integral closedness, available in a Dedekind domain, reflects divisibility of
p-th powers when removing the distinguished root's ramified depth.
-/

namespace DkMath.FLT.Kummer.RegularDescent

open DkMath.Lib.NumberTheory
open scoped BigOperators nonZeroDivisors

section Domain

variable {R : Type*} [CommRing R] [IsDomain R]
variable {p : ℕ} [hp : Fact p.Prime] {P : RamifiedPhasePacket R p}

/-- Differences of distinct slopes are units, uniformly in the prime degree. -/
theorem slope_sub_isUnit (P : RamifiedPhasePacket R p) {i j : Fin p} (hij : i ≠ j) :
    IsUnit (P.slope i - P.slope j) := by
  have hr (k : Fin p) : P.zeta ^ k.val ∈ Polynomial.nthRootsFinset p (1 : R) := by
    apply (Polynomial.mem_nthRootsFinset hp.out.pos 1).mpr
    rw [← pow_mul, Nat.mul_comm k.val p, pow_mul, P.primitive.pow_eq_one, one_pow]
  have hne : P.zeta ^ i.val ≠ P.zeta ^ j.val := by
    intro he
    exact hij (Fin.ext (P.primitive.pow_inj i.isLt j.isLt he))
  obtain ⟨u, hu⟩ := P.primitive.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime
    hp.out (hr i) (hr j) hne
  have he : P.slope i - P.slope j = -(u : R) := by
    apply mul_right_cancel₀ P.lambda_prime.ne_zero
    have hi := P.slope_spec i
    have hj := P.slope_spec j
    rw [P.lambda_eq] at hi hj ⊢
    linear_combination hi - hj - hu
  rw [he]
  exact u.isUnit.neg

/-- Original primitivity survives between every normalized factor and `y`. -/
theorem State.quotient_coprime_y {m : ℕ} (E : State P m) (hm : 1 ≤ m) (i : Fin p) :
    IsCoprime (P.quotient (E.center hm) E.y i) E.y := by
  have hc : IsCoprime (E.x + P.zeta ^ i.val * E.y) E.y := by
    simpa only [mul_comm] using E.coprime.add_mul_left_left (P.zeta ^ i.val)
  have hs : E.x + P.zeta ^ i.val * E.y = P.lambda * P.quotient (E.center hm) E.y i := by
    linear_combination P.quotient_spec (E.center hm) E.y i + E.center_spec hm
  rw [hs] at hc
  exact hc.of_mul_left_right

/-- Every two different normalized factors remain globally coprime. -/
theorem State.quotients_coprime {m : ℕ} (E : State P m) (hm : 1 ≤ m)
    {i j : Fin p} (hij : i ≠ j) :
    IsCoprime (P.quotient (E.center hm) E.y i) (P.quotient (E.center hm) E.y j) := by
  obtain ⟨t, ht⟩ := slope_sub_isUnit P hij
  have hy : E.y = (↑t⁻¹ : R) *
      (P.quotient (E.center hm) E.y i - P.quotient (E.center hm) E.y j) := by
    have he : P.quotient (E.center hm) E.y i - P.quotient (E.center hm) E.y j =
        (t : R) * E.y := by
      rw [ht]
      unfold RamifiedPhasePacket.quotient
      ring
    have htinv : (↑t⁻¹ : R) * (t : R) = 1 := t.inv_val
    rw [he, ← mul_assoc, htinv, one_mul]
  obtain ⟨a, b, hab⟩ := E.quotient_coprime_y hm i
  refine ⟨a + b * (↑t⁻¹ : R), -(b * (↑t⁻¹ : R)), ?_⟩
  have hab' : a * P.quotient (E.center hm) E.y i + b * ((↑t⁻¹ : R) *
      (P.quotient (E.center hm) E.y i - P.quotient (E.center hm) E.y j)) = 1 := by
    rw [← hy]
    exact hab
  linear_combination hab'

/-- Removing the `p` common ramified factors lowers the product depth by one. -/
theorem State.quotient_product (hodd : Odd p) {m : ℕ} (E : State P (m + 1)) :
    (∏ i : Fin p, P.quotient (E.center (by omega)) E.y i) =
      (E.epsilon : R) * (P.lambda ^ m * E.z) ^ p := by
  apply mul_left_cancel₀ (pow_ne_zero p P.lambda_prime.ne_zero)
  calc
    _ = E.x ^ p + E.y ^ p := (E.product_quotients hodd (by omega)).symm
    _ = _ := by rw [E.equation, pow_succ]; ring

end Domain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {p : ℕ} [hp : Fact p.Prime] {P : RamifiedPhasePacket R p}

/-- Each quotient generates a p-th-power ideal. -/
theorem State.quotient_ideal_power (hodd : Odd p) {m : ℕ} (E : State P (m + 1)) (i : Fin p) :
    ∃ I : Ideal R, Ideal.span ({P.quotient (E.center (by omega)) E.y i} : Set R) = I ^ p := by
  classical
  have hprod : (∏ j : Fin p, Ideal.span ({P.quotient (E.center (by omega)) E.y j} : Set R)) =
      Ideal.span ({P.lambda ^ m * E.z} : Set R) ^ p := by
    rw [Ideal.prod_span_singleton, E.quotient_product hodd,
      Ideal.span_singleton_mul_left_unit E.epsilon.isUnit, Ideal.span_singleton_pow]
  apply Finset.exists_eq_pow_of_mul_eq_pow_of_coprime (fun j _ k _ hjk => ?_)
    hprod i (Finset.mem_univ i)
  rw [Ideal.isCoprime_span_singleton_iff]
  exact E.quotients_coprime (by omega) hjk

/-- Class-group p-torsion-freeness suffices; no element UFD or PID is assumed. -/
theorem State.exists_quotient_roots (hodd : Odd p)
    (hfree : classGroupPTorsionFreeAt R p) {m : ℕ} (E : State P (m + 1)) :
    ∃ (u : Fin p → Rˣ) (b : Fin p → R),
      ∀ i, P.quotient (E.center (by omega)) E.y i = (u i : R) * b i ^ p := by
  classical
  have hz : E.z ≠ 0 := fun he => E.z_away (he ▸ dvd_zero P.lambda)
  have hprod : (∏ i : Fin p, P.quotient (E.center (by omega)) E.y i) ≠ 0 := by
    rw [E.quotient_product hodd]
    exact mul_ne_zero E.epsilon.isUnit.ne_zero
      (pow_ne_zero p (mul_ne_zero (pow_ne_zero m P.lambda_prime.ne_zero) hz))
  have hi (i : Fin p) : ∃ (u : Rˣ) (b : R),
      P.quotient (E.center (by omega)) E.y i = (u : R) * b ^ p := by
    obtain ⟨I, hI⟩ := E.quotient_ideal_power hodd i
    have hq : P.quotient (E.center (by omega)) E.y i ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i)
    have hI0 : I ∈ (Ideal R)⁰ := by
      rw [mem_nonZeroDivisors_iff_ne_zero]
      intro hzero
      have hh : Ideal.span ({P.quotient (E.center (by omega)) E.y i} : Set R) = ⊥ := by
        simpa [hzero, hp.out.ne_zero] using hI
      exact hq (Ideal.span_singleton_eq_bot.mp hh)
    obtain ⟨v, b, hv, _, he⟩ :=
      exists_unit_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt hI0 hfree hI
    exact ⟨hv.unit, b, by simpa only [IsUnit.unit_spec] using he⟩
  choose u b hb using hi
  exact ⟨u, b, hb⟩

/-- Remove precisely the ramified depth from the distinguished p-th root,
retaining the other roots and their coprimality. -/
theorem State.exists_descent_roots (hodd : Odd p)
    (hfree : classGroupPTorsionFreeAt R p) {m : ℕ} (E : State P (m + 1)) :
    ∃ (u : Fin p → Rˣ) (b : Fin p → R) (g : R),
      (∀ i, P.quotient (E.center (by omega)) E.y i = (u i : R) * b i ^ p) ∧
      P.quotient (E.center (by omega)) E.y (P.distinguished (E.center (by omega)) E.y) =
        (u (P.distinguished (E.center (by omega)) E.y) : R) * (P.lambda ^ m * g) ^ p ∧
      ¬ P.lambda ∣ g ∧
      (∀ i, i ≠ P.distinguished (E.center (by omega)) E.y → ¬ P.lambda ∣ b i) ∧
      (∀ i j, i ≠ j → IsCoprime (b i) (b j)) := by
  classical
  obtain ⟨u, b, hb⟩ := E.exists_quotient_roots hodd hfree
  let i0 := P.distinguished (E.center (by omega)) E.y
  let rest := ∏ i ∈ (Finset.univ.erase i0), P.quotient (E.center (by omega)) E.y i
  have hrest : ¬ P.lambda ∣ rest := by
    intro hd
    obtain ⟨i, hi, hd⟩ := (P.lambda_prime.dvd_finsetProd_iff _).mp hd
    exact (Finset.mem_erase.mp hi).1 ((P.quotient_dvd_iff _ _ E.y_away i).mp hd)
  have hprod : P.quotient (E.center (by omega)) E.y i0 * rest =
      (E.epsilon : R) * (P.lambda ^ m * E.z) ^ p := by
    rw [← E.quotient_product hodd]
    exact Finset.mul_prod_erase _ _ (Finset.mem_univ i0)
  have hdq : P.lambda ^ (m * p) ∣ P.quotient (E.center (by omega)) E.y i0 := by
    apply P.lambda_prime.pow_dvd_of_dvd_mul_right (m * p) hrest
    rw [hprod, mul_pow, ← pow_mul]
    exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
  rw [hb i0] at hdq
  have hdb : P.lambda ^ m ∣ b i0 := by
    have huinv : (↑((u i0)⁻¹) : R) * (u i0 : R) = 1 := (u i0).inv_val
    apply (IsIntegrallyClosed.pow_dvd_pow_iff hp.out.ne_zero).mp
    rw [← pow_mul]
    simpa only [← mul_assoc, huinv, one_mul] using
      dvd_mul_of_dvd_right hdq (↑((u i0)⁻¹) : R)
  obtain ⟨g, hg⟩ := hdb
  have hgfac : P.quotient (E.center (by omega)) E.y i0 =
      (u i0 : R) * (P.lambda ^ m * g) ^ p := by rw [hb i0, hg]
  have hcancel : (u i0 : R) * g ^ p * rest = (E.epsilon : R) * E.z ^ p := by
    apply mul_left_cancel₀ (pow_ne_zero (m * p) P.lambda_prime.ne_zero)
    calc
      _ = P.quotient (E.center (by omega)) E.y i0 * rest := by rw [hgfac]; ring
      _ = _ := by rw [hprod]; ring
  have hga : ¬ P.lambda ∣ g := by
    intro hd
    have hz := congrArg P.residue hcancel
    have hg0 := (P.residue_zero_iff _).mpr hd
    simp only [map_mul, map_pow, hg0, zero_pow hp.out.ne_zero, mul_zero, zero_mul] at hz
    have hzpow : P.residue E.z ^ p = 0 :=
      (mul_eq_zero.mp hz.symm).resolve_left (E.epsilon.isUnit.map P.residue).ne_zero
    exact E.z_away ((P.residue_zero_iff _).mp (eq_zero_of_pow_eq_zero hzpow))
  have haway : ∀ i, i ≠ i0 → ¬ P.lambda ∣ b i := by
    intro i hi hd
    have hqi : P.lambda ∣ P.quotient (E.center (by omega)) E.y i := by
      rw [hb i]
      exact dvd_mul_of_dvd_right (hd.trans (dvd_pow_self _ hp.out.ne_zero)) _
    exact hi ((P.quotient_dvd_iff _ _ E.y_away i).mp hqi)
  have hbcop : ∀ i j, i ≠ j → IsCoprime (b i) (b j) := by
    intro i j hij
    apply IsCoprime.mono _ _ (E.quotients_coprime (by omega) hij)
    · rw [hb i]; exact dvd_mul_of_dvd_right (dvd_pow_self _ hp.out.ne_zero) _
    · rw [hb j]; exact dvd_mul_of_dvd_right (dvd_pow_self _ hp.out.ne_zero) _
  exact ⟨u, b, g, hb, hgfac, hga, haway, hbcop⟩

end DkMath.FLT.Kummer.RegularDescent
