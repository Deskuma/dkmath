/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.GNDegreeFactorization
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Algebra.Polynomial.Taylor

#print "file: DkMath.NumberTheory.GapFocusing.Degree"

/-!
# Degree routes of the focused GN kernel

The universal composition identity gives routes indexed by degree factors.
The integral polynomial at boundary `u = 1` retains the divisor layers as
translated cyclotomic factors. Its irreducibility is exactly prime degree.
This statement concerns the polynomial over `ℤ`, not each evaluated GN value
or arbitrary coefficient rings.

The `2p` identities below are valid over every commutative semiring and require
no primality hypothesis. They describe composition of power maps, without an
additional geometric object map.
-/

open scoped BigOperators

namespace DkMath.NumberTheory.GapFocusing

open Polynomial
open DkMath.CosmicFormula

/-- The focused polynomial on the unit boundary. -/
noncomputable def kernelPolynomial (d : ℕ) : ℤ[X] := GN d X 1

/-- The focused integral polynomial is a translated geometric sum. -/
theorem kernelPolynomial_eq_geom_sum (d : ℕ) :
    kernelPolynomial d = ∑ i ∈ Finset.range d, (X + 1 : ℤ[X]) ^ i := by
  apply mul_left_cancel₀ (X_ne_zero (R := ℤ))
  have hGN := add_pow_eq_mul_GTail_one_add_gap d (X : ℤ[X]) 1
  have hgeom := geom_sum_mul (X + 1 : ℤ[X]) d
  change X * GTail d 1 (X : ℤ[X]) 1 =
    X * (∑ i ∈ Finset.range d, (X + 1 : ℤ[X]) ^ i)
  calc
    _ = (X + 1 : ℤ[X]) ^ d - 1 := by
      apply eq_sub_iff_add_eq.mpr
      simpa only [one_pow] using hGN.symm
    _ = _ := by
      simpa only [add_sub_cancel_right, mul_comm] using hgeom.symm

/-- Each nontrivial divisor is retained as a translated cyclotomic layer. -/
theorem kernelPolynomial_eq_prod_cyclotomic {d : ℕ} (hd : 0 < d) :
    kernelPolynomial d =
      ∏ k ∈ d.divisors.erase 1, (cyclotomic k ℤ).comp (X + 1) := by
  rw [kernelPolynomial_eq_geom_sum]
  have h := congrArg (fun P : ℤ[X] => P.comp (X + 1))
    (prod_cyclotomic_eq_geom_sum hd ℤ)
  simpa only [prod_comp, sum_comp, pow_comp, X_comp] using h.symm

/-- The translated divisor layers preserve monicity. -/
theorem kernelPolynomial_monic {d : ℕ} (hd : 0 < d) :
    (kernelPolynomial d).Monic := by
  rw [kernelPolynomial_eq_prod_cyclotomic hd]
  apply monic_prod_of_monic
  intro k _
  simpa only [C_1] using (cyclotomic.monic k ℤ).comp_X_add_C 1

/-- Extension of coefficients gives the same focused polynomial over `ℚ`. -/
theorem kernelPolynomial_map_rat (d : ℕ) :
    (kernelPolynomial d).map (Int.castRingHom ℚ) = GN d (X : ℚ[X]) 1 := by
  have h := map_GN (Polynomial.mapRingHom (Int.castRingHom ℚ)) d (X : ℤ[X]) 1
  change (GTail d 1 (X : ℤ[X]) 1).map (Int.castRingHom ℚ) =
    GTail d 1 ((X : ℤ[X]).map (Int.castRingHom ℚ))
      ((1 : ℤ[X]).map (Int.castRingHom ℚ)) at h
  simpa only [kernelPolynomial, Polynomial.map_X, Polynomial.map_one] using h

/-- A nontrivial degree divisor yields an actual polynomial divisor layer. -/
theorem cyclotomic_layer_dvd_kernelPolynomial {k d : ℕ}
    (hkd : k ∣ d) (hk : k ≠ 1) :
    (cyclotomic k ℤ).comp (X + 1) ∣ kernelPolynomial d := by
  rw [kernelPolynomial_eq_geom_sum]
  have h := cyclotomic_dvd_geom_sum_of_dvd ℤ hkd hk
  rcases h with ⟨Q, hQ⟩
  refine ⟨Q.comp (X + 1), ?_⟩
  have h' := congrArg (fun P : ℤ[X] => P.comp (X + 1)) hQ
  simpa only [sum_comp, pow_comp, X_comp, mul_comp] using h'

/-- At prime degree the divisor product has exactly one residual layer. -/
theorem kernelPolynomial_prime {p : ℕ} (hp : Nat.Prime p) :
    kernelPolynomial p = (cyclotomic p ℤ).comp (X + 1) := by
  let : Fact (Nat.Prime p) := ⟨hp⟩
  rw [kernelPolynomial_eq_geom_sum, cyclotomic_prime]
  simp only [sum_comp, pow_comp, X_comp]

/-- The constant coefficient remembers the degree on the unit boundary. -/
theorem kernelPolynomial_eval_zero (d : ℕ) :
    (kernelPolynomial d).eval 0 = (d : ℤ) := by
  rw [kernelPolynomial_eq_geom_sum]
  simp only [eval_finsetSum, eval_pow, eval_add, eval_X, eval_one,
    zero_add, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

private theorem kernelPolynomial_not_isUnit {d : ℕ} (hd : 2 ≤ d) :
    ¬ IsUnit (kernelPolynomial d) := by
  intro h
  have h' := h.map (evalRingHom (0 : ℤ))
  change IsUnit ((kernelPolynomial d).eval 0) at h'
  rw [kernelPolynomial_eval_zero, Int.isUnit_iff] at h'
  rcases h' with h' | h' <;> omega

/-- Composite routes have two nonunit integral polynomial factors. -/
theorem kernelPolynomial_nonunit_factors {a b : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ¬ IsUnit (kernelPolynomial a) ∧
      ¬ IsUnit (GN b (X * kernelPolynomial a) (1 : ℤ[X])) := by
  refine ⟨kernelPolynomial_not_isUnit ha, ?_⟩
  intro h
  have h' := h.map (evalRingHom (0 : ℤ))
  have heval :
      (GN b (X * kernelPolynomial a) (1 : ℤ[X])).eval 0 = (b : ℤ) := by
    change (evalRingHom (0 : ℤ)) (GN b (X * kernelPolynomial a) (1 : ℤ[X])) = _
    rw [map_GN]
    simp only [map_mul, coe_evalRingHom, eval_X, zero_mul, eval_one]
    rw [GN_zero_eval]
    simp only [Nat.choose_one_right, one_pow, mul_one]
  change IsUnit ((GN b (X * kernelPolynomial a) (1 : ℤ[X])).eval 0) at h'
  rw [heval, Int.isUnit_iff] at h'
  rcases h' with h' | h' <;> omega

/-- Universal degree composition specializes to integral polynomial factors. -/
theorem kernelPolynomial_mul_degree (a b : ℕ) :
    kernelPolynomial (a * b) =
      kernelPolynomial a * GN b (X * kernelPolynomial a) (1 : ℤ[X]) := by
  simpa only [kernelPolynomial, one_pow] using
    (DkMath.CosmicFormula.GN_mul_degree a b (X : ℤ[X]) 1)

/-- Composite degree produces a genuine reducible integral polynomial. -/
theorem kernelPolynomial_not_irreducible_mul_degree {a b : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ¬ Irreducible (kernelPolynomial (a * b)) := by
  intro h
  have hf := h.isUnit_or_isUnit (kernelPolynomial_mul_degree a b)
  exact hf.elim (kernelPolynomial_nonunit_factors ha hb).1
    (kernelPolynomial_nonunit_factors ha hb).2

/-- Prime degree is characterized by irreducibility of the focused polynomial
on the unit boundary over `ℤ`. This is stronger than merely excluding degree
factorizations, and does not assert primality of its integer evaluations. -/
theorem kernelPolynomial_irreducible_iff_prime {d : ℕ} (hd : 2 ≤ d) :
    Irreducible (kernelPolynomial d) ↔ Nat.Prime d := by
  constructor
  · intro h
    by_contra hnp
    rcases (Nat.not_prime_iff_exists_mul_eq hd).mp hnp with
      ⟨a, b, ha, hb, hab⟩
    have ha2 : 2 ≤ a := by nlinarith
    have hb2 : 2 ≤ b := by nlinarith
    rw [← hab] at h
    exact kernelPolynomial_not_irreducible_mul_degree ha2 hb2 h
  · intro hp
    rw [kernelPolynomial_prime hp]
    have h := (cyclotomic.irreducible hp.pos).map
      (taylorEquiv (1 : ℤ)).toRingEquiv.toMulEquiv
    change Irreducible (taylor 1 (cyclotomic d ℤ)) at h
    simpa only [taylor_apply, C_1] using h

/-- The polynomial rigidity criterion also holds over `ℚ`, by Gauss's lemma. -/
theorem GN_polynomial_rat_irreducible_iff_prime {d : ℕ} (hd : 2 ≤ d) :
    Irreducible (GN d (X : ℚ[X]) 1) ↔ Nat.Prime d := by
  rw [← kernelPolynomial_map_rat]
  rw [← Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    (kernelPolynomial_monic (by omega : 0 < d)).isPrimitive]
  exact kernelPolynomial_irreducible_iff_prime hd

/-- Degree two is the explicit linear tail. -/
theorem GN_two {R : Type*} [CommSemiring R] (x u : R) :
    GN 2 x u = x + 2 * u := by
  simp [GN, GTail, Finset.sum_range_succ]
  ring

/-- `p` then `2`: the second factor is the sum of the two `p`th powers. -/
theorem GN_two_mul_degree_p_then_two {R : Type*} [CommSemiring R]
    (p : ℕ) (x u : R) :
    GN (2 * p) x u = GN p x u * ((x + u) ^ p + u ^ p) := by
  have hcomp := DkMath.CosmicFormula.GN_mul_degree p 2 x u
  change GN (p * 2) x u = GN p x u * GN 2 (x * GN p x u) (u ^ p) at hcomp
  rw [Nat.mul_comm p 2, GN_two] at hcomp
  rw [hcomp]
  congr 1
  rw [add_pow_eq_mul_GTail_one_add_gap]
  ring

/-- `2` then `p`: the quadratic gap and boundary feed the `p`th kernel. -/
theorem GN_two_mul_degree_two_then_p {R : Type*} [CommSemiring R]
    (p : ℕ) (x u : R) :
    GN (2 * p) x u =
      (x + 2 * u) * GN p (x * (x + 2 * u)) (u ^ 2) := by
  have hcomp := DkMath.CosmicFormula.GN_mul_degree 2 p x u
  change GN (2 * p) x u = GN 2 x u * GN p (x * GN 2 x u) (u ^ 2) at hcomp
  simpa only [GN_two] using hcomp

/-- The two composition orders agree as products, with distinct inner inputs. -/
theorem GN_two_mul_degree_orders {R : Type*} [CommSemiring R]
    (p : ℕ) (x u : R) :
    GN p x u * ((x + u) ^ p + u ^ p) =
      (x + 2 * u) * GN p (x * (x + 2 * u)) (u ^ 2) := by
  rw [← GN_two_mul_degree_p_then_two, GN_two_mul_degree_two_then_p]

/-- The nontrivial divisors of a doubled prime. At `p = 2` two listed
entries coincide; for odd `p` they give three distinct layers. -/
theorem two_mul_prime_divisors_erase_one {p : ℕ}
    (hp : Nat.Prime p) :
    (2 * p).divisors.erase 1 = {2, p, 2 * p} := by
  have hpos : 0 < 2 * p := Nat.mul_pos (by decide) hp.pos
  ext k
  simp only [Finset.mem_erase, Nat.mem_divisors, ne_eq,
    hpos.ne', not_false_eq_true, and_true, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hk1, hkd⟩
    by_cases h2k : 2 ∣ k
    · rcases h2k with ⟨r, rfl⟩
      have hrp : r ∣ p := (Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)).mp hkd
      rcases hp.eq_one_or_self_of_dvd r hrp with rfl | rfl
      · exact Or.inl (by simp)
      · exact Or.inr (Or.inr rfl)
    · have hk2 : k.Coprime 2 := (Nat.prime_two.coprime_iff_not_dvd.mpr h2k).symm
      have hkp : k ∣ p := hk2.dvd_of_dvd_mul_left hkd
      rcases hp.eq_one_or_self_of_dvd k hkp with hk | hk
      · exact (hk1 hk).elim
      · exact Or.inr (Or.inl hk)
  · rintro (rfl | rfl | rfl)
    · exact ⟨by decide, dvd_mul_right 2 p⟩
    · exact ⟨hp.ne_one, ⟨2, by omega⟩⟩
    · exact ⟨by nlinarith [hp.two_le], dvd_rfl⟩

/-- At odd prime `p`, the doubled degree retains the `2`, `p`, and `2p`
cyclotomic layers. The first translated layer is the linear factor `X + 2`. -/
theorem kernelPolynomial_two_mul_prime {p : ℕ}
    (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    kernelPolynomial (2 * p) =
      (X + 2 : ℤ[X]) * (cyclotomic p ℤ).comp (X + 1) *
        (cyclotomic (2 * p) ℤ).comp (X + 1) := by
  rw [kernelPolynomial_eq_prod_cyclotomic (Nat.mul_pos (by decide) hp.pos),
    two_mul_prime_divisors_erase_one hp]
  have h2p : 2 ≠ 2 * p := by nlinarith [hp.two_le]
  have hpp : p ≠ 2 * p := by nlinarith [hp.pos]
  have h2 : (2 : ℕ) ∉ ({p, 2 * p} : Finset ℕ) := by simp [hp2.symm, h2p]
  have hp' : p ∉ ({2 * p} : Finset ℕ) := by simp [hpp]
  rw [Finset.prod_insert h2, Finset.prod_insert hp', Finset.prod_singleton]
  simp only [cyclotomic_two, add_comp, X_comp, one_comp]
  ring

/-- The three residual layers have degrees `1`, `p - 1`, and `p - 1`. -/
theorem two_mul_prime_cyclotomic_layer_degrees {p : ℕ}
    (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    ((cyclotomic 2 ℤ).comp (X + 1)).natDegree = 1 ∧
      ((cyclotomic p ℤ).comp (X + 1)).natDegree = p - 1 ∧
        ((cyclotomic (2 * p) ℤ).comp (X + 1)).natDegree = p - 1 := by
  have hdegree (k : ℕ) :
      ((cyclotomic k ℤ).comp (X + 1)).natDegree = k.totient := by
    simpa only [taylor_apply, C_1] using
      (natDegree_taylor (cyclotomic k ℤ) 1).trans (natDegree_cyclotomic k ℤ)
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm
  simp only [hdegree, Nat.totient_two, Nat.totient_prime hp,
    Nat.totient_mul hcop, one_mul, and_self]

end DkMath.NumberTheory.GapFocusing
