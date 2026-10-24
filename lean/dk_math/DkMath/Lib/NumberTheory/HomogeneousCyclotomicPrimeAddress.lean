/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.HomogeneousCyclotomicBoundary
import DkMath.Lib.NumberTheory.PowerDifferenceCofactorPrimeAddress

#print "file: DkMath.Lib.NumberTheory.HomogeneousCyclotomicPrimeAddress"

/-!
# Direct-coordinate prime addresses, boundaries and textbook examples

[DkMath.Lib] GN-LIB-006b. These APIs use the Lib spelling at coordinates a,b.
The historical shifted-address proofs are reused through the exact carrier
bridge. The single-layer ray n=r*q^k is distinct from r|n for the whole R_n.
Degree zero, order one and vanishing coordinates are treated separately.
-/

namespace DkMath.Lib.NumberTheory

open DkMath.NumberTheory.GapFocusing

/-- [DkMath.Lib] Homogeneous evaluation commutes with coefficient maps.
The coordinate difference is transported by map_sub; the old shifted map
law supplies the polynomial proof. -/
theorem map_homogeneousCyclotomicEval
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) (a b : R) :
    f (homogeneousCyclotomicEval n a b) = homogeneousCyclotomicEval n (f a) (f b) := by
  unfold homogeneousCyclotomicEval
  rw [map_cyclotomicShiftedEval, map_sub]

/-- [DkMath.Lib] The anchor-one evaluator is the ordinary Lib evaluator.
This holds in every commutative ring, without a field or gap condition. -/
theorem homogeneousCyclotomicEval_one_right
    {R : Type*} [CommRing R] (n : ℕ) (a : R) :
    homogeneousCyclotomicEval n a 1 = cyclotomicEval n a := by
  unfold homogeneousCyclotomicEval
  rw [cyclotomicShiftedEval_one_eq_cyclotomicEval, sub_add_cancel]
  exact cfbRC_cyclotomicEval_eq_lib n a

/-- [DkMath.Lib] At zero anchor the cyclotomic leading term survives.
This boundary does not use dehomogenization or an inverse of zero. -/
theorem homogeneousCyclotomicEval_zero_right
    {R : Type*} [CommRing R] (n : ℕ) (a : R) :
    homogeneousCyclotomicEval n a 0 = a ^ n.totient := by
  simp only [homogeneousCyclotomicEval, sub_zero, cyclotomicShiftedEval_zero_anchor]

/-- [DkMath.Lib] The degree-zero cyclotomic evaluator is one even at zero coordinates.
The positive-degree guard in the prime-power ray therefore cannot be dropped. -/
@[simp] theorem homogeneousCyclotomicEval_zero_degree
    {R : Type*} [CommRing R] (a b : R) : homogeneousCyclotomicEval 0 a b = 1 := by
  rw [homogeneousCyclotomicEval_eq_eval_homogenize]
  simp [Polynomial.cyclotomic_zero]

/-- [DkMath.Lib] The complete single-layer address at positive degree.
Only b must be prime-free. A vanishing numerator gives order zero and hence
no positive ray. No assumption about valuation one or primality of n is made. -/
theorem prime_dvd_homogeneousCyclotomicEval_iff_order_ray
    {q n : ℕ} [Fact q.Prime] (hn : 0 < n) (a b : ℤ) (hb : ¬ (q : ℤ) ∣ b) :
    (q : ℤ) ∣ homogeneousCyclotomicEval n a b ↔
      ∃ k : ℕ, n = primeOrder q a b * q ^ k := by
  exact dvd_cyclotomicShiftedEval_iff_prime_pow_mul_orderOf q hn a b hb

/-- [DkMath.Lib] Away from q in the degree, the layer is exactly the basic order.
The hypothesis excludes degree zero automatically. -/
theorem prime_dvd_homogeneousCyclotomicEval_iff_order_eq_of_not_dvd
    {q : ℕ} [Fact q.Prime] (n : ℕ) (a b : ℤ) (hb : ¬ (q : ℤ) ∣ b) (hqn : ¬ q ∣ n) :
    (q : ℤ) ∣ homogeneousCyclotomicEval n a b ↔ primeOrder q a b = n := by
  exact dvd_cyclotomicShiftedEval_iff_primeOrder_eq_of_not_dvd q n a b hb hqn

/-- [DkMath.Lib] When q divides the denominator, divisibility of a positive
layer is exactly divisibility of the numerator. This separate branch replaces
the unit-ratio law rather than applying it at a zero denominator. -/
theorem prime_dvd_homogeneousCyclotomicEval_iff_dvd_first_of_dvd_second
    {q n : ℕ} [Fact q.Prime] (hn : 0 < n) (a b : ℤ) (hb : (q : ℤ) ∣ b) :
    (q : ℤ) ∣ homogeneousCyclotomicEval n a b ↔ (q : ℤ) ∣ a := by
  exact dvd_cyclotomicShiftedEval_iff_dvd_first_of_dvd_second q hn a b hb

/-- [DkMath.Lib] A prime dividing only the numerator occurs in no positive layer.
The ray theorem supplies the proof: the residue ratio is zero, so its order
is zero. This is not an assertion that the integer value is prime-free. -/
theorem not_prime_dvd_homogeneousCyclotomicEval_of_dvd_first
    {q n : ℕ} [Fact q.Prime] (hn : 0 < n) (a b : ℤ)
    (ha : (q : ℤ) ∣ a) (hb : ¬ (q : ℤ) ∣ b) :
    ¬ (q : ℤ) ∣ homogeneousCyclotomicEval n a b := by
  intro hdiv
  obtain ⟨k, hk⟩ := (prime_dvd_homogeneousCyclotomicEval_iff_order_ray hn a b hb).mp hdiv
  have ha0 := (ZMod.intCast_zmod_eq_zero_iff_dvd a q).mpr ha
  simp only [primeOrder, primeRatio, ha0, zero_mul, orderOf_zero] at hk
  omega

/-! ## Textbook examples
A nontrivial ratio gives a multiplicative q-power ray, not every multiple of
its basic order. At order one the first positive layer is 1, while the first
nontrivial layer is q. Boundary examples retain the positive-degree guard.
-/
example (n : ℕ) (hn : 0 < n) :
    (7 : ℤ) ∣ homogeneousCyclotomicEval n 18 1 ↔ ∃ k : ℕ, n = 3 * 7 ^ k := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hr : primeOrder 7 18 1 = 3 := by
    unfold primeOrder primeRatio
    apply orderOf_eq_prime <;> norm_num <;> decide
  simpa only [Nat.cast_ofNat, hr] using
    (prime_dvd_homogeneousCyclotomicEval_iff_order_ray (q := 7) hn 18 1 (by decide))

example : (7 ∣ DkMath.Lib.Cosmic.powerDifferenceCofactor 6 (18 : ℕ) 1) ∧
    ¬ (7 : ℤ) ∣ homogeneousCyclotomicEval 6 18 1 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hr : primeOrder 7 18 1 = 3 := by
    unfold primeOrder primeRatio
    apply orderOf_eq_prime <;> norm_num <;> decide
  refine ⟨by decide, ?_⟩
  intro hdiv
  have he := (prime_dvd_homogeneousCyclotomicEval_iff_order_eq_of_not_dvd
    (q := 7) 6 18 1 (by decide) (by decide)).mp hdiv
  omega

example : IsLeast (primeLayerAddresses 2 3 1) 2 := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  exact primeLayerAddresses_isLeast_of_primeOrder_eq_one 2 3 1 (by decide)
    ((primeOrder_eq_one_iff_dvd_gap 3 1 (by decide)).mpr (by decide))

example : FirstLayerAppearance 3 4 1 1 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact (firstLayerAppearance_iff_primeOrder_eq 3 4 1 (by decide) (by decide)).mpr
    ((primeOrder_eq_one_iff_dvd_gap 4 1 (by decide)).mpr (by decide))

example : IsLeast (primeLayerAddresses 3 4 1) 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact primeLayerAddresses_isLeast_of_primeOrder_eq_one 3 4 1 (by decide)
    ((primeOrder_eq_one_iff_dvd_gap 4 1 (by decide)).mpr (by decide))

example (n : ℕ) (hn : 0 < n) : ¬ (3 : ℤ) ∣ homogeneousCyclotomicEval n 1 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  intro hdiv
  exact (by decide : ¬ (3 : ℤ) ∣ 1)
    ((prime_dvd_homogeneousCyclotomicEval_iff_dvd_first_of_dvd_second
      (q := 3) hn 1 3 (by decide)).mp hdiv)

example (n : ℕ) (hn : 0 < n) : (3 : ℤ) ∣ homogeneousCyclotomicEval n 6 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact (prime_dvd_homogeneousCyclotomicEval_iff_dvd_first_of_dvd_second
    (q := 3) hn 6 3 (by decide)).mpr (by decide)

example (n : ℕ) (hn : 0 < n) : ¬ (3 : ℤ) ∣ homogeneousCyclotomicEval n 3 1 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact not_prime_dvd_homogeneousCyclotomicEval_of_dvd_first hn 3 1 (by decide) (by decide)

example : homogeneousCyclotomicEval 0 (0 : ℤ) 0 = 1 := by simp

example : homogeneousCyclotomicEval 3 (18 : ℤ) 1 = 343 := by
  rw [homogeneousCyclotomicEval_one_right]
  norm_num [cyclotomicEval, Polynomial.cyclotomic_three]

example : padicValNat 7 (homogeneousCyclotomicEval 3 (18 : ℤ) 1).natAbs = 3 := by
  rw [homogeneousCyclotomicEval_one_right]
  norm_num [cyclotomicEval, Polynomial.cyclotomic_three]
  change padicValNat 7 (7 ^ 3) = 3
  exact padicValNat_base_pow (by decide) 3

end DkMath.Lib.NumberTheory
