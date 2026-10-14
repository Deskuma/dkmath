/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CFBRC.CyclotomicProduct
import DkMath.NumberTheory.GapFocusing.CyclotomicAddress
import DkMath.NumberTheory.GapFocusing.PrimeOrder

#print "file: DkMath.NumberTheory.GapFocusing.HomogeneousAddress"

/-!
# Rational-prime addresses of the existing homogeneous cyclotomic evaluation

The value formalism is `CFBRC.cyclotomicShiftedEval`. Substituting
`x=a-b,u=b` gives the homogeneous value at `(a,b)`. Reduction to a finite
field compares its zero locus with the root of the cyclotomic polynomial
at `a*b⁻¹`, without identifying carriers by a norm.
-/

namespace DkMath.NumberTheory.GapFocusing

open DkMath.CFBRC Polynomial

/-- Homogeneous cyclotomic evaluation commutes with coefficient homomorphisms. -/
theorem map_cyclotomicShiftedEval
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (n : ℕ) (x u : R) :
    f (cyclotomicShiftedEval n x u) = cyclotomicShiftedEval n (f x) (f u) := by
  unfold cyclotomicShiftedEval
  rw [MvPolynomial.map_eval, ← Polynomial.homogenize_map, Polynomial.map_map]
  have hf : f.comp (Int.castRingHom R) = Int.castRingHom S := by
    ext z
    simp
  rw [hf]
  congr 1
  congr 1
  funext i
  fin_cases i <;> simp

/-- The unit-anchor homogeneous evaluator is the existing plain evaluator
over every commutative ring, without a field hypothesis. -/
theorem cyclotomicShiftedEval_one_eq_cyclotomicEval
    {R : Type*} [CommRing R] (n : ℕ) (x : R) :
    cyclotomicShiftedEval n x 1 = cyclotomicEval n (x + 1) := by
  unfold cyclotomicShiftedEval
  change MvPolynomial.eval₂ (RingHom.id R) ![x + 1, 1]
    (((cyclotomic n ℤ).map (Int.castRingHom R)).homogenize (cyclotomic n ℤ).natDegree) = _
  rw [Polynomial.eval₂_homogenize_of_eq_one
    (Polynomial.natDegree_map_le (p := cyclotomic n ℤ) (f := Int.castRingHom R))
    (RingHom.id R) ![x + 1, 1] (by simp)]
  simp [cyclotomicEval, eval₂_eq_eval_map]

/-- Positive homogeneous layer indices containing a chosen rational divisor.
Primality and nonvanishing are hypotheses of the classification, not of the set. -/
def primeLayerAddresses (q : ℕ) (a b : ℤ) : Set ℕ :=
  {n | 1 < n ∧ (q : ℤ) ∣ cyclotomicShiftedEval n (a - b) b}

/-- A layer index maps to its set of rational prime divisors. Distinct
indices can have overlapping, and even equal, support after evaluation. -/
def layerPrimeSupport (a b : ℤ) (n : ℕ) : Set ℕ :=
  {q | q.Prime ∧ (q : ℤ) ∣ cyclotomicShiftedEval n (a - b) b}

/-- A prime address set is the corresponding support-incidence fiber. -/
theorem primeLayerAddresses_eq_support_fiber
    {q : ℕ} (hq : q.Prime) (a b : ℤ) :
    primeLayerAddresses q a b = {n | 1 < n ∧ q ∈ layerPrimeSupport a b n} := by
  ext n
  simp [primeLayerAddresses, layerPrimeSupport, hq]

/-- Divisibility of the homogeneous value is the actual residue-field root
condition. Only the second coordinate must be invertible for this reduction. -/
theorem dvd_cyclotomicShiftedEval_iff_isRoot
    (q : ℕ) [Fact q.Prime] (n : ℕ) (a b : ℤ) (hb : ¬(q : ℤ) ∣ b) :
    (q : ℤ) ∣ cyclotomicShiftedEval n (a - b) b ↔
      (cyclotomic n (ZMod q)).IsRoot ((a : ZMod q) * (b : ZMod q)⁻¹) := by
  have hb0 : (b : ZMod q) ≠ 0 := by
    intro hz
    exact hb ((ZMod.intCast_zmod_eq_zero_iff_dvd b q).mp hz)
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  change (Int.castRingHom (ZMod q)) (cyclotomicShiftedEval n (a - b) b) = 0 ↔ _
  rw [map_cyclotomicShiftedEval]
  change cyclotomicShiftedEval n ((a - b : ℤ) : ZMod q) (b : ZMod q) = 0 ↔ _
  rw [cyclotomicShiftedEval_eq_cyclotomicEval_div_mul_pow n _ _ hb0]
  have hbpow : (b : ZMod q) ^ (cyclotomic n ℤ).natDegree ≠ 0 := pow_ne_zero _ hb0
  rw [mul_eq_zero, or_iff_left hbpow]
  simp [cyclotomicEval, eval₂_eq_eval_map, IsRoot.def, div_eq_mul_inv]

/-- Complete homogeneous divisibility law at every positive degree. -/
theorem dvd_cyclotomicShiftedEval_iff_prime_pow_mul_orderOf
    (q : ℕ) [Fact q.Prime] {n : ℕ} (hn : 0 < n) (a b : ℤ)
    (hb : ¬(q : ℤ) ∣ b) :
    (q : ℤ) ∣ cyclotomicShiftedEval n (a - b) b ↔
      ∃ k : ℕ, n = orderOf ((a : ZMod q) * (b : ZMod q)⁻¹) * q ^ k := by
  rw [dvd_cyclotomicShiftedEval_iff_isRoot q n a b hb,
    isRoot_cyclotomic_iff_prime_pow_mul_orderOf hn]

/-- At an index not divisible by the residue characteristic, the only
possible homogeneous prime layer is the fundamental order itself. -/
theorem dvd_cyclotomicShiftedEval_iff_primeOrder_eq_of_not_dvd
    (q : ℕ) [Fact q.Prime] (n : ℕ) (a b : ℤ)
    (hb : ¬(q : ℤ) ∣ b) (hqn : ¬q ∣ n) :
    (q : ℤ) ∣ cyclotomicShiftedEval n (a - b) b ↔ primeOrder q a b = n := by
  rw [dvd_cyclotomicShiftedEval_iff_isRoot q n a b hb,
    isRoot_cyclotomic_iff_orderOf_of_not_dvd hqn]
  rfl

/-- The nontrivial layer addresses are exactly the prime-power order ray,
restricted to indices greater than one. -/
theorem mem_primeLayerAddresses_iff
    (q : ℕ) [Fact q.Prime] (a b : ℤ) (hb : ¬(q : ℤ) ∣ b) (n : ℕ) :
    n ∈ primeLayerAddresses q a b ↔
      1 < n ∧ ∃ k : ℕ, n = orderOf ((a : ZMod q) * (b : ZMod q)⁻¹) * q ^ k := by
  constructor
  · rintro ⟨hn, hdiv⟩
    exact ⟨hn, (dvd_cyclotomicShiftedEval_iff_prime_pow_mul_orderOf
      q (by omega) a b hb).mp hdiv⟩
  · rintro ⟨hn, hdegree⟩
    exact ⟨hn, (dvd_cyclotomicShiftedEval_iff_prime_pow_mul_orderOf
      q (by omega) a b hb).mpr hdegree⟩

/-- Multiplication of the degree by the rational prime preserves its
homogeneous layer support, even when the prime already divides the degree. -/
theorem dvd_cyclotomicShiftedEval_mul_prime_iff
    (q : ℕ) [Fact q.Prime] (n : ℕ) (a b : ℤ) (hb : ¬(q : ℤ) ∣ b) :
    (q : ℤ) ∣ cyclotomicShiftedEval (n * q) (a - b) b ↔
      (q : ℤ) ∣ cyclotomicShiftedEval n (a - b) b := by
  rw [dvd_cyclotomicShiftedEval_iff_isRoot q (n * q) a b hb,
    dvd_cyclotomicShiftedEval_iff_isRoot q n a b hb,
    isRoot_cyclotomic_mul_prime_iff]

/-- First appearance includes all positive indices, including the linear
factor at degree one. This is different from minimizing only `n>1` addresses. -/
def FirstLayerAppearance (q : ℕ) (a b : ℤ) (n : ℕ) : Prop :=
  0 < n ∧ (q : ℤ) ∣ cyclotomicShiftedEval n (a - b) b ∧
    ∀ m : ℕ, 0 < m → m < n → ¬(q : ℤ) ∣ cyclotomicShiftedEval m (a - b) b

/-- First homogeneous layer appearance is exactly the order of the residue ratio. -/
theorem firstLayerAppearance_iff_primeOrder_eq
    (q : ℕ) [Fact q.Prime] (a b : ℤ) {n : ℕ}
    (hn : 0 < n) (hb : ¬(q : ℤ) ∣ b) :
    FirstLayerAppearance q a b n ↔ primeOrder q a b = n := by
  have hlaw (m : ℕ) (hm : 0 < m) :
      (q : ℤ) ∣ cyclotomicShiftedEval m (a - b) b ↔
        ∃ k : ℕ, m = primeOrder q a b * q ^ k :=
    dvd_cyclotomicShiftedEval_iff_prime_pow_mul_orderOf q hm a b hb
  have hqpow (k : ℕ) : 0 < q ^ k := pow_pos (Fact.out : q.Prime).pos k
  constructor
  · rintro ⟨_, hdiv, hlow⟩
    obtain ⟨k, hnk⟩ := (hlaw n hn).mp hdiv
    have hrpos : 0 < primeOrder q a b := by
      by_contra hr
      have hz : primeOrder q a b = 0 := by omega
      rw [hz, zero_mul] at hnk
      omega
    have hrle : primeOrder q a b ≤ n := by
      rw [hnk]
      exact Nat.le_mul_of_pos_right _ (hqpow k)
    have hrfactor : (q : ℤ) ∣ cyclotomicShiftedEval (primeOrder q a b) (a - b) b :=
      (hlaw _ hrpos).mpr ⟨0, by simp⟩
    by_contra hne
    exact hlow _ hrpos (by omega) hrfactor
  · intro hr
    refine ⟨hn, (hlaw n hn).mpr ⟨0, by simp [hr]⟩, ?_⟩
    intro m hm hmn hdiv
    obtain ⟨k, hmk⟩ := (hlaw m hm).mp hdiv
    have hnle : n ≤ m := by
      rw [hmk, hr]
      exact Nat.le_mul_of_pos_right _ (hqpow k)
    omega

/-- The existing Zsigmondy notion and first homogeneous layer appearance
coincide under the natural-number subtraction and denominator hypotheses. -/
theorem primitivePrimeDivisor_iff_firstLayerAppearance
    {q a b n : ℕ} [Fact q.Prime] (hab : b ≤ a) (hn : 0 < n) (hb : ¬q ∣ b) :
    DkMath.Zsigmondy.PrimitivePrimeDivisor a b n q ↔
      FirstLayerAppearance q a b n := by
  have hbZ : ¬(q : ℤ) ∣ (b : ℤ) := by exact_mod_cast hb
  rw [primitivePrimeDivisor_iff_primeOrder_eq hab hn hb,
    firstLayerAppearance_iff_primeOrder_eq q a b hn hbZ]

/-- Above degree one, an existing primitive prime gives first layer appearance
without an extra coordinate coprimality assumption. -/
theorem primitivePrimeDivisor_firstLayerAppearance
    {q a b n : ℕ} (hab : b ≤ a) (hn : 1 < n)
    (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor a b n q) :
    FirstLayerAppearance q a b n := by
  let : Fact q.Prime := ⟨hprim.prime⟩
  have hb := (primitivePrimeDivisor_not_dvd_coordinates hab hn hprim).2
  exact (primitivePrimeDivisor_iff_firstLayerAppearance hab (by omega) hb).mp hprim

/-- An order above one is the least nontrivial layer address. -/
theorem primeLayerAddresses_isLeast_of_one_lt_primeOrder
    (q : ℕ) [Fact q.Prime] (a b : ℤ) (hb : ¬(q : ℤ) ∣ b)
    (hr : 1 < primeOrder q a b) :
    IsLeast (primeLayerAddresses q a b) (primeOrder q a b) := by
  constructor
  · exact (mem_primeLayerAddresses_iff q a b hb _).mpr ⟨hr, 0, by simp [primeOrder, primeRatio]⟩
  · intro n hn
    obtain ⟨_, k, hnk⟩ := (mem_primeLayerAddresses_iff q a b hb n).mp hn
    change n = primeOrder q a b * q ^ k at hnk
    rw [hnk]
    exact Nat.le_mul_of_pos_right _ (pow_pos (Fact.out : q.Prime).pos k)

/-- If the ratio has order one, the least address above degree one is `q`.
It is a reappearance of the degree-one divisor, not a primitive prime at `q`. -/
theorem primeLayerAddresses_isLeast_of_primeOrder_eq_one
    (q : ℕ) [Fact q.Prime] (a b : ℤ) (hb : ¬(q : ℤ) ∣ b)
    (hr : primeOrder q a b = 1) : IsLeast (primeLayerAddresses q a b) q := by
  have hq : q.Prime := Fact.out
  constructor
  · apply (mem_primeLayerAddresses_iff q a b hb q).mpr
    refine ⟨hq.one_lt, 1, ?_⟩
    change q = primeOrder q a b * q ^ 1
    simp [hr]
  · intro n hn
    obtain ⟨hn1, k, hnk⟩ := (mem_primeLayerAddresses_iff q a b hb n).mp hn
    change n = primeOrder q a b * q ^ k at hnk
    rw [hr, one_mul] at hnk
    have hk : k ≠ 0 := by
      intro hk
      simp [hk] at hnk
      omega
    rw [hnk]
    exact le_self_pow hq.one_lt.le hk

/-- Each nontrivial prime-layer address has a strictly larger address by
degree multiplication, not by additive periodicity. -/
theorem exists_gt_mem_primeLayerAddresses_of_mem
    (q : ℕ) [Fact q.Prime] (a b : ℤ) (hb : ¬(q : ℤ) ∣ b)
    {n : ℕ} (hn : n ∈ primeLayerAddresses q a b) :
    ∃ m : ℕ, n < m ∧ m ∈ primeLayerAddresses q a b := by
  have hq : q.Prime := Fact.out
  obtain ⟨hn1, hdiv⟩ := hn
  have hlt : n < n * q := by nlinarith [hq.one_lt]
  refine ⟨n * q, hlt, ?_⟩
  exact ⟨by omega, (dvd_cyclotomicShiftedEval_mul_prime_iff q n a b hb).mpr hdiv⟩

end DkMath.NumberTheory.GapFocusing
