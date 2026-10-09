/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTailSelection
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Choose.Dvd

#print "file: DkMath.Lib.Cosmic.GTailFactor"

/-!
# Monomial factors and coefficient gcd of selected binomial bodies

Only active indices in `0..d` contribute. Bounds on those indices yield a
common monomial factor over any commutative semiring, without cancellation.
The natural gcd of active Pascal coefficients supplies a separate common
divisor of natural evaluations. It is not a gcd of evaluated coordinate values
and does not assert maximal powers of either coordinate.
-/

open scoped BigOperators

namespace DkMath.CosmicFormula

/-- Selected indices that actually contribute to the degree-`d` expansion. -/
def activeSelectedIndices (d : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (Finset.range (d + 1)).filter (fun k => k ∈ S)

@[simp] theorem mem_activeSelectedIndices (d : ℕ) (S : Finset ℕ) (k : ℕ) :
    k ∈ activeSelectedIndices d S ↔ k ≤ d ∧ k ∈ S := by
  simp [activeSelectedIndices]

/-- Residual after removing the monomial prescribed by active-index bounds. -/
def selectedResidual {R : Type*} [CommSemiring R]
    (d : ℕ) (S : Finset ℕ) (i j : ℕ) (x u : R) : R :=
  ∑ k ∈ activeSelectedIndices d S,
    (Nat.choose d k : R) * x ^ (k - i) * u ^ (j - k)

/--
Extract a common monomial using bounds on active indices only.
The empty active set gives a zero identity with the same hypotheses.
-/
theorem selectedBody_eq_monomial_mul_residual
    {R : Type*} [CommSemiring R]
    (d : ℕ) (S : Finset ℕ) (i j : ℕ) (x u : R)
    (_hij : i ≤ j) (hjd : j ≤ d)
    (hbounds : ∀ k ∈ activeSelectedIndices d S, i ≤ k ∧ k ≤ j) :
    selectedBody d S x u = x ^ i * u ^ (d - j) * selectedResidual d S i j x u := by
  change (∑ k ∈ activeSelectedIndices d S, selectedTerm d k x u) = _
  rw [selectedResidual, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  obtain ⟨hik, hkj⟩ := hbounds k hk
  have hx : i + (k - i) = k := by omega
  have hu : (d - j) + (j - k) = d - k := by omega
  calc
    selectedTerm d k x u =
        (Nat.choose d k : R) * (x ^ i * x ^ (k - i)) *
          (u ^ (d - j) * u ^ (j - k)) := by
      rw [← pow_add, ← pow_add, hx, hu]
      rfl
    _ = _ := by ac_rfl

/-- The active minimum and maximum give valid monomial bounds. -/
theorem selectedBody_eq_min_max_mul_residual
    {R : Type*} [CommSemiring R]
    (d : ℕ) (S : Finset ℕ) (x u : R)
    (hne : (activeSelectedIndices d S).Nonempty) :
    selectedBody d S x u =
      x ^ (activeSelectedIndices d S).min' hne *
        u ^ (d - (activeSelectedIndices d S).max' hne) *
        selectedResidual d S ((activeSelectedIndices d S).min' hne)
          ((activeSelectedIndices d S).max' hne) x u := by
  apply selectedBody_eq_monomial_mul_residual
  · exact Finset.min'_le_max' (activeSelectedIndices d S) hne
  · exact (mem_activeSelectedIndices d S _).mp
      ((activeSelectedIndices d S).max'_mem hne) |>.1
  · intro k hk
    exact ⟨Finset.min'_le _ _ hk, Finset.le_max' _ k hk⟩

/-- The extracted monomial divides every natural evaluation of the Body. -/
theorem monomial_dvd_selectedBody
    (d : ℕ) (S : Finset ℕ) (i j x u : ℕ)
    (hij : i ≤ j) (hjd : j ≤ d)
    (hbounds : ∀ k ∈ activeSelectedIndices d S, i ≤ k ∧ k ≤ j) :
    x ^ i * u ^ (d - j) ∣ selectedBody d S x u := by
  exact ⟨selectedResidual d S i j x u,
    selectedBody_eq_monomial_mul_residual d S i j x u hij hjd hbounds⟩

/-- Natural gcd of the active Pascal coefficients; the empty gcd is `0`. -/
def coeffGCD (d : ℕ) (S : Finset ℕ) : ℕ :=
  (activeSelectedIndices d S).gcd (Nat.choose d)

@[simp] theorem coeffGCD_empty (d : ℕ) : coeffGCD d ∅ = 0 := by
  simp [coeffGCD, activeSelectedIndices]

/-- The coefficient gcd divides each active coefficient. -/
theorem coeffGCD_dvd_choose (d : ℕ) (S : Finset ℕ) (k : ℕ)
    (hk : k ∈ activeSelectedIndices d S) :
    coeffGCD d S ∣ Nat.choose d k :=
  Finset.gcd_dvd hk

/-- Common active-coefficient divisors are exactly divisors of the coefficient gcd. -/
theorem dvd_coeffGCD_iff (d : ℕ) (S : Finset ℕ) (c : ℕ) :
    c ∣ coeffGCD d S ↔ ∀ k ∈ activeSelectedIndices d S, c ∣ Nat.choose d k :=
  Finset.dvd_gcd_iff

/-- A common coefficient divisor divides the natural residual, even if it is zero. -/
theorem dvd_selectedResidual_of_dvd_coeff
    (d : ℕ) (S : Finset ℕ) (i j x u c : ℕ)
    (hc : ∀ k ∈ activeSelectedIndices d S, c ∣ Nat.choose d k) :
    c ∣ selectedResidual d S i j x u := by
  apply Finset.dvd_sum
  intro k hk
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (hc k hk) _) _

/-- The coefficient gcd divides the natural Body; coordinates need not be nonzero. -/
theorem coeffGCD_dvd_selectedBody (d : ℕ) (S : Finset ℕ) (x u : ℕ) :
    coeffGCD d S ∣ selectedBody d S x u := by
  change coeffGCD d S ∣ ∑ k ∈ activeSelectedIndices d S, selectedTerm d k x u
  apply Finset.dvd_sum
  intro k hk
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (coeffGCD_dvd_choose d S k hk) _) _

/-- An active constant endpoint forces coefficient gcd `1`, including degree zero. -/
theorem coeffGCD_eq_one_of_zero_mem (d : ℕ) (S : Finset ℕ) (hzero : 0 ∈ S) :
    coeffGCD d S = 1 := by
  apply Nat.dvd_one.mp
  simpa only [Nat.choose_zero_right] using
    coeffGCD_dvd_choose d S 0 ((mem_activeSelectedIndices d S 0).mpr ⟨Nat.zero_le d, hzero⟩)

/-- An active top endpoint also forces coefficient gcd `1`. -/
theorem coeffGCD_eq_one_of_self_mem (d : ℕ) (S : Finset ℕ) (htop : d ∈ S) :
    coeffGCD d S = 1 := by
  apply Nat.dvd_one.mp
  simpa only [Nat.choose_self] using
    coeffGCD_dvd_choose d S d ((mem_activeSelectedIndices d S d).mpr ⟨le_rfl, htop⟩)

/-- Coefficient and monomial factors combine without coprimality assumptions. -/
theorem coeffGCD_mul_monomial_dvd_selectedBody
    (d : ℕ) (S : Finset ℕ) (i j x u : ℕ)
    (hij : i ≤ j) (hjd : j ≤ d)
    (hbounds : ∀ k ∈ activeSelectedIndices d S, i ≤ k ∧ k ≤ j) :
    coeffGCD d S * x ^ i * u ^ (d - j) ∣ selectedBody d S x u := by
  rw [selectedBody_eq_monomial_mul_residual d S i j x u hij hjd hbounds]
  have hc := dvd_selectedResidual_of_dvd_coeff d S i j x u (coeffGCD d S)
    (fun k hk => coeffGCD_dvd_choose d S k hk)
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    mul_dvd_mul_left (x ^ i * u ^ (d - j)) hc

/-- Removing both endpoints gives exactly the active interior interval. -/
@[simp] theorem activeSelectedIndices_interior (d : ℕ) :
    activeSelectedIndices d (Finset.Ico 1 d) = Finset.Ico 1 d := by
  ext k
  simp only [mem_activeSelectedIndices, Finset.mem_Ico]
  omega

/--
Any active subset of a prime interior that retains index `1` has gcd `p`.
This adapts prime coefficient divisibility to arbitrary sparse selections.
-/
theorem coeffGCD_eq_prime_of_interior
    (p : ℕ) (S : Finset ℕ) (hp : Nat.Prime p)
    (hinterior : ∀ k ∈ activeSelectedIndices p S, 0 < k ∧ k < p)
    (hone : 1 ∈ activeSelectedIndices p S) :
    coeffGCD p S = p := by
  apply Nat.dvd_antisymm
  · simpa only [Nat.choose_one_right] using coeffGCD_dvd_choose p S 1 hone
  · apply (dvd_coeffGCD_iff p S p).mpr
    intro k hk
    obtain ⟨hkpos, hkp⟩ := hinterior k hk
    exact hp.dvd_choose_self (Nat.ne_of_gt hkpos) hkp

/-- The prime interior coefficient gcd is exactly the prime, including `p = 2`. -/
theorem coeffGCD_prime_interior (p : ℕ) (hp : Nat.Prime p) :
    coeffGCD p (Finset.Ico 1 p) = p := by
  apply coeffGCD_eq_prime_of_interior p (Finset.Ico 1 p) hp
  · intro k hk
    rw [activeSelectedIndices_interior] at hk
    have := Finset.mem_Ico.mp hk
    omega
  · rw [activeSelectedIndices_interior]
    exact Finset.mem_Ico.mpr ⟨le_rfl, hp.one_lt⟩

/-- Both endpoint removal forces the common divisor `p*x*u` on natural bodies. -/
theorem prime_mul_coords_dvd_selectedBody_interior
    (p x u : ℕ) (hp : Nat.Prime p) :
    p * x * u ∣ selectedBody p (Finset.Ico 1 p) x u := by
  have hbounds : ∀ k ∈ activeSelectedIndices p (Finset.Ico 1 p),
      1 ≤ k ∧ k ≤ p - 1 := by
    intro k hk
    rw [activeSelectedIndices_interior] at hk
    have := Finset.mem_Ico.mp hk
    omega
  have h := coeffGCD_mul_monomial_dvd_selectedBody p (Finset.Ico 1 p) 1 (p - 1) x u
    (by have := hp.two_le; omega) (Nat.sub_le p 1) hbounds
  rw [coeffGCD_prime_interior p hp] at h
  have hsub : p - (p - 1) = 1 := by have := hp.two_le; omega
  simpa only [hsub, pow_one] using h

end DkMath.CosmicFormula
