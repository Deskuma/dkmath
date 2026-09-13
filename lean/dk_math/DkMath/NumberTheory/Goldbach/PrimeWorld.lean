/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/
import DkMath.NumberTheory.Goldbach.Obstruction
import DkMath.NumberTheory.Primitive.PeriodicPrimeWorld
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.ZMod.Basic

#print "file: DkMath.NumberTheory.Goldbach.PrimeWorld"

/-!
# Paired prime worlds

The raw obstruction classes are `n` and `-n` modulo each prime. They coincide
exactly when the prime divides `2*n`; in particular the direction `2` removes
one class, not two. CRT describes a full product period. It does not place a
survivor inside the much shorter interval `u < n-1`. Proper-divisor endpoint
exceptions are handled separately by the finite interval layer.
-/

namespace DkMath.NumberTheory

open Primitive StructuralArithmetic

/-- A finite certified world for paired residue observations. -/
structure GoldbachPrimeWorld where
  primes : Finset ℕ
  isPrime : KnownPrimeScales primes

/-- The canonical square-root world is certified by its defining filter. -/
def goldbachSmallWorld (n : ℕ) : GoldbachPrimeWorld where
  primes := goldbachSmallPrimes n
  isPrime := fun _ hr => (mem_goldbachSmallPrimes.mp hr).1

/-- The two raw forbidden classes, with duplicates removed by `Finset`. -/
def goldbachForbiddenResidues (n r : ℕ) : Finset (ZMod r) :=
  {(n : ZMod r), -(n : ZMod r)}

/-- Natural left divisibility is the residue `+n`, under the necessary order bound. -/
theorem goldbach_left_obstructed_iff {n r u : ℕ} (hu : u ≤ n) :
    GoldbachLeftObstructed n r u ↔ (u : ZMod r) = (n : ZMod r) := by
  unfold GoldbachLeftObstructed
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hu, sub_eq_zero]
  exact eq_comm

/-- Right divisibility is the residue `-n`. -/
theorem goldbach_right_obstructed_iff (n r u : ℕ) :
    GoldbachRightObstructed n r u ↔ (u : ZMod r) = -(n : ZMod r) := by
  unfold GoldbachRightObstructed
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, add_comm, add_eq_zero_iff_eq_neg]

/-- Raw obstruction agrees exactly with membership in the two-class set. -/
theorem goldbach_obstructed_iff_mem_forbidden {n r u : ℕ} (hu : u ≤ n) :
    GoldbachObstructed n r u ↔ (u : ZMod r) ∈ goldbachForbiddenResidues n r := by
  simp [GoldbachObstructed, goldbach_left_obstructed_iff hu,
    goldbach_right_obstructed_iff, goldbachForbiddenResidues]

/-- The two forbidden directions merge precisely at divisors of twice the center. -/
theorem goldbach_residue_eq_neg_iff (n r : ℕ) :
    (n : ZMod r) = -(n : ZMod r) ↔ r ∣ 2 * n := by
  rw [eq_neg_iff_add_eq_zero, ← two_mul, ← Nat.cast_two, ← Nat.cast_mul,
    ZMod.natCast_eq_zero_iff]

/-- Exact local forbidden-seat count, including `r=2` and divisors of the center. -/
theorem goldbach_card_forbidden (n r : ℕ) :
    (goldbachForbiddenResidues n r).card = if r ∣ 2 * n then 1 else 2 := by
  by_cases h : r ∣ 2 * n
  · have he := (goldbach_residue_eq_neg_iff n r).mpr h
    rw [if_pos h]
    unfold goldbachForbiddenResidues
    rw [Finset.insert_eq_of_mem (Finset.mem_singleton.mpr he)]
    exact Finset.card_singleton _
  · have he := (goldbach_residue_eq_neg_iff n r).not.mpr h
    rw [if_neg h]
    exact Finset.card_pair he

/-- Local raw survivors in a nonzero modulus. -/
def goldbachLocalResidues (n r : ℕ) [NeZero r] : Finset (ZMod r) :=
  Finset.univ \ goldbachForbiddenResidues n r

/-- Exact local survivor count is the modulus minus one or two forbidden classes. -/
theorem goldbach_card_local (n r : ℕ) [NeZero r] :
    (goldbachLocalResidues n r).card = r - if r ∣ 2 * n then 1 else 2 := by
  rw [goldbachLocalResidues, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, ZMod.card, goldbach_card_forbidden]

/-- Raw simultaneous avoidance; this observer is periodic on all natural offsets. -/
def GoldbachResidueSurvives (n : ℕ) (S : Finset ℕ) (u : ℕ) : Prop :=
  ∀ r ∈ S, (u : ZMod r) ∉ goldbachForbiddenResidues n r

instance (n : ℕ) (S : Finset ℕ) (u : ℕ) : Decidable (GoldbachResidueSurvives n S u) := by
  unfold GoldbachResidueSurvives
  infer_instance

/-- Canonical paired residues in one product period. -/
def goldbachPrimeWorldResidues (n : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (Finset.range (primeWorldModulus S)).filter (GoldbachResidueSurvives n S)

/-- The canonical residue set retains exactly the bounded raw survivors. -/
@[simp] theorem mem_goldbachPrimeWorldResidues {n u : ℕ} {S : Finset ℕ} :
    u ∈ goldbachPrimeWorldResidues n S ↔
      u < primeWorldModulus S ∧ GoldbachResidueSurvives n S u := by
  simp [goldbachPrimeWorldResidues]

/-- Multiples of the product modulus leave every local coordinate unchanged. -/
theorem goldbach_cast_add_period {S : Finset ℕ} {r : ℕ} (hr : r ∈ S) (u k : ℕ) :
    ((u + k * primeWorldModulus S : ℕ) : ZMod r) = (u : ZMod r) := by
  have hzero : (primeWorldModulus S : ZMod r) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (dvd_primeWorldModulus_of_mem hr)
  simp [Nat.cast_add, Nat.cast_mul, hzero]

/-- Full product-period invariance needs divisibility only, not CRT or primality. -/
theorem goldbach_residue_periodic (n u k : ℕ) (S : Finset ℕ) :
    GoldbachResidueSurvives n S (u + k * primeWorldModulus S) ↔
      GoldbachResidueSurvives n S u := by
  unfold GoldbachResidueSurvives
  apply forall_congr'
  intro r
  apply forall_congr'
  intro hr
  rw [goldbach_cast_add_period hr]

/-- Reduction to the canonical period preserves raw paired avoidance. -/
theorem goldbach_residue_mod_period (n u : ℕ) (S : Finset ℕ) :
    GoldbachResidueSurvives n S (u % primeWorldModulus S) ↔
      GoldbachResidueSurvives n S u := by
  simpa [Nat.mod_add_div, Nat.mul_comm] using
    (goldbach_residue_periodic n (u % primeWorldModulus S)
      (u / primeWorldModulus S) S).symm

/-- Inserting a prime refines the paired observer by exactly its two forbidden classes. -/
theorem goldbach_residue_insert (n q u : ℕ) (S : Finset ℕ) :
    GoldbachResidueSurvives n (insert q S) u ↔
      GoldbachResidueSurvives n S u ∧
        (u : ZMod q) ∉ goldbachForbiddenResidues n q := by
  simp only [GoldbachResidueSurvives, Finset.mem_insert, forall_eq_or_imp]
  exact and_comm

/-- CRT realizes any prescribed local coordinates inside one complete product period. -/
theorem goldbach_primeWorld_crt (W : GoldbachPrimeWorld) (a : ℕ → ℕ) :
    ∃ u < primeWorldModulus W.primes,
      ∀ r ∈ W.primes, (u : ZMod r) = (a r : ZMod r) := by
  have hn : ∀ r ∈ W.primes, r ≠ 0 := fun r hr => (W.isPrime hr).ne_zero
  have hc : Set.Pairwise (↑W.primes) (fun p q => Nat.Coprime p q) := by
    intro p hp q hq hne
    exact (Nat.coprime_primes (W.isPrime hp) (W.isPrime hq)).mpr hne
  let u := Nat.chineseRemainderOfFinset a (fun r : ℕ => r) W.primes hn hc
  refine ⟨u.val, Nat.chineseRemainderOfFinset_lt_prod a (fun r : ℕ => r) hn hc, ?_⟩
  intro r hr
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (u.property r hr)

/-- Local avoiding representatives give a full-period survivor by CRT. -/
theorem goldbach_primeWorld_nonempty_of_local (n : ℕ) (W : GoldbachPrimeWorld)
    (a : ℕ → ℕ)
    (ha : ∀ r ∈ W.primes, (a r : ZMod r) ∉ goldbachForbiddenResidues n r) :
    (goldbachPrimeWorldResidues n W.primes).Nonempty := by
  obtain ⟨u, hu, hc⟩ := goldbach_primeWorld_crt W a
  refine ⟨u, mem_goldbachPrimeWorldResidues.mpr ⟨hu, ?_⟩⟩
  intro r hr
  rw [hc r hr]
  exact ha r hr

/-- Raw avoidance is sufficient for proper-divisor survival inside the interval. -/
theorem goldbach_survives_of_residue {n u : ℕ} {S : Finset ℕ}
    (hu : u ≤ n) (hs : GoldbachResidueSurvives n S u) : GoldbachSurvives n S u := by
  intro r hr ho
  apply hs r hr
  apply (goldbach_obstructed_iff_mem_forbidden hu).mp
  exact ho.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)

/-- If both endpoints exceed every world prime, the endpoint exceptions disappear. -/
theorem goldbach_survives_iff_residue_of_large_endpoints {n u : ℕ} {S : Finset ℕ}
    (hu : u ≤ n) (hlarge : ∀ r ∈ S, r < n - u) :
    GoldbachSurvives n S u ↔ GoldbachResidueSurvives n S u := by
  constructor
  · intro hs r hr ho
    have hl := hlarge r hr
    apply hs r hr
    have hraw := (goldbach_obstructed_iff_mem_forbidden hu).mpr ho
    exact hraw.elim (fun hd => Or.inl ⟨hd, by omega⟩)
      (fun hd => Or.inr ⟨hd, by omega⟩)
  · exact goldbach_survives_of_residue hu

end DkMath.NumberTheory
