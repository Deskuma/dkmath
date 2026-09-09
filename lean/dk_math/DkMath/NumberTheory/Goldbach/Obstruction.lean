/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/
import DkMath.NumberTheory.Goldbach.Basic
import Mathlib.Data.Nat.Sqrt

#print "file: DkMath.NumberTheory.Goldbach.Obstruction"

/-!
# Exact finite obstruction reduction

A prime dividing an endpoint is an obstruction only when it is a proper
divisor. This exception retains `2+2`, `3+7`, and every pair containing a
prime below the sieve cutoff. The complete cutoff `sqrt (2*n)` detects every
composite endpoint in the admissible interval. Thus finite survival is
equivalent to Goldbach at the fixed center; existence is not assumed.
-/

namespace DkMath.NumberTheory

/-- Raw left divisibility; its modular interpretation requires `u ≤ n`. -/
def GoldbachLeftObstructed (n r u : ℕ) : Prop := r ∣ n - u

/-- Raw right divisibility. -/
def GoldbachRightObstructed (n r u : ℕ) : Prop := r ∣ n + u

/-- Raw union of the two divisibility waves, before endpoint exceptions. -/
def GoldbachObstructed (n r u : ℕ) : Prop :=
  GoldbachLeftObstructed n r u ∨ GoldbachRightObstructed n r u

/-- A genuine obstruction excludes equality of a prime divisor and its endpoint. -/
def GoldbachProperObstructed (n r u : ℕ) : Prop :=
  (r ∣ n - u ∧ n - u ≠ r) ∨ (r ∣ n + u ∧ n + u ≠ r)

instance (n r u : ℕ) : Decidable (GoldbachProperObstructed n r u) := by
  unfold GoldbachProperObstructed
  infer_instance

/-- The complete finite set of obstruction primes, including the square-root boundary. -/
def goldbachSmallPrimes (n : ℕ) : Finset ℕ :=
  (Finset.range (Nat.sqrt (2 * n) + 1)).filter Nat.Prime

/-- Membership in the cutoff is exactly primality and the square bound. -/
@[simp] theorem mem_goldbachSmallPrimes {n r : ℕ} :
    r ∈ goldbachSmallPrimes n ↔ Nat.Prime r ∧ r ^ 2 ≤ 2 * n := by
  simp only [goldbachSmallPrimes, Finset.mem_filter, Finset.mem_range,
    Nat.lt_succ_iff, Nat.le_sqrt']
  exact and_comm

/-- Every nonprime endpoint above one has a proper small prime divisor. -/
theorem goldbach_small_prime_witness {n m : ℕ}
    (hm : 2 ≤ m) (hbound : m ≤ 2 * n) (hc : ¬ Nat.Prime m) :
    ∃ r ∈ goldbachSmallPrimes n, r ∣ m ∧ m ≠ r := by
  have hp : Nat.Prime m.minFac := Nat.minFac_prime (by omega)
  refine ⟨m.minFac, mem_goldbachSmallPrimes.mpr
    ⟨hp, (Nat.minFac_sq_le_self (by omega) hc).trans hbound⟩,
    Nat.minFac_dvd m, ?_⟩
  intro heq
  exact hc (heq.symm ▸ hp)

/-- A prime endpoint cannot have a proper prime divisor. -/
theorem goldbach_no_proper_divisor_of_prime {m r : ℕ}
    (hm : Nat.Prime m) (hr : Nat.Prime r) : ¬ (r ∣ m ∧ m ≠ r) := by
  rintro ⟨hd, hne⟩
  exact hne ((Nat.prime_dvd_prime_iff_eq hr hm).mp hd).symm

/-- At an admissible seat, failure of the pair is exactly a finite prime obstruction. -/
theorem goldbach_not_prime_pair_iff_obstructed {n u : ℕ}
    (hu : u ∈ goldbachOffsets n) :
    ¬ (Nat.Prime (n - u) ∧ Nat.Prime (n + u)) ↔
      ∃ r ∈ goldbachSmallPrimes n, GoldbachProperObstructed n r u := by
  have hb := goldbachOffset_bounds hu
  constructor
  · intro h
    by_cases hl : Nat.Prime (n - u)
    · have hr : ¬ Nat.Prime (n + u) := fun hr => h ⟨hl, hr⟩
      obtain ⟨r, hr, hd⟩ := goldbach_small_prime_witness hb.2.2.1 hb.2.2.2.2 hr
      exact ⟨r, hr, Or.inr hd⟩
    · obtain ⟨r, hr, hd⟩ := goldbach_small_prime_witness hb.2.1 hb.2.2.2.1 hl
      exact ⟨r, hr, Or.inl hd⟩
  · rintro ⟨r, hr, ho⟩ ⟨hl, hright⟩
    have hp := (mem_goldbachSmallPrimes.mp hr).1
    exact ho.elim (goldbach_no_proper_divisor_of_prime hl hp)
      (goldbach_no_proper_divisor_of_prime hright hp)

/-- Exact survival in a finite world, retaining endpoints equal to a world prime. -/
def GoldbachSurvives (n : ℕ) (S : Finset ℕ) (u : ℕ) : Prop :=
  ∀ r ∈ S, ¬ GoldbachProperObstructed n r u

instance (n : ℕ) (S : Finset ℕ) (u : ℕ) : Decidable (GoldbachSurvives n S u) := by
  unfold GoldbachSurvives
  infer_instance

/-- Executable survivors in the actual interval, as opposed to a full residue period. -/
def goldbachSurvivors (n : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (goldbachOffsets n).filter (GoldbachSurvives n S)

/-- The finite survivor set exposes the interval and proper-divisor conditions. -/
@[simp] theorem mem_goldbachSurvivors {n u : ℕ} {S : Finset ℕ} :
    u ∈ goldbachSurvivors n S ↔ u ∈ goldbachOffsets n ∧ GoldbachSurvives n S u := by
  simp [goldbachSurvivors]

/-- Complete small-prime survival forces both endpoints to be prime. -/
theorem goldbach_survives_iff_prime_pair {n u : ℕ}
    (hu : u ∈ goldbachOffsets n) :
    GoldbachSurvives n (goldbachSmallPrimes n) u ↔
      Nat.Prime (n - u) ∧ Nat.Prime (n + u) := by
  have h := goldbach_not_prime_pair_iff_obstructed hu
  unfold GoldbachSurvives
  constructor
  · intro hs
    by_contra hc
    obtain ⟨r, hr, ho⟩ := h.mp hc
    exact hs r hr ho
  · intro hp r hr ho
    exact (h.mpr ⟨r, hr, ho⟩) hp

/-- Finite nonemptiness is an exact, executable reformulation of the fixed-center conjecture. -/
theorem goldbachPairAt_iff_survivors_nonempty (n : ℕ) :
    GoldbachPairAt n ↔ (goldbachSurvivors n (goldbachSmallPrimes n)).Nonempty := by
  rw [goldbachPairAt_iff_exists_offset]
  constructor
  · rintro ⟨u, hu, hp⟩
    exact ⟨u, mem_goldbachSurvivors.mpr
      ⟨hu, (goldbach_survives_iff_prime_pair hu).mpr hp⟩⟩
  · rintro ⟨u, hu⟩
    rcases mem_goldbachSurvivors.mp hu with ⟨hu, hs⟩
    exact ⟨u, hu, (goldbach_survives_iff_prime_pair hu).mp hs⟩

/-- Complete finite search decides each fixed center, without deciding the universal conjecture. -/
instance (n : ℕ) : Decidable (GoldbachPairAt n) :=
  decidable_of_iff (goldbachSurvivors n (goldbachSmallPrimes n)).Nonempty
    (goldbachPairAt_iff_survivors_nonempty n).symm

/-- The GN fiber inherits the same complete finite decision procedure. -/
instance (n : ℕ) : Decidable (GoldbachGNFiberAt n) :=
  decidable_of_iff (GoldbachPairAt n) (goldbachPairAt_iff_gnFiberAt n)

/-- Goldbach failure is precisely a cover of every admissible seat by proper small divisors. -/
theorem goldbach_failure_iff_finite_cover (n : ℕ) :
    ¬ GoldbachPairAt n ↔
      ∀ u ∈ goldbachOffsets n,
        ∃ r ∈ goldbachSmallPrimes n, GoldbachProperObstructed n r u := by
  rw [goldbachPairAt_iff_exists_offset]
  constructor
  · intro h u hu
    exact (goldbach_not_prime_pair_iff_obstructed hu).mp
      (fun hp => h ⟨u, hu, hp⟩)
  · rintro h ⟨u, hu, hp⟩
    exact (goldbach_not_prime_pair_iff_obstructed hu).mpr (h u hu) hp

/-- Adding more obstruction primes can only remove finite interval survivors. -/
theorem goldbachSurvivors_antitone {n : ℕ} {S T : Finset ℕ} (hST : S ⊆ T) :
    goldbachSurvivors n T ⊆ goldbachSurvivors n S := by
  intro u hu
  rcases mem_goldbachSurvivors.mp hu with ⟨hu, hs⟩
  exact mem_goldbachSurvivors.mpr ⟨hu, fun r hr => hs r (hST hr)⟩

end DkMath.NumberTheory
