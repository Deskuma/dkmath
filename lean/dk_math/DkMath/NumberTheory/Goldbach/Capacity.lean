/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/
import DkMath.NumberTheory.Goldbach.PrimeWorld

#print "file: DkMath.NumberTheory.Goldbach.Capacity"

/-!
# Exact interval capacity and conditional closure

The union counts each obstructed offset once; incidence counts it once for
each obstructing prime. The exact complement identity reduces Goldbach to a
strict union-capacity inequality. An incidence bound is a sufficient, stronger
criterion, and may fail even when Goldbach holds. No universal capacity
inequality is supplied as an axiom or hidden in a data structure.
-/

namespace DkMath.NumberTheory

open scoped BigOperators

/-- Seats blocked by one prime, with proper-divisor endpoint exceptions. -/
def goldbachBlockedSeats (n r : ℕ) : Finset ℕ :=
  (goldbachOffsets n).filter (GoldbachProperObstructed n r)

/-- The exact obstruction cover counts the union without multiplicity. -/
def goldbachCoveredSeats (n : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.biUnion (goldbachBlockedSeats n)

/-- Incidence capacity counts prime-seat incidences, including overlap between primes. -/
def goldbachIncidence (n : ℕ) (S : Finset ℕ) : ℕ :=
  ∑ r ∈ S, (goldbachBlockedSeats n r).card

/-- The cover consists exactly of interval seats failing the survival condition. -/
theorem goldbachCoveredSeats_eq_filter (n : ℕ) (S : Finset ℕ) :
    goldbachCoveredSeats n S =
      (goldbachOffsets n).filter (fun u => ¬ GoldbachSurvives n S u) := by
  ext u
  simp only [goldbachCoveredSeats, Finset.mem_biUnion, goldbachBlockedSeats,
    Finset.mem_filter, GoldbachSurvives]
  constructor
  · rintro ⟨r, hr, hu, ho⟩
    exact ⟨hu, fun hs => hs r hr ho⟩
  · rintro ⟨hu, hs⟩
    push Not at hs
    obtain ⟨r, hr, ho⟩ := hs
    exact ⟨r, hr, hu, ho⟩

/-- Exact conservation of finite seat count into survivors and covered seats. -/
theorem goldbach_survivors_add_covered (n : ℕ) (S : Finset ℕ) :
    (goldbachSurvivors n S).card + (goldbachCoveredSeats n S).card = n - 1 := by
  rw [goldbachCoveredSeats_eq_filter, goldbachSurvivors,
    Finset.card_filter_add_card_filter_not]
  simp [goldbachOffsets]

/-- The union bound is valid globally, but can overcount overlapping obstructions. -/
theorem goldbach_covered_le_incidence (n : ℕ) (S : Finset ℕ) :
    (goldbachCoveredSeats n S).card ≤ goldbachIncidence n S :=
  Finset.card_biUnion_le

/-- Every supplied per-prime bound gives a global incidence upper bound. -/
theorem goldbach_incidence_le_sum {n : ℕ} {S : Finset ℕ} (b : ℕ → ℕ)
    (hb : ∀ r ∈ S, (goldbachBlockedSeats n r).card ≤ b r) :
    goldbachIncidence n S ≤ ∑ r ∈ S, b r :=
  Finset.sum_le_sum hb

/-- Residue and quotient coordinates bound each prime's blocked seats in the finite interval. -/
theorem goldbach_blocked_card_le_residue_capacity (n r : ℕ) :
    (goldbachBlockedSeats n r).card ≤
      (if r ∣ 2 * n then 1 else 2) * ((n - 2) / r + 1) := by
  let T := (goldbachForbiddenResidues n r).product (Finset.range ((n - 2) / r + 1))
  have hcard : (goldbachBlockedSeats n r).card ≤ T.card := by
    apply Finset.card_le_card_of_injOn (fun u : ℕ => ((u : ZMod r), u / r))
    · intro u hu
      rcases Finset.mem_filter.mp hu with ⟨hu, ho⟩
      have hb := goldbachOffset_bounds hu
      have hu_le : u ≤ n - 2 := by
        simp only [goldbachOffsets, Finset.mem_range] at hu
        omega
      refine Finset.mem_product.mpr ⟨?_, Finset.mem_range.mpr ?_⟩
      · apply (goldbach_obstructed_iff_mem_forbidden hb.1).mp
        exact ho.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
      · change u / r < (n - 2) / r + 1
        exact Nat.lt_succ_of_le (Nat.div_le_div_right hu_le)
    · intro u _ v _ he
      have hmod := (ZMod.natCast_eq_natCast_iff' u v r).mp (congrArg Prod.fst he)
      have hdiv : u / r = v / r := congrArg Prod.snd he
      calc
        u = u % r + r * (u / r) := (Nat.mod_add_div u r).symm
        _ = v % r + r * (v / r) := by rw [hmod, hdiv]
        _ = v := Nat.mod_add_div v r
  simpa [T, Finset.card_product, goldbach_card_forbidden] using hcard

/-- The local one-or-two-class counts give a concrete global incidence upper bound. -/
theorem goldbach_incidence_le_residue_capacity (n : ℕ) (S : Finset ℕ) :
    goldbachIncidence n S ≤
      ∑ r ∈ S, (if r ∣ 2 * n then 1 else 2) * ((n - 2) / r + 1) :=
  goldbach_incidence_le_sum _ (fun r _ => goldbach_blocked_card_le_residue_capacity n r)

/-- Exact capacity shortfall is equivalent to the prime-pair statement. -/
theorem goldbachPairAt_iff_covered_card_lt (n : ℕ) :
    GoldbachPairAt n ↔
      (goldbachCoveredSeats n (goldbachSmallPrimes n)).card < n - 1 := by
  rw [goldbachPairAt_iff_survivors_nonempty, ← Finset.card_pos]
  have h := goldbach_survivors_add_covered n (goldbachSmallPrimes n)
  omega

/-- A strict incidence bound is a sufficient certificate for a fixed center. -/
theorem goldbachPairAt_of_incidence_lt {n : ℕ}
    (h : goldbachIncidence n (goldbachSmallPrimes n) < n - 1) : GoldbachPairAt n := by
  apply (goldbachPairAt_iff_covered_card_lt n).mpr
  exact (goldbach_covered_le_incidence n (goldbachSmallPrimes n)).trans_lt h

/-- A supplied sum of local capacities closes the fixed-center conjecture if it is small enough. -/
theorem goldbachPairAt_of_local_capacity {n : ℕ} (b : ℕ → ℕ)
    (hb : ∀ r ∈ goldbachSmallPrimes n, (goldbachBlockedSeats n r).card ≤ b r)
    (hsmall : (∑ r ∈ goldbachSmallPrimes n, b r) < n - 1) : GoldbachPairAt n :=
  goldbachPairAt_of_incidence_lt ((goldbach_incidence_le_sum b hb).trans_lt hsmall)

/-- The precise missing universal statement, defined as a proposition without a provider. -/
def GoldbachCapacityEscape : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (goldbachCoveredSeats n (goldbachSmallPrimes n)).card < n - 1

/-- The exact capacity escape problem has the full logical strength of strong Goldbach. -/
theorem strongGoldbach_iff_capacityEscape : StrongGoldbach ↔ GoldbachCapacityEscape := by
  unfold StrongGoldbach GoldbachCapacityEscape
  exact forall_congr' fun n => forall_congr' fun _ => goldbachPairAt_iff_covered_card_lt n

/-- Conditional final endpoint: an independent universal escape proof would close Goldbach. -/
theorem strongGoldbach_of_capacityEscape (h : GoldbachCapacityEscape) : StrongGoldbach :=
  strongGoldbach_iff_capacityEscape.mpr h

/-- The same conditional closure returns the fixed-center GN formulation. -/
theorem goldbachGNFiberAt_of_capacityEscape (h : GoldbachCapacityEscape)
    {n : ℕ} (hn : 2 ≤ n) : GoldbachGNFiberAt n :=
  (goldbachPairAt_iff_gnFiberAt n).mp (strongGoldbach_of_capacityEscape h n hn)

end DkMath.NumberTheory
