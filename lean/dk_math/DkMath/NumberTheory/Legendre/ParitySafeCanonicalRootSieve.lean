/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeCanonicalRootFiber

#print "file: DkMath.NumberTheory.Legendre.ParitySafeCanonicalRootSieve"

/-! Exact finite exclusions for roots 3, 5, 7, and a generic union bound.
All waves retain candidate coprimality and parity. -/

namespace DkMath.NumberTheory
open scoped BigOperators

/-- Neutral two-exclusion identity: restore intersection credit before Nat subtraction. -/
theorem card_filter_two_exclusions {α : Type*}
    (S : Finset α) (P Q : α → Prop) [DecidablePred P] [DecidablePred Q] :
    (S.filter (fun x => ¬P x ∧ ¬Q x)).card =
      S.card + (S.filter (fun x => P x ∧ Q x)).card -
        ((S.filter P).card + (S.filter Q).card) := by
  classical
  have hinter : S.filter (fun x => P x ∧ Q x) = S.filter P ∩ S.filter Q := by
    ext x; simp only [Finset.mem_filter, Finset.mem_inter]; tauto
  have hgood : S.filter (fun x => ¬P x ∧ ¬Q x) = S \ (S.filter P ∪ S.filter Q) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_union]; tauto
  have hsub : S.filter P ∪ S.filter Q ⊆ S := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h <;> exact (Finset.mem_filter.mp h).1
  have he := Finset.card_union_add_card_inter (S.filter P) (S.filter Q)
  have hle := Finset.card_le_card hsub
  rw [hgood, Finset.card_sdiff_of_subset hsub, hinter]
  omega

/-- Removing a finite union costs at most the sum of its individual costs. -/
theorem card_finite_exclusion_lower {α β : Type*}
    (S : Finset α) (T : Finset β) (P : β → α → Prop) [∀ b, DecidablePred (P b)] :
    S.card - (∑ b ∈ T, (S.filter (P b)).card) ≤
      (S.filter (fun x => ∀ b ∈ T, ¬P b x)).card := by
  classical
  have hg : S.filter (fun x => ∀ b ∈ T, ¬P b x) =
      S \ T.biUnion (fun b => S.filter (P b)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_biUnion]
    constructor
    · rintro ⟨hx, hh⟩
      exact ⟨hx, by rintro ⟨b, hb, _, hP⟩; exact hh b hb hP⟩
    · rintro ⟨hx, hh⟩
      exact ⟨hx, fun b hb hP => hh ⟨b, hb, hx, hP⟩⟩
  have hs : T.biUnion (fun b => S.filter (P b)) ⊆ S := by
    intro x hx
    obtain ⟨b, hb, hx⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_filter.mp hx).1
  rw [hg, Finset.card_sdiff_of_subset hs]
  exact Nat.sub_le_sub_left (Finset.card_biUnion_le) _

end DkMath.NumberTheory

namespace DkMath.NumberTheory.Legendre
open scoped BigOperators

/-- Generic root sieve lower bound; only smaller active primes are charged. -/
theorem canonicalRootPair_card_ge_finite_sieve (n p q : ℕ) :
    (paritySafeProductWaveOffsets n (p * q)).card -
      (∑ a ∈ (squareAnchorOddActivePrimes n).filter (fun a => a < p),
        ((paritySafeProductWaveOffsets n (p * q)).filter (fun r => a ∣ n ^ 2 + r)).card) ≤
      (canonicalRootPairOffsets n p q).card := by
  classical
  have h := card_finite_exclusion_lower (paritySafeProductWaveOffsets n (p * q))
    ((squareAnchorOddActivePrimes n).filter (fun a => a < p))
    (fun a r => a ∣ n ^ 2 + r)
  simpa only [canonicalRootPairOffsets, Finset.mem_filter, and_imp] using h

/-- A finite, computable-by-wave lower estimate for the next canonical root. -/
noncomputable def canonicalRootSieveLower (n p : ℕ) : ℕ :=
  ∑ q ∈ (squareAnchorOddActivePrimes n).filter (fun q => p < q),
    ((paritySafeProductWaveOffsets n (p * q)).card -
      ∑ a ∈ (squareAnchorOddActivePrimes n).filter (fun a => a < p),
        ((paritySafeProductWaveOffsets n (p * q)).filter (fun r => a ∣ n ^ 2 + r)).card)

/-- The union-bound estimate is bounded by the exact existing root fiber. -/
theorem canonicalRootSieveLower_le_fiber {n p : ℕ}
    (hp : p ∈ squareAnchorOddActivePrimes n) :
    canonicalRootSieveLower n p ≤ (canonicalRootFiber n p).card := by
  classical
  rw [canonicalRootFiber_card_eq_sum_pairs hp]
  apply Finset.sum_le_sum
  intro q hq
  exact canonicalRootPair_card_ge_finite_sieve n p q

/-- An arbitrary adaptive finite root selection has a reusable structural lower charge. -/
theorem sum_canonicalRootSieveLower_le_excess {n : ℕ} (R : Finset ℕ)
    (hR : R ⊆ squareAnchorOddActivePrimes n) :
    (∑ p ∈ R, canonicalRootSieveLower n p) ≤ paritySafeSupportExcess n := by
  exact (Finset.sum_le_sum (fun p hp => canonicalRootSieveLower_le_fiber (hR hp))).trans
    (sum_canonicalRootFiber_le_excess n R)

/-- Distinct active primes are coprime. -/
theorem activePrimes_coprime {n a b : ℕ} (ha : a ∈ squareAnchorOddActivePrimes n)
    (hb : b ∈ squareAnchorOddActivePrimes n) (hne : a ≠ b) : Nat.Coprime a b := by
  have hap := (mem_squareAnchorOddActivePrimes.mp ha).1
  have hbp := (mem_squareAnchorOddActivePrimes.mp hb).1
  apply hap.coprime_iff_not_dvd.mpr
  intro hd
  exact hne (((Nat.dvd_prime hbp).mp hd).resolve_left hap.ne_one)

/-- An extra coprime divisor gives exactly the corresponding candidate product wave. -/
theorem productWave_filter_dvd {n a m : ℕ} (hcop : Nat.Coprime a m) :
    (paritySafeProductWaveOffsets n m).filter (fun r => a ∣ n ^ 2 + r) =
      paritySafeProductWaveOffsets n (a * m) := by
  classical
  ext r
  simp only [paritySafeProductWaveOffsets, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hr, hm⟩, ha⟩
    exact ⟨hr, hcop.mul_dvd_of_dvd_of_dvd ha hm⟩
  · rintro ⟨hr, hd⟩
    exact ⟨⟨hr, dvd_trans (dvd_mul_left m a) hd⟩, dvd_trans (dvd_mul_right a m) hd⟩

/-- Active primes below 7 are exactly the applicable initial odd prime labels. -/
theorem activePrime_small_cases {n a : ℕ} (ha : a ∈ squareAnchorOddActivePrimes n)
    (h : a < 7) : a = 3 ∨ a = 5 := by
  have hh := mem_squareAnchorOddActivePrimes.mp ha
  have hodd := hh.1.odd_of_ne_two hh.2.2.2
  obtain ⟨k, hk⟩ := hodd
  have := hh.1.two_le
  omega

/-- Prime anchors above 7 supply the three initial roots. -/
theorem primeAnchor_small_roots {n : ℕ} (hn : n.Prime) (hlarge : 7 < n) :
    3 ∈ squareAnchorOddActivePrimes n ∧ 5 ∈ squareAnchorOddActivePrimes n ∧
      7 ∈ squareAnchorOddActivePrimes n := by
  have H : ∀ p ∈ ({3, 5, 7} : Finset ℕ), p ∈ squareAnchorOddActivePrimes n := by
    intro p hp
    have hpprime : p.Prime := by
      rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hp :
        p = 3 ∨ p = 5 ∨ p = 7) with rfl | rfl | rfl <;> decide
    have hpbound : p ≤ 7 ∧ p ≠ 2 := by
      rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hp :
        p = 3 ∨ p = 5 ∨ p = 7) with rfl | rfl | rfl <;> omega
    apply mem_squareAnchorOddActivePrimes.mpr
    refine ⟨hpprime, by omega, ?_, hpbound.2⟩
    intro hd
    rcases (Nat.dvd_prime hn).mp hd with he | he
    · exact hpprime.ne_one he
    · omega
  exact ⟨H 3 (by simp), H 5 (by simp), H 7 (by simp)⟩

/-- Root 3 has no smaller active contamination. -/
theorem canonicalRoot3Pair_eq (n q : ℕ) :
    canonicalRootPairOffsets n 3 q = paritySafeProductWaveOffsets n (3 * q) := by
  classical
  apply Finset.filter_eq_self.mpr
  intro r hr a ha hlt
  have hh := mem_squareAnchorOddActivePrimes.mp ha
  have := hh.1.two_le
  omega

/-- Root 5 excludes exactly direction 3, provided that direction is active. -/
theorem canonicalRoot5Pair_eq {n q : ℕ} (h3 : 3 ∈ squareAnchorOddActivePrimes n) :
    canonicalRootPairOffsets n 5 q =
      (paritySafeProductWaveOffsets n (5 * q)).filter (fun r => ¬3 ∣ n ^ 2 + r) := by
  classical
  ext r
  simp only [canonicalRootPairOffsets, Finset.mem_filter]
  constructor
  · rintro ⟨hr, hs⟩; exact ⟨hr, hs 3 h3 (by decide)⟩
  · rintro ⟨hr, hs⟩
    refine ⟨hr, ?_⟩
    intro a ha hlt
    rcases activePrime_small_cases ha (by omega) with rfl | rfl
    · exact hs
    · omega

/-- Root 7 excludes exactly directions 3 and 5 when both are active. -/
theorem canonicalRoot7Pair_eq {n q : ℕ}
    (h3 : 3 ∈ squareAnchorOddActivePrimes n) (h5 : 5 ∈ squareAnchorOddActivePrimes n) :
    canonicalRootPairOffsets n 7 q =
      (paritySafeProductWaveOffsets n (7 * q)).filter
        (fun r => ¬3 ∣ n ^ 2 + r ∧ ¬5 ∣ n ^ 2 + r) := by
  classical
  ext r
  simp only [canonicalRootPairOffsets, Finset.mem_filter]
  constructor
  · rintro ⟨hr, hs⟩; exact ⟨hr, hs 3 h3 (by decide), hs 5 h5 (by decide)⟩
  · rintro ⟨hr, hs⟩
    refine ⟨hr, ?_⟩
    intro a ha hlt
    rcases activePrime_small_cases ha hlt with rfl | rfl
    · exact hs.1
    · exact hs.2

/-- Exact one-exclusion count in candidate waves. -/
theorem canonicalRoot5Pair_card {n q : ℕ}
    (h3 : 3 ∈ squareAnchorOddActivePrimes n) (h5 : 5 ∈ squareAnchorOddActivePrimes n)
    (hq : q ∈ squareAnchorOddActivePrimes n) (hgt : 5 < q) :
    (canonicalRootPairOffsets n 5 q).card =
      (paritySafeProductWaveOffsets n (5 * q)).card -
        (paritySafeProductWaveOffsets n (15 * q)).card := by
  classical
  rw [canonicalRoot5Pair_eq h3]
  have he := Finset.card_filter_add_card_filter_not
    (s := paritySafeProductWaveOffsets n (5 * q)) (fun r => 3 ∣ n ^ 2 + r)
  have hcop := (activePrimes_coprime h3 h5 (by decide)).mul_right
    (activePrimes_coprime h3 hq (by omega))
  rw [productWave_filter_dvd hcop] at he
  have hmul : 3 * (5 * q) = 15 * q := by omega
  rw [hmul] at he
  omega

/-- Exact two-exclusion count, with intersection credit before subtraction. -/
theorem canonicalRoot7Pair_card {n q : ℕ}
    (h3 : 3 ∈ squareAnchorOddActivePrimes n) (h5 : 5 ∈ squareAnchorOddActivePrimes n)
    (h7 : 7 ∈ squareAnchorOddActivePrimes n)
    (hq : q ∈ squareAnchorOddActivePrimes n) (hgt : 7 < q) :
    (canonicalRootPairOffsets n 7 q).card =
      (paritySafeProductWaveOffsets n (7 * q)).card +
        (paritySafeProductWaveOffsets n (105 * q)).card -
      ((paritySafeProductWaveOffsets n (21 * q)).card +
        (paritySafeProductWaveOffsets n (35 * q)).card) := by
  classical
  rw [canonicalRoot7Pair_eq h3 h5, card_filter_two_exclusions]
  have hc3 := (activePrimes_coprime h3 h7 (by decide)).mul_right
    (activePrimes_coprime h3 hq (by omega))
  have hc5 := (activePrimes_coprime h5 h7 (by decide)).mul_right
    (activePrimes_coprime h5 hq (by omega))
  have hc35 := (activePrimes_coprime h5 h3 (by decide)).mul_right hc5
  have hi : ((paritySafeProductWaveOffsets n (7 * q)).filter
      (fun r => 3 ∣ n ^ 2 + r ∧ 5 ∣ n ^ 2 + r)) =
      ((paritySafeProductWaveOffsets n (7 * q)).filter (fun r => 3 ∣ n ^ 2 + r)).filter
        (fun r => 5 ∣ n ^ 2 + r) := by ext r; simp [and_assoc]
  rw [hi, productWave_filter_dvd hc3, productWave_filter_dvd hc35,
    productWave_filter_dvd hc5]
  have e1 : 5 * (3 * (7 * q)) = 105 * q := by omega
  have e2 : 3 * (7 * q) = 21 * q := by omega
  have e3 : 5 * (7 * q) = 35 * q := by omega
  rw [e1, e2, e3]

end DkMath.NumberTheory.Legendre
