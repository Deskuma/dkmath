/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeCanonicalRootTail

#print "file: DkMath.NumberTheory.Legendre.ParitySafeCanonicalRootEleven"

namespace DkMath.NumberTheory

/-- Three exclusions, with every positive intersection credit before Nat subtraction. -/
theorem card_filter_three_exclusions {α : Type*} (S : Finset α)
    (P Q R : α → Prop) [DecidablePred P] [DecidablePred Q] [DecidablePred R] :
    (S.filter (fun x => ¬P x ∧ ¬Q x ∧ ¬R x)).card =
      S.card + (S.filter (fun x => P x ∧ Q x)).card +
        (S.filter (fun x => P x ∧ R x)).card + (S.filter (fun x => Q x ∧ R x)).card -
      ((S.filter P).card + (S.filter Q).card + (S.filter R).card +
        (S.filter (fun x => P x ∧ Q x ∧ R x)).card) := by
  classical
  let T := S.filter (fun x => ¬P x ∧ ¬Q x)
  let V := (S.filter R).filter (fun x => ¬P x ∧ ¬Q x)
  have hgood : S.filter (fun x => ¬P x ∧ ¬Q x ∧ ¬R x) = T.filter (fun x => ¬R x) := by
    ext x; simp only [T, Finset.mem_filter]; tauto
  have hV : T.filter R = V := by
    ext x; simp only [T,V,Finset.mem_filter]; tauto
  have hsum := Finset.card_filter_add_card_filter_not (s := T) R
  rw [hV] at hsum
  have ht := card_filter_two_exclusions S P Q
  have hv := card_filter_two_exclusions (S.filter R) P Q
  have htCost : (S.filter P).card + (S.filter Q).card ≤
      S.card + (S.filter (fun x => P x ∧ Q x)).card := by
    have h := Finset.card_union_add_card_inter (S.filter P) (S.filter Q)
    have hle := Finset.card_le_card (Finset.union_subset
      (Finset.filter_subset P S) (Finset.filter_subset Q S))
    have he : S.filter P ∩ S.filter Q = S.filter (fun x => P x ∧ Q x) := by
      ext x; simp only [Finset.mem_inter,Finset.mem_filter]; tauto
    rw [he] at h
    omega
  have hvCost : ((S.filter R).filter P).card + ((S.filter R).filter Q).card ≤
      (S.filter R).card + ((S.filter R).filter (fun x => P x ∧ Q x)).card := by
    have h := Finset.card_union_add_card_inter ((S.filter R).filter P) ((S.filter R).filter Q)
    have hle := Finset.card_le_card (Finset.union_subset
      (Finset.filter_subset P (S.filter R)) (Finset.filter_subset Q (S.filter R)))
    have he : (S.filter R).filter P ∩ (S.filter R).filter Q =
        (S.filter R).filter (fun x => P x ∧ Q x) := by
      ext x; simp only [Finset.mem_inter,Finset.mem_filter]; tauto
    rw [he] at h
    omega
  have ep : (S.filter R).filter P = S.filter (fun x => P x ∧ R x) := by
    ext x; simp only [Finset.mem_filter]; tauto
  have eq : (S.filter R).filter Q = S.filter (fun x => Q x ∧ R x) := by
    ext x; simp only [Finset.mem_filter]; tauto
  have er : (S.filter R).filter (fun x => P x ∧ Q x) =
      S.filter (fun x => P x ∧ Q x ∧ R x) := by
    ext x; simp only [Finset.mem_filter]; tauto
  rw [ep,eq,er] at hv hvCost
  change T.card = _ at ht
  change V.card = _ at hv
  rw [hgood]
  omega

end DkMath.NumberTheory

namespace DkMath.NumberTheory.Legendre
open scoped BigOperators

/-- A product wave surviving directions3,5,7. -/
noncomputable def candidateAvoidThree (n m : ℕ) : Finset ℕ :=
  (paritySafeProductWaveOffsets n m).filter
    (fun r => ¬3 ∣ n ^ 2 + r ∧ ¬5 ∣ n ^ 2 + r ∧ ¬7 ∣ n ^ 2 + r)

/-- Exact three-exclusion wave formula under explicit coprimality hypotheses. -/
theorem candidateAvoidThree_card {n m : ℕ}
    (h3 : Nat.Coprime 3 m) (h5 : Nat.Coprime 5 m) (h7 : Nat.Coprime 7 m) :
    (candidateAvoidThree n m).card =
      (paritySafeProductWaveOffsets n m).card +
      (paritySafeProductWaveOffsets n (15 * m)).card +
      (paritySafeProductWaveOffsets n (21 * m)).card +
      (paritySafeProductWaveOffsets n (35 * m)).card -
      ((paritySafeProductWaveOffsets n (3 * m)).card +
       (paritySafeProductWaveOffsets n (5 * m)).card +
       (paritySafeProductWaveOffsets n (7 * m)).card +
       (paritySafeProductWaveOffsets n (105 * m)).card) := by
  classical
  rw [candidateAvoidThree, card_filter_three_exclusions]
  have H (a b : ℕ) (ha : Nat.Coprime a m) (hab : Nat.Coprime b a) (hb : Nat.Coprime b m) :
      (paritySafeProductWaveOffsets n m).filter
        (fun r => a ∣ n ^ 2 + r ∧ b ∣ n ^ 2 + r) = paritySafeProductWaveOffsets n (b * (a * m)) := by
    rw [← Finset.filter_filter, productWave_filter_dvd ha,
      productWave_filter_dvd (hab.mul_right hb)]
  have hi : (paritySafeProductWaveOffsets n m).filter
      (fun r => 3 ∣ n ^ 2 + r ∧ 5 ∣ n ^ 2 + r ∧ 7 ∣ n ^ 2 + r) =
      ((paritySafeProductWaveOffsets n m).filter
        (fun r => 3 ∣ n ^ 2 + r ∧ 5 ∣ n ^ 2 + r)).filter (fun r => 7 ∣ n ^ 2 + r) := by
    ext r; simp only [Finset.mem_filter]; tauto
  rw [hi, H 3 5 h3 (by decide) h5,
    productWave_filter_dvd ((by decide : Nat.Coprime 7 5).mul_right ((by decide : Nat.Coprime 7 3).mul_right h7))]
  rw [H 3 7 h3 (by decide) h7, H 5 7 h5 (by decide) h7,
    productWave_filter_dvd h3, productWave_filter_dvd h5, productWave_filter_dvd h7]
  norm_num [← Nat.mul_assoc]

/-- No active prime below11 other than3,5,7. -/
theorem activePrime_below_eleven {n a : ℕ} (ha : a ∈ squareAnchorOddActivePrimes n)
    (hlt : a < 11) : a = 3 ∨ a = 5 ∨ a = 7 := by
  have hh := mem_squareAnchorOddActivePrimes.mp ha
  obtain ⟨k,hk⟩ := hh.1.odd_of_ne_two hh.2.2.2
  have := hh.1.two_le
  have hc : a = 3 ∨ a = 5 ∨ a = 7 ∨ a = 9 := by omega
  rcases hc with h | h | h | rfl
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · norm_num at hh

/-- Root11 owns exactly the candidate11q wave surviving3,5,7. -/
theorem canonicalRoot11Pair_eq {n q : ℕ}
    (h3 : 3 ∈ squareAnchorOddActivePrimes n) (h5 : 5 ∈ squareAnchorOddActivePrimes n)
    (h7 : 7 ∈ squareAnchorOddActivePrimes n) :
    canonicalRootPairOffsets n 11 q = candidateAvoidThree n (11 * q) := by
  classical
  ext r
  simp only [canonicalRootPairOffsets,candidateAvoidThree,Finset.mem_filter]
  constructor
  · rintro ⟨hr,hs⟩; exact ⟨hr,hs 3 h3 (by decide),hs 5 h5 (by decide),hs 7 h7 (by decide)⟩
  · rintro ⟨hr,h3',h5',h7'⟩
    refine ⟨hr,?_⟩
    intro a ha hlt
    rcases activePrime_below_eleven ha hlt with rfl | rfl | rfl
    · exact h3'
    · exact h5'
    · exact h7'

/-- Positive pairwise credits, negative singles and triple intersection. -/
theorem canonicalRoot11Pair_card {n q : ℕ}
    (h3 : 3 ∈ squareAnchorOddActivePrimes n) (h5 : 5 ∈ squareAnchorOddActivePrimes n)
    (h7 : 7 ∈ squareAnchorOddActivePrimes n) (h11 : 11 ∈ squareAnchorOddActivePrimes n)
    (hq : q ∈ squareAnchorOddActivePrimes n) (hgt : 11 < q) :
    (canonicalRootPairOffsets n 11 q).card =
      (paritySafeProductWaveOffsets n (11 * q)).card +
      (paritySafeProductWaveOffsets n (165 * q)).card +
      (paritySafeProductWaveOffsets n (231 * q)).card +
      (paritySafeProductWaveOffsets n (385 * q)).card -
      ((paritySafeProductWaveOffsets n (33 * q)).card +
       (paritySafeProductWaveOffsets n (55 * q)).card +
       (paritySafeProductWaveOffsets n (77 * q)).card +
       (paritySafeProductWaveOffsets n (1155 * q)).card) := by
  rw [canonicalRoot11Pair_eq h3 h5 h7,
    candidateAvoidThree_card
      ((activePrimes_coprime h3 h11 (by decide)).mul_right (activePrimes_coprime h3 hq (by omega)))
      ((activePrimes_coprime h5 h11 (by decide)).mul_right (activePrimes_coprime h5 hq (by omega)))
      ((activePrimes_coprime h7 h11 (by decide)).mul_right (activePrimes_coprime h7 hq (by omega)))]
  simp only [← Nat.mul_assoc]

/-- Floor/product-wave normal form for a wave avoiding3,5,7. -/
def primeAnchorAvoidThreeCount (n m : ℕ) : ℕ :=
  primeAnchorProductWaveCount n m + primeAnchorProductWaveCount n (15 * m) +
    primeAnchorProductWaveCount n (21 * m) + primeAnchorProductWaveCount n (35 * m) -
  (primeAnchorProductWaveCount n (3 * m) + primeAnchorProductWaveCount n (5 * m) +
    primeAnchorProductWaveCount n (7 * m) + primeAnchorProductWaveCount n (105 * m))

/-- All secondary primes above11 are retained. -/
noncomputable def canonicalRootCharge11 (n : ℕ) : ℕ :=
  ∑ q ∈ (squareAnchorOddActivePrimes n).filter (fun q => 11 < q),
    primeAnchorAvoidThreeCount n (11 * q)

/-- Exact floor normal form for the three-exclusion wave. -/
theorem candidateAvoidThree_card_eq_count {n m : ℕ} (hn : n.Prime) (hlarge : 7 < n)
    (hm : Odd m) (hnm : Nat.Coprime n m)
    (h3m : Nat.Coprime 3 m) (h5m : Nat.Coprime 5 m) (h7m : Nat.Coprime 7 m) :
    (candidateAvoidThree n m).card = primeAnchorAvoidThreeCount n m := by
  obtain ⟨h3,h5,h7⟩ := primeAnchor_small_roots hn hlarge
  have hc3 : Nat.Coprime n 3 := ((mem_squareAnchorOddActivePrimes.mp h3).1.coprime_iff_not_dvd.mpr
    (mem_squareAnchorOddActivePrimes.mp h3).2.2.1).symm
  have hc5 : Nat.Coprime n 5 := ((mem_squareAnchorOddActivePrimes.mp h5).1.coprime_iff_not_dvd.mpr
    (mem_squareAnchorOddActivePrimes.mp h5).2.2.1).symm
  have hc7 : Nat.Coprime n 7 := ((mem_squareAnchorOddActivePrimes.mp h7).1.coprime_iff_not_dvd.mpr
    (mem_squareAnchorOddActivePrimes.mp h7).2.2.1).symm
  have H : ∀ k ∈ ({1,3,5,7,15,21,35,105} : Finset ℕ),
      (paritySafeProductWaveOffsets n (k * m)).card = primeAnchorProductWaveCount n (k * m) := by
    intro k hk
    have ho : Odd k := by
      rcases (by simpa only [Finset.mem_insert,Finset.mem_singleton] using hk :
        k=1 ∨ k=3 ∨ k=5 ∨ k=7 ∨ k=15 ∨ k=21 ∨ k=35 ∨ k=105) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hc : Nat.Coprime n k := by
      rcases (by simpa only [Finset.mem_insert,Finset.mem_singleton] using hk :
        k=1 ∨ k=3 ∨ k=5 ∨ k=7 ∨ k=15 ∨ k=21 ∨ k=35 ∨ k=105) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp
      · exact hc3
      · exact hc5
      · exact hc7
      · exact hc3.mul_right hc5
      · exact hc3.mul_right hc7
      · exact hc5.mul_right hc7
      · exact (hc3.mul_right hc5).mul_right hc7
    exact paritySafeProductWave_card_eq_count hn (hn.odd_of_ne_two (by omega)) (ho.mul hm)
      (hc.mul_right hnm)
  have h1 := H 1 (by simp)
  simp only [Nat.one_mul] at h1
  rw [candidateAvoidThree_card h3m h5m h7m, h1, H 15 (by simp), H 21 (by simp),
    H 35 (by simp), H 3 (by simp), H 5 (by simp), H 7 (by simp), H 105 (by simp)]
  rfl

/-- Root11 is active at prime anchors above11. -/
theorem primeAnchor_root11 {n : ℕ} (hn : n.Prime) (hlt : 11 < n) :
    11 ∈ squareAnchorOddActivePrimes n := by
  apply mem_squareAnchorOddActivePrimes.mpr
  refine ⟨by decide,by omega,?_,by decide⟩
  intro hd
  rcases (Nat.dvd_prime hn).mp hd with h | h <;> omega

/-- Root11 total charge equals its existing exact incidence fiber. -/
theorem canonicalRootCharge11_eq_fiber {n : ℕ} (hn : n.Prime) (hlarge : 11 < n) :
    canonicalRootCharge11 n = (canonicalRootFiber n 11).card := by
  classical
  obtain ⟨h3,h5,h7⟩ := primeAnchor_small_roots hn (by omega)
  have h11 := primeAnchor_root11 hn hlarge
  rw [canonicalRootFiber_card_eq_sum_pairs h11]
  unfold canonicalRootCharge11
  apply Finset.sum_congr rfl
  intro q hq
  obtain ⟨hqa,hgt⟩ := Finset.mem_filter.mp hq
  rw [canonicalRoot11Pair_eq h3 h5 h7]
  symm
  apply candidateAvoidThree_card_eq_count hn (by omega)
  · exact (by decide : Odd 11).mul
      ((mem_squareAnchorOddActivePrimes.mp hqa).1.odd_of_ne_two
        (mem_squareAnchorOddActivePrimes.mp hqa).2.2.2)
  · have hc11 : Nat.Coprime n 11 := ((mem_squareAnchorOddActivePrimes.mp h11).1.coprime_iff_not_dvd.mpr
      (mem_squareAnchorOddActivePrimes.mp h11).2.2.1).symm
    exact hc11.mul_right ((mem_squareAnchorOddActivePrimes.mp hqa).1.coprime_iff_not_dvd.mpr
      (mem_squareAnchorOddActivePrimes.mp hqa).2.2.1).symm
  · exact (activePrimes_coprime h3 h11 (by decide)).mul_right (activePrimes_coprime h3 hqa (by omega))
  · exact (activePrimes_coprime h5 h11 (by decide)).mul_right (activePrimes_coprime h5 hqa (by omega))
  · exact (activePrimes_coprime h7 h11 (by decide)).mul_right (activePrimes_coprime h7 hqa (by omega))

/-- Four exact roots provide a structural excess lower charge. -/
theorem canonicalFourRootCharges_le_excess {n : ℕ} (hn : n.Prime) (hlt : 11 < n) :
    canonicalRootCharge3 n + canonicalRootCharge5 n + canonicalRootCharge7 n + canonicalRootCharge11 n ≤
      paritySafeSupportExcess n := by
  classical
  obtain ⟨h3,h5,h7⟩ := canonicalSmallRootCharges_eq_fibers hn (by omega)
  rw [h3,h5,h7,canonicalRootCharge11_eq_fiber hn hlt]
  simpa [Finset.sum_insert,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
    sum_canonicalRootFiber_le_excess n {3,5,7,11}

/-- Exact active roots at the four calibration cutoffs. -/
theorem activePrimes_smallCutoff {n P : ℕ} (hn : n.Prime) (hlt : 11 < n)
    (hP : P ∈ ({3,5,7,11} : Finset ℕ)) :
    (squareAnchorOddActivePrimes n).filter (fun p => p ≤ P) =
      ({3,5,7,11} : Finset ℕ).filter (fun p => p ≤ P) := by
  classical
  obtain ⟨h3,h5,h7⟩ := primeAnchor_small_roots hn (by omega)
  have h11 := primeAnchor_root11 hn hlt
  have hPle : P ≤ 11 := by
    rcases (by simpa only [Finset.mem_insert,Finset.mem_singleton] using hP :
      P=3 ∨ P=5 ∨ P=7 ∨ P=11) with rfl | rfl | rfl | rfl <;> omega
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hp,hb⟩
    refine ⟨?_,hb⟩
    by_cases he : p=11
    · simp [he]
    · rcases activePrime_below_eleven hp (by omega) with rfl | rfl | rfl <;> simp
  · rintro ⟨hp,hb⟩
    refine ⟨?_,hb⟩
    rcases (by simpa only [Finset.mem_insert,Finset.mem_singleton] using hp :
      p=3 ∨ p=5 ∨ p=7 ∨ p=11) with rfl | rfl | rfl | rfl
    · exact h3
    · exact h5
    · exact h7
    · exact h11

/-- Cumulative charge at all four cutoffs is an exact head cardinality. -/
theorem canonicalSmallHeads_eq_charges {n : ℕ} (hn : n.Prime) (hlt : 11 < n) :
    (canonicalRootHead n 3).card = canonicalRootCharge3 n ∧
    (canonicalRootHead n 5).card = canonicalRootCharge3 n + canonicalRootCharge5 n ∧
    (canonicalRootHead n 7).card = canonicalRootCharge3 n + canonicalRootCharge5 n + canonicalRootCharge7 n ∧
    (canonicalRootHead n 11).card = canonicalRootCharge3 n + canonicalRootCharge5 n +
      canonicalRootCharge7 n + canonicalRootCharge11 n := by
  classical
  obtain ⟨h3,h5,h7⟩ := canonicalSmallRootCharges_eq_fibers hn (by omega)
  have h11 := canonicalRootCharge11_eq_fiber hn hlt
  have H (P : ℕ) (hP : P ∈ ({3,5,7,11} : Finset ℕ)) :
      (canonicalRootHead n P).card =
        ∑ p ∈ ({3,5,7,11} : Finset ℕ).filter (fun p => p ≤ P), (canonicalRootFiber n p).card := by
    rw [canonicalRootHead_card_eq_root_sum,activePrimes_smallCutoff hn hlt hP]
  have f3 : ({3,5,7,11}:Finset ℕ).filter (fun p => p ≤ 3) = {3} := by decide
  have f5 : ({3,5,7,11}:Finset ℕ).filter (fun p => p ≤ 5) = {3,5} := by decide
  have f7 : ({3,5,7,11}:Finset ℕ).filter (fun p => p ≤ 7) = {3,5,7} := by decide
  have f11 : ({3,5,7,11}:Finset ℕ).filter (fun p => p ≤ 11) = {3,5,7,11} := by decide
  refine ⟨?_,?_,?_,?_⟩
  · rw [H 3 (by simp),f3]
    simp [← h3]
  · rw [H 5 (by simp),f5]
    simp [← h3,← h5]
  · rw [H 7 (by simp),f7]
    simp [← h3,← h5,← h7,Nat.add_assoc]
  · rw [H 11 (by simp),f11]
    simp [← h3,← h5,← h7,← h11,Nat.add_assoc]

end DkMath.NumberTheory.Legendre
