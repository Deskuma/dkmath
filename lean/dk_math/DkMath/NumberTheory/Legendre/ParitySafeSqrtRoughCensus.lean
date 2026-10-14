/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeSqrtRoughSingleton

#print "file: DkMath.NumberTheory.Legendre.ParitySafeSqrtRoughCensus"

namespace DkMath.NumberTheory.Legendre
open scoped BigOperators
open DkMath.NumberTheory

/-- Three rough labels, allowing repetitions, reconstruct the actual carrier and exact support. -/
theorem sqrt_rough_three_factor_packet {n p q s : ℕ}
    (hp : p ∈ roughActiveLabels n (Nat.sqrt n))
    (hq : q ∈ roughActiveLabels n (Nat.sqrt n))
    (hs : s ∈ roughActiveLabels n (Nat.sqrt n))
    (hlo : n ^ 2 < p * q * s) (hhi : p * q * s ≤ n ^ 2 + 2 * n) :
    p * q * s - n ^ 2 ∈ canonicalRoughCandidates n (Nat.sqrt n) ∧
      paritySafeActiveSupport n (p * q * s - n ^ 2) = {p, q, s} := by
  obtain ⟨hpA, hpgt⟩ := Finset.mem_filter.mp hp
  obtain ⟨hqA, hqgt⟩ := Finset.mem_filter.mp hq
  obtain ⟨hsA, hsgt⟩ := Finset.mem_filter.mp hs
  have hpP := (mem_squareAnchorOddActivePrimes.mp hpA).1
  have hqP := (mem_squareAnchorOddActivePrimes.mp hqA).1
  have hsP := (mem_squareAnchorOddActivePrimes.mp hsA).1
  have he : n ^ 2 + (p * q * s - n ^ 2) = p * q * s := by omega
  have hdiv (u : ℕ) (hu : u.Prime) : u ∣ p * q * s ↔ u = p ∨ u = q ∨ u = s := by
    rw [hu.dvd_mul, hu.dvd_mul, Nat.prime_dvd_prime_iff_eq hu hpP,
      Nat.prime_dvd_prime_iff_eq hu hqP, Nat.prime_dvd_prime_iff_eq hu hsP]
    tauto
  constructor
  · apply sqrt_rough_of_reduced_point
    · dsimp only [SquareOffset]; omega
    · rw [he]
      exact ((activePrime_reducedResidue_packet hpA).2.2.2.2.mul_right
        (activePrime_reducedResidue_packet hqA).2.2.2.2).mul_right
          (activePrime_reducedResidue_packet hsA).2.2.2.2
    · intro u hu hd
      rw [he, hdiv u hu] at hd
      rcases hd with rfl | rfl | rfl <;> assumption
  · ext u
    rw [mem_paritySafeActiveSupport_iff_dvd, he]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hu, hd⟩; exact (hdiv u (mem_squareAnchorOddActivePrimes.mp hu).1).mp hd
    · intro hu
      rcases hu with hu | hu | hu
      · rw [hu]; exact ⟨hpA, (dvd_mul_right p q).trans (dvd_mul_right (p * q) s)⟩
      · rw [hu]; exact ⟨hqA, (dvd_mul_left q p).trans (dvd_mul_right (p * q) s)⟩
      · rw [hu]; exact ⟨hsA, dvd_mul_left s (p * q)⟩

/-- false repeats the smaller label, true repeats the larger one. -/
def sqrtRepeatedProduct (a : (ℕ × ℕ) × Bool) : ℕ :=
  if a.2 then a.1.1 * a.1.2 ^ 2 else a.1.1 ^ 2 * a.1.2

noncomputable def sqrtRoughRepeatedKeys (n : ℕ) : Finset ((ℕ × ℕ) × Bool) :=
  ((roughPairs n (Nat.sqrt n)).product Finset.univ).filter
    (fun a => n ^ 2 < sqrtRepeatedProduct a ∧ sqrtRepeatedProduct a ≤ n ^ 2 + 2 * n)

theorem sqrt_repeated_offset_packet {n : ℕ} {a : (ℕ × ℕ) × Bool}
    (ha : a ∈ sqrtRoughRepeatedKeys n) :
    sqrtRepeatedProduct a - n ^ 2 ∈ roughDoubleSeats n ∧
      paritySafeActiveSupport n (sqrtRepeatedProduct a - n ^ 2) = {a.1.1, a.1.2} := by
  obtain ⟨ha, hlo, hhi⟩ := Finset.mem_filter.mp ha
  obtain ⟨hp, hq, hpq⟩ := mem_roughPairs.mp (Finset.mem_product.mp ha).1
  rcases a with ⟨⟨p, q⟩, b⟩
  cases b
  · simp only [sqrtRepeatedProduct, Bool.false_eq_true, ↓reduceIte] at hlo hhi ⊢
    have h := sqrt_rough_three_factor_packet hp hp hq
      (by nlinarith [hlo]) (by nlinarith [hhi])
    have he : p * p * q = p ^ 2 * q := by ring
    rw [he] at h
    have hS : paritySafeActiveSupport n (p ^ 2 * q - n ^ 2) = {p, q} := by simpa using h.2
    exact ⟨Finset.mem_filter.mpr ⟨h.1, by rw [hS]; simp [hpq.ne]⟩, hS⟩
  · simp only [sqrtRepeatedProduct, ↓reduceIte] at hlo hhi ⊢
    have h := sqrt_rough_three_factor_packet hp hq hq
      (by nlinarith [hlo]) (by nlinarith [hhi])
    have he : p * q * q = p * q ^ 2 := by ring
    rw [he] at h
    have hS : paritySafeActiveSupport n (p * q ^ 2 - n ^ 2) = {p, q} := by simpa using h.2
    exact ⟨Finset.mem_filter.mpr ⟨h.1, by rw [hS]; simp [hpq.ne]⟩, hS⟩

/-- Sorted support labels fix the pair; cancellation then fixes the repetition side. -/
theorem sqrt_repeated_keys_offset_injective (n : ℕ) :
    Set.InjOn (fun a => sqrtRepeatedProduct a - n ^ 2) (sqrtRoughRepeatedKeys n) := by
  intro a ha b hb he
  dsimp only at he
  obtain ⟨haP, haLo, _⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbP, hbLo, _⟩ := Finset.mem_filter.mp hb
  obtain ⟨hp, hq, hpq⟩ := mem_roughPairs.mp (Finset.mem_product.mp haP).1
  obtain ⟨hx, hy, hxy⟩ := mem_roughPairs.mp (Finset.mem_product.mp hbP).1
  have hS := (sqrt_repeated_offset_packet ha).2
  have hT := (sqrt_repeated_offset_packet hb).2
  rw [he] at hS
  have hST := hS.symm.trans hT
  have hpa : a.1.1 = b.1.1 := by
    have h₁ : a.1.1 ∈ ({b.1.1, b.1.2} : Finset ℕ) := hST ▸ Finset.mem_insert_self _ _
    have h₂ : b.1.1 ∈ ({a.1.1, a.1.2} : Finset ℕ) := hST.symm ▸ Finset.mem_insert_self _ _
    simp only [Finset.mem_insert, Finset.mem_singleton] at h₁ h₂
    rcases h₁ with h₁ | h₁
    · exact h₁
    · rcases h₂ with h₂ | h₂
      · exact False.elim (hxy.ne (h₂.trans h₁))
      · have hab : a.1.1 < b.1.1 := by simpa only [h₂] using hpq
        have hba : b.1.1 < a.1.1 := by simpa only [h₁] using hxy
        exact False.elim (lt_asymm hab hba)
  have hqa : a.1.2 = b.1.2 := by
    have h₁ : a.1.2 ∈ ({b.1.1, b.1.2} : Finset ℕ) := hST ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have h₂ : b.1.2 ∈ ({a.1.1, a.1.2} : Finset ℕ) := hST.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    simp only [Finset.mem_insert, Finset.mem_singleton] at h₁ h₂
    rcases h₁ with h₁ | h₁
    · exact False.elim (hpq.ne (hpa.trans h₁.symm))
    · exact h₁
  have hprod : sqrtRepeatedProduct a = sqrtRepeatedProduct b := by omega
  have hpPos := (mem_squareAnchorOddActivePrimes.mp (Finset.mem_filter.mp hp).1).1.pos
  have hqPos := (mem_squareAnchorOddActivePrimes.mp (Finset.mem_filter.mp hq).1).1.pos
  rcases a with ⟨⟨p, q⟩, s⟩
  rcases b with ⟨⟨x, y⟩, t⟩
  dsimp only at hpa hqa hpq hxy hpPos hqPos
  subst x; subst y
  suffices s = t by subst t; rfl
  cases s <;> cases t <;> try rfl
  all_goals
    simp only [sqrtRepeatedProduct, Bool.false_eq_true, ↓reduceIte] at hprod
    have hcancel : p = q := by
      apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hpPos hqPos)
      nlinarith [hprod]
    omega

/-- For a fixed sorted pair, even the two repetition sides jointly occupy at most one seat. -/
theorem sqrt_repeated_pair_occupancy {n p q : ℕ}
    (hpair : (p, q) ∈ roughPairs n (Nat.sqrt n)) :
    ((sqrtRoughRepeatedKeys n).filter (fun a => a.1 = (p, q))).card ≤ 1 := by
  classical
  have hmap : Set.MapsTo (fun a => sqrtRepeatedProduct a - n ^ 2)
      ((sqrtRoughRepeatedKeys n).filter (fun a => a.1 = (p, q)))
      (roughPairWave n (Nat.sqrt n) p q) := by
    intro a ha
    obtain ⟨ha, he⟩ := Finset.mem_filter.mp ha
    have h := sqrt_repeated_offset_packet ha
    apply Finset.mem_filter.mpr
    refine ⟨(Finset.mem_filter.mp h.1).1, (roughPair_support_iff_product hpair).mp ?_⟩
    rw [h.2]
    rw [he]
    have hpq := (mem_roughPairs.mp hpair).2.2
    simp only [Internal.upperPairs, Finset.mem_filter, Finset.mem_offDiag,
      Finset.mem_insert, Finset.mem_singleton]
    exact ⟨⟨Or.inl trivial, Or.inr trivial, hpq.ne⟩, hpq⟩
  have hinj : Set.InjOn (fun a => sqrtRepeatedProduct a - n ^ 2)
      ((sqrtRoughRepeatedKeys n).filter (fun a => a.1 = (p, q))) := by
    intro a ha b hb he
    exact sqrt_repeated_keys_offset_injective n (Finset.mem_filter.mp ha).1
      (Finset.mem_filter.mp hb).1 he
  exact (Finset.card_le_card_of_injOn _ hmap hinj).trans (sqrt_roughPairWave_card_le_one hpair)

noncomputable def roughRepeatedSeats (n : ℕ) : Finset ℕ :=
  (sqrtRoughRepeatedKeys n).image (fun a => sqrtRepeatedProduct a - n ^ 2)

theorem rough_double_eq_repeated_seats (n : ℕ) : roughDoubleSeats n = roughRepeatedSeats n := by
  classical
  ext r
  constructor
  · intro hr
    obtain ⟨hrR, hc⟩ := Finset.mem_filter.mp hr
    obtain ⟨p, q, hne, hS⟩ := Finset.card_eq_two.mp hc
    have hsorted : ∃ p q, p < q ∧ paritySafeActiveSupport n r = {p, q} := by
      by_cases h : p < q
      · exact ⟨p, q, h, hS⟩
      · exact ⟨q, p, by omega, by rw [hS]; exact Finset.pair_comm _ _⟩
    obtain ⟨p, q, hpq, hS⟩ := hsorted
    have hp : p ∈ paritySafeActiveSupport n r := by rw [hS]; simp
    have hq : q ∈ paritySafeActiveSupport n r := by rw [hS]; simp
    have hkey := mem_roughPairs.mpr ⟨rough_support_subset_labels hrR hp,
      rough_support_subset_labels hrR hq, hpq⟩
    have hs := squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets (Finset.mem_filter.mp hrR).1
    dsimp only [SquareOffset] at hs
    rcases sqrt_two_support_repeated_prime hrR hkey hS with he | he
    · apply Finset.mem_image.mpr
      refine ⟨((p, q), false), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hkey, Finset.mem_univ _⟩, ?_⟩, ?_⟩
      · simp only [sqrtRepeatedProduct, Bool.false_eq_true, ↓reduceIte]; omega
      · simp only [sqrtRepeatedProduct, Bool.false_eq_true, ↓reduceIte]; omega
    · apply Finset.mem_image.mpr
      refine ⟨((p, q), true), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hkey, Finset.mem_univ _⟩, ?_⟩, ?_⟩
      · simp only [sqrtRepeatedProduct, ↓reduceIte]; omega
      · simp only [sqrtRepeatedProduct, ↓reduceIte]; omega
  · intro hr
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
    exact (sqrt_repeated_offset_packet ha).1

theorem rough_double_card_eq_repeated (n : ℕ) :
    (roughDoubleSeats n).card = (sqrtRoughRepeatedKeys n).card := by
  rw [rough_double_eq_repeated_seats, roughRepeatedSeats,
    Finset.card_image_of_injOn (sqrt_repeated_keys_offset_injective n)]

theorem sqrt_triple_offset_packet {n : ℕ} {a : ℕ × ℕ × ℕ}
    (ha : a ∈ sqrtRoughTripleProductsInShell n) :
    a.1 * a.2.1 * a.2.2 - n ^ 2 ∈ roughTripleSeats n ∧
      paritySafeActiveSupport n (a.1 * a.2.1 * a.2.2 - n ^ 2) = {a.1, a.2.1, a.2.2} := by
  obtain ⟨ha, hlo, hhi⟩ := Finset.mem_filter.mp ha
  obtain ⟨hp, hq, hs, hpq, hqs⟩ := mem_roughTriples.mp ha
  have h := sqrt_rough_three_factor_packet hp hq hs hlo hhi
  exact ⟨Finset.mem_filter.mpr ⟨h.1, by rw [h.2]; simp [hpq.ne, hqs.ne, (hpq.trans hqs).ne]⟩, h.2⟩

theorem sqrt_triple_keys_offset_injective (n : ℕ) :
    Set.InjOn (fun a : ℕ × ℕ × ℕ => a.1 * a.2.1 * a.2.2 - n ^ 2)
      (sqrtRoughTripleProductsInShell n) := by
  intro a ha b hb he
  dsimp only at he
  have hS := (sqrt_triple_offset_packet ha).2
  have hT := (sqrt_triple_offset_packet hb).2
  rw [he] at hS
  obtain ⟨_, _, _, hapq, haqs⟩ := mem_roughTriples.mp (Finset.mem_filter.mp ha).1
  obtain ⟨_, _, _, hbpq, hbqs⟩ := mem_roughTriples.mp (Finset.mem_filter.mp hb).1
  have h := congrArg upperTriples (hS.symm.trans hT)
  rw [upperTriples_three hapq haqs, upperTriples_three hbpq hbqs] at h
  exact Finset.singleton_injective h

noncomputable def roughTripleProductSeats (n : ℕ) : Finset ℕ :=
  (sqrtRoughTripleProductsInShell n).image (fun a => a.1 * a.2.1 * a.2.2 - n ^ 2)

theorem rough_triple_eq_product_seats (n : ℕ) : roughTripleSeats n = roughTripleProductSeats n := by
  classical
  ext r
  constructor
  · intro hr
    obtain ⟨hrR, hc⟩ := Finset.mem_filter.mp hr
    obtain ⟨p, q, s, hpq, hqs, hS⟩ := exists_ordered_triple_of_card_three hc
    have hsupport : (p, q, s) ∈ upperTriples (paritySafeActiveSupport n r) := by
      rw [hS, upperTriples_three hpq hqs]; simp
    have hp : p ∈ paritySafeActiveSupport n r := by rw [hS]; simp
    have hq : q ∈ paritySafeActiveSupport n r := by rw [hS]; simp
    have hs : s ∈ paritySafeActiveSupport n r := by rw [hS]; simp
    have hkey := mem_roughTriples.mpr ⟨rough_support_subset_labels hrR hp,
      rough_support_subset_labels hrR hq, rough_support_subset_labels hrR hs, hpq, hqs⟩
    have he := sqrt_roughTriple_point_eq_product hrR hkey hsupport
    have hwindow := squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets (Finset.mem_filter.mp hrR).1
    dsimp only [SquareOffset] at hwindow
    exact Finset.mem_image.mpr ⟨(p, q, s), Finset.mem_filter.mpr ⟨hkey, by dsimp only; omega, by dsimp only; omega⟩, by dsimp only; omega⟩
  · intro hr
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
    exact (sqrt_triple_offset_packet ha).1

theorem rough_triple_card_eq_products (n : ℕ) :
    (roughTripleSeats n).card = (sqrtRoughTripleProductsInShell n).card := by
  rw [rough_triple_eq_product_seats, roughTripleProductSeats,
    Finset.card_image_of_injOn (sqrt_triple_keys_offset_injective n)]

/-- Explicit disjointness of all five seat images in the complete census. -/
theorem sqrt_product_seats_pairwise_disjoint (n : ℕ) :
    Disjoint (paritySafeUncoveredCandidates n) (roughCubeSeats n) ∧
    Disjoint (paritySafeUncoveredCandidates n) (roughCrossSeats n) ∧
    Disjoint (paritySafeUncoveredCandidates n) (roughRepeatedSeats n) ∧
    Disjoint (paritySafeUncoveredCandidates n) (roughTripleProductSeats n) ∧
    Disjoint (roughCubeSeats n) (roughCrossSeats n) ∧
    Disjoint (roughCubeSeats n) (roughRepeatedSeats n) ∧
    Disjoint (roughCubeSeats n) (roughTripleProductSeats n) ∧
    Disjoint (roughCrossSeats n) (roughRepeatedSeats n) ∧
    Disjoint (roughCrossSeats n) (roughTripleProductSeats n) ∧
    Disjoint (roughRepeatedSeats n) (roughTripleProductSeats n) := by
  have hC : roughCubeSeats n ⊆ roughSingletonSeats n := by
    rw [rough_singleton_eq_cube_union_cross]; exact Finset.subset_union_left
  have hX : roughCrossSeats n ⊆ roughSingletonSeats n := by
    rw [rough_singleton_eq_cube_union_cross]; exact Finset.subset_union_right
  obtain ⟨h0S, h0D, h0T, hSD, hST, hDT⟩ := rough_strata_pairwise_disjoint n
  rw [← roughZeroSeats_eq_uncovered, ← rough_double_eq_repeated_seats,
    ← rough_triple_eq_product_seats]
  exact ⟨h0S.mono_right hC, h0S.mono_right hX, h0D, h0T,
    rough_cube_cross_disjoint n, hSD.mono_left hC, hST.mono_left hC,
    hSD.mono_left hX, hST.mono_left hX, hDT⟩

theorem sqrt_product_seats_union (n : ℕ) :
    paritySafeUncoveredCandidates n ∪ roughCubeSeats n ∪ roughCrossSeats n ∪
      roughRepeatedSeats n ∪ roughTripleProductSeats n = canonicalRoughCandidates n (Nat.sqrt n) := by
  rw [← rough_strata_union, roughZeroSeats_eq_uncovered, rough_singleton_eq_cube_union_cross,
    rough_double_eq_repeated_seats, rough_triple_eq_product_seats]
  simp only [Finset.union_assoc]

/-- The zero stratum reuses the established support-escape prime criterion. -/
theorem sqrt_zero_point_prime {n r : ℕ} (hr : r ∈ roughZeroSeats n) :
    (n ^ 2 + r).Prime ∧ SquareCell n (n ^ 2 + r) := by
  have hs := squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets
    (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1
  have hn : 0 < n := by dsimp only [SquareOffset] at hs; omega
  have hu : r ∈ paritySafeUncoveredCandidates n := by
    rwa [roughZeroSeats_eq_uncovered] at hr
  have hm := (mem_paritySafeUncoveredCandidates_iff hn).mp hu
  have hd := supportDisjointFrom_primeScalesUpTo_square_add_iff_not_covered.mpr hm.2
  exact ⟨prime_of_squareAnchoredSupportEscape hn hs hd,
    (squareCell_iff_exists_squareOffset n (n ^ 2 + r)).mpr ⟨r, hs, rfl⟩⟩

/-- Every actual rough point belongs to exactly one of the disjoint arithmetic types.
Disjointness follows from the four support strata and `rough_cube_cross_disjoint`. -/
theorem sqrt_rough_point_factorization {n r : ℕ}
    (hr : r ∈ canonicalRoughCandidates n (Nat.sqrt n)) :
    (r ∈ paritySafeUncoveredCandidates n ∧ (n ^ 2 + r).Prime ∧ SquareCell n (n ^ 2 + r)) ∨
    (∃ p ∈ sqrtRoughCubeKeys n, n ^ 2 + r = p ^ 3) ∨
    (∃ a ∈ sqrtRoughCrossKeys n, n ^ 2 + r = a.1 * a.2) ∨
    (∃ a ∈ sqrtRoughRepeatedKeys n, n ^ 2 + r = sqrtRepeatedProduct a) ∨
    (∃ a ∈ sqrtRoughTripleProductsInShell n, n ^ 2 + r = a.1 * a.2.1 * a.2.2) := by
  classical
  have hwindow := squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets (Finset.mem_filter.mp hr).1
  dsimp only [SquareOffset] at hwindow
  rw [← rough_strata_union] at hr
  rcases Finset.mem_union.mp hr with hr | hr
  · rcases Finset.mem_union.mp hr with hr | hr
    · rcases Finset.mem_union.mp hr with hr | hr
      · exact Or.inl ⟨by rwa [roughZeroSeats_eq_uncovered] at hr, sqrt_zero_point_prime hr⟩
      · rw [rough_singleton_eq_cube_union_cross] at hr
        rcases Finset.mem_union.mp hr with hr | hr
        · obtain ⟨p, hp, he⟩ := Finset.mem_image.mp hr
          have hlo := (Finset.mem_filter.mp hp).2.1
          exact Or.inr (Or.inl ⟨p, hp, by omega⟩)
        · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hr
          have hlo := (mem_sqrtRoughCrossKeys.mp ha).2.2.2.1
          exact Or.inr (Or.inr (Or.inl ⟨a, ha, by omega⟩))
    · rw [rough_double_eq_repeated_seats] at hr
      obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hr
      have hlo := (Finset.mem_filter.mp ha).2.1
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, ha, by omega⟩)))
  · rw [rough_triple_eq_product_seats] at hr
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hr
    have hlo := (Finset.mem_filter.mp ha).2.1
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, ha, by omega⟩)))

/-- The complete additive census uses the existing uncovered class and four arithmetic key types. -/
theorem sqrt_rough_factorization_census (n : ℕ) :
    (canonicalRoughCandidates n (Nat.sqrt n)).card = (paritySafeUncoveredCandidates n).card +
      (sqrtRoughCubeKeys n).card + (sqrtRoughCrossKeys n).card +
      (sqrtRoughRepeatedKeys n).card + (sqrtRoughTripleProductsInShell n).card := by
  rw [rough_strata_card, roughZeroSeats_eq_uncovered, rough_singleton_card_eq_cube_cross,
    rough_double_card_eq_repeated, rough_triple_card_eq_products]
  omega

theorem sqrt_product_pairMoment (n : ℕ) :
    roughPairMoment n (Nat.sqrt n) = (sqrtRoughRepeatedKeys n).card +
      3 * (sqrtRoughTripleProductsInShell n).card := by
  rw [rough_pairMoment_eq_strata, rough_double_card_eq_repeated, rough_triple_card_eq_products]

theorem sqrt_product_incidence (n : ℕ) :
    (∑ q ∈ squareAnchorOddActivePrimes n, (canonicalRoughWave n (Nat.sqrt n) q).card) =
      (sqrtRoughCubeKeys n).card + (sqrtRoughCrossKeys n).card +
      2 * (sqrtRoughRepeatedKeys n).card + 3 * (sqrtRoughTripleProductsInShell n).card := by
  rw [rough_incidence_eq_strata, rough_singleton_card_eq_cube_cross,
    rough_double_card_eq_repeated, rough_triple_card_eq_products]

theorem sqrt_product_covered (n : ℕ) :
    ((canonicalRoughCandidates n (Nat.sqrt n)).filter
      (fun r => (paritySafeActiveSupport n r).Nonempty)).card =
      (sqrtRoughCubeKeys n).card + (sqrtRoughCrossKeys n).card +
      (sqrtRoughRepeatedKeys n).card + (sqrtRoughTripleProductsInShell n).card := by
  rw [rough_covered_eq_strata, rough_singleton_card_eq_cube_cross,
    rough_double_card_eq_repeated, rough_triple_card_eq_products]

theorem sqrt_uncovered_pos_iff_product_census (n : ℕ) :
    0 < (paritySafeUncoveredCandidates n).card ↔
      (sqrtRoughCubeKeys n).card + (sqrtRoughCrossKeys n).card +
        (sqrtRoughRepeatedKeys n).card + (sqrtRoughTripleProductsInShell n).card <
          (canonicalRoughCandidates n (Nat.sqrt n)).card := by
  have h := sqrt_rough_factorization_census n
  omega

theorem prime_squareCell_of_sqrt_factorization_census {n : ℕ} (hn : 0 < n)
    (h : (sqrtRoughCubeKeys n).card + (sqrtRoughCrossKeys n).card +
      (sqrtRoughRepeatedKeys n).card + (sqrtRoughTripleProductsInShell n).card <
        (canonicalRoughCandidates n (Nat.sqrt n)).card) :
    ∃ p, p.Prime ∧ SquareCell n p := by
  apply prime_squareCell_of_sqrt_moment hn
  have hu := (sqrt_uncovered_pos_iff_product_census n).mpr h
  exact (sqrt_uncovered_card_pos_iff_moment n).mp hu

/-- Exact provider contract: the external prime cofactor sum is explicit. -/
theorem prime_squareCell_of_cross_fiber_budget {n : ℕ} (hn : 0 < n)
    (h : (sqrtRoughCubeKeys n).card +
      (∑ p ∈ roughActiveLabels n (Nat.sqrt n), (sqrtRoughCrossFiber n p).card) +
      (sqrtRoughRepeatedKeys n).card + (sqrtRoughTripleProductsInShell n).card <
        (canonicalRoughCandidates n (Nat.sqrt n)).card) :
    ∃ p, p.Prime ∧ SquareCell n p := by
  apply prime_squareCell_of_sqrt_factorization_census hn
  simpa only [sqrt_cross_count_eq_fiber_sum] using h

end DkMath.NumberTheory.Legendre
