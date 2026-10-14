/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeSqrtCrossQuotient

#print "file: DkMath.NumberTheory.Legendre.ParitySafeSqrtCompositeRouting"

/-! Routing uses every actual supported owner, rather than a canonical minimum. -/

namespace DkMath.NumberTheory.Legendre
open scoped BigOperators

/-- Every supported owner reconstructs exactly one reduced, rough, above-anchor quotient. -/
theorem sqrt_supported_quotient_packet {n r p : ℕ}
    (hr : r ∈ canonicalRoughCandidates n (Nat.sqrt n))
    (hp : p ∈ paritySafeActiveSupport n r) :
    squareOffsetSupportQuotient n p r ∈ sqrtRoughRoutedFiber n p ∧
      n < squareOffsetSupportQuotient n p r ∧
      p * squareOffsetSupportQuotient n p r = n ^ 2 + r := by
  classical
  have hpL := rough_support_subset_labels hr hp
  have hpA := (mem_paritySafeActiveSupport_iff_dvd.mp hp).1
  have hd := (mem_paritySafeActiveSupport_iff_dvd.mp hp).2
  have hw := mem_paritySafeActiveWaveOffsets.mpr ⟨(Finset.mem_filter.mp hr).1, hd⟩
  have hm := paritySafeActiveWaveOffsets_quotient_mem_interval hpA hw
  have hf := mul_squareOffsetSupportQuotient_eq hd
  have he : p * squareOffsetSupportQuotient n p r - n ^ 2 = r := by omega
  exact ⟨Finset.mem_filter.mpr ⟨hm, by rwa [he]⟩, sqrt_quotient_gt_anchor hpL hm, hf⟩

/-- The quotient relation recovers actual support, so it introduces no second support universe. -/
theorem sqrt_quotient_owners_eq_support {n r : ℕ}
    (hr : r ∈ canonicalRoughCandidates n (Nat.sqrt n)) :
    (roughActiveLabels n (Nat.sqrt n)).filter
      (fun p => ∃ q ∈ sqrtRoughRoutedFiber n p, p * q = n ^ 2 + r) =
      paritySafeActiveSupport n r := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hpL, q, hq, he⟩ := Finset.mem_filter.mp hp
    exact mem_paritySafeActiveSupport_iff_dvd.mpr
      ⟨(Finset.mem_filter.mp hpL).1, ⟨q, he.symm⟩⟩
  · intro hp
    have h := sqrt_supported_quotient_packet hr hp
    exact Finset.mem_filter.mpr ⟨rough_support_subset_labels hr hp,
      squareOffsetSupportQuotient n p r, h.1, h.2.2⟩

theorem sqrt_routed_fiber_card_eq_rough_wave {n p : ℕ}
    (hp : p ∈ roughActiveLabels n (Nat.sqrt n)) :
    (sqrtRoughRoutedFiber n p).card = (canonicalRoughWave n (Nat.sqrt n) p).card := by
  classical
  apply Finset.card_bij (fun q _ => p * q - n ^ 2)
  · intro q hq
    have hs := sqrt_quotient_seat_packet hp (Finset.mem_filter.mp hq).1
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hq).2,
      (mem_paritySafeActiveSupport_iff_dvd.mp hs.2.2.2.1).2⟩
  · intro q hq s hs he
    have hqP := sqrt_quotient_seat_packet hp (Finset.mem_filter.mp hq).1
    have hsP := sqrt_quotient_seat_packet hp (Finset.mem_filter.mp hs).1
    have hm : p * q = p * s := by omega
    exact Nat.eq_of_mul_eq_mul_left (mem_squareAnchorOddActivePrimes.mp
      (Finset.mem_filter.mp hp).1).1.pos hm
  · intro r hr
    obtain ⟨hrR, hd⟩ := Finset.mem_filter.mp hr
    have h := sqrt_supported_quotient_packet hrR
      (mem_paritySafeActiveSupport_iff_dvd.mpr ⟨(Finset.mem_filter.mp hp).1, hd⟩)
    exact ⟨squareOffsetSupportQuotient n p r, h.1, by omega⟩

/-- Complement normal forms, including repeated factors: all three values are above n. -/
theorem sqrt_three_factor_owner_quotients {n p q s : ℕ}
    (hp : p ∈ roughActiveLabels n (Nat.sqrt n))
    (hq : q ∈ roughActiveLabels n (Nat.sqrt n))
    (hs : s ∈ roughActiveLabels n (Nat.sqrt n))
    (hlo : n ^ 2 < p * q * s) (hhi : p * q * s ≤ n ^ 2 + 2 * n) :
    q * s ∈ sqrtRoughRoutedFiber n p ∧ n < q * s ∧ ¬(q * s).Prime ∧
    p * s ∈ sqrtRoughRoutedFiber n q ∧ n < p * s ∧ ¬(p * s).Prime ∧
    p * q ∈ sqrtRoughRoutedFiber n s ∧ n < p * q ∧ ¬(p * q).Prime := by
  have h := sqrt_rough_three_factor_packet hp hq hs hlo hhi
  have he : n ^ 2 + (p * q * s - n ^ 2) = p * q * s := by omega
  have hP := (mem_squareAnchorOddActivePrimes.mp (Finset.mem_filter.mp hp).1).1
  have hQ := (mem_squareAnchorOddActivePrimes.mp (Finset.mem_filter.mp hq).1).1
  have hS := (mem_squareAnchorOddActivePrimes.mp (Finset.mem_filter.mp hs).1).1
  have hquot (a b : ℕ) (ha : a ∈ paritySafeActiveSupport n (p * q * s - n ^ 2))
      (hab : a * b = p * q * s) :
      b ∈ sqrtRoughRoutedFiber n a ∧ n < b := by
    have ht := sqrt_supported_quotient_packet h.1 ha
    have haP := (mem_squareAnchorOddActivePrimes.mp
      (mem_paritySafeActiveSupport_iff_dvd.mp ha).1).1
    have hb : squareOffsetSupportQuotient n a (p * q * s - n ^ 2) = b := by
      apply Nat.eq_of_mul_eq_mul_left haP.pos
      rw [ht.2.2, he, hab]
    have htPair := And.intro ht.1 ht.2.1
    simpa only [hb] using htPair
  have hpq := hquot p (q * s) (by rw [h.2]; simp) (by ring)
  have hqp := hquot q (p * s) (by rw [h.2]; simp) (by ring)
  have hsp := hquot s (p * q) (by rw [h.2]; simp) (by ring)
  exact ⟨hpq.1, hpq.2, Nat.not_prime_mul hQ.ne_one hS.ne_one,
    hqp.1, hqp.2, Nat.not_prime_mul hP.ne_one hS.ne_one,
    hsp.1, hsp.2, Nat.not_prime_mul hP.ne_one hQ.ne_one⟩


/-- The cube complement is p², above n, and composite. -/
theorem sqrt_cube_owner_quotient {n p : ℕ} (hp : p ∈ sqrtRoughCubeKeys n) :
    p ^ 2 ∈ sqrtRoughRoutedFiber n p ∧ n < p ^ 2 ∧ ¬(p ^ 2).Prime := by
  obtain ⟨hpL, hlo, hhi⟩ := Finset.mem_filter.mp hp
  have ht := sqrt_three_factor_owner_quotients hpL hpL hpL
    (by nlinarith [hlo]) (by nlinarith [hhi])
  have htFirst := And.intro ht.1 (And.intro ht.2.1 ht.2.2.1)
  simpa only [pow_two] using htFirst

/-- The orientation bit determines both repeated complements; neither is dropped above n. -/
theorem sqrt_repeated_owner_quotients {n : ℕ} {a : (ℕ × ℕ) × Bool}
    (ha : a ∈ sqrtRoughRepeatedKeys n) :
    (if a.2 then a.1.2 ^ 2 else a.1.1 * a.1.2) ∈ sqrtRoughRoutedFiber n a.1.1 ∧
    n < (if a.2 then a.1.2 ^ 2 else a.1.1 * a.1.2) ∧
    ¬(if a.2 then a.1.2 ^ 2 else a.1.1 * a.1.2).Prime ∧
    (if a.2 then a.1.1 * a.1.2 else a.1.1 ^ 2) ∈ sqrtRoughRoutedFiber n a.1.2 ∧
    n < (if a.2 then a.1.1 * a.1.2 else a.1.1 ^ 2) ∧
    ¬(if a.2 then a.1.1 * a.1.2 else a.1.1 ^ 2).Prime := by
  obtain ⟨ha, hlo, hhi⟩ := Finset.mem_filter.mp ha
  obtain ⟨hp, hq, _⟩ := mem_roughPairs.mp (Finset.mem_product.mp ha).1
  rcases a with ⟨⟨p, q⟩, b⟩
  cases b
  · simp only [sqrtRepeatedProduct, Bool.false_eq_true, ↓reduceIte] at hlo hhi ⊢
    have ht := sqrt_three_factor_owner_quotients hp hp hq
      (by nlinarith [hlo]) (by nlinarith [hhi])
    have hpp := And.intro ht.2.2.2.2.2.2.1 (And.intro ht.2.2.2.2.2.2.2.1 ht.2.2.2.2.2.2.2.2)
    exact ⟨ht.1, ht.2.1, ht.2.2.1, by simpa only [pow_two] using hpp⟩
  · simp only [sqrtRepeatedProduct, ↓reduceIte] at hlo hhi ⊢
    have ht := sqrt_three_factor_owner_quotients hp hq hq
      (by nlinarith [hlo]) (by nlinarith [hhi])
    have hqq := And.intro ht.1 (And.intro ht.2.1 ht.2.2.1)
    have hf : q ^ 2 ∈ sqrtRoughRoutedFiber n p ∧ n < q ^ 2 ∧ ¬(q ^ 2).Prime := by
      simpa only [pow_two] using hqq
    exact ⟨hf.1, hf.2.1, hf.2.2, ht.2.2.2.1, ht.2.2.2.2.1, ht.2.2.2.2.2.1⟩

/-- Each supported owner of a triple sees the other two prime factors. -/
theorem sqrt_triple_owner_quotients {n : ℕ} {a : ℕ × ℕ × ℕ}
    (ha : a ∈ sqrtRoughTripleProductsInShell n) :
    a.2.1 * a.2.2 ∈ sqrtRoughRoutedFiber n a.1 ∧ n < a.2.1 * a.2.2 ∧
      ¬(a.2.1 * a.2.2).Prime ∧
    a.1 * a.2.2 ∈ sqrtRoughRoutedFiber n a.2.1 ∧ n < a.1 * a.2.2 ∧
      ¬(a.1 * a.2.2).Prime ∧
    a.1 * a.2.1 ∈ sqrtRoughRoutedFiber n a.2.2 ∧ n < a.1 * a.2.1 ∧
      ¬(a.1 * a.2.1).Prime := by
  obtain ⟨ha, hlo, hhi⟩ := Finset.mem_filter.mp ha
  obtain ⟨hp, hq, hs, _, _⟩ := mem_roughTriples.mp ha
  exact sqrt_three_factor_owner_quotients hp hq hs hlo hhi

/-- The three census types have respectively 1, 2, and 3 supported quotient owners. -/
theorem sqrt_cube_quotient_owner_multiplicity {n p : ℕ} (hp : p ∈ sqrtRoughCubeKeys n) :
    ((roughActiveLabels n (Nat.sqrt n)).filter
      (fun a => ∃ q ∈ sqrtRoughRoutedFiber n a, a * q = p ^ 3)).card = 1 := by
  have hs := sqrt_cube_offset_packet hp
  have he : n ^ 2 + (p ^ 3 - n ^ 2) = p ^ 3 := by
    have := (Finset.mem_filter.mp hp).2; omega
  rw [← he, sqrt_quotient_owners_eq_support (Finset.mem_filter.mp hs.1).1,
    hs.2, Finset.card_singleton]

theorem sqrt_repeated_quotient_owner_multiplicity {n : ℕ} {a : (ℕ × ℕ) × Bool}
    (ha : a ∈ sqrtRoughRepeatedKeys n) :
    ((roughActiveLabels n (Nat.sqrt n)).filter
      (fun p => ∃ q ∈ sqrtRoughRoutedFiber n p, p * q = sqrtRepeatedProduct a)).card = 2 := by
  have hs := sqrt_repeated_offset_packet ha
  have he : n ^ 2 + (sqrtRepeatedProduct a - n ^ 2) = sqrtRepeatedProduct a := by
    have := (Finset.mem_filter.mp ha).2; omega
  rw [← he, sqrt_quotient_owners_eq_support (Finset.mem_filter.mp hs.1).1]
  exact (Finset.mem_filter.mp hs.1).2

theorem sqrt_triple_quotient_owner_multiplicity {n : ℕ} {a : ℕ × ℕ × ℕ}
    (ha : a ∈ sqrtRoughTripleProductsInShell n) :
    ((roughActiveLabels n (Nat.sqrt n)).filter
      (fun p => ∃ q ∈ sqrtRoughRoutedFiber n p, p * q = a.1 * a.2.1 * a.2.2)).card = 3 := by
  have hs := sqrt_triple_offset_packet ha
  have he : n ^ 2 + (a.1 * a.2.1 * a.2.2 - n ^ 2) = a.1 * a.2.1 * a.2.2 := by
    have := (Finset.mem_filter.mp ha).2; omega
  rw [← he, sqrt_quotient_owners_eq_support (Finset.mem_filter.mp hs.1).1]
  exact (Finset.mem_filter.mp hs.1).2

/-- Composite routing is exhaustive only after the small-prime rejection filter. -/
theorem sqrt_composite_quotient_routes_to_census {n p q : ℕ}
    (hp : p ∈ roughActiveLabels n (Nat.sqrt n))
    (hq : q ∈ sqrtRoughRoutedFiber n p) (hcom : ¬q.Prime) :
    (∃ a ∈ sqrtRoughCubeKeys n, p * q = a ^ 3) ∨
    (∃ a ∈ sqrtRoughRepeatedKeys n, p * q = sqrtRepeatedProduct a) ∨
    (∃ a ∈ sqrtRoughTripleProductsInShell n, p * q = a.1 * a.2.1 * a.2.2) := by
  have hseat := sqrt_quotient_seat_packet hp (Finset.mem_filter.mp hq).1
  have hr := (Finset.mem_filter.mp hq).2
  have he := hseat.2.2.1
  rcases sqrt_rough_point_factorization hr with hu | hc | hx | hd | ht
  · have hs := (mem_uncovered_iff_no_activeSupport.mp hu.1).2
    exact False.elim (hs ⟨p, hseat.2.2.2.1⟩)
  · exact Or.inl (by simpa only [he] using hc)
  · obtain ⟨a, ha, hpoint⟩ := hx
    have hpk := sqrt_cross_offset_packet ha
    have hlow := (mem_sqrtRoughCrossKeys.mp ha).2.2.2.1
    have hoff : a.1 * a.2 - n ^ 2 = p * q - n ^ 2 := by omega
    rw [hoff] at hpk
    have hpa : p = a.1 := by
      have hh := hseat.2.2.2.1
      rw [hpk.2, Finset.mem_singleton] at hh
      exact hh
    have hqa : q = a.2 := by
      apply Nat.eq_of_mul_eq_mul_left (mem_squareAnchorOddActivePrimes.mp
        (Finset.mem_filter.mp hp).1).1.pos
      simpa only [he, ← hpa] using hpoint
    exact False.elim (hcom (hqa ▸ (mem_sqrtRoughCrossKeys.mp ha).2.1))
  · exact Or.inr (Or.inl (by simpa only [he] using hd))
  · exact Or.inr (Or.inr (by simpa only [he] using ht))


/-- The proposed above-n refinement has exactly the same multiplicity as actual support. -/
theorem sqrt_quotient_owners_above_eq_support {n r : ℕ}
    (hr : r ∈ canonicalRoughCandidates n (Nat.sqrt n)) :
    (roughActiveLabels n (Nat.sqrt n)).filter
      (fun p => ∃ q ∈ sqrtRoughRoutedFiber n p, n < q ∧ p * q = n ^ 2 + r) =
      paritySafeActiveSupport n r := by
  classical
  rw [← sqrt_quotient_owners_eq_support hr]
  apply Finset.filter_congr
  intro p hp
  constructor
  · rintro ⟨q, hq, _, he⟩; exact ⟨q, hq, he⟩
  · rintro ⟨q, hq, he⟩
    exact ⟨q, hq, sqrt_quotient_gt_anchor hp (Finset.mem_filter.mp hq).1, he⟩

/-- Every rough composite quotient has exactly two rough active prime factors, counted with repetition. -/
theorem sqrt_composite_quotient_normal_forms {n p q : ℕ}
    (hp : p ∈ roughActiveLabels n (Nat.sqrt n))
    (hq : q ∈ sqrtRoughRoutedFiber n p) (hc : ¬q.Prime) :
    (q = p ^ 2 ∧ p ∈ sqrtRoughCubeKeys n) ∨
    (∃ a ∈ roughActiveLabels n (Nat.sqrt n), a ≠ p ∧ (q = p * a ∨ q = a ^ 2)) ∨
    (∃ a ∈ roughActiveLabels n (Nat.sqrt n), ∃ b ∈ roughActiveLabels n (Nat.sqrt n),
      a ≠ b ∧ a ≠ p ∧ b ≠ p ∧ q = a * b) := by
  have hs := sqrt_quotient_seat_packet hp (Finset.mem_filter.mp hq).1
  have hpP := (mem_squareAnchorOddActivePrimes.mp (Finset.mem_filter.mp hp).1).1
  have cancel (c : ℕ) (he : p * q = p * c) : q = c := Nat.eq_of_mul_eq_mul_left hpP.pos he
  rcases sqrt_composite_quotient_routes_to_census hp hq hc with hcube | hrepeat | htriple
  · obtain ⟨a, ha, he⟩ := hcube
    have ht := sqrt_cube_offset_packet ha
    have hoff : a ^ 3 - n ^ 2 = p * q - n ^ 2 := by omega
    rw [hoff] at ht
    have hpa : p = a := by
      have hh := hs.2.2.2.1
      rwa [ht.2, Finset.mem_singleton] at hh
    subst a
    exact Or.inl ⟨cancel (p ^ 2) (by nlinarith [he]), ha⟩
  · obtain ⟨a, ha, he⟩ := hrepeat
    have ht := sqrt_repeated_offset_packet ha
    have hoff : sqrtRepeatedProduct a - n ^ 2 = p * q - n ^ 2 := by omega
    rw [hoff] at ht
    have howner := hs.2.2.2.1
    rw [ht.2, Finset.mem_insert, Finset.mem_singleton] at howner
    obtain ⟨hA, hB, hlt⟩ := mem_roughPairs.mp (Finset.mem_product.mp (Finset.mem_filter.mp ha).1).1
    rcases a with ⟨⟨a, b⟩, side⟩
    dsimp only at howner hA hB hlt
    right; left
    rcases howner with rfl | rfl
    · refine ⟨b, hB, hlt.ne.symm, ?_⟩
      cases side
      · left; apply cancel; simpa only [sqrtRepeatedProduct, Bool.false_eq_true, ↓reduceIte,
          pow_two, Nat.mul_assoc] using he
      · right; apply cancel; simpa only [sqrtRepeatedProduct, ↓reduceIte] using he
    · refine ⟨a, hA, hlt.ne, ?_⟩
      cases side
      · right; apply cancel; simpa only [sqrtRepeatedProduct, Bool.false_eq_true, ↓reduceIte,
          Nat.mul_comm] using he
      · left; apply cancel; simpa only [sqrtRepeatedProduct, ↓reduceIte, pow_two,
          Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using he
  · obtain ⟨a, ha, he⟩ := htriple
    have ht := sqrt_triple_offset_packet ha
    have hoff : a.1 * a.2.1 * a.2.2 - n ^ 2 = p * q - n ^ 2 := by omega
    rw [hoff] at ht
    have howner := hs.2.2.2.1
    rw [ht.2, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at howner
    obtain ⟨hA, hB, hC, hab, hbc⟩ := mem_roughTriples.mp (Finset.mem_filter.mp ha).1
    rcases a with ⟨a, b, c⟩
    dsimp only at howner hA hB hC hab hbc he
    right; right
    rcases howner with rfl | rfl | rfl
    · refine ⟨b, hB, c, hC, hbc.ne, hab.ne.symm, (hab.trans hbc).ne.symm, ?_⟩
      apply cancel; simpa only [Nat.mul_assoc] using he
    · refine ⟨a, hA, c, hC, (hab.trans hbc).ne, hab.ne, hbc.ne.symm, ?_⟩
      apply cancel; simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using he
    · refine ⟨a, hA, b, hB, hab.ne, (hab.trans hbc).ne, hbc.ne, ?_⟩
      apply cancel; simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using he


/-- A prime divisor of a routed composite quotient is active, never an external prime. -/
theorem sqrt_routed_composite_factor_packet {n p q u : ℕ}
    (hp : p ∈ roughActiveLabels n (Nat.sqrt n))
    (hq : q ∈ sqrtRoughRoutedFiber n p) (hc : ¬q.Prime)
    (hu : u.Prime) (hd : u ∣ q) :
    u ∈ roughActiveLabels n (Nat.sqrt n) ∧ u ∈ paritySafeActiveSupport n (p * q - n ^ 2) ∧
      Nat.sqrt n < u ∧ u ≤ n := by
  have hf : ∃ a ∈ roughActiveLabels n (Nat.sqrt n),
      ∃ b ∈ roughActiveLabels n (Nat.sqrt n), q = a * b := by
    rcases sqrt_composite_quotient_normal_forms hp hq hc with hcube | hrepeat | htriple
    · exact ⟨p, hp, p, hp, by simpa only [pow_two] using hcube.1⟩
    · obtain ⟨a, ha, _, he⟩ := hrepeat
      rcases he with he | he
      · exact ⟨p, hp, a, ha, he⟩
      · exact ⟨a, ha, a, ha, by simpa only [pow_two] using he⟩
    · obtain ⟨a, ha, b, hb, _, _, _, he⟩ := htriple
      exact ⟨a, ha, b, hb, he⟩
  obtain ⟨a, ha, b, hb, he⟩ := hf
  have haP := (mem_squareAnchorOddActivePrimes.mp (Finset.mem_filter.mp ha).1).1
  have hbP := (mem_squareAnchorOddActivePrimes.mp (Finset.mem_filter.mp hb).1).1
  have huL : u ∈ roughActiveLabels n (Nat.sqrt n) := by
    rw [he, hu.dvd_mul, Nat.prime_dvd_prime_iff_eq hu haP,
      Nat.prime_dvd_prime_iff_eq hu hbP] at hd
    rcases hd with rfl | rfl <;> assumption
  have hs := sqrt_quotient_seat_packet hp (Finset.mem_filter.mp hq).1
  refine ⟨huL, ?_, (Finset.mem_filter.mp huL).2,
    (mem_squareAnchorOddActivePrimes.mp (Finset.mem_filter.mp huL).1).2.1⟩
  apply mem_paritySafeActiveSupport_iff_dvd.mpr
  refine ⟨(Finset.mem_filter.mp huL).1, ?_⟩
  rw [hs.2.2.1]
  exact dvd_mul_of_dvd_right hd p

end DkMath.NumberTheory.Legendre
