/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeSqrtRoughStrata

#print "file: DkMath.NumberTheory.Legendre.ParitySafeSqrtRoughSingleton"

namespace DkMath.NumberTheory.Legendre
open scoped BigOperators

/-- A reduced candidate with no prime divisor below the cutoff is in the existing rough carrier. -/
theorem sqrt_rough_of_reduced_point {n r : ℕ} (hs : SquareOffset n r)
    (hc : Nat.Coprime (2 * n) (n ^ 2 + r))
    (hfloor : ∀ u, u.Prime → u ∣ n ^ 2 + r → Nat.sqrt n < u) :
    r ∈ canonicalRoughCandidates n (Nat.sqrt n) := by
  apply Finset.mem_filter.mpr
  refine ⟨mem_squareAnchorOddPointCoprimeOffsets_iff_reducedResidue.mpr ⟨hs, hc⟩, ?_⟩
  intro u hu hle hd
  have := hfloor u (mem_squareAnchorOddActivePrimes.mp hu).1 hd
  omega

noncomputable def sqrtRoughCubeKeys (n : ℕ) : Finset ℕ :=
  (roughActiveLabels n (Nat.sqrt n)).filter (fun p => n ^ 2 < p ^ 3 ∧ p ^ 3 ≤ n ^ 2 + 2 * n)

/-- The upper cofactor endpoint is already divided by its owner p, keeping the finite carrier small. -/
noncomputable def sqrtRoughCrossFiber (n p : ℕ) : Finset ℕ :=
  (Finset.Ioc (max n (n ^ 2 / p)) ((n ^ 2 + 2 * n) / p)).filter (fun q => q.Prime)

noncomputable def sqrtRoughCrossKeys (n : ℕ) : Finset (ℕ × ℕ) :=
  (roughActiveLabels n (Nat.sqrt n)).biUnion
    (fun p => (sqrtRoughCrossFiber n p).image (fun q => (p, q)))

@[simp] theorem mem_sqrtRoughCrossFiber {n p q : ℕ} :
    q ∈ sqrtRoughCrossFiber n p ↔ q.Prime ∧ n < q ∧ n ^ 2 / p < q ∧
      q ≤ (n ^ 2 + 2 * n) / p := by
  simp only [sqrtRoughCrossFiber, Finset.mem_filter, Finset.mem_Ioc, max_lt_iff]
  tauto

theorem mem_sqrtRoughCrossKeys_fiber {n p q : ℕ} :
    (p, q) ∈ sqrtRoughCrossKeys n ↔ p ∈ roughActiveLabels n (Nat.sqrt n) ∧
      q ∈ sqrtRoughCrossFiber n p := by
  classical
  simp [sqrtRoughCrossKeys]

@[simp] theorem mem_sqrtRoughCrossKeys {n p q : ℕ} :
    (p, q) ∈ sqrtRoughCrossKeys n ↔ p ∈ roughActiveLabels n (Nat.sqrt n) ∧
      q.Prime ∧ n < q ∧ n ^ 2 < p * q ∧ p * q ≤ n ^ 2 + 2 * n := by
  rw [mem_sqrtRoughCrossKeys_fiber, mem_sqrtRoughCrossFiber]
  constructor
  · rintro ⟨hp, hq, hqn, hlo, hhi⟩
    have hpP := (mem_squareAnchorOddActivePrimes.mp (Finset.mem_filter.mp hp).1).1
    exact ⟨hp, hq, hqn, by simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hpP.pos).mp hlo,
      by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hpP.pos).mp hhi⟩
  · rintro ⟨hp, hq, hqn, hlo, hhi⟩
    have hpP := (mem_squareAnchorOddActivePrimes.mp (Finset.mem_filter.mp hp).1).1
    exact ⟨hp, hq, hqn, (Nat.div_lt_iff_lt_mul hpP.pos).mpr (by simpa only [Nat.mul_comm] using hlo),
      (Nat.le_div_iff_mul_le hpP.pos).mpr (by simpa only [Nat.mul_comm] using hhi)⟩

theorem sqrt_cube_offset_packet {n p : ℕ} (hp : p ∈ sqrtRoughCubeKeys n) :
    p ^ 3 - n ^ 2 ∈ roughSingletonSeats n ∧
      paritySafeActiveSupport n (p ^ 3 - n ^ 2) = {p} := by
  obtain ⟨hpL, hlo, hhi⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpA, hpgt⟩ := Finset.mem_filter.mp hpL
  have hpP := (mem_squareAnchorOddActivePrimes.mp hpA).1
  have he : n ^ 2 + (p ^ 3 - n ^ 2) = p ^ 3 := by omega
  have hrough : p ^ 3 - n ^ 2 ∈ canonicalRoughCandidates n (Nat.sqrt n) := by
    apply sqrt_rough_of_reduced_point
    · dsimp only [SquareOffset]; omega
    · rw [he]; exact (activePrime_reducedResidue_packet hpA).2.2.2.2.pow_right 3
    · intro u hu hd
      rw [he] at hd
      have huEq := Nat.prime_dvd_prime_iff_eq hu hpP |>.mp (hu.dvd_of_dvd_pow hd)
      simpa only [huEq] using hpgt
  have hsupport : paritySafeActiveSupport n (p ^ 3 - n ^ 2) = {p} := by
    ext u
    rw [mem_paritySafeActiveSupport_iff_dvd, Finset.mem_singleton, he]
    constructor
    · rintro ⟨huA, hd⟩
      exact (Nat.prime_dvd_prime_iff_eq (mem_squareAnchorOddActivePrimes.mp huA).1 hpP).mp
        ((mem_squareAnchorOddActivePrimes.mp huA).1.dvd_of_dvd_pow hd)
    · intro hu; subst u
      exact ⟨hpA, dvd_pow_self p (by decide : (3 : ℕ) ≠ 0)⟩
  exact ⟨Finset.mem_filter.mpr ⟨hrough, by rw [hsupport, Finset.card_singleton]⟩, hsupport⟩

theorem sqrt_cross_offset_packet {n p q : ℕ} (h : (p, q) ∈ sqrtRoughCrossKeys n) :
    p * q - n ^ 2 ∈ roughSingletonSeats n ∧
      paritySafeActiveSupport n (p * q - n ^ 2) = {p} := by
  obtain ⟨hpL, hqP, hqn, hlo, hhi⟩ := mem_sqrtRoughCrossKeys.mp h
  obtain ⟨hpA, hpgt⟩ := Finset.mem_filter.mp hpL
  have hpP := mem_squareAnchorOddActivePrimes.mp hpA
  have hnpos : 0 < n := lt_of_lt_of_le hpP.1.pos hpP.2.1
  have hqne : q ≠ 2 := by have := hpP.1.two_le; omega
  have hqcop : Nat.Coprime (2 * n) q := by
    rw [Nat.coprime_comm, Nat.coprime_mul_iff_right]
    refine ⟨Nat.coprime_two_right.mpr (hqP.odd_of_ne_two hqne), hqP.coprime_iff_not_dvd.mpr ?_⟩
    intro hd
    have := Nat.le_of_dvd hnpos hd
    omega
  have he : n ^ 2 + (p * q - n ^ 2) = p * q := by omega
  have hrough : p * q - n ^ 2 ∈ canonicalRoughCandidates n (Nat.sqrt n) := by
    apply sqrt_rough_of_reduced_point
    · dsimp only [SquareOffset]; omega
    · rw [he]; exact (activePrime_reducedResidue_packet hpA).2.2.2.2.mul_right hqcop
    · intro u hu hd
      rw [he] at hd
      rcases hu.dvd_mul.mp hd with hd | hd
      · have huEq := (Nat.prime_dvd_prime_iff_eq hu hpP.1).mp hd
        simpa only [huEq] using hpgt
      · have huEq := (Nat.prime_dvd_prime_iff_eq hu hqP).mp hd
        have := Nat.sqrt_le_self n
        omega
  have hsupport : paritySafeActiveSupport n (p * q - n ^ 2) = {p} := by
    ext u
    rw [mem_paritySafeActiveSupport_iff_dvd, Finset.mem_singleton, he]
    constructor
    · rintro ⟨huA, hd⟩
      have huP := mem_squareAnchorOddActivePrimes.mp huA
      rcases huP.1.dvd_mul.mp hd with hd | hd
      · exact (Nat.prime_dvd_prime_iff_eq huP.1 hpP.1).mp hd
      · have := (Nat.prime_dvd_prime_iff_eq huP.1 hqP).mp hd
        omega
    · intro hu; subst u; exact ⟨hpA, dvd_mul_right p q⟩
  exact ⟨Finset.mem_filter.mpr ⟨hrough, by rw [hsupport, Finset.card_singleton]⟩, hsupport⟩

theorem sqrt_cross_representation_unique {n p q a b : ℕ}
    (hp : p ∈ roughActiveLabels n (Nat.sqrt n)) (ha : a ∈ roughActiveLabels n (Nat.sqrt n))
    (_hq : q.Prime) (hb : b.Prime) (_hqn : n < q) (hbn : n < b)
    (he : p * q = a * b) : p = a ∧ q = b := by
  have hpP := mem_squareAnchorOddActivePrimes.mp (Finset.mem_filter.mp hp).1
  have haP := mem_squareAnchorOddActivePrimes.mp (Finset.mem_filter.mp ha).1
  have hpd : p ∣ a * b := he ▸ dvd_mul_right p q
  have hpa : p = a := by
    rcases hpP.1.dvd_mul.mp hpd with hd | hd
    · exact (Nat.prime_dvd_prime_iff_eq hpP.1 haP.1).mp hd
    · have := (Nat.prime_dvd_prime_iff_eq hpP.1 hb).mp hd
      omega
  subst a
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hpP.1.pos he⟩

theorem sqrt_cube_cross_disjoint_products {n p a q : ℕ}
    (hp : p ∈ roughActiveLabels n (Nat.sqrt n)) (_ha : a ∈ roughActiveLabels n (Nat.sqrt n))
    (hq : q.Prime) (hqn : n < q) : p ^ 3 ≠ a * q := by
  intro he
  have hpP := mem_squareAnchorOddActivePrimes.mp (Finset.mem_filter.mp hp).1
  have hd : q ∣ p ^ 3 := he.symm ▸ dvd_mul_left q a
  have := (Nat.prime_dvd_prime_iff_eq hq hpP.1).mp (hq.dvd_of_dvd_pow hd)
  omega

noncomputable def roughCubeSeats (n : ℕ) : Finset ℕ :=
  (sqrtRoughCubeKeys n).image (fun p => p ^ 3 - n ^ 2)

noncomputable def roughCrossSeats (n : ℕ) : Finset ℕ :=
  (sqrtRoughCrossKeys n).image (fun a => a.1 * a.2 - n ^ 2)

theorem sqrt_cube_keys_offset_injective (n : ℕ) :
    Set.InjOn (fun p => p ^ 3 - n ^ 2) (sqrtRoughCubeKeys n) := by
  intro p hp a ha he
  have hS := (sqrt_cube_offset_packet hp).2
  have hT := (sqrt_cube_offset_packet ha).2
  dsimp only at he
  rw [he] at hS
  exact Finset.singleton_injective (hS.symm.trans hT)

theorem sqrt_cross_keys_offset_injective (n : ℕ) :
    Set.InjOn (fun a : ℕ × ℕ => a.1 * a.2 - n ^ 2) (sqrtRoughCrossKeys n) := by
  intro a ha b hb he
  obtain ⟨hp, hq, hqn, hlo, _⟩ := mem_sqrtRoughCrossKeys.mp ha
  obtain ⟨hp', hq', hqn', hlo', _⟩ := mem_sqrtRoughCrossKeys.mp hb
  dsimp only at he
  have hpoint : a.1 * a.2 = b.1 * b.2 := by omega
  have hkey := sqrt_cross_representation_unique hp hp' hq hq' hqn hqn' hpoint
  exact Prod.ext hkey.1 hkey.2

theorem rough_cube_cross_disjoint (n : ℕ) : Disjoint (roughCubeSeats n) (roughCrossSeats n) := by
  classical
  apply Finset.disjoint_left.mpr
  intro r hr hs
  obtain ⟨p, hp, hpr⟩ := Finset.mem_image.mp hr
  obtain ⟨a, ha, har⟩ := Finset.mem_image.mp hs
  obtain ⟨hpL, hpLo, _⟩ := Finset.mem_filter.mp hp
  obtain ⟨haL, hq, hqn, haLo, _⟩ := mem_sqrtRoughCrossKeys.mp ha
  have he : p ^ 3 = a.1 * a.2 := by omega
  exact sqrt_cube_cross_disjoint_products hpL haL hq hqn he

theorem rough_singleton_eq_cube_union_cross (n : ℕ) :
    roughSingletonSeats n = roughCubeSeats n ∪ roughCrossSeats n := by
  classical
  ext r
  constructor
  · intro hr
    obtain ⟨p, hpP, hpgt, hpn, hpd, hS⟩ := roughSingleton_label_packet hr
    have hpS : p ∈ paritySafeActiveSupport n r := by rw [hS]; exact Finset.mem_singleton_self p
    have hpL := rough_support_subset_labels (Finset.mem_filter.mp hr).1 hpS
    have hs := squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets
      (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1
    dsimp only [SquareOffset] at hs
    rcases sqrt_singleton_point_cube_or_cross (Finset.mem_filter.mp hr).1 hS with he | ⟨q, hq, hqn, he⟩
    · apply Finset.mem_union.mpr; left
      exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hpL, by omega, by omega⟩, by omega⟩
    · apply Finset.mem_union.mpr; right
      exact Finset.mem_image.mpr ⟨(p, q), mem_sqrtRoughCrossKeys.mpr
        ⟨hpL, hq, hqn, by omega, by omega⟩, by dsimp only; omega⟩
  · intro hr
    rcases Finset.mem_union.mp hr with hr | hr
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hr
      exact (sqrt_cube_offset_packet hp).1
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
      exact (sqrt_cross_offset_packet ha).1

theorem rough_singleton_card_eq_cube_cross (n : ℕ) :
    (roughSingletonSeats n).card = (sqrtRoughCubeKeys n).card + (sqrtRoughCrossKeys n).card := by
  rw [rough_singleton_eq_cube_union_cross, Finset.card_union_of_disjoint (rough_cube_cross_disjoint n)]
  rw [roughCubeSeats, roughCrossSeats, Finset.card_image_of_injOn (sqrt_cube_keys_offset_injective n),
    Finset.card_image_of_injOn (sqrt_cross_keys_offset_injective n)]

theorem sqrtRoughCubeKeys_card_le_one (n : ℕ) : (sqrtRoughCubeKeys n).card ≤ 1 := by
  have hsep : ∀ p ∈ sqrtRoughCubeKeys n, ∀ q ∈ sqrtRoughCubeKeys n, p < q → False := by
    intro p hp q hq hpq
    obtain ⟨hpL, hpLo, hpHi⟩ := Finset.mem_filter.mp hp
    obtain ⟨hqL, hqLo, hqHi⟩ := Finset.mem_filter.mp hq
    have hpgt := (Finset.mem_filter.mp hpL).2
    have hpPow : n < p ^ 2 := by
      have := sqrt_successor_square_gt n
      have hm := Nat.mul_self_le_mul_self (show Nat.sqrt n + 1 ≤ p by omega)
      nlinarith
    have hc : (p + 1) ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left (show p + 1 ≤ q by omega) 3
    nlinarith
  apply Finset.card_le_one.mpr
  intro p hp q hq
  rcases lt_trichotomy p q with h | h | h
  · exact False.elim (hsep p hp q hq h)
  · exact h
  · exact False.elim (hsep q hq p hp h)

theorem sqrt_cross_count_eq_fiber_sum (n : ℕ) :
    (sqrtRoughCrossKeys n).card = ∑ p ∈ roughActiveLabels n (Nat.sqrt n), (sqrtRoughCrossFiber n p).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst)
    (t := roughActiveLabels n (Nat.sqrt n))
    (by intro a ha; exact (mem_sqrtRoughCrossKeys_fiber.mp ha).1)]
  apply Finset.sum_congr rfl
  intro p hp
  symm
  apply Finset.card_bij (fun q _ => (p, q))
  · intro q hq
    exact Finset.mem_filter.mpr ⟨mem_sqrtRoughCrossKeys_fiber.mpr ⟨hp, hq⟩, rfl⟩
  · intro a ha b hb he; exact congrArg Prod.snd he
  · intro a ha
    obtain ⟨ha, he⟩ := Finset.mem_filter.mp ha
    rcases a with ⟨s, q⟩
    dsimp at he
    subst s
    exact ⟨q, (mem_sqrtRoughCrossKeys_fiber.mp ha).2, rfl⟩

/-- The external prime fiber is exactly the prime-above-anchor part of the old reduced interval. -/
theorem sqrt_cross_fiber_eq_reduced_quotient_filter {n p : ℕ}
    (hp : p ∈ roughActiveLabels n (Nat.sqrt n)) :
    sqrtRoughCrossFiber n p = (paritySafeReducedQuotientInterval n p).filter
      (fun q => q.Prime ∧ n < q) := by
  classical
  have hpA := (Finset.mem_filter.mp hp).1
  have hpPos := (mem_squareAnchorOddActivePrimes.mp hpA).1.pos
  ext q
  constructor
  · intro hq
    have hkey := mem_sqrtRoughCrossKeys_fiber.mpr ⟨hp, hq⟩
    have hseat := (sqrt_cross_offset_packet hkey).1
    have hpoint := mem_sqrtRoughCrossKeys.mp hkey
    have he : n ^ 2 + (p * q - n ^ 2) = p * q := by omega
    have hw : p * q - n ^ 2 ∈ paritySafeActiveWaveOffsets n p :=
      mem_paritySafeActiveWaveOffsets.mpr
        ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hseat).1).1,
          by change p ∣ n ^ 2 + (p * q - n ^ 2); rw [he]; exact dvd_mul_right p q⟩
    have hcop := (paritySafeActiveWaveOffsets_quotient_properties hpA hw).2.1
    have hquot : squareOffsetSupportQuotient n p (p * q - n ^ 2) = q := by
      unfold squareOffsetSupportQuotient
      rw [he, Nat.mul_div_right _ hpPos]
    rw [hquot] at hcop
    exact Finset.mem_filter.mpr ⟨(mem_paritySafeReducedQuotientInterval_iff hpPos).mpr
      ⟨hpoint.2.2.2.1, hpoint.2.2.2.2, hcop⟩, hpoint.2.1, hpoint.2.2.1⟩
  · intro hq
    obtain ⟨hq, hprime, hgt⟩ := Finset.mem_filter.mp hq
    have hwindow := (mem_paritySafeReducedQuotientInterval_iff hpPos).mp hq
    exact (mem_sqrtRoughCrossKeys_fiber.mp (mem_sqrtRoughCrossKeys.mpr
      ⟨hp, hprime, hgt, hwindow.1, hwindow.2.1⟩)).2

/-- An exact map precedes reuse of the old wave capacity. -/
theorem sqrt_cross_fiber_card_le_active_wave {n p : ℕ}
    (hp : p ∈ roughActiveLabels n (Nat.sqrt n)) :
    (sqrtRoughCrossFiber n p).card ≤ (paritySafeActiveWaveOffsets n p).card := by
  rw [sqrt_cross_fiber_eq_reduced_quotient_filter hp,
    card_paritySafeActiveWaveOffsets_eq_reducedQuotientInterval (Finset.mem_filter.mp hp).1]
  exact Finset.card_le_card (Finset.filter_subset ..)

/-- Exact integer span before primality or oddness is used. -/
theorem sqrt_cross_fiber_card_le_quotient_span (n p : ℕ) :
    (sqrtRoughCrossFiber n p).card ≤ (n ^ 2 + 2 * n) / p - max n (n ^ 2 / p) := by
  have h := Finset.card_le_card (Finset.filter_subset (s :=
    Finset.Ioc (max n (n ^ 2 / p)) ((n ^ 2 + 2 * n) / p)) (p := fun q => q.Prime))
  simpa only [sqrtRoughCrossFiber, Nat.card_Ioc] using h

/-- The geometric bound alone ignores primality and is insufficient as a uniform summed provider. -/
theorem sqrt_cross_fiber_card_le_div_add_one {n p : ℕ}
    (hp : p ∈ roughActiveLabels n (Nat.sqrt n)) :
    (sqrtRoughCrossFiber n p).card ≤ (2 * n) / p + 1 := by
  have hpPos := (mem_squareAnchorOddActivePrimes.mp (Finset.mem_filter.mp hp).1).1.pos
  have hsub : sqrtRoughCrossFiber n p ⊆ Finset.Ioc (n ^ 2 / p) ((n ^ 2 + 2 * n) / p) := by
    intro q hq
    have h := mem_sqrtRoughCrossFiber.mp hq
    exact Finset.mem_Ioc.mpr ⟨h.2.2.1, h.2.2.2⟩
  have hbound := Finset.card_le_card hsub
  rw [Nat.card_Ioc] at hbound
  have hwave := card_squareWaveOffsets_le_div_add_one (n := n) hpPos
  rw [card_squareWaveOffsets_eq_div_sub_div hpPos] at hwave
  exact hbound.trans hwave

theorem sqrt_cross_fiber_parity_spacing {n p q s : ℕ}
    (hp : p ∈ roughActiveLabels n (Nat.sqrt n))
    (hq : q ∈ sqrtRoughCrossFiber n p) (hs : s ∈ sqrtRoughCrossFiber n p) (hqs : q < s) :
    Even (s - q) ∧ 2 ≤ s - q := by
  rw [sqrt_cross_fiber_eq_reduced_quotient_filter hp] at hq hs
  have hqcop := (mem_paritySafeReducedQuotientInterval_iff
    (mem_squareAnchorOddActivePrimes.mp (Finset.mem_filter.mp hp).1).1.pos).mp (Finset.mem_filter.mp hq).1
  have hscop := (mem_paritySafeReducedQuotientInterval_iff
    (mem_squareAnchorOddActivePrimes.mp (Finset.mem_filter.mp hp).1).1.pos).mp (Finset.mem_filter.mp hs).1
  have he := Nat.Odd.sub_odd (coprime_two_mul_iff_coprime_and_odd.mp hscop.2.2).2
    (coprime_two_mul_iff_coprime_and_odd.mp hqcop.2.2).2
  refine ⟨he, Nat.le_of_dvd (by omega) (even_iff_two_dvd.mp he)⟩

/-- At an odd prime anchor the exact parity/anchor-exclusion floor capacity also bounds the fiber. -/
theorem primeAnchor_cross_fiber_card_le_floor {n p : ℕ} (hn : n.Prime) (hne : n ≠ 2)
    (hp : p ∈ roughActiveLabels n (Nat.sqrt n)) :
    (sqrtRoughCrossFiber n p).card ≤ primeAnchorProductWaveCount n p := by
  have hpA := activePrime_reducedResidue_packet (Finset.mem_filter.mp hp).1
  have he : paritySafeActiveWaveOffsets n p = paritySafeProductWaveOffsets n p := by
    ext r
    simp only [mem_paritySafeActiveWaveOffsets_iff_dvd, paritySafeProductWaveOffsets, Finset.mem_filter]
  have hb := sqrt_cross_fiber_card_le_active_wave hp
  rw [he, paritySafeProductWave_card_eq_count hn (hn.odd_of_ne_two hne)
    (hpA.1.odd_of_ne_two hpA.2.2.2.1)
    (hpA.2.2.2.2.coprime_dvd_left (dvd_mul_left n 2))] at hb
  exact hb

end DkMath.NumberTheory.Legendre
