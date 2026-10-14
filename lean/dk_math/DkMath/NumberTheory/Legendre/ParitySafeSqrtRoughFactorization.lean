/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeSqrtRoughProductWaves

#print "file: DkMath.NumberTheory.Legendre.ParitySafeSqrtRoughFactorization"

namespace DkMath.NumberTheory.Legendre

/-- Every prime divisor of a reduced candidate below the anchor is an actual active label. -/
theorem prime_dvd_candidate_mem_active {n r u : ℕ}
    (hr : r ∈ squareAnchorOddPointCoprimeOffsets n) (hu : u.Prime)
    (hun : u ≤ n) (hd : u ∣ n ^ 2 + r) : u ∈ squareAnchorOddActivePrimes n := by
  have hcop := (mem_squareAnchorOddPointCoprimeOffsets_iff_reducedResidue.mp hr).2
  have hcu : Nat.Coprime u (2 * n) := (hcop.coprime_dvd_right hd).symm
  have hnot := hu.coprime_iff_not_dvd.mp hcu
  refine mem_squareAnchorOddActivePrimes.mpr ⟨hu, hun, ?_, ?_⟩
  · intro h; exact hnot (dvd_mul_of_dvd_right h 2)
  · intro h; subst u; exact hnot (dvd_mul_right 2 n)

/-- All prime factors of a sqrt-rough point exceed the cutoff, including factors above n. -/
theorem sqrt_rough_prime_divisor_gt {n r u : ℕ}
    (hr : r ∈ canonicalRoughCandidates n (Nat.sqrt n)) (hu : u.Prime)
    (hd : u ∣ n ^ 2 + r) : Nat.sqrt n < u := by
  by_contra hh
  have hle : u ≤ Nat.sqrt n := by omega
  have ha := prime_dvd_candidate_mem_active (Finset.mem_filter.mp hr).1 hu
    (hle.trans (Nat.sqrt_le_self n)) hd
  exact (Finset.mem_filter.mp hr).2 u ha hle hd

theorem sqrt_roughPair_product_lower {n p q : ℕ}
    (h : (p, q) ∈ roughPairs n (Nat.sqrt n)) : (Nat.sqrt n + 1) ^ 2 ≤ p * q := by
  obtain ⟨hp, hq, _⟩ := mem_roughPairs.mp h
  have hlp := (Finset.mem_filter.mp hp).2
  have hlq := (Finset.mem_filter.mp hq).2
  simpa only [pow_two] using Nat.mul_le_mul (show Nat.sqrt n + 1 ≤ p by omega)
    (show Nat.sqrt n + 1 ≤ q by omega)

theorem sqrt_roughTriple_product_lower {n p q s : ℕ}
    (h : (p, q, s) ∈ roughTriples n (Nat.sqrt n)) : (Nat.sqrt n + 1) ^ 3 ≤ p * q * s := by
  obtain ⟨hp, hq, hs, hpq, _⟩ := mem_roughTriples.mp h
  have hl := (Finset.mem_filter.mp hs).2
  have hpair := sqrt_roughPair_product_lower (mem_roughPairs.mpr ⟨hp, hq, hpq⟩)
  simpa only [pow_succ, pow_two] using
    Nat.mul_le_mul hpair (show Nat.sqrt n + 1 ≤ s by omega)

/-- Three supported labels already exhaust the point; no complementary factor survives. -/
theorem sqrt_roughTriple_point_eq_product {n r p q s : ℕ}
    (hr : r ∈ canonicalRoughCandidates n (Nat.sqrt n))
    (h : (p, q, s) ∈ roughTriples n (Nat.sqrt n))
    (hs : (p, q, s) ∈ upperTriples (paritySafeActiveSupport n r)) :
    n ^ 2 + r = p * q * s := by
  have hd := (roughTriple_support_iff_product h).mp hs
  obtain ⟨c, hc⟩ := hd
  have hpoint := squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets (Finset.mem_filter.mp hr).1
  dsimp only [SquareOffset] at hpoint
  have hlo := sqrt_roughTriple_product_lower h
  have hfour := sqrtCutoff_power_four_gt n
  have hclt : c < Nat.sqrt n + 1 := by
    by_contra hh
    have hm := Nat.mul_le_mul hlo (show Nat.sqrt n + 1 ≤ c by omega)
    have he : (Nat.sqrt n + 1) ^ 3 * (Nat.sqrt n + 1) = (Nat.sqrt n + 1) ^ 4 := by ring
    rw [he, ← hc] at hm
    omega
  have hcpos : 0 < c := by
    by_contra hh
    have hz : c = 0 := by omega
    rw [hz, Nat.mul_zero] at hc
    omega
  have hc1 : c = 1 := by
    by_contra hh
    obtain ⟨u, hu, hdc⟩ := Nat.exists_prime_and_dvd hh
    have hule := Nat.le_of_dvd hcpos hdc
    have hdpoint : u ∣ n ^ 2 + r := hc ▸ dvd_mul_of_dvd_right hdc (p * q * s)
    have := sqrt_rough_prime_divisor_gt hr hu hdpoint
    omega
  simpa only [hc1, Nat.mul_one] using hc

/-- The full triple fiber consists precisely of its product point, with the actual rough filter. -/
theorem sqrt_roughTripleWave_eq_product_seat {n p q s : ℕ}
    (h : (p, q, s) ∈ roughTriples n (Nat.sqrt n)) :
    roughTripleWave n (Nat.sqrt n) p q s = (canonicalRoughCandidates n (Nat.sqrt n)).filter (fun r => n ^ 2 + r = p * q * s) := by
  ext r
  simp only [roughTripleWave, Finset.mem_filter]
  constructor
  · rintro ⟨hr, hd⟩
    exact ⟨hr, sqrt_roughTriple_point_eq_product hr h ((roughTriple_support_iff_product h).mpr hd)⟩
  · rintro ⟨hr, he⟩
    exact ⟨hr, he ▸ dvd_refl _⟩

/-- A two-support seat has only a unit or one prime in its complementary quotient. -/
theorem sqrt_roughPair_quotient_one_or_prime {n r p q c : ℕ}
    (hr : r ∈ canonicalRoughCandidates n (Nat.sqrt n))
    (h : (p, q) ∈ roughPairs n (Nat.sqrt n)) (hc : n ^ 2 + r = p * q * c) :
    c = 1 ∨ (c.Prime ∧ c ≤ n ∧ c ∈ paritySafeActiveSupport n r) := by
  have hlo := sqrt_roughPair_product_lower h
  have hgt := sqrt_roughPair_product_gt h
  have hpoint := squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets (Finset.mem_filter.mp hr).1
  dsimp only [SquareOffset] at hpoint
  have hfour := sqrtCutoff_power_four_gt n
  have hcpos : 0 < c := by
    by_contra hh
    have hz : c = 0 := by omega
    rw [hz, Nat.mul_zero] at hc
    omega
  have hclt : c < (Nat.sqrt n + 1) ^ 2 := by
    by_contra hh
    have hm := Nat.mul_le_mul hlo (show (Nat.sqrt n + 1) ^ 2 ≤ c by omega)
    have he : (Nat.sqrt n + 1) ^ 2 * (Nat.sqrt n + 1) ^ 2 = (Nat.sqrt n + 1) ^ 4 := by ring
    rw [he, ← hc] at hm
    omega
  by_cases h1 : c = 1
  · exact Or.inl h1
  · have hprime : c.Prime := by
      by_contra hh
      have hu := Nat.minFac_prime h1
      have hd : c.minFac ∣ n ^ 2 + r := hc ▸ dvd_mul_of_dvd_right (Nat.minFac_dvd c) (p * q)
      have hmin := sqrt_rough_prime_divisor_gt hr hu hd
      have hsquare := Nat.minFac_sq_le_self hcpos hh
      have hsq := Nat.mul_self_le_mul_self (show Nat.sqrt n + 1 ≤ c.minFac by omega)
      nlinarith
    have hcn : c ≤ n := by
      by_contra hh
      nlinarith [Nat.mul_le_mul (show n + 1 ≤ p * q by omega) (show n + 1 ≤ c by omega)]
    have hd : c ∣ n ^ 2 + r := hc ▸ dvd_mul_left c (p * q)
    exact Or.inr ⟨hprime, hcn, mem_paritySafeActiveSupport_iff_dvd.mpr
      ⟨prime_dvd_candidate_mem_active (Finset.mem_filter.mp hr).1 hprime hcn hd, hd⟩⟩

theorem sqrt_two_support_classification {n r p q : ℕ}
    (hr : r ∈ canonicalRoughCandidates n (Nat.sqrt n))
    (h : (p, q) ∈ roughPairs n (Nat.sqrt n))
    (hs : paritySafeActiveSupport n r = {p, q}) :
    n ^ 2 + r = p * q ∨ n ^ 2 + r = p ^ 2 * q ∨ n ^ 2 + r = p * q ^ 2 := by
  have hsupport : (p, q) ∈ Internal.upperPairs (paritySafeActiveSupport n r) := by
    obtain ⟨_, _, hpq⟩ := mem_roughPairs.mp h
    simp only [Internal.upperPairs, Finset.mem_filter, Finset.mem_offDiag, hs,
      Finset.mem_insert, Finset.mem_singleton]
    exact ⟨⟨Or.inl trivial, Or.inr trivial, hpq.ne⟩, hpq⟩
  obtain ⟨c, hc⟩ := (roughPair_support_iff_product h).mp hsupport
  rcases sqrt_roughPair_quotient_one_or_prime hr h hc with h1 | ⟨_, _, hcS⟩
  · left; simpa only [h1, Nat.mul_one] using hc
  · rw [hs, Finset.mem_insert, Finset.mem_singleton] at hcS
    rcases hcS with rfl | rfl
    · right; left; nlinarith [hc]
    · right; right; nlinarith [hc]

/-- Two active labels are at most n, so their squarefree product cannot reach the open shell. -/
theorem sqrt_two_support_repeated_prime {n r p q : ℕ}
    (hr : r ∈ canonicalRoughCandidates n (Nat.sqrt n))
    (h : (p, q) ∈ roughPairs n (Nat.sqrt n))
    (hs : paritySafeActiveSupport n r = {p, q}) :
    n ^ 2 + r = p ^ 2 * q ∨ n ^ 2 + r = p * q ^ 2 := by
  have hc := sqrt_two_support_classification hr h hs
  obtain ⟨hp, hq, _⟩ := mem_roughPairs.mp h
  have hpn := (mem_squareAnchorOddActivePrimes.mp (Finset.mem_filter.mp hp).1).2.1
  have hqn := (mem_squareAnchorOddActivePrimes.mp (Finset.mem_filter.mp hq).1).2.1
  have hshell := squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets (Finset.mem_filter.mp hr).1
  have hprod := Nat.mul_le_mul hpn hqn
  dsimp only [SquareOffset] at hshell
  rcases hc with hc | hc | hc
  · nlinarith
  · exact Or.inl hc
  · exact Or.inr hc

theorem sqrt_roughTriple_product_offset_mem {n p q s : ℕ}
    (h : (p, q, s) ∈ roughTriples n (Nat.sqrt n))
    (hlo : n ^ 2 < p * q * s) (hhi : p * q * s ≤ n ^ 2 + 2 * n) :
    p * q * s - n ^ 2 ∈ canonicalRoughCandidates n (Nat.sqrt n) := by
  obtain ⟨hp, hq, hs, _, _⟩ := mem_roughTriples.mp h
  obtain ⟨hpA, hpL⟩ := Finset.mem_filter.mp hp
  obtain ⟨hqA, hqL⟩ := Finset.mem_filter.mp hq
  obtain ⟨hsA, hsL⟩ := Finset.mem_filter.mp hs
  have hpP := (mem_squareAnchorOddActivePrimes.mp hpA).1
  have hqP := (mem_squareAnchorOddActivePrimes.mp hqA).1
  have hsP := (mem_squareAnchorOddActivePrimes.mp hsA).1
  have he : n ^ 2 + (p * q * s - n ^ 2) = p * q * s := by omega
  have hcop : Nat.Coprime (2 * n) (p * q * s) :=
    ((activePrime_reducedResidue_packet hpA).2.2.2.2.mul_right
      (activePrime_reducedResidue_packet hqA).2.2.2.2).mul_right
        (activePrime_reducedResidue_packet hsA).2.2.2.2
  apply Finset.mem_filter.mpr
  refine ⟨mem_squareAnchorOddPointCoprimeOffsets_iff_reducedResidue.mpr
    ⟨by dsimp only [SquareOffset]; omega, by simpa only [he] using hcop⟩, ?_⟩
  intro a ha haL hd
  have haP := (mem_squareAnchorOddActivePrimes.mp ha).1
  rw [he] at hd
  rcases haP.dvd_mul.mp hd with hd | hd
  · rcases haP.dvd_mul.mp hd with hd | hd
    · have := (hpP.dvd_iff_eq haP.ne_one).mp hd; omega
    · have := (hqP.dvd_iff_eq haP.ne_one).mp hd; omega
  · have := (hsP.dvd_iff_eq haP.ne_one).mp hd; omega

/-- Exact 0/1 triple cost: an eligible triple contributes only its own product, never a multiple. -/
theorem sqrt_roughTripleWave_card_eq_product_indicator {n p q s : ℕ}
    (h : (p, q, s) ∈ roughTriples n (Nat.sqrt n)) :
    (roughTripleWave n (Nat.sqrt n) p q s).card =
      if n ^ 2 < p * q * s ∧ p * q * s ≤ n ^ 2 + 2 * n then 1 else 0 := by
  classical
  by_cases he : n ^ 2 < p * q * s ∧ p * q * s ≤ n ^ 2 + 2 * n
  · rw [ite_eq_left he]
    apply Finset.card_eq_one.mpr
    refine ⟨p * q * s - n ^ 2, ?_⟩
    ext r
    rw [sqrt_roughTripleWave_eq_product_seat h, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hr, heq⟩; omega
    · intro hr; subst r
      exact ⟨sqrt_roughTriple_product_offset_mem h he.1 he.2, by omega⟩
  · rw [ite_eq_right he]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro r hr
    rw [sqrt_roughTripleWave_eq_product_seat h] at hr
    obtain ⟨hr, heq⟩ := Finset.mem_filter.mp hr
    have hs := squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets (Finset.mem_filter.mp hr).1
    dsimp only [SquareOffset] at hs
    exact he ⟨by omega, by omega⟩

noncomputable def sqrtRoughTripleProductsInShell (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (roughTriples n (Nat.sqrt n)).filter
    (fun a => n ^ 2 < a.1 * a.2.1 * a.2.2 ∧ a.1 * a.2.1 * a.2.2 ≤ n ^ 2 + 2 * n)

/-- A strict refinement of raw triple carry budgets: cost is a count of actual shell products. -/
theorem sqrt_roughTripleMoment_eq_product_count (n : ℕ) :
    roughTripleMoment n (Nat.sqrt n) = (sqrtRoughTripleProductsInShell n).card := by
  classical
  rw [sqrt_roughTripleMoment_eq_wave_sum]
  calc
    _ = ∑ a ∈ roughTriples n (Nat.sqrt n),
      (if n ^ 2 < a.1 * a.2.1 * a.2.2 ∧ a.1 * a.2.1 * a.2.2 ≤ n ^ 2 + 2 * n
        then (1 : ℕ) else 0) :=
      Finset.sum_congr rfl (fun _ ha => sqrt_roughTripleWave_card_eq_product_indicator ha)
    _ = _ := by rw [Finset.sum_boole]; rfl

/-- A square-scale divisor leaves at most one prime in its rough complementary quotient. -/
theorem sqrt_rough_square_quotient_one_or_prime {n r d c : ℕ}
    (hr : r ∈ canonicalRoughCandidates n (Nat.sqrt n))
    (hd : (Nat.sqrt n + 1) ^ 2 ≤ d) (hc : n ^ 2 + r = d * c) :
    c = 1 ∨ (c.Prime ∧ c ≤ n ∧ c ∈ paritySafeActiveSupport n r) := by
  have hs := squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets (Finset.mem_filter.mp hr).1
  dsimp only [SquareOffset] at hs
  have hfour := sqrtCutoff_power_four_gt n
  have hdsq := sqrt_successor_square_gt n
  have hdgt : n < d := lt_of_lt_of_le hdsq hd
  have hcpos : 0 < c := by
    by_contra hh
    have hz : c = 0 := by omega
    rw [hz, Nat.mul_zero] at hc
    omega
  have hclt : c < (Nat.sqrt n + 1) ^ 2 := by
    by_contra hh
    have hm := Nat.mul_le_mul hd (show (Nat.sqrt n + 1) ^ 2 ≤ c by omega)
    have he : (Nat.sqrt n + 1) ^ 2 * (Nat.sqrt n + 1) ^ 2 = (Nat.sqrt n + 1) ^ 4 := by ring
    rw [he, ← hc] at hm
    omega
  by_cases h1 : c = 1
  · exact Or.inl h1
  · have hprime : c.Prime := by
      by_contra hh
      have hu := Nat.minFac_prime h1
      have hdu : c.minFac ∣ n ^ 2 + r := hc ▸ dvd_mul_of_dvd_right (Nat.minFac_dvd c) d
      have hmin := sqrt_rough_prime_divisor_gt hr hu hdu
      have hsquare := Nat.minFac_sq_le_self hcpos hh
      have hsq := Nat.mul_self_le_mul_self (show Nat.sqrt n + 1 ≤ c.minFac by omega)
      nlinarith
    have hcn : c ≤ n := by
      by_contra hh
      have hm := Nat.mul_le_mul (show n + 1 ≤ d by omega) (show n + 1 ≤ c by omega)
      nlinarith
    have hdc : c ∣ n ^ 2 + r := hc ▸ dvd_mul_left c d
    exact Or.inr ⟨hprime, hcn, mem_paritySafeActiveSupport_iff_dvd.mpr
      ⟨prime_dvd_candidate_mem_active (Finset.mem_filter.mp hr).1 hprime hcn hdc, hdc⟩⟩

/-- Singleton rough points are exactly cubes or a small active prime times a prime above n. -/
theorem sqrt_singleton_point_cube_or_cross {n r p : ℕ}
    (hr : r ∈ canonicalRoughCandidates n (Nat.sqrt n))
    (hS : paritySafeActiveSupport n r = {p}) :
    n ^ 2 + r = p ^ 3 ∨ ∃ q, q.Prime ∧ n < q ∧ n ^ 2 + r = p * q := by
  have hpS : p ∈ paritySafeActiveSupport n r := by rw [hS]; exact Finset.mem_singleton_self p
  obtain ⟨hpA, hpd⟩ := mem_paritySafeActiveSupport_iff_dvd.mp hpS
  have hpP := mem_squareAnchorOddActivePrimes.mp hpA
  have hpL := (Finset.mem_filter.mp (rough_support_subset_labels hr hpS)).2
  obtain ⟨c, hc⟩ := hpd
  have hs := squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets (Finset.mem_filter.mp hr).1
  dsimp only [SquareOffset] at hs
  have hcpos : 0 < c := by
    by_contra hh
    have hz : c = 0 := by omega
    rw [hz, Nat.mul_zero] at hc
    omega
  have hc1 : c ≠ 1 := by
    intro h1
    rw [h1, Nat.mul_one] at hc
    nlinarith [hpP.2.1]
  by_cases hcP : c.Prime
  · right
    refine ⟨c, hcP, ?_, hc⟩
    by_contra hh
    have hd : c ∣ n ^ 2 + r := hc ▸ dvd_mul_left c p
    have ha := prime_dvd_candidate_mem_active (Finset.mem_filter.mp hr).1 hcP (by omega) hd
    have hcS := mem_paritySafeActiveSupport_iff_dvd.mpr ⟨ha, hd⟩
    rw [hS, Finset.mem_singleton] at hcS
    have hm := Nat.mul_self_le_mul_self hpP.2.1
    rw [hcS] at hc
    nlinarith
  · have huP := Nat.minFac_prime hc1
    have huD := Nat.minFac_dvd c
    have huSquare := Nat.minFac_sq_le_self hcpos hcP
    have huPoint : c.minFac ∣ n ^ 2 + r := hc ▸ dvd_mul_of_dvd_right huD p
    have hcLe : c ≤ n ^ 2 + r := by
      rw [hc]
      exact Nat.le_mul_of_pos_left c hpP.1.pos
    have huLe : c.minFac ≤ n := by nlinarith
    have huA := prime_dvd_candidate_mem_active (Finset.mem_filter.mp hr).1 huP huLe huPoint
    have huS := mem_paritySafeActiveSupport_iff_dvd.mpr ⟨huA, huPoint⟩
    rw [hS, Finset.mem_singleton] at huS
    rw [huS] at huD
    obtain ⟨d, hd⟩ := huD
    have hpoint : n ^ 2 + r = p ^ 2 * d := by rw [hc, hd]; ring
    have hlo : (Nat.sqrt n + 1) ^ 2 ≤ p ^ 2 := by
      simpa only [pow_two] using Nat.mul_self_le_mul_self (show Nat.sqrt n + 1 ≤ p by omega)
    rcases sqrt_rough_square_quotient_one_or_prime hr hlo hpoint with hd1 | ⟨_, _, hdS⟩
    · rw [hd1, Nat.mul_one] at hpoint
      have hm := Nat.mul_self_le_mul_self hpP.2.1
      nlinarith
    · rw [hS, Finset.mem_singleton] at hdS
      left
      rw [hdS] at hpoint
      simpa only [← pow_succ] using hpoint

end DkMath.NumberTheory.Legendre
