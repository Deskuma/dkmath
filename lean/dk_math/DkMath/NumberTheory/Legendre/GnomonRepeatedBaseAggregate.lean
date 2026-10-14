/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.GnomonRepeatedCarryPhase

#print "file: DkMath.NumberTheory.Legendre.GnomonRepeatedBaseAggregate"

namespace DkMath.NumberTheory.Legendre
open scoped BigOperators

/-- Eligible exponent intervals include every repeated power, with no target quotienting. -/
def gnomonRepeatedBaseExponents (n p : ℕ) : Finset ℕ :=
  Finset.Icc (gnomonRepeatedFirstExponent n p) (Nat.log p (n ^ 2))

noncomputable def gnomonRepeatedBaseWeight (n p : ℕ) : ℝ :=
  ((gnomonRepeatedBaseExponents n p).card : ℝ) * Real.log (p : ℝ)

/-- This exact base receiver is infrastructure, not the aggregate upper bound. -/
def gnomonRepeatedActiveBases (n : ℕ) : Finset ℕ :=
  (Finset.Icc 2 n).filter (fun p => p.Prime ∧ gnomonRepeatedBaseActive n p)

private theorem exponent_bounds {n p a : ℕ} (hn : 3 ≤ n) (hp : p.Prime)
    (ha : a ∈ gnomonRepeatedBaseExponents n p) :
    2 ≤ a ∧ 2 * n < p ^ a ∧ p ^ a ≤ n ^ 2 := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp ha
  have ht : 2 ≤ gnomonRepeatedFirstExponent n p := le_max_left _ _
  have hl : Nat.log p (2 * n) + 1 ≤ gnomonRepeatedFirstExponent n p := le_max_right _ _
  exact ⟨by omega, Nat.lt_pow_of_log_lt hp.one_lt (by omega),
    Nat.pow_le_of_le_log (by nlinarith : n ^ 2 ≠ 0) hhi⟩

private theorem prime_power_labels {n : ℕ} (hn : 3 ≤ n) :
    (gnomonRepeatedPhaseEnvelope n).filter IsPrimePow =
      (gnomonRepeatedActiveBases n).biUnion (fun p =>
        (gnomonRepeatedBaseExponents n p).image (fun a => p ^ a)) := by
  ext d
  constructor
  · intro hd
    obtain ⟨hE, hpp⟩ := Finset.mem_filter.mp hd
    obtain ⟨hband, hactive⟩ := Finset.mem_filter.mp hE
    obtain ⟨hI, hnp⟩ := Finset.mem_filter.mp hband
    obtain ⟨hlo, htop⟩ := Finset.mem_Icc.mp hI
    obtain ⟨p, a, hp, ha, he⟩ := (isPrimePow_nat_iff d).mp hpp
    have ha2 : 2 ≤ a := by
      by_contra h
      have ha1 : a = 1 := by omega
      have : d = p := by simpa [ha1] using he.symm
      exact hnp (this ▸ hp)
    have hm : d.minFac = p := by rw [← he, hp.pow_minFac (by omega)]
    have hp2 : p ^ 2 ≤ d := by
      rw [← he]
      exact Nat.pow_le_pow_right hp.pos ha2
    have hpn : p ≤ n := by nlinarith
    have hw : 2 * n < p ^ a := by omega
    have hlog := Nat.log_lt_of_lt_pow (by omega : 2 * n ≠ 0) hw
    have hfirst : gnomonRepeatedFirstExponent n p ≤ a := max_le ha2 (by omega)
    have hupper : a ≤ Nat.log p (n ^ 2) := Nat.le_log_of_pow_le hp.one_lt (by omega)
    exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hpn⟩, hp, hm ▸ hactive⟩,
      Finset.mem_image.mpr ⟨a, Finset.mem_Icc.mpr ⟨hfirst, hupper⟩, he⟩⟩
  · intro hd
    obtain ⟨p, hpB, hpd⟩ := Finset.mem_biUnion.mp hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hpd
    obtain ⟨_, hp, hactive⟩ := Finset.mem_filter.mp hpB
    obtain ⟨ha2, hw, ht⟩ := exponent_bounds hn hp ha
    have hm := hp.pow_minFac (by omega : a ≠ 0)
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, ht⟩,
        Nat.Prime.not_prime_pow ha2⟩, (by simpa only [hm] using hactive)⟩,
      (isPrimePow_nat_iff _).mpr ⟨p, a, hp, by omega, rfl⟩⟩

/-- Exact base-sum form of 040, preserving the complete exponent multiplicity. -/
theorem gnomonRepeatedPhaseBudget_eq_base_sum {n : ℕ} (hn : 3 ≤ n) :
    gnomonRepeatedPhaseBudget n =
      ∑ p ∈ gnomonRepeatedActiveBases n, gnomonRepeatedBaseWeight n p := by
  have hz : (∑ d ∈ (gnomonRepeatedPhaseEnvelope n).filter IsPrimePow,
      ArithmeticFunction.vonMangoldt d) = gnomonRepeatedPhaseBudget n := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hnot
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpp
    exact hnot (Finset.mem_filter.mpr ⟨hd, hpp⟩)
  rw [← hz, prime_power_labels hn]
  have hdis : Set.PairwiseDisjoint (↑(gnomonRepeatedActiveBases n))
      (fun p => (gnomonRepeatedBaseExponents n p).image (fun a => p ^ a)) := by
    intro p hp q hq hpq
    apply Finset.disjoint_left.mpr
    intro d hpd hqd
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hpd
    obtain ⟨b, hb, hf⟩ := Finset.mem_image.mp hqd
    have hpp := (Finset.mem_filter.mp hp).2.1
    have hqp := (Finset.mem_filter.mp hq).2.1
    have ha2 := (exponent_bounds hn hpp ha).1
    have hb2 := (exponent_bounds hn hqp hb).1
    have hm : d.minFac = p := by rw [← he, hpp.pow_minFac (by omega)]
    have hm' : d.minFac = q := by rw [← hf, hqp.pow_minFac (by omega)]
    exact hpq (hm.symm.trans hm')
  rw [Finset.sum_biUnion hdis]
  apply Finset.sum_congr rfl
  intro p hp
  have hpp := (Finset.mem_filter.mp hp).2.1
  rw [Finset.sum_image (Nat.pow_right_injective hpp.two_le).injOn]
  exact gnomonRepeatedExponentInterval_weight n hpp

/-- Below the square-width cutoff, preserve all exponents and discard activity. -/
def gnomonRepeatedSmallBases (n : ℕ) : Finset ℕ :=
  (Finset.Icc 2 n).filter (fun p => p.Prime ∧ p ^ 2 ≤ 2 * n)

/-- Integer square-root endpoints, with no prime or carry-bit tests. -/
def gnomonRepeatedSquareWindow (n k : ℕ) : Finset ℕ :=
  Finset.Icc (max (Nat.sqrt (n ^ 2 / k)) (Nat.sqrt (2 * n)) + 1)
    (min n (Nat.sqrt ((n ^ 2 + 2 * n) / k)))

/-- Drop primality in the large-square region and activity in the small region. -/
def gnomonRepeatedAggregateBases (n : ℕ) : Finset ℕ :=
  gnomonRepeatedSmallBases n ∪
    (Finset.Icc 2 (n - 1)).biUnion (gnomonRepeatedSquareWindow n)

noncomputable def gnomonRepeatedAggregateBudget (n : ℕ) : ℝ :=
  ∑ p ∈ gnomonRepeatedAggregateBases n, gnomonRepeatedBaseWeight n p

/-- For large-square bases, the first eligible repeated exponent is two. -/
theorem gnomonRepeatedFirstExponent_eq_two {n p : ℕ} (_hp : p.Prime)
    (hw : 2 * n < p ^ 2) : gnomonRepeatedFirstExponent n p = 2 := by
  have hlog : Nat.log p (2 * n) < 2 := by
    by_cases hn : n = 0
    · subst n
      simp
    · exact Nat.log_lt_of_lt_pow (by omega : 2 * n ≠ 0) hw
  unfold gnomonRepeatedFirstExponent
  omega

/-- Endpoint membership describes square multiples, without a primality test. -/
theorem mem_gnomonRepeatedSquareWindow {n k p : ℕ} (hk : 0 < k) :
    p ∈ gnomonRepeatedSquareWindow n k ↔
      p ≤ n ∧ 2 * n < p ^ 2 ∧ n ^ 2 < k * p ^ 2 ∧
        k * p ^ 2 ≤ n ^ 2 + 2 * n := by
  simp only [gnomonRepeatedSquareWindow, Finset.mem_Icc, Nat.add_one_le_iff,
    max_lt_iff, le_min_iff, Nat.sqrt_lt', Nat.le_sqrt']
  rw [Nat.div_lt_iff_lt_mul hk, Nat.le_div_iff_mul_le hk]
  constructor
  · rintro ⟨⟨hlo, hw⟩, hn, hhi⟩
    exact ⟨hn, hw, by simpa [Nat.mul_comm] using hlo,
      by simpa [Nat.mul_comm] using hhi⟩
  · rintro ⟨hn, hw, hlo, hhi⟩
    exact ⟨⟨by simpa [Nat.mul_comm] using hlo, hw⟩, hn,
      by simpa [Nat.mul_comm] using hhi⟩

/-- An active square base is routed to its canonical endpoint window. -/
theorem gnomonRepeatedActiveBase_square_window {n p : ℕ} (hn : 3 ≤ n)
    (hp : p ∈ gnomonRepeatedActiveBases n) (hw : 2 * n < p ^ 2) :
    let k := n ^ 2 / p ^ 2 + 1
    k ∈ Finset.Icc 2 (n - 1) ∧ p ∈ gnomonRepeatedSquareWindow n k := by
  obtain ⟨hI, hprime, hactive⟩ := Finset.mem_filter.mp hp
  have hpn := (Finset.mem_Icc.mp hI).2
  have hc : gnomonLowDivisorCarryBit n (p ^ 2) = 1 := by
    simpa only [gnomonRepeatedBaseActive, gnomonRepeatedFirstExponent_eq_two hprime hw]
      using hactive
  have hpacket := (gnomonNextShellMultiple_packet hw hc).1
  have hklo : 2 ≤ n ^ 2 / p ^ 2 + 1 := by
    have hle : p ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hpn 2
    have hp0 : 0 < p ^ 2 := pow_pos hprime.pos 2
    have hdiv : 1 ≤ n ^ 2 / p ^ 2 := (Nat.le_div_iff_mul_le hp0).mpr
      (by simpa using hle)
    omega
  have hkhi := gnomonNextShellMultiple_cofactor_lt hn hw
  refine ⟨Finset.mem_Icc.mpr ⟨hklo, by omega⟩,
    (mem_gnomonRepeatedSquareWindow (by omega : 0 < n ^ 2 / p ^ 2 + 1)).mpr
      ⟨hpn, hw, ?_, ?_⟩⟩
  · have := hpacket.1
    change n ^ 2 < p ^ 2 * (n ^ 2 / p ^ 2 + 1) at this
    simpa [Nat.mul_comm] using this
  · have := hpacket.2
    change p ^ 2 * (n ^ 2 / p ^ 2 + 1) < (n + 1) ^ 2 at this
    nlinarith

/-- The aggregate carrier drops both small-base activity and large-base primality. -/
theorem gnomonRepeatedActiveBases_subset_aggregate {n : ℕ} (hn : 3 ≤ n) :
    gnomonRepeatedActiveBases n ⊆ gnomonRepeatedAggregateBases n := by
  intro p hp
  by_cases hw : p ^ 2 ≤ 2 * n
  · obtain ⟨hI, hprime, _⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hI, hprime, hw⟩)
  · have h := gnomonRepeatedActiveBase_square_window hn hp (by omega)
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨n ^ 2 / p ^ 2 + 1, h.1, h.2⟩)

theorem gnomonRepeatedBaseWeight_nonneg (n p : ℕ) :
    0 ≤ gnomonRepeatedBaseWeight n p := by
  unfold gnomonRepeatedBaseWeight
  apply mul_nonneg (by positivity)
  by_cases hp : p = 0
  · simp [hp]
  · apply Real.log_nonneg
    exact_mod_cast (by omega : 1 ≤ p)

theorem gnomonRepeatedSquareWindow_subset_aggregate {n k : ℕ}
    (hk : k ∈ Finset.Icc 2 (n - 1)) :
    gnomonRepeatedSquareWindow n k ⊆ gnomonRepeatedAggregateBases n := by
  intro p hp
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k, hk, hp⟩)

/-- An extra integer base certifies the information discarded by the aggregate bound. -/
theorem gnomonRepeatedPhaseBudget_add_extra_le_aggregate {n p : ℕ} (hn : 3 ≤ n)
    (hp : p ∈ gnomonRepeatedAggregateBases n) (hz : p ∉ gnomonRepeatedActiveBases n) :
    gnomonRepeatedPhaseBudget n + gnomonRepeatedBaseWeight n p ≤
      gnomonRepeatedAggregateBudget n := by
  have hsub : insert p (gnomonRepeatedActiveBases n) ⊆ gnomonRepeatedAggregateBases n := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hp
    · exact gnomonRepeatedActiveBases_subset_aggregate hn hq
  have h := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun q _ _ => gnomonRepeatedBaseWeight_nonneg n q)
  rw [Finset.sum_insert hz, ← gnomonRepeatedPhaseBudget_eq_base_sum hn] at h
  change gnomonRepeatedBaseWeight n p + gnomonRepeatedPhaseBudget n ≤
    gnomonRepeatedAggregateBudget n at h
  linarith

/-- A genuine endpoint envelope: composite square bases may contribute positive weight. -/
theorem gnomonRepeatedPhaseBudget_le_aggregate {n : ℕ} (hn : 3 ≤ n) :
    gnomonRepeatedPhaseBudget n ≤ gnomonRepeatedAggregateBudget n := by
  rw [gnomonRepeatedPhaseBudget_eq_base_sum hn]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (gnomonRepeatedActiveBases_subset_aggregate hn)
    (fun p _ _ => gnomonRepeatedBaseWeight_nonneg n p)

/-- Each quotient window contains at most one integer base, even without primality. -/
theorem gnomonRepeatedSquareWindow_subsingleton {n k p q : ℕ} (hn : 3 ≤ n)
    (hk : 2 ≤ k) (hp : p ∈ gnomonRepeatedSquareWindow n k)
    (hq : q ∈ gnomonRepeatedSquareWindow n k) : p = q := by
  have hpos : 0 < k := by omega
  obtain ⟨hpn, _, hlo, _⟩ := (mem_gnomonRepeatedSquareWindow hpos).mp hp
  obtain ⟨hqn, _, hqlo, hqhi⟩ := (mem_gnomonRepeatedSquareWindow hpos).mp hq
  have ruled_out : ∀ a b : ℕ, a ≤ n → n ^ 2 < k * a ^ 2 →
      k * b ^ 2 ≤ n ^ 2 + 2 * n → ¬ a < b := by
    intro a b han hal hbh hab
    have hmul := Nat.mul_le_mul_left (k * a) han
    have hka : n < k * a := by nlinarith
    have hs : a ^ 2 + 2 * a + 1 ≤ b ^ 2 := by nlinarith
    have hs' := Nat.mul_le_mul_left k hs
    nlinarith
  have hp_hi := ((mem_gnomonRepeatedSquareWindow hpos).mp hp).2.2.2
  rcases lt_trichotomy p q with h | h | h
  · exact (ruled_out p q hpn hlo hqhi h).elim
  · exact h
  · exact (ruled_out q p hqn hqlo hp_hi h).elim

theorem card_gnomonRepeatedSquareWindow_le_one {n k : ℕ} (hn : 3 ≤ n) (hk : 2 ≤ k) :
    (gnomonRepeatedSquareWindow n k).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp q hq
  exact gnomonRepeatedSquareWindow_subsingleton hn hk hp hq

/-- Weighted endpoint evaluation: each quotient contributes either zero or one integer base. -/
theorem gnomonRepeatedSquareWindow_weight {n k : ℕ} (hn : 3 ≤ n) (hk : 2 ≤ k) :
    let L := max (Nat.sqrt (n ^ 2 / k)) (Nat.sqrt (2 * n)) + 1
    let U := min n (Nat.sqrt ((n ^ 2 + 2 * n) / k))
    (∑ p ∈ gnomonRepeatedSquareWindow n k, gnomonRepeatedBaseWeight n p) =
      if L ≤ U then gnomonRepeatedBaseWeight n U else 0 := by
  dsimp only
  split_ifs with h
  · have hu : min n (Nat.sqrt ((n ^ 2 + 2 * n) / k)) ∈
        gnomonRepeatedSquareWindow n k := Finset.mem_Icc.mpr ⟨h, le_rfl⟩
    have he : gnomonRepeatedSquareWindow n k = {min n (Nat.sqrt ((n ^ 2 + 2 * n) / k))} := by
      ext p
      constructor
      · intro hp
        exact Finset.mem_singleton.mpr (gnomonRepeatedSquareWindow_subsingleton hn hk hp hu)
      · intro hp
        exact (Finset.mem_singleton.mp hp) ▸ hu
    rw [he, Finset.sum_singleton]
  · have he : gnomonRepeatedSquareWindow n k = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
    rw [he, Finset.sum_empty]

/-- Any base in a quotient window has that quotient as its canonical routing value. -/
theorem gnomonRepeatedSquareWindow_quotient {n k p : ℕ} (hk : 0 < k)
    (hp : p ∈ gnomonRepeatedSquareWindow n k) : k = n ^ 2 / p ^ 2 + 1 := by
  obtain ⟨_, hw, hlo, hhi⟩ := (mem_gnomonRepeatedSquareWindow hk).mp hp
  have hp0 : 0 < p ^ 2 := by omega
  have hy : SquareCell n (k * p ^ 2) := ⟨hlo, by nlinarith⟩
  have hdiv : p ^ 2 ∣ k * p ^ 2 := dvd_mul_left _ _
  have hc := gnomonLarge_divisor_carry hw hy hdiv
  have he := gnomonNextShellMultiple_unique hw hc hy hdiv
  change k * p ^ 2 = p ^ 2 * (n ^ 2 / p ^ 2 + 1) at he
  rw [Nat.mul_comm k (p ^ 2)] at he
  exact Nat.eq_of_mul_eq_mul_left hp0 he

/-- Distinct quotient windows are disjoint, so their weights need no collision factor. -/
theorem gnomonRepeatedSquareWindows_disjoint {n k j : ℕ}
    (hk : 0 < k) (hj : 0 < j) (hne : k ≠ j) :
    Disjoint (gnomonRepeatedSquareWindow n k) (gnomonRepeatedSquareWindow n j) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact hne ((gnomonRepeatedSquareWindow_quotient hk hp).trans
    (gnomonRepeatedSquareWindow_quotient hj hq).symm)

/-- A scalar endpoint sum, without enumerating active prime bases or later carry bits. -/
theorem gnomonRepeatedAggregateBudget_eq_endpoint_sum {n : ℕ} (hn : 3 ≤ n) :
    gnomonRepeatedAggregateBudget n =
      (∑ p ∈ gnomonRepeatedSmallBases n, gnomonRepeatedBaseWeight n p) +
      ∑ k ∈ Finset.Icc 2 (n - 1),
        if max (Nat.sqrt (n ^ 2 / k)) (Nat.sqrt (2 * n)) + 1 ≤
            min n (Nat.sqrt ((n ^ 2 + 2 * n) / k)) then
          gnomonRepeatedBaseWeight n (min n (Nat.sqrt ((n ^ 2 + 2 * n) / k))) else 0 := by
  have hdis : Disjoint (gnomonRepeatedSmallBases n)
      ((Finset.Icc 2 (n - 1)).biUnion (gnomonRepeatedSquareWindow n)) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hw := (Finset.mem_filter.mp hp).2.2
    obtain ⟨k, hk, hpk⟩ := Finset.mem_biUnion.mp hq
    have hk2 := (Finset.mem_Icc.mp hk).1
    have hw' := ((mem_gnomonRepeatedSquareWindow (by omega : 0 < k)).mp hpk).2.1
    omega
  have hpair : Set.PairwiseDisjoint (↑(Finset.Icc 2 (n - 1)))
      (gnomonRepeatedSquareWindow n) := by
    intro k hk j hj hne
    have hk2 := (Finset.mem_Icc.mp hk).1
    have hj2 := (Finset.mem_Icc.mp hj).1
    exact gnomonRepeatedSquareWindows_disjoint (by omega) (by omega) hne
  unfold gnomonRepeatedAggregateBudget gnomonRepeatedAggregateBases
  rw [Finset.sum_union hdis, Finset.sum_biUnion hpair]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  exact gnomonRepeatedSquareWindow_weight hn (Finset.mem_Icc.mp hk).1

/-- Each prime base's entire retained interval costs at most the old log cutoff. -/
theorem gnomonRepeatedBaseWeight_le_log_square {n p : ℕ} (hn : 3 ≤ n) (hp : p.Prime) :
    gnomonRepeatedBaseWeight n p ≤ Real.log ((n : ℝ) ^ 2) := by
  have hcard : (gnomonRepeatedBaseExponents n p).card ≤ Nat.log p (n ^ 2) := by
    unfold gnomonRepeatedBaseExponents
    rw [Nat.card_Icc]
    have htwo : 2 ≤ gnomonRepeatedFirstExponent n p := le_max_left _ _
    omega
  have hc : ((gnomonRepeatedBaseExponents n p).card : ℝ) ≤
      (Nat.log p (n ^ 2) : ℝ) := by exact_mod_cast hcard
  have hl : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hpow : p ^ Nat.log p (n ^ 2) ≤ n ^ 2 :=
    Nat.pow_le_of_le_log (by nlinarith : n ^ 2 ≠ 0) le_rfl
  have hreal : (p : ℝ) ^ Nat.log p (n ^ 2) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hpow
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hlog := Real.log_le_log (pow_pos hpR _) hreal
  rw [Real.log_pow] at hlog
  exact (mul_le_mul_of_nonneg_right hc hl).trans hlog

/-- A controlled small-base bound, preserving unrestricted exponent multiplicity. -/
theorem gnomonRepeatedSmallBaseMass_le_sqrt_log {n : ℕ} (hn : 3 ≤ n) :
    (∑ p ∈ gnomonRepeatedSmallBases n, gnomonRepeatedBaseWeight n p) ≤
      (Nat.sqrt (2 * n) : ℝ) * Real.log ((n : ℝ) ^ 2) := by
  have hsub : gnomonRepeatedSmallBases n ⊆ Finset.Icc 1 (Nat.sqrt (2 * n)) := by
    intro p hp
    obtain ⟨hI, _, hw⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hI).1; omega,
      Nat.le_sqrt'.mpr hw⟩
  have hcard : (gnomonRepeatedSmallBases n).card ≤ Nat.sqrt (2 * n) := by
    have hc := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hc
    omega
  have hsum : (∑ p ∈ gnomonRepeatedSmallBases n, gnomonRepeatedBaseWeight n p) ≤
      ∑ _p ∈ gnomonRepeatedSmallBases n, Real.log ((n : ℝ) ^ 2) := by
    apply Finset.sum_le_sum
    intro p hp
    exact gnomonRepeatedBaseWeight_le_log_square hn (Finset.mem_filter.mp hp).2.1
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  have hcardR : ((gnomonRepeatedSmallBases n).card : ℝ) ≤ (Nat.sqrt (2 * n) : ℝ) :=
    by exact_mod_cast hcard
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log ((n : ℝ) ^ 2) := Real.log_nonneg (by nlinarith)
  exact hsum.trans (mul_le_mul_of_nonneg_right hcardR hlog)

/-- The endpoint envelope combines with the existing strongest small-phase estimate. -/
noncomputable def gnomonBaseAggregateCorrectionBudget (n : ℕ) : ℝ :=
  Chebyshev.psi (2 * n) - gnomonSmallPhaseExcludedMass n +
    gnomonRepeatedAggregateBudget n + shellHigherPrimePowerReciprocalBudget n

theorem gnomonRepeatPhaseCorrectionBudget_le_baseAggregate {n : ℕ} (hn : 3 ≤ n) :
    gnomonRepeatPhaseCorrectionBudget n ≤ gnomonBaseAggregateCorrectionBudget n := by
  have h := gnomonRepeatedPhaseBudget_le_aggregate hn
  unfold gnomonRepeatPhaseCorrectionBudget gnomonBaseAggregateCorrectionBudget
  linarith

theorem gnomonNonSingletonCorrection_le_baseAggregate {n : ℕ} (hn : 3 ≤ n) :
    gnomonNonSingletonCorrection n ≤ gnomonBaseAggregateCorrectionBudget n :=
  (gnomonNonSingletonCorrection_le_repeatPhaseBudget hn).trans
    (gnomonRepeatPhaseCorrectionBudget_le_baseAggregate hn)

theorem exists_prime_squareCell_of_baseAggregateBudget_lt {n : ℕ} (hn : 3 ≤ n)
    (hstrict : gnomonCofactorWindowMass n + gnomonBaseAggregateCorrectionBudget n <
      Real.log (GnomonPascalCell n : ℝ)) : ∃ p, p.Prime ∧ SquareCell n p := by
  apply exists_prime_squareCell_of_repeatPhaseBudget_lt hn
  have h := gnomonRepeatPhaseCorrectionBudget_le_baseAggregate hn
  linarith

end DkMath.NumberTheory.Legendre
