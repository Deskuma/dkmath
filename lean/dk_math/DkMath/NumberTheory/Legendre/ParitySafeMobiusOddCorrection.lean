/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeMobiusWave

#print "file: DkMath.NumberTheory.Legendre.ParitySafeMobiusOddCorrection"

/-!
## ParitySafeMobiusOddCorrection

This module folds the two-adic channel of the PRIM-L038 ledger.  The
remaining correction is indexed by odd divisors of the anchor `n`, and is
identified with the cardinality loss from the unfiltered odd quotient
interval.  The construction is finite and exact; it supplies no analytic
estimate and no proof of Legendre's conjecture.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open scoped ArithmeticFunction.Moebius BigOperators

/-! ### PRIM-L039.1: odd quotient intervals and channel counts -/

/-- The quotient interval before imposing anchor coprimality. -/
noncomputable def paritySafeOddRawQuotientInterval
    (n q : ℕ) : Finset ℕ :=
  (Finset.Ioc ((n ^ 2) / q) ((n ^ 2 + 2 * n) / q)).filter Odd

/-- The nonnegative floor difference counting odd multiples of `d`. -/
def paritySafeOddMultipleFloorDelta (A B d : ℕ) : ℕ :=
  (B / d - A / d) - (B / (2 * d) - A / (2 * d))

private theorem odd_multiple_delta_one_eq_half_sub
    {A B : ℕ} (hAB : A ≤ B) :
    paritySafeOddMultipleFloorDelta A B 1 =
      (B + 1) / 2 - (A + 1) / 2 := by
  unfold paritySafeOddMultipleFloorDelta
  omega

private theorem card_filter_dvd_Ioc_eq_sub_div
    {A B d : ℕ} (hAB : A ≤ B) :
    ((Finset.Ioc A B).filter (fun k => d ∣ k)).card = B / d - A / d := by
  have ht :
      (Finset.Ioc A B).filter (fun k => d ∣ k) =
        (Finset.Ioc 0 B).filter (fun k => d ∣ k) \
          (Finset.Ioc 0 A).filter (fun k => d ∣ k) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff]
    omega
  have hsub :
      (Finset.Ioc 0 A).filter (fun k => d ∣ k) ⊆
        (Finset.Ioc 0 B).filter (fun k => d ∣ k) := by
    intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hkIoc, hdk⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, hdk⟩
    have hkIoc' := Finset.mem_Ioc.mp hkIoc
    exact Finset.mem_Ioc.mpr ⟨hkIoc'.1, by omega⟩
  rw [ht, Finset.card_sdiff_of_subset hsub]
  rw [Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div]

private theorem card_filter_odd_Ioc_eq_half_sub
    {A B : ℕ} (hAB : A ≤ B) :
    ((Finset.Ioc A B).filter Odd).card = (B + 1) / 2 - (A + 1) / 2 := by
  have ht :
      (Finset.Ioc A B).filter Odd =
        Finset.Ioc A B \
          (Finset.Ioc A B).filter (fun k => 2 ∣ k) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff]
    constructor
    · rintro ⟨hk, hodd⟩
      refine ⟨hk, ?_⟩
      intro hev
      exact (Nat.not_even_iff_odd.mpr hodd)
        (even_iff_two_dvd.mpr hev.2)
    · rintro ⟨hk, hnot⟩
      refine ⟨hk, Nat.not_even_iff_odd.mp ?_⟩
      intro heven
      apply hnot
      exact ⟨hk, even_iff_two_dvd.mp heven⟩
  have hsub :
      (Finset.Ioc A B).filter (fun k => 2 ∣ k) ⊆ Finset.Ioc A B :=
    Finset.filter_subset _ _
  rw [ht, Finset.card_sdiff_of_subset hsub, Nat.card_Ioc]
  rw [card_filter_dvd_Ioc_eq_sub_div hAB]
  omega

/-- Every L037 reduced quotient is an odd raw quotient. -/
theorem paritySafeReducedQuotientInterval_subset_oddRaw
    {n q : ℕ} :
    paritySafeReducedQuotientInterval n q ⊆
      paritySafeOddRawQuotientInterval n q := by
  intro k hk
  have hk' := Finset.mem_filter.mp hk
  apply Finset.mem_filter.mpr
  exact ⟨hk'.1, (coprime_two_mul_iff_coprime_and_odd.mp hk'.2).2⟩

/-- The raw odd quotient interval has its exact half-open cardinality. -/
theorem paritySafeOddRawQuotientInterval_card_eq
    {n q : ℕ} (_hqpos : 0 < q) :
    (paritySafeOddRawQuotientInterval n q).card =
      ((((n ^ 2 + 2 * n) / q) + 1) / 2 -
        ((n ^ 2 / q) + 1) / 2) := by
  unfold paritySafeOddRawQuotientInterval
  apply card_filter_odd_Ioc_eq_half_sub
  exact Nat.div_le_div_right (by omega)

private theorem filter_odd_dvd_eq_sdiff_two_mul
    {A B d : ℕ} (hdOdd : Odd d) :
    (Finset.Ioc A B).filter (fun k => Odd k ∧ d ∣ k) =
      (Finset.Ioc A B).filter (fun k => d ∣ k) \
        (Finset.Ioc A B).filter (fun k => 2 * d ∣ k) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_sdiff]
  constructor
  · rintro ⟨hk, hodd, hdk⟩
    refine ⟨⟨hk, hdk⟩, ?_⟩
    intro h2d
    apply (Nat.not_even_iff_odd.mpr hodd)
    apply even_iff_two_dvd.mpr
    rcases h2d with ⟨_, h2d⟩
    rcases h2d with ⟨t, ht⟩
    exact ⟨d * t, by rw [ht]; ring⟩
  · rintro ⟨⟨hk, hdk⟩, hnot⟩
    have hodd : Odd k := by
      apply Nat.not_even_iff_odd.mp
      intro hkEven
      rcases hdk with ⟨m, hm⟩
      have hdmEven : Even (d * m) := by
        simpa [hm] using hkEven
      have hmEven : Even m :=
        (Nat.even_mul.mp hdmEven).resolve_left
          (Nat.not_even_iff_odd.mpr hdOdd)
      rcases even_iff_two_dvd.mp hmEven with ⟨t, ht⟩
      apply hnot
      refine ⟨hk, t, ?_⟩
      rw [hm, ht]
      ring
    exact ⟨hk, hodd, hdk⟩

private theorem card_filter_odd_dvd_Ioc_eq_delta
    {A B d : ℕ} (hdOdd : Odd d) (hAB : A ≤ B) :
    ((Finset.Ioc A B).filter (fun k => Odd k ∧ d ∣ k)).card =
      paritySafeOddMultipleFloorDelta A B d := by
  rw [filter_odd_dvd_eq_sdiff_two_mul hdOdd]
  have hsub :
      (Finset.Ioc A B).filter (fun k => 2 * d ∣ k) ⊆
        (Finset.Ioc A B).filter (fun k => d ∣ k) := by
    intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hkIoc, hdk⟩
    apply Finset.mem_filter.mpr
    exact ⟨hkIoc, dvd_trans (by simp [Nat.mul_comm]) hdk⟩
  rw [Finset.card_sdiff_of_subset hsub]
  rw [card_filter_dvd_Ioc_eq_sub_div hAB,
    card_filter_dvd_Ioc_eq_sub_div hAB]
  rfl

/-! ### PRIM-L039.2: odd-divisor Möbius ledger -/

private theorem sum_moebius_divisors_eq_indicator (m : ℕ) :
    (∑ d ∈ m.divisors, ArithmeticFunction.moebius d : ℤ) =
      if m = 1 then 1 else 0 := by
  cases m with
  | zero => simp
  | succ m =>
      have h := congrArg (fun f : ArithmeticFunction ℤ => f (m + 1))
        ArithmeticFunction.coe_zeta_mul_moebius
      rw [← ArithmeticFunction.coe_zeta_mul_apply]
      exact h

private theorem divisors_filter_dvd_gcd
    {M k : ℕ} (hM : 0 < M) :
    M.divisors.filter (fun d => d ∣ k) = (M.gcd k).divisors := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hdM, _⟩, hdk⟩
    exact ⟨Nat.dvd_gcd hdM hdk, Nat.gcd_ne_zero_left hM.ne'⟩
  · intro hdg
    exact ⟨⟨Nat.dvd_trans hdg.1 (Nat.gcd_dvd_left M k), hM.ne'⟩,
      Nat.dvd_trans hdg.1 (Nat.gcd_dvd_right M k)⟩

private theorem card_filter_odd_coprime_Ioc_eq_odd_moebius_sum
    {M A B : ℕ} (hM : 0 < M) (hAB : A ≤ B) :
    (((Finset.Ioc A B).filter (fun k => Odd k ∧ Nat.Coprime M k)).card : ℤ) =
      ∑ d ∈ M.divisors,
        if Odd d then ArithmeticFunction.moebius d *
          (paritySafeOddMultipleFloorDelta A B d : ℤ) else 0 := by
  classical
  let S : Finset ℕ := Finset.Ioc A B
  have hpoint (k : ℕ) :
      (if Odd k ∧ Nat.Coprime M k then (1 : ℤ) else 0) =
        if Odd k then
          ∑ d ∈ M.divisors,
            if d ∣ k then ArithmeticFunction.moebius d else 0
        else 0 := by
    by_cases hodd : Odd k
    · simp only [hodd, true_and, ite_true]
      have hfilter := divisors_filter_dvd_gcd hM (k := k)
      have hsum :
          (∑ d ∈ M.divisors, if d ∣ k then ArithmeticFunction.moebius d else 0) =
            ∑ d ∈ (M.gcd k).divisors, ArithmeticFunction.moebius d := by
        rw [← Finset.sum_filter]
        exact congrArg (fun t => ∑ d ∈ t, ArithmeticFunction.moebius d) hfilter
      rw [hsum, sum_moebius_divisors_eq_indicator]
    · simp [hodd]
  have hsum_points :
      (∑ k ∈ S, if Odd k ∧ Nat.Coprime M k then (1 : ℤ) else 0) =
        ∑ k ∈ S, if Odd k then
          ∑ d ∈ M.divisors,
            if d ∣ k then ArithmeticFunction.moebius d else 0
        else 0 := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hpoint k
  calc
    (((Finset.Ioc A B).filter (fun k => Odd k ∧ Nat.Coprime M k)).card : ℤ) =
        ∑ k ∈ S, if Odd k ∧ Nat.Coprime M k then (1 : ℤ) else 0 := by
      change (((S.filter (fun k => Odd k ∧ Nat.Coprime M k)).card : ℤ)) = _
      exact Finset.natCast_card_filter (R := ℤ)
        (fun k => Odd k ∧ Nat.Coprime M k) S
    _ = ∑ k ∈ S, if Odd k then
          ∑ d ∈ M.divisors,
            if d ∣ k then ArithmeticFunction.moebius d else 0
        else 0 := hsum_points
    _ = ∑ k ∈ S.filter Odd, ∑ d ∈ M.divisors,
          if d ∣ k then ArithmeticFunction.moebius d else 0 := by
      rw [Finset.sum_filter]
    _ = ∑ d ∈ M.divisors, ∑ k ∈ S.filter Odd,
          if d ∣ k then ArithmeticFunction.moebius d else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ M.divisors,
          if Odd d then ArithmeticFunction.moebius d *
            (paritySafeOddMultipleFloorDelta A B d : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro d _hd
      rw [← Finset.sum_filter]
      have hfilter :
          (S.filter Odd).filter (fun k => d ∣ k) =
            (Finset.Ioc A B).filter (fun k => Odd k ∧ d ∣ k) := by
        ext k
        dsimp [S]
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        tauto
      rw [hfilter]
      simp only [Finset.sum_const]
      by_cases hdOdd : Odd d
      · rw [card_filter_odd_dvd_Ioc_eq_delta hdOdd hAB]
        simp only [ite_eq_left hdOdd]
        simp only [nsmul_eq_mul]
        ring
      · have hdEven : Even d := Nat.not_odd_iff_even.mp hdOdd
        have hempty :
            (Finset.Ioc A B).filter (fun k => Odd k ∧ d ∣ k) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro k hk
          rintro ⟨hodd, hdk⟩
          rcases hdk with ⟨m, hm⟩
          rcases even_iff_two_dvd.mp hdEven with ⟨t, ht⟩
          apply (Nat.not_even_iff_odd.mpr hodd)
          exact even_iff_two_dvd.mpr ⟨t * m, by rw [hm, ht]; ring⟩
        rw [hempty]
        simp [hdOdd]

/-! ### PRIM-L039.3: wave correction and sign -/

/-- The signed correction left after removing the raw odd channel. -/
noncomputable def paritySafeOddMobiusCorrection (n q : ℕ) : ℤ :=
  ∑ d ∈ n.divisors,
    if Odd d ∧ d ≠ 1 then ArithmeticFunction.moebius d *
      (paritySafeOddMultipleFloorDelta ((n ^ 2) / q)
        ((n ^ 2 + 2 * n) / q) d : ℤ) else 0

/-- The correction is indexed only by nontrivial odd divisors of the anchor. -/
theorem paritySafeOddMobiusCorrection_eq_odd_divisor_sum
    {n q : ℕ} :
    paritySafeOddMobiusCorrection n q =
      ∑ d ∈ n.divisors,
        if Odd d ∧ d ≠ 1 then ArithmeticFunction.moebius d *
          (paritySafeOddMultipleFloorDelta ((n ^ 2) / q)
            ((n ^ 2 + 2 * n) / q) d : ℤ) else 0 := by
  rfl

/-- Exact wave decomposition into raw odd occupancy and odd-anchor correction. -/
theorem paritySafeActiveWave_card_eq_oddRaw_add_correction
    {n q : ℕ} (hq : q ∈ squareAnchorOddActivePrimes n) :
    ((paritySafeActiveWaveOffsets n q).card : ℤ) =
      (paritySafeOddRawQuotientInterval n q).card +
        paritySafeOddMobiusCorrection n q := by
  classical
  have hq' := activePrime_reducedResidue_packet hq
  have hn : 0 < n := lt_of_lt_of_le hq'.1.pos hq'.2.1
  have hAB : (n ^ 2) / q ≤ (n ^ 2 + 2 * n) / q :=
    Nat.div_le_div_right (by omega)
  have hledger := card_filter_odd_coprime_Ioc_eq_odd_moebius_sum
    hn hAB
  have hred :
      (paritySafeReducedQuotientInterval n q).card =
        ((Finset.Ioc ((n ^ 2) / q) ((n ^ 2 + 2 * n) / q)).filter
          (fun k => Odd k ∧ Nat.Coprime n k)).card := by
    apply congrArg Finset.card
    ext k
    simp only [paritySafeReducedQuotientInterval, Finset.mem_filter,
      Finset.mem_Ioc]
    constructor
    · rintro ⟨hi, hcop⟩
      exact ⟨hi, (coprime_two_mul_iff_coprime_and_odd.mp hcop).2,
        (coprime_two_mul_iff_coprime_and_odd.mp hcop).1⟩
    · rintro ⟨hi, hodd, hcop⟩
      exact ⟨hi, coprime_two_mul_iff_coprime_and_odd.mpr ⟨hcop, hodd⟩⟩
  have hwave := card_paritySafeActiveWaveOffsets_eq_reducedQuotientInterval hq
  rw [hwave, hred, hledger]
  have hraw := card_filter_odd_Ioc_eq_half_sub hAB
  rw [show (paritySafeOddRawQuotientInterval n q).card =
      ((((n ^ 2 + 2 * n) / q) + 1) / 2 -
        ((n ^ 2 / q) + 1) / 2) by
      unfold paritySafeOddRawQuotientInterval
      exact hraw]
  unfold paritySafeOddMobiusCorrection
  have hone : 1 ∈ n.divisors := Nat.one_mem_divisors.mpr hn.ne'
  have hsplit :
      (∑ d ∈ n.divisors, if Odd d then ArithmeticFunction.moebius d *
          (paritySafeOddMultipleFloorDelta ((n ^ 2) / q)
            ((n ^ 2 + 2 * n) / q) d : ℤ) else 0) =
        (paritySafeOddMultipleFloorDelta ((n ^ 2) / q)
          ((n ^ 2 + 2 * n) / q) 1 : ℤ) +
          paritySafeOddMobiusCorrection n q := by
    unfold paritySafeOddMobiusCorrection
    rw [← Finset.sum_erase_add (s := n.divisors)
      (f := fun d => if Odd d then ArithmeticFunction.moebius d *
        (paritySafeOddMultipleFloorDelta ((n ^ 2) / q)
          ((n ^ 2 + 2 * n) / q) d : ℤ) else 0) hone]
    simp only [ArithmeticFunction.moebius_apply_one, one_mul]
    rw [add_comm]
    congr 1
    have hset :
        (n.divisors.erase 1).filter Odd =
          n.divisors.filter (fun d => Odd d ∧ d ≠ 1) := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_erase, Nat.mem_divisors]
      tauto
    rw [← Finset.sum_filter, ← Finset.sum_filter, hset]
  rw [hsplit]
  have hdelta_one :
      paritySafeOddMultipleFloorDelta ((n ^ 2) / q)
        ((n ^ 2 + 2 * n) / q) 1 =
        ((((n ^ 2 + 2 * n) / q) + 1) / 2 -
          ((n ^ 2 / q) + 1) / 2 : ℕ) := by
    exact odd_multiple_delta_one_eq_half_sub hAB
  rw [hdelta_one]
  simp only [paritySafeOddMobiusCorrection]

/-- The odd-anchor correction is always nonpositive. -/
theorem paritySafeOddMobiusCorrection_nonpos
    {n q : ℕ} (hq : q ∈ squareAnchorOddActivePrimes n) :
    paritySafeOddMobiusCorrection n q ≤ 0 := by
  have hdecomp := paritySafeActiveWave_card_eq_oddRaw_add_correction hq
  have hsubset := paritySafeReducedQuotientInterval_subset_oddRaw
    (n := n) (q := q)
  have hcard :
      (paritySafeReducedQuotientInterval n q).card ≤
        (paritySafeOddRawQuotientInterval n q).card :=
    Finset.card_le_card hsubset
  have hwave := card_paritySafeActiveWaveOffsets_eq_reducedQuotientInterval hq
  rw [hwave] at hdecomp
  omega

/-- Strict negativity follows when an odd raw quotient is non-coprime to `n`. -/
theorem paritySafeOddMobiusCorrection_neg_of_exists_not_coprime
    {n q : ℕ} (hq : q ∈ squareAnchorOddActivePrimes n)
    (hk : ∃ k ∈ paritySafeOddRawQuotientInterval n q,
      ¬ Nat.Coprime n k) :
    paritySafeOddMobiusCorrection n q < 0 := by
  have hsubset := paritySafeReducedQuotientInterval_subset_oddRaw
    (n := n) (q := q)
  have hnot :
      ¬ paritySafeOddRawQuotientInterval n q ⊆
        paritySafeReducedQuotientInterval n q := by
    intro hrev
    rcases hk with ⟨k, hkraw, hknc⟩
    have hred : k ∈ paritySafeReducedQuotientInterval n q := hrev hkraw
    have hred' := Finset.mem_filter.mp hred
    exact hknc ((coprime_two_mul_iff_coprime_and_odd.mp hred'.2).1)
  have hcardlt :
      (paritySafeReducedQuotientInterval n q).card <
        (paritySafeOddRawQuotientInterval n q).card :=
    Finset.card_lt_card ⟨hsubset, hnot⟩
  have hwave := card_paritySafeActiveWaveOffsets_eq_reducedQuotientInterval hq
  have hdecomp := paritySafeActiveWave_card_eq_oddRaw_add_correction hq
  rw [hwave] at hdecomp
  omega

/-! ### PRIM-L039.4: concrete witness and global upper ledger -/

/-- The supplied `(n,q)=(6,5)` wave has one raw odd quotient and no reduced one. -/
theorem paritySafeOddCorrection_six_five_witness :
    5 ∈ squareAnchorOddActivePrimes 6 ∧
      (paritySafeOddRawQuotientInterval 6 5).card = 1 ∧
      (paritySafeReducedQuotientInterval 6 5).card = 0 ∧
      paritySafeOddMobiusCorrection 6 5 = -1 := by
  have hq : 5 ∈ squareAnchorOddActivePrimes 6 := by
    norm_num [squareAnchorOddActivePrimes]
  have hraw : (paritySafeOddRawQuotientInterval 6 5).card = 1 := by
    rw [paritySafeOddRawQuotientInterval_card_eq (by norm_num : 0 < (5 : ℕ))]
    norm_num
  have hred : (paritySafeReducedQuotientInterval 6 5).card = 0 := by
    decide
  have hc := paritySafeActiveWave_card_eq_oddRaw_add_correction hq
  have hw := card_paritySafeActiveWaveOffsets_eq_reducedQuotientInterval hq
  rw [hw, hred, hraw] at hc
  refine ⟨hq, hraw, hred, ?_⟩
  omega

/-- The global incidence is bounded by the sum of raw odd wave occupancies. -/
theorem paritySafeIncidenceCount_le_oddRaw_sum
    (n : ℕ) :
    (paritySafeIncidenceCount n : ℤ) ≤
      ∑ q ∈ squareAnchorOddActivePrimes n,
        (paritySafeOddRawQuotientInterval n q).card := by
  classical
  rw [show paritySafeIncidenceCount n =
      ∑ q ∈ squareAnchorOddActivePrimes n,
        (paritySafeActiveWaveOffsets n q).card by rfl]
  push_cast
  apply Finset.sum_le_sum
  intro q hq
  have hdecomp := paritySafeActiveWave_card_eq_oddRaw_add_correction hq
  have hc := paritySafeOddMobiusCorrection_nonpos hq
  omega

end DkMath.NumberTheory.Legendre
