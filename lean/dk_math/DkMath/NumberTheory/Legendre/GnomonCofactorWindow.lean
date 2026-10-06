/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.GnomonCarryFiber
import Mathlib.Data.Nat.Choose.Dvd

#print "file: DkMath.NumberTheory.Legendre.GnomonCofactorWindow"

/-! Singleton carry labels have exact cofactor windows. Binomial divisibility
and odd spacing give an independent envelope; its strict consumer is conditional. -/

namespace DkMath.NumberTheory.Legendre

open scoped BigOperators

/-- The prime, hence depth-one, part of the large carry mass. -/
noncomputable def gnomonSingletonCarryMass (n : ℕ) : ℝ :=
  ∑ p ∈ (gnomonPascalLargeCarryEvents n).filter Nat.Prime,
    ArithmeticFunction.vonMangoldt p

/-- The remaining large labels are genuine higher powers of their prime bases. -/
noncomputable def gnomonRepeatedCarryMass (n : ℕ) : ℝ :=
  ∑ d ∈ (gnomonPascalLargeCarryEvents n).filter (fun d => ¬ d.Prime),
    ArithmeticFunction.vonMangoldt d

theorem gnomonPascalLargeCarryMass_eq_repeated_add_singleton (n : ℕ) :
    gnomonPascalLargeCarryMass n =
      gnomonRepeatedCarryMass n + gnomonSingletonCarryMass n := by
  unfold gnomonPascalLargeCarryMass gnomonRepeatedCarryMass gnomonSingletonCarryMass
  rw [add_comm, Finset.sum_filter_add_sum_filter_not]

/-- Natural quotient endpoints; width excludes every repeated-power base. -/
def gnomonCofactorWindowPrimes (n k : ℕ) : Finset ℕ :=
  (Finset.Icc (max (n ^ 2 / k) (2 * n) + 1) ((n ^ 2 + 2 * n) / k)).filter Nat.Prime

theorem mem_gnomonCofactorWindowPrimes {n k p : ℕ} :
    p ∈ gnomonCofactorWindowPrimes n k ↔
      p.Prime ∧ 2 * n < p ∧ n ^ 2 / k < p ∧ p ≤ (n ^ 2 + 2 * n) / k := by
  simp only [gnomonCofactorWindowPrimes, Finset.mem_filter, Finset.mem_Icc, Nat.add_one_le_iff, max_lt_iff]
  tauto

/-- Q from the checkpoint, with all quotients taken in the natural numbers. -/
noncomputable def gnomonCofactorWindowMass (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 (n - 1), ∑ p ∈ gnomonCofactorWindowPrimes n k, Real.log (p : ℝ)

private theorem window_packet {n k p : ℕ} (hn : 3 ≤ n)
    (hk : k ∈ Finset.Icc 2 (n - 1)) (hp : p ∈ gnomonCofactorWindowPrimes n k) :
    p ∈ (gnomonPascalLargeCarryEvents n).filter Nat.Prime ∧ k = n ^ 2 / p + 1 := by
  obtain ⟨hprime, hw, hlo, hhi⟩ := mem_gnomonCofactorWindowPrimes.mp hp
  obtain ⟨hklo, hkhi⟩ := Finset.mem_Icc.mp hk
  have hkpos : 0 < k := by omega
  have hylo : n ^ 2 < p * k := by
    simpa only [mul_comm] using (Nat.div_lt_iff_lt_mul hkpos).mp hlo
  have hyhi : p * k ≤ n ^ 2 + 2 * n := (Nat.le_div_iff_mul_le hkpos).mp hhi
  have hy : SquareCell n (p * k) := ⟨hylo, by nlinarith⟩
  have hold : p ≤ n ^ 2 := by
    have hmul : 2 * p ≤ p * k := by nlinarith
    have htwo : 2 ≤ n := Nat.le_trans (by decide) hn
    have hwidth : 2 * n ≤ n ^ 2 := by
      simpa only [pow_two] using Nat.mul_le_mul_right n htwo
    have hle : 2 * p ≤ 2 * n ^ 2 := by
      calc
        2 * p ≤ p * k := hmul
        _ ≤ n ^ 2 + 2 * n := hyhi
        _ ≤ 2 * n ^ 2 := by nlinarith only [hwidth]
    omega
  have hdiv : p ∣ p * k := dvd_mul_right p k
  have hc := gnomonLarge_divisor_carry hw hy hdiv
  have he := gnomonNextShellMultiple_unique hw hc hy hdiv
  have hcofactor : k = n ^ 2 / p + 1 := by
    unfold gnomonNextShellMultiple at he
    exact Nat.eq_of_mul_eq_mul_left hprime.pos he
  exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨mem_gnomonPascalLowCarryEvents.mpr ⟨hprime.pos, hold,
      (isPrimePow_nat_iff p).mpr ⟨p, 1, hprime, by omega, by simp⟩, hc⟩, hw⟩,
      hprime⟩, hcofactor⟩

/-- Every singleton label has the unique cofactor of its next shell multiple. -/
theorem gnomonSingletonCarry_cofactor_window {n p : ℕ} (hn : 3 ≤ n)
    (hp : p ∈ (gnomonPascalLargeCarryEvents n).filter Nat.Prime) :
    n ^ 2 / p + 1 ∈ Finset.Icc 2 (n - 1) ∧
      p ∈ gnomonCofactorWindowPrimes n (n ^ 2 / p + 1) := by
  have hprime := (Finset.mem_filter.mp hp).2
  have hlarge := Finset.mem_filter.mp (Finset.mem_filter.mp hp).1
  have hlow := mem_gnomonPascalLowCarryEvents.mp hlarge.1
  have hpacket := gnomonNextShellMultiple_packet hlarge.2 hlow.2.2.2
  have hklo : 2 ≤ n ^ 2 / p + 1 := by
    have h : 1 ≤ n ^ 2 / p :=
      (Nat.le_div_iff_mul_le hprime.pos).mpr (by simpa using hlow.2.1)
    omega
  have hkhi := gnomonNextShellMultiple_cofactor_lt hn hlarge.2
  refine ⟨Finset.mem_Icc.mpr ⟨hklo, by omega⟩,
    mem_gnomonCofactorWindowPrimes.mpr ⟨hprime, hlarge.2, ?_, ?_⟩⟩
  · apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
    simpa only [gnomonNextShellMultiple, mul_comm] using hpacket.1.1
  · apply (Nat.le_div_iff_mul_le (by omega)).mpr
    have ht := hpacket.1.2
    change p * (n ^ 2 / p + 1) ≤ n ^ 2 + 2 * n
    unfold gnomonNextShellMultiple at ht
    nlinarith

/-- Cofactor windows are disjoint as prime carriers. This is indexing uniqueness. -/
theorem gnomonCofactorWindow_unique {n k l p : ℕ} (hn : 3 ≤ n)
    (hk : k ∈ Finset.Icc 2 (n - 1)) (hl : l ∈ Finset.Icc 2 (n - 1))
    (hp : p ∈ gnomonCofactorWindowPrimes n k)
    (hp' : p ∈ gnomonCofactorWindowPrimes n l) : k = l :=
  (window_packet hn hk hp).2.trans (window_packet hn hl hp').2.symm

/-- Q is precisely the old large prime-label mass, without any numerical saving. -/
theorem gnomonCofactorWindowMass_eq_singleton {n : ℕ} (hn : 3 ≤ n) :
    gnomonCofactorWindowMass n = gnomonSingletonCarryMass n := by
  unfold gnomonCofactorWindowMass gnomonSingletonCarryMass
  rw [Finset.sum_sigma']
  apply Finset.sum_bij (fun t _ => t.2)
  · intro t ht
    have h := Finset.mem_sigma.mp ht
    exact (window_packet hn h.1 h.2).1
  · intro t ht u hu he
    have h := Finset.mem_sigma.mp ht
    have h' := Finset.mem_sigma.mp hu
    have hk := (window_packet hn h.1 h.2).2
    have hl := (window_packet hn h'.1 h'.2).2
    exact Sigma.ext (by rw [hk, hl, he]) (by simpa using he)
  · intro p hp
    have h := gnomonSingletonCarry_cofactor_window hn hp
    exact ⟨⟨n ^ 2 / p + 1, p⟩, Finset.mem_sigma.mpr h, rfl⟩
  · intro t ht
    have hp := (mem_gnomonCofactorWindowPrimes.mp (Finset.mem_sigma.mp ht).2).1
    exact (ArithmeticFunction.vonMangoldt_apply_prime hp).symm

/-- Window length is shorter than every prime in the window. -/
theorem gnomonCofactorWindow_length_lt {n k p : ℕ} (hn : 3 ≤ n) (hk : 2 ≤ k)
    (hp : p ∈ gnomonCofactorWindowPrimes n k) :
    (n ^ 2 + 2 * n) / k - max (n ^ 2 / k) (2 * n) < p := by
  have hw := (mem_gnomonCofactorWindowPrimes.mp hp).2.1
  have hquot := Nat.add_div_le_div_add_div_add_one (n ^ 2) (2 * n) k
  have hdiv : 2 * n / k ≤ n := by
    apply Nat.div_le_of_le_mul
    nlinarith
  have hmax := le_max_left (n ^ 2 / k) (2 * n)
  omega

/-- Each distinct window prime divides an endpoint-only binomial coefficient. -/
theorem gnomonCofactorWindow_prime_dvd_choose {n k p : ℕ} (hn : 3 ≤ n) (hk : 2 ≤ k)
    (hp : p ∈ gnomonCofactorWindowPrimes n k) :
    p ∣ Nat.choose ((n ^ 2 + 2 * n) / k)
      ((n ^ 2 + 2 * n) / k - max (n ^ 2 / k) (2 * n)) := by
  obtain ⟨hprime, hw, hlo, hhi⟩ := mem_gnomonCofactorWindowPrimes.mp hp
  have hA : max (n ^ 2 / k) (2 * n) < p := max_lt hlo hw
  have hAB : max (n ^ 2 / k) (2 * n) ≤ (n ^ 2 + 2 * n) / k := hA.le.trans hhi
  apply hprime.dvd_choose (gnomonCofactorWindow_length_lt hn hk hp) _ hhi
  simpa only [Nat.sub_sub_self hAB] using hA

private theorem sum_prime_logs_le_log {s : Finset ℕ} {C : ℕ} (hC : 0 < C)
    (h : ∀ p ∈ s, p.Prime ∧ p ∣ C) :
    (∑ p ∈ s, Real.log (p : ℝ)) ≤ Real.log (C : ℝ) := by
  have hs : s ⊆ C.primeFactors := by
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨(h p hp).1, (h p hp).2, by omega⟩
  have hd : (∏ p ∈ s, p) ∣ C :=
    (Finset.prod_dvd_prod_of_subset s C.primeFactors id hs).trans (Nat.prod_primeFactors_dvd C)
  have hle := Nat.le_of_dvd hC hd
  have hpos : 0 < (∏ p ∈ s, p) := Finset.prod_pos (fun p hp => (h p hp).1.pos)
  have hlog : Real.log ((∏ p ∈ s, p : ℕ) : ℝ) ≤ Real.log (C : ℝ) :=
    Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle)
  rw [Nat.cast_prod, Real.log_prod (fun p hp => by exact_mod_cast (h p hp).1.ne_zero)] at hlog
  exact hlog

/-- A finite geometric envelope, independent of the carry or prime inventory. -/
noncomputable def gnomonCofactorBinomialBudget (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 (n - 1),
    Real.log (Nat.choose ((n ^ 2 + 2 * n) / k)
      ((n ^ 2 + 2 * n) / k - max (n ^ 2 / k) (2 * n)) : ℝ)

/-- Prime divisibility yields the independent weighted cofactor bound. -/
theorem gnomonCofactorWindowMass_le_binomialBudget {n : ℕ} (hn : 3 ≤ n) :
    gnomonCofactorWindowMass n ≤ gnomonCofactorBinomialBudget n := by
  apply Finset.sum_le_sum
  intro k hk
  apply sum_prime_logs_le_log (Nat.choose_pos (Nat.sub_le _ _))
  intro p hp
  exact ⟨(mem_gnomonCofactorWindowPrimes.mp hp).1,
    gnomonCofactorWindow_prime_dvd_choose hn (Finset.mem_Icc.mp hk).1 hp⟩

private theorem window_card_le_odd_span {n k : ℕ} (hn : 3 ≤ n) :
    (gnomonCofactorWindowPrimes n k).card ≤
      (((n ^ 2 + 2 * n) / k + 1) / 2) - ((max (n ^ 2 / k) (2 * n) + 1) / 2) := by
  rw [← Nat.card_Ico]
  apply Finset.card_le_card_of_injOn (fun p => p / 2)
  · intro p hp
    obtain ⟨hprime, hw, hlo, hhi⟩ := mem_gnomonCofactorWindowPrimes.mp hp
    have hA := max_lt hlo hw
    obtain ⟨a, ha⟩ := hprime.odd_of_ne_two (by omega)
    apply Finset.mem_Ico.mpr
    dsimp only
    omega
  · intro p hp q hq he
    have h := mem_gnomonCofactorWindowPrimes.mp hp
    have h' := mem_gnomonCofactorWindowPrimes.mp hq
    obtain ⟨a, ha⟩ := h.1.odd_of_ne_two (by omega)
    obtain ⟨b, hb⟩ := h'.1.odd_of_ne_two (by omega)
    dsimp only at he
    omega

/-- Per window, choose the smaller binomial or odd-spacing integer envelope. -/
noncomputable def gnomonCofactorGeometricBudget (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 (n - 1),
    Real.log ((min
      (Nat.choose ((n ^ 2 + 2 * n) / k)
        ((n ^ 2 + 2 * n) / k - max (n ^ 2 / k) (2 * n)))
      ((max 1 ((n ^ 2 + 2 * n) / k)) ^
        ((((n ^ 2 + 2 * n) / k + 1) / 2) - ((max (n ^ 2 / k) (2 * n) + 1) / 2))) : ℕ) : ℝ)

/-- The combined endpoint estimate improves the binomial-only upper estimate. -/
theorem gnomonCofactorGeometricBudget_le_binomialBudget (n : ℕ) :
    gnomonCofactorGeometricBudget n ≤ gnomonCofactorBinomialBudget n := by
  apply Finset.sum_le_sum
  intro k _
  apply Real.log_le_log
  · have hc := Nat.choose_pos (Nat.sub_le ((n ^ 2 + 2 * n) / k) (max (n ^ 2 / k) (2 * n)))
    have hp : 0 < max 1 ((n ^ 2 + 2 * n) / k) := lt_of_lt_of_le (by decide) (le_max_left _ _)
    exact_mod_cast lt_min hc (pow_pos hp _)
  · exact_mod_cast min_le_left _ _

/-- Both elementary endpoint envelopes bound every window prime weight. -/
theorem gnomonCofactorWindowMass_le_geometricBudget {n : ℕ} (hn : 3 ≤ n) :
    gnomonCofactorWindowMass n ≤ gnomonCofactorGeometricBudget n := by
  apply Finset.sum_le_sum
  intro k hk
  let A := max (n ^ 2 / k) (2 * n)
  let B := (n ^ 2 + 2 * n) / k
  let J := (B + 1) / 2 - (A + 1) / 2
  change (∑ p ∈ gnomonCofactorWindowPrimes n k, Real.log (p : ℝ)) ≤
    Real.log ((min (Nat.choose B (B - A)) ((max 1 B) ^ J) : ℕ) : ℝ)
  by_cases hc : Nat.choose B (B - A) ≤ (max 1 B) ^ J
  · rw [min_eq_left hc]
    apply sum_prime_logs_le_log (Nat.choose_pos (Nat.sub_le _ _))
    intro p hp
    exact ⟨(mem_gnomonCofactorWindowPrimes.mp hp).1,
      gnomonCofactorWindow_prime_dvd_choose hn (Finset.mem_Icc.mp hk).1 hp⟩
  · rw [min_eq_right (le_of_not_ge hc), Nat.cast_pow, Real.log_pow]
    calc
      _ ≤ ∑ _p ∈ gnomonCofactorWindowPrimes n k, Real.log ((max 1 B : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have h := mem_gnomonCofactorWindowPrimes.mp hp
        exact Real.log_le_log (by exact_mod_cast h.1.pos)
          (by exact_mod_cast h.2.2.2.trans (le_max_right 1 B))
      _ = ((gnomonCofactorWindowPrimes n k).card : ℝ) * Real.log ((max 1 B : ℕ) : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast window_card_le_odd_span (k := k) hn)
        (Real.log_nonneg (by exact_mod_cast le_max_left 1 B))

/-- Exact excess: this upper envelope adds U-Q to the old budget. -/
theorem gnomonPascalOldLogBudget_cofactor_excess {n : ℕ} (hn : 3 ≤ n) :
    gnomonPascalSmallCarryMass n + gnomonRepeatedCarryMass n +
      gnomonCofactorGeometricBudget n + gnomonPascalShellHigherPrimePowerMass n =
    gnomonPascalOldLogBudget n +
      (gnomonCofactorGeometricBudget n - gnomonCofactorWindowMass n) := by
  rw [gnomonPascalOldLogBudget_eq_higher_add_lowCarryMass hn,
    gnomonPascalLowCarryMass_eq_small_add_large,
    gnomonPascalLargeCarryMass_eq_repeated_add_singleton,
    gnomonCofactorWindowMass_eq_singleton hn]
  ring

/-- An endpoint-only singleton bound feeds the exact higher-correction consumer. -/
theorem exists_prime_squareCell_of_cofactorGeometricBudget_lt {n : ℕ} (hn : 3 ≤ n)
    (hstrict : gnomonPascalSmallCarryMass n + gnomonRepeatedCarryMass n +
      gnomonCofactorGeometricBudget n + gnomonPascalShellHigherPrimePowerMass n <
        Real.log (GnomonPascalCell n : ℝ)) :
    ∃ p, p.Prime ∧ SquareCell n p := by
  apply (gnomonPascalOldLogBudget_lt_iff hn).mp
  have hbound := gnomonCofactorWindowMass_le_geometricBudget hn
  rw [gnomonPascalOldLogBudget_cofactor_excess hn] at hstrict
  linarith

end DkMath.NumberTheory.Legendre
