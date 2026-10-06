/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.SquareShellPrimePower
import DkMath.NumberTheory.Legendre.SquareShellVonMangoldt

#print "file: DkMath.NumberTheory.Legendre.SquareShellPrimePowerGauge"

/-! Small higher-power budgets and conditional prime providers.
The missing ingredient remains a lower bound for the shell von Mangoldt mass. -/

namespace DkMath.NumberTheory.Legendre

open scoped BigOperators

/-- Canonical base weight and exact logarithmic depth relation. -/
theorem shellHigherPrimePower_log_packet {n q : ℕ} (hc : SquareCell n q)
    (hq : IsPrimePow q) (hnp : ¬ q.Prime) :
    ArithmeticFunction.vonMangoldt q = Real.log (q.minFac : ℝ) ∧
    Real.log (q : ℝ) = (q.factorization q.minFac : ℝ) * Real.log (q.minFac : ℝ) := by
  have c := shell_higher_primePower_canonical hc hq hnp
  constructor
  · simp [ArithmeticFunction.vonMangoldt_apply, hq]
  · conv_lhs => rw [c.2.2.2.1]
    rw [Nat.cast_pow, Real.log_pow]

/-- Higher events have relative logarithmic weight at most one third. -/
theorem shellHigherPrimePower_weight_gap {n q : ℕ} (hc : SquareCell n q)
    (hq : IsPrimePow q) (hnp : ¬ q.Prime) :
    3 * ArithmeticFunction.vonMangoldt q ≤ Real.log (q : ℝ) := by
  have c := shell_higher_primePower_canonical hc hq hnp
  have h := shellHigherPrimePower_log_packet hc hq hnp
  rw [h.1, h.2]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast c.2.1)
    (Real.log_nonneg (by exact_mod_cast c.1.one_le))

/-- The discrete prime-power gauge has the same exact one-third upper bound. -/
theorem shellHigherPrimePower_logGauge_le {n q : ℕ} (hc : SquareCell n q)
    (hq : IsPrimePow q) (hnp : ¬ q.Prime) :
    pascalPrimePowerLogGauge q.minFac (q.factorization q.minFac) ≤ 1 / 3 := by
  have c := shell_higher_primePower_canonical hc hq hnp
  rw [pascalPrimePowerLogGauge_eq c.1 (by omega)]
  apply one_div_le_one_div_of_le (by norm_num)
  exact_mod_cast c.2.1

/-- Genuine prime events instead have full weight. -/
theorem shellPrime_weight_eq_log {n q : ℕ} (_hc : SquareCell n q) (hq : q.Prime) :
    ArithmeticFunction.vonMangoldt q = Real.log (q : ℝ) :=
  ArithmeticFunction.vonMangoldt_apply_prime hq

/-- Offset-to-label reindexing is an exact finite bijection. -/
theorem squareOffsets_sum_eq_values (n : ℕ) (f : ℕ → ℝ) :
    (∑ r ∈ squareOffsets n, f (n ^ 2 + r)) =
      ∑ q ∈ Finset.Icc (n ^ 2 + 1) (n ^ 2 + 2 * n), f q := by
  apply Finset.sum_bij (fun r _ => n ^ 2 + r)
  · intro r hr
    have h := mem_squareOffsets.mp hr
    exact Finset.mem_Icc.mpr ⟨by dsimp [SquareOffset] at h; omega,
      by dsimp [SquareOffset] at h; omega⟩
  · intro r _ s _ he; omega
  · intro q hq
    have h := Finset.mem_Icc.mp hq
    refine ⟨q - n ^ 2, mem_squareOffsets.mpr ?_, ?_⟩
    · unfold SquareOffset; omega
    · omega
  · intro r _; rfl

/-- Only actual nonprime prime-power shell labels remain in the correction. -/
theorem gnomonPascalShellHigherPrimePowerMass_eq_events (n : ℕ) :
    gnomonPascalShellHigherPrimePowerMass n =
      ∑ q ∈ shellHigherPrimePowerEvents n, ArithmeticFunction.vonMangoldt q := by
  rw [gnomonPascalShellHigherPrimePowerMass, squareOffsets_sum_eq_values]
  simp only [shellHigherPrimePowerEvents, Finset.sum_filter, higherPrimePowerWeight]

/-- Exact base-prime image of the higher events. -/
def shellHigherPrimePowerBases (n : ℕ) : Finset ℕ :=
  (shellHigherPrimePowerEvents n).image Nat.minFac

/-- The base image lies in the old primes at most n. -/
theorem shellHigherPrimePowerBases_subset_primesLE (n : ℕ) :
    shellHigherPrimePowerBases n ⊆ Nat.primesLE n := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  have h := mem_shellHigherPrimePowerEvents.mp hq
  have c := shell_higher_primePower_canonical h.1 h.2.1 h.2.2
  exact Nat.mem_primesLE.mpr ⟨c.2.2.2.2.1, c.1⟩

/-- Base injection reindexes the correction without multiplicities. -/
theorem gnomonPascalShellHigherPrimePowerMass_eq_base_logs {n : ℕ} (hn : 3 ≤ n) :
    gnomonPascalShellHigherPrimePowerMass n =
      ∑ p ∈ shellHigherPrimePowerBases n, Real.log (p : ℝ) := by
  rw [gnomonPascalShellHigherPrimePowerMass_eq_events, shellHigherPrimePowerBases,
    Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro q hq
    have h := mem_shellHigherPrimePowerEvents.mp hq
    exact (shellHigherPrimePower_log_packet h.1 h.2.1 h.2.2).1
  · intro q hq r hr he
    have hq' := mem_shellHigherPrimePowerEvents.mp hq
    have hr' := mem_shellHigherPrimePowerEvents.mp hr
    exact squareCell_primePower_minFac_injective hn hq'.2.1 hr'.2.1 hq'.1 hr'.1 he

/-- A uniform correction budget over primes at most the anchor. -/
theorem gnomonPascalShellHigherPrimePowerMass_le_theta {n : ℕ} (hn : 3 ≤ n) :
    gnomonPascalShellHigherPrimePowerMass n ≤ Chebyshev.theta (n : ℝ) := by
  rw [gnomonPascalShellHigherPrimePowerMass_eq_base_logs hn,
    Chebyshev.theta_eq_sum_primesLE_log]
  apply Finset.sum_le_sum_of_subset_of_nonneg (shellHigherPrimePowerBases_subset_primesLE n)
  intro p hp _
  exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le)

/-- Optional sharper arithmetic carrier, avoiding real cube roots. -/
def shellHigherBaseCandidates (n : ℕ) : Finset ℕ :=
  (Nat.primesLE n).filter (fun p => p ^ 3 < (n + 1) ^ 2)

/-- Every contributing base belongs to the cube cutoff carrier. -/
theorem shellHigherPrimePowerBases_subset_candidates (n : ℕ) :
    shellHigherPrimePowerBases n ⊆ shellHigherBaseCandidates n := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  have h := mem_shellHigherPrimePowerEvents.mp hq
  have c := shell_higher_primePower_canonical h.1 h.2.1 h.2.2
  exact Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨c.2.2.2.2.1, c.1⟩, c.2.2.2.2.2⟩

/-- The cube-cutoff budget is at least as sharp as theta. -/
theorem shellHigherBaseCandidates_log_sum_le_theta (n : ℕ) :
    (∑ p ∈ shellHigherBaseCandidates n, Real.log (p : ℝ)) ≤ Chebyshev.theta (n : ℝ) := by
  rw [Chebyshev.theta_eq_sum_primesLE_log]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro p hp _
  exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le)

/-- Exact higher correction bounded by cube-cutoff candidate primes. -/
theorem gnomonPascalShellHigherPrimePowerMass_le_candidate_logs {n : ℕ} (hn : 3 ≤ n) :
    gnomonPascalShellHigherPrimePowerMass n ≤
      ∑ p ∈ shellHigherBaseCandidates n, Real.log (p : ℝ) := by
  rw [gnomonPascalShellHigherPrimePowerMass_eq_base_logs hn]
  apply Finset.sum_le_sum_of_subset_of_nonneg (shellHigherPrimePowerBases_subset_candidates n)
  intro p hp _
  exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2.one_le)

/-- Each event weighs at most log n. -/
theorem gnomonPascalShellHigherPrimePowerMass_le_card_log {n : ℕ} (_hn : 3 ≤ n) :
    gnomonPascalShellHigherPrimePowerMass n ≤
      ((shellHigherPrimePowerEvents n).card : ℝ) * Real.log (n : ℝ) := by
  rw [gnomonPascalShellHigherPrimePowerMass_eq_events]
  calc
    _ ≤ ∑ _q ∈ shellHigherPrimePowerEvents n, Real.log (n : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      have h := mem_shellHigherPrimePowerEvents.mp hq
      have c := shell_higher_primePower_canonical h.1 h.2.1 h.2.2
      rw [(shellHigherPrimePower_log_packet h.1 h.2.1 h.2.2).1]
      exact Real.log_le_log (by exact_mod_cast c.1.pos) (by exact_mod_cast c.2.2.2.2.1)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

/-- Explicit logarithmic-count times logarithmic-weight correction budget. -/
noncomputable def shellHigherPrimePowerLogBudget (n : ℕ) : ℝ :=
  ((Nat.log 2 ((n + 1) ^ 2) + 1 : ℕ) : ℝ) * Real.log (n : ℝ)

theorem gnomonPascalShellHigherPrimePowerMass_le_logBudget {n : ℕ} (hn : 3 ≤ n) :
    gnomonPascalShellHigherPrimePowerMass n ≤ shellHigherPrimePowerLogBudget n := by
  apply (gnomonPascalShellHigherPrimePowerMass_le_card_log hn).trans
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast shellHigherPrimePowerEvents_card_le n)
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)))

/-- Any strict upper-budget comparison is a conditional fresh-prime provider. -/
theorem exists_prime_squareCell_of_higher_bound {n : ℕ} {B : ℝ}
    (hbound : gnomonPascalShellHigherPrimePowerMass n ≤ B)
    (hmass : B < gnomonPascalShellVonMangoldtMass n) :
    ∃ p, p.Prime ∧ SquareCell n p := by
  apply (gnomonPascalShellBirthLogMass_pos_iff n).mp
  have hs := gnomonPascalShellVonMangoldtMass_eq_birth_add_higher n
  linarith

theorem exists_prime_squareCell_of_theta_lt {n : ℕ} (hn : 3 ≤ n)
    (hmass : Chebyshev.theta (n : ℝ) < gnomonPascalShellVonMangoldtMass n) :
    ∃ p, p.Prime ∧ SquareCell n p :=
  exists_prime_squareCell_of_higher_bound (gnomonPascalShellHigherPrimePowerMass_le_theta hn) hmass

theorem exists_prime_squareCell_of_logBudget_lt {n : ℕ} (hn : 3 ≤ n)
    (hmass : shellHigherPrimePowerLogBudget n < gnomonPascalShellVonMangoldtMass n) :
    ∃ p, p.Prime ∧ SquareCell n p :=
  exists_prime_squareCell_of_higher_bound (gnomonPascalShellHigherPrimePowerMass_le_logBudget hn) hmass

/-- Canonical higher events resynchronize old Pascal coordinates at depth >=3. -/
theorem shellHigherPrimePowerResynchronizationPacket {n q : ℕ}
    (hc : SquareCell n q) (hq : IsPrimePow q) (hnp : ¬ q.Prime) :
    3 ≤ q.factorization q.minFac ∧ Odd (q.factorization q.minFac) ∧
    PascalPrebirthAlternationMod (q - 1) q.minFac ∧
    AllInnerChooseDivisible q q.minFac ∧
    q.minFac ∈ pascalPrimeCoordinateSupportUpTo (q - 1) ∧
    q.minFac ∉ pascalPrimeCoordinateBirthSupport q ∧
    pascalPrimePowerLogGauge q.minFac (q.factorization q.minFac) =
      1 / (q.factorization q.minFac : ℝ) := by
  have c := shell_higher_primePower_canonical hc hq hnp
  have hp := prime_power_resynchronization_packet c.1 (by omega : 1 < q.factorization q.minFac)
  rw [← c.2.2.2.1] at hp
  exact ⟨c.2.1, c.2.2.1, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2,
    pascalPrimePowerLogGauge_eq c.1 (by omega)⟩

/-- Prime shell labels have the existing full birth packet and gauge one. -/
theorem shellPrimeBirthPacket {n q : ℕ} (_hc : SquareCell n q) (hq : q.Prime) :
    PascalPrebirthAlternationMod (q - 1) q ∧
    q ∈ pascalPrimeCoordinateBirthSupport q ∧
    pascalPrimePowerLogGauge q 1 = 1 := by
  have h := prime_prebirth_birth_packet hq
  exact ⟨h.2.1, h.2.2.1, by rw [pascalPrimePowerLogGauge_eq hq (by decide)]; norm_num⟩

/-- Global row gcd one does not furnish a selected-cell prime provider. -/
theorem gnomon_top_innerCommonDivisor_eq_one {n : ℕ} (hn : 3 ≤ n) :
    pascalInnerCommonDivisor (n ^ 2 + 2 * n) = 1 := by
  have he : n ^ 2 + 2 * n = n * (n + 2) := by ring
  apply pascalInnerCommonDivisor_eq_one (by nlinarith : 1 < n ^ 2 + 2 * n)
  rw [he]
  exact gnomon_top_not_isPrimePow hn

end DkMath.NumberTheory.Legendre
