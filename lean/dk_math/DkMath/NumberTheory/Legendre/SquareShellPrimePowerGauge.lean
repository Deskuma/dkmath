/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.SquareShellPrimePower
import DkMath.NumberTheory.Legendre.SquareShellVonMangoldt
import DkMath.NumberTheory.OddReciprocal

#print "file: DkMath.NumberTheory.Legendre.SquareShellPrimePowerGauge"

/-! Canonical depth gauges, finite harmonic correction budgets, and conditional
prime providers. The missing ingredient remains a lower bound for the shell
von Mangoldt mass. No asymptotic estimate is asserted by a budget name. -/

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

/-! Odd-depth reciprocal compression. All prime providers retain a strict
lower shell-mass hypothesis; no asymptotic statement is asserted. -/

/-- Occupied canonical depths, with no inverse-event choice. -/
def shellHigherPrimePowerDepths (n : ℕ) : Finset ℕ :=
  (shellHigherPrimePowerEvents n).image (fun q => q.factorization q.minFac)

@[simp] theorem mem_shellHigherPrimePowerDepths {n a : ℕ} :
    a ∈ shellHigherPrimePowerDepths n ↔
      ∃ q ∈ shellHigherPrimePowerEvents n, a = q.factorization q.minFac := by
  simp only [shellHigherPrimePowerDepths, Finset.mem_image, eq_comm]

/-- The canonical image has odd depths from three to the binary cutoff. -/
theorem shellHigherPrimePowerDepths_bounds {n a : ℕ} (ha : a ∈ shellHigherPrimePowerDepths n) :
    3 ≤ a ∧ Odd a ∧ a ≤ Nat.log 2 ((n + 1) ^ 2) := by
  obtain ⟨q, hq, rfl⟩ := mem_shellHigherPrimePowerDepths.mp ha
  have h := mem_shellHigherPrimePowerEvents.mp hq
  have c := shell_higher_primePower_canonical h.1 h.2.1 h.2.2
  refine ⟨c.2.1, c.2.2.1, squareCell_prime_power_exponent_le_log c.1 ?_⟩
  rw [← c.2.2.2.1]; exact h.1

/-- The injective image preserves the complete event count. -/
theorem card_shellHigherPrimePowerDepths (n : ℕ) :
    (shellHigherPrimePowerDepths n).card = (shellHigherPrimePowerEvents n).card := by
  exact Finset.card_image_iff.mpr (shellHigherPrimePower_depth_injective n)

/-- Admissible depths are exponents, independent of primality. -/
def shellOddDepths (n : ℕ) : Finset ℕ :=
  (Finset.Icc 3 (Nat.log 2 ((n + 1) ^ 2))).filter Odd

@[simp] theorem mem_shellOddDepths {n a : ℕ} :
    a ∈ shellOddDepths n ↔ 3 ≤ a ∧ a ≤ Nat.log 2 ((n + 1) ^ 2) ∧ Odd a := by
  simp only [shellOddDepths, Finset.mem_filter, Finset.mem_Icc]
  tauto

/-- Every occupied depth is admissible; the reverse containment is not asserted. -/
theorem shellHigherPrimePowerDepths_subset_oddDepths (n : ℕ) :
    shellHigherPrimePowerDepths n ⊆ shellOddDepths n := by
  intro a ha
  have h := shellHigherPrimePowerDepths_bounds ha
  exact mem_shellOddDepths.mpr ⟨h.1, h.2.2, h.2.1⟩

/-- Higher-event weight is exactly its label logarithm divided by canonical depth. -/
theorem shellHigherPrimePower_weight_eq_log_div_depth {n q : ℕ}
    (hq : q ∈ shellHigherPrimePowerEvents n) :
    ArithmeticFunction.vonMangoldt q =
      Real.log (q : ℝ) / (q.factorization q.minFac : ℝ) := by
  have h := mem_shellHigherPrimePowerEvents.mp hq
  have c := shell_higher_primePower_canonical h.1 h.2.1 h.2.2
  have hp := shellHigherPrimePower_log_packet h.1 h.2.1 h.2.2
  have ha : (q.factorization q.minFac : ℝ) ≠ 0 := by
    exact_mod_cast (show q.factorization q.minFac ≠ 0 by omega)
  rw [hp.1, hp.2]
  field_simp

/-- Exact shell endpoint provides the pointwise reciprocal upper weight. -/
theorem shellHigherPrimePower_weight_le_top_log_div_depth {n q : ℕ}
    (_hn : 3 ≤ n) (hq : q ∈ shellHigherPrimePowerEvents n) :
    ArithmeticFunction.vonMangoldt q ≤
      Real.log ((n ^ 2 + 2 * n : ℕ) : ℝ) / (q.factorization q.minFac : ℝ) := by
  have h := mem_shellHigherPrimePowerEvents.mp hq
  have c := shell_higher_primePower_canonical h.1 h.2.1 h.2.2
  have hqpos : (0 : ℝ) < q := by exact_mod_cast h.2.1.pos
  have htop : q ≤ n ^ 2 + 2 * n := by have := h.1.2; nlinarith
  have hdepth : (0 : ℝ) < q.factorization q.minFac := by
    exact_mod_cast (show 0 < q.factorization q.minFac by omega)
  rw [shellHigherPrimePower_weight_eq_log_div_depth hq]
  exact div_le_div_of_nonneg_right
    (Real.log_le_log hqpos (by exact_mod_cast htop)) hdepth.le

/-- Pointwise bounds reindex injectively on occupied depths. -/
theorem gnomonPascalShellHigherPrimePowerMass_le_depth_sum {n : ℕ} (hn : 3 ≤ n) :
    gnomonPascalShellHigherPrimePowerMass n ≤
      ∑ a ∈ shellHigherPrimePowerDepths n,
        Real.log ((n ^ 2 + 2 * n : ℕ) : ℝ) / (a : ℝ) := by
  rw [gnomonPascalShellHigherPrimePowerMass_eq_events, shellHigherPrimePowerDepths,
    Finset.sum_image (shellHigherPrimePower_depth_injective n)]
  exact Finset.sum_le_sum fun _ hq => shellHigherPrimePower_weight_le_top_log_div_depth hn hq

/-- All omitted admissible depths have nonnegative reciprocal upper weights. -/
theorem gnomonPascalShellHigherPrimePowerMass_le_oddDepth_sum {n : ℕ} (hn : 3 ≤ n) :
    gnomonPascalShellHigherPrimePowerMass n ≤
      ∑ a ∈ shellOddDepths n, Real.log ((n ^ 2 + 2 * n : ℕ) : ℝ) / (a : ℝ) := by
  apply (gnomonPascalShellHigherPrimePowerMass_le_depth_sum hn).trans
  apply Finset.sum_le_sum_of_subset_of_nonneg (shellHigherPrimePowerDepths_subset_oddDepths n)
  intro a _ _
  apply div_nonneg
  · apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ n ^ 2 + 2 * n by nlinarith)
  · exact Nat.cast_nonneg a

/-- Reciprocal cost of every admissible odd depth. -/
noncomputable def shellOddDepthReciprocalSum (n : ℕ) : ℝ :=
  ∑ a ∈ shellOddDepths n, (1 : ℝ) / (a : ℝ)

/-- Exact finite reciprocal budget, before any harmonic approximation. -/
noncomputable def shellHigherPrimePowerReciprocalBudget (n : ℕ) : ℝ :=
  Real.log ((n ^ 2 + 2 * n : ℕ) : ℝ) * shellOddDepthReciprocalSum n

/-- Factoring the constant top logarithm gives the primary finite budget. -/
theorem gnomonPascalShellHigherPrimePowerMass_le_reciprocalBudget {n : ℕ} (hn : 3 ≤ n) :
    gnomonPascalShellHigherPrimePowerMass n ≤ shellHigherPrimePowerReciprocalBudget n := by
  have h := gnomonPascalShellHigherPrimePowerMass_le_oddDepth_sum hn
  have he : (∑ a ∈ shellOddDepths n, Real.log ((n ^ 2 + 2 * n : ℕ) : ℝ) / (a : ℝ)) =
      shellHigherPrimePowerReciprocalBudget n := by
    unfold shellHigherPrimePowerReciprocalBudget shellOddDepthReciprocalSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [he] at h
  exact h

/-- The cutoff is nontrivial throughout the provider domain. -/
theorem shell_binary_depth_cutoff_ge_three {n : ℕ} (hn : 3 ≤ n) :
    3 ≤ Nat.log 2 ((n + 1) ^ 2) := by
  apply Nat.le_log_of_pow_le (by decide)
  norm_num
  nlinarith

/-- Harmonic compression applies to the complete admissible odd universe. -/
theorem shellOddDepthReciprocalSum_le_log_cutoff {n : ℕ} (hn : 3 ≤ n) :
    shellOddDepthReciprocalSum n ≤ Real.log (Nat.log 2 ((n + 1) ^ 2) : ℝ) :=
  odd_reciprocal_sum_le_log (shell_binary_depth_cutoff_ge_three hn)

/-- Nested-logarithm scale only; this definition asserts no Big-O theorem. -/
noncomputable def shellHigherPrimePowerLogLogBudget (n : ℕ) : ℝ :=
  Real.log ((n ^ 2 + 2 * n : ℕ) : ℝ) * Real.log (Nat.log 2 ((n + 1) ^ 2) : ℝ)

/-- Separate comparison records the harmonic approximation's exact cost. -/
theorem shellHigherPrimePowerReciprocalBudget_le_logLogBudget {n : ℕ} (hn : 3 ≤ n) :
    shellHigherPrimePowerReciprocalBudget n ≤ shellHigherPrimePowerLogLogBudget n := by
  apply mul_le_mul_of_nonneg_left (shellOddDepthReciprocalSum_le_log_cutoff hn)
  apply Real.log_nonneg
  exact_mod_cast (show 1 ≤ n ^ 2 + 2 * n by nlinarith)

/-- Main compressed explicit higher correction bound. -/
theorem gnomonPascalShellHigherPrimePowerMass_le_logLogBudget {n : ℕ} (hn : 3 ≤ n) :
    gnomonPascalShellHigherPrimePowerMass n ≤ shellHigherPrimePowerLogLogBudget n :=
  (gnomonPascalShellHigherPrimePowerMass_le_reciprocalBudget hn).trans
    (shellHigherPrimePowerReciprocalBudget_le_logLogBudget hn)

/-- The exact top logarithm is below the next-square logarithm. -/
theorem shell_top_log_lt_twice_log_succ {n : ℕ} (hn : 1 ≤ n) :
    Real.log ((n ^ 2 + 2 * n : ℕ) : ℝ) < 2 * Real.log ((n + 1 : ℕ) : ℝ) := by
  have htop : (0 : ℝ) < (n ^ 2 + 2 * n : ℕ) := by
    exact_mod_cast (show 0 < n ^ 2 + 2 * n by nlinarith)
  have hlt := Real.log_lt_log htop (show ((n ^ 2 + 2 * n : ℕ) : ℝ) < ((n + 1 : ℕ) : ℝ) ^ 2 by
    push_cast; nlinarith)
  simpa only [Real.log_pow, Nat.cast_ofNat] using hlt

/-- An optional geometric presentation of the same compressed estimate. -/
theorem gnomonPascalShellHigherPrimePowerMass_le_geometricLogBudget {n : ℕ} (hn : 3 ≤ n) :
    gnomonPascalShellHigherPrimePowerMass n ≤
      2 * Real.log ((n + 1 : ℕ) : ℝ) * Real.log (Nat.log 2 ((n + 1) ^ 2) : ℝ) := by
  apply (gnomonPascalShellHigherPrimePowerMass_le_logLogBudget hn).trans
  apply mul_le_mul_of_nonneg_right (shell_top_log_lt_twice_log_succ (by omega)).le
  exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ Nat.log 2 ((n + 1) ^ 2) from
    (by have := shell_binary_depth_cutoff_ge_three hn; omega)))

/-- The compressed budget is uniformly no larger than instruction 026's budget. -/
theorem shellHigherPrimePowerLogLogBudget_le_logBudget {n : ℕ} (hn : 3 ≤ n) :
    shellHigherPrimePowerLogLogBudget n ≤ shellHigherPrimePowerLogBudget n := by
  have htpos : (0 : ℝ) < (n ^ 2 + 2 * n : ℕ) := by
    exact_mod_cast (show 0 < n ^ 2 + 2 * n by nlinarith)
  have htop : n ^ 2 + 2 * n ≤ n ^ 3 := by
    have h := Nat.mul_le_mul_left n (show n + 2 ≤ n ^ 2 by nlinarith)
    nlinarith [h]
  have ht := Real.log_le_log htpos (show ((n ^ 2 + 2 * n : ℕ) : ℝ) ≤ (n : ℝ) ^ 3 by
    exact_mod_cast htop)
  rw [Real.log_pow] at ht
  have hL := shell_binary_depth_cutoff_ge_three hn
  have hLpos : (0 : ℝ) < Nat.log 2 ((n + 1) ^ 2) := by
    exact_mod_cast (show 0 < Nat.log 2 ((n + 1) ^ 2) by omega)
  have hll := three_mul_log_le_add_one hLpos
  have hl0 : 0 ≤ Real.log (Nat.log 2 ((n + 1) ^ 2) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ Nat.log 2 ((n + 1) ^ 2) by omega))
  have hn0 := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega) : (1 : ℝ) ≤ n)
  unfold shellHigherPrimePowerLogLogBudget shellHigherPrimePowerLogBudget
  have hmul := mul_le_mul_of_nonneg_right hll hn0
  have htopmul := mul_le_mul_of_nonneg_right ht hl0
  have hresult : Real.log ((n ^ 2 + 2 * n : ℕ) : ℝ) *
      Real.log (Nat.log 2 ((n + 1) ^ 2) : ℝ) ≤
      ((Nat.log 2 ((n + 1) ^ 2) : ℝ) + 1) * Real.log (n : ℝ) := by
    norm_num only [Nat.cast_ofNat] at htopmul
    nlinarith [htopmul, hmul]
  simpa only [Nat.cast_add, Nat.cast_one] using hresult

/-- Conditional prime provider from the exact reciprocal upper budget. -/
theorem exists_prime_squareCell_of_reciprocalBudget_lt {n : ℕ} (hn : 3 ≤ n)
    (h : shellHigherPrimePowerReciprocalBudget n < gnomonPascalShellVonMangoldtMass n) :
    ∃ p, p.Prime ∧ SquareCell n p :=
  exists_prime_squareCell_of_higher_bound
    (gnomonPascalShellHigherPrimePowerMass_le_reciprocalBudget hn) h

/-- Conditional prime provider from the compressed log-log upper budget. -/
theorem exists_prime_squareCell_of_logLogBudget_lt {n : ℕ} (hn : 3 ≤ n)
    (h : shellHigherPrimePowerLogLogBudget n < gnomonPascalShellVonMangoldtMass n) :
    ∃ p, p.Prime ∧ SquareCell n p :=
  exists_prime_squareCell_of_higher_bound
    (gnomonPascalShellHigherPrimePowerMass_le_logLogBudget hn) h

/-- Exact psi-difference version of the reciprocal conditional provider. -/
theorem exists_prime_squareCell_of_reciprocalBudget_lt_psi_sub {n : ℕ} (hn : 3 ≤ n)
    (h : shellHigherPrimePowerReciprocalBudget n <
      Chebyshev.psi ((n ^ 2 + 2 * n : ℕ) : ℝ) - Chebyshev.psi ((n ^ 2 : ℕ) : ℝ)) :
    ∃ p, p.Prime ∧ SquareCell n p := by
  apply exists_prime_squareCell_of_reciprocalBudget_lt hn
  rw [gnomonPascalShellVonMangoldtMass_eq_psi_sub]
  exact h

/-- Exact psi-difference version of the compressed conditional provider. -/
theorem exists_prime_squareCell_of_logLogBudget_lt_psi_sub {n : ℕ} (hn : 3 ≤ n)
    (h : shellHigherPrimePowerLogLogBudget n <
      Chebyshev.psi ((n ^ 2 + 2 * n : ℕ) : ℝ) - Chebyshev.psi ((n ^ 2 : ℕ) : ℝ)) :
    ∃ p, p.Prime ∧ SquareCell n p := by
  apply exists_prime_squareCell_of_logLogBudget_lt hn
  rw [gnomonPascalShellVonMangoldtMass_eq_psi_sub]
  exact h

end DkMath.NumberTheory.Legendre
