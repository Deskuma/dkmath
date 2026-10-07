/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.GnomonNonSingletonCorrection

#print "file: DkMath.NumberTheory.Legendre.GnomonSmallCarryPhase"

namespace DkMath.NumberTheory.Legendre
open scoped BigOperators

/-- A bounded quadratic residue zone, plus the exact minus-one residue exclusion.
This is a sufficient zero-phase test, not the full small-carry complement. -/
def gnomonSmallPhaseExclusions (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (2 * n)).filter (fun d =>
    (n % d ≤ 4 * Nat.sqrt d ∧
      (n % d) ^ 2 % d + (2 * (n % d)) % d < d) ∨ n % d = d - 1)

noncomputable def gnomonSmallPhaseExcludedMass (n : ℕ) : ℝ :=
  ∑ d ∈ gnomonSmallPhaseExclusions n, ArithmeticFunction.vonMangoldt d

/-- Compute the square and width remainders from the single width residue. -/
theorem gnomonSmallPhaseExclusions_carry_zero {n d : ℕ}
    (hd : d ∈ gnomonSmallPhaseExclusions n) : gnomonLowDivisorCarryBit n d = 0 := by
  obtain ⟨hI, hzone⟩ := Finset.mem_filter.mp hd
  have hdpos : 0 < d := by have := (Finset.mem_Icc.mp hI).1; omega
  apply (gnomonLowDivisorCarryBit_eq_zero_iff hdpos).mpr
  have hsq : n ^ 2 % d = (n % d) ^ 2 % d := by simp [Nat.pow_mod]
  have hwidth : (2 * n) % d = (2 * (n % d)) % d := by simp [Nat.mul_mod]
  rw [hsq, hwidth]
  rcases hzone with hz | hm
  · exact hz.2
  · by_cases hd1 : d = 1
    · subst d
      omega
    have hd2 : 2 ≤ d := by omega
    have he : (d - 1) ^ 2 % d = 1 % d := by
      have heq : (d - 1) ^ 2 = d * (d - 2) + 1 := by
        have h1 : d - 1 + 1 = d := by omega
        have h2 : d - 2 + 2 = d := by omega
        nlinarith
      rw [heq]
      simp
    rw [hm, he, Nat.mod_eq_of_lt (by omega : 1 < d)]
    have he2 : 2 * (d - 1) = d + (d - 2) := by omega
    rw [he2, Nat.add_mod]
    simp only [Nat.mod_self, Nat.zero_add, Nat.mod_mod]
    rw [Nat.mod_eq_of_lt (by omega : d - 2 < d)]
    omega

/-- A phase-aware width-prefix estimate; no shell primes are inspected. -/
theorem gnomonPascalSmallCarryMass_le_phasePsi (n : ℕ) :
    gnomonPascalSmallCarryMass n ≤ Chebyshev.psi (2 * n) -
      gnomonSmallPhaseExcludedMass n := by
  have hdis : Disjoint (gnomonPascalSmallCarryEvents n) (gnomonSmallPhaseExclusions n) := by
    apply Finset.disjoint_left.mpr
    intro d hs he
    have hc := (mem_gnomonPascalLowCarryEvents.mp (Finset.mem_filter.mp hs).1).2.2.2
    have hz := gnomonSmallPhaseExclusions_carry_zero he
    omega
  have hsub : gnomonPascalSmallCarryEvents n ∪ gnomonSmallPhaseExclusions n ⊆
      Finset.Icc 0 (2 * n) := by
    intro d hd
    rcases Finset.mem_union.mp hd with hs | he
    · exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, (Finset.mem_filter.mp hs).2⟩
    · have hi := Finset.mem_Icc.mp (Finset.mem_filter.mp he).1
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, hi.2⟩
  have h := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun d _ _ => ArithmeticFunction.vonMangoldt_nonneg (n := d))
  rw [Finset.sum_union hdis] at h
  have hp : Chebyshev.psi (2 * n) =
      ∑ d ∈ Finset.Icc 0 (2 * n), ArithmeticFunction.vonMangoldt d := by
    rw [Chebyshev.psi_eq_sum_Icc]
    have he : (2 : ℝ) * n = ((2 * n : ℕ) : ℝ) := by norm_cast
    rw [he, Nat.floor_natCast]
  unfold gnomonPascalSmallCarryMass gnomonSmallPhaseExcludedMass
  rw [hp]
  linarith

/-- Nonprime labels in the large band only, without carry predicates. -/
noncomputable def gnomonRepeatedCarryBandBudget (n : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc (2 * n + 1) (n ^ 2)).filter (fun d => ¬ d.Prime),
    ArithmeticFunction.vonMangoldt d

theorem gnomonRepeatedCarryMass_le_bandBudget (n : ℕ) :
    gnomonRepeatedCarryMass n ≤ gnomonRepeatedCarryBandBudget n := by
  unfold gnomonRepeatedCarryMass gnomonRepeatedCarryBandBudget
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    obtain ⟨hl, hp⟩ := Finset.mem_filter.mp hd
    obtain ⟨hlo, hlarge⟩ := Finset.mem_filter.mp hl
    have htop := (mem_gnomonPascalLowCarryEvents.mp hlo).2.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, htop⟩, hp⟩
  · intro d _ _
    exact ArithmeticFunction.vonMangoldt_nonneg

/-- Subtract a certified zero-phase mass from the collision-safe 036 prefix bound. -/
noncomputable def gnomonPhaseCorrectionBudget (n : ℕ) : ℝ :=
  gnomonNonSingletonBudget n - gnomonSmallPhaseExcludedMass n

private theorem nonprime_prefix (N : ℕ) :
    (∑ d ∈ (Finset.Icc 0 N).filter (fun d => ¬ d.Prime),
      ArithmeticFunction.vonMangoldt d) = Chebyshev.psi N - Chebyshev.theta N := by
  rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast]
  have he := Finset.sum_filter_add_sum_filter_not (Finset.Icc 0 N) Nat.Prime
    (fun d => ArithmeticFunction.vonMangoldt d)
  have hp : (∑ d ∈ (Finset.Icc 0 N).filter Nat.Prime, ArithmeticFunction.vonMangoldt d) =
      ∑ d ∈ (Finset.Icc 0 N).filter Nat.Prime, Real.log (d : ℝ) := by
    apply Finset.sum_congr rfl
    intro d hd
    exact ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hd).2
  rw [hp] at he
  linarith

theorem gnomonRepeatedCarryBandBudget_prefix_identity {n : ℕ} (hn : 3 ≤ n) :
    Chebyshev.psi (2 * n) + gnomonRepeatedCarryBandBudget n =
      Chebyshev.theta (2 * n) + (Chebyshev.psi ((n : ℝ) ^ 2) -
        Chebyshev.theta ((n : ℝ) ^ 2)) := by
  let L := (Finset.Icc 0 (2 * n)).filter (fun d => ¬ d.Prime)
  let R := (Finset.Icc (2 * n + 1) (n ^ 2)).filter (fun d => ¬ d.Prime)
  have hdis : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    intro d hl hr
    have := Finset.mem_Icc.mp (Finset.mem_filter.mp hl).1
    have := Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1
    omega
  have he : L ∪ R = (Finset.Icc 0 (n ^ 2)).filter (fun d => ¬ d.Prime) := by
    have hN : 2 * n ≤ n ^ 2 := by nlinarith
    ext d
    simp only [L, R, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro (⟨⟨h0, hle⟩, hp⟩ | ⟨⟨hlo, hle⟩, hp⟩)
      · exact ⟨⟨h0, hle.trans hN⟩, hp⟩
      · exact ⟨⟨Nat.zero_le _, hle⟩, hp⟩
    · rintro ⟨⟨h0, hle⟩, hp⟩
      by_cases hd : d ≤ 2 * n
      · exact Or.inl ⟨⟨h0, hd⟩, hp⟩
      · exact Or.inr ⟨⟨by omega, hle⟩, hp⟩
  have hs : (∑ d ∈ L, ArithmeticFunction.vonMangoldt d) +
      (∑ d ∈ R, ArithmeticFunction.vonMangoldt d) =
      Chebyshev.psi ((n : ℝ) ^ 2) - Chebyshev.theta ((n : ℝ) ^ 2) := by
    rw [← Finset.sum_union hdis, he, nonprime_prefix, Nat.cast_pow]
  have hl : (∑ d ∈ L, ArithmeticFunction.vonMangoldt d) =
      Chebyshev.psi (2 * n) - Chebyshev.theta (2 * n) := by
    have hcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by norm_cast
    rw [← hcast]
    exact nonprime_prefix (2 * n)
  rw [hl] at hs
  change Chebyshev.psi (2 * n) + (∑ d ∈ R, ArithmeticFunction.vonMangoldt d) = _
  linarith

theorem gnomonNonSingletonCorrection_le_phaseBudget {n : ℕ} (hn : 3 ≤ n) :
    gnomonNonSingletonCorrection n ≤ gnomonPhaseCorrectionBudget n := by
  have hs := gnomonPascalSmallCarryMass_le_phasePsi n
  have hr := gnomonRepeatedCarryMass_le_bandBudget n
  have hh := gnomonPascalShellHigherPrimePowerMass_le_reciprocalBudget hn
  have he := gnomonRepeatedCarryBandBudget_prefix_identity hn
  unfold gnomonNonSingletonCorrection gnomonPhaseCorrectionBudget gnomonNonSingletonBudget
  linarith

theorem gnomonPhaseCorrectionBudget_le_previous (n : ℕ) :
    gnomonPhaseCorrectionBudget n ≤ gnomonNonSingletonBudget n := by
  have h : 0 ≤ gnomonSmallPhaseExcludedMass n :=
    Finset.sum_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  unfold gnomonPhaseCorrectionBudget
  linarith

theorem exists_prime_squareCell_of_phaseCorrectionBudget_lt {n : ℕ} (hn : 3 ≤ n)
    (hstrict : gnomonCofactorWindowMass n + gnomonPhaseCorrectionBudget n <
      Real.log (GnomonPascalCell n : ℝ)) : ∃ p, p.Prime ∧ SquareCell n p := by
  apply (gnomonPascalOldLogBudget_lt_iff hn).mp
  rw [gnomonPascalOldLogBudget_eq_singleton_add_correction hn]
  have h := gnomonNonSingletonCorrection_le_phaseBudget hn
  linarith

end DkMath.NumberTheory.Legendre
