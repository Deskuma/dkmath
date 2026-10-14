/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.GnomonSmallCarryPhase
import DkMath.NumberTheory.Legendre.GnomonCarryFiber

#print "file: DkMath.NumberTheory.Legendre.GnomonRepeatedCarryPhase"

namespace DkMath.NumberTheory.Legendre
open scoped BigOperators

/-- The first repeated exponent strictly above the shell width. -/
def gnomonRepeatedFirstExponent (n p : ℕ) : ℕ :=
  max 2 (Nat.log p (2 * n) + 1)

/-- Only the first eligible power is tested; later powers retain multiplicity. -/
def gnomonRepeatedBaseActive (n p : ℕ) : Prop :=
  gnomonLowDivisorCarryBit n (p ^ gnomonRepeatedFirstExponent n p) = 1

instance (n p : ℕ) : Decidable (gnomonRepeatedBaseActive n p) :=
  inferInstanceAs (Decidable (_ = _))

/-- A base gate, not the exact carry predicate at every label. -/
def gnomonRepeatedPhaseEnvelope (n : ℕ) : Finset ℕ :=
  ((Finset.Icc (2 * n + 1) (n ^ 2)).filter (fun d => ¬ d.Prime)).filter
    (fun d => gnomonRepeatedBaseActive n d.minFac)

noncomputable def gnomonRepeatedPhaseBudget (n : ℕ) : ℝ :=
  ∑ d ∈ gnomonRepeatedPhaseEnvelope n, ArithmeticFunction.vonMangoldt d

/-- Divisibility transports activity down the same-base exponent chain. -/
theorem gnomonRepeatedCarry_base_active {n p a : ℕ} (hn : 3 ≤ n)
    (hp : p.Prime) (ha : 2 ≤ a) (hw : 2 * n < p ^ a)
    (hc : gnomonLowDivisorCarryBit n (p ^ a) = 1) :
    gnomonRepeatedBaseActive n p := by
  have hlog := Nat.log_lt_of_lt_pow (by omega : 2 * n ≠ 0) hw
  have hle : gnomonRepeatedFirstExponent n p ≤ a := by
    unfold gnomonRepeatedFirstExponent
    exact max_le ha (by omega)
  have hfirst : 2 * n < p ^ gnomonRepeatedFirstExponent n p := by
    apply Nat.lt_pow_of_log_lt hp.one_lt
    unfold gnomonRepeatedFirstExponent
    have := le_max_right 2 (Nat.log p (2 * n) + 1)
    omega
  obtain ⟨hy, hd⟩ := gnomonNextShellMultiple_packet hw hc
  exact gnomonLarge_divisor_carry hfirst hy ((Nat.pow_dvd_pow p hle).trans hd)

/-- All exact repeated labels pass the first-power gate. -/
theorem gnomonRepeatedCarryEvents_subset_phaseEnvelope {n : ℕ} (hn : 3 ≤ n) :
    (gnomonPascalLargeCarryEvents n).filter (fun d => ¬ d.Prime) ⊆
      gnomonRepeatedPhaseEnvelope n := by
  intro d hd
  obtain ⟨hl, hnp⟩ := Finset.mem_filter.mp hd
  obtain ⟨hlo, hw⟩ := Finset.mem_filter.mp hl
  obtain ⟨hpos, htop, hpp, hc⟩ := mem_gnomonPascalLowCarryEvents.mp hlo
  obtain ⟨p, a, hp, ha, he⟩ := (isPrimePow_nat_iff d).mp hpp
  have ha2 : 2 ≤ a := by
    by_contra h
    have ha1 : a = 1 := by omega
    have : d = p := by simpa [ha1] using he.symm
    exact hnp (this ▸ hp)
  have hm : d.minFac = p := by rw [← he, hp.pow_minFac (by omega)]
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, htop⟩, hnp⟩, ?_⟩
  rw [hm]
  exact gnomonRepeatedCarry_base_active hn hp ha2 (he ▸ hw) (he ▸ hc)

theorem gnomonRepeatedCarryMass_le_phaseBudget {n : ℕ} (hn : 3 ≤ n) :
    gnomonRepeatedCarryMass n ≤ gnomonRepeatedPhaseBudget n := by
  unfold gnomonRepeatedCarryMass gnomonRepeatedPhaseBudget
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (gnomonRepeatedCarryEvents_subset_phaseEnvelope hn)
    (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)

theorem gnomonRepeatedPhaseBudget_le_bandBudget (n : ℕ) :
    gnomonRepeatedPhaseBudget n ≤ gnomonRepeatedCarryBandBudget n := by
  unfold gnomonRepeatedPhaseBudget gnomonRepeatedPhaseEnvelope gnomonRepeatedCarryBandBudget
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)

/-- A failed first-power test excludes the whole later repeated chain. -/
theorem gnomonRepeatedCarry_zero_of_inactive {n p a : ℕ} (hn : 3 ≤ n)
    (hp : p.Prime) (ha : 2 ≤ a) (hw : 2 * n < p ^ a)
    (hz : ¬ gnomonRepeatedBaseActive n p) :
    gnomonLowDivisorCarryBit n (p ^ a) = 0 := by
  rcases gnomonLowDivisorCarryBit_binary n (p ^ a) with h | h
  · exact h
  · exact (hz (gnomonRepeatedCarry_base_active hn hp ha hw h)).elim

/-- The retained exponent interval charges one base log for every exponent. -/
theorem gnomonRepeatedExponentInterval_weight (n : ℕ) {p : ℕ} (hp : p.Prime) :
    (∑ a ∈ Finset.Icc (gnomonRepeatedFirstExponent n p) (Nat.log p (n ^ 2)),
      ArithmeticFunction.vonMangoldt (p ^ a)) =
      ((Finset.Icc (gnomonRepeatedFirstExponent n p) (Nat.log p (n ^ 2))).card : ℝ) *
        Real.log (p : ℝ) := by
  calc
    _ = ∑ _a ∈ Finset.Icc (gnomonRepeatedFirstExponent n p) (Nat.log p (n ^ 2)),
        Real.log (p : ℝ) := by
      apply Finset.sum_congr rfl
      intro a ha
      have hlow := (Finset.mem_Icc.mp ha).1
      have htwo : 2 ≤ gnomonRepeatedFirstExponent n p := le_max_left _ _
      exact gnomonCarry_prime_pow_weight hp (by omega)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- One excluded positive-weight label certifies a quantitative saving. -/
theorem gnomonRepeatedPhaseBudget_add_excluded_le_band {n d : ℕ}
    (hd : d ∈ (Finset.Icc (2 * n + 1) (n ^ 2)).filter (fun d => ¬ d.Prime))
    (hz : d ∉ gnomonRepeatedPhaseEnvelope n) :
    gnomonRepeatedPhaseBudget n + ArithmeticFunction.vonMangoldt d ≤
      gnomonRepeatedCarryBandBudget n := by
  have hsub : insert d (gnomonRepeatedPhaseEnvelope n) ⊆
      (Finset.Icc (2 * n + 1) (n ^ 2)).filter (fun d => ¬ d.Prime) := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact hd
    · exact (Finset.mem_filter.mp he).1
  have h := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun e _ _ => ArithmeticFunction.vonMangoldt_nonneg (n := e))
  rw [Finset.sum_insert hz] at h
  change ArithmeticFunction.vonMangoldt d + gnomonRepeatedPhaseBudget n ≤ _ at h
  change _ ≤ ∑ e ∈ (Finset.Icc (2 * n + 1) (n ^ 2)).filter (fun e => ¬ e.Prime),
    ArithmeticFunction.vonMangoldt e
  linarith

/-- Strongest proved small-phase bound plus the base-gated repeated envelope. -/
noncomputable def gnomonRepeatPhaseCorrectionBudget (n : ℕ) : ℝ :=
  Chebyshev.psi (2 * n) - gnomonSmallPhaseExcludedMass n +
    gnomonRepeatedPhaseBudget n + shellHigherPrimePowerReciprocalBudget n

theorem gnomonNonSingletonCorrection_le_repeatPhaseBudget {n : ℕ} (hn : 3 ≤ n) :
    gnomonNonSingletonCorrection n ≤ gnomonRepeatPhaseCorrectionBudget n := by
  have hs := gnomonPascalSmallCarryMass_le_phasePsi n
  have hr := gnomonRepeatedCarryMass_le_phaseBudget hn
  have hh := gnomonPascalShellHigherPrimePowerMass_le_reciprocalBudget hn
  unfold gnomonNonSingletonCorrection gnomonRepeatPhaseCorrectionBudget
  linarith

theorem gnomonRepeatPhaseCorrectionBudget_le_phase037 {n : ℕ} (hn : 3 ≤ n) :
    gnomonRepeatPhaseCorrectionBudget n ≤ gnomonPhaseCorrectionBudget n := by
  have he := gnomonRepeatedCarryBandBudget_prefix_identity hn
  have hr := gnomonRepeatedPhaseBudget_le_bandBudget n
  unfold gnomonRepeatPhaseCorrectionBudget gnomonPhaseCorrectionBudget gnomonNonSingletonBudget
  linarith

theorem exists_prime_squareCell_of_repeatPhaseBudget_lt {n : ℕ} (hn : 3 ≤ n)
    (hstrict : gnomonCofactorWindowMass n + gnomonRepeatPhaseCorrectionBudget n <
      Real.log (GnomonPascalCell n : ℝ)) : ∃ p, p.Prime ∧ SquareCell n p := by
  apply (gnomonPascalOldLogBudget_lt_iff hn).mp
  rw [gnomonPascalOldLogBudget_eq_singleton_add_correction hn]
  have h := gnomonNonSingletonCorrection_le_repeatPhaseBudget hn
  linarith

end DkMath.NumberTheory.Legendre
