/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.GnomonCentralCarryCompensation
import DkMathTest.NumberTheory.GnomonSmallCarryPhaseCalibration

#print "file: DkMathTest.NumberTheory.GnomonCentralCarryCompensationCalibration"

namespace DkMathTest.NumberTheory.GnomonCentralCarryCompensationCalibration
open DkMath.NumberTheory.Legendre
open scoped BigOperators

theorem carriers4_checked :
    gnomonCommonCarryEvents 4 = ∅ ∧
    gnomonSmallOnlyCarryEvents 4 = {3} ∧
    gnomonCentralOnlyCarryEvents 4 = {5, 7, 8} := by
  decide +kernel

/-- Cross-base compensation is an inequality; it is not divisibility. -/
theorem products4_checked :
    (∏ d ∈ gnomonSmallOnlyCarryEvents 4, d.minFac) = 3 ∧
    (∏ d ∈ gnomonCentralOnlyCarryEvents 4, d.minFac) = 70 ∧
    3 ≤ 70 ∧ ¬ 3 ∣ 70 := by
  decide +kernel

theorem pointwise4_retained : gnomonLowDivisorCarryBit 4 3 = 1 ∧
    ¬ 3 ≤ 4 % 3 + 4 % 3 ∧ (Nat.choose 8 4).factorization 3 = 0 :=
  GnomonSmallCarryPhaseCalibration.pointwise4_counterexample

theorem carriers27_checked :
    gnomonSmallOnlyCarryEvents 27 = {5, 11, 19, 23} ∧
    gnomonCentralOnlyCarryEvents 27 = {2, 4, 7, 16, 47, 49, 53} := by
  decide +kernel

theorem compensation27_checked :
    (∑ d ∈ gnomonSmallOnlyCarryEvents 27, ArithmeticFunction.vonMangoldt d) ≤
      ∑ d ∈ gnomonCentralOnlyCarryEvents 27, ArithmeticFunction.vonMangoldt d :=
  (gnomonSmallCarry_le_central_iff_compensation 27).mp
    GnomonSmallCarryPhaseCalibration.central27_checked

theorem products27_checked :
    (∏ d ∈ gnomonSmallOnlyCarryEvents 27, d.minFac) = 24035 ∧
    (∏ d ∈ gnomonCentralOnlyCarryEvents 27, d.minFac) = 976472 := by
  decide +kernel

/-- Three residual bases exceed 7, but only two central residual bases do.
Even a weight-increasing one-coordinate injection is impossible at this anchor. -/
theorem no_dominating_injection27 : ¬ ∃ f : ℕ → ℕ,
    Set.InjOn f (↑(gnomonSmallOnlyCarryEvents 27)) ∧
    (∀ d ∈ gnomonSmallOnlyCarryEvents 27,
      f d ∈ gnomonCentralOnlyCarryEvents 27 ∧ d.minFac ≤ (f d).minFac) := by
  rintro ⟨f, hinj, hmap⟩
  let S := (gnomonSmallOnlyCarryEvents 27).filter (fun d => 7 < d.minFac)
  let T := (gnomonCentralOnlyCarryEvents 27).filter (fun d => 7 < d.minFac)
  have hmaps : Set.MapsTo f (↑S) (↑T) := by
    intro d hd
    obtain ⟨hdS, hdhi⟩ := Finset.mem_filter.mp hd
    obtain ⟨hfd, hle⟩ := hmap d hdS
    exact Finset.mem_filter.mpr ⟨hfd, hdhi.trans_le hle⟩
  have hi : Set.InjOn f (↑S) := by
    intro a ha b hb he
    exact hinj (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 he
  have hcard := Finset.card_le_card_of_injOn f hmaps hi
  have hs : S.card = 3 := by decide +kernel
  have ht : T.card = 2 := by decide +kernel
  rw [hs, ht] at hcard
  omega

/-- Complementing a residue can land in common coordinates rather than compensating ones. -/
theorem complementary_residue11_checked :
    14 % 11 = 3 ∧ 8 % 11 = 11 - 3 ∧
    gnomonLowDivisorCarryBit 14 11 = 1 ∧ ¬ 11 ≤ 14 % 11 + 14 % 11 ∧
    gnomonLowDivisorCarryBit 8 11 = 1 ∧ 11 ≤ 8 % 11 + 8 % 11 := by
  decide +kernel

/-- Anchor instances of the universal bridge, not a universal compensation result. -/
theorem anchor_central_bridge {n : ℕ}
    (_hn : n ∈ ({4, 27, 32, 69, 210, 297, 1031, 5000} : Finset ℕ)) :
    Real.log (Nat.choose (2 * n) n : ℝ) =
      ∑ d ∈ gnomonCentralCarryEvents n, ArithmeticFunction.vonMangoldt d :=
  gnomonCentralCarry_log_eq n

end DkMathTest.NumberTheory.GnomonCentralCarryCompensationCalibration
