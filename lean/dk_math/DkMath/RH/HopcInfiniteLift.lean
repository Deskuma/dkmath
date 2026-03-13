/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.EulerZeta

/-!
# HOPC Infinite Lift

OP-001（finite → infinite）向けに、
`hopcPrimeContributionSum` の極限接続を扱う最小 API。
-/

namespace DkMath.RH.EulerZeta

open scoped BigOperators Topology

/-- HOPC 局所寄与の無限側関数（素数 subtype 上）。 -/
noncomputable def hopcPrimeContributionFn (σ t : ℝ) :
    {p // Nat.Prime p} → ℝ :=
  fun p => hopcPrimeLocalContribution p.1 σ t

/-- HOPC 局所寄与の無限和（`tsum`）。 -/
noncomputable def hopcPrimeContributionTsum (σ t : ℝ) : ℝ :=
  ∑' p : {q // Nat.Prime q}, hopcPrimeContributionFn σ t p

/-- OP-001 向け finite→infinite 接続の最小仮定パッケージ。 -/
structure HopcInfiniteLiftAssumptions (σ t : ℝ) : Prop where
  hHasSumZero : HasSum (hopcPrimeContributionFn σ t) 0

/--
`HasSum` 仮定から、有限集合版 `hopcPrimeContributionSum` の atTop 極限を得る。
-/
theorem tendsto_hopcPrimeContributionSum_atTop_of_hasSum
    {σ t L : ℝ}
    (hHasSum : HasSum (hopcPrimeContributionFn σ t) L) :
    Filter.Tendsto
      (fun S : Finset {p // Nat.Prime p} =>
        hopcPrimeContributionSum (S := S) σ t)
      Filter.atTop (𝓝 L) := by
  simpa [hopcPrimeContributionFn, hopcPrimeContributionSum] using hHasSum

/-- `HopcInfiniteLiftAssumptions` 版の atTop 極限（極限値 0）。 -/
theorem tendsto_hopcPrimeContributionSum_atTop_of_assumptions
    {σ t : ℝ}
    (hAssump : HopcInfiniteLiftAssumptions σ t) :
    Filter.Tendsto
      (fun S : Finset {p // Nat.Prime p} =>
        hopcPrimeContributionSum (S := S) σ t)
      Filter.atTop (𝓝 (0 : ℝ)) :=
  tendsto_hopcPrimeContributionSum_atTop_of_hasSum hAssump.hHasSumZero

/-- `HasSum = 0` 仮定から `hopcPrimeContributionTsum = 0` を得る。 -/
theorem hopcPrimeContributionTsum_eq_zero_of_hasSumZero
    {σ t : ℝ}
    (hHasSumZero : HasSum (hopcPrimeContributionFn σ t) 0) :
    hopcPrimeContributionTsum σ t = 0 := by
  simpa [hopcPrimeContributionTsum, hopcPrimeContributionFn] using hHasSumZero.tsum_eq

/-- `HopcInfiniteLiftAssumptions` 版の `tsum = 0`。 -/
theorem hopcPrimeContributionTsum_eq_zero_of_assumptions
    {σ t : ℝ}
    (hAssump : HopcInfiniteLiftAssumptions σ t) :
    hopcPrimeContributionTsum σ t = 0 :=
  hopcPrimeContributionTsum_eq_zero_of_hasSumZero hAssump.hHasSumZero

/--
極限 0 の場合、有限集合版寄与和は最終的に任意 `ε` 未満になる。
-/
theorem eventually_abs_hopcPrimeContributionSum_lt_of_assumptions
    {σ t ε : ℝ}
    (hε : 0 < ε)
    (hAssump : HopcInfiniteLiftAssumptions σ t) :
    ∀ᶠ S : Finset {p // Nat.Prime p} in Filter.atTop,
      |hopcPrimeContributionSum (S := S) σ t| < ε := by
  have hT :
      Filter.Tendsto
        (fun S : Finset {p // Nat.Prime p} =>
          hopcPrimeContributionSum (S := S) σ t)
        Filter.atTop (𝓝 (0 : ℝ)) :=
    tendsto_hopcPrimeContributionSum_atTop_of_assumptions hAssump
  have hBall : Metric.ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ) :=
    Metric.ball_mem_nhds (0 : ℝ) hε
  have hEv :
      ∀ᶠ S : Finset {p // Nat.Prime p} in Filter.atTop,
        hopcPrimeContributionSum (S := S) σ t ∈ Metric.ball (0 : ℝ) ε :=
    hT.eventually hBall
  exact hEv.mono (by
    intro S hS
    simpa [Metric.mem_ball, Real.dist_eq] using hS)

end DkMath.RH.EulerZeta
