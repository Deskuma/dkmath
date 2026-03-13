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

/-- OP-001 向け finite→infinite 接続の運用仮定（`Summable + tsum = 0`）。 -/
structure HopcInfiniteLiftSummableAssumptions (σ t : ℝ) : Prop where
  hSummable : Summable (hopcPrimeContributionFn σ t)
  hTsumZero : hopcPrimeContributionTsum σ t = 0

/--
OP-001 向け majorant 仮定。
`|hopcPrimeContributionFn|` が非負可和関数 `majorant` で抑えられることを表す。
-/
structure HopcInfiniteLiftMajorantAssumptions (σ t : ℝ) : Type where
  majorant : {p // Nat.Prime p} → ℝ
  hMajorantNonneg : ∀ p, 0 ≤ majorant p
  hMajorantSummable : Summable majorant
  hAbsLe : ∀ p, |hopcPrimeContributionFn σ t p| ≤ majorant p
  hTsumZero : hopcPrimeContributionTsum σ t = 0

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

/--
`Summable + tsum = 0` 仮定から `HasSum = 0` 仮定を復元する。
-/
theorem hasSumZero_of_summable_assumptions
    {σ t : ℝ}
    (hAssump : HopcInfiniteLiftSummableAssumptions σ t) :
    HasSum (hopcPrimeContributionFn σ t) 0 := by
  have hHas :
      HasSum (hopcPrimeContributionFn σ t) (hopcPrimeContributionTsum σ t) := by
    simpa [hopcPrimeContributionTsum] using hAssump.hSummable.hasSum
  simpa [hAssump.hTsumZero] using hHas

/-- `Summable + tsum = 0` 仮定を RH-O1 の仮定パッケージへ落とす。 -/
theorem assumptions_of_summable_assumptions
    {σ t : ℝ}
    (hAssump : HopcInfiniteLiftSummableAssumptions σ t) :
    HopcInfiniteLiftAssumptions σ t :=
  ⟨hasSumZero_of_summable_assumptions hAssump⟩

/--
majorant 仮定から `hopcPrimeContributionFn` の可和性を得る。
-/
theorem summable_hopcPrimeContributionFn_of_majorant_assumptions
    {σ t : ℝ}
    (hAssump : HopcInfiniteLiftMajorantAssumptions σ t) :
    Summable (hopcPrimeContributionFn σ t) := by
  have hAbsSummable :
      Summable (fun p : {q // Nat.Prime q} => |hopcPrimeContributionFn σ t p|) :=
    Summable.of_nonneg_of_le
      (fun _ => abs_nonneg _)
      (hAssump.hAbsLe)
      hAssump.hMajorantSummable
  exact hAbsSummable.of_abs

/--
majorant 仮定を `Summable + tsum = 0` 仮定へ落とす。
-/
theorem summable_assumptions_of_majorant_assumptions
    {σ t : ℝ}
    (hAssump : HopcInfiniteLiftMajorantAssumptions σ t) :
    HopcInfiniteLiftSummableAssumptions σ t :=
  ⟨summable_hopcPrimeContributionFn_of_majorant_assumptions hAssump, hAssump.hTsumZero⟩

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

/-- `Summable + tsum = 0` 仮定版の `tsum = 0`。 -/
theorem hopcPrimeContributionTsum_eq_zero_of_summable_assumptions
    {σ t : ℝ}
    (hAssump : HopcInfiniteLiftSummableAssumptions σ t) :
    hopcPrimeContributionTsum σ t = 0 :=
  hAssump.hTsumZero

/-- `Summable + tsum = 0` 仮定版の atTop 極限（極限値 0）。 -/
theorem tendsto_hopcPrimeContributionSum_atTop_of_summable_assumptions
    {σ t : ℝ}
    (hAssump : HopcInfiniteLiftSummableAssumptions σ t) :
    Filter.Tendsto
      (fun S : Finset {p // Nat.Prime p} =>
        hopcPrimeContributionSum (S := S) σ t)
      Filter.atTop (𝓝 (0 : ℝ)) :=
  tendsto_hopcPrimeContributionSum_atTop_of_assumptions
    (assumptions_of_summable_assumptions hAssump)

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

/--
`Summable + tsum = 0` 仮定版:
有限集合版寄与和は最終的に任意 `ε` 未満になる。
-/
theorem eventually_abs_hopcPrimeContributionSum_lt_of_summable_assumptions
    {σ t ε : ℝ}
    (hε : 0 < ε)
    (hAssump : HopcInfiniteLiftSummableAssumptions σ t) :
    ∀ᶠ S : Finset {p // Nat.Prime p} in Filter.atTop,
      |hopcPrimeContributionSum (S := S) σ t| < ε :=
  eventually_abs_hopcPrimeContributionSum_lt_of_assumptions
    hε (assumptions_of_summable_assumptions hAssump)

/-- majorant 仮定版の atTop 極限（極限値 0）。 -/
theorem tendsto_hopcPrimeContributionSum_atTop_of_majorant_assumptions
    {σ t : ℝ}
    (hAssump : HopcInfiniteLiftMajorantAssumptions σ t) :
    Filter.Tendsto
      (fun S : Finset {p // Nat.Prime p} =>
        hopcPrimeContributionSum (S := S) σ t)
      Filter.atTop (𝓝 (0 : ℝ)) :=
  tendsto_hopcPrimeContributionSum_atTop_of_summable_assumptions
    (summable_assumptions_of_majorant_assumptions hAssump)

/-- majorant 仮定版の `tsum = 0`。 -/
theorem hopcPrimeContributionTsum_eq_zero_of_majorant_assumptions
    {σ t : ℝ}
    (hAssump : HopcInfiniteLiftMajorantAssumptions σ t) :
    hopcPrimeContributionTsum σ t = 0 :=
  hAssump.hTsumZero

/--
majorant 仮定版:
有限集合版寄与和は最終的に任意 `ε` 未満になる。
-/
theorem eventually_abs_hopcPrimeContributionSum_lt_of_majorant_assumptions
    {σ t ε : ℝ}
    (hε : 0 < ε)
    (hAssump : HopcInfiniteLiftMajorantAssumptions σ t) :
    ∀ᶠ S : Finset {p // Nat.Prime p} in Filter.atTop,
      |hopcPrimeContributionSum (S := S) σ t| < ε :=
  eventually_abs_hopcPrimeContributionSum_lt_of_summable_assumptions
    hε (summable_assumptions_of_majorant_assumptions hAssump)

end DkMath.RH.EulerZeta
