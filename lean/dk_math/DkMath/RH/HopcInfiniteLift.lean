/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.EulerZetaConvergence

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
`|hopcPrimeContributionFn| ≤ C / p^σ`（`σ > 1`）型の評価から
`hopcPrimeContributionFn` の可和性を得る。
-/
theorem summable_hopcPrimeContributionFn_of_prime_rpow_bound
    {σ t C : ℝ}
    (hσ : 1 < σ)
    (hAbsLe :
      ∀ p : {q // Nat.Prime q},
        |hopcPrimeContributionFn σ t p| ≤ C / (↑p : ℝ) ^ σ) :
    Summable (hopcPrimeContributionFn σ t) := by
  have hPrime :
      Summable (fun p : {q // Nat.Prime q} => (1 : ℝ) / (↑p : ℝ) ^ σ) :=
    summable_one_div_prime_rpow_sigma σ hσ
  have hMajorantSummable :
      Summable (fun p : {q // Nat.Prime q} => C / (↑p : ℝ) ^ σ) := by
    have hMul :
        Summable (fun p : {q // Nat.Prime q} => C * ((1 : ℝ) / (↑p : ℝ) ^ σ)) :=
      Summable.mul_left C hPrime
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hMul
  have hAbsSummable :
      Summable (fun p : {q // Nat.Prime q} => |hopcPrimeContributionFn σ t p|) :=
    Summable.of_nonneg_of_le
      (fun _ => abs_nonneg _)
      hAbsLe
      hMajorantSummable
  exact hAbsSummable.of_abs

/--
`C / p^σ` 上界（`σ > 1`）と `tsum = 0` から、
majorant 仮定パッケージを構成する。
-/
noncomputable def majorant_assumptions_of_prime_rpow_bound
    {σ t C : ℝ}
    (hσ : 1 < σ) (hC : 0 ≤ C)
    (hAbsLe :
      ∀ p : {q // Nat.Prime q},
        |hopcPrimeContributionFn σ t p| ≤ C / (↑p : ℝ) ^ σ)
    (hTsumZero : hopcPrimeContributionTsum σ t = 0) :
    HopcInfiniteLiftMajorantAssumptions σ t := by
  refine
    ⟨(fun p : {q // Nat.Prime q} => C / (↑p : ℝ) ^ σ), ?_, ?_, hAbsLe, hTsumZero⟩
  · intro p
    have hp_pos : (0 : ℝ) < (↑p : ℝ) := by
      exact_mod_cast p.2.pos
    exact div_nonneg hC (le_of_lt (Real.rpow_pos_of_pos hp_pos σ))
  · have hPrime :
        Summable (fun p : {q // Nat.Prime q} => (1 : ℝ) / (↑p : ℝ) ^ σ) :=
      summable_one_div_prime_rpow_sigma σ hσ
    have hMul :
        Summable (fun p : {q // Nat.Prime q} => C * ((1 : ℝ) / (↑p : ℝ) ^ σ)) :=
      Summable.mul_left C hPrime
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hMul

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
  simpa only [HasSum, hopcPrimeContributionFn, hopcPrimeContributionSum] using hHasSum

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

/--
`C / p^σ` 上界（`σ > 1`）と `tsum = 0` から、
有限寄与和の atTop 極限（0）を得る。
-/
theorem tendsto_hopcPrimeContributionSum_atTop_of_prime_rpow_bound
    {σ t C : ℝ}
    (hσ : 1 < σ) (hC : 0 ≤ C)
    (hAbsLe :
      ∀ p : {q // Nat.Prime q},
        |hopcPrimeContributionFn σ t p| ≤ C / (↑p : ℝ) ^ σ)
    (hTsumZero : hopcPrimeContributionTsum σ t = 0) :
    Filter.Tendsto
      (fun S : Finset {p // Nat.Prime p} =>
        hopcPrimeContributionSum (S := S) σ t)
      Filter.atTop (𝓝 (0 : ℝ)) :=
  tendsto_hopcPrimeContributionSum_atTop_of_majorant_assumptions
    (majorant_assumptions_of_prime_rpow_bound
      (σ := σ) (t := t) (C := C) hσ hC hAbsLe hTsumZero)

/--
全素数で `w_p(σ,t) ≠ 0` が成り立ち、有限集合版観測器が最終的に停留するとき、
`hopcPrimeContributionSum` は最終的に 0 になる。
-/
theorem eventually_hopcPrimeContributionSum_eq_zero_of_eventually_stationaryAt
    {σ t : ℝ}
    (hPrime_ne :
      ∀ p : {q // Nat.Prime q}, eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hEvStationary :
      ∀ᶠ S : Finset {q // Nat.Prime q} in Filter.atTop,
        DkMath.RH.stationaryAt
          (fun v : ℝ => eulerZetaFinite_onVertical S σ v) t) :
    ∀ᶠ S : Finset {q // Nat.Prime q} in Filter.atTop,
      hopcPrimeContributionSum (S := S) σ t = 0 := by
  refine hEvStationary.mono ?_
  intro S hS
  have hS_ne :
      ∀ p ∈ S, eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0 := by
    intro p hp
    exact hPrime_ne p
  exact
    (stationaryAt_eulerZetaFinite_onVertical_iff_hopcPrimeContributionSum_eq_zero
      (S := S) (σ := σ) (t := t) hS_ne).1 hS

/--
`eventually stationary` 仮定版:
有限集合版寄与和は最終的に任意 `ε` 未満になる。
-/
theorem eventually_abs_hopcPrimeContributionSum_lt_of_eventually_stationaryAt
    {σ t ε : ℝ}
    (hε : 0 < ε)
    (hPrime_ne :
      ∀ p : {q // Nat.Prime q}, eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hEvStationary :
      ∀ᶠ S : Finset {q // Nat.Prime q} in Filter.atTop,
        DkMath.RH.stationaryAt
          (fun v : ℝ => eulerZetaFinite_onVertical S σ v) t) :
    ∀ᶠ S : Finset {q // Nat.Prime q} in Filter.atTop,
      |hopcPrimeContributionSum (S := S) σ t| < ε := by
  have hEv0 :
      ∀ᶠ S : Finset {q // Nat.Prime q} in Filter.atTop,
        hopcPrimeContributionSum (S := S) σ t = 0 :=
    eventually_hopcPrimeContributionSum_eq_zero_of_eventually_stationaryAt
      (σ := σ) (t := t) hPrime_ne hEvStationary
  exact hEv0.mono (by
    intro S hS0
    have hAbs0 : |hopcPrimeContributionSum (S := S) σ t| = 0 := by
      rw [hS0]
      simp
    exact hAbs0 ▸ hε)

/--
`Summable` と `eventually stationary` から、無限和観測量 `hopcPrimeContributionTsum` は 0。
-/
theorem hopcPrimeContributionTsum_eq_zero_of_summable_of_eventually_stationaryAt
    {σ t : ℝ}
    (hSummable : Summable (hopcPrimeContributionFn σ t))
    (hPrime_ne :
      ∀ p : {q // Nat.Prime q}, eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hEvStationary :
      ∀ᶠ S : Finset {q // Nat.Prime q} in Filter.atTop,
        DkMath.RH.stationaryAt
          (fun v : ℝ => eulerZetaFinite_onVertical S σ v) t) :
    hopcPrimeContributionTsum σ t = 0 := by
  have hEv0 :
      ∀ᶠ S : Finset {q // Nat.Prime q} in Filter.atTop,
        hopcPrimeContributionSum (S := S) σ t = 0 :=
    eventually_hopcPrimeContributionSum_eq_zero_of_eventually_stationaryAt
      (σ := σ) (t := t) hPrime_ne hEvStationary
  have hEventuallyEq :
      (fun S : Finset {q // Nat.Prime q} =>
        hopcPrimeContributionSum (S := S) σ t) =ᶠ[Filter.atTop]
      (fun _ => (0 : ℝ)) :=
    hEv0
  have hT0 :
      Filter.Tendsto
        (fun S : Finset {q // Nat.Prime q} =>
          hopcPrimeContributionSum (S := S) σ t)
        Filter.atTop (𝓝 (0 : ℝ)) := by
    exact
      (tendsto_const_nhds :
        Filter.Tendsto (fun _ : Finset {q // Nat.Prime q} => (0 : ℝ))
          Filter.atTop (𝓝 (0 : ℝ))).congr' hEventuallyEq.symm
  have hTsum :
      Filter.Tendsto
        (fun S : Finset {q // Nat.Prime q} =>
          hopcPrimeContributionSum (S := S) σ t)
        Filter.atTop (𝓝 (hopcPrimeContributionTsum σ t)) := by
    simpa only [HasSum, hopcPrimeContributionFn, hopcPrimeContributionTsum,
      hopcPrimeContributionSum]
      using hSummable.hasSum
  exact tendsto_nhds_unique hTsum hT0

/--
`C / p^σ` 上界（`σ > 1`）と `eventually stationary` から、
`hopcPrimeContributionTsum = 0` を得る。
-/
theorem hopcPrimeContributionTsum_eq_zero_of_prime_rpow_bound_of_eventually_stationaryAt
    {σ t C : ℝ}
    (hσ : 1 < σ)
    (hAbsLe :
      ∀ p : {q // Nat.Prime q},
        |hopcPrimeContributionFn σ t p| ≤ C / (↑p : ℝ) ^ σ)
    (hPrime_ne :
      ∀ p : {q // Nat.Prime q}, eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hEvStationary :
      ∀ᶠ S : Finset {q // Nat.Prime q} in Filter.atTop,
        DkMath.RH.stationaryAt
          (fun v : ℝ => eulerZetaFinite_onVertical S σ v) t) :
    hopcPrimeContributionTsum σ t = 0 := by
  have hSummable : Summable (hopcPrimeContributionFn σ t) :=
    summable_hopcPrimeContributionFn_of_prime_rpow_bound
      (σ := σ) (t := t) (C := C) hσ hAbsLe
  exact
    hopcPrimeContributionTsum_eq_zero_of_summable_of_eventually_stationaryAt
      (σ := σ) (t := t) hSummable hPrime_ne hEvStationary

/--
`C / p^σ` 上界（`σ > 1`）と `eventually stationary` から、
有限寄与和の atTop 極限（0）を得る。
-/
theorem tendsto_hopcPrimeContributionSum_atTop_of_prime_rpow_bound_of_eventually_stationaryAt
    {σ t C : ℝ}
    (hσ : 1 < σ)
    (hAbsLe :
      ∀ p : {q // Nat.Prime q},
        |hopcPrimeContributionFn σ t p| ≤ C / (↑p : ℝ) ^ σ)
    (hPrime_ne :
      ∀ p : {q // Nat.Prime q}, eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hEvStationary :
      ∀ᶠ S : Finset {q // Nat.Prime q} in Filter.atTop,
        DkMath.RH.stationaryAt
          (fun v : ℝ => eulerZetaFinite_onVertical S σ v) t) :
    Filter.Tendsto
      (fun S : Finset {p // Nat.Prime p} =>
        hopcPrimeContributionSum (S := S) σ t)
      Filter.atTop (𝓝 (0 : ℝ)) := by
  have hSummable : Summable (hopcPrimeContributionFn σ t) :=
    summable_hopcPrimeContributionFn_of_prime_rpow_bound
      (σ := σ) (t := t) (C := C) hσ hAbsLe
  have hTsumZero :
      hopcPrimeContributionTsum σ t = 0 :=
    hopcPrimeContributionTsum_eq_zero_of_prime_rpow_bound_of_eventually_stationaryAt
      (σ := σ) (t := t) (C := C) hσ hAbsLe hPrime_ne hEvStationary
  exact
    tendsto_hopcPrimeContributionSum_atTop_of_summable_assumptions
      (σ := σ) (t := t) ⟨hSummable, hTsumZero⟩

/--
`σ > 1` なら、全素数で `w_p(σ,t) = exp((σ+it)\log p)-1` は非零。
-/
theorem hPrime_ne_of_sigma_gt_one
    {σ t : ℝ}
    (hσ : 1 < σ) :
    ∀ p : {q // Nat.Prime q}, eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0 := by
  intro p
  exact eulerZeta_exp_s_log_p_sub_one_ne_zero_strong p.1 p.2 σ t hσ

/--
`σ > 1` 仮定版:
`eventually stationary` から `eventually hopcPrimeContributionSum = 0` を得る。
-/
theorem eventually_hopcPrimeContributionSum_eq_zero_of_sigma_gt_one_of_eventually_stationaryAt
    {σ t : ℝ}
    (hσ : 1 < σ)
    (hEvStationary :
      ∀ᶠ S : Finset {q // Nat.Prime q} in Filter.atTop,
        DkMath.RH.stationaryAt
          (fun v : ℝ => eulerZetaFinite_onVertical S σ v) t) :
    ∀ᶠ S : Finset {q // Nat.Prime q} in Filter.atTop,
      hopcPrimeContributionSum (S := S) σ t = 0 :=
  eventually_hopcPrimeContributionSum_eq_zero_of_eventually_stationaryAt
    (σ := σ) (t := t) (hPrime_ne_of_sigma_gt_one (σ := σ) (t := t) hσ) hEvStationary

/--
`σ > 1` 仮定版:
`eventually stationary` から `hopcPrimeContributionTsum = 0` を得る。
-/
theorem hopcPrimeContributionTsum_eq_zero_of_prime_rpow_bound_sigma_gt_one
    {σ t C : ℝ}
    (hσ : 1 < σ)
    (hAbsLe :
      ∀ p : {q // Nat.Prime q},
        |hopcPrimeContributionFn σ t p| ≤ C / (↑p : ℝ) ^ σ)
    (hEvStationary :
      ∀ᶠ S : Finset {q // Nat.Prime q} in Filter.atTop,
        DkMath.RH.stationaryAt
          (fun v : ℝ => eulerZetaFinite_onVertical S σ v) t) :
    hopcPrimeContributionTsum σ t = 0 :=
  hopcPrimeContributionTsum_eq_zero_of_prime_rpow_bound_of_eventually_stationaryAt
    (σ := σ) (t := t) (C := C) hσ hAbsLe
    (hPrime_ne_of_sigma_gt_one (σ := σ) (t := t) hσ) hEvStationary

/--
`σ > 1` 仮定版:
`C / p^σ` 上界と `eventually stationary` から
有限寄与和の atTop 極限（0）を得る。
-/
theorem tendsto_hopcPrimeContributionSum_atTop_of_prime_rpow_bound_sigma_gt_one
    {σ t C : ℝ}
    (hσ : 1 < σ)
    (hAbsLe :
      ∀ p : {q // Nat.Prime q},
        |hopcPrimeContributionFn σ t p| ≤ C / (↑p : ℝ) ^ σ)
    (hEvStationary :
      ∀ᶠ S : Finset {q // Nat.Prime q} in Filter.atTop,
        DkMath.RH.stationaryAt
          (fun v : ℝ => eulerZetaFinite_onVertical S σ v) t) :
    Filter.Tendsto
      (fun S : Finset {p // Nat.Prime p} =>
        hopcPrimeContributionSum (S := S) σ t)
      Filter.atTop (𝓝 (0 : ℝ)) :=
  tendsto_hopcPrimeContributionSum_atTop_of_prime_rpow_bound_of_eventually_stationaryAt
    (σ := σ) (t := t) (C := C) hσ hAbsLe
    (hPrime_ne_of_sigma_gt_one (σ := σ) (t := t) hσ) hEvStationary

end DkMath.RH.EulerZeta
