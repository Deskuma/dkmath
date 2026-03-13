# DkMath.RH：位相ドリフト骨格 + EulerZeta（現状の全コード）

- Authors: D. and Kenro (ChatGPT-5.2)
- Last updated: 2026/03/13 23:45

このディレクトリは、リーマンゼータ関数に差し込む前に必要な

- 「複素関数の位相（角度）の変化＝位相速度」を Lean で扱う骨格
- その骨格を使って定義した **EulerZeta（magnitude/phase）** の無限積を、収束・正値まで含めて固める

ためのモジュール群です。

重要方針は 2 つ：

1. `arg`（偏角）を直接扱わず、**位相を積分で定義（アンラップ）** して枝問題を回避する。
2. 位相付き Euler 因子を「magnitude（大きさ）」と「phase（位相）」に分解し、
   まず magnitude の無限積を **σ > 1 で収束する**ことまで Lean で確定する。

このファイルは詳細版（理論背景・証明戦略）であり、
入口と API 一覧は `DkMath/RH/README.md` を優先参照とする。
実装計画の 1 枚版は `HOPC-RH-Roadmap.md` を参照。
語彙の定義域整理は `HOPC-RH-Glossary.md` を参照。
未解決タスク一覧は `HOPC-RH-OpenProblems.md` を参照。

---

## 論文

このモジュール群の理論的背景は、次の論文に基づきます。

- [Euler Zeta Function ζe(s): A Novel Approach to Prime Distribution through Scale Analysis](./EulerZetaFunction-v0-1.pdf)
  - March 15, 2025
  - Author: D. and Kenro (ChatGPT-4o)
  - cid: 67d46595-3550-8009-896d-00c3263c4f23

### オイラーゼータ関数

$$
  \Large
  \zeta_e(s) = \prod_{p} \frac{e^{\sigma \log p}}{| e^{(\sigma+it) \log p} - 1 |}
$$

オイラー積表示より導出されたゼータ関数の変形版で、位相因子を含むものを指します。

#### オイラー積表示

$$
  \large
  \zeta(s) = \prod_{p} \frac{1}{1 - p^{-s}}
$$

$$
  \left(
  \frac{1}{1 - p^{-s}}
  = \frac{p^s}{p^s - 1}
  = \frac{\exp(s\ln p)}{\exp(s\ln p) - 1}
  \right)
$$

※ $s = \sigma + it$ : 複素数変数

---

## ファイル構成（現状）

### 位相ドリフト骨格

- `Basic.lean`
  空ファイル（予約）。将来の共通設定や再輸出（re-export）置き場候補。

- `Defs.lean`
  定義置き場（記号・概念の導入のみ）。

- `Lemmas.lean`
  定義間の関係を示す補題（代数コア、同値、別表現など）。

- `Theorems.lean`
  積分で定義した位相が期待通り微分できること（解析骨格）を示す定理。

### EulerZeta（今回追加された成果）

- `EulerZeta.lean`
  EulerZeta（magnitude/phase）に関する公開インタフェース（定義の再輸出、主要定理の提示）。

- `EulerZetaLemmas.lean`
  EulerZeta の局所補題集：
  分母 `w = exp((σ+it)log p) - 1` の非零、`‖a_p - 1‖` の評価など。

- `EulerZetaConvergence.lean`
  収束と正値の主証明：
  `σ > 1` のもとで `EulerZetaMagMultipliable` と `0 < eulerZetaMag` を確定。

- `HopcInfiniteLift.lean`
  OP-001 向け finite→infinite 接続 API：
  `HasSum` 仮定から `hopcPrimeContributionSum` の atTop 極限・`tsum` へ接続。

---

## 位相ドリフト骨格：到達点（短く）

- 位相速度 `phaseVel` を `torque / normSq` として代数的に扱えるようにした。
- 「ドリフト消失」は「位相速度ゼロ」と同値になった（零点回避 `f t ≠ 0` を条件に）。
- `arg` を使わず、位相を積分で定義した上で、微分が正しく戻ることを示した。

（詳細は [DkMath_RH.md](./DkMath_RH.md) を参照）

---

## EulerZeta：定義と成果（短く）

### 定義（magnitude / phase）

素数ごとに

- 分母（複素数）
  `w(p,σ,t) := exp((σ+it)log p) - 1`

- magnitude 因子（実数）
  `a_p(σ,t) := exp(σ log p) / ‖w(p,σ,t)‖`

を定義し、EulerZeta magnitude を

- `eulerZetaMag (σ t : ℝ) : ℝ := ∏' p : {p // Nat.Prime p}, a_p(σ,t)`

として無限積（`tprod`）で定義します。

また位相は

- `eulerZetaPhase (p) (σ t) := Complex.arg (w(p,σ,t))`

として別途導入します（位相骨格の側は `arg` を直接使わずにアンラップへ接続する予定）。

### 主定理（σ > 1）

- `eulerZetaMag_multipliable_sigma_gt_one`
  `σ > 1` のもとで EulerZeta magnitude の無限積が収束（`Multipliable`）。

- `eulerZetaMag_pos_sigma_gt_one`
  `σ > 1` のもとで `0 < eulerZetaMag σ t`。

### 証明戦略（要点）

1. `w(p,σ,t) ≠ 0` を確定（定義が安全になる）。
2. 近似評価：`‖a_p(σ,t) - 1‖ ≤ 2 / p^σ`（σ > 1）。
3. `∑ 1/n^σ`（p-series）へ比較して `Summable` を得る。
4. Mathlib の一般定理で `Multipliable` と `tprod` の正値へ落とす。

---

## 現状 API（HOPC 公開名・RH-N53 時点）

CFBRC 連携で使う公開名は次を基準とする。

- 観測量（`EulerZeta.lean`）
  - `hopcPrimeLocalContribution`
  - `hopcPrimeContributionSum`
- finite→infinite 接続（`HopcInfiniteLift.lean`）
  - `hopcPrimeContributionFn`
  - `hopcPrimeContributionTsum`
  - `HopcInfiniteLiftAssumptions`
  - `HopcInfiniteLiftSummableAssumptions`
  - `HopcInfiniteLiftMajorantAssumptions`
  - `summable_hopcPrimeContributionFn_of_majorant_assumptions`
  - `summable_assumptions_of_majorant_assumptions`
  - `hasSumZero_of_summable_assumptions`
  - `assumptions_of_summable_assumptions`
  - `tendsto_hopcPrimeContributionSum_atTop_of_assumptions`
  - `hopcPrimeContributionTsum_eq_zero_of_assumptions`
  - `tendsto_hopcPrimeContributionSum_atTop_of_summable_assumptions`
  - `hopcPrimeContributionTsum_eq_zero_of_summable_assumptions`
  - `tendsto_hopcPrimeContributionSum_atTop_of_majorant_assumptions`
  - `hopcPrimeContributionTsum_eq_zero_of_majorant_assumptions`
  - `eventually_abs_hopcPrimeContributionSum_lt_of_assumptions`
  - `eventually_abs_hopcPrimeContributionSum_lt_of_summable_assumptions`
  - `eventually_abs_hopcPrimeContributionSum_lt_of_majorant_assumptions`
  - `summable_hopcPrimeContributionFn_of_prime_rpow_bound`
  - `majorant_assumptions_of_prime_rpow_bound`
  - `tendsto_hopcPrimeContributionSum_atTop_of_prime_rpow_bound`
  - `eventually_hopcPrimeContributionSum_eq_zero_of_eventually_stationaryAt`
  - `eventually_abs_hopcPrimeContributionSum_lt_of_eventually_stationaryAt`
  - `hopcPrimeContributionTsum_eq_zero_of_summable_of_eventually_stationaryAt`
  - `hopcPrimeContributionTsum_eq_zero_of_prime_rpow_bound_of_eventually_stationaryAt`
  - `tendsto_hopcPrimeContributionSum_atTop_of_prime_rpow_bound_of_eventually_stationaryAt`
  - `hPrime_ne_of_sigma_gt_one`
  - `eventually_hopcPrimeContributionSum_eq_zero_of_sigma_gt_one_of_eventually_stationaryAt`
  - `hopcPrimeContributionTsum_eq_zero_of_prime_rpow_bound_sigma_gt_one`
  - `tendsto_hopcPrimeContributionSum_atTop_of_prime_rpow_bound_sigma_gt_one`
  - `hopcPrimeContributionFn_abs_le_prime_rpow_of_boundaryDiffPow_split`
  - `hopcPrimeContributionTsum_eq_zero_of_boundaryDiffPow_split_prime_rpow_bound_sigma_gt_one`
  - `tendsto_hopcPrimeContributionSum_atTop_of_boundaryDiffPow_split_prime_rpow_bound_sigma_gt_one`
  - `hopcPrimeContributionFn_abs_le_prime_rpow_of_local_zero`
  - `hopcPrimeContributionFn_abs_le_prime_rpow_of_boundaryDiffPow_factor0`
  - `hopcPrimeContributionFn_abs_le_prime_rpow_of_boundaryDiffPow_offdvd_local0`
  - `hopcPrimeContributionFn_abs_le_prime_rpow_of_boundaryDiffPow_factor0_with_offdvd_local0`
  - `hopcPrimeContributionTsum_eq_zero_of_boundaryDiffPow_factor0_with_offdvd_local0_sigma_gt_one`
  - `tendsto_hopcPrimeContributionSum_atTop_of_boundaryDiffPow_factor0_with_offdvd_local0_sigma_gt_one`
  - `BoundaryOffDvdLocalZeroProvider`
  - `BoundaryOffDvdLocalZeroOnSetProvider`
  - `boundaryOffDvdLocalZeroOnSetProvider_of_global`
  - `boundary_hlocal_offdvd_singleton_of_insertProvider_and_witness_local0`
  - `boundary_hlocal_offdvd_singleton_of_insertProvider_and_boundaryDiffPow_factor0`
  - `boundaryOffDvdLocalZeroOnSetProvider_singleton_of_insertProvider_and_boundaryDiffPow_factor0`
  - `boundary_hlocal_on_S_of_insertProvider_and_witness_local0_and_local0_on_erase`
  - `boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_witness_local0_and_local0_on_erase`
  - `boundary_hlocal_on_S_of_insertProvider_and_boundaryDiffPow_factor0_and_dvd_on_erase`
  - `boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_boundaryDiffPow_factor0_and_dvd_on_erase`
  - `boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_boundaryDiffPow_factor0_and_dvd_on_S`
  - `boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_global_witness_local0_and_local0_on_erase` (legacy, deprecated; removal target: 2026-06-30)
  - `boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_boundaryDiffPow_factor0_and_dvd_on_erase_of_global_witness` (legacy, deprecated; removal target: 2026-06-30)
  - `boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_boundaryDiffPow_factor0_and_dvd_on_S_of_global_witness` (legacy, deprecated; removal target: 2026-06-30)
  - `boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_boundaryDiffPow_factor0_and_dvd_on_S_of_cfbRc_primitive_prime_boundaryDiffPow_of_coprime` (legacy, deprecated; removal target: 2026-06-30)
  - `BoundaryGlobalWitnessProvider`
  - `BoundaryGlobalWitnessLocalZeroProvider`
  - `boundaryGlobalWitnessProvider_of_exists`
  - `boundaryGlobalWitnessLocalZeroProvider_of_exists`
  - `boundaryGlobalWitnessProvider_of_cfbRc_primitive_prime_boundaryDiffPow_of_coprime`
  - `boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_globalWitnessLocalZeroProvider_and_local0_on_erase`
  - `boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_boundaryDiffPow_factor0_and_dvd_on_S_of_globalWitnessProvider`
  - `boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_boundaryDiffPow_factor0_and_dvd_on_S_of_globalWitnessProvider_of_cfbRc_primitive_prime_boundaryDiffPow_of_coprime`
  - `BoundaryDiffPowFactorZeroProvider`
  - `boundaryDiffPowFactorZeroProvider_of_split`
  - `boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_dvd_on_erase_of_globalWitnessProvider_and_diffFactorZeroProvider`
  - `boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_dvd_on_S_of_globalWitnessProvider_and_diffFactorZeroProvider`
  - `boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_dvd_on_S_of_cfbRc_primitive_prime_and_diffFactorZeroProvider`
  - `BoundaryOffDvdFactorZeroProvider`
  - `boundaryOffDvdFactorZeroProvider_of_split`
  - `boundaryOffDvdFactorZeroProvider_of_nonzero_and_localZeroProvider`
  - `boundaryOffDvdFactorZeroProvider_of_boundaryInsertLocalLiftProvider_of_nonzero_and_localZeroProvider`
  - `boundaryOffDvdFactorZeroProvider_of_boundaryInsertLocalLiftProvider_of_nonzero_and_local_zero`
  - `boundaryOffDvdLocalZeroProvider_of_offdvdFactorZeroProvider`
  - `boundaryOffDvdLocalZeroProvider_of_boundaryInsertLocalLiftProvider`
  - `boundaryOffDvdLocalZeroProvider_of_factorPhaseVelLocal_eq_zero`
  - `boundaryOffDvdLocalZeroProvider_of_boundaryInsertLocalLiftProvider_of_factorPhaseVelLocal_eq_zero`
  - `boundaryOffDvdLocalZeroProvider_of_boundaryInsertLocalLiftProvider_of_offdvdFactorZeroProvider`
  - `hopcPrimeContributionFn_abs_le_prime_rpow_of_boundaryDiffPow_factor0_with_insertProvider_and_offdvdFactorZeroProvider`
  - `hopcPrimeContributionTsum_eq_zero_of_boundaryDiffPow_factor0_with_insertProvider_and_offdvdFactorZeroProvider_sigma_gt_one`
  - `tendsto_hopcPrimeContributionSum_atTop_of_boundaryDiffPow_factor0_with_insertProvider_and_offdvdFactorZeroProvider_sigma_gt_one`
  - `hopcPrimeContributionFn_abs_le_prime_rpow_of_boundaryDiffPow_factor0_with_insertProvider_sigma`
  - `hopcPrimeContributionTsum_eq_zero_of_boundaryDiffPow_factor0_with_insertProvider_sigma_gt_one`
  - `tendsto_hopcPrimeContributionSum_atTop_of_boundaryDiffPow_factor0_with_insertProvider_sigma_gt_one`
  - `hopcPrimeContributionFn_abs_le_prime_rpow_of_boundaryDiffPow_factor0_with_offdvd_provider`
  - `hopcPrimeContributionTsum_eq_zero_of_boundaryDiffPow_factor0_with_offdvd_provider_sigma_gt_one`
  - `tendsto_hopcPrimeContributionSum_atTop_of_boundaryDiffPow_factor0_with_offdvd_provider_sigma_gt_one`
- 同一化（`EulerZetaLemmas.lean`）
  - `eulerZetaFactorPhaseVelFinite_eq_hopcPrimeContributionSum`
- 停留判定（`EulerZetaLemmas.lean`）
  - `driftFreeAt_eulerZetaFinite_onVertical_iff_hopcPrimeContributionSum_eq_zero`
  - `stationaryAt_eulerZetaFinite_onVertical_iff_hopcPrimeContributionSum_eq_zero`
  - `nondegenerateStationaryAt_eulerZetaFinite_onVertical_iff_hopcPrimeContributionSum`
- CFBRC 連携 bridge（`CFBRCBridge.lean`）
  - `exists_stationaryAt_singleton_of_cfbRc_primitive_prime_bridge`
  - `exists_stationaryAt_singleton_of_cfbRc_primitive_prime_bridge_of_local`
  - `stationaryAt_insert_of_hopcPrimeContributionSum_eq_zero`
  - `exists_stationaryAt_insert_of_cfbRc_primitive_prime_bridge_of_local`
  - `exists_stationaryAt_insert_of_cfbRc_primitive_prime_bridge_of_local_split`
  - `exists_stationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_local`
  - `exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_local`
  - `exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_local_split`
  - `BoundaryInsertLocalLiftProvider`
  - `exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_provider`
  - `boundary_hS_lift_of_nonzero_on_S_and_witness`
  - `boundaryInsertLocalLiftProvider_of_nonzero_on_S_and_witness`
  - `boundary_hsum_lift_of_local_zero_on_S_and_witness`
  - `boundaryInsertLocalLiftProvider_of_nonzero_and_local_zero_on_S_and_witness`
  - `boundary_nonzero_on_S_of_boundary_dvd_and_gap`
  - `boundary_hwnz_witness_of_boundaryCore_nonzero`
  - `boundary_local_zero_on_S_of_boundary_dvd_and_gap`
  - `boundary_hlocal_witness_of_boundaryCore_local_zero`
  - `boundary_dvd_on_insert_of_boundary_dvd_and_witness`
  - `boundary_gap_on_insert_of_boundary_gap_and_witness`
  - `exists_boundaryPrime_dvd_gap_of_cfbRc_primitive_prime_boundaryDiffPow_of_coprime`
  - `exists_boundary_dvd_gap_on_insert_of_cfbRc_primitive_prime_boundaryDiffPow_of_coprime`
  - `boundaryInsertLocalLiftProvider_of_boundary_dvd_and_gap`
  - `boundaryInsertLocalLiftProvider_of_boundary_dvd_and_gap_of_boundaryCore_witness`
  - `hopcPrimeLocalContribution_eq_eulerZetaFactorPhaseVelLocal_of_nonzero`
  - `hopcPrimeLocalContribution_eq_zero_of_factorPhaseVelLocal_eq_zero_of_nonzero`
  - `eulerZetaFactorPhaseVelLocal_eq_zero_of_hopcPrimeLocalContribution_eq_zero_of_nonzero`
  - `boundary_hlocal_core_of_boundaryCore_factorPhaseVelLocal_eq_zero`
  - `boundary_hfactor_core0_of_boundaryCore_local_zero`
  - `boundary_hlocal_core_of_boundaryDiffPow_local_zero`
  - `boundary_hwnz_core_of_boundaryDiffPow_nonzero`
  - `boundary_hlocal_diff0_of_boundaryDiffPow_factorPhaseVelLocal_eq_zero`
  - `boundaryInsertLocalLiftProvider_of_boundary_dvd_gap_of_boundaryCore_factor0`
  - `boundaryInsertLocalLiftProvider_of_boundary_dvd_gap_of_boundaryDiffPow_local0`
  - `boundaryInsertLocalLiftProvider_of_boundary_dvd_gap_of_boundaryDiffPow_factor0`
  - `boundaryInsertLocalLiftProvider_of_boundary_dvd_of_boundaryDiffPow_factor0`
  - `boundaryDiffPowDvdSet`
  - `boundary_dvd_on_boundaryDiffPowDvdSet`
  - `boundaryInsertLocalLiftProvider_of_boundaryDiffPow_factor0_normalized`
  - `boundaryInsertLocalLiftProvider_of_boundaryDiffPow_factor0_with_offdvd`
  - `exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_factor0`
  - `exists_stationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_factor0`
  - `exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_local0`
  - `exists_stationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_local0`
  - `exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_local0`
  - `exists_stationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_local0`
  - `exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_factor0`
  - `exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_factor0_of_dvd`
  - `exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_factor0_normalized`
  - `exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_factor0_with_offdvd`
  - `exists_stationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_factor0`
  - `boundaryInsertLocalLiftProvider_of_boundary_dvd_and_gap_and_local_zero`

補足:

- 上記公開名は明示和
  `∑_{p∈S} (log p - phaseVel(w_p))`
  の alias/wrapper 層として設計されている。
- `RH-CFBRC-Discussion.md` の `Implementation Bridge (RH-H1/H2)` と対応。

---

## 利用例（import）

RH 側 API を使う最小例:

```lean
import DkMath.RH.EulerZeta
import DkMath.RH.EulerZetaLemmas
```

CFBRC 連携 bridge まで使う例:

```lean
import DkMath.RH.CFBRCBridge

open DkMath.RH.EulerZeta
```

`BoundarySide` + small finite-set（split 仮定）テンプレート:

```lean
import DkMath.RH.CFBRCBridge

open DkMath.RH.EulerZeta

example (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u)
    (hS_lift :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with | .right => ¬ p.1 ∣ x | .left => ¬ p.1 ∣ u) →
          ∀ r ∈ (insert p S), eulerZeta_exp_s_log_p_sub_one r.1 σ t ≠ 0)
    (hsum_lift :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with | .right => ¬ p.1 ∣ x | .left => ¬ p.1 ∣ u) →
          hopcPrimeContributionSum (S := insert p S) σ t = 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.stationaryAt
        (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t := by
  exact
    exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_local_split
      (side := side) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
      hd_prime hd_ge hx hu hcop hpnd hS_lift hsum_lift
```

`BoundaryInsertLocalLiftProvider`（provider record）テンプレート:

```lean
import DkMath.RH.CFBRCBridge

open DkMath.RH.EulerZeta

example (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u)
    (provider : BoundaryInsertLocalLiftProvider side S d x u σ t) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.stationaryAt
        (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t := by
  exact
    exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_provider
      (side := side) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
      hd_prime hd_ge hx hu hcop hpnd provider
```

段階供給（RH-N12/N13）から provider を生成するテンプレート:

```lean
import DkMath.RH.CFBRCBridge

open DkMath.RH.EulerZeta

example (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hS_nonzero :
      ∀ r ∈ S, eulerZeta_exp_s_log_p_sub_one r.1 σ t ≠ 0)
    (hwnz_witness :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with | .right => ¬ p.1 ∣ x | .left => ¬ p.1 ∣ u) →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hS_local0 :
      ∀ r ∈ S, hopcPrimeLocalContribution r.1 σ t = 0)
    (hlocal_witness :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with | .right => ¬ p.1 ∣ x | .left => ¬ p.1 ∣ u) →
          hopcPrimeLocalContribution p.1 σ t = 0) :
    BoundaryInsertLocalLiftProvider side S d x u σ t := by
  exact
    boundaryInsertLocalLiftProvider_of_nonzero_and_local_zero_on_S_and_witness
      (side := side) (S := S)
      (hS_nonzero := hS_nonzero)
      (hwnz_witness := hwnz_witness)
      (hS_local0 := hS_local0)
      (hlocal_witness := hlocal_witness)
```

`boundary_dvd + gap` 供給（RH-N21 前提簡約版）から provider を生成するテンプレート:

```lean
import DkMath.RH.CFBRCBridge

open DkMath.RH.EulerZeta

example (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hS_gap :
      ∀ r ∈ S, (match side with | .right => ¬ r.1 ∣ x | .left => ¬ r.1 ∣ u))
    (hwnz_witness :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with | .right => ¬ p.1 ∣ x | .left => ¬ p.1 ∣ u) →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hlocal_witness :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with | .right => ¬ p.1 ∣ x | .left => ¬ p.1 ∣ u) →
          hopcPrimeLocalContribution p.1 σ t = 0) :
    BoundaryInsertLocalLiftProvider side S d x u σ t := by
  exact
    boundaryInsertLocalLiftProvider_of_boundary_dvd_and_gap
      (side := side) (S := S)
      (hS_dvd := hS_dvd)
      (hS_gap := hS_gap)
      (hwnz_witness := hwnz_witness)
      (hlocal_witness := hlocal_witness)
```

`boundaryCore` 側 witness 仮定（RH-N22）から provider を生成するテンプレート:

```lean
import DkMath.RH.CFBRCBridge

open DkMath.RH.EulerZeta

example (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hS_gap :
      ∀ r ∈ S, (match side with | .right => ¬ r.1 ∣ x | .left => ¬ r.1 ∣ u))
    (hwnz_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hlocal_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          hopcPrimeLocalContribution p.1 σ t = 0) :
    BoundaryInsertLocalLiftProvider side S d x u σ t := by
  exact
    boundaryInsertLocalLiftProvider_of_boundary_dvd_and_gap_of_boundaryCore_witness
      (side := side) (S := S)
      (hS_dvd := hS_dvd)
      (hS_gap := hS_gap)
      (hwnz_core := hwnz_core)
      (hlocal_core := hlocal_core)
```

`boundaryCore` 上の factor 位相速度ゼロ仮定（RH-N23）から provider を生成するテンプレート:

```lean
import DkMath.RH.CFBRCBridge

open DkMath.RH.EulerZeta

example (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hS_gap :
      ∀ r ∈ S, (match side with | .right => ¬ r.1 ∣ x | .left => ¬ r.1 ∣ u))
    (hwnz_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_core0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0) :
    BoundaryInsertLocalLiftProvider side S d x u σ t := by
  exact
    boundaryInsertLocalLiftProvider_of_boundary_dvd_gap_of_boundaryCore_factor0
      (side := side) (S := S)
      (hS_dvd := hS_dvd)
      (hS_gap := hS_gap)
      (hwnz_core := hwnz_core)
      (hfactor_core0 := hfactor_core0)
```

`boundaryCore` factor0 から停留点存在へ直接接続するテンプレート（RH-N24）:

```lean
import DkMath.RH.CFBRCBridge

open DkMath.RH.EulerZeta

example (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with | .right => ¬ d ∣ x | .left => ¬ d ∣ u)
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hS_gap :
      ∀ r ∈ S, (match side with | .right => ¬ r.1 ∣ x | .left => ¬ r.1 ∣ u))
    (hwnz_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_core0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.stationaryAt
        (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t := by
  exact
    exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_factor0
      (side := side) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
      hd_prime hd_ge hx hu hcop hpnd hS_dvd hS_gap hwnz_core hfactor_core0
```

`boundaryCore` local0 から停留点存在へ直接接続するテンプレート（RH-N25）:

```lean
import DkMath.RH.CFBRCBridge

open DkMath.RH.EulerZeta

example (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with | .right => ¬ d ∣ x | .left => ¬ d ∣ u)
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hS_gap :
      ∀ r ∈ S, (match side with | .right => ¬ r.1 ∣ x | .left => ¬ r.1 ∣ u))
    (hwnz_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hlocal_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          hopcPrimeLocalContribution p.1 σ t = 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.stationaryAt
        (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t := by
  exact
    exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_local0
      (side := side) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
      hd_prime hd_ge hx hu hcop hpnd hS_dvd hS_gap hwnz_core hlocal_core
```

`boundaryDiffPow` local0 から停留点存在へ直接接続するテンプレート（RH-N26）:

```lean
import DkMath.RH.CFBRCBridge

open DkMath.RH.EulerZeta

example (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with | .right => ¬ d ∣ x | .left => ¬ d ∣ u)
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hS_gap :
      ∀ r ∈ S, (match side with | .right => ¬ r.1 ∣ x | .left => ¬ r.1 ∣ u))
    (hwnz_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hlocal_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          hopcPrimeLocalContribution p.1 σ t = 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.stationaryAt
        (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t := by
  exact
    exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_local0
      (side := side) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
      hd_prime hd_ge hx hu hcop hpnd hS_dvd hS_gap hwnz_core hlocal_diff0
```

`boundaryDiffPow` factor0 から停留点存在へ直接接続するテンプレート（RH-N27）:

```lean
import DkMath.RH.CFBRCBridge

open DkMath.RH.EulerZeta

example (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with | .right => ¬ d ∣ x | .left => ¬ d ∣ u)
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hS_gap :
      ∀ r ∈ S, (match side with | .right => ¬ r.1 ∣ x | .left => ¬ r.1 ∣ u))
    (hwnz_diff :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.stationaryAt
        (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t := by
  exact
    exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_factor0
      (side := side) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
      hd_prime hd_ge hx hu hcop hpnd hS_dvd hS_gap hwnz_diff hfactor_diff0
```

---

## `#print axioms` に `sorryAx` が出る件について（メモ）

ソース（`.lean`）上に `sorry` が無いのに `#print axioms` で `sorryAx` が見える場合、
典型的には次のどちらかです：

- 古い `.olean` が残っている（ビルドキャッシュ混入）
- 依存先（環境側）に `sorryAx` を含むものがある

まずは `lake clean` と `.lake/build` の再生成で切り分けるのが確実です。

なお `propext / Classical.choice / Quot.sound` は、Mathlib を普通に使うと出やすい標準的な依存です。

---

## 次にやると自然な拡張（予定メモ）

- EulerZeta の phase 側を、位相骨格（アンラップ位相）へ接続する：
  `arg` を直接扱わず、`phaseUnwrap` で連続位相として扱う。
- σ 方向（横方向）でも同型テンプレートを作る：
  `phaseVelSigma` / `phaseUnwrapSigma`。
- ゼータ差し込みのための仮定（零点回避・可微分性・可積分性）を整理してまとめる。

---

VSCode and GitHub Markdown $\LaTeX$ Style Documentation

This document uses GitHub-flavored Markdown and $\LaTeX$ for mathematical expressions. To render the $\LaTeX$ expressions correctly, ensure that your Markdown viewer supports MathJax or a similar library.
