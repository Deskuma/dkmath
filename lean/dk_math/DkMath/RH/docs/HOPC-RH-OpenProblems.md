# HOPC-RH Open Problems

HOPC-RH の未完タスクを、実装可能な issue 形式で管理する。

## OP-001: finite → infinite（位相寄与和）の接続

- 背景:
  - 現在は有限集合 `S` 上で
    `hopcPrimeContributionSum S σ t`
    による停留判定が成立している。
- 課題:
  - `S` を拡大したときの収束・極限交換条件を整理し、
    無限側観測量へ上げるための前提を明文化する。
- 目標成果:
  - 条件付きの「有限判定 → 極限判定」補題群
- 状態: 進行中（RH-O7: `BoundarySide` split bound から `hAbsLe` 供給 wrapper を追加）
- 到達済み:
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
  - `eventually_hopcPrimeContributionSum_eq_zero_of_eventually_stationaryAt`
  - `eventually_abs_hopcPrimeContributionSum_lt_of_eventually_stationaryAt`
  - `hopcPrimeContributionTsum_eq_zero_of_summable_of_eventually_stationaryAt`
  - `summable_hopcPrimeContributionFn_of_prime_rpow_bound`
  - `majorant_assumptions_of_prime_rpow_bound`
  - `tendsto_hopcPrimeContributionSum_atTop_of_prime_rpow_bound`
  - `hopcPrimeContributionTsum_eq_zero_of_prime_rpow_bound_of_eventually_stationaryAt`
  - `tendsto_hopcPrimeContributionSum_atTop_of_prime_rpow_bound_of_eventually_stationaryAt`
  - `hPrime_ne_of_sigma_gt_one`
  - `eventually_hopcPrimeContributionSum_eq_zero_of_sigma_gt_one_of_eventually_stationaryAt`
  - `hopcPrimeContributionTsum_eq_zero_of_prime_rpow_bound_sigma_gt_one`
  - `tendsto_hopcPrimeContributionSum_atTop_of_prime_rpow_bound_sigma_gt_one`
  - `hopcPrimeContributionFn_abs_le_prime_rpow_of_boundaryDiffPow_split`
  - `hopcPrimeContributionTsum_eq_zero_of_boundaryDiffPow_split_prime_rpow_bound_sigma_gt_one`
  - `tendsto_hopcPrimeContributionSum_atTop_of_boundaryDiffPow_split_prime_rpow_bound_sigma_gt_one`
- 残タスク:
  - `hAbs_dvd` / `hAbs_offdvd` を CFBRC 既存 provider 仮定から導く具体評価補題を追加
  - split bound 仮定を `BoundaryInsertLocalLiftProvider` レベルへ持ち上げる設計を追加
- 優先度: 高

## OP-002: 非零前提の管理 API

- 背景:
  - 多くの補題が `∀ p ∈ S, w_p(σ,t) ≠ 0` を要求。
- 課題:
  - 実運用でこの前提を毎回手で供給するコストが高い。
- 目標成果:
  - 前提正規化 wrapper（有限集合版）
  - 使い回し用の補題セット（非零前提の伝播）
- 優先度: 中

## OP-003: CFBRC 連携の実定理（橋渡し命題）

- 背景:
  - 文書上は prime-local contribution language が整った。
- 課題:
  - CFBRC 側 API（core/divisibility/valuation）と
    RH 側 HOPC API をつなぐ「具体的命題」の供給層を強化する。
- 目標成果:
  - provider 前提を直接受ける bridge 補題（`hS_lift` / `hsum_lift` 実供給）
  - finite-set から運用可能な仮定正規化 wrapper 群
- 状態: 完了（RH-N1〜N31 で API 骨格・provider 入口・実供給導線を整備完了）
- 到達済み:
  - singleton bridge（global/local）
  - small finite-set bridge（`insert p S`）
  - `BoundarySide` 統一高位 API（singleton / insert / split）
  - provider 入口:
    - `BoundaryInsertLocalLiftProvider`
    - `exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_provider`
  - provider 段階供給補題:
    - `boundary_hS_lift_of_nonzero_on_S_and_witness`
    - `boundaryInsertLocalLiftProvider_of_nonzero_on_S_and_witness`
    - `boundary_hsum_lift_of_local_zero_on_S_and_witness`
    - `boundaryInsertLocalLiftProvider_of_nonzero_and_local_zero_on_S_and_witness`
  - provider 実供給補題:
    - `boundary_nonzero_on_S_of_boundary_dvd_and_gap`
    - `boundary_hwnz_witness_of_boundaryCore_nonzero`
    - `boundary_local_zero_on_S_of_boundary_dvd_and_gap`
    - `boundary_hlocal_witness_of_boundaryCore_local_zero`
    - `boundary_dvd_on_insert_of_boundary_dvd_and_witness`
    - `boundary_gap_on_insert_of_boundary_gap_and_witness`
    - `exists_boundaryPrime_dvd_gap_of_cfbRc_primitive_prime_boundaryDiffPow_of_coprime`
    - `exists_boundary_dvd_gap_on_insert_of_cfbRc_primitive_prime_boundaryDiffPow_of_coprime`
    - `hopcPrimeLocalContribution_eq_eulerZetaFactorPhaseVelLocal_of_nonzero`
    - `hopcPrimeLocalContribution_eq_zero_of_factorPhaseVelLocal_eq_zero_of_nonzero`
    - `eulerZetaFactorPhaseVelLocal_eq_zero_of_hopcPrimeLocalContribution_eq_zero_of_nonzero`
    - `boundary_hlocal_core_of_boundaryCore_factorPhaseVelLocal_eq_zero`
    - `boundary_hfactor_core0_of_boundaryCore_local_zero`
    - `boundary_hlocal_core_of_boundaryDiffPow_local_zero`
    - `boundary_hwnz_core_of_boundaryDiffPow_nonzero`
    - `boundary_hlocal_diff0_of_boundaryDiffPow_factorPhaseVelLocal_eq_zero`
    - `boundaryInsertLocalLiftProvider_of_boundary_dvd_and_gap_and_local_zero`
    - `boundaryInsertLocalLiftProvider_of_boundary_dvd_and_gap`
    - `boundaryInsertLocalLiftProvider_of_boundary_dvd_and_gap_of_boundaryCore_witness`
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
  - README / Discussion / docs README の利用テンプレート同期（split 版 / provider 版）
- 残タスク:
  - なし（以後の発展は OP-001 / OP-004 で管理）
- 優先度: 完了

## OP-004: 曲率条件の運用規約

- 背景:
  - `nondegenerateStationaryAt` は導入済みだが、
    どの状況で `phaseCurv ≠ 0` を供給するかの運用規約が未整理。
- 課題:
  - 曲率前提の供給パターン（解析仮定 / 計算補題 / provider）を切り分ける。
- 目標成果:
  - `phaseCurv` 供給戦略メモ + wrapper 名称規約
- 優先度: 中

## OP-005: 文書同期の継続管理

- 背景:
  - README / Roadmap / Glossary / Discussion が増えたため同期漏れリスクがある。
- 課題:
  - どの更新時にどの文書を更新するかのルールを固定する。
- 目標成果:
  - ドキュメント更新チェックリスト（最小運用）
- 優先度: 低

### OP-005 チェックリスト v1（最小運用）

更新時に、次を上から順に確認する。

1. `.lean` 追加/改名/削除があるか
   - `DkMath/RH/README.md` の「ファイル構成（実装）」を更新
   - 必要なら `DkMath/RH.lean` の import を更新
2. 公開 API（定義/補題名）が増減したか
   - `DkMath/RH/README.md` の「主要 API」を更新
   - `DkMath/RH/docs/README.md` の「現状 API」を更新
   - `DkMath/RH/docs/HOPC-RH-Glossary.md` に語彙を追加
3. CFBRC 連携 API/bridge が増減したか
   - `DkMath/RH/docs/RH-CFBRC-Discussion.md` の
     `Implementation Bridge` / `Bridge Usage` を更新
4. フェーズ状態や次段計画が変わったか
   - `DkMath/RH/docs/HOPC-RH-Roadmap.md` のフェーズ状態を更新
   - `DkMath/RH/docs/HOPC-RH-OpenProblems.md` の優先度・状態を更新
5. すべての作業で履歴を記録したか
   - `DkMath/RH/docs/RH_Implements_History.md` にテンプレート形式で追記

## 参照

- 方針: `HOPC-RH.txt`
- ロードマップ: `HOPC-RH-Roadmap.md`
- 用語集: `HOPC-RH-Glossary.md`
- 議論: `RH-CFBRC-Discussion.md`
- 実装履歴: `RH_Implements_History.md`
