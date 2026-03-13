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
- 状態: 完了（RH-O24: 未公開運用前提で外部依存なしを確認）
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
  - `boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_global_witness_local0_and_local0_on_erase`
  - `boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_boundaryDiffPow_factor0_and_dvd_on_erase_of_global_witness`
  - `boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_boundaryDiffPow_factor0_and_dvd_on_S_of_global_witness`
  - `boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_boundaryDiffPow_factor0_and_dvd_on_S_of_cfbRc_primitive_prime_boundaryDiffPow_of_coprime`
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
  - `boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_dvd_on_S_of_globalWitnessProvider_and_diffFactorZeroProvider`
  - `boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_dvd_on_S_of_cfbRc_primitive_prime_and_diffFactorZeroProvider`
  - `boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_dvd_on_erase_of_globalWitnessProvider_and_diffFactorZeroProvider`
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
- 備考:
  - リポジトリ内（`DkMath/**/*.lean`）の旧命名呼び出しは移行完了
    （旧命名は `CFBRCBridge.lean` の互換定義 + `deprecated` 属性のみ）
  - 本リポジトリは未公開運用のため、2026-03-14 時点で外部依存は想定しない。
  - 旧命名 API の削除実施は `2026-06-30` を目安に公開計画と合わせて再判定する。

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
- 状態: 完了（RH-P1/P2/P3/P4）
- 到達済み:
  - `nondegenerateStationaryAt_insert_of_hopcPrimeContributionSum_eq_zero_and_phaseCurv_ne_zero`
  - `exists_nondegenerateStationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_local_and_phaseCurv`
  - `BoundaryInsertPhaseCurvProvider`
  - `boundaryInsertPhaseCurvProvider_of_split`
  - `exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_bridge_of_local_split_and_phaseCurv`
  - `exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_local_split_and_phaseCurv`
  - `exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_provider_and_phaseCurvProvider`
  - `exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_factor0_and_phaseCurv`
  - `exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_local0_and_phaseCurv`
  - `exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_local0_and_phaseCurv`
  - `exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_factor0_and_phaseCurv`
  - `exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_factor0_of_dvd_and_phaseCurv`
  - `exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_factor0_normalized_and_phaseCurv`
  - `exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_factor0_with_offdvd_and_phaseCurv`
  - singleton 版:
    - `..._boundaryCore_factor0_and_phaseCurv`
    - `..._boundaryCore_local0_and_phaseCurv`
    - `..._boundaryDiffPow_local0_and_phaseCurv`
    - `..._boundaryDiffPow_factor0_and_phaseCurv`
- 供給パターン v1（暫定）:
  - 解析仮定版:
    `hcurv_lift` / `hcurv_local0` を仮定として直接入力する
  - 計算補題版:
    `hopcPrimeContributionSum = 0` 側は局所 zero 補題から再利用し、
    曲率側のみ `phaseCurv ≠ 0` 補題を差し替える
  - provider 版:
    `BoundaryInsertLocalLiftProvider` + `BoundaryInsertPhaseCurvProvider` を合成する
- 命名規約（暫定）:
  - split 入力は `..._of_local_split_and_phaseCurv`
  - singleton 入力は `..._singleton_..._of_local_and_phaseCurv`
  - provider 入力は `..._of_provider_and_phaseCurvProvider`
- 残タスク:
  - なし（以後の拡張は OP-001 系の研究タスクとして管理）
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
   - `DkMath/RH/docs/HOPC-RH-Glossary.md` に語彙を追加
3. CFBRC 連携 API/bridge が増減したか
   - `DkMath/RH/docs/RH-CFBRC-Discussion.md` の
     `Implementation Bridge` / `Bridge Usage` を更新
4. フェーズ状態や次段計画が変わったか
   - `DkMath/RH/docs/HOPC-RH-Roadmap.md` のフェーズ状態を更新
   - `DkMath/RH/docs/HOPC-RH-OpenProblems.md` の優先度・状態を更新
5. すべての作業で履歴を記録したか
   - `DkMath/RH/docs/RH_Implements_History-02.md` にテンプレート形式で追記

## 参照

- 方針: `HOPC-RH.txt`
- ロードマップ: `HOPC-RH-Roadmap.md`
- 用語集: `HOPC-RH-Glossary.md`
- 議論: `RH-CFBRC-Discussion.md`
- 実装履歴: `RH_Implements_History-02.md`
