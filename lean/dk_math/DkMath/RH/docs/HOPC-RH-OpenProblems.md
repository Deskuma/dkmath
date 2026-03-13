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
- 状態: 進行中（RH-N1〜N25 で API 骨格・provider 入口・実供給導線を整備済み）
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
    - `hopcPrimeLocalContribution_eq_eulerZetaFactorPhaseVelLocal_of_nonzero`
    - `hopcPrimeLocalContribution_eq_zero_of_factorPhaseVelLocal_eq_zero_of_nonzero`
    - `eulerZetaFactorPhaseVelLocal_eq_zero_of_hopcPrimeLocalContribution_eq_zero_of_nonzero`
    - `boundary_hlocal_core_of_boundaryCore_factorPhaseVelLocal_eq_zero`
    - `boundary_hfactor_core0_of_boundaryCore_local_zero`
    - `boundaryInsertLocalLiftProvider_of_boundary_dvd_and_gap_and_local_zero`
    - `boundaryInsertLocalLiftProvider_of_boundary_dvd_and_gap`
    - `boundaryInsertLocalLiftProvider_of_boundary_dvd_and_gap_of_boundaryCore_witness`
    - `boundaryInsertLocalLiftProvider_of_boundary_dvd_gap_of_boundaryCore_factor0`
    - `exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_factor0`
    - `exists_stationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_factor0`
    - `exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_local0`
    - `exists_stationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_local0`
  - README / Discussion / docs README の利用テンプレート同期（split 版 / provider 版）
- 残タスク:
  - provider 実供給補題の具体化:
    - local contribution 側から `hlocal_core` を生成する実補題
    - CFBRC 側 primitive prime existence と `hS_dvd` / `hS_gap` を接続する実補題
    - 上記実補題を使う direct existence wrapper のさらなる仮定削減
  - OP-001 の finite→infinite 接続で再利用できる仮定パッケージ化
- 優先度: 高（継続）

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
