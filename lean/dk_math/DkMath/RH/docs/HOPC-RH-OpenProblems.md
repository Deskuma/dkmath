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
    RH 側 HOPC API をつなぐ「具体的命題」が未実装。
- 目標成果:
  - CFBRC 側条件を受けて RH 側停留判定へ落ちる bridge 補題（最低 1 本）
- 優先度: 高

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

## 参照

- 方針: `HOPC-RH.txt`
- ロードマップ: `HOPC-RH-Roadmap.md`
- 用語集: `HOPC-RH-Glossary.md`
- 議論: `RH-CFBRC-Discussion.md`
- 実装履歴: `RH_Implements_History.md`
