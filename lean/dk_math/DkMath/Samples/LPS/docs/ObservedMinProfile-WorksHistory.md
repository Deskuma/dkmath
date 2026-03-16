# Observed Minimum Profile Works History

## 運用方針

- このファイルは `ObservedMinProfile` 系作業の履歴を時系列で積み上げる。
- 以後は**作業ごとに追記**し、過去記録は削除せず残す。
- 1 エントリは「目的 / 変更 / 検証 / 次アクション」を最小単位とする。

## 履歴

### 2026-03-17: 交点地形（profile map）分析の追記

- **目的**
  - 「標本がある」状態から一歩進め、`ObservedMinOne ↔ ObservedMinTwo` の境界が
    どこに現れるかを研究ノートで読める形にする。

- **変更**
  - `ObservedMinProfile-ResearchNote.md` に
    - 「交点地形メモ（profile map）」節を追加。
    - 交点を 3 層（PowerSwap / same Big / profile 境界）で整理。
    - 固定 Big で `B ↦ label(Big - B)` として観測する枠組みを明記。
    - `Big = 216, d = 3` の境界表（Body, residual, profile）を追記。

- **検証**
  - 文書更新のみ（Lean コード変更なし）。

- **次アクション候補**
  - 同形式の境界表を `Big = 64`, `Big = 125` にも追加。
  - 必要なら小スクリプトで `Body` 掃引表を自動生成し、ノートへ転記。

### 2026-03-17: 現状分析の固定と生成テンプレ明文化

- **目的**
  - 現状分析の重要点を `ResearchNote` に固定し、次作業へ使える Lean 対応テンプレを明文化する。

- **変更**
  - `ObservedMinProfile-ResearchNote.md` に
    - 「現状分析（2026-03-17）」節を追記。
    - `d = 3` 独立 3 標本再現の重要性、`d = 2` 補足、強み・未確定点を整理。
    - 「生成テンプレ（Lean 定理名対応）」節を追加し、
      `candidate*` 系定理の最小構成手順を固定。

- **検証**
  - 文書更新のみ（Lean コード変更なし）。

- **次アクション候補**
  - テンプレに沿って `d = 3` の 4 標本目を追加する。
  - もしくは `d = 2` 側で 2 標本目を追加し、次数横断の再現性を厚くする。

### 2026-03-17: 初回作業履歴（現状までの概要）

- **目的**
  - LPS サンプル群で observed minimum profile 分岐の実験基盤を整備する。

- **変更**
  - `BigFamilyInt.lean` を `Samples/LPS` 配下に新設。
  - `BigFamilyExamples.lean` を新設し、観測標本を追加。
  - `ObservedMinOne/Two` を局所定義として導入（実験段階のため局所維持）。
  - 立方 `d = 3` で独立 3 標本を束ねる総括定理
    - `cube_observed_min_split_reproduced_three_samples`
    を追加。
  - `docs/ObservedMinProfile-ResearchNote.md` を新設し、
    事実確認と標本生成原理（短メモ）を整理。
  - `README.md` に `docs` ノートへの導線を追加。

- **検証**
  - `./lean-build.sh DkMath.Samples.LPS.BigFamilyExamples` 成功。
  - `./lean-build.sh DkMath.Samples` 成功。

- **次アクション候補**
  - 新規標本追加（`d = 3` 継続）または生成原理節の精密化。
  - 必要に応じて `ObservedMin` の共通 API 昇格を再評価。
