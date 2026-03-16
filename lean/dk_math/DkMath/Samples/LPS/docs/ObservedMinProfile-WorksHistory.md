# Observed Minimum Profile Works History

## 運用方針

- このファイルは `ObservedMinProfile` 系作業の履歴を時系列で積み上げる。
- 以後は**作業ごとに追記**し、過去記録は削除せず残す。
- 1 エントリは「目的 / 変更 / 検証 / 次アクション」を最小単位とする。

## 履歴

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
