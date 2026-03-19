# ABC 予想形式化ロードマップ

このドキュメントは、`lean/dk_math/DkMath/ABC/` 内のファイル群の役割と、証明の「流れ」を整理するためのものです。

## 1. 主要ファイルの役割

- `ABC.lean` / `ABC#Research.lean`
  - ABC 予想の主要定義・公開 API をまとめるエントリポイント（仮）
  - まだ内容が薄いので、今後 `ABCXXX.lean` のコア論理を整理して統合する計画

- `ABC00x.lean` 系
  - 番号付けされたモジュール群。各ファイルは以下の役割を持つ。
    - `ABC002.lean` など: 密度議論や極限議論を扱う
    - `ABC014.lean` など: 解析的評価（log/質の上限）を扱う

- `ABCError.lean`
  - 計算や定義上の整合性チェックを行う補助モジュール

- `ABCSolvedProofSamples.lean`, `ABCWorking.lean`
  - 途中証明・検証用のサンプル集。特定の仮定下での証明や反例検証など。

- `Basic.lean`, `Core.lean`, `Rad.lean`, `RatioBound.lean`, `Square.lean`, `Triple.lean`
  - ABC 予想で必要になる数論的・解析的補題をまとめた共通ライブラリ的モジュール。

## 2. 進捗の流れ（暫定）

1. **定義フェーズ**
   - `Rad`（rad関数）の定義
   - `quality`（質）の定義
   - `abc_conjecture` / `weak_abc_conjecture` の定式化

2. **局所評価フェーズ**
   - `quality` の上界評価（`quality_le_of_*` 系）
   - log 変換・素因子の和への展開
   - `adjBadCount` や `adj_quality_density_one` などの密度議論

3. **全体戦略フェーズ**
   - `abc_quality_le_of_not_bad` などの統合的主張
   - ε の引き下げや有限例の扱い

4. **未完フェーズ（TODO）**
   - `sorry` が残る部分の完成
   - 証明の整備・モジュール分割の最適化
   - 「証明全体のパイプライン」を把握しやすくするためのドキュメント整備

## 3. 追跡すべきポイント

- `sorry` が残っている定理・補題
- 依存関係が複雑になりがちなモジュール（例: `Core.lean` → `ABC014.lean` など）
- 解析的推論と数論的推論の境界（log の扱い、密度議論、誤差項）

---

> このドキュメントは今後、各ファイルの「要約」「キーレマ」「依存関係図」を追加していく予定です。
> 追加したい内容や見たい観点があれば教えてください。
