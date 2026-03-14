# KUS Fiber Design Options (phase-06)

この文書は、fixed fiber の型を

- `Fiber support := Nat`（現行）
- `Fiber support := {x : KUS // extract x = support}`（subtype）

のどちらで運用するかを比較し、採用方針を明文化する。

## 結論（phase-06）

- 当面は **`Fiber := Nat` を継続採用** する。
- 理由は、phase-01〜05 の目的（最小核・Scale・整合補題）に対して実装負荷が最小で、
  補題の見通しとビルド安定性が高いから。
- subtype 版は将来の拡張候補として保持し、必要条件が満たされた時点で再評価する。

## 比較

### 1. `Fiber := Nat`（現行）

**長所**

- 係数層の演算が `Nat` にそのまま還元され、証明が短い。
- `Monoid` と `Scale` の整合を `toNat` レベルで素直に書ける。
- ビルド・リファクタのコストが低い。

**短所**

- fiber 要素そのものは `support` 証明を持たないため、
  「要素自体が本当にその fiber に属する」情報は `toKUS` 経由で外在化される。
- transport 後 fiber を型レベルで追跡する表現力は弱い。

### 2. subtype fiber

**長所**

- `extract x = support` を型で保持でき、所属が内在化される。
- transport / pullback 的な設計へ拡張しやすい。

**短所**

- 補題・instance が重くなりやすく、初期段階では証明コストが高い。
- 既存の最小 API を大量に置換する必要がある。

## 移行トリガー（Nat 版から subtype 版へ）

以下のいずれかが必要になった時点で再評価する。

1. fiber 要素の所属証明を、API 利用側で直接パターンマッチしたい
2. scale 後 fiber を、型レベルで厳密に追跡する必要が出る
3. `toNat` レベルの外在化では不十分な定理（依存等式中心）が主戦場になる

## 実務ルール（phase-06 時点）

- fiber 演算は引き続き `Nat` レベルで実装する
- KUS 本体へ戻す入口は `Fiber.toKUS` に統一する
- scale との整合は `Scale.lean` の補題群へ集約する

## 次作業

1. `Examples.lean` に phase-05 補題の利用例を 1 つ追加（phase-07）
2. 必要なら subtype 版の試作を別 docs に設計メモとして切り出す
