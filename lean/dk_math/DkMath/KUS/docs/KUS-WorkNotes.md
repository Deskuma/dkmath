# KUS Work Notes

status: 作業中 - phase-05: scale-monoid compatibility

## 課題

- [x] KUS の最小依存型 `US`, `KUS` を Lean で定義する
- [x] `Nat -> KUS` 埋め込みと `KUS -> Nat` forget を導入する
- [x] `extract : KUS -> US` を通常除法と分離して導入する
- [x] 最小 round-trip 定理を追加する
- [x] 固定 fiber 上の可換モノイド的構造を設計する
- [x] `Scale` と unit transport の仕様を定める
- [x] toy blueprint による最小使用例を追加する
- [x] `Scale` と `Monoid` の整合補題を最小追加する

## 状況タスク

- 完了条件（phase-05）
  - [x] `DkMath/KUS/Unit.lean` が `US` を提供する
  - [x] `DkMath/KUS/Core.lean` が `KUS`, `mkWith`, `zeroState` を提供する
  - [x] `DkMath/KUS/NatEmbed.lean` が `ofNat`, `toNat` を提供する
  - [x] `DkMath/KUS/Extract.lean` が `extract` を提供する
  - [x] `DkMath/KUS/RoundTrip.lean` が最小往復定理を提供する
  - [x] 固定 fiber の演算 API が確定する
  - [x] `DkMath/KUS/Scale.lean` が `ScaleSpec` と最小 transport API を提供する
  - [x] `DkMath/KUS/Examples.lean` が toy 使用例を提供する
  - [x] `Scale` と fixed fiber の整合補題が `Scale.lean` にある

## 計画

- 直近の主戦場:
  - transport 後 fiber 型の見直し方針を決める
- 直近の設計候補:
  - `Fiber := Nat` のまま進める場合の利点/制約を docs に分離記録する
  - 例示モジュールを肥大化させず、証明用の最小例に限定する
  - phase-06 では設計比較（subtype fiber への回帰可能性）を先に文書化する
- 非目標（phase-01 ではやらない）:
  - `Div` の導入
  - `K : ℚ`, `ℝ`, 一般 carrier への拡張
  - `Scale` の実装

## 実装メモ

- `US` を先に独立させたことで、README の `(U, S_U)` を `extract` の戻り値として明示できる形になった。
- `KUS` は `coeff : Nat` と support の従属対であり、零状態は「係数が 0 になった support 保持状態」として `zeroState` に切り出した。
- `ofNat (extract x) (toNat x) = x` を最小の再構成定理として置き、観測側と構造保持側の分離を Lean 上で固定した。
- phase-02 では `Fiber support := {x : KUS // extract x = support}` を導入し、固定 support 上で `Nat` 係数と同型な `AddCommMonoid` を与えた。
- phase-03 では `ScaleSpec` により、`US` / `KUS` へ unit transport を与える最小 API を追加し、係数保存と extract 整合を補題で固定した。
- phase-04 では `Examples.lean` を追加し、toy blueprint 上で `KUS` / `Fiber` / `ScaleSpec` の最小利用例を固定した。
- phase-05 では `Scale.lean` に fixed fiber 整合補題を追加し、`Scale` と `Monoid` の接続を観測係数レベルで固定した。

## 作業ログ

### 2026-03-14 phase-01 最小核の実装

- 対象:
  - `lean/dk_math/DkMath/KUS.lean`
  - `lean/dk_math/DkMath/KUS/Unit.lean`
  - `lean/dk_math/DkMath/KUS/Blueprint.lean`
  - `lean/dk_math/DkMath/KUS/Core.lean`
  - `lean/dk_math/DkMath/KUS/NatEmbed.lean`
  - `lean/dk_math/DkMath/KUS/Extract.lean`
  - `lean/dk_math/DkMath/KUS/RoundTrip.lean`
- 内容:
  1. README の世界観のうち、`Nat` 係数・support 保持・extract 分離に絞って最小 Lean 核を追加した
  2. `US` を構造保持側、`KUS` を観測係数付き状態として分け、`zeroState`, `ofNat`, `toNat`, `extract` を整えた
  3. round-trip は `Nat -> KUS -> Nat` と `KUS -> extract -> ofNat` の両側で最小形を追加した
- 次の予定:
  - 固定 fiber 上の演算型を `Monoid.lean` として切り出す
  - `README` の planned modules と実装済みモジュールの差分を別ドキュメントで埋める

### 2026-03-14 phase-01 ビルド確認

- 対象:
  - `cd lean/dk_math && lake build DkMath.KUS`
  - `cd lean/dk_math && lake build DkMath`
- 内容:
  1. `DkMath.KUS` はビルド通過を確認した
  2. root の `DkMath` に import を追加した状態でも全体ビルドで破綻しないことを確認した
  3. 既存 repo 由来の `sorry` warning は残るが、今回追加した KUS 群はエラーなしで接続できた
- 次の予定:
  - fixed support 上の加法構造を `Monoid.lean` として導入する
  - linter の軽微な style warning を、次回の小修正タイミングでまとめて掃除する

### 2026-03-14 phase-02 固定 fiber 加法モノイド

- 対象:
  - `lean/dk_math/DkMath/KUS/Monoid.lean`
  - `lean/dk_math/DkMath/KUS.lean`
- 内容:
  1. `Fiber support := Nat` として fixed support の係数層を最小実装した
  2. `Fiber.toKUS` / `Fiber.toNat` を導入し、固定 fiber と KUS 本体の接続 API を整えた
  3. `Fiber` 上に `Zero`, `Add`, `AddCommMonoid` instance を追加し、加法構造を固定 support 上で確立した
  4. 入口 `DkMath/KUS.lean` で `Monoid.lean` を import して公開 API へ接続した
- 次の予定:
  - `Scale.lean` の仕様を docs で先に固定する
  - `Examples.lean` で固定 fiber 演算の toy 例を最小追加する

### 2026-03-14 phase-02 ビルド確認（lean-build.sh）

- 対象:
  - `cd lean/dk_math && ./lean-build.sh DkMath.KUS`
  - `cd lean/dk_math && ./lean-build.sh DkMath`
- 内容:
  1. `DkMath.KUS` は build succeeded を確認した
  2. root の `DkMath` でも build succeeded を確認し、KUS phase-02 の接続が全体で有効であることを確認した
  3. 全体ビルドで出る warning は既存 repo 由来の `sorry` 群が中心で、今回追加分に新規エラーはない
- 次の予定:
  - `Scale` 仕様の文書化を先行し、phase-03 の実装境界を固定する

### 2026-03-14 phase-03 Scale transport 仕様と実装

- 対象:
  - `lean/dk_math/DkMath/KUS/Scale.lean`
  - `lean/dk_math/DkMath/KUS.lean`
  - `lean/dk_math/DkMath/KUS/docs/KUS-ScaleSpec.md`
- 内容:
  1. `ScaleSpec` を導入し、`mapUnit` と依存型 `mapBlueprint` を同時に持つ最小仕様を追加した
  2. `scaleUS` / `scaleKUS` を追加し、`toNat` 保存と `extract` 整合を補題で固定した
  3. `idScale` と `comp` を追加し、transport の単位元・合成の最小法則を追加した
  4. 入口 `DkMath/KUS.lean` で `Scale.lean` を import して公開 API へ接続した
- 次の予定:
  - `Examples.lean` で toy blueprint を導入し、`Scale` と `Monoid` の最小使用例を追加する

### 2026-03-14 phase-03 ビルド確認（lean-build.sh）

- 対象:
  - `cd lean/dk_math && ./lean-build.sh DkMath.KUS`
  - `cd lean/dk_math && ./lean-build.sh DkMath`
- 内容:
  1. `DkMath.KUS` は build succeeded を確認
  2. root `DkMath` でも build succeeded を確認
  3. `Scale.lean` の軽微な lint 警告（`simpa`/未使用変数/whitespace）は修正済み
- 次の予定:
  - phase-04 として `Examples.lean` を追加し、toy blueprint 上の `Monoid` / `Scale` 使用例を固定する

### 2026-03-14 phase-04 Examples 追加

- 対象:
  - `lean/dk_math/DkMath/KUS/Examples.lean`
  - `lean/dk_math/DkMath/KUS.lean`
- 内容:
  1. `ToyUnit := Nat`, `ToyBlueprint u := Fin (u+1)` を定義し、依存型 blueprint の最小具体例を導入した
  2. 固定 support `toySupport`、KUS 値 `toyX`、fiber 加法 `toyFiberSum` を追加した
  3. `toyScale` を追加し、`toNat` 保存と `extract` 整合を具体例で確認した
  4. 入口 `DkMath/KUS.lean` へ `Examples.lean` import を追加した
- 次の予定:
  - `Scale` と `Monoid` の整合補題を最小追加する（phase-05）

### 2026-03-14 phase-04 ビルド確認（lean-build.sh）

- 対象:
  - `cd lean/dk_math && ./lean-build.sh DkMath.KUS`
  - `cd lean/dk_math && ./lean-build.sh DkMath`
- 内容:
  1. `DkMath.KUS` は build succeeded を確認
  2. root `DkMath` でも build succeeded を確認
  3. `Examples.lean` の軽微な whitespace 警告を修正し、KUS 側の追加分は warning なしで通過
- 次の予定:
  - phase-05 で `Scale` と `Monoid` の整合補題を最小追加する

### 2026-03-14 phase-05 Scale×Monoid 整合補題

- 対象:
  - `lean/dk_math/DkMath/KUS/Scale.lean`
  - `lean/dk_math/DkMath/KUS/docs/KUS-ScaleSpec.md`
- 内容:
  1. `scaleKUS_toKUS` を追加し、scale と fixed fiber 埋め込みの整合を固定した
  2. `extract_scaleKUS_toKUS` を追加し、transport 後 support の抽出整合を固定した
  3. `toNat_scaleKUS_toKUS_add` を追加し、観測係数レベルで加法整合を固定した
- 次の予定:
  - phase-06 として、transport 後 fiber 型（Nat 別名 vs subtype）の設計比較を文書化する

### 2026-03-14 phase-05 ビルド確認（lean-build.sh）

- 対象:
  - `cd lean/dk_math && ./lean-build.sh DkMath.KUS`
  - `cd lean/dk_math && ./lean-build.sh DkMath`
- 内容:
  1. `DkMath.KUS` は build succeeded を確認
  2. root `DkMath` でも build succeeded を確認
  3. KUS 追加分の warning は解消し、全体 warning は既存 repo 由来の `sorry` 群のみ
- 次の予定:
  - phase-06 で fiber 型設計比較（Nat alias / subtype）を docs へ明示する
