# KUS Work Notes

status: 作業中 - phase-01: minimal dependent core

## 課題

- [x] KUS の最小依存型 `US`, `KUS` を Lean で定義する
- [x] `Nat -> KUS` 埋め込みと `KUS -> Nat` forget を導入する
- [x] `extract : KUS -> US` を通常除法と分離して導入する
- [x] 最小 round-trip 定理を追加する
- [ ] 固定 fiber 上の可換モノイド的構造を設計する
- [ ] `Scale` と unit transport の仕様を定める

## 状況タスク

- 完了条件（phase-01）
  - [x] `DkMath/KUS/Unit.lean` が `US` を提供する
  - [x] `DkMath/KUS/Core.lean` が `KUS`, `mkWith`, `zeroState` を提供する
  - [x] `DkMath/KUS/NatEmbed.lean` が `ofNat`, `toNat` を提供する
  - [x] `DkMath/KUS/Extract.lean` が `extract` を提供する
  - [x] `DkMath/KUS/RoundTrip.lean` が最小往復定理を提供する
  - [ ] 固定 fiber の演算 API が確定する

## 計画

- 直近の主戦場:
  - fixed support 上の演算をどう切るかを決める
- 直近の設計候補:
  - `US` を support と見なし、その上で `Nat` 係数層として fiber を定義する
  - 加法は係数加算、零元は `zeroState`、必要なら `support` ごとの subobject として型を切る
  - blueprint が一致する場合に限る大域演算を入れるかは後回しにする
- 非目標（phase-01 ではやらない）:
  - `Div` の導入
  - `K : ℚ`, `ℝ`, 一般 carrier への拡張
  - `Scale` の実装

## 実装メモ

- `US` を先に独立させたことで、README の `(U, S_U)` を `extract` の戻り値として明示できる形になった。
- `KUS` は `coeff : Nat` と support の従属対であり、零状態は「係数が 0 になった support 保持状態」として `zeroState` に切り出した。
- `ofNat (extract x) (toNat x) = x` を最小の再構成定理として置き、観測側と構造保持側の分離を Lean 上で固定した。

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
