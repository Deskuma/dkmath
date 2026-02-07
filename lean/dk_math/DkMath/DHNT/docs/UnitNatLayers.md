# Unit/Nat 層（UnitNatLayers）ドキュメント

目的

- DHNT の観点で「Unit 層（連続・単位・回転）」と「Nat 層（離散・反復・増分）」を区別し、
  それらを結ぶ抽象的な `Bridge` を導入した実装のまとめ。

実装ファイル

- Lean 実装: [UnitNatLayers.lean](../UnitNatLayers.lean#L31)
  - `Progress` / `HasCycle` / `Mixable`（Nat 層の基礎述語）
  - 抽象クラス `Bridge`（`phi : Unit → Nat`）
  - `MixableViaBridge` と `not_mixable_via_bridge_of_progress`
  - 具体的な Bridge 実装例：`piBridge`, `floorBridge`, `scale10Bridge`
  - CI 用の `example` ブロックを含む（`T := succ`, `I := id` を用いた簡易テスト）

設計要点

- 層の分離:
  - `Unit` 層の恒等式（例: オイラーの公式）は直接 `Nat` 層の定理を破らない。
  - `Unit`→`Nat` の射影は必ず明示的な `Bridge`（`phi`）を通す。
- `Progress`（毎ステップで不変量が少なくとも 1 増える）を仮定すると、
  その同一の遷移系内で非自明閉路は存在しない（`no_nontrivial_cycle_of_ge_one`）。
  これを元に `Mixable`／`MixableViaBridge` の否定を示す。

具体例

- `piBridge`:
  - 最小実装で常に `1` を返す橋（`phi u := 1`）。`Real.pi` を `pi` フィールドに持つ。
- `floorBridge`:
  - `phi u := floor(u.val) + 1` により Unit の大きさを整数化して量子化する例。
- `scale10Bridge`:
  - `phi u := floor(u.val * 10) + 1` により小数第一位を用いた粗い量子化を行う例。

利用方法

1. 参照（Lean 側）:

   ```lean
   import DkMath.DHNT.UnitNatLayers
   ```

2. 任意の `T : State → State` と `I : State → Nat` があり `Progress T I` を示せば、
   任意の `B : Bridge` に対して `¬ MixableViaBridge T I B` が導ける。

ビルド

- 通常のライブラリビルドで確認済み:

  ```bash
  cd lean/dk_math
  lake build
  ```
