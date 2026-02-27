# No Square on S0 Work Notes

status: 作業中 - phase-13: 完全証明への道（）

## Index

※以前の作業は以下、アーカイブログへ移しました。

[NoSqOnS0: phase-01](NoSqOnS0-WorkNotes-phase-01.md)
[NoSqOnS0: phase-02](NoSqOnS0-WorkNotes-phase-02.md)
[NoSqOnS0: phase-03](NoSqOnS0-WorkNotes-phase-03.md)
[NoSqOnS0: phase-04](NoSqOnS0-WorkNotes-phase-04.md)
[NoSqOnS0: phase-05](NoSqOnS0-WorkNotes-phase-05.md)
[NoSqOnS0: phase-06](NoSqOnS0-WorkNotes-phase-06.md)
[NoSqOnS0: phase-07](NoSqOnS0-WorkNotes-phase-07.md)
[NoSqOnS0: phase-08](NoSqOnS0-WorkNotes-phase-08.md)
[NoSqOnS0: phase-09](NoSqOnS0-WorkNotes-phase-09.md)
[NoSqOnS0: phase-10](NoSqOnS0-WorkNotes-phase-10.md)
[NoSqOnS0: phase-11](NoSqOnS0-WorkNotes-phase-11.md)
[NoSqOnS0: phase-12](NoSqOnS0-WorkNotes-phase-12.md)

## 課題

- [ ] 仮定の証明
  - [ ] `NonLiftableS0` の証明（下降法）
  - [x] ただし、`GEisensteinBridge` の `descent` インターフェースは実装済み。

## 状況タスク

- 完了条件（DoD）:
  - [ ] 1. `TriominoFLT.lean` に `sorry` がない。
  - [ ] 2. `FLT_highExponent_core_pending` が実装済み（または不要化）。
  - [ ] 3. `cd lean/dk_math && lake build DkMath.CosmicFormula.TriominoFLT` が成功。
  - [ ] 4. 暫定依存の残有無をコメントとログに明示。
- 受け入れ条件:
  - [ ] 1. Bridge から `Main` の triomino 接続口へ実際に到達すること。
  - [ ] 2. `Main` 側既存 API（line 772 / 788）を変更せず接続できること。

## 計画

### 2026-02-26 ここからの実装計画（phase-13 以降）

- 現在地:
  1. `TriominoFLT.lean` の `sorry` は `FLT_highExponent_core_pending` の1件に集約済み。
  2. 未解決の実体は「`hprimeFLT`（`p ≠ 2,3` 素数指数 FLT 供給）」の構成。
  3. `FLT3/4` は暫定ブリッジとして利用中（将来除去方針は維持）。

- 実装方針（順序固定）:
  1. **インターフェース固定**
     - `hprimeFLT` の要求形（`∀ p, Prime p → p∣n → p≠2 → p≠3 → FermatLastTheoremFor p`）を
       高指数核の唯一の入口として維持。
     - 目的: 以降の実装を「供給構築」に限定し、核本体の再変更を避ける。
  2. **供給の段階実装（仮説分解）**
     - `hprimeFLT` を一気に作らず、次の局所補題へ分割:
       - (a) 素数指数 `p` の場合の幾何条件（色不変量/タイル不可能性）
       - (b) (a) から `FermatLastTheoremFor p` への接続
     - 目的: 各補題の責務を分離し、失敗箇所を局所化。
  3. **最終接続**
     - 分割補題を束ねて `hprimeFLT` を定義し、`FLT_highExponent_core_pending` を置換。
     - 目的: `TriominoFLT.lean` の `sorry` をゼロ化。
  4. **暫定依存の整理**
     - 高指数側が閉じた後、`fermatLastTheoremThree/Four` の暫定参照を
       Triomino/Cosmic 独立証明に順次置換。

- 完了条件（DoD）:
  1. `TriominoFLT.lean` に `sorry` がない。
  2. `FLT_highExponent_core_pending` が実装済み（または不要化）。
  3. `cd lean/dk_math && lake build DkMath.CosmicFormula.TriominoFLT` が成功。
  4. 暫定依存の残有無をコメントとログに明示。

### 2026-02-26 Main 接続計画（Triomino -> FLT.Main）

- 現状認識:
  1. `TriominoFLT.lean` は `FLT.Main` から import されていない（直接参照なし）。
  2. `Main` 側には接続口が既に存在:
     - `FLT_d3_by_padicValNat_of_triominoHasNoSqFamily_coprimeSupport_direct`
       (`DkMath/FLT/Main.lean:772`)
     - `FLT_d3_by_padicValNat_of_triominoHasNonLiftableFamily_coprimeSupport_direct`
       (`DkMath/FLT/Main.lean:788`)

- 接続設計（実装予定）:
  1. `TriominoFLT` 側でまず `hprimeFLT` 供給を完成し、`hasNoSq` か `hasNonLiftable` の family 形へ落とす。
  2. 新規アダプタモジュール（例: `DkMath/FLT/TriominoMainBridge.lean`）を作成し、
     `import DkMath.CosmicFormula.TriominoFLT` と `import DkMath.FLT.Main` を同時に読み込む。
  3. 同モジュール内で
     - `triominoHasNoSqFamily`（または `triominoHasNonLiftableFamily`）
     - `FLT_d3_by_padicValNat_via_triomino...`（`Main` の接続口を呼ぶ）
     を定理として公開する。
  4. `Main.lean` 自体には Triomino import を追加しない（依存方向を固定し、循環と肥大化を回避）。

- 実装順:
  1. `TriominoFLT` の `sorry` ゼロ化（高指数核の供給完成）
  2. `TriominoMainBridge` 追加
  3. `lake build` で `TriominoFLT + Main + Bridge` 同時確認

- 受け入れ条件:
  1. Bridge から `Main` の triomino 接続口へ実際に到達すること。
  2. `Main` 側既存 API（line 772 / 788）を変更せず接続できること。

## 作業ログ
