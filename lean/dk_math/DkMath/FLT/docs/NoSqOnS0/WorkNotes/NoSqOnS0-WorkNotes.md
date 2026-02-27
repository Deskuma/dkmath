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

### 2026-02-27 phase-13 着手（Bridge モジュール実装）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/TriominoMainBridge.lean`（新規）
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 実装内容:
  1. `TriominoHasNoSqFamily` / `TriominoHasNonLiftableFamily` を bridge 側で型別名化
  2. `FLT_d3_by_padicValNat_via_triominoHasNoSqFamily_coprimeSupport_direct`
  3. `FLT_d3_by_padicValNat_via_triominoHasNonLiftableFamily_coprimeSupport_direct`
  4. 上記 2 定理は `Main` の既存接続口（line 772 / 788）へ委譲
- 接続方針への適合:
  - `Main.lean` は無変更（依存方向固定）。
  - `TriominoFLT` と `Main` の同時 import は bridge モジュールに限定。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.TriominoMainBridge`
  - 結果: 成功（`TriominoFLT` の既存 warning / `sorry` 1件は継続）。

### 2026-02-27 phase-13 次ステップ（接続完了まで）

- 次に実施すること:
  1. `TriominoFLT` 側で `FLT_highExponent_core_pending` を完了し、`hprimeFLT` 供給を構成
  2. bridge の入力 `TriominoHasNoSqFamily` か `TriominoHasNonLiftableFamily` を
     Triomino 定理群から具体的に生成する補題を追加
  3. bridge 経由で `FLT_d3_by_padicValNat...` の end-to-end 呼び出し例を 1 本作成
- 完了判定:
  1. `TriominoFLT.lean` の `sorry` が 0
  2. `TriominoMainBridge.lean` から `Main` 入口へ具体供給で到達する定理がある
  3. `lake build DkMath.FLT.TriominoMainBridge DkMath.CosmicFormula.TriominoFLT DkMath.FLT.Main` が通る

### 2026-02-27 phase-13 継続（prime provider 受入れの確定版 API 追加）

- 変更ファイル:
  - `lean/dk_math/DkMath/CosmicFormula/TriominoFLT.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `PrimeExponentFLTProvider` / `GlobalPrimeExponentFLTProvider`
  2. `primeExponentFLTProvider_of_global`
  3. `FLT_highExponent_core_of_provider`（`sorry` なし）
  4. `FLT_from_tromino_tiling_of_primeProvider`（`sorry` なし）
  5. `FLT_general_via_tromino_of_primeProvider`（`sorry` なし）
  6. `FLT_general_via_tromino_of_globalPrimeProvider`（`sorry` なし）
- 意図:
  - 既存の `..._pending`（単一 `sorry`）を残しつつ、
    供給があれば即座に使える確定版 API を先に公開。
  - bridge 側や外部モジュールから段階的に接続しやすい形へ整理。
- 現在の `sorry` 状態:
  - `TriominoFLT.lean` の `sorry` は引き続き `FLT_highExponent_core_pending` の1件のみ。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.CosmicFormula.TriominoFLT DkMath.FLT.TriominoMainBridge`
  - 結果: 成功。

### 2026-02-27 phase-13 継続（provider 受入れ補題の強化 + bridge 公開）

- 変更ファイル:
  - `lean/dk_math/DkMath/CosmicFormula/TriominoFLT.lean`
  - `lean/dk_math/DkMath/FLT/TriominoMainBridge.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容（TriominoFLT）:
  1. `FLT_highExponent_core_pending_of_primeProvider`
  2. `FLT_highExponent_core_pending_of_globalProvider`
- 追加内容（Bridge）:
  1. `FLT_general_via_triominoGlobalProvider`
     - `DkMath.FLT_general_via_tromino_of_globalPrimeProvider` への委譲
     - Main 接続口とは独立した「確定版 API の公開入口」
- 意図:
  - `pending` 系と `provider` 系の対応関係を明示し、置換時の見通しを改善。
  - bridge 側からも global provider 版の到達可能性を公開し、接続実験をしやすくする。
- 現在の `sorry` 状態:
  - `TriominoFLT.lean` は `FLT_highExponent_core_pending` の1件のみ。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.CosmicFormula.TriominoFLT DkMath.FLT.TriominoMainBridge`
  - 結果: 成功。

### 2026-02-27 phase-13 継続（TriominoPrimeProvider モジュール追加）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/TriominoPrimeProvider.lean`（新規）
  - `lean/dk_math/DkMath/FLT.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `TriominoPrimeProvider := GlobalPrimeExponentFLTProvider`
  2. `FLT_general_via_triominoPrimeProvider`
  3. `FLT_d3_via_triominoPrimeProvider`
- 意図:
  - `sorry` 本体は後回しのまま、
    「provider 入力 -> Triomino bridge 経由で FLT 結論」の使用入口を独立モジュールとして固定。
  - 外部実験・検証時に bridge/本体へ直接依存せず呼び出せる導線を確保。
- 併せて実施:
  - `DkMath/FLT.lean` に `import DkMath.FLT.TriominoPrimeProvider` を追加（公開面へ反映）。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.TriominoPrimeProvider DkMath.FLT`
  - 結果: 成功（既存 warning / `TriominoFLT` の `sorry` 1件は継続）。

### 2026-02-27 phase-13 継続（`FermatLastTheorem` 仮定から provider を生成）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/TriominoPrimeProvider.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `triominoPrimeProvider_of_fermatLastTheorem`
  2. `triominoPrimeProvider_of_oddPrimes`
     - `FermatLastTheorem.of_odd_primes` 経由
  3. `FLT_general_via_fermatLastTheorem`
  4. `FLT_d3_via_fermatLastTheorem`
- 意図:
  - 供給モジュールを「ただの alias」から「仮定 -> provider 生成器」へ拡張。
  - 将来の独立証明置換前でも、仮定を与えて end-to-end を動かせる実験導線を強化。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.TriominoPrimeProvider DkMath.FLT.TriominoMainBridge`
  - 結果: 成功（`TriominoFLT` の `sorry` 1件は継続）。

## 作業ログ

### 2026-02-27 phase-13 継続（TriominoPrimeProvider の入口拡張）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/TriominoPrimeProvider.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `FLT_general_via_oddPrimes`
  2. `FLT_d3_via_oddPrimes`
  3. `FLT_d3_by_padicValNat_via_triominoPrimeProvider_coprimeSupport_direct`
  4. `FLT_d3_by_padicValNat_via_fermatLastTheorem_coprimeSupport_direct`
  5. `FLT_d3_by_padicValNat_via_oddPrimes_coprimeSupport_direct`
- 意図:
  - `TriominoPrimeProvider` を「general/d3 結論」だけでなく、
    `Main` で使っている coprime-support 形の引数セットからも直接呼べる API に拡張。
  - 研究側で仮定供給（`FermatLastTheorem` / odd-primes）を切り替えても、
    呼び出し側の形をほぼ固定できるようにした。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.TriominoPrimeProvider`
  - 結果: 成功（既存 warning: `TriominoFLT` の `sorry` 1件は継続）。
