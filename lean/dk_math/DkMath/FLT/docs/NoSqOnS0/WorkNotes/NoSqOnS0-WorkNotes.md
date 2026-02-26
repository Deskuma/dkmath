# No Square on S0 Work Notes

status: 作業中 - phase-11: 完全証明への道（下降法で `NonLiftableS0` を実証する）

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

## 課題

- [ ] 仮定の証明
  - [ ] `NonLiftableS0` の証明（下降法）
  - [x] ただし、`GEisensteinBridge` の `descent` インターフェースは実装済み。

## 状況タスク

**現状評価**

- [ ] 3. 未充足の本丸は `NonLiftableS0` の自動生成です。  
  今は `hNonLift` を入力で受けるか、`NoSq` から逆算しています。

**phase-10 攻略法（本命）**

- [ ] 3. 上の供給を下降法（または同等の反例縮小）で埋める。  
  `GEisensteinBridge` はまだ導入段階（`lean/dk_math/DkMath/FLT/GEisensteinBridge.lean`）なので、ここが最大工数です。
- [ ] 4. 最終入口を `NoSqBaseInput` 一発に統合。  
  `lean/dk_math/DkMath/FLT/Main.lean:334` を最終公開入口にし、他はラッパーに寄せる。

**保険ルート**

- [ ] 1. 「まず完全定理を公開したい」なら、既存 `Basic` 系（`FLT_case_3`, `FLT`）への橋定理を先に立てる。  
- [ ] 2. その後に phase-11 本命（下降法）を段階置換する。

この方針なら、短期で前進しつつ、最終的に“仮定なし NonLiftable”へ到達できます。  

## 状況

### D.1. ルート1. 下降法で `NonLiftableS0` を実証する

ファイル内の用語で言えば、欲しいのはこれ：

\[
\text{PrimitiveOnS0}(c,b,q)\ \Rightarrow\ \neg(q^2 \mid S0_nat(c,b))
\]

これを “最小反例” 仮定のもとで示し、もし \(q^2\mid S0\) なら **より小さい反例** を構成して矛盾、が王道じゃ。

Lean 的には、だいたいこういう形の核が要る：

```lean
-- 最小の反例 (a,b,c) を仮定し、
-- q^2 | S0 から、より小さい (a',b',c') を構成して矛盾
theorem nonLiftableS0_of_minCounterexample
  {a b c q : ℕ} :
  -- (1) a^3 + b^3 = c^3, gcd 条件, 最小性
  -- (2) PrimitiveOnS0 c b q
  -- (3) q^2 ∣ S0_nat c b
  False := by
  ...
```

この “下降ステップの構成” には、結局 **アイゼンシュタイン整数 \(\mathbb{Z}[\omega]\)**（あるいは同等の因数分解構造）が効く。
ぬしの `GEisensteinBridge` 構想は、まさにここに刺さる。

---

## 資料

[議事録](../../discussion-infinite-descent.md)

## 作業ログ

### 2026-02-25 phase-11 方針固め（議事録反映）

- 読了資料:
  - `lean/dk_math/DkMath/FLT/docs/discussion-infinite-descent.md`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 現在の到達点:
  - `GEisensteinBridge` に下降フレーム（`measure` / `step` / `step_pred`）と停止到達 API は実装済み。
  - `Main` への接続（`..._of_descentClassify_...`, `..._of_GEisensteinCore_...`）は実装済み。
  - ただし `DescentClassifyImpossibleOnPrimitive` の中身は、まだ `NoSq` 系供給に依存している。
- phase-11 の本丸（未充足）:
  - `PrimitiveOnS0 c b q -> ¬ q^2 ∣ S0_nat c b` を、外部 `hNonLift` 仮定なしで供給する下降法コアを作る。
- 実装方針（確定）:
  1. `GEisensteinBridge` に「最小反例/測度」インターフェースを追加し、`measure` の厳密減少を証明可能形で固定する。
  2. `PrimitiveOnS0` を保持する状態から、`q^2 ∣ S0` 仮定時により小さい候補へ落とす `step` 補題群を分離実装する。
  3. 最小反例矛盾 (`wellFounded` / 最小元原理) から `DescentClassifyImpossibleOnPrimitive` を生成する。
  4. 既存 `nonLiftableS0_family_of_descentClassify` に接続し、`Main` 公開入口は差し替えなしで完成させる。
- 直近の着手点（次コミット）:
  - `GEisensteinBridge.lean` に phase-11 用の state/measure スケルトン補題を追加する。
  - 既存 `primitiveSized` の `pred` 減少は「停止性 API」として残し、実体降下補題は別名前空間で段階追加する。

### 2026-02-25 phase-11 実装開始（strict descent スケルトン投入）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/GEisensteinBridge.lean`
  - `lean/dk_math/DkMath/FLT/Main.lean`
- `GEisensteinBridge` 追加:
  1. `PrimitiveSquareWitness`
  2. `PrimitiveSquareDescentStep`
  3. `not_primitiveSquareWitness_of_descentStep`（最小反例 `Nat.find` + strict 減少で矛盾）
  4. `nonLiftableS0_family_of_descentStep`
  5. `descentClassifyImpossibleOnPrimitive_of_harmonicEnvelope_descentStep`
  6. `descentClassifyImpossibleOnPrimitive_via_GEisenstein_descentStep`
- `Main` 追加入口:
  - `FLT_d3_by_padicValNat_of_harmonicEnvelope_descentStep_coprimeSupport`
  - 役割: `NoSq` を仮定せず、`PrimitiveSquareDescentStep` から `descentClassify` を生成して既存入口へ接続。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.GEisensteinBridge DkMath.FLT.Main`
  - 結果: 成功（対象2モジュール build OK）。

### 2026-02-26 phase-11 継続（descent engine 化）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/GEisensteinBridge.lean`
  - `lean/dk_math/DkMath/FLT/Main.lean`
- 追加内容:
  1. `PrimitiveSquareDescentEngine` 構造体を追加。
  2. `primitiveSquareDescentStep_of_engine` で engine -> step 条件を自動変換。
  3. `nonLiftableS0_family_of_descentEngine` を追加。
  4. `descentClassifyImpossibleOnPrimitive_of_harmonicEnvelope_descentEngine` を追加。
  5. `descentClassifyImpossibleOnPrimitive_via_GEisenstein_descentEngine` を追加。
  6. `Main` に `FLT_d3_by_padicValNat_of_harmonicEnvelope_descentEngine_coprimeSupport` を追加。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.GEisensteinBridge DkMath.FLT.Main`
  - 結果: 成功。

### 2026-02-26 phase-11 継続（NoSq 直結ルート追加）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/GEisensteinBridge.lean`
  - `lean/dk_math/DkMath/FLT/Main.lean`
- 追加内容:
  1. `NoSqOnS0_of_descentStep_coprime`
  2. `NoSqOnS0_of_descentEngine_coprime`
  3. `FLT_d3_by_padicValNat_of_descentStep_coprimeSupport_direct`
  4. `FLT_d3_by_padicValNat_of_descentEngine_coprimeSupport_direct`
- 意図:
  - harmonic envelope を経由せず、
    `strict descent (+ coprime)` から直接 `NoSqOnS0` を回復して
    既存 `FLT_d3_by_padicValNat_of_NoSqOnS0` へ接続できる導線を確保。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.GEisensteinBridge DkMath.FLT.Main`
  - 結果: 成功。

### 2026-02-26 phase-11 継続（step 実装前の API 整備）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/GEisensteinBridge.lean`
- 追加内容:
  1. `PrimitiveSquareReduction`（`q` 固定の1-step縮小証明レコード）
  2. `PrimitiveSquareReduction.toStep`
  3. `primitiveSquareDescentEngine_of_reduce`
  4. `primitiveSquareDescentStep_of_reduce`
- 意図:
  - 今後は「`reduce` 補題（局所縮小）」を証明するだけで
    `PrimitiveSquareDescentEngine` / `PrimitiveSquareDescentStep` へ自動接続できる形にした。
  - これで `step` の具体実装を数学補題へ分離して進められる。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.GEisensteinBridge DkMath.FLT.Main`
  - 結果: 成功。

### 2026-02-26 phase-11 継続（API 実用性の刺し検証）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/GEisensteinBridge.lean`
  - `lean/dk_math/DkMath/FLT/Main.lean`
- 追加内容:
  1. `not_primitiveSquareWitness_of_descentEngine`
  2. `not_primitiveSquareWitness_of_reduce`
  3. `nonLiftableS0_family_of_reduce`
  4. `NoSqOnS0_of_reduce_coprime`
  5. `FLT_d3_by_padicValNat_of_reduce_coprimeSupport_direct`
- 意図:
  - 同じ終点（`NoSqOnS0` / FLT 入口）に対して
    `step` / `engine` / `reduce` の3入力形式を揃え、差し替え可能性を確認。
  - 今後は数学側で `reduce` 補題を作れば、`Main` 直結まで追加作業なしで到達できる。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.GEisensteinBridge DkMath.FLT.Main`
  - 結果: 成功。

### 2026-02-26 phase-11 継続（タスク1: reduce 最小実装）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/GEisensteinBridge.lean`
  - `lean/dk_math/DkMath/FLT/Main.lean`
- 追加内容:
  1. `primitiveSquareReduce_of_step` (`noncomputable`)
  2. `primitiveSquareDescentEngine_of_step` (`noncomputable`)
  3. `FLT_d3_by_padicValNat_of_step_via_reduce_coprimeSupport_direct`
- 意図:
  - 「`step` しかない状態」から `reduce` API を即時生成できることを実装で確認。
  - `reduce` 直結入口が実運用可能であることを明示。
- 備考:
  - `Exists` から `PrimitiveSquareReduction` を作るため `Classical.choose` を使用（`noncomputable`）。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.GEisensteinBridge DkMath.FLT.Main`
  - 結果: 成功。

### 2026-02-26 phase-11 継続（タスク2: reduce 候補 2系統の刺し）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/GEisensteinBridge.lean`
  - `lean/dk_math/DkMath/FLT/Main.lean`
- 追加内容:
  1. `NumberTheoryReduce`（`reduce` 候補の数論系別名）
  2. `TrominoReduce`（`reduce` 候補の幾何系別名）
  3. `NoSqOnS0_of_numberTheoryReduce_coprime`
  4. `NoSqOnS0_of_trominoReduce_coprime`
  5. `FLT_d3_by_padicValNat_of_numberTheoryReduce_coprimeSupport_direct`
  6. `FLT_d3_by_padicValNat_of_trominoReduce_coprimeSupport_direct`
- 意図:
  - 同一 API 上で `reduce` の供給源だけを2系統に分けて差し替えられるかを確認。
  - 将来、数論側 `reduce` とトロミノ側 `reduce` を並行開発して同じ入口に接続可能。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.GEisensteinBridge DkMath.FLT.Main`
  - 結果: 成功。

### 2026-02-26 phase-11 継続（数論ルート固定）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/GEisensteinBridge.lean`
  - `lean/dk_math/DkMath/FLT/Main.lean`
- 追加内容:
  1. `numberTheoryReduce_of_step`
  2. `numberTheoryEngine_of_step`
  3. `numberTheoryEngine_of_reduce`
  4. `FLT_d3_by_padicValNat_of_numberTheoryStep_coprimeSupport_direct`
- 意図:
  - 「数論で進める」方針を API 名称と入口で固定。
  - 今後の実体補題は `NumberTheoryReduce` へ直接供給すればよい状態にした。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.GEisensteinBridge DkMath.FLT.Main`
  - 結果: 成功。

### 2026-02-26 phase-11 継続（数論 first concrete）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/GEisensteinBridge.lean`
  - `lean/dk_math/DkMath/FLT/Main.lean`
- 追加内容:
  1. `numberTheoryReduce_basic`（`step -> reduce` の最小実装名）
  2. `numberTheoryEngine_basic`
  3. `FLT_d3_by_padicValNat_of_numberTheoryReduce_basic_coprimeSupport_direct`
- 意図:
  - 数論側の実体実装ポイントを `numberTheoryReduce_basic` に固定。
  - 今後はこの定義の中身を「本物の局所縮小補題」に差し替えるだけで前進可能。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.GEisensteinBridge DkMath.FLT.Main`
  - 結果: 成功。

### 2026-02-26 phase-11 継続（状態付き数論降下スケルトン）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/GEisensteinBridge.lean`
- 追加内容:
  1. `NumberTheoryDescentState`（`c,b,q` と `Primitive/Sq` 証拠を保持）
  2. `NumberTheoryDescentState.measure`（暫定: `c+b+q`）
  3. `NumberTheoryDescentState.IsStep`
  4. `NumberTheoryDescentState.StepExists`（次状態存在性の型を確定）
  5. `NumberTheoryDescentState.measure_lt_of_isStep`
- 意図:
  - 固定 `(c,b)` API から、実際の反例縮小を表す状態遷移 API へ展開する準備。
  - 次段で `StepExists` を埋める局所数論補題（`step_exists/preserves/decreases`）へ進む。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.GEisensteinBridge DkMath.FLT.Main`
  - 結果: 成功。

### 2026-02-26 phase-11 継続（StepSpec 追加）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/GEisensteinBridge.lean`
- 追加内容:
  1. `NumberTheoryDescentState.StepFunction`
  2. `NumberTheoryDescentState.StepDecreases`
  3. `NumberTheoryDescentState.stepExists_of_stepFunction`
  4. `NumberTheoryDescentState.StepSpec`
  5. `NumberTheoryDescentState.stepExists_of_spec`
- 意図:
  - `StepExists` を直接証明する代わりに、`next + 減少証明` の仕様オブジェクトで管理する形へ整理。
  - 次段では `StepSpec.next` の中身（数論局所構成）を実装すればよい。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.GEisensteinBridge DkMath.FLT.Main`
  - 結果: 成功。

### 2026-02-26 phase-11 継続（StepExists と StepSpec の往復）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/GEisensteinBridge.lean`
- 追加内容:
  1. `NumberTheoryDescentState.spec_of_stepExists`（`StepExists -> StepSpec`）
  2. `NumberTheoryDescentState.stepExists_iff_exists_stepSpec`
- 意図:
  - `StepExists` を直接扱うルートと `StepSpec` 仕様オブジェクトルートを等価化。
  - 次段で `next` 実装を差し込む際、どちらの形でも利用可能にした。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.GEisensteinBridge DkMath.FLT.Main`
  - 結果: 成功。

### 2026-02-26 phase-11 継続（StepExists から NonLiftable/NoSq 接続）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/GEisensteinBridge.lean`
  - `lean/dk_math/DkMath/FLT/Main.lean`
- 追加内容:
  1. `NumberTheoryDescentState.false_of_state_of_stepExists`
  2. `NumberTheoryDescentState.not_nonempty_of_stepExists`
  3. `nonLiftableS0_of_numberTheoryStepExists`
  4. `nonLiftableS0_family_of_numberTheoryStepExists`
  5. `NoSqOnS0_of_numberTheoryStepExists_coprime`
  6. `FLT_d3_by_padicValNat_of_numberTheoryStepExists_coprimeSupport_direct`
- 意図:
  - 状態遷移仕様 `StepExists`（global）から、既存ルート `NonLiftable -> NoSq -> FLT` へ接続。
  - 次段の実装では `StepSpec.next` を具体化すれば、この入口をそのまま利用できる。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.GEisensteinBridge DkMath.FLT.Main`
  - 結果: 成功。

### 2026-02-26 phase-11 継続（降下仕様の健全化）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/GEisensteinBridge.lean`
- 変更内容:
  1. `NumberTheoryDescentState.measure` を `c+b+q` から `q` へ変更
  2. `NumberTheoryDescentState.IsStepCore` を追加（現段階は `c,b` 保存）
  3. `NumberTheoryDescentState.IsStep := IsStepCore ∧ measure減少` へ強化
  4. `core_of_isStep`, `measure_lt_of_isStep` を整備
  5. `false_of_state_of_stepExists` の減少抽出を `measure_lt_of_isStep` 経由に修正
- 意図:
  - 「正当な遷移条件 + 測度減少」の2層構造に修正し、降下仕様を明示化。
  - 測度軸を `q` に統一して、`PrimitiveSquareReduction.hlt : q' < q` と整合させる。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.GEisensteinBridge DkMath.FLT.Main`
  - 結果: 成功。

### 2026-02-26 phase-11 継続（LocalReduce 連結）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/GEisensteinBridge.lean`
  - `lean/dk_math/DkMath/FLT/Main.lean`
- 追加内容:
  1. `NumberTheoryDescentState.nextOfReduction`
  2. `NumberTheoryDescentState.isStep_of_reduction`
  3. `NumberTheoryDescentState.LocalReduce`
  4. `NumberTheoryDescentState.stepFunction_of_localReduce`
  5. `NumberTheoryDescentState.stepDecreases_of_localReduce`
  6. `NumberTheoryDescentState.stepSpec_of_localReduce`
  7. `NumberTheoryDescentState.stepExists_of_localReduce`
  8. `FLT_d3_by_padicValNat_of_numberTheoryLocalReduce_coprimeSupport_direct`
- 意図:
  - 局所縮小データ `LocalReduce` を与えると、
    `StepExists -> NonLiftable -> NoSq -> FLT` が機械的に接続される構成を完成。
  - 次段は `LocalReduce` の実体（数論補題）を埋めるだけ。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.GEisensteinBridge DkMath.FLT.Main`
  - 結果: 成功。

### 2026-02-26 phase-11 継続（固定 `(c,b)` 版の IsStepCore 実体化）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/GEisensteinBridge.lean`
- 変更内容:
  1. `NumberTheoryDescentOn.nextOfReduction` を追加
  2. `NumberTheoryDescentOn.IsStepCore` を追加（`PrimitiveSquareReduction` 由来の遷移のみ許可）
  3. `NumberTheoryDescentOn.IsStep := IsStepCore ∧ measure減少` に変更
  4. `core_of_isStep`, `measure_lt_of_isStep`, `isStep_of_reduction` を追加
  5. `false_of_state_of_stepExists` を `measure_lt_of_isStep` 経由に修正
  6. `stepFunction_of_localReduce` / `stepDecreases_of_localReduce` を `nextOfReduction` と `isStep_of_reduction` ベースへ更新
- 意図:
  - fixed `(c,b)` ルートでも「正当遷移 + 測度減少」の2層構造を明示し、
    `StepExists` の前提を reduction 由来の仕様に固定。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.GEisensteinBridge DkMath.FLT.Main`
  - 結果: 成功。

### 2026-02-26 phase-11 継続（step/reduce から StepExistsOn へのアダプタ追加）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/GEisensteinBridge.lean`
  - `lean/dk_math/DkMath/FLT/Main.lean`
- 追加内容:
  1. `numberTheoryLocalReduceOn_of_step`
  2. `numberTheoryLocalReduceOn_of_reduce`
  3. `numberTheoryStepExistsOn_of_step`
  4. `numberTheoryStepExistsOn_of_reduce`
  5. `FLT_d3_by_padicValNat_of_numberTheoryStepOn_coprimeSupport_direct`
  6. `FLT_d3_by_padicValNat_of_numberTheoryReduceOn_coprimeSupport_direct`
- 意図:
  - `PrimitiveSquareDescentStep` / `NumberTheoryReduce` から、固定 `(c,b)` 版 `StepExistsOn` へ一段で接続。
  - local 降下仕様ルートを `Main` の公開入口として直接使えるようにした。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.GEisensteinBridge DkMath.FLT.Main`
  - 結果: 成功。

### 2026-02-26 phase-11 継続（ReductionKernel 導入: 実体補題3本の受け口）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/GEisensteinBridge.lean`
  - `lean/dk_math/DkMath/FLT/Main.lean`
- 追加内容:
  1. `NumberTheoryDescentOn.ReductionKernel`
     - `nextQ`
     - `preserves_prim`
     - `preserves_sq`
     - `decreases`
  2. `NumberTheoryDescentOn.localReduce_of_kernel`
  3. `NumberTheoryDescentOn.stepExists_of_kernel`
  4. `numberTheoryStepExistsOn_of_kernel`
  5. `FLT_d3_by_padicValNat_of_numberTheoryKernel_coprimeSupport_direct`
- 意図:
  - 数論本体を「次候補構成 / primitive保存 / 平方因子保存 / strict減少」の3+1補題として独立実装可能にする。
  - `ReductionKernel` を1つ与えれば `LocalReduce -> StepExistsOn -> NoSq -> FLT` に自動接続できるようにした。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.GEisensteinBridge DkMath.FLT.Main`
  - 結果: 成功。

### 2026-02-26 phase-11 継続（既存 step/reduce から ReductionKernel へ寄せる）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/GEisensteinBridge.lean`
- 追加内容:
  1. `numberTheoryKernel_of_reduce`
  2. `numberTheoryKernel_of_step`
  3. `numberTheoryStepExistsOn_of_step` を kernel 経由へ切替
  4. `numberTheoryStepExistsOn_of_reduce` を kernel 経由へ切替
- 意図:
  - 新設 `ReductionKernel` を中心に据え、既存の `step/reduce` 入力も同じ経路 (`kernel -> StepExistsOn`) に統一。
  - 今後の本実装は kernel の4フィールドを埋めることに集中できる状態にした。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.GEisensteinBridge DkMath.FLT.Main`
  - 結果: 成功。

### 2026-02-26 phase-11 継続（Kernel 中心ルートへ一本化）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/GEisensteinBridge.lean`
  - `lean/dk_math/DkMath/FLT/Main.lean`
- 追加/変更内容:
  1. `NumberTheoryDescentOn.kernel_of_localReduce` を追加（`hbc/hcop` 前提付き）
  2. `NoSqOnS0_of_numberTheoryKernel_coprime` を追加
  3. `NoSqOnS0_of_numberTheoryLocalReduceOn_coprime` を kernel 経由へ変更
  4. `Main` の local 入口群（`StepOn/ReduceOn/LocalReduceOn/Kernel`）を kernel 中心の NoSq 回復に統一
- 意図:
  - `StepExistsOn` を直接露出させるのではなく、`ReductionKernel` を主入口にして導線を単純化。
  - 実数論実装は kernel の4フィールドを埋めればよい、という設計を明示。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.GEisensteinBridge DkMath.FLT.Main`
  - 結果: 成功。

### 2026-02-26 phase-11 継続（StepExists と LocalReduce/Kernel の同値化）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/GEisensteinBridge.lean`
  - `lean/dk_math/DkMath/FLT/Main.lean`
- 追加内容:
  1. `NumberTheoryDescentOn.localReduce_of_stepExists`（`Classical.choose`）
  2. `NumberTheoryDescentOn.stepExists_iff_nonempty_localReduce`
  3. `NumberTheoryDescentOn.stepExists_iff_nonempty_kernel`（`hbc/hcop` 前提）
  4. `Main` に `FLT_d3_by_padicValNat_of_numberTheoryHasKernel_coprimeSupport_direct`
- 変更内容:
  1. `StepOn/ReduceOn/LocalReduceOn` 入口は kernel 中心の `NoSq` 回復へ統一済み
- 意図:
  - 「次状態存在仕様」「local reduce」「kernel 存在」を相互変換できる形にして、
    今後の数論本体で `Nonempty (ReductionKernel c b)` を示すだけでも Main 入口へ接続可能にした。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.GEisensteinBridge DkMath.FLT.Main`
  - 結果: 成功。

### 2026-02-26 phase-11 継続（`localReduce_of_stepExists` の防御的強化）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/GEisensteinBridge.lean`
- 追加内容:
  1. `NumberTheoryDescentOn.reduction_of_isStep`
     - `IsStep` から `PrimitiveSquareReduction` を再構成
     - `hlt` は `IsStep` の測度減少成分から再構成
  2. `localReduce_of_stepExists` を `reduction_of_isStep` 経由へ変更
- 意図:
  - `IsStepCore` から取り出した reduction の `hlt` を暗黙依存にせず、
    `IsStep` の第2成分（measure 減少）に明示的に結び付ける。
  - 将来 `IsStepCore` の内容を変更した場合の頑健性を上げる。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.GEisensteinBridge DkMath.FLT.Main`
  - 結果: 成功。

### 2026-02-26 phase-11 継続（HasKernel 補題層の追加と Main 委譲整理）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/GEisensteinBridge.lean`
  - `lean/dk_math/DkMath/FLT/Main.lean`
- 追加内容:
  1. `numberTheoryHasKernel_of_step`
  2. `numberTheoryHasKernel_of_reduce`
  3. `numberTheoryHasKernel_of_localReduce`
  4. `NoSqOnS0_of_numberTheoryHasKernel_coprime`
- 変更内容:
  1. `Main` の `StepOn/ReduceOn/Kernel/LocalReduceOn` 入口を `HasKernel` ベースの `NoSq` 回復に寄せて重複を削減
- 意図:
  - 実装本体側は `Nonempty (ReductionKernel c b)` を供給することに集中し、
    入口側は統一された回復補題を使う構造へ整理。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.GEisensteinBridge DkMath.FLT.Main`
  - 結果: 成功。

### 2026-02-26 phase-11 継続（`StepExistsOn` と `HasKernel` の往復補題）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/GEisensteinBridge.lean`
  - `lean/dk_math/DkMath/FLT/Main.lean`
- 追加内容:
  1. `numberTheoryHasKernel_of_stepExistsOn`
  2. `numberTheoryStepExistsOn_of_hasKernel`
- 変更内容:
  1. `FLT_d3_by_padicValNat_of_numberTheoryStepExistsOn_coprimeSupport_direct` を `HasKernel` 経由で `NoSq` 回復する形に統一
- 意図:
  - 入力が `StepExistsOn` でも `HasKernel` でも相互変換できることを明示し、
    入口層の概念を `HasKernel` 中心に揃えた。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.GEisensteinBridge DkMath.FLT.Main`
  - 結果: 成功。

### 2026-02-26 phase-11 継続（実装ターゲットとして `KernelProvider` を明文化）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/GEisensteinBridge.lean`
  - `lean/dk_math/DkMath/FLT/Main.lean`
- 追加内容:
  1. `NumberTheoryKernelProvider`（全 `(c,b)` で kernel を供給）
  2. `NoSqOnS0_of_numberTheoryKernelProvider`
  3. `FLT_d3_by_padicValNat_of_numberTheoryKernelProvider_coprimeSupport_direct`
- 意図:
  - phase-11 本実装の到達点を「kernel を全 `(c,b)` で供給できること」として型で固定。
  - 以後は provider の中身（具体数論補題）を実装すれば、そのまま Main 入口へ接続できる。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.GEisensteinBridge DkMath.FLT.Main`
  - 結果: 成功。

### 2026-02-26 phase-11 継続（`StepProvider` 導入と `KernelProvider` への昇格）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/GEisensteinBridge.lean`
  - `lean/dk_math/DkMath/FLT/Main.lean`
- 追加内容:
  1. `NumberTheoryStepProvider`
  2. `numberTheoryKernelProvider_of_stepProvider`
  3. `NoSqOnS0_of_numberTheoryStepProvider`
  4. `FLT_d3_by_padicValNat_of_numberTheoryStepProvider_coprimeSupport_direct`
- 意図:
  - `ReductionKernel` を直接供給しづらい場合に、より自然な `PrimitiveSquareDescentStep` 供給形で本実装を進められるようにした。
  - `StepProvider -> KernelProvider -> NoSq -> FLT` の一方向導線を確立。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.GEisensteinBridge DkMath.FLT.Main`
  - 結果: 成功。

### 2026-02-26 phase-11 継続（`ReduceProvider` 導入）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/GEisensteinBridge.lean`
  - `lean/dk_math/DkMath/FLT/Main.lean`
- 追加内容:
  1. `NumberTheoryReduceProvider`
  2. `numberTheoryStepProvider_of_reduceProvider`
  3. `numberTheoryKernelProvider_of_reduceProvider`
  4. `NoSqOnS0_of_numberTheoryReduceProvider`
  5. `FLT_d3_by_padicValNat_of_numberTheoryReduceProvider_coprimeSupport_direct`
- 意図:
  - 数論本体を `NumberTheoryReduce` 形で実装したい場合でも、
    `ReduceProvider -> StepProvider/KernelProvider -> NoSq -> FLT` の経路へ即接続できるようにした。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.GEisensteinBridge DkMath.FLT.Main`
  - 結果: 成功。
