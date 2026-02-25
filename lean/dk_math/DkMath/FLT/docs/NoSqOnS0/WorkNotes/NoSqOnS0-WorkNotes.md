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
