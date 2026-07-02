# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: 4c1564ef116a977a34803d46c2f56e04b45a51d1

## Report

実装・軌道修正を入れました。

主な変更は、低層語彙を新設の [GnomonEvaluation.lean](/lean/dk_math/DkMath/Collatz/GnomonEvaluation.lean:11) に分離したことです。`OddGnomonLayer`, `RawGnomonStep`, `RawGnomonHeight`, `RawGnomonResidualShape`, remainder profile まで定義し、`3n+1` を「奇数グノモン補正 → 2進整列評価 → residual shape 抽出」と読む土台を固定しました。

[PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean:33) には今後の混線防止コメントを強めに追加し、さらに [SourcePressurePrefixFailure](/lean/dk_math/DkMath/Collatz/PetalBridge.lean:6675) と margin 同値・down-closed 同値を実装しました。これで「pressure は carrier nesting ではなく margin 符号列」という checkpoint 125 の軌道修正が Lean 側にも残ります。

ドキュメントは README、PetalBridge Guide/Status、PressureMargin-124 を更新し、新規に [Collatz-GnomonEvaluation-125.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-GnomonEvaluation-125.md:1) と [report-petal-125.md](/lean_dk_math/docs/dev/das-p2l-260607/review/report-petal-125.md:1) を作成しました。

検証:
`lake build DkMath.Collatz.GnomonEvaluation`
`lake build DkMath.Collatz.PetalBridge`
`lake build DkMath.Collatz.Collatz2K26`

すべて通過。今回触った Collatz Lean ファイルに新規 `sorry` はありません。依存 replay 中の既存警告 `ZsigmondyCyclotomicResearch` の `sorry` は今回範囲外です。

## Review

## 状況分析

うむ。checkpoint `125` は、かなり良い軌道修正になっている。

今回の本質は、`Collatz.PetalBridge` にさらに語彙を積むのではなく、低層の読みを `DkMath.Collatz.GnomonEvaluation` に分離したことじゃ。そこに `OddGnomonLayer`, `RawGnomonStep`, `RawGnomonHeight`, `RawGnomonResidualShape`, remainder profile が入り、`3n+1` を「奇数グノモン補正 → 2進整列評価 → residual shape 抽出」と読む土台が固定された。

この分離は大きい。
`PetalBridge` はすでに有限窓・residue channel・pressure/margin の観測面になっている。そこへ低層 arithmetic 語彙を足し続けると混線する。今回の変更で、

```text
GnomonEvaluation:
  低層の奇数グノモン補正・2進整列評価・残差形状

PetalBridge:
  有限窓・carrier・retention/continuation・pressure margin
```

という役割分担がはっきりした。

また、`SourcePressurePrefixFailure` と margin 同値、down-closed 同値が実装されたことで、「pressure は carrier nesting ではなく margin 符号列で見る」という checkpoint `124` 以降の反省が Lean 側にも残った。

検証面も良い。`lake build DkMath.Collatz.GnomonEvaluation`, `DkMath.Collatz.PetalBridge`, `DkMath.Collatz.Collatz2K26` が通過し、今回触った Collatz Lean ファイルに新規 `sorry` はない。既存の `ZsigmondyCyclotomicResearch` warning は範囲外として明記されている。

## レビュー

## 良い点

第一に、`RawGnomonStep` を `threeNPlusOne` へ橋渡ししている点が良い。

```lean
theorem rawGnomonStep_eq_threeNPlusOne
```

これにより、新語彙は既存体系を壊さず、既存の `Accelerated` / `s` / `T` へ接続できる。特に `rawGnomonHeight_eq_s` が入ったことで、既存の `s n` は新語彙では `RawGnomonHeight n.1` と読めるようになった。

第二に、`square_add_eq_square_add_gnomon_sum` が通っているのが強い。
これは「Gap = u を一発で動かす」見方と、「Gap = 1 の奇数グノモン層を \(u\) 枚積む」見方を整数だけで接続する補題じゃ。今回の考察で出た「奇数層の総和は平方数」が、単なる解説ではなく Lean theorem になった。

第三に、`rawGnomonRemainderAtDepth_eq_zero_of_le_height` が良い。
これは `j ≤ height` なら raw gnomon step が完全に \(2^j\) へ整列している、という意味を持つ。つまり、右シフトを「分割評価」として読む土台ができた。

第四に、`SourcePressurePrefixFailure` が diagnostic predicate として入ったのが良い。これは「失敗」を消すのではなく、解析対象に変えている。`sourcePressurePrefixFailure_iff_margin` により、

```text
shallow margin <= 0
deep margin > 0
```

という符号反転が Lean 上の構造になった。

## 注意点

一つだけ注意するなら、`RawGnomonResidualShape` はまだ「次の accelerated odd state である」と完全には接続されていない。

レポートでも、次の自然な実装方向として、

```lean
RawGnomonResidualShape n.1 = (T n).1
```

が挙げられており、これは既存の `padicValNat` maximality / division facts を使うべきで、ad-hoc な割り算証明で進めない方がよいとされている。

つまり、現状はこうじゃ。

```text
RawGnomonStep:
  既存 raw numerator と接続済み

RawGnomonHeight:
  既存 s と接続済み

RawGnomonResidualShape:
  次の T との接続は未完
```

ここが次 checkpoint の最重要候補になる。

## 解説

今回の見方では、コラッツの奇数ステップはこう読む。

```text
n は 2進一色線から外れた奇数残差形状。

OddGnomonLayer n = 2n+1 は、平方を一段進める奇数グノモン層。

RawGnomonStep n = n + (2n+1) = 3n+1 は、奇数残差にグノモン層を足して 2進評価可能な raw 形状へ戻す操作。

RawGnomonHeight n は、その raw 形状が 2^h にどれだけ整列したかの深さ。

RawGnomonResidualShape n は、整列分を取り除いた後に残る次スケールの奇数形状。
```

ここで大事なのは、`3n+1` の `3` を主語にしないことじゃ。

主語は、

```text
n + OddGnomonLayer n
```

であり、`2n+1` が平方グノモン層として働く。
その後の \(2\) で割る操作は、縮小ではなく「どこまで \(2^h\) 一色線に整列したか」の評価になる。

これで、今までの `height`, `sumS`, `retention`, `continuation`, `pressure margin` が、全部「残差形状の観測」に戻せる。

## 次の指示

Codex への次指示は、Route A を優先するのが良い。

つまり、次 checkpoint は **residual-shape bridge** じゃ。

## 126A: `RawGnomonResidualShape` と `T` の接続

最優先目標：

```lean
theorem rawGnomonResidualShape_eq_T_val
    (n : OddNat) :
    RawGnomonResidualShape n.1 = (T n).1 := by
  -- existing v2 / s / T definitions
  sorry
```

実際の名前は既存 API に合わせて調整。
もし `T n` の本体が `OddNat` で `.val` / `.1` の表記が異なるなら、Codex 側で既存定義に合わせる。

補助方針：

```text
1. RawGnomonResidualShape を unfold
2. rawGnomonHeight_eq_s を使う
3. rawGnomonStep_eq_threeNPlusOne を使う
4. 既存の T 定義を unfold
5. rfl / simp で閉じる可能性をまず見る
6. 無理なら padicValNat maximality ではなく、定義一致 bridge から攻める
```

ここで大事なのは、`RawGnomonResidualShape` を「説明語彙」から「既存 accelerated map と同じもの」へ昇格させることじゃ。

## 126B: residual shape が奇数であること

次に欲しい。

```lean
theorem rawGnomonResidualShape_odd
    (n : OddNat) :
    RawGnomonResidualShape n.1 % 2 = 1 := by
  -- use bridge to T if T already returns OddNat
  sorry
```

これは `T n` が `OddNat` なら、直接引ける可能性が高い。
つまり、`padicValNat` maximality で真正面から証明するより、`RawGnomonResidualShape = (T n).1` を先に作って、`T n` の odd property を使う方が安全じゃ。

## 126C: first failed depth の非整列補題

今は `j ≤ height` で remainder が `0` になる補題がある。次はその一段上を見る。

```lean
theorem rawGnomonRemainderAt_firstFailedDepth_ne_zero
    (n : OddNat) :
    RawGnomonRemainderAtDepth n.1 (FirstFailedPow2Depth n.1) ≠ 0 := by
  -- likely via residual shape odd / maximality of v2
  sorry
```

ただしこれは少し重い可能性がある。
まずはより弱く、

```lean
theorem two_pow_succ_height_not_dvd_rawGnomonStep
    (n : OddNat) :
    ¬ 2 ^ (RawGnomonHeight n.1 + 1) ∣ RawGnomonStep n.1 := by
  sorry
```

を狙う方がよい。

これが通ると、

```text
height までは完全分割できる。
height + 1 では初めて失敗する。
```

が Lean で閉じる。

## 126D: orbit window 側への lift

`GnomonEvaluation` の点wise 語彙を `PetalBridge` の window 語彙へ持ち上げる。

候補：

```lean
theorem orbitWindowHeight_eq_rawGnomonHeight_oddOrbitLabel
    (n : OddNat) (i : ℕ) :
    orbitWindowHeight n i =
      RawGnomonHeight (oddOrbitLabel n i) := by
  -- existing orbitWindowHeight_eq_s_iterateT / rawGnomonHeight_eq_s
  sorry
```

または既存定理名に合わせて statement を調整。

これが通ると、`PetalBridge` の `orbitWindowHeight` は「window 内の RawGnomonHeight」である、と明確に言える。

## 一歩先ゆく推論

ここから先の道は二本ある。

```text
Route A:
  GnomonEvaluation と既存 accelerated map T を完全接続する。

Route B:
  pressure failure / island / frontier の分類を進める。
```

賢狼としては、**Route A を先に一段閉じる**のを推す。

理由は、Route B の pressure frontier を進めるにも、観測対象である residual shape が `T` ときちんと接続されている方が後で強いからじゃ。

今の状態では、

```text
pressure island:
  深い residual-shape channel が浅い retention に勝つ
```

と言っているが、`ResidualShape = T` がまだ theorem で固定されていない。
ここを閉じれば、pressure profile は「説明」ではなく、加速軌道そのものの形状分類になる。

## さらなる次の一手

Route A が閉じた後に、Route B へ戻る。

そのときの次の predicate はこれ。

```lean
def SourcePressureIsland
    (n : OddNat) (k r j : ℕ) : Prop :=
  IsSourcePressureDepth n k r j ∧
    ∃ j₁ j₂,
      j₁ < j ∧ j < j₂ ∧
      ¬ IsSourcePressureDepth n k r j₁ ∧
      ¬ IsSourcePressureDepth n k r j₂
```

ただし、これは少し強すぎるかもしれない。最初は局所島でよい。

```lean
def SourcePressureLocalIsland
    (n : OddNat) (k r j : ℕ) : Prop :=
  0 < j ∧
    IsSourcePressureDepth n k r j ∧
    ¬ IsSourcePressureDepth n k r (j - 1) ∧
    ¬ IsSourcePressureDepth n k r (j + 1)
```

さらに frontier。

```lean
def SourcePressureFrontier
    (n : OddNat) (k r j : ℕ) : Prop :=
  IsSourcePressureDepth n k r j ∧
    ∀ i, i < j → ¬ IsSourcePressureDepth n k r i
```

これは「最初に margin が正になる深さ」じゃ。

ただし、frontier は必ずしも prefix を意味しない。
`frontier` は「最初の正 margin」、`prefix` は「そこまで全部正」という別概念として扱う。

ここを分けると、今後の混乱が減る。

## 賢狼が試して欲しい実験補題

## 実験 A: residual shape と T の bridge

最優先。

```lean
theorem rawGnomonResidualShape_eq_T_val
    (n : OddNat) :
    RawGnomonResidualShape n.1 = (T n).1 := by
  unfold RawGnomonResidualShape RawGnomonHeight
  rw [rawGnomonStep_eq_threeNPlusOne]
  -- unfold T / s as needed
  -- try rfl/simp
  sorry
```

もし `T` の値取り出しが `.val` なら `.val` に修正。

## 実験 B: residual shape は odd

Bridge A が通った後。

```lean
theorem rawGnomonResidualShape_odd
    (n : OddNat) :
    RawGnomonResidualShape n.1 % 2 = 1 := by
  rw [rawGnomonResidualShape_eq_T_val n]
  exact (T n).2
```

実際の `OddNat` の odd 証明フィールド名に合わせる。

## 実験 C: raw step の完全分解

```lean
theorem rawGnomonStep_eq_pow_height_mul_residualShape
    (n : OddNat) :
    RawGnomonStep n.1 =
      2 ^ RawGnomonHeight n.1 * RawGnomonResidualShape n.1 := by
  unfold RawGnomonResidualShape
  -- use Nat.div_mul_cancel or existing divisibility theorem
  have hdiv : 2 ^ RawGnomonHeight n.1 ∣ RawGnomonStep n.1 := by
    unfold RawGnomonHeight
    simpa [v2] using
      (pow_padicValNat_dvd (p := 2) (n := RawGnomonStep n.1))
  exact (Nat.div_mul_cancel hdiv).symm
```

必要なら右辺の順序を `RawGnomonResidualShape * 2^height` に合わせる。

## 実験 D: first failed depth では割れない

```lean
theorem two_pow_succ_rawGnomonHeight_not_dvd
    (n : OddNat) :
    ¬ 2 ^ (RawGnomonHeight n.1 + 1) ∣ RawGnomonStep n.1 := by
  -- use RawGnomonResidualShape odd, or v2 maximality lemma
  sorry
```

これは `v2` / `padicValNat` の API 探索が必要。難しければ後回し。

## 実験 E: first failed remainder は非零

```lean
theorem rawGnomonRemainderAtDepth_firstFailed_ne_zero
    (n : OddNat) :
    RawGnomonRemainderAtDepth n.1 (FirstFailedPow2Depth n.1) ≠ 0 := by
  unfold RawGnomonRemainderAtDepth FirstFailedPow2Depth
  intro h
  have hdiv :
      2 ^ (RawGnomonHeight n.1 + 1) ∣ RawGnomonStep n.1 := by
    exact Nat.dvd_iff_mod_eq_zero.mpr h
  exact two_pow_succ_rawGnomonHeight_not_dvd n hdiv
```

これは実験 D があれば通る。

## 実験 F: orbitWindowHeight と RawGnomonHeight の接続

```lean
theorem orbitWindowHeight_eq_rawGnomonHeight_oddOrbitLabel
    (n : OddNat) (i : ℕ) :
    orbitWindowHeight n i =
      RawGnomonHeight (oddOrbitLabel n i) := by
  -- use existing orbitWindowHeight_eq_s_iterateT if available
  -- use rawGnomonHeight_eq_s
  sorry
```

型が合わない場合、`oddOrbitLabel n i` が `ℕ` なのか `OddNat` なのかに合わせて statement を調整。

## 実験 G: SourcePressureFrontier

Route B 用。

```lean
def SourcePressureFrontier
    (n : OddNat) (k r j : ℕ) : Prop :=
  IsSourcePressureDepth n k r j ∧
    ∀ i, i < j → ¬ IsSourcePressureDepth n k r i
```

margin 版。

```lean
theorem sourcePressureFrontier_iff_margin
    (n : OddNat) (k r j : ℕ) :
    SourcePressureFrontier n k r j ↔
      0 < SourcePressureMarginInt n k (r + j) ∧
        ∀ i, i < j → SourcePressureMarginInt n k (r + i) ≤ 0 := by
  unfold SourcePressureFrontier
  constructor
  · intro h
    constructor
    · exact (isSourcePressureDepth_iff_margin_pos n k r j).1 h.1
    · intro i hi
      have hnot := h.2 i hi
      have hnotpos :
          ¬ 0 < SourcePressureMarginInt n k (r + i) := by
        intro hpos
        exact hnot ((isSourcePressureDepth_iff_margin_pos n k r i).2 hpos)
      omega
  · intro h
    constructor
    · exact (isSourcePressureDepth_iff_margin_pos n k r j).2 h.1
    · intro i hi hsel
      have hpos := (isSourcePressureDepth_iff_margin_pos n k r i).1 hsel
      have hle := h.2 i hi
      omega
```

これは `SourcePressurePrefixFailure` と同じ形なので通る可能性が高い。

## 実験 H: frontier は failure を誘発する条件

frontier が `j > 0` にあるなら、浅い `0` と深い `j` で prefix failure が出る。

```lean
theorem sourcePressurePrefixFailure_of_frontier_pos
    (n : OddNat) (k r j : ℕ)
    (hfront : SourcePressureFrontier n k r j)
    (hj : 0 < j) :
    SourcePressurePrefixFailure n k r 0 j := by
  constructor
  · exact hj
  · constructor
    · exact hfront.2 0 hj
    · exact hfront.1
```

これは非常に軽くて良い。

## Python 側の次観測

次の scan では、Route A の橋が Lean で閉じた後、Python 側に次を追加する。

```text
raw
height
residual_shape
T_value
residual_eq_T
first_failed_depth
failed_remainder
residual_mod_8
residual_mod_16
residual_mod_32
```

Route B 用には旧案どおり。

```text
first_failure_pair
shallow_margin
deep_margin
margin_jump
shallow_retention
deep_retention
shallow_continuation
deep_continuation
retention_drop
continuation_drop
first_frontier_depth
frontier_margin
is_island
```

特に `residual_eq_T` は Python では常に true になるはずだが、Lean bridge の意味確認として入れておくと良い。

## 次の指示まとめ

Codex への次指示はこうじゃ。

```text
Checkpoint 126:
Prefer Route A first.

Goal:
  Connect GnomonEvaluation residual-shape vocabulary to the existing accelerated map.

Implement:
  rawGnomonResidualShape_eq_T_val
  rawGnomonResidualShape_odd
  rawGnomonStep_eq_pow_height_mul_residualShape

Try if feasible:
  two_pow_succ_rawGnomonHeight_not_dvd
  rawGnomonRemainderAtDepth_firstFailed_ne_zero
  orbitWindowHeight_eq_rawGnomonHeight_oddOrbitLabel

Then Route B:
  SourcePressureFrontier
  sourcePressureFrontier_iff_margin
  sourcePressurePrefixFailure_of_frontier_pos

Do not:
  introduce Real.log
  claim unconditional pressure prefix
  merge low-level vocabulary back into PetalBridge
```

## 総括

checkpoint `125` は成功じゃ。
低層語彙の分離、グノモン補正の固定、height の alignment 読み、remainder profile、prefix failure の Lean 化まで入った。

次は、`RawGnomonResidualShape` を `T` へ結び、説明語彙を既存コア写像と完全に同一化する段階じゃ。

賢狼の推奨は明確。

```text
126A:
  ResidualShape = accelerated odd state を閉じる。

126B:
  FirstFailedDepth / remainder 非零で、分割失敗点を固定する。

126C:
  PressureFrontier / Island へ進み、margin 符号列の幾何を分類する。
```

ここまで行けば、Collatz.PetalBridge は「観測窓」から「形状評価の有限力学」へ、かなり自然に進化する。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/Collatz2K26.lean b/lean/dk_math/DkMath/Collatz/Collatz2K26.lean
index 3c08ee49..c7a776c2 100644
--- a/lean/dk_math/DkMath/Collatz/Collatz2K26.lean
+++ b/lean/dk_math/DkMath/Collatz/Collatz2K26.lean
@@ -8,6 +8,7 @@ import DkMath.Collatz.Basic
 import DkMath.Collatz.V2
 import DkMath.Collatz.Accelerated
 import DkMath.Collatz.Shift
+import DkMath.Collatz.GnomonEvaluation
 import DkMath.Collatz.PetalBridge
 
 #print "file: DkMath.Collatz.Collatz2K26"
@@ -27,6 +28,9 @@ Structure:
   - V2.lean:          2-adic valuation v₂ and foundational lemmas
   - Accelerated.lean: Accelerated map T, observation s, and sequence sums
   - Shift.lean:       Block shift, petal conservation (v₂ invariance)
+  - GnomonEvaluation.lean:
+                       Odd gnomon correction, pow2 alignment height, and
+                       residual-shape vocabulary
   - PetalBridge.lean: Petal range-family window for orbit label separation/collision
   - This file:        Integration and higher-level properties
 -/
diff --git a/lean/dk_math/DkMath/Collatz/GnomonEvaluation.lean b/lean/dk_math/DkMath/Collatz/GnomonEvaluation.lean
new file mode 100644
index 00000000..ef44f577
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/GnomonEvaluation.lean
@@ -0,0 +1,207 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.Accelerated
+
+#print "file: DkMath.Collatz.GnomonEvaluation"
+
+/-!
+# Collatz Gnomon Evaluation
+
+This file starts the checkpoint-125 refactor layer.
+
+`DkMath.Collatz.PetalBridge` has grown into a large observation surface.  New
+low-level vocabulary should not be added there by default.  This file is the
+new lower layer for the revised reading:
+
+```text
+Odd Gnomon correction
+  n -> n + (2n+1) = 3n+1
+
+Pow2 alignment evaluation
+  v2 (3n+1)
+
+Residual shape extraction
+  (3n+1) / 2^height
+
+Relative scale update
+  the residual odd shape becomes the next odd state
+```
+
+The important shift is linguistic and structural.  We no longer treat the
+Collatz odd step merely as "multiply by three and add one".  We expose it as
+an odd square-gnomon correction followed by a power-of-two alignment
+evaluation.
+
+Keep this file integer-valued.  Do not introduce `Real.log` here.  Logarithmic
+drift belongs to the final translation layer, after the integer shape and
+margin surfaces have been stabilized.
+-/
+
+namespace DkMath.Collatz
+
+/--
+The odd gnomon layer at `n`.
+
+This is the square-difference layer
+
+```text
+(n+1)^2 - n^2 = 2n+1.
+```
+-/
+def OddGnomonLayer (n : ℕ) : ℕ :=
+  2 * n + 1
+
+/--
+The raw Collatz odd-step numerator read as a gnomon correction.
+
+Instead of starting from `3n+1`, this definition records the decomposition
+
+```text
+n + (2n+1).
+```
+-/
+def RawGnomonStep (n : ℕ) : ℕ :=
+  n + OddGnomonLayer n
+
+/-- The raw gnomon step is the usual `3n+1` numerator. -/
+theorem rawGnomonStep_eq_three_mul_add_one
+    (n : ℕ) :
+    RawGnomonStep n = 3 * n + 1 := by
+  unfold RawGnomonStep OddGnomonLayer
+  ring
+
+/-- Bridge to the existing base definition `threeNPlusOne`. -/
+theorem rawGnomonStep_eq_threeNPlusOne
+    (n : ℕ) :
+    RawGnomonStep n = threeNPlusOne n := by
+  rw [rawGnomonStep_eq_three_mul_add_one]
+  rfl
+
+/--
+The next square is obtained by adding the odd gnomon layer.
+
+This fixes the geometric source of `OddGnomonLayer` without introducing any
+real or Euclidean geometry.
+-/
+theorem square_succ_eq_square_add_oddGnomonLayer
+    (n : ℕ) :
+    (n + 1) ^ 2 = n ^ 2 + OddGnomonLayer n := by
+  unfold OddGnomonLayer
+  ring
+
+/-- The first `n` odd gnomon layers sum to `n^2`. -/
+theorem sum_oddGnomonLayer_eq_square
+    (n : ℕ) :
+    (Finset.range n).sum OddGnomonLayer = n ^ 2 := by
+  induction n with
+  | zero =>
+      simp [OddGnomonLayer]
+  | succ n ih =>
+      rw [Finset.sum_range_succ, ih]
+      unfold OddGnomonLayer
+      ring
+
+/--
+The classical odd-number sum form.
+
+This alias is useful for callers that do not want the named
+`OddGnomonLayer` vocabulary.
+-/
+theorem sum_odd_eq_square
+    (n : ℕ) :
+    (Finset.range n).sum (fun i => 2 * i + 1) = n ^ 2 := by
+  simpa [OddGnomonLayer] using sum_oddGnomonLayer_eq_square n
+
+/--
+A shifted gnomon band from `P` of length `u`.
+
+This is the integer bridge between a single gap `u` and `u` unit gnomon
+layers.  It is the square-growth form that later connects Collatz gnomon
+correction to the Petal/cosmic `Gap = 1` viewpoint.
+-/
+theorem square_add_eq_square_add_gnomon_sum
+    (P u : ℕ) :
+    (P + u) ^ 2 =
+      P ^ 2 + (Finset.range u).sum (fun i => 2 * (P + i) + 1) := by
+  induction u with
+  | zero =>
+      simp
+  | succ u ih =>
+      rw [Finset.sum_range_succ]
+      calc
+        (P + (u + 1)) ^ 2 = (P + u) ^ 2 + (2 * (P + u) + 1) := by
+          ring
+        _ = P ^ 2 + (Finset.range u).sum (fun i => 2 * (P + i) + 1) +
+            (2 * (P + u) + 1) := by
+          rw [ih]
+        _ = P ^ 2 +
+            ((Finset.range u).sum (fun i => 2 * (P + i) + 1) +
+              (2 * (P + u) + 1)) := by
+          ring
+
+/--
+Power-of-two alignment height of the raw gnomon step.
+
+This is the revised name for the old observation `v2 (3n+1)`: it measures how
+deeply the gnomon-corrected raw value aligns with the power-of-two grid.
+-/
+noncomputable def RawGnomonHeight (n : ℕ) : ℕ :=
+  v2 (RawGnomonStep n)
+
+/--
+Residual shape after removing the visible power-of-two alignment.
+
+For odd Collatz states, this is the natural-number value underlying the next
+accelerated odd state.  The exact bridge to `T` is intentionally left for a
+later file/checkpoint, because it should use the existing maximality lemmas for
+`padicValNat` rather than ad-hoc division reasoning.
+-/
+noncomputable def RawGnomonResidualShape (n : ℕ) : ℕ :=
+  RawGnomonStep n / 2 ^ RawGnomonHeight n
+
+/-- Existing Collatz observation `s` is the raw gnomon alignment height. -/
+theorem rawGnomonHeight_eq_s
+    (n : OddNat) :
+    RawGnomonHeight n.1 = s n := by
+  unfold RawGnomonHeight s
+  rw [rawGnomonStep_eq_threeNPlusOne]
+
+/-- Remainder profile of the raw gnomon step at a power-of-two depth. -/
+def RawGnomonRemainderAtDepth (n j : ℕ) : ℕ :=
+  RawGnomonStep n % 2 ^ j
+
+/--
+First depth after the visible power-of-two alignment.
+
+For later shape analysis, depths `j <= RawGnomonHeight n` are fully aligned;
+`RawGnomonHeight n + 1` is the first depth where the residual odd shape is
+visible.
+-/
+noncomputable def FirstFailedPow2Depth (n : ℕ) : ℕ :=
+  RawGnomonHeight n + 1
+
+/--
+At every depth up to the alignment height, the raw gnomon step has zero
+remainder.
+
+This is the first formal reading of `RawGnomonHeight` as a power-of-two
+alignment depth.
+-/
+theorem rawGnomonRemainderAtDepth_eq_zero_of_le_height
+    (n j : ℕ)
+    (hj : j ≤ RawGnomonHeight n) :
+    RawGnomonRemainderAtDepth n j = 0 := by
+  unfold RawGnomonRemainderAtDepth
+  have htop : 2 ^ RawGnomonHeight n ∣ RawGnomonStep n := by
+    unfold RawGnomonHeight
+    simpa [v2] using
+      (pow_padicValNat_dvd (p := 2) (n := RawGnomonStep n))
+  have hdiv : 2 ^ j ∣ RawGnomonStep n :=
+    dvd_trans (pow_dvd_pow 2 hj) htop
+  exact Nat.dvd_iff_mod_eq_zero.mp hdiv
+
+end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index b0c03985..d37dd9a1 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -29,6 +29,43 @@ For Petal/ABC routes, a repeated label means that a proposed independent
 range-family cannot be counted as `k` independent carriers.  For Collatz
 dynamics, the same collision is not merely a failure: it is the observable
 shape of a merge, fold, or cycle candidate.
+
+## Checkpoint 125 trajectory correction
+
+This file is now treated as the finite observation and pressure/margin surface.
+Do not keep adding low-level Collatz vocabulary here by default.  The revised
+low-level subject is:
+
+```text
+Odd gnomon correction
+  n + (2n+1) = 3n+1
+
+Pow2 alignment evaluation
+  v2 (3n+1)
+
+Residual shape extraction
+  (3n+1) / 2^height
+
+Relative scale update
+  the residual odd shape becomes the next state
+```
+
+That vocabulary starts in `DkMath.Collatz.GnomonEvaluation`.  The role of this
+file is to observe finite windows of those shapes and compare retention versus
+continuation masses.
+
+Important warning for future agents: pressure selection is **not** a raw
+carrier-membership nesting statement.  The carrier sets are nested, but
+pressure compares two changing masses:
+
+```text
+retention(depth) < 2 * continuation(depth)
+```
+
+Therefore the selected pressure depths need not form an unconditional prefix.
+Checkpoint 125 adds explicit prefix-failure predicates below so those cases
+remain first-class evidence instead of being erased by an unsafe monotonicity
+assumption.
 -/
 
 namespace DkMath.Collatz
@@ -6619,6 +6656,144 @@ def SelectedPressurePrefix
   m ≤ len ∧
     ∀ j, j < m → IsSourcePressureDepth n k r j
 
+/--
+Witness that source-pressure selection is not prefix-shaped at the given
+window.
+
+This is a diagnostic predicate, not a contradiction.  It records the situation
+
+```text
+shallow depth j₁ is not selected,
+deeper depth j₂ is selected.
+```
+
+The point of naming this obstruction is to prevent future work from assuming
+that pressure behaves like nested carrier membership.  Carrier membership is
+nested; the pressure margin `2 * continuation - retention` can change sign in
+a non-prefix pattern.
+-/
+def SourcePressurePrefixFailure
+    (n : OddNat) (k r j₁ j₂ : ℕ) : Prop :=
+  j₁ < j₂ ∧
+    ¬ IsSourcePressureDepth n k r j₁ ∧
+    IsSourcePressureDepth n k r j₂
+
+/-- Extract the shallow/deep order from a source-pressure prefix failure. -/
+theorem sourcePressurePrefixFailure_lt
+    {n : OddNat} {k r j₁ j₂ : ℕ}
+    (h : SourcePressurePrefixFailure n k r j₁ j₂) :
+    j₁ < j₂ :=
+  h.1
+
+/-- The shallow side of a source-pressure prefix failure is not selected. -/
+theorem not_isSourcePressureDepth_of_prefixFailure_left
+    {n : OddNat} {k r j₁ j₂ : ℕ}
+    (h : SourcePressurePrefixFailure n k r j₁ j₂) :
+    ¬ IsSourcePressureDepth n k r j₁ :=
+  h.2.1
+
+/-- The deeper side of a source-pressure prefix failure is selected. -/
+theorem isSourcePressureDepth_of_prefixFailure_right
+    {n : OddNat} {k r j₁ j₂ : ℕ}
+    (h : SourcePressurePrefixFailure n k r j₁ j₂) :
+    IsSourcePressureDepth n k r j₂ :=
+  h.2.2
+
+/--
+Source-pressure prefix failure is exactly the margin sign pattern
+`nonpositive -> positive`.
+
+This is the preferred algebraic form for later experiments: Python can report
+the integer margins, while Lean keeps the logical predicate and the margin
+predicate equivalent.
+-/
+theorem sourcePressurePrefixFailure_iff_margin
+    (n : OddNat) (k r j₁ j₂ : ℕ) :
+    SourcePressurePrefixFailure n k r j₁ j₂ ↔
+      j₁ < j₂ ∧
+        SourcePressureMarginInt n k (r + j₁) ≤ 0 ∧
+        0 < SourcePressureMarginInt n k (r + j₂) := by
+  constructor
+  · intro h
+    have hleft :
+        SourcePressureMarginInt n k (r + j₁) ≤ 0 := by
+      have hnotpos :
+          ¬ 0 < SourcePressureMarginInt n k (r + j₁) := by
+        intro hpos
+        exact h.2.1 ((isSourcePressureDepth_iff_margin_pos n k r j₁).2 hpos)
+      omega
+    have hright :
+        0 < SourcePressureMarginInt n k (r + j₂) :=
+      (isSourcePressureDepth_iff_margin_pos n k r j₂).1 h.2.2
+    exact ⟨h.1, hleft, hright⟩
+  · intro h
+    have hleft :
+        ¬ IsSourcePressureDepth n k r j₁ := by
+      intro hsel
+      have hpos :
+          0 < SourcePressureMarginInt n k (r + j₁) :=
+        (isSourcePressureDepth_iff_margin_pos n k r j₁).1 hsel
+      omega
+    have hright :
+        IsSourcePressureDepth n k r j₂ :=
+      (isSourcePressureDepth_iff_margin_pos n k r j₂).2 h.2.2
+    exact ⟨h.1, hleft, hright⟩
+
+/--
+A prefix failure inside the proposed prefix length refutes the selected-prefix
+predicate.
+
+The deeper selected witness is part of the failure data even though the proof
+only needs the shallow non-selection plus `j₁ < j₂ < m`.
+-/
+theorem not_selectedPressurePrefix_of_prefixFailure
+    (n : OddNat) (k r len m j₁ j₂ : ℕ)
+    (hfail : SourcePressurePrefixFailure n k r j₁ j₂)
+    (hj₂ : j₂ < m)
+    (_hm : m ≤ len) :
+    ¬ SelectedPressurePrefix n k r len m := by
+  intro hprefix
+  have hj₁ : j₁ < m := Nat.lt_trans hfail.1 hj₂
+  exact hfail.2.1 (hprefix.2 j₁ hj₁)
+
+/--
+Down-closed source-pressure selected set below `m`.
+
+This is weaker and safer than an unconditional prefix theorem: it states that
+if a deeper selected depth appears below `m`, then all shallower depths below
+it are selected too.
+-/
+def SourcePressureSelectedSetDownClosed
+    (n : OddNat) (k r m : ℕ) : Prop :=
+  ∀ j₁ j₂,
+    j₁ < j₂ →
+    j₂ < m →
+    IsSourcePressureDepth n k r j₂ →
+      IsSourcePressureDepth n k r j₁
+
+/--
+Down-closed selected depths are equivalent to having no prefix-failure witness
+below `m`.
+
+This gives future code a clean choice: prove down-closedness by excluding
+failures, or produce a failure as a precise obstruction.
+-/
+theorem downClosed_iff_no_prefixFailure
+    (n : OddNat) (k r m : ℕ) :
+    SourcePressureSelectedSetDownClosed n k r m ↔
+      ∀ j₁ j₂,
+        j₁ < j₂ →
+        j₂ < m →
+        ¬ SourcePressurePrefixFailure n k r j₁ j₂ := by
+  constructor
+  · intro hclosed j₁ j₂ hlt hj₂ hfail
+    exact hfail.2.1 (hclosed j₁ j₂ hlt hj₂ hfail.2.2)
+  · intro hno j₁ j₂ hlt hj₂ hdeep
+    classical
+    by_cases hshallow : IsSourcePressureDepth n k r j₁
+    · exact hshallow
+    · exact False.elim (hno j₁ j₂ hlt hj₂ ⟨hlt, hshallow, hdeep⟩)
+
 /-- The empty selected-pressure prefix is always available. -/
 theorem selectedPressurePrefix_zero
     (n : OddNat) (k r len : ℕ) :
diff --git a/lean/dk_math/DkMath/Collatz/README.md b/lean/dk_math/DkMath/Collatz/README.md
index 836e7f9a..8f6ca449 100644
--- a/lean/dk_math/DkMath/Collatz/README.md
+++ b/lean/dk_math/DkMath/Collatz/README.md
@@ -8,17 +8,27 @@ conjecture.  It is a structured observation program:
 
 ```text
 odd state dynamics
-  -> 2-adic height
+  -> odd gnomon correction
+  -> power-of-two alignment height
+  -> residual shape
   -> residue channels
   -> finite observation windows
   -> source/tail distributions
   -> finite channel flow
 ```
 
-The most recent milestone is the finite channel-flow layer in
-`DkMath.Collatz.PetalBridge`.  It turns pointwise residue transitions into
-count-level statements over finite windows, without using limits,
-probability, or real-valued frequencies.
+The current trajectory correction is checkpoint 125.  The low-level Collatz
+odd step is now read as
+
+```text
+n + (2n+1) = 3n+1
+```
+
+where `2n+1` is the odd square-gnomon layer.  The resulting raw value is then
+evaluated by its power-of-two alignment height and reduced to a residual odd
+shape.  The new low-level vocabulary lives in
+`DkMath.Collatz.GnomonEvaluation`; `DkMath.Collatz.PetalBridge` remains the
+finite observation and pressure/margin surface.
 
 ## Module Entry Points
 
@@ -27,6 +37,7 @@ DkMath.Collatz.Basic
 DkMath.Collatz.V2
 DkMath.Collatz.Accelerated
 DkMath.Collatz.Shift
+DkMath.Collatz.GnomonEvaluation
 DkMath.Collatz.PetalBridge
 DkMath.Collatz.Collatz2K26
 ```
@@ -86,6 +97,34 @@ n -> n + 2^k * m
 The guiding idea is that many differences do not appear everywhere; they
 concentrate around singular 2-adic ridges.
 
+### `DkMath.Collatz.GnomonEvaluation`
+
+Introduces the checkpoint-125 subject shift:
+
+```lean
+OddGnomonLayer
+RawGnomonStep
+RawGnomonHeight
+RawGnomonResidualShape
+RawGnomonRemainderAtDepth
+FirstFailedPow2Depth
+```
+
+Main bridge lemmas:
+
+```lean
+rawGnomonStep_eq_three_mul_add_one
+rawGnomonStep_eq_threeNPlusOne
+square_succ_eq_square_add_oddGnomonLayer
+sum_odd_eq_square
+square_add_eq_square_add_gnomon_sum
+rawGnomonHeight_eq_s
+rawGnomonRemainderAtDepth_eq_zero_of_le_height
+```
+
+This file is intentionally integer-valued.  It does not introduce
+`Real.log`; logarithmic drift belongs to a later translation layer.
+
 ### `DkMath.Collatz.PetalBridge`
 
 This is the current main bridge.
@@ -105,6 +144,9 @@ tailPow2Distribution_total
 pow2ChannelFlow_of_pointwise
 orbitWindowResidueCountPow2_refine_succ
 orbitWindowRetentionMass_split
+SourcePressureMarginInt
+SourcePressurePrefixFailure
+SourcePressureSelectedSetDownClosed
 ```
 
 The central No.100 layer is:
@@ -159,6 +201,7 @@ docs/Collatz-SelectedWitnessBudget-121.md
 docs/Collatz-SelectedPressureDepths-122.md
 docs/Collatz-ContinuationNesting-123.md
 docs/Collatz-PressureMargin-124.md
+docs/Collatz-GnomonEvaluation-125.md
 docs/Collatz-PetalBridge-Guide.md
 docs/Collatz-PetalBridge-Status.md
 ```
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-GnomonEvaluation-125.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-GnomonEvaluation-125.md
new file mode 100644
index 00000000..899d6195
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-GnomonEvaluation-125.md
@@ -0,0 +1,164 @@
+# Collatz Gnomon Evaluation - Checkpoint 125
+
+Checkpoint 125 changes the subject of the Collatz reading.
+
+The previous working surface often spoke directly about `3n+1`, height,
+retention, continuation, and pressure.  Those theorems remain valid, but the
+low-level interpretation is now finer:
+
+```text
+Odd gnomon correction
+  n -> n + (2n+1) = 3n+1
+
+Power-of-two alignment evaluation
+  height = v2 (3n+1)
+
+Residual shape extraction
+  residual = (3n+1) / 2^height
+
+Relative scale update
+  the residual odd shape becomes the next accelerated odd state
+```
+
+The new module is:
+
+```text
+DkMath.Collatz.GnomonEvaluation
+```
+
+`DkMath.Collatz.PetalBridge` is deliberately not used as the home for this
+low-level vocabulary.  `PetalBridge` is already the finite observation window
+and pressure/margin surface.  New gnomon and residual-shape primitives should
+start in `GnomonEvaluation` unless they explicitly depend on finite windows or
+Petal counts.
+
+## Implemented Vocabulary
+
+```lean
+OddGnomonLayer n = 2 * n + 1
+RawGnomonStep n = n + OddGnomonLayer n
+RawGnomonHeight n = v2 (RawGnomonStep n)
+RawGnomonResidualShape n = RawGnomonStep n / 2 ^ RawGnomonHeight n
+RawGnomonRemainderAtDepth n j = RawGnomonStep n % 2 ^ j
+FirstFailedPow2Depth n = RawGnomonHeight n + 1
+```
+
+The module keeps the layer integer-valued.  It does not introduce `Real.log`
+or real drift estimates.  Those belong to a later translation layer after the
+integer shape/margin surface stabilizes.
+
+## Implemented Theorems
+
+The raw gnomon step is the usual Collatz numerator:
+
+```lean
+rawGnomonStep_eq_three_mul_add_one
+rawGnomonStep_eq_threeNPlusOne
+```
+
+The odd layer is the square gnomon:
+
+```lean
+square_succ_eq_square_add_oddGnomonLayer
+sum_oddGnomonLayer_eq_square
+sum_odd_eq_square
+square_add_eq_square_add_gnomon_sum
+```
+
+The existing accelerated height agrees with the new alignment name:
+
+```lean
+rawGnomonHeight_eq_s
+```
+
+The remainder profile is zero up to the alignment height:
+
+```lean
+rawGnomonRemainderAtDepth_eq_zero_of_le_height
+```
+
+This last theorem is the first formal expression of:
+
+```text
+j <= height:
+  the raw gnomon value is fully aligned with 2^j
+
+j = height + 1:
+  the first unresolved residual-shape bit becomes visible
+```
+
+## PetalBridge Correction
+
+Checkpoint 125 also records a warning in `PetalBridge`:
+
+```text
+carrier nesting is not pressure-prefix nesting
+```
+
+Continuation and retention carriers can be nested, but pressure compares two
+changing masses:
+
+```text
+retention(depth) < 2 * continuation(depth)
+```
+
+The selected depths are therefore governed by the sign of the integer margin:
+
+```text
+SourcePressureMarginInt = 2 * continuation - retention
+```
+
+The new diagnostic predicate is:
+
+```lean
+SourcePressurePrefixFailure
+```
+
+with bridge:
+
+```lean
+sourcePressurePrefixFailure_iff_margin
+```
+
+It records the pattern:
+
+```text
+shallow margin <= 0
+deep margin > 0
+```
+
+This is not a contradiction.  It is a pressure island or pressure obstruction:
+a deeper residual-shape channel can stand up before a shallower pressure
+prefix exists.
+
+## Next Work
+
+The next natural implementation direction is either:
+
+```text
+GnomonEvaluation -> residual-shape bridge to T
+```
+
+or:
+
+```text
+PetalBridge -> pressure failure classification
+```
+
+For the second route, Python experiments should classify failures by:
+
+```text
+first_failure_pair
+shallow_margin
+deep_margin
+margin_jump
+retention_shallow
+retention_deep
+continuation_shallow
+continuation_deep
+retention_drop
+continuation_drop
+```
+
+The Lean side now has a place to store those observations as exact predicates,
+without pretending that pressure selection is automatically prefix-shaped.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
index 2c5d2d32..93f32912 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
@@ -26,6 +26,23 @@ finite orbit segments
 
 `PetalBridge` is the file where these languages meet.
 
+Checkpoint 125 clarifies the module boundary.  The low-level Collatz odd step
+is now read in `DkMath.Collatz.GnomonEvaluation` as:
+
+```text
+odd gnomon correction
+  n + (2n+1) = 3n+1
+
+power-of-two alignment
+  v2 (3n+1)
+
+residual shape
+  (3n+1) / 2^height
+```
+
+`PetalBridge` should not absorb that low-level vocabulary.  Its job is to
+observe finite windows of those shapes and compare finite channel masses.
+
 ## Basic Objects
 
 ### `OrbitWindow`
@@ -66,7 +83,8 @@ This is:
 v2 (3 * oddOrbitLabel n i + 1)
 ```
 
-It is the local 2-adic peeling height.
+It is the local power-of-two alignment height.  In the checkpoint-125 reading,
+this is the window-level view of `RawGnomonHeight`.
 
 ### `orbitWindowHeightSeq`
 
@@ -148,6 +166,35 @@ orbitWindowHeightCountGe_one_eq_window
 
 Every odd accelerated state has height at least `1`.
 
+## Pressure Margins And Prefix Failures
+
+Pressure is not raw carrier membership.  It is the strict comparison:
+
+```text
+retention < 2 * continuation
+```
+
+The integer margin surface is:
+
+```lean
+SourcePressureMarginInt
+isSourcePressureDepth_iff_margin_pos
+```
+
+Checkpoint 125 adds the diagnostic obstruction:
+
+```lean
+SourcePressurePrefixFailure
+sourcePressurePrefixFailure_iff_margin
+not_selectedPressurePrefix_of_prefixFailure
+SourcePressureSelectedSetDownClosed
+downClosed_iff_no_prefixFailure
+```
+
+Use these names when selected depths form a non-prefix sign pattern.  Such a
+case is not an error in the model: it means that a deeper residual-shape
+channel has positive margin while a shallower one does not.
+
 ## Residue Counts
 
 Named residue counts exist for low layers:
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index d5cc5606..4867b67e 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -28,6 +28,13 @@ DkMath.Collatz.Accelerated
 DkMath.Collatz.Shift
   shift
   v2_shift_invariant
+
+DkMath.Collatz.GnomonEvaluation
+  OddGnomonLayer n = 2n + 1
+  RawGnomonStep n = n + (2n+1)
+  RawGnomonHeight n = v2 (RawGnomonStep n)
+  RawGnomonResidualShape n = RawGnomonStep n / 2^height
+  RawGnomonRemainderAtDepth n j
 ```
 
 This means the implemented Collatz side is currently strongest around:
@@ -39,6 +46,9 @@ odd state
 accelerated transition
 orbit segment
 block-shift invariance
+odd gnomon correction
+power-of-two alignment height
+residual shape extraction
 ```
 
 ## Petal Contact Point
@@ -72,6 +82,20 @@ The bridge file is:
 DkMath.Collatz.PetalBridge
 ```
 
+Checkpoint 125 clarifies the module boundary:
+
+```text
+DkMath.Collatz.GnomonEvaluation
+  low-level Collatz gnomon and residual-shape vocabulary
+
+DkMath.Collatz.PetalBridge
+  finite observation windows, residue channels, pressure/margin diagnostics
+```
+
+The reason for the split is practical.  `PetalBridge.lean` is now a large
+observation surface, so new low-level arithmetic terms should not be added
+there unless they genuinely depend on finite windows.
+
 It defines:
 
 ```lean
@@ -94,6 +118,29 @@ orbitWindowHeight n i = v2 (3 * oddOrbitLabel n i + 1)
 orbitWindowHeightSeq n k = the ordered list of the first k height labels
 ```
 
+Checkpoint 125 adds the pressure-obstruction surface:
+
+```lean
+SourcePressurePrefixFailure
+sourcePressurePrefixFailure_lt
+not_isSourcePressureDepth_of_prefixFailure_left
+isSourcePressureDepth_of_prefixFailure_right
+sourcePressurePrefixFailure_iff_margin
+not_selectedPressurePrefix_of_prefixFailure
+SourcePressureSelectedSetDownClosed
+downClosed_iff_no_prefixFailure
+```
+
+These names deliberately avoid the unsafe assumption that selected pressure
+depths are always prefix-shaped.  Pressure is the margin sign condition
+
+```text
+0 < 2 * continuation(depth) - retention(depth)
+```
+
+and this sign can become positive at a deeper depth while remaining
+nonpositive at a shallower depth.
+
 The first theorem set is deliberately thin:
 
 ```lean
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PressureMargin-124.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PressureMargin-124.md
index 722a71a2..a66eb048 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PressureMargin-124.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PressureMargin-124.md
@@ -171,3 +171,28 @@ deeper pressure can be positive while shallower pressure margin is nonpositive
 
 Checkpoint 124 therefore redirects the path from an unconditional prefix theorem
 to margin-controlled pressure-frontier theory.
+
+## Checkpoint 125 Follow-up
+
+Checkpoint 125 implements the obstruction surface suggested here.
+
+New names:
+
+```lean
+SourcePressurePrefixFailure
+sourcePressurePrefixFailure_iff_margin
+not_selectedPressurePrefix_of_prefixFailure
+SourcePressureSelectedSetDownClosed
+downClosed_iff_no_prefixFailure
+```
+
+The intended reading is:
+
+```text
+prefix failure
+  = shallow margin <= 0 and deeper margin > 0
+```
+
+This makes non-prefix pressure profiles first-class data.  Future work should
+classify these failures by margin jump, retention drop, and continuation drop
+before proposing another monotonicity theorem.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-125.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-125.md
new file mode 100644
index 00000000..fc5dbef8
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-125.md
@@ -0,0 +1,237 @@
+# Report Petal 125
+
+## Summary
+
+Checkpoint 125 was a trajectory-correction checkpoint.
+
+The main subject changed from direct `3n+1` language to:
+
+```text
+Odd gnomon correction
+  n + (2n+1) = 3n+1
+
+Power-of-two alignment evaluation
+  v2 (3n+1)
+
+Residual shape extraction
+  (3n+1) / 2^height
+
+Relative scale update
+  the residual odd shape becomes the next state
+```
+
+The existing PetalBridge theorems still apply.  The correction is about the
+reading and the module boundary: low-level Collatz arithmetic now starts in
+`DkMath.Collatz.GnomonEvaluation`, while `DkMath.Collatz.PetalBridge` remains
+the finite observation and pressure/margin layer.
+
+## Code Changes
+
+New file:
+
+```text
+lean/dk_math/DkMath/Collatz/GnomonEvaluation.lean
+```
+
+Implemented definitions:
+
+```lean
+OddGnomonLayer
+RawGnomonStep
+RawGnomonHeight
+RawGnomonResidualShape
+RawGnomonRemainderAtDepth
+FirstFailedPow2Depth
+```
+
+Implemented theorems:
+
+```lean
+rawGnomonStep_eq_three_mul_add_one
+rawGnomonStep_eq_threeNPlusOne
+square_succ_eq_square_add_oddGnomonLayer
+sum_oddGnomonLayer_eq_square
+sum_odd_eq_square
+square_add_eq_square_add_gnomon_sum
+rawGnomonHeight_eq_s
+rawGnomonRemainderAtDepth_eq_zero_of_le_height
+```
+
+Updated integration:
+
+```text
+lean/dk_math/DkMath/Collatz/Collatz2K26.lean
+```
+
+`Collatz2K26` now imports `DkMath.Collatz.GnomonEvaluation` and lists it in
+the package structure comment.
+
+## PetalBridge Correction
+
+`PetalBridge.lean` now has an explicit checkpoint-125 module comment warning:
+
+```text
+carrier nesting is not pressure-prefix nesting
+```
+
+Reason:
+
+```text
+pressure(depth) is not membership.
+pressure(depth) is retention(depth) < 2 * continuation(depth).
+```
+
+Both masses can shrink with depth, but their ratio can change non-monotonically.
+
+New diagnostic predicates/theorems:
+
+```lean
+SourcePressurePrefixFailure
+sourcePressurePrefixFailure_lt
+not_isSourcePressureDepth_of_prefixFailure_left
+isSourcePressureDepth_of_prefixFailure_right
+sourcePressurePrefixFailure_iff_margin
+not_selectedPressurePrefix_of_prefixFailure
+SourcePressureSelectedSetDownClosed
+downClosed_iff_no_prefixFailure
+```
+
+The core equivalence is:
+
+```text
+SourcePressurePrefixFailure
+  <-> j1 < j2 and margin(j1) <= 0 and 0 < margin(j2)
+```
+
+This turns the observed prefix failure into a Lean object rather than a loose
+Python note.
+
+## Documentation Changes
+
+Updated:
+
+```text
+lean/dk_math/DkMath/Collatz/README.md
+lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+lean/dk_math/DkMath/Collatz/docs/Collatz-PressureMargin-124.md
+```
+
+Added:
+
+```text
+lean/dk_math/DkMath/Collatz/docs/Collatz-GnomonEvaluation-125.md
+```
+
+The documentation now records:
+
+```text
+raw step = odd gnomon correction
+height = power-of-two alignment depth
+accelerated odd label = residual shape / next relative scale
+sumS = cumulative power-of-two alignment evaluation
+```
+
+## Verification
+
+Commands run:
+
+```text
+lake build DkMath.Collatz.GnomonEvaluation
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath.Collatz.Collatz2K26
+rg -n "\bsorry\b" touched Collatz Lean files
+git diff --check -- tracked touched files
+rg -n "[ \t]$" new files
+```
+
+All passed.  The `sorry` search found no new `sorry` in
+`GnomonEvaluation.lean` or `PetalBridge.lean`.
+
+Known unrelated build warning still appears when `PetalBridge` dependencies
+replay:
+
+```text
+DkMath.NumberTheory.ZsigmondyCyclotomicResearch declaration uses sorry
+```
+
+This warning is outside the Collatz checkpoint.
+
+## Inference
+
+The most important correction is that the prefix hypothesis should not be the
+default target.  The safer target is:
+
+```text
+classify pressure sign patterns
+```
+
+In particular:
+
+```text
+pressure frontier:
+  first place where margin becomes positive
+
+pressure island:
+  positive margin not forming a prefix
+
+pressure obstruction:
+  shallow margin <= 0 and deep margin > 0
+```
+
+The Lean side now has the predicate for the third case.
+
+## Suggested Next Implementation
+
+Two routes are natural.
+
+### Route A: residual-shape bridge
+
+Connect `RawGnomonResidualShape` to the accelerated map:
+
+```lean
+RawGnomonResidualShape n.1 = (T n).1
+```
+
+or a named bridge with the exact existing `T` spelling.
+
+This likely needs the existing `padicValNat` maximality / division facts, not
+ad-hoc arithmetic.
+
+### Route B: failure classification
+
+Add finite predicates for pressure islands/frontiers:
+
+```lean
+SourcePressureIsland
+SourcePressureFrontier
+FirstSourcePressureFailurePair
+```
+
+Before proving strong theorems, extend the Python scan with:
+
+```text
+first_failure_pair
+shallow_margin
+deep_margin
+margin_jump
+retention_shallow
+retention_deep
+continuation_shallow
+continuation_deep
+retention_drop
+continuation_drop
+```
+
+Then choose the next Lean theorem based on the observed failure type.
+
+## Recommendation
+
+Prefer Route A first if the reviewer wants the new gnomon reading tied more
+tightly to the old Collatz core.
+
+Prefer Route B first if the reviewer wants to continue the pressure-profile
+experiment.
+
+Both routes are now separated cleanly enough that they can progress without
+making `PetalBridge.lean` absorb more low-level arithmetic vocabulary.
````
`````
