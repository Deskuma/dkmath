# Git diff / Report / Review

## Upd: Analysis.DkReal.Semantic

gch: 8d93afe3ce21321cafd416887b5c86fa3e0e67fe

## Report

レビュー修正と次段階を完了しました。

実装内容:

- `widthReal` と幅のゼロ収束
- semantic point の一意性
- `Equiv` に対する semantic value の不変性
- `DkNNRealQ.semanticValue` への quotient lift
- rational、`0`、`1`、加法の semantic 保存
- 公開 import の計算可能性説明を修正
- タスク書・現場履歴を更新

```text
lake build DkMath.Analysis.DkReal DkMath.Analysis DkMath
Build completed successfully (8565 jobs).
```

`git diff --check` も通過。次は乗法、自然数冪、順序の semantic bridge です。

## Review

## 1. 総評

ぬしよ、これは **かなり良い進捗** じゃ。前回レビューで指摘した「幅のゼロ収束」「semantic point の一意性」「`Equiv` 不変性」「quotient descent」まで、ほぼそのまま正しい順で閉じておる。

報告上も、今回の追加は `widthReal`、幅のゼロ収束、semantic point の一意性、`Equiv` 不変性、`DkNNRealQ.semanticValue` への lift、rational / `0` / `1` / 加法の保存まで含み、`lake build DkMath.Analysis.DkReal DkMath.Analysis DkMath` と `git diff --check` が通過している。

判定は **採用でよい** 。
これはもう「semantic bridge 開始」ではなく、 **DkReal から Mathlib `Real` への quotient-compatible semantic map が成立した段階** じゃ。

## 2. 特に良い点

一番良いのは、`eq_semanticValue_of_mem_all_intervals` の置き方じゃ。

任意の候補点 \(r\) と `semanticValue x` がすべての近似区間に入るなら、

$$
|r-\operatorname{semanticValue}(x)|\le \operatorname{widthReal}(x,n)
$$

を示し、右辺が \(0\) に収束するので \(r=\operatorname{semanticValue}(x)\) とする。これは王道で、かつ DkReal の「区間幅が潰れる」という表現不変量をそのまま使っている。実装でも `squeeze_zero` と `tendsto_widthReal_zero` で閉じており、証明の構造がよい。

次に、`semanticValue_eq_of_equiv` が良い。`equiv_tendsto_lo_sub_zero` から rational lower endpoint の差が \(0\) に収束することを取り、`Rat.continuous_coe_real` で `Real` に移し、両 lower sequence の極限一意性で semantic value の一致を出している。これは前回想定したルートそのものじゃ。

さらに `DkNNRealQ.semanticValue` を `Quotient.liftOn` で定義し、その well-definedness を `DkReal.semanticValue_eq_of_equiv` に依存させた点も正しい。代表元独立を先に閉じてから quotient に降ろしているので、構造が綺麗じゃ。

## 3. 加法保存の評価

`DkReal.semanticValue_add` はかなり美しい。

証明は、

$$
\operatorname{semanticValue}(x)+\operatorname{semanticValue}(y)
$$

が `add x y` のすべての近似区間に入ることを示し、一意性補題で semantic value と同一視している。これは「演算結果の endpoint と semantic point の interval membership」を使う、今後の乗法・冪にも使える型じゃ。

このパターンは一般化できる。

```lean
semanticValue_op
  = 期待される Real 側の値が全 output interval に入る
  -> eq_semanticValue_of_mem_all_intervals
```

つまり、今後の `mulNonneg`、`powNonneg`、`q2` 保存でも、まず「期待値が全近似区間に入る」を示せばよい。

## 4. 小さな注意点

一点だけ、将来の保守性として注意じゃ。

`Semantic.lean` が `DkNNRealQ` まで含むようになったので、ファイル名 `Semantic.lean` の責務が少し広がっている。まだ許容範囲だが、今後 `mul`、`pow`、`order`、`q2` まで入るなら、分割を考えた方がよい。

候補はこうじゃ。

```text
DkReal/Semantic.lean
  lowerReal / upperReal / semanticValue / uniqueness / Equiv invariance

DkReal/SemanticQ.lean
  DkNNRealQ.semanticValue / quotient lift / constants / add / mul / pow / order
```

あるいは、

```text
DkReal/BridgeReal.lean
```

に quotient 側を移す。
設計ドラフトでも `BridgeReal.lean` は DkReal から Mathlib `Real` への意味論写像の場所として想定されていたので、長期的にはこの分離が綺麗じゃ。DkMath.Analysis の設計では、計算可能表現層と semantic bridge 層を分ける方針が明確に置かれている。

ただし今すぐ分割必須ではない。今は momentum を優先してよい。

## 5. 次の実装順序

次は報告通り、乗法、自然数冪、順序でよい。
ただし順番は、わっちならこうする。

```text
1. DkReal semantic multiplication on nonnegative quadrant
2. DkNNRealQ semantic multiplication
3. DkReal powNonneg semantic preservation
4. DkNNRealQ natural power preservation
5. order preservation
6. order reflection は最後
7. CF2D q2 semantic bridge
```

理由は、`pow` は `mul` の繰り返しとして行ける可能性があるからじゃ。ただ、既存の `powNonneg` がすでに強いなら、`powNonneg` を先に semantic bridge してもよい。

自然数冪については、過去のマイルストーンで、非負 DkReal の stagewise power は rational endpoints 上の有限演算として閉じ、幅収束も GapGN の有界性で示されている。つまり semantic bridge に進む材料は揃っている。

## 6. 次の補題案

乗法はまず representation 側でこう欲しい。

```lean
theorem DkReal.semanticValue_mulNonneg
    (x y : DkNNReal) :
    DkReal.semanticValue (DkReal.mulNonneg x.val y.val ?hx ?hy)
      = DkReal.semanticValue x.val * DkReal.semanticValue y.val
```

実際の名前は既存 API に合わせるとして、証明方針は加法と同じじゃ。

$$
\operatorname{semanticValue}(x)\in [x.lo_n,x.hi_n]
$$

$$
\operatorname{semanticValue}(y)\in [y.lo_n,y.hi_n]
$$

かつ非負なら、積は

$$
\operatorname{semanticValue}(x)\operatorname{semanticValue}(y)
\in [x.lo_n y.lo_n,\;x.hi_n y.hi_n]
$$

に入る。よって一意性で落とす。

その後 quotient 側。

```lean
theorem DkNNRealQ.semanticValue_mul
    (x y : DkNNRealQ) :
    semanticValue (x * y) = semanticValue x * semanticValue y
```

これは `Quotient.inductionOn₂` で加法と同様に行けるはずじゃ。

## 7. 順序 bridge の注意

順序は「保存」と「反映」を分けるべきじゃ。

まず保存。

```lean
theorem semanticValue_le_of_le
    {x y : DkNNRealQ} :
    x ≤ y -> semanticValue x ≤ semanticValue y
```

これは asymptotic order の定義から比較的自然に出るはず。

反映は重い。

```lean
theorem le_of_semanticValue_le
    {x y : DkNNRealQ} :
    semanticValue x ≤ semanticValue y -> x ≤ y
```

これは DkReal の order 定義が「最終的に endpoint で分離できる」形なら可能だが、等号近傍や overlap が絡む。最初から狙うと重くなるので、保存を先に閉じるのがよい。

特に CF2D の初期 consumer は、順序反映まで要求しないはずじゃ。必要なのは保存量 `q2` が semantic map で壊れないことじゃからの。

## 8. CF2D への接続評価

今回で、CF2D Phase 2 への橋が現実になった。

以前の三角関数実装では、核は

$$
Q(x,y)=x^2+y^2
$$

と

$$
(a,b)\star(x,y)=(ax-by,ay+bx)
$$

であり、`UnitKernel` が \(Q\) を保存する、という代数層だった。設計ドラフトでも、`DkMath.Analysis` はここから「保存核を連続パラメータで走査する層」へ進むと整理されている。

つまり次の第一 consumer はこれでよい。

```text
DkNNRealQ semantic map preserves:
  addition
  multiplication
  natural powers

therefore preserves:
  q2(x,y) = x^2 + y^2
```

これが閉じれば、

```text
DkReal / DkNNRealQ 上の保存核
  -> Mathlib Real 上の保存核
```

という橋ができる。角度復元、連続性、周期性、微分はその後でよい。

## 9. 最終判定

今回の実装は **かなり重要な到達点** じゃ。

```text
DkReal representation
  -> semanticValue : DkReal -> Real
  -> uniqueness
  -> Equiv invariance
  -> DkNNRealQ quotient lift
  -> constants and addition preservation
```

ここまで進んだ。
これは単なる補題追加ではなく、DkReal が「計算可能区間表現」と「標準 Real 意味論」の二重構造を持ち始めた瞬間じゃ。

わっちのレビュー結論はこうじゃ。

**採用。次は非負乗法と自然数冪を semantic bridge へ載せる。順序反映は焦らず、まず保存を閉じる。CF2D へは `q2` semantic preservation を最初の接続点にするのが最短で堅い。**

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 16978094..f35740b1 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -31,8 +31,9 @@ Public entry point for the complete Route B algebraic checkpoint:
 * `DkReal.CanonicalOrder` extracts nonnegative Gap universes.
 * `DkReal.Semantic` begins the noncomputable bridge to Mathlib's `Real`.
 
-All endpoint operations in this import tree remain computable. No represented
-limit in Mathlib's `Real` or `NNReal` is selected here.
+All endpoint operations in the representation modules remain computable. The
+publicly imported optional `Semantic` module selects a Mathlib `Real` value
+noncomputably; it does not alter the computable representation operations.
 
 `DkReal.Order` defines a quotient-compatible asymptotic order and installs a
 `PartialOrder` and Mathlib's semiring-level `IsOrderedRing` predicate on
@@ -68,12 +69,12 @@ a linear order.
 decision procedure for asymptotic interval order is currently available.
 Classical comparison should therefore remain an explicit local choice.
 
-`DkReal.Semantic` now selects the lower-endpoint supremum and proves that it
-lies in every approximation interval.
+`DkReal.Semantic` selects the lower-endpoint supremum, proves that it is the
+unique real point lying in every approximation interval, and proves invariance
+under representation equivalence.
 
-[TODO: semantic-bridge] Prove that semantic evaluation is independent of
-representatives, then lift it to `DkNNRealQ` and establish arithmetic and order
-bridge laws.
+[TODO: semantic-bridge] Lift semantic evaluation to `DkNNRealQ` and establish
+arithmetic and order bridge laws.
 
 [TODO: signed-arithmetic] General signed multiplication requires the minimum and maximum of four
 endpoint products and belongs outside the current nonnegative API.
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/Semantic.lean b/lean/dk_math/DkMath/Analysis/DkReal/Semantic.lean
index bf310158..4c39c9bf 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/Semantic.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/Semantic.lean
@@ -4,7 +4,7 @@ Released under MIT license as described in the file LICENSE.
 Authors: D. and Wise Wolf.
 -/
 
-import DkMath.Analysis.DkReal.Equiv
+import DkMath.Analysis.DkReal.DkNNRealQ
 
 #print "file: DkMath.Analysis.DkReal.Semantic"
 
@@ -20,14 +20,12 @@ endpoint bounds it. Consequently the supremum lies in every approximation
 interval.
 
 This file deliberately stops before quotient descent and arithmetic
-preservation. Those require representative independence of `semanticValue`.
-
-[TODO: semantic/equiv] Prove
-`DkReal.Equiv x y -> semanticValue x = semanticValue y`.
+preservation. Representative independence of `semanticValue` is proved here
+as the final representation-level bridge.
 
 [TODO: semantic/quotient] Lift the value through `DkNNRealQ`, then prove
-preservation of zero, one, addition, nonnegative multiplication, powers, and
-order.
+preservation of nonnegative multiplication, powers, and order. Quotient
+descent, rational constants, and addition are established below.
 -/
 
 namespace DkMath.Analysis.DkReal
@@ -42,6 +40,10 @@ def lowerReal (x : DkMath.Analysis.DkReal) (n : ℕ) : ℝ :=
 def upperReal (x : DkMath.Analysis.DkReal) (n : ℕ) : ℝ :=
   (x.interval n).hi
 
+/-- Width of an approximation interval, interpreted in Mathlib's `Real`. -/
+def widthReal (x : DkMath.Analysis.DkReal) (n : ℕ) : ℝ :=
+  upperReal x n - lowerReal x n
+
 /-- Cast lower endpoints form a monotone real sequence. -/
 theorem lowerReal_monotone (x : DkMath.Analysis.DkReal) :
     Monotone (lowerReal x) := by
@@ -97,11 +99,153 @@ theorem semanticValue_mem_interval
     semanticValue x ∈ Set.Icc (lowerReal x n) (upperReal x n) :=
   ⟨lowerReal_le_semanticValue x n, semanticValue_le_upperReal x n⟩
 
+/-- Cast interval widths tend to zero. -/
+theorem tendsto_widthReal_zero (x : DkMath.Analysis.DkReal) :
+    Filter.Tendsto (widthReal x) Filter.atTop (nhds 0) := by
+  have hcast :=
+    Rat.continuous_coe_real.continuousAt.tendsto.comp x.tendsto_width_zero
+  convert hcast using 1
+  · funext n
+    simp [widthReal, upperReal, lowerReal, GapInterval.width]
+  · simp
+
 /-- Cast lower endpoints converge monotonically to the semantic value. -/
 theorem tendsto_lowerReal_semanticValue (x : DkMath.Analysis.DkReal) :
     Filter.Tendsto (lowerReal x) Filter.atTop (nhds (semanticValue x)) := by
   exact tendsto_atTop_ciSup (lowerReal_monotone x) (bddAbove_range_lowerReal x)
 
+/--
+The semantic value is the unique real point contained in every approximation
+interval.
+
+Both candidate points lie in each interval, so their distance is bounded by
+that interval's width. The widths tend to zero.
+-/
+theorem eq_semanticValue_of_mem_all_intervals
+    (x : DkMath.Analysis.DkReal) (r : ℝ)
+    (hr : ∀ n, r ∈ Set.Icc (lowerReal x n) (upperReal x n)) :
+    r = semanticValue x := by
+  have hbound :
+      ∀ n, |r - semanticValue x| ≤ widthReal x n := by
+    intro n
+    have hs := semanticValue_mem_interval x n
+    rcases hr n with ⟨hrlo, hrhi⟩
+    rcases hs with ⟨hslo, hshi⟩
+    rw [abs_sub_le_iff]
+    constructor <;> simp only [widthReal] <;> linarith
+  have hzero :
+      Filter.Tendsto (fun _ : ℕ => |r - semanticValue x|)
+        Filter.atTop (nhds 0) :=
+    squeeze_zero (fun _ => abs_nonneg _) hbound (tendsto_widthReal_zero x)
+  have heq : |r - semanticValue x| = 0 :=
+    tendsto_nhds_unique tendsto_const_nhds hzero
+  exact sub_eq_zero.mp (abs_eq_zero.mp heq)
+
+/--
+Equivalent interval representations select the same semantic real.
+
+The rational lower-endpoint difference tends to zero by representation
+equivalence. Continuity of the rational embedding transfers that convergence
+to `Real`, while the two lower-endpoint sequences converge to their respective
+semantic values.
+-/
+theorem semanticValue_eq_of_equiv
+    {x y : DkMath.Analysis.DkReal} (hxy : Equiv x y) :
+    semanticValue x = semanticValue y := by
+  have hxyRat := equiv_tendsto_lo_sub_zero hxy
+  have hxyReal :
+      Filter.Tendsto
+        (fun n => lowerReal x n - lowerReal y n)
+        Filter.atTop (nhds 0) := by
+    have hcast :=
+      Rat.continuous_coe_real.continuousAt.tendsto.comp hxyRat
+    convert hcast using 1
+    · funext n
+      simp [lowerReal]
+    · simp
+  have hsemantic :
+      Filter.Tendsto
+        (fun n => lowerReal x n - lowerReal y n)
+        Filter.atTop (nhds (semanticValue x - semanticValue y)) :=
+    (tendsto_lowerReal_semanticValue x).sub
+      (tendsto_lowerReal_semanticValue y)
+  have hzero : semanticValue x - semanticValue y = 0 :=
+    tendsto_nhds_unique hsemantic hxyReal
+  exact sub_eq_zero.mp hzero
+
+/-- Embedded rationals have their expected semantic value. -/
+@[simp]
+theorem semanticValue_ofRat (q : ℚ) :
+    semanticValue (DkMath.Analysis.DkReal.ofRat q) = q := by
+  symm
+  apply eq_semanticValue_of_mem_all_intervals
+  intro n
+  simp [lowerReal, upperReal]
+
+/-- Semantic evaluation preserves representation addition. -/
+theorem semanticValue_add
+    (x y : DkMath.Analysis.DkReal) :
+    semanticValue (add x y) = semanticValue x + semanticValue y := by
+  symm
+  apply eq_semanticValue_of_mem_all_intervals
+  intro n
+  have hx := semanticValue_mem_interval x n
+  have hy := semanticValue_mem_interval y n
+  constructor
+  · simpa [lowerReal, add_interval, addApprox] using add_le_add hx.1 hy.1
+  · simpa [upperReal, add_interval, addApprox] using add_le_add hx.2 hy.2
+
 end
 
 end DkMath.Analysis.DkReal
+
+namespace DkMath.Analysis.DkNNRealQ
+
+noncomputable section
+
+/--
+Semantic evaluation of a quotient-backed nonnegative DkMath real.
+
+Representative independence follows from
+`DkReal.semanticValue_eq_of_equiv`.
+-/
+def semanticValue (x : DkNNRealQ) : ℝ :=
+  Quotient.liftOn x
+    (fun a => DkReal.semanticValue a.val)
+    (fun _ _ h => DkReal.semanticValue_eq_of_equiv h)
+
+/-- Semantic evaluation computes on quotient constructors. -/
+@[simp]
+theorem semanticValue_mk (x : DkNNReal) :
+    semanticValue (mk x) = DkReal.semanticValue x.val := rfl
+
+/-- Embedded nonnegative rationals have their expected semantic value. -/
+@[simp]
+theorem semanticValue_ofRat (q : ℚ) (hq : 0 ≤ q) :
+    semanticValue (ofRat q hq) = q :=
+  DkReal.semanticValue_ofRat q
+
+/-- Quotient zero evaluates to real zero. -/
+@[simp]
+theorem semanticValue_zero :
+    semanticValue 0 = 0 := by
+  change semanticValue (ofRat 0 le_rfl) = 0
+  simp
+
+/-- Quotient one evaluates to real one. -/
+@[simp]
+theorem semanticValue_one :
+    semanticValue 1 = 1 := by
+  change semanticValue (ofRat 1 zero_le_one) = 1
+  simp
+
+/-- Semantic evaluation preserves quotient addition. -/
+theorem semanticValue_add (x y : DkNNRealQ) :
+    semanticValue (x + y) = semanticValue x + semanticValue y := by
+  refine Quotient.inductionOn₂ x y ?_
+  intro x y
+  exact DkReal.semanticValue_add x.val y.val
+
+end
+
+end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index bacfe9ab..07175bac 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -123,8 +123,9 @@ Order:
 
 BridgeNNReal / BridgeReal:
   semanticValue now selects the lower-endpoint supremum
-  next prove representative independence and uniqueness
-  prove semiring-homomorphism laws
+  uniqueness and representative independence are proved
+  DkNNRealQ evaluation, rational constants, and addition are proved
+  next prove multiplication, powers, and order bridge laws
   compare semantic equality with DkReal.Equiv
 ```
 
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
index 55714625..40adf995 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
@@ -36,14 +36,19 @@ DkReal representation
 ## Current Implementation Step
 
 `DkMath.Analysis.DkReal.Semantic` implements the lower-endpoint supremum,
-boundedness, interval membership, and monotone convergence.
+boundedness, interval membership, width convergence, uniqueness, monotone
+endpoint convergence, and invariance under `DkReal.Equiv`.
 
-The next obligation is representative independence. It should use:
+The next obligation is quotient descent:
 
 ```text
-equiv_tendsto_lo_sub_zero
-tendsto_lowerReal_semanticValue
-uniqueness of limits in Real
+DkNNRealQ.semanticValue
+map_zero
+map_one
+map_add
+map_mul
+map_pow
+order preservation and reflection
 ```
 
 No global decidable comparison or `LinearOrder` instance is needed.
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index 42589462..281b7a14 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -114,3 +114,32 @@ Archive
    - 全区間に属する実数点の一意性を証明する。
    - `Equiv x y -> semanticValue x = semanticValue y` を証明する。
    - その後 `DkNNRealQ` へ semantic map を降ろす。
+
+### 2026/06/21 20:28 JST (Semantic uniqueness and quotient descent)
+
+1. 目的:
+   - review-trig-046 の指摘を反映し、semantic point の一意性と
+     representative independence を閉じる。
+   - `DkNNRealQ` へ semantic evaluation を降ろす。
+2. 実施:
+   - `widthReal` と `tendsto_widthReal_zero` を追加した。
+   - 全 approximation interval に属する実数点の一意性を証明した。
+   - `Equiv x y -> semanticValue x = semanticValue y` を証明した。
+   - `DkNNRealQ.semanticValue` を quotient lift として定義した。
+   - rational constants、zero、one、addition の semantic 保存を証明した。
+   - 公開 import の計算可能性説明を semantic module 付きの現状へ修正した。
+3. 結論:
+   - DkReal representation から Mathlib Real への写像が quotient-compatible
+     になった。
+   - 次の解析本線は nonnegative multiplication、power、order bridge である。
+4. 検証:
+   - `lake build DkMath.Analysis.DkReal.Semantic` 成功。
+5. 失敗事例:
+   - rational-to-real cast の composed function が簡約されず、関数外延性で
+     cast 前後の式を明示的に一致させた。
+   - quotient zero/one は `rfl` では閉じず、rational evaluation theorem を
+     経由した。
+6. 次の課題:
+   - semantic multiplication と natural power preservation。
+   - internal order と Mathlib Real order の保存・反映。
+   - 保存量 `q2` の semantic bridge を最初の CF2D consumer とする。
````
`````
