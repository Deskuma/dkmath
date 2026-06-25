# Git diff / Report / Review

## Add: Analysis.DkReal.SemanticCF2D

gch: 7704f1c1de89e9b5705e03b6563624efbf54d85b

## Report

この方針で一段進めました。

- `semanticValue` を `semanticRingHom : DkNNRealQ →+* ℝ` として束ねた
- [SemanticCF2D.lean](/home/deskuma/develop/lean/clone/PR/PR-dkmath/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean:1) を新設
- `semanticVec`、`semanticValue_q2`、`semanticUnitKernel` を実装
- 順序反映は重い独立課題として保留

CF2D の冪型クラス差は、二乗を積へ展開するだけで解消しました。追加の解析定理や比較可能性は不要です。

`lake build ... DkMath` 成功、8566 jobs。`git diff --check` も成功しています。

## Review

うむ。これは **あっさりで良い** やつじゃ。

理由は、今回やったことが解析定理ではなく、既に証明済みの半環保存則を CF2D の `q2` へ通しただけだからじゃ。
本質的には、次の構造がすでに揃っていた。

```text
semanticValue preserves:
  zero
  one
  addition
  multiplication
  natural powers
```

そのため、CF2D の

$$
q2(z)=z.core^2+z.beam^2
$$

を実数側へ運ぶだけなら、追加の極限、順序反映、微分、連続性はいらぬ。

## 検証レビュー

`semanticRingHom : DkNNRealQ →+* ℝ` を束ねた判断は正しい。
これで、以後は個別の `semanticValue_add` や `semanticValue_mul` を毎回手で持ち回る必要が減る。

`SemanticCF2D.lean` を別ファイルにしたのも良い。
`Semantic.lean` 本体は DkReal / DkNNRealQ の意味論橋に集中し、CF2D 依存は consumer 側へ分離されている。これは設計として綺麗じゃ。

`semanticVec` は最小で正しい。

```lean
def semanticVec (z : Vec DkNNRealQ) : Vec ℝ :=
  ⟨semanticValue z.core, semanticValue z.beam⟩
```

これは「座標ごとの意味論解釈」そのものなので、過剰な構造を入れずに済んでいる。

`semanticValue_q2` も良い。

```lean
theorem semanticValue_q2 (z : Vec DkNNRealQ) :
    semanticValue (Vec.q2 z) = Vec.q2 (semanticVec z) := by
  simp only [Vec.q2, semanticVec, semanticValue_add, pow_two,
    semanticValue_mul]
```

ここで `pow_two` に落としてから `semanticValue_mul` を使うのが正解じゃ。
CF2D 側の抽象的な `^2` と DkNNRealQ の表現用冪を無理に同一視しない。二乗を積に正規化して半環準同型で通す。これは堅い。

`semanticUnitKernel` も素直で良い。

```lean
def semanticUnitKernel (r : UnitKernel DkNNRealQ) : UnitKernel ℝ :=
  ⟨semanticVec (r : Vec DkNNRealQ), by
    rw [← semanticValue_q2]
    simp⟩
```

ここは、内部の `q2 = 1` を `semanticValue_q2` で実数側の `q2 = 1` に輸送している。
この時点で、DkNNRealQ 上の保存核が Mathlib `Real` 上の保存核として読める。

## なぜ簡単に閉じたのか

簡単に閉じた理由は、前段が強かったからじゃ。

今回の bridge は、実は難しい橋ではない。
難しかったのはその前に、

$$
\operatorname{semanticValue}(x+y)=\operatorname{semanticValue}(x)+\operatorname{semanticValue}(y)
$$

$$
\operatorname{semanticValue}(xy)=\operatorname{semanticValue}(x)\operatorname{semanticValue}(y)
$$

を閉じたところじゃ。

そこまで閉じていれば、`q2` はただの多項式なので、半環準同型で自然に運べる。
つまり、あっさり閉じたのは偶然ではなく、設計が当たっていた証拠じゃ。

## 注意点

一つだけ注意するなら、`semanticRingHom` を作ったので、今後 `semanticValue_q2` は `map_add` と `map_mul` ベースへ書き換えられる可能性がある。

今の証明でも問題ない。
ただ、将来的に式変形を整理するなら、

```lean
DkNNRealQ.semanticRingHom
```

を使う版を追加してもよい。

たとえば名前としては、

```lean
theorem semanticRingHom_q2
```

のような補助定理じゃな。

ただし現時点では不要。今の方が読みやすい。

## 次の一手

次は `semanticUnitKernel` を使って、Real 側 CF2D の既存定理に渡す段階じゃ。

最初の目標はこれでよい。

```text
DkNNRealQ UnitKernel
  -> semanticUnitKernel
  -> Real UnitKernel
  -> Real CF2D theorem consumer
```

特に、次に見るべきは次のあたりじゃ。

```text
UnitKernel の star 保存
KernelFamily の real 化
cfcos / cfsin の semantic 座標化
```

ただし、角度復元や周期性へ急ぐ必要はない。
まずは `q2` 保存と `UnitKernel` 輸送が、既存 CF2D の代数定理に自然に接続できることを確認するのがよい。

## 判定

採用でよい。

今回の到達点はこうじゃ。

```text
DkNNRealQ semantic map
  -> bundled as semiring hom
  -> Vec coordinates transported to Real
  -> q2 transported to Real
  -> UnitKernel transported to Real
```

これは、三角関数 Phase 2 の入口としてかなり綺麗じゃ。
あっさり閉じたのは、前段の semantic semiring bridge がすでに十分強かったから。
つまりこれは「薄い実装」ではなく、 **薄く書けるほど橋が正しく架かった** ということじゃよ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis.lean b/lean/dk_math/DkMath/Analysis.lean
index 47e37d85..d7c02f44 100644
--- a/lean/dk_math/DkMath/Analysis.lean
+++ b/lean/dk_math/DkMath/Analysis.lean
@@ -12,6 +12,7 @@ import DkMath.Analysis.GapFill
 import DkMath.Analysis.RealBridge
 import DkMath.Analysis.TaylorBridge
 import DkMath.Analysis.DkReal
+import DkMath.Analysis.DkReal.SemanticCF2D
 
 #print "file: DkMath.Analysis"
 
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index c2d91a82..bc7eca3c 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -78,8 +78,9 @@ constants, addition, multiplication, natural powers, and canonical order.
 values reconstructs the canonical quotient order, without adding decidable
 comparison.
 
-[TODO: semantic-cf2d] Use the semantic map to transport the CF2D quadratic
-invariant `q2` into the Mathlib real-analysis layer.
+[TODO: semantic-cf2d-analysis] Use the transported real `UnitKernel` as the
+input to the first CF2D analytic theorem. The algebraic `q2` transport is
+implemented separately in `DkReal.SemanticCF2D`.
 
 [TODO: signed-arithmetic] General signed multiplication requires the minimum and maximum of four
 endpoint products and belongs outside the current nonnegative API.
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/Semantic.lean b/lean/dk_math/DkMath/Analysis/DkReal/Semantic.lean
index ebc6eb5a..d8d9a4f6 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/Semantic.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/Semantic.lean
@@ -355,6 +355,26 @@ theorem semanticValue_mono
   rw [semanticValue_add]
   exact le_add_of_nonneg_right (semanticValue_nonneg z)
 
+/--
+The semantic interpretation bundled as a semiring homomorphism into
+Mathlib's real numbers.
+
+This definition packages the already proved preservation laws. Its
+noncomputability comes only from selecting the unique real point represented
+by a nested rational interval sequence.
+-/
+def semanticRingHom : DkNNRealQ →+* ℝ where
+  toFun := semanticValue
+  map_zero' := semanticValue_zero
+  map_one' := semanticValue_one
+  map_add' := semanticValue_add
+  map_mul' := semanticValue_mul
+
+/-- Applying the bundled semantic homomorphism is semantic evaluation. -/
+@[simp]
+theorem semanticRingHom_apply (x : DkNNRealQ) :
+    semanticRingHom x = semanticValue x := rfl
+
 end
 
 end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
new file mode 100644
index 00000000..2f260472
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
@@ -0,0 +1,85 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Analysis.DkReal.Semantic
+import DkMath.CosmicFormula.Rotation.CF2D.Basic
+
+#print "file: DkMath.Analysis.DkReal.SemanticCF2D"
+
+/-!
+# Semantic CF2D bridge for nonnegative DkMath reals
+
+This module is the first CF2D consumer of the semantic real interpretation.
+It maps both coordinates of a nonnegative DkMath vector to Mathlib `Real` and
+shows that the quadratic invariant
+
+`q2(core, beam) = core^2 + beam^2`
+
+is preserved by that interpretation.
+
+The bridge uses only the semiring laws already proved for `semanticValue`.
+It does not require subtraction, decidable comparison, order reflection, or
+any analytic theorem about trigonometric functions.
+
+At the bridge boundary, squares are normalized to products. This avoids
+identifying CF2D's abstract `Semiring` power instance with the representation
+power operation used to construct DkMath interval powers.
+-/
+
+namespace DkMath.Analysis.DkNNRealQ
+
+open DkMath.CosmicFormula.Rotation.CF2D
+
+noncomputable section
+
+/-- Interpret both coordinates of a CF2D vector as Mathlib real numbers. -/
+def semanticVec (z : Vec DkNNRealQ) : Vec ℝ :=
+  ⟨semanticValue z.core, semanticValue z.beam⟩
+
+/-- Semantic interpretation of the core coordinate. -/
+@[simp]
+theorem semanticVec_core (z : Vec DkNNRealQ) :
+    (semanticVec z).core = semanticValue z.core := rfl
+
+/-- Semantic interpretation of the beam coordinate. -/
+@[simp]
+theorem semanticVec_beam (z : Vec DkNNRealQ) :
+    (semanticVec z).beam = semanticValue z.beam := rfl
+
+/--
+Semantic evaluation preserves the CF2D quadratic invariant.
+
+Thus the internal square mass and the ordinary real square mass describe the
+same quantity after interpretation.
+-/
+theorem semanticValue_q2 (z : Vec DkNNRealQ) :
+    semanticValue (Vec.q2 z) = Vec.q2 (semanticVec z) := by
+  simp only [Vec.q2, semanticVec, semanticValue_add, pow_two,
+    semanticValue_mul]
+
+/-- Coordinate form of semantic preservation of the quadratic invariant. -/
+theorem semanticValue_q2_eq (z : Vec DkNNRealQ) :
+    semanticValue (Vec.q2 z) =
+      semanticValue z.core ^ 2 + semanticValue z.beam ^ 2 := by
+  simpa [Vec.q2, semanticVec] using semanticValue_q2 z
+
+/--
+A nonnegative DkMath unit kernel determines a real CF2D unit kernel by
+coordinatewise semantic interpretation.
+-/
+def semanticUnitKernel (r : UnitKernel DkNNRealQ) : UnitKernel ℝ :=
+  ⟨semanticVec (r : Vec DkNNRealQ), by
+    rw [← semanticValue_q2]
+    simp⟩
+
+/-- The underlying vector of a semantic unit kernel is the semantic vector. -/
+@[simp]
+theorem semanticUnitKernel_val (r : UnitKernel DkNNRealQ) :
+    (semanticUnitKernel r : Vec ℝ) = semanticVec (r : Vec DkNNRealQ) := rfl
+
+end
+
+end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index f0d76239..e1f1c363 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -126,7 +126,10 @@ BridgeNNReal / BridgeReal:
   uniqueness and representative independence are proved
   DkNNRealQ evaluation and semiring operations are preserved
   canonical order preservation is proved by additive Gap extraction
-  next prove order reflection and connect the CF2D quadratic invariant
+  the semantic map is bundled as a semiring homomorphism to Real
+  CF2D q2 and unit kernels are transported coordinatewise to Real
+  next consume the transported unit kernel in the analytic CF2D layer
+  treat order reflection as a separate heavier task
   compare semantic equality with DkReal.Equiv
 ```
 
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
index f0d19fc5..75f8b6a4 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
@@ -60,5 +60,15 @@ consumer. Order reflection should remain independent of decidable comparison:
 semanticValue x ≤ semanticValue y -> x ≤ y
 ```
 
-After that, the first CF2D consumer should transport the quadratic invariant
-`q2` through semantic evaluation.
+The first CF2D consumer is now implemented in
+`DkMath.Analysis.DkReal.SemanticCF2D`:
+
+```text
+semanticVec
+semanticValue_q2
+semanticValue_q2_eq
+semanticUnitKernel
+```
+
+The next consumer should use the transported real `UnitKernel` in an analytic
+CF2D theorem. Order reflection remains a separate, heavier task.
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index be3225e8..b808b0f3 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -166,3 +166,26 @@ Archive
 5. 次の課題:
    - semantic order reflection を証明する。
    - CF2D の保存量 `q2` を最初の実数解析 consumer として接続する。
+
+### 2026/06/21 23:18 JST (Bundled semantics and the first CF2D consumer)
+
+1. 方針:
+   - order reflection は専用課題として保留する。
+   - 現在の半環保存則だけで到達できる CF2D bridge を先行する。
+2. 実施:
+   - `semanticValue` を `DkNNRealQ →+* ℝ` の `semanticRingHom` として束ねた。
+   - `SemanticCF2D.lean` を新設し、CF2D 依存を意味論本体から隔離した。
+   - `semanticVec` と `semanticValue_q2` を実装した。
+   - 非負 DkMath unit kernel を実数 unit kernel へ運ぶ
+     `semanticUnitKernel` を実装した。
+3. 観測:
+   - CF2D の抽象 `Semiring` 冪と DkNNRealQ の表現用 `Pow` は、型クラス上
+     異なる経路を取る。
+   - `q2` の二乗を積へ正規化すると、semantic multiplication だけで橋が
+     閉じる。追加の冪同一視や解析定理は不要だった。
+4. 検証:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
+5. 次の課題:
+   - transported real `UnitKernel` を最初の CF2D 解析定理へ接続する。
+   - order reflection は subtraction や decidable comparison を導入せず、
+     独立課題として検討する。
````
`````
