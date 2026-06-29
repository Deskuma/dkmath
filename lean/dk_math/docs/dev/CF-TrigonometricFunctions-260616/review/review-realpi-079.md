# Git diff / Report / Review

## Add: Analysis.DkReal.SemanticCF2DRefinement

gch: 151099f5dcef9d41076014a0ed570d9b7a1b786b

## Report

有限 depth refinement law を実装しました。

- 奇数子節点の範囲付き定理を追加
- `SemanticCF2DRefinement.lean` を新設
- depth・normalization の反射則と even-child 継承
- odd-child depth の正確な二次補正則を証明
- 資料・TODO・履歴を同期

`lake build DkMath.Analysis` 成功（8291 jobs）、`git diff --check` 成功です。

## Review

ぬしよ、今回の差分は **かなり良い節目** じゃ。

## 1. 総評

今回の実装は、`SemanticCF2DDyadic` で作った有限 dyadic mesh の観測を、次の段階へ進めたものじゃな。

追加された核はこれじゃ。

\[
    \mathrm{depth}_{n+1,2k+1}=\frac{\mathrm{depth}_{n,k}+\mathrm{depth}_{n,k+1}}{2}-\frac{1}{2(2^n)^2}
\]

これはとても良い。
理由は、まだ極限も Gaussian も correction product も選んでいない段階で、 **有限 depth refinement の局所欠損量** を完全に代数で捕まえているからじゃ。

添付差分でも、今回の追加は `SemanticCF2DRefinement.lean` の新設、depth と normalization の dyadic 観測、reflection、even-child inheritance、odd-child depth の二次補正則、さらに関連 docs と history の同期まで含まれている。`lake build DkMath.Analysis` と `git diff --check` も成功した報告になっておる。

わっちの判定では、これは **採用してよい実装** じゃ。

## 2. 数学的な意味づけ

今回の実装で得たものは、有限 mesh 上の「深さの曲率」じゃ。

even child は親ノードそのものを細分化後も再現する。

\[
    \mathrm{depth}_{n+1,2k}=\mathrm{depth}_{n,k}
\]

一方、odd child は親区間の中点に相当するので、単なる平均にはならぬ。`phaseDepth` が二次関数であるため、中点値は隣接親ノード深度の平均から、明示的な補正量だけ下がる。

\[
    \mathrm{depth}_{n+1,2k+1}=\frac{\mathrm{depth}_{n,k}+\mathrm{depth}_{n,k+1}}{2}-\frac{1}{2(2^n)^2}
\]

ここが非常に重要じゃ。

これは「平均化して滑らかになる」ではなく、 **平均化すると必ず有限 mesh の二次欠損が出る** という観測になっている。
つまり、pre-geometric な「くぼみ」が、ここで初めて数式として固定された。

DkMath.Analysis の設計書では、Gap、Body、GN を使って離散観測点の間を補正核で埋める方針が立っていた。今回の refinement law は、その思想の CF2D phase-depth 版にかなり近い。標準実数解析を置き換えるのではなく、DkMath の語彙で解析対象を再構成する層として `DkMath.Analysis` を整備する、という設計方針とも整合しておる。

## 3. 実装として良い点

第一に、ファイルの切り方が良い。
`SemanticCF2DDyadic` にさらに詰め込まず、`SemanticCF2DRefinement` を新設したのは正しい。Dyadic node の基本事実と、その上の refinement law を分けられている。

第二に、まだ aggregate correction を選んでいない点が良い。
docs 側でも、infinite product、log sum、Gaussian limit を未選択のまま残している。これはとても大事じゃ。今回の定理は有限法則であり、極限法則ではない。その境界を越えていないのは健全じゃ。

第三に、normalization も同じ観測対象として定義している点が良い。
現時点では odd-child normalization の補正式までは出していないが、depth と normalization を同じ mesh 上の observable として揃えたので、次の段階で correction composition を比較できる。

第四に、`dyadicPhaseNode_child_odd_mem_unitInterval` を追加したのもよい。
odd child を「本物の親区間の中点」として扱うには、範囲条件 \(k<2^n\) が必要になる。ここを先に入れたことで、後続の semantic theorem が書きやすくなる。

## 4. 注意点と改善候補

一つ目。`dyadicPhaseDepth_child_odd` は現在、任意の \(k\) で証明されている。
これは代数恒等式としては問題ない。`dyadicPhaseNode` が単なる有理的な実数ノードとして定義されているなら、範囲外の \(k\) でも式自体は成立するからじゃ。

ただし、意味論的には「adjacent parent depths」と呼ぶには \(k<2^n\) が欲しい。
したがって、今の theorem は代数版として残し、別名で範囲付き版を追加すると綺麗じゃ。

```lean
theorem dyadicPhaseDepth_child_odd_of_lt
    {n k : ℕ} (hk : k < dyadicPhaseDenom n) :
    dyadicPhaseDepth (n + 1) (2 * k + 1) =
      (dyadicPhaseDepth n k + dyadicPhaseDepth n (k + 1)) / 2 -
        1 / (2 * (dyadicPhaseDenom n : ℝ) ^ 2) := by
  exact dyadicPhaseDepth_child_odd n k
```

この薄い theorem でも価値がある。
「mesh 内の本物の odd child」という意味を型の上に刻めるからじゃ。

二つ目。補正項の正値性を別 theorem にすると、次の composition law へ進みやすい。

例えば次が欲しい。

```lean
theorem dyadicPhaseDepth_child_odd_correction_pos
    (n : ℕ) :
    0 < 1 / (2 * (dyadicPhaseDenom n : ℝ) ^ 2) := by
  ...
```

さらに、odd child は平均より小さい、という形も有用じゃ。

```lean
theorem dyadicPhaseDepth_child_odd_lt_average
    (n k : ℕ) :
    dyadicPhaseDepth (n + 1) (2 * k + 1) <
      (dyadicPhaseDepth n k + dyadicPhaseDepth n (k + 1)) / 2 := by
  ...
```

これは「くぼみ」の定理名として非常に強い。
今は等式が主役だが、研究物語では不等式のほうが直感に刺さる。

三つ目。`noncomputable section` は現状許容でよいが、将来的には分けてもよい。
`phaseNormalization` が実数の平方根や逆数などを使うなら noncomputable が必要かもしれぬ。一方、`dyadicPhaseDepth` だけなら代数的に computable 寄りかもしれない。

DkReal の非負自然冪 milestone では、有限観測と有理端点演算に閉じる限り `noncomputable` を不要にできる、という原則が立っていた。今回の semantic layer は Mathlib `ℝ` 観測なので `noncomputable` が混ざるのは自然だが、将来 `DkReal` 側へ持ち上げるときは depth-only と normalization を分ける価値がある。

四つ目。docs の text formula は問題ないが、研究資料側では correction の記号を早めに名前化するとよい。

例えば概念名として、

```text
dyadicDepthDefect n = 1 / (2 * (2^n)^2)
```

または Lean 側で、

```lean
def dyadicPhaseDepthDefect (n : ℕ) : ℝ :=
  1 / (2 * (dyadicPhaseDenom n : ℝ) ^ 2)
```

を置くと、後続が読みやすくなる。

すると主定理はこう読める。

```lean
dyadicPhaseDepth_child_odd :
  dyadicPhaseDepth (n + 1) (2 * k + 1) =
    (dyadicPhaseDepth n k + dyadicPhaseDepth n (k + 1)) / 2 -
      dyadicPhaseDepthDefect n
```

このほうが「局所補正量を合成する」という次の課題へ自然につながる。

## 5. 次に実装すると良い定理

次は、単発の odd-child law から、有限深度全体の補正総量へ向かう準備じゃ。

おすすめ順はこれじゃ。

1. `dyadicPhaseDepthDefect` を定義する。

2. `dyadicPhaseDepthDefect_pos` と `dyadicPhaseDepthDefect_eq` を追加する。

3. `dyadicPhaseDepth_child_odd_eq_average_sub_defect` の名前で主定理を再表現する。

4. odd child が平均より小さい theorem を追加する。

5. 深度 \(n\) の全 odd child correction の有限和を定義する。

有限和としては、まず次の形が見える。

\[
    \sum_{k=0}^{2^n-1}\frac{1}{2(2^n)^2}=\frac{1}{2\cdot 2^n}
\]

これは非常に良い。
局所 defect は \(1/(2(2^n)^2)\) で、odd child は \(2^n\) 個ある。合計すると \(1/(2\cdot 2^n)\) になる。つまり refinement が深くなるほど、全 odd defect の総量は \(0\) へ落ちる。

これは Gaussian へ行く前の **有限補正総量の消失則** になる。

## 6. 研究上の位置づけ

今回の実装は、DkMath.Analysis の中でかなり象徴的じゃ。

これまでは、

\[
    (u+\delta)^d-u^d=\delta\,GapGN_d(u,\delta)
\]

のように、Gap 伸長を GN で完全補正する流れが主軸だった。
今回は CF2D の phase-depth 側で、dyadic refinement による局所補正が

\[
    \frac{1}{2(2^n)^2}
\]

として出た。

つまり、これは GN 型の冪差分補正とは別系統の、 **二次曲率による mesh refinement 補正** じゃ。

ここから先は、二つの道が見える。

第一の道は、finite law を積み上げて、深度ごとの補正総量を評価する道。

第二の道は、normalization と接続して、境界復元の correction composition を選ぶ道。

今の段階で product や log sum を仮定していないのは本当に良い。
まず有限和、有限積、有限 defect table を作って、その形を見てから aggregate law を選ぶべきじゃ。

## 7. レビュー結論

この差分は通してよい。

特に良い点は、以下じゃ。

1. `SemanticCF2DRefinement` の分離が正しい。

2. odd-child depth の補正項が完全に有限代数で証明されている。

3. aggregate correction を未選択にしており、過大主張していない。

4. docs と history が実装内容に同期している。

5. `DkMath.Analysis` の設計思想、つまり「連続や極限へ行く前に有限観測の補正核を固定する」という方針に合っている。

修正必須の問題は見当たらぬ。
ただし次の小改良は強く推奨じゃ。

`dyadicPhaseDepthDefect` を定義し、正値性、平均より小さい theorem、範囲付き odd-child theorem、有限和の補正総量 theorem を足すと、次の correction composition へかなり進みやすくなる。

ぬしよ、今回の実装は「円である」と言う前に、mesh のくぼみを手で触っている段階じゃ。
そしてそのくぼみが、ついに \(1/(2(2^n)^2)\) という硬い形で捕まった。これは良い収穫じゃよ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis.lean b/lean/dk_math/DkMath/Analysis.lean
index 7b1fa6d2..3549fe81 100644
--- a/lean/dk_math/DkMath/Analysis.lean
+++ b/lean/dk_math/DkMath/Analysis.lean
@@ -15,6 +15,7 @@ import DkMath.Analysis.DkReal
 import DkMath.Analysis.DkReal.SemanticCF2D
 import DkMath.Analysis.DkReal.SemanticCF2DPhase
 import DkMath.Analysis.DkReal.SemanticCF2DDyadic
+import DkMath.Analysis.DkReal.SemanticCF2DRefinement
 import DkMath.Analysis.DkReal.SemanticCF2DPath
 import DkMath.Analysis.DkReal.SemanticCF2DNormalize
 import DkMath.CosmicFormula.Rotation.CF2D.EuclideanPhase
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index aa8167f7..7149491a 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -104,6 +104,12 @@ phase at the finite nodes `k / 2^n`. Endpoint, unit-interval, reflection,
 even-child, odd-child midpoint, and reflected phase-depth laws are proved
 without selecting a correction product or taking a limit.
 
+[IMPLEMENTED: semantic-cf2d-finite-refinement]
+`DkReal.SemanticCF2DRefinement` evaluates depth and normalization on the
+dyadic mesh. Reflection and even-child inheritance hold for both observations.
+At every odd child, quadraticity gives the exact finite correction
+`1 / (2 * (2^n)^2)` from the average of adjacent parent depths.
+
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
 affine edge as a Mathlib `Path`. Four seam-compatible edges concatenate to a
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DDyadic.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DDyadic.lean
index 30ca097b..6c382e86 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DDyadic.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DDyadic.lean
@@ -89,6 +89,18 @@ theorem dyadicPhaseNode_child_odd_mid (n k : ℕ) :
   simp [dyadicPhaseNode, dyadicPhaseDenom, pow_succ]
   ring
 
+/--
+For a genuine parent interval, its odd child midpoint lies in the closed
+phase interval.
+-/
+theorem dyadicPhaseNode_child_odd_mem_unitInterval
+    {n k : ℕ} (hk : k < dyadicPhaseDenom n) :
+    dyadicPhaseNode (n + 1) (2 * k + 1) ∈ Set.Icc (0 : ℝ) 1 := by
+  apply dyadicPhaseNode_mem_unitInterval
+  simp only [dyadicPhaseDenom] at hk ⊢
+  rw [pow_succ]
+  omega
+
 /-- The exact phase-depth observation agrees at complementary dyadic nodes. -/
 theorem phaseDepth_dyadic_reflect
     {n k : ℕ} (hk : k ≤ dyadicPhaseDenom n) :
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DRefinement.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DRefinement.lean
new file mode 100644
index 00000000..6714e021
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DRefinement.lean
@@ -0,0 +1,83 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Analysis.DkReal.SemanticCF2DDyadic
+import DkMath.Analysis.DkReal.SemanticCF2DNormalize
+
+#print "file: DkMath.Analysis.DkReal.SemanticCF2DRefinement"
+
+/-!
+# Finite observations under dyadic phase refinement
+
+This module evaluates the exact phase-depth and boundary-normalization
+profiles on the finite dyadic mesh. It records the laws forced by the mesh
+before choosing any aggregate correction.
+
+The key new identity concerns an odd child. Since `phaseDepth` is quadratic,
+its value at the midpoint of adjacent parent nodes is their average depth
+minus an explicit positive mesh correction. This is a finite algebraic
+refinement law, not an asymptotic or Gaussian statement.
+-/
+
+namespace DkMath.Analysis.DkNNRealQ
+
+noncomputable section
+
+/-- The exact boundary-depth factor observed at a dyadic phase node. -/
+def dyadicPhaseDepth (n k : ℕ) : ℝ :=
+  phaseDepth (dyadicPhaseNode n k)
+
+/-- The boundary-restoring normalization observed at a dyadic phase node. -/
+def dyadicPhaseNormalization (n k : ℕ) : ℝ :=
+  phaseNormalization (dyadicPhaseNode n k)
+
+/-- Complementary dyadic nodes have equal boundary depth. -/
+theorem dyadicPhaseDepth_reflect
+    {n k : ℕ} (hk : k ≤ dyadicPhaseDenom n) :
+    dyadicPhaseDepth n (dyadicPhaseDenom n - k) =
+      dyadicPhaseDepth n k := by
+  exact phaseDepth_dyadic_reflect hk
+
+/-- An even child retains the exact depth of its parent. -/
+@[simp]
+theorem dyadicPhaseDepth_child_even (n k : ℕ) :
+    dyadicPhaseDepth (n + 1) (2 * k) = dyadicPhaseDepth n k := by
+  simp [dyadicPhaseDepth]
+
+/-- Complementary dyadic nodes require the same boundary normalization. -/
+theorem dyadicPhaseNormalization_reflect
+    {n k : ℕ} (hk : k ≤ dyadicPhaseDenom n) :
+    dyadicPhaseNormalization n (dyadicPhaseDenom n - k) =
+      dyadicPhaseNormalization n k := by
+  rw [dyadicPhaseNormalization, dyadicPhaseNormalization,
+    dyadicPhaseNode_reflect hk, phaseNormalization_one_sub]
+
+/-- An even child retains the exact normalization of its parent. -/
+@[simp]
+theorem dyadicPhaseNormalization_child_even (n k : ℕ) :
+    dyadicPhaseNormalization (n + 1) (2 * k) =
+      dyadicPhaseNormalization n k := by
+  simp [dyadicPhaseNormalization]
+
+/--
+The odd-child depth is the average of adjacent parent depths minus the exact
+quadratic mesh correction `1 / (2 * (2^n)^2)`.
+-/
+theorem dyadicPhaseDepth_child_odd
+    (n k : ℕ) :
+    dyadicPhaseDepth (n + 1) (2 * k + 1) =
+      (dyadicPhaseDepth n k + dyadicPhaseDepth n (k + 1)) / 2 -
+        1 / (2 * (dyadicPhaseDenom n : ℝ) ^ 2) := by
+  have hdenom : (dyadicPhaseDenom n : ℝ) ≠ 0 := by
+    exact_mod_cast (dyadicPhaseDenom_pos n).ne'
+  simp [dyadicPhaseDepth, dyadicPhaseNode, dyadicPhaseDenom, phaseDepth,
+    pow_succ]
+  field_simp
+  ring
+
+end
+
+end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
index 90557e2f..02a720c2 100644
--- a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
+++ b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
@@ -139,7 +139,19 @@ This finite checkpoint is now implemented in `SemanticCF2DDyadic.lean`.
 Even child indices recover their parent nodes exactly, while odd child
 indices are the midpoints of adjacent parents. Complementary indices produce
 the reflected parameter `1 - t`, and therefore have equal `phaseDepth`.
-The remaining refinement-law task is to identify a mathematically justified
+
+`SemanticCF2DRefinement.lean` now adds the first exact observation law.
+Depth and normalization are inherited by even children and preserved by
+reflection. At an odd child, the quadratic profile satisfies
+
+```text
+child depth
+  = average of adjacent parent depths
+    - 1 / (2 * (2^n)^2).
+```
+
+Thus the first refinement defect is an explicit positive inverse-square mesh
+term. The remaining task is to identify a mathematically justified aggregate
 composition law for local corrections.
 
 ### Milestone D: limit and Gaussian bridge
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
index 89f61ed7..3908f64d 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
@@ -365,9 +365,15 @@ explicit.
 `SemanticCF2DDyadic` defines the finite nodes `k / 2^n`, proves their endpoint,
 unit-interval, reflection, even-child, odd-child midpoint, and reflected
 phase-depth laws.
-[TODO: semantic-cf2d-phase/refinement-law] Select and prove the composition
-law for local boundary corrections. Do not assume that it is an infinite
-product or a logarithmic sum before this finite law is established.
+[IMPLEMENTED: semantic-cf2d-phase/finite-depth-refinement]
+`SemanticCF2DRefinement` proves reflection and even-child inheritance for
+dyadic depth and normalization. Quadraticity gives the exact odd-child law:
+its depth is the average adjacent-parent depth minus
+`1 / (2 * (2^n)^2)`.
+[TODO: semantic-cf2d-phase/correction-composition] Select and prove an
+aggregate composition law for local boundary corrections. Do not assume that
+it is an infinite product or a logarithmic sum before its finite form is
+established.
 [TODO: semantic-cf2d-phase/gaussian-limit]
 [TODO: semantic-cf2d-phase/pi-identification]
 ```
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index 230ca15c..65e16e80 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -790,3 +790,22 @@ Archive
 5. verification:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2DDyadic` 成功
      (8275 jobs)。
+
+### 2026/06/23 18:06 JST (Exact finite depth refinement law)
+
+1. correction:
+   - odd child を parent interval として利用する場合の範囲付き
+     unit-interval theorem を追加した。
+2. module:
+   - `DkMath.Analysis.DkReal.SemanticCF2DRefinement` を新設した。
+   - dyadic mesh 上の depth と normalization observation を定義した。
+3. exact laws:
+   - reflection と even-child inheritance を両 observation で証明した。
+   - odd-child depth が adjacent-parent depth の平均から
+     `1 / (2 * (2^n)^2)` を引いた値に厳密に等しいことを証明した。
+4. boundary:
+   - aggregate correction、infinite product、log sum、Gaussian limit は
+     引き続き未選択とした。
+5. verification:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2DRefinement` 成功
+     (8279 jobs)。
````
`````
