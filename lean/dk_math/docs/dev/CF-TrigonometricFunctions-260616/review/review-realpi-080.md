# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DRefinement

gch: 94a57048d7cf32c7a7a57f6068c48b6b4de96784

## Report

有限 defect 集約層を完成させました。

- `dyadicPhaseDepthDefect` を定義
- defect の正値性
- 範囲付き odd-child refinement
- odd child が親平均より厳密に低いこと
- 全 odd-child defect の有限和 `1 / (2 * 2^n)`

`lake build DkMath.Analysis` 成功（8291 jobs）、`git diff --check` 成功です。

## Review

うむ、これは前回レビューで挙げた「有限 defect 集約層」が、そのまま綺麗に閉じておる。
わっちの判定では、今回の差分は **かなり良い確定マイルストーン** じゃ。

## 1. 総評

今回の実装で、`SemanticCF2DRefinement` は単なる odd-child 局所法則から一段進み、 **有限 refinement defect の観測層** になった。

今回そろったものは次じゃな。

```text
dyadicPhaseDepthDefect
  局所 defect の名前化

dyadicPhaseDepthDefect_pos
  defect の正値性

dyadicPhaseDepth_child_odd_of_lt
  mesh 内 parent interval としての意味付け

dyadicPhaseDepth_child_odd_lt_average
  odd child が親平均より低いこと

sum_dyadicPhaseDepthDefect
  level n+1 の全 odd-child defect 総和
```

これで、有限 dyadic refinement の局所くぼみが、

$$
    \frac{1}{2(2^n)^2}
$$

として現れ、それが \(2^n\) 個集まることで、

$$
    \frac{1}{2\cdot 2^n}
$$

になる、という有限集約則まで Lean 側で固定されたわけじゃ。

これは **収束定理ではないが、収束定理が見るべきスケールを完全に露出させた** という意味で、とても良い。

## 2. 数学的な意味

今回の主役は、局所 defect と全体 defect の階層差じゃ。

局所 defect は、

$$
    \mathrm{defect}_n=\frac{1}{2(2^n)^2}
$$

で、これは mesh 幅 \(1/2^n\) の二乗スケールを持つ。
つまり、まさに二次関数 `phaseDepth` の曲率由来の欠損じゃ。

一方、level \(n+1\) で導入される odd child は \(2^n\) 個ある。
よって有限総量は、

$$
    2^n\cdot\frac{1}{2(2^n)^2}=\frac{1}{2\cdot 2^n}
$$

になる。

ここが重要じゃ。
局所では二乗で小さくなり、個数は一次で増える。だから総 defect は一次スケールで小さくなる。

これは CF2D の pre-geometric 観測としてかなり美しい。

```text
局所 defect:
  mesh^2

個数:
  mesh^{-1}

総 defect:
  mesh
```

という構造じゃな。

## 3. 実装レビュー

`dyadicPhaseDepthDefect` を定義したのは正解じゃ。

以前の形では、定理の右辺に直接

```lean
1 / (2 * (dyadicPhaseDenom n : ℝ) ^ 2)
```

が埋め込まれていた。
今回これを名前化したことで、次の correction composition や finite table 化に進みやすくなった。

`dyadicPhaseDepthDefect_pos` も良い。
証明は素直で、`dyadicPhaseDenom_pos` を実数へ持ち上げ、平方の正値性と積の正値性から `one_div_pos` で閉じている。過剰な補題もなく、読みやすい。

`dyadicPhaseDepth_child_odd_of_lt` は、実体としては既存定理への alias じゃが、これは意味論上とても価値がある。
代数的には範囲外 \(k\) でも式は成り立つが、「genuine odd child」と呼べるのは \(k<2^n\) のときじゃ。この theorem があることで、後続で mesh 内部の議論を書きやすくなる。

`dyadicPhaseDepth_child_odd_lt_average` は研究物語として非常に強い。
等式だけでは「補正がある」としか言えぬが、不等式になると、

```text
odd child は親平均より必ず低い
```

と明確に言える。
これは、ぬしが言っていた「境界と合わないくぼみを観測する」流れにぴったり合う。

`sum_dyadicPhaseDepthDefect` も良い。
これはまだ極限ではなく、有限恒等式として押さえている点が正しい。docs 側でも「収束主張ではない」と明記されており、過大主張を避けられている。

## 4. 気になる点

大きな問題は見当たらぬ。ビルド成功報告もあり、このまま通してよい。

ただし、Lean スタイルとしては `sum_dyadicPhaseDepthDefect` の `n` は明示引数にしたほうが読みやすいかもしれぬ。

現在の形は、おそらく Lean の auto implicit により `n` が暗黙に入っている。

```lean
theorem sum_dyadicPhaseDepthDefect :
    ∑ _k ∈ Finset.range (dyadicPhaseDenom n), dyadicPhaseDepthDefect n =
      1 / (2 * (dyadicPhaseDenom n : ℝ)) := by
```

ビルドが通っているなら問題はない。
ただ、プロジェクトの保守性を考えるなら、次の形のほうが親切じゃ。

```lean
theorem sum_dyadicPhaseDepthDefect (n : ℕ) :
    ∑ _k ∈ Finset.range (dyadicPhaseDenom n), dyadicPhaseDepthDefect n =
      1 / (2 * (dyadicPhaseDenom n : ℝ)) := by
```

これは趣味というより、後で検索したときに「この theorem は \(n\) ごとの定理だ」とすぐ読める利点がある。

もう一つ、名前としては `sum_dyadicPhaseDepthDefect` でもよいが、より意味を出すなら、

```lean
theorem sum_oddChild_dyadicPhaseDepthDefect
```

または、

```lean
theorem total_dyadicPhaseDepthDefect
```

のような名前も候補じゃ。
現名でも十分通じるので、これは必須ではない。

## 5. 次に足すと強い theorem

次の一手は、有限総量の消失スケールを扱うことじゃ。

まだ convergence theorem を主張しない判断は正しい。
だが、次の補助定理は入れてよい。

```lean
theorem total_dyadicPhaseDepthDefect_eq :
    1 / (2 * (dyadicPhaseDenom n : ℝ)) =
      1 / (2 * (2 : ℝ) ^ n) := by
  simp [dyadicPhaseDenom]
```

これは表記の整理じゃな。

その次に、別ファイルか後段で、

```text
n が増えると total defect は 0 に向かう
```

を示せる。
ただし、これは `SemanticCF2DRefinement` に即入れるより、`SemanticCF2DLimit` や `SemanticCF2DAsymptotic` 的な層へ分けたほうが綺麗じゃ。

また、累積総量も面白い。

各 level の総 defect は、

$$
    \frac{1}{2\cdot 2^n}
$$

なので、\(n=0\) から無限に足すと形式的には、

$$
    \sum_{n=0}^{\infty}\frac{1}{2\cdot 2^n}=1
$$

になる。
これは今すぐ主張する必要はないが、かなり意味深じゃ。局所くぼみの全階層総量が \(1\) に正規化される可能性がある。Gaussian bridge や normalization composition へ行く前に、有限部分和を先に置くとよさそうじゃ。

有限部分和なら、

$$
    \sum_{i=0}^{m}\frac{1}{2\cdot 2^i}=1-\frac{1}{2^{m+1}}
$$

となる。
この形は、後で境界復元と接続する時に効くかもしれぬ。

## 6. docs 更新について

docs の更新も良い。

特に、

```text
This is an exact finite aggregation law.
It does not yet assert convergence.
```

この注意はかなり大事じゃ。
研究資料では、こういう有限恒等式を見た瞬間に「では極限は？」へ進みたくなるが、Lean 実装では層を分けるべきじゃからな。

`task-trig-continuous-phase-065.md` 側も、TODO が `correction-composition` に移っていて自然じゃ。
今回の実装で depth defect の finite aggregation は閉じた。残る大きな未確定要素は、 **boundary normalization の局所補正をどう合成するか** じゃ。

## 7. このマイルストーンの位置づけ

今回で、CF2D pre-geometric phase は次の段階に入った。

以前は、

```text
dyadic node を置く
reflection がある
even child は親を継承する
odd child は中点である
```

までだった。

今回からは、

```text
odd child は親平均より低い
その低さは明示的 defect である
level 全体の defect 総量も閉じる
```

まで来た。

つまり、単なる mesh 構造ではなく、 **mesh refinement が生む curvature defect の会計** が始まった。

これは解析層として大きい。
極限へ行く前に「有限段階で何が発生しているか」を完全に数え上げている。DkMath らしい、たいへん良い進み方じゃ。

## 8. 結論

この差分は採用でよい。

わっちのレビュー結論はこうじゃ。

```text
実装品質:
  良い。局所 theorem、意味論 theorem、有限集約 theorem の分離ができている。

数学的意味:
  非常に良い。二次 defect と総 defect のスケール差が明確になった。

過大主張:
  なし。収束定理と有限恒等式を分離できている。

次の課題:
  normalization correction composition。
  その前に total defect の表記整理、有限部分和、将来の tendsto 層を検討するとよい。
```

ぬしよ、これはなかなか良い。
「くぼみがある気がする」から、「くぼみは正で、親平均より必ず低く、全体では \(1/(2\cdot 2^n)\) だけ現れる」へ進んだ。

これはもう観測ではなく、有限会計じゃ。
賢狼としても、尻尾を揺らしてよい収穫じゃよ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 7149491a..4da48fa1 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -108,7 +108,10 @@ without selecting a correction product or taking a limit.
 `DkReal.SemanticCF2DRefinement` evaluates depth and normalization on the
 dyadic mesh. Reflection and even-child inheritance hold for both observations.
 At every odd child, quadraticity gives the exact finite correction
-`1 / (2 * (2^n)^2)` from the average of adjacent parent depths.
+`1 / (2 * (2^n)^2)` from the average of adjacent parent depths. This defect
+is positive, so every genuine odd child lies strictly below that average.
+Summing the identical defect over all `2^n` parent intervals gives the exact
+finite total `1 / (2 * 2^n)`.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DRefinement.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DRefinement.lean
index 6714e021..2f1d02ab 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DRefinement.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DRefinement.lean
@@ -34,6 +34,21 @@ def dyadicPhaseDepth (n k : ℕ) : ℝ :=
 def dyadicPhaseNormalization (n k : ℕ) : ℝ :=
   phaseNormalization (dyadicPhaseNode n k)
 
+/--
+The local quadratic defect introduced at every odd child of refinement level
+`n + 1`.
+-/
+def dyadicPhaseDepthDefect (n : ℕ) : ℝ :=
+  1 / (2 * (dyadicPhaseDenom n : ℝ) ^ 2)
+
+/-- The local dyadic depth defect is strictly positive. -/
+theorem dyadicPhaseDepthDefect_pos (n : ℕ) :
+    0 < dyadicPhaseDepthDefect n := by
+  have hdenom : (0 : ℝ) < dyadicPhaseDenom n := by
+    exact_mod_cast dyadicPhaseDenom_pos n
+  apply one_div_pos.mpr
+  exact mul_pos (by norm_num) (sq_pos_of_pos hdenom)
+
 /-- Complementary dyadic nodes have equal boundary depth. -/
 theorem dyadicPhaseDepth_reflect
     {n k : ℕ} (hk : k ≤ dyadicPhaseDenom n) :
@@ -70,14 +85,47 @@ theorem dyadicPhaseDepth_child_odd
     (n k : ℕ) :
     dyadicPhaseDepth (n + 1) (2 * k + 1) =
       (dyadicPhaseDepth n k + dyadicPhaseDepth n (k + 1)) / 2 -
-        1 / (2 * (dyadicPhaseDenom n : ℝ) ^ 2) := by
+        dyadicPhaseDepthDefect n := by
   have hdenom : (dyadicPhaseDenom n : ℝ) ≠ 0 := by
     exact_mod_cast (dyadicPhaseDenom_pos n).ne'
-  simp [dyadicPhaseDepth, dyadicPhaseNode, dyadicPhaseDenom, phaseDepth,
-    pow_succ]
+  simp [dyadicPhaseDepth, dyadicPhaseDepthDefect, dyadicPhaseNode,
+    dyadicPhaseDenom, phaseDepth, pow_succ]
   field_simp
   ring
 
+/--
+The odd-child law restricted to an actual parent interval of the dyadic mesh.
+-/
+theorem dyadicPhaseDepth_child_odd_of_lt
+    {n k : ℕ} (_hk : k < dyadicPhaseDenom n) :
+    dyadicPhaseDepth (n + 1) (2 * k + 1) =
+      (dyadicPhaseDepth n k + dyadicPhaseDepth n (k + 1)) / 2 -
+        dyadicPhaseDepthDefect n :=
+  dyadicPhaseDepth_child_odd n k
+
+/-- Every genuine odd child lies strictly below its adjacent-parent average. -/
+theorem dyadicPhaseDepth_child_odd_lt_average
+    {n k : ℕ} (_hk : k < dyadicPhaseDenom n) :
+    dyadicPhaseDepth (n + 1) (2 * k + 1) <
+      (dyadicPhaseDepth n k + dyadicPhaseDepth n (k + 1)) / 2 := by
+  rw [dyadicPhaseDepth_child_odd n k]
+  exact sub_lt_self _ (dyadicPhaseDepthDefect_pos n)
+
+/--
+The total defect over all odd children introduced at level `n + 1` is
+`1 / (2 * 2^n)`.
+
+There are `2^n` parent intervals, each carrying the same inverse-square local
+defect. This is a finite identity and makes no convergence claim.
+-/
+theorem sum_dyadicPhaseDepthDefect :
+    ∑ _k ∈ Finset.range (dyadicPhaseDenom n), dyadicPhaseDepthDefect n =
+      1 / (2 * (dyadicPhaseDenom n : ℝ)) := by
+  have hdenom : (dyadicPhaseDenom n : ℝ) ≠ 0 := by
+    exact_mod_cast (dyadicPhaseDenom_pos n).ne'
+  simp [dyadicPhaseDepthDefect]
+  field_simp
+
 end
 
 end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
index 02a720c2..35a0cd26 100644
--- a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
+++ b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
@@ -151,8 +151,18 @@ child depth
 ```
 
 Thus the first refinement defect is an explicit positive inverse-square mesh
-term. The remaining task is to identify a mathematically justified aggregate
-composition law for local corrections.
+term. It is now named `dyadicPhaseDepthDefect`; its positivity proves that
+every genuine odd child lies strictly below the adjacent-parent average.
+There are exactly `2^n` such children, and their finite total defect is
+
+```text
+2^n * 1 / (2 * (2^n)^2) = 1 / (2 * 2^n).
+```
+
+This is an exact finite aggregation law. It does not yet assert convergence,
+although its closed form exposes the scale that a later limit theorem must
+analyze. The remaining task is to identify a mathematically justified
+aggregate composition law for boundary normalization.
 
 ### Milestone D: limit and Gaussian bridge
 
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
index 3908f64d..55a12ec5 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
@@ -369,7 +369,9 @@ phase-depth laws.
 `SemanticCF2DRefinement` proves reflection and even-child inheritance for
 dyadic depth and normalization. Quadraticity gives the exact odd-child law:
 its depth is the average adjacent-parent depth minus
-`1 / (2 * (2^n)^2)`.
+`1 / (2 * (2^n)^2)`. The named defect is positive, every genuine odd child
+lies strictly below its parent average, and the finite sum over all odd
+children introduced at that level is exactly `1 / (2 * 2^n)`.
 [TODO: semantic-cf2d-phase/correction-composition] Select and prove an
 aggregate composition law for local boundary corrections. Do not assume that
 it is an infinite product or a logarithmic sum before its finite form is
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index 65e16e80..659147fe 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -809,3 +809,21 @@ Archive
 5. verification:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2DRefinement` 成功
      (8279 jobs)。
+
+### 2026/06/23 19:03 JST (Finite total dyadic depth defect)
+
+1. local defect:
+   - `dyadicPhaseDepthDefect n = 1 / (2 * (2^n)^2)` を定義した。
+   - defect の厳密正値性を証明した。
+2. semantic form:
+   - mesh 内の parent interval に限定した odd-child refinement theorem を
+     追加した。
+   - genuine odd child depth が adjacent-parent average より厳密に小さい
+     ことを証明した。
+3. finite aggregation:
+   - level `n + 1` で導入される全 `2^n` odd children の defect 総和が
+     `1 / (2 * 2^n)` に厳密に等しいことを証明した。
+   - これは有限恒等式であり、収束定理とは区別した。
+4. verification:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2DRefinement` 成功
+     (8279 jobs)。
````
`````
