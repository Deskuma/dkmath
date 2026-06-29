# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DLogComposition

gch: 6ad9930eddae9cc277f8482ba0a4985534bd910a

## Report

進めました。

[SemanticCF2DLogComposition.lean](/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean) に、centered log-depth 台形和の閉形式上界を追加しました。

```lean
theorem dyadicPhaseTrapezoidCenteredLogDepthSum_le_closedQuadraticBound
    (n : ℕ) :
    dyadicPhaseTrapezoidCenteredLogDepthSum n ≤
      1 / 3 + 2 / (3 * (dyadicPhaseDenom n : ℝ) ^ 2)
```

これは既存の

```lean
dyadicPhaseTrapezoidCenteredLogDepthSum_le_centeredQuadraticSum
dyadicPhaseTrapezoidCenteredQuadraticSum_eq
```

を合成したものです。有限段階で、centered log correction が具体的な閉形式上界を持つところまで来ました。まだ極限・積分・Gaussian・`pi` は主張していません。

ドキュメントも更新しました。`dyadicPhaseDenom n = 2^n` も研究メモ側に明記しています。

検証済みです。

```text
lake build DkMath.Analysis.DkReal.SemanticCF2DLogComposition
lake build DkMath.Analysis
git diff --check
```

## Review

うむ、賢狼レビューじゃ。
今回の差分は **採用でよい** 。これは小さな合成定理に見えるが、研究上はかなり大事な橋じゃ。

今回追加された `dyadicPhaseTrapezoidCenteredLogDepthSum_le_closedQuadraticBound` は、既存の `dyadicPhaseTrapezoidCenteredLogDepthSum_le_centeredQuadraticSum` と `dyadicPhaseTrapezoidCenteredQuadraticSum_eq` を合成し、centered log-depth 台形和を有限閉形式 `1 / 3 + 2 / (3 * (dyadicPhaseDenom n : ℝ) ^ 2)` で上から抑える theorem じゃ。報告でも、これは有限段階の closed upper bound であり、極限・積分・Gaussian・`pi` はまだ主張していない、と明確に整理されている。

## 1. 状況解説

前回までで、台形 centered quadratic moment は閉形式で出ていた。

$$
\mathrm{TrapezoidCenteredQuadraticSum}_n=\frac{1}{3}+\frac{2}{3(2^n)^2}
$$

また、centered log-depth は pointwise に centered quadratic で上から支配されていた。

$$
\mathrm{centeredLogPhaseDepth}(t)\le 4\left(t-\frac{1}{2}\right)^2
$$

今回、この二つを合成して、

$$
\mathrm{TrapezoidCenteredLogDepthSum}_n\le\frac{1}{3}+\frac{2}{3(2^n)^2}
$$

まで Lean で閉じた。

つまり、centered log correction の台形観測量が、有限段階で具体的な閉形式上界を持つようになった。

## 2. 数学的な意味

これは、次の流れが完全に繋がったということじゃ。

```text id="kkb7ap"
centered log-depth
  ↓
pointwise quadratic upper bound
  ↓
trapezoidal finite weighted sum
  ↓
finite centered quadratic moment closed form
  ↓
closed upper bound for centered log-depth sum
```

この closed upper bound は、まだ収束定理ではない。
しかし後で極限を取るなら、右辺の補正項

$$
\frac{2}{3(2^n)^2}
$$

が消えて、候補値 \(1/3\) が現れる。

大事なのは、ここで \(1/3\) は積分から借りたものではなく、有限和の閉形式から出ていることじゃ。
これは pre-geometric program の方針に合っている。

## 3. 実装レビュー

実装は非常に素直で良い。

```lean id="uv8muv"
theorem dyadicPhaseTrapezoidCenteredLogDepthSum_le_closedQuadraticBound
    (n : ℕ) :
    dyadicPhaseTrapezoidCenteredLogDepthSum n ≤
      1 / 3 + 2 / (3 * (dyadicPhaseDenom n : ℝ) ^ 2) := by
  calc
    dyadicPhaseTrapezoidCenteredLogDepthSum n
        ≤ dyadicPhaseTrapezoidCenteredQuadraticSum n :=
          dyadicPhaseTrapezoidCenteredLogDepthSum_le_centeredQuadraticSum n
    _ = 1 / 3 + 2 / (3 * (dyadicPhaseDenom n : ℝ) ^ 2) := by
          rw [dyadicPhaseTrapezoidCenteredQuadraticSum_eq]
```

これは理想的な合成 theorem じゃ。
余計な再証明をせず、既存の構造をそのまま使っている。

こういう theorem は後続でかなり便利になる。
「log-depth の台形和は具体的に何で抑えられる？」という問いに、一発で使えるからじゃ。

## 4. 文書更新も良い

研究メモ側で `dyadicPhaseDenom n = 2^n` を明記したのは良い判断じゃ。
Lean 定理は `dyadicPhaseDenom n` で書かれるが、人間の研究文脈では \(2^n\) と読めた方が分かりやすい。

また、今回の文書でも「左辺の収束を主張していない」と明記している。これは重要じゃ。
いま得たのは、

$$
\mathrm{TrapezoidCenteredLogDepthSum}_n\le\frac{1}{3}+\frac{2}{3(2^n)^2}
$$

であって、

$$
\mathrm{TrapezoidCenteredLogDepthSum}_n\to\frac{1}{3}
$$

ではない。
この区別を守っているのが良い。

## 5. 研究上の位置づけ

これは、Gaussian bridge へ行く前の **有限上界層の完成形に近い** 。

これまでの積み上げはこうじゃ。

```text id="wuyudw"
finite affine transition
  ↓
phaseDepth
  ↓
finite log cancellation
  ↓
centered log-depth
  ↓
quadratic upper bound
  ↓
finite quadratic moment closed form
  ↓
closed finite upper bound for log correction
```

ここまで、円も角度も積分も使っていない。
ただし、有限和の中から \(1/3\) への補正付き構造が出ている。

これはかなり良い。
今後、極限層へ移るときにも、何が finite correction なのかが明確に残る。

## 6. 気になる点

大きな問題はない。
ただし、次に極限へ進むなら、命名とファイル分割を少し考えてもよい。

`SemanticCF2DLogComposition.lean` はかなり大きくなってきているはずじゃ。
次に `tendsto` 系や極限補題を増やすなら、

```text id="7lxu8j"
SemanticCF2DLogLimit.lean
```

または、

```text id="azkcl5"
SemanticCF2DMoment.lean
```

のような別ファイルを切るのもありじゃ。

ただ、今はまだ finite theorem が中心なので、このファイルに置いても問題ない。
極限 theorem が増え始めたら分離でよい。

## 7. 次の一手

次は自然に、右辺の極限を証明する段階じゃ。

まずは quadratic bound 側。

$$
\frac{1}{3}+\frac{2}{3(2^n)^2}\to \frac{1}{3}
$$

Lean theorem 候補はこう。

```lean id="uq880w"
theorem tendsto_closedQuadraticBound_one_third :
    Filter.Tendsto
      (fun n : ℕ =>
        1 / 3 + 2 / (3 * (dyadicPhaseDenom n : ℝ) ^ 2))
      Filter.atTop
      (nhds (1 / 3 : ℝ))
```

そして、閉形式定理から、

```lean id="bdu4nk"
theorem tendsto_dyadicPhaseTrapezoidCenteredQuadraticSum_one_third :
    Filter.Tendsto
      dyadicPhaseTrapezoidCenteredQuadraticSum
      Filter.atTop
      (nhds (1 / 3 : ℝ))
```

ここまでは自然じゃ。

ただし、centered log-depth 台形和そのものが \(1/3\) に収束するとはまだ言えない。
上界が \(1/3\) に向かうだけじゃ。下界や squeeze が必要になる。

## 8. その先に必要なもの

centered log-depth の収束を狙うなら、下界が欲しくなる。

現在は、

$$
0\le \log(1+x)\le x
$$

の上界だけがある。

下界候補は例えば、

$$
\log(1+x)\ge \frac{x}{1+x}
$$

または、区間制限つきで、

$$
\log(1+x)\ge x-\frac{x^2}{2}
$$

じゃ。

この \(x\) は、

$$
x=4\left(t-\frac{1}{2}\right)^2
$$

で、単位区間では \(0\le x\le 1\)。
そのため、区間制限つきの良い下界が使える可能性がある。

ただし、いきなり下界へ行く前に、まず quadratic moment の極限 theorem を取るのが自然じゃな。

## 9. 結論

今回の差分は採用でよい。

```text id="h8cu00"
実装:
  良い。既存 theorem の合成で閉形式上界を綺麗に追加している。

数学:
  良い。centered log correction が具体的な有限閉形式で上から制御された。

研究位置:
  重要。finite quadratic moment から log correction bound へ橋が架かった。

安全性:
  良い。極限、積分、Gaussian、pi は未主張。

次:
  closed quadratic bound の 1/3 への tendsto、
  quadratic moment 自体の tendsto、
  その後に centered log-depth の下界検討。
```

ぬしよ、これは良い。
いまや centered log correction は、ただの観測量ではなく、有限閉形式の上界を持つ量になった。

次に \(1/3\) への極限を Lean で押さえれば、「有限から極限へ」の扉が開く。
ただし、log-depth 本体の極限はまだ焦らぬことじゃ。まずは支配する二次モーメントの極限から固めるのが賢い。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 33e4b575..5e662057 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -162,7 +162,8 @@ finite moment estimate is also available: the trapezoidal centered quadratic
 sum is bounded by one. The finite trapezoidal centered quadratic moment is
 now evaluated exactly as
 `1 / 3 + 2 / (3 * (dyadicPhaseDenom n : ℝ)^2)`, exposing the finite correction
-to the later `1 / 3` target without taking a limit.
+to the later `1 / 3` target without taking a limit. The centered log-depth
+trapezoidal sum is consequently bounded above by that same closed expression.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean
index 5270028a..a07d80f4 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean
@@ -920,6 +920,24 @@ theorem dyadicPhaseTrapezoidCenteredQuadraticSum_eq (n : ℕ) :
           field_simp [hdenom]
           ring
 
+/--
+Closed finite upper bound for the trapezoidal centered log-depth sum.
+
+This combines the pointwise logarithmic estimate with the exact trapezoidal
+centered quadratic moment. It is still a finite-level theorem; no limiting
+integral, Gaussian law, or `pi` identification is used.
+-/
+theorem dyadicPhaseTrapezoidCenteredLogDepthSum_le_closedQuadraticBound
+    (n : ℕ) :
+    dyadicPhaseTrapezoidCenteredLogDepthSum n ≤
+      1 / 3 + 2 / (3 * (dyadicPhaseDenom n : ℝ) ^ 2) := by
+  calc
+    dyadicPhaseTrapezoidCenteredLogDepthSum n
+        ≤ dyadicPhaseTrapezoidCenteredQuadraticSum n :=
+          dyadicPhaseTrapezoidCenteredLogDepthSum_le_centeredQuadraticSum n
+    _ = 1 / 3 + 2 / (3 * (dyadicPhaseDenom n : ℝ) ^ 2) := by
+          rw [dyadicPhaseTrapezoidCenteredQuadraticSum_eq]
+
 /--
 For centered log-depth, the plain mesh-width and trapezoidal sums differ by
 the restored endpoint correction `h_n * log 2`.
diff --git a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
index 0798f76e..9e7a5a28 100644
--- a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
+++ b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
@@ -322,11 +322,26 @@ dyadicPhaseTrapezoidCenteredQuadraticSum n
   = 1/3 + 2/(3 * (2^n)^2).
 ```
 
+Here `2^n` is Lean's `dyadicPhaseDenom n`. The code states the theorem with
+`dyadicPhaseDenom n`, and the equality `dyadicPhaseDenom n = 2^n` is the
+definition of the dyadic denominator.
+
 The proof stays finite. It first evaluates the complete-node mesh-width
 quadratic moment by elementary first-power and square-sum formulas, then
 subtracts the trapezoidal endpoint correction. This exposes the finite
 correction to the later `1/3` target without invoking an integral or a limit.
 
+Combining this closed quadratic moment with the pointwise logarithmic upper
+bound gives the finite centered log-depth estimate
+
+```text
+dyadicPhaseTrapezoidCenteredLogDepthSum n
+  <= 1/3 + 2/(3 * (2^n)^2).
+```
+
+This is still only a finite inequality. It does not assert convergence of the
+left-hand side.
+
 ### Milestone D: limit and Gaussian bridge
 
 1. Prove convergence of the refinement correction.
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
index 4b63cb10..125c178a 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
@@ -47,7 +47,9 @@ trapezoidal corollaries. These are finite quadratic-moment controls only; no
 Gaussian, integral, angle, or `pi` interpretation is selected here. The first
 trapezoidal centered quadratic moment bound is now `<= 1`, and its exact
 finite value is
-`1/3 + 2/(3 * (dyadicPhaseDenom n : Real)^2)`.
+`1/3 + 2/(3 * (dyadicPhaseDenom n : Real)^2)`. Here
+`dyadicPhaseDenom n = 2^n`. The trapezoidal centered log-depth sum is bounded
+above by the same closed finite expression.
 
 The current implementation proves a four-state return:
 
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index 70428be8..0edcbc63 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -1154,3 +1154,25 @@ Archive
 5. verification:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2DLogComposition` 成功
      (8281 jobs)。
+
+### 2026/06/27 14:40 JST (Centered log-depth closed quadratic bound)
+
+1. API:
+   - `dyadicPhaseTrapezoidCenteredLogDepthSum_le_closedQuadraticBound` を
+     追加した。
+2. finite estimate:
+   - 既存の
+     `dyadicPhaseTrapezoidCenteredLogDepthSum_le_centeredQuadraticSum` と
+     `dyadicPhaseTrapezoidCenteredQuadraticSum_eq` を合成し、
+     centered log-depth の台形和を
+     `1 / 3 + 2 / (3 * (dyadicPhaseDenom n : ℝ) ^ 2)` で上から抑えた。
+3. documentation:
+   - `dyadicPhaseDenom n = 2^n` を研究メモ側に明記した。
+   - public `DkReal.lean` comment、continuous phase task、pre-geometric
+     pi research note を同期した。
+4. interpretation:
+   - まだ極限、積分、Gaussian、`pi` identification は主張していない。
+     これは finite-level closed upper bound である。
+5. verification:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2DLogComposition` 成功
+     (8281 jobs)。
````
`````
