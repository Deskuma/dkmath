# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2D

gch: b850e79f136dc22f4e9aef59abe443f8a57b5f7f

## Report

次の段階まで完了しました。

- `SemanticFixed`
- fixed point、period one、minimal period one の同値
- fixed point から任意周期
- 原点が常に fixed point
- `SemanticPositiveFiniteOrder`
- 正有限位数の正倍数伝播
- 正有限位数から全点の minimal period positivity

正有限位数は「正の witness」であり、最小作用位数とは限らない点も明記しました。

全体ビルド成功、8566 jobs。`git diff --check` も成功です。

## Review

うむ。これは良い整理じゃ。
今回で、周期まわりの基礎 API がかなり安全な形で揃った。

状況としては、すでにこうなっておる。

```text
DkNNRealQ 由来 kernel
-> Real 上の q2 保存同型
-> orbit
-> periodic point
-> minimal period
-> fixed point
-> positive finite action order
```

角度も連続性も signed source も使っていない。
それでここまで来たのは、かなり強い。

## 良い点

`SemanticFixed` を Mathlib の `Function.IsFixedPt` に寄せたのは正しい。

```lean
def SemanticFixed
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) : Prop :=
  Function.IsFixedPt (semanticAct r) z
```

これで fixed point、period one、minimal period one が標準 API でつながる。

特に、

```lean
semanticFixed_iff_minimalPeriod_eq_one
```

は大事じゃ。
固定点は「1 回で戻る点」であり、Mathlib の minimal period では \(1\) になる、という整理ができた。

また、原点が常に fixed point であることも自然で良い。

$$
(0,0)
$$

はどの線形作用でも原点に戻る。
これは今後、非零 fixed point 分類をやるときの基準点になる。

## PositiveFiniteOrder の意義

`SemanticFiniteOrder r n` は \(n=0\) でも成立しうる。
0 回反復は恒等写像だからじゃ。

だから、

```lean
def SemanticPositiveFiniteOrder
    (r : UnitKernel DkNNRealQ) (n : ℕ) : Prop :=
  0 < n ∧ SemanticFiniteOrder r n
```

を分けたのは正しい。

これは「正の witness を持つ有限位数」じゃ。
ただし、文書にもある通り、これは最小正位数とは限らない。
この注意も正しい。

たとえば本当の最小位数が \(3\) なら、\(6\) も正有限位数 witness になる。
だから `PositiveFiniteOrder` は「存在証明」であって「分類値」ではない。

## minimal period positivity について

`semanticMinimalPeriod_pos_of_positiveFiniteOrder` は正しい。

正の \(n\) で全点が周期になるなら、任意点に正周期が存在する。
したがって Mathlib の minimal period も正になる。

これは特に、非周期点では minimal period が \(0\) になる Mathlib 規約との切り分けに効いている。

## 注意点

ここまでの定理はすべて「写像反復」の話じゃ。

まだ言っていないものは次。

```text
角度が 2π の有理倍である
三角関数の周期である
連続一パラメータ群である
source 側 kernel family がある
```

これらはまだ先。
今あるのは、Real 側へ輸送された一つの作用 `semanticAct r` の離散反復理論じゃ。

この区別を守っているので、今回の主張は堅い。

## 次の自然な分類

次は、文書にある通り「非零 fixed point の座標分類」が自然じゃ。

作用を

$$
(x,y)\mapsto (C x - S y,\; C y + S x)
$$

と見ると、固定点条件は次の二式になる。

$$
(C-1)x-Sy=0,\quad Sx+(C-1)y=0
$$

ここで \(C^2+S^2=1\)。

この連立の行列式は、

$$
(C-1)^2+S^2=2(1-C)
$$

となる。
したがって \(C\ne 1\) なら固定点は原点だけ。
\(C=1\) なら \(S=0\) なので、作用は恒等写像になる。

つまり次の分類が狙える。

```text
semantic unit kernel が恒等核でないなら、fixed point は原点のみ
semantic unit kernel が恒等核なら、全点 fixed
```

これは角度なしで行ける。
`C = 1` と `S = 0` の座標条件だけでよい。

## 判定

採用でよい。

今回の到達点はこうじゃ。

```text
periodic / fixed / minimal period / finite order
```

が Mathlib の標準 API 上で揃った。
そして、0 回反復で成立してしまう弱い有限位数と、正の witness を持つ有限位数を分けた。
ここはかなり丁寧で良い。

次は非零固定点の分類がよい。
これは今の API の最初の実質的な幾何定理になるはずじゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 9caea3e3..cee454fa 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -87,7 +87,8 @@ these maps are equivalences of the plane and of each level set. Their finite
 iterates generate forward orbits of constant square mass. Periodic points and
 finite action order are expressed through Mathlib's standard discrete-dynamics
 API. Minimal periods use Mathlib's zero-for-aperiodic convention and divide
-all known return times.
+all known return times. Fixed points and positive finite action order are
+separated from the weaker zero-iterate-compatible periodicity predicates.
 
 [TODO: semantic-cf2d-signed] Source-level `Vec.star` and `KernelFamily` require
 signed arithmetic. Defer them until a signed DkReal layer exists.
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
index 027bbcd4..4aaff15e 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
@@ -463,6 +463,68 @@ theorem semanticMinimalPeriod_pos
     0 < semanticMinimalPeriod r z :=
   Function.IsPeriodicPt.minimalPeriod_pos hn h
 
+/-- A fixed point of the transported real action. -/
+def SemanticFixed
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) : Prop :=
+  Function.IsFixedPt (semanticAct r) z
+
+/-- Fixed points are exactly period-one points. -/
+theorem semanticFixed_iff_periodic_one
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
+    SemanticFixed r z ↔ SemanticPeriodic r z 1 := by
+  rfl
+
+/-- Fixed points are exactly points of minimal period one. -/
+theorem semanticFixed_iff_minimalPeriod_eq_one
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
+    SemanticFixed r z ↔ semanticMinimalPeriod r z = 1 := by
+  exact Function.minimalPeriod_eq_one_iff_isFixedPt.symm
+
+/-- A fixed point is periodic at every iterate count. -/
+theorem semanticPeriodic_of_fixed
+    {r : UnitKernel DkNNRealQ} {z : Vec ℝ}
+    (h : SemanticFixed r z) (n : ℕ) :
+    SemanticPeriodic r z n :=
+  Function.IsFixedPt.isPeriodicPt h n
+
+/-- The origin is fixed by every transported linear CF2D action. -/
+theorem semanticFixed_zero (r : UnitKernel DkNNRealQ) :
+    SemanticFixed r (Vec.mk 0 0) := by
+  simp [SemanticFixed, Function.IsFixedPt, semanticAct, UnitKernel.act,
+    Vec.star]
+
+/--
+Positive finite action order excludes the vacuous zero-iterate witness.
+
+This still records an exhibited positive order, not necessarily the least
+positive order of the action.
+-/
+def SemanticPositiveFiniteOrder
+    (r : UnitKernel DkNNRealQ) (n : ℕ) : Prop :=
+  0 < n ∧ SemanticFiniteOrder r n
+
+/-- Positive finite action order supplies positive periodicity of every point. -/
+theorem semanticPeriodic_of_positiveFiniteOrder
+    {r : UnitKernel DkNNRealQ} {n : ℕ}
+    (h : SemanticPositiveFiniteOrder r n) (z : Vec ℝ) :
+    0 < n ∧ SemanticPeriodic r z n :=
+  ⟨h.1, (semanticFiniteOrder_iff r n).mp h.2 z⟩
+
+/-- Positive finite action order persists at every positive multiple. -/
+theorem semanticPositiveFiniteOrder_of_dvd
+    {r : UnitKernel DkNNRealQ} {m n : ℕ}
+    (h : SemanticPositiveFiniteOrder r m) (hmn : m ∣ n) (hn : 0 < n) :
+    SemanticPositiveFiniteOrder r n :=
+  ⟨hn, semanticFiniteOrder_of_dvd h.2 hmn⟩
+
+/-- Under positive finite order, every point has positive minimal period. -/
+theorem semanticMinimalPeriod_pos_of_positiveFiniteOrder
+    {r : UnitKernel DkNNRealQ} {n : ℕ}
+    (h : SemanticPositiveFiniteOrder r n) (z : Vec ℝ) :
+    0 < semanticMinimalPeriod r z :=
+  semanticMinimalPeriod_pos h.1
+    ((semanticFiniteOrder_iff r n).mp h.2 z)
+
 /-
 [TODO: semantic-cf2d/signed-kernel] Source-level `Vec.star` and
 `KernelFamily` require a ring because their core coordinate uses subtraction.
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index 0030f637..f5c9b04c 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -138,6 +138,8 @@ BridgeNNReal / BridgeReal:
   periodic points use Mathlib IsPeriodicPt
   finite action order makes every level-set point periodic
   minimal periods divide all known return times and finite action orders
+  fixed points are exactly minimal-period-one points
+  positive finite order excludes the vacuous zero iterate
   source-level star and KernelFamily wait for signed DkReal arithmetic
   treat order reflection as a separate heavier task
   compare semantic equality with DkReal.Equiv
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
index 5d8092f0..1a541361 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
@@ -94,6 +94,9 @@ semanticFiniteOrder_of_dvd
 semanticMinimalPeriod
 semanticPeriodic_iff_minimalPeriod_dvd
 semanticMinimalPeriod_dvd_of_finiteOrder
+SemanticFixed
+semanticFixed_iff_minimalPeriod_eq_one
+SemanticPositiveFiniteOrder
 ```
 
 The transported kernel now acts on real CF2D vectors and preserves `q2`.
@@ -125,8 +128,14 @@ equivalent to divisibility by this minimal period. Every point's minimal
 period divides any finite action order, and finite action order propagates to
 all multiples.
 
+Fixed points use Mathlib's `Function.IsFixedPt`: they are exactly period-one
+points and exactly points of minimal period one. The origin is fixed by every
+transported action. `SemanticPositiveFiniteOrder` adds positivity to an
+exhibited finite action order; it does not claim minimality of that order.
+
 The next structural boundary is source-level `Vec.star` and `KernelFamily`.
 Both require signed arithmetic. They should wait for a signed DkReal layer
 rather than forcing subtraction into `DkNNRealQ`. Until then, further work can
-remain on the real side, for example classifying fixed points or finite-order
-actions. Order reflection remains a separate, heavier task.
+remain on the real side, for example coordinate classification of nonzero
+fixed points under explicit kernel hypotheses. Order reflection remains a
+separate, heavier task.
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index c5259ac3..42ffca3d 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -236,6 +236,30 @@ Archive
 6. 検証:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
 
+### 2026/06/22 04:17 JST (Fixed points and positive finite action order)
+
+1. 方針:
+   - fixed point は Mathlib `Function.IsFixedPt` を用いる。
+   - zero iterate でも成立する弱い finite order と、正の witness を持つ版を
+     分離する。
+2. 実施:
+   - `SemanticFixed` を追加した。
+   - fixed point、period one、minimal period one の同値を公開した。
+   - fixed point が任意 period の周期点になることを証明した。
+   - 原点が全 transported action の fixed point であることを証明した。
+   - `SemanticPositiveFiniteOrder` を追加した。
+   - 正有限位数の正倍数伝播と、全点の minimal period positivity を証明した。
+3. 注意:
+   - positive finite order の `n` は正だが、作用の最小正位数とは限らない。
+4. 結論:
+   - fixed / periodic / minimal-period / finite-order の基本関係が標準 API
+     上で揃った。
+5. 次の候補:
+   - 明示的 kernel 条件下での非零 fixed point の座標分類。
+   - source-level family は signed DkReal 層まで保留。
+6. 検証:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
+
 ### 2026/06/22 03:50 JST (Periodic points and finite action order)
 
 1. 方針:
````
`````
