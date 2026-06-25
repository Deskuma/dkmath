# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2D

gch: 7baefc33a823a933379ce35f0cde7a95777f7858

## Report

非零固定点の分類まで完了しました。

- `SemanticIdentityKernel`
- identity kernel と semantic core `= 1` の同値
- core `= 1` から beam `= 0`
- identity kernel は全点を固定
- nonidentity kernel の固定点は原点のみ

証明は `C² + S² = 1` と固定点連立方程式の行列式だけを使用しています。角度・連続性・signed source は不要です。

全体ビルド成功、8566 jobs。`git diff --check` も成功です。

## Review

うむ。これはかなり綺麗に閉じておる。
採用でよい。

今回の到達点は、実数側 transported action の固定点分類じゃな。
しかも、角度も連続性も signed source も使っていない。使っているのは、実数側の座標恒等式と固定点方程式だけじゃ。

## 状況

いまの構造はこうなった。

```text
DkNNRealQ unit kernel
-> Real unit kernel
-> Real q2 保存作用
-> orbit / periodic / finite order
-> fixed point
-> fixed point classification
```

今回で、固定点について次が言えるようになった。

```text
identity kernel なら全点 fixed
nonidentity kernel なら fixed point は原点だけ
```

これはかなり強い。
三角関数の角度をまだ定義していないのに、「非自明回転的作用は原点以外を固定しない」という幾何事実まで来ている。

## 証明の核

Real 側の transported kernel の座標を \(C,S\) とすると、unit kernel なので、

$$
C^2+S^2=1
$$

がある。

固定点条件は、

$$
C x - S y = x,\quad C y + S x = y
$$

なので、整理すると、

$$
(C-1)x-Sy=0,\quad Sx+(C-1)y=0
$$

この連立方程式の行列式が、

$$
(C-1)^2+S^2
$$

じゃ。

もし \(C\ne 1\) なら、この値は \(0\) ではない。
したがって \(x=0\) かつ \(y=0\)。
つまり固定点は原点だけ。

Lean 実装でもこの構造がそのまま出ておる。

```lean
linear_combination (C - 1) * hx + S * hy
linear_combination (C - 1) * hy - S * hx
```

この使い方は良い。手計算の消去法そのものじゃ。

## 良い点

`SemanticIdentityKernel` を Real 側の中立核との等式にしたのは正しい。

```lean
def SemanticIdentityKernel (r : UnitKernel DkNNRealQ) : Prop :=
  semanticUnitKernel r = UnitKernel.one ℝ
```

source 側で identity を判定しない。
あくまで Real へ transport した後の kernel が中立かを見る。
これは今の設計境界に合っている。

`semanticIdentityKernel_iff_core_eq_one` も良い。

Real unit kernel では、core が \(1\) なら beam は \(0\)。
したがって中立核になる。

ここで beam の非負性すら不要で、\(C^2+S^2=1\) だけで閉じているのが美しい。

## 注意点

この分類は transported Real action の分類じゃ。
source 側 DkNNRealQ に signed な kernel 群構造ができた、という主張ではない。

また、`SemanticIdentityKernel` は semantic 側の identity なので、source 側で別表現だが同じ Real kernel になる可能性は、semantic equality の問題として扱うことになる。
これは現段階では問題ではない。今の定理は Real 側 action の分類だからじゃ。

## 次に進むなら

次は finite-order classification の入口が自然じゃ。

今の固定点分類から見ると、非 identity kernel の 1-periodic point は原点だけ。
次は \(n\)-periodic point や finite order を、kernel の \(n\) 回合成が identity になる条件に寄せる段階じゃ。

ただし、角度なしで行くなら、まずは Real 側 kernel product の反復を定義して、

```text
n-fold semantic kernel product が identity
```

と、

```text
semanticAct の n 回反復が identity
```

をつなぐのが安全じゃな。

## 判定

採用。かなり良い。

今回の成果は、単なる補題追加ではなく、最初の実質的な幾何分類じゃ。

```text
identity kernel
  -> 全点固定

nonidentity kernel
  -> 原点だけ固定
```

これを、角度なし・連続性なし・signed source なしで閉じた。
かなり DkMath らしい到達点じゃよ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index cee454fa..007f21d9 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -89,6 +89,8 @@ finite action order are expressed through Mathlib's standard discrete-dynamics
 API. Minimal periods use Mathlib's zero-for-aperiodic convention and divide
 all known return times. Fixed points and positive finite action order are
 separated from the weaker zero-iterate-compatible periodicity predicates.
+Identity transported kernels fix every point; nonidentity transported kernels
+fix exactly the origin.
 
 [TODO: semantic-cf2d-signed] Source-level `Vec.star` and `KernelFamily` require
 signed arithmetic. Defer them until a signed DkReal layer exists.
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
index 4aaff15e..0eff8594 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
@@ -525,6 +525,96 @@ theorem semanticMinimalPeriod_pos_of_positiveFiniteOrder
   semanticMinimalPeriod_pos h.1
     ((semanticFiniteOrder_iff r n).mp h.2 z)
 
+/-- The transported kernel is the neutral real unit kernel. -/
+def SemanticIdentityKernel (r : UnitKernel DkNNRealQ) : Prop :=
+  semanticUnitKernel r = UnitKernel.one ℝ
+
+/--
+For a transported first-quadrant unit kernel, core coordinate one forces the
+beam coordinate to vanish.
+-/
+theorem semanticUnitKernel_beam_eq_zero_of_core_eq_one
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 1) :
+    semanticValue (r : Vec DkNNRealQ).beam = 0 := by
+  have hq := semanticUnitKernel_sq_add_sq r
+  nlinarith [sq_nonneg (semanticValue (r : Vec DkNNRealQ).beam)]
+
+/-- Identity-kernel status is characterized by semantic core coordinate one. -/
+theorem semanticIdentityKernel_iff_core_eq_one
+    (r : UnitKernel DkNNRealQ) :
+    SemanticIdentityKernel r ↔
+      semanticValue (r : Vec DkNNRealQ).core = 1 := by
+  constructor
+  · intro h
+    have hv := congrArg (fun k : UnitKernel ℝ => (k : Vec ℝ).core) h
+    simpa [SemanticIdentityKernel, semanticUnitKernel, semanticVec,
+      UnitKernel.one, Vec.one] using hv
+  · intro hcore
+    have hbeam := semanticUnitKernel_beam_eq_zero_of_core_eq_one hcore
+    apply UnitKernel.ext
+    cases r with
+    | mk val hq =>
+        cases val with
+        | mk core beam =>
+            simp_all [semanticUnitKernel, semanticVec, UnitKernel.one, Vec.one]
+
+/-- An identity transported kernel fixes every real vector. -/
+theorem semanticFixed_of_identityKernel
+    {r : UnitKernel DkNNRealQ} (h : SemanticIdentityKernel r)
+    (z : Vec ℝ) :
+    SemanticFixed r z := by
+  rw [SemanticIdentityKernel] at h
+  simp [SemanticFixed, Function.IsFixedPt, semanticAct, h]
+
+/--
+If the semantic core coordinate is not one, the transported action has only
+the origin as a fixed point.
+-/
+theorem eq_zero_of_semanticFixed_of_core_ne_one
+    {r : UnitKernel DkNNRealQ} {z : Vec ℝ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core ≠ 1)
+    (hz : SemanticFixed r z) :
+    z = Vec.mk 0 0 := by
+  let C := semanticValue (r : Vec DkNNRealQ).core
+  let S := semanticValue (r : Vec DkNNRealQ).beam
+  have hq : C ^ 2 + S ^ 2 = 1 := by
+    simpa [C, S] using semanticUnitKernel_sq_add_sq r
+  have hfix := hz
+  rw [SemanticFixed, Function.IsFixedPt] at hfix
+  have hx :
+      C * z.core - S * z.beam = z.core := by
+    simpa [semanticAct, C, S] using congrArg Vec.core hfix
+  have hy :
+      C * z.beam + S * z.core = z.beam := by
+    simpa [semanticAct, C, S] using congrArg Vec.beam hfix
+  have hdet : (C - 1) ^ 2 + S ^ 2 ≠ 0 := by
+    intro hzero
+    have : C = 1 := by nlinarith [sq_nonneg (C - 1), sq_nonneg S]
+    exact hcore (by simpa [C] using this)
+  have hdx : ((C - 1) ^ 2 + S ^ 2) * z.core = 0 := by
+    linear_combination (C - 1) * hx + S * hy
+  have hdy : ((C - 1) ^ 2 + S ^ 2) * z.beam = 0 := by
+    linear_combination (C - 1) * hy - S * hx
+  have zx : z.core = 0 :=
+    (mul_eq_zero.mp hdx).resolve_left hdet
+  have zy : z.beam = 0 :=
+    (mul_eq_zero.mp hdy).resolve_left hdet
+  cases z
+  simp_all
+
+/-- A nonidentity transported kernel fixes exactly the origin. -/
+theorem semanticFixed_iff_eq_zero_of_not_identity
+    {r : UnitKernel DkNNRealQ} (h : ¬SemanticIdentityKernel r)
+    (z : Vec ℝ) :
+    SemanticFixed r z ↔ z = Vec.mk 0 0 := by
+  have hcore :
+      semanticValue (r : Vec DkNNRealQ).core ≠ 1 := by
+    intro hcore
+    exact h ((semanticIdentityKernel_iff_core_eq_one r).2 hcore)
+  exact ⟨eq_zero_of_semanticFixed_of_core_ne_one hcore,
+    fun hz => hz ▸ semanticFixed_zero r⟩
+
 /-
 [TODO: semantic-cf2d/signed-kernel] Source-level `Vec.star` and
 `KernelFamily` require a ring because their core coordinate uses subtraction.
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index f5c9b04c..62507f37 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -140,6 +140,8 @@ BridgeNNReal / BridgeReal:
   minimal periods divide all known return times and finite action orders
   fixed points are exactly minimal-period-one points
   positive finite order excludes the vacuous zero iterate
+  identity kernels fix every point
+  nonidentity transported kernels fix exactly the origin
   source-level star and KernelFamily wait for signed DkReal arithmetic
   treat order reflection as a separate heavier task
   compare semantic equality with DkReal.Equiv
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
index 1a541361..bd0b3cd5 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
@@ -97,6 +97,9 @@ semanticMinimalPeriod_dvd_of_finiteOrder
 SemanticFixed
 semanticFixed_iff_minimalPeriod_eq_one
 SemanticPositiveFiniteOrder
+SemanticIdentityKernel
+semanticIdentityKernel_iff_core_eq_one
+semanticFixed_iff_eq_zero_of_not_identity
 ```
 
 The transported kernel now acts on real CF2D vectors and preserves `q2`.
@@ -133,9 +136,16 @@ points and exactly points of minimal period one. The origin is fixed by every
 transported action. `SemanticPositiveFiniteOrder` adds positivity to an
 exhibited finite action order; it does not claim minimality of that order.
 
+The first fixed-point classification is complete. For a transported
+first-quadrant unit kernel, semantic core coordinate one forces beam zero and
+therefore the neutral kernel. An identity kernel fixes every point; every
+nonidentity transported kernel fixes exactly the origin. The proof uses only
+the Pythagorean kernel identity and the determinant of the fixed-point linear
+system.
+
 The next structural boundary is source-level `Vec.star` and `KernelFamily`.
 Both require signed arithmetic. They should wait for a signed DkReal layer
 rather than forcing subtraction into `DkNNRealQ`. Until then, further work can
-remain on the real side, for example coordinate classification of nonzero
-fixed points under explicit kernel hypotheses. Order reflection remains a
-separate, heavier task.
+remain on the real side, for example finite-order classification under
+explicit semantic coordinate hypotheses. Order reflection remains a separate,
+heavier task.
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index 42ffca3d..877072f7 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -236,6 +236,28 @@ Archive
 6. 検証:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
 
+### 2026/06/22 04:23 JST (Fixed-point classification without angles)
+
+1. 目的:
+   - transported action の非零 fixed point を座標的に分類する。
+2. 実施:
+   - `SemanticIdentityKernel` を real neutral kernel との等式として定義した。
+   - semantic core が one なら `C^2 + S^2 = 1` から beam zero を証明した。
+   - identity-kernel 条件と semantic core one の同値を証明した。
+   - identity kernel が全実数 vector を固定することを証明した。
+   - core が one でない kernel の fixed point 連立方程式から、行列式
+     `(C - 1)^2 + S^2` を用いて両座標 zero を導いた。
+   - 非 identity kernel の fixed point が原点と同値であることを証明した。
+3. 結論:
+   - identity kernel なら全点 fixed。
+   - nonidentity transported kernel なら fixed point は原点のみ。
+4. 使用していないもの:
+   - angle、continuity、signed DkReal source。
+5. 次の候補:
+   - 明示的 semantic coordinate 条件下での finite-order classification。
+6. 検証:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
+
 ### 2026/06/22 04:17 JST (Fixed points and positive finite action order)
 
 1. 方針:
````
`````
