# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2D

gch: 59a9f6b870a82a25dee1b70b4e42c672ee80ba95

## Report

次の段階まで完了しました。

- `noncomputable` に関する記述を正確化
- order 1 を identity / core = 1 と分類
- order 2 も第一象限制約により identity / core = 1 と分類
- 非自明な order 2 kernel が存在しないことを証明
- docstring・設計資料・履歴を更新

検証:

- 対象ビルド: 8273 jobs 成功
- 全体ビルド: 8566 jobs 成功
- `git diff --check` 成功

## Review

うむ。これは採用でよい。
今回の分類はかなり自然で、しかも境界が正しい。

## 状況

ここまでで、Real 側 transported kernel について次が揃った。

```text
semanticUnitKernel
semanticKernelPower
SemanticKernelFiniteOrder
semanticKernelFiniteOrder_iff
```

つまり、DkNNRealQ 由来の kernel を Real 側に輸送し、その Real unit kernel の反復積で有限位数を語れるようになっている。

今回さらに、

```text
order dividing 1
order dividing 2
```

が分類された。

結論はこうじゃ。

```text
order dividing 1 なら identity
order dividing 2 でも identity
```

したがって、DkNNRealQ から来る第一象限 kernel には、非自明な二位数 kernel が存在しない。

## 数学的には正しい

Real unit kernel 全体で見れば、二乗して identity になる kernel は少なくとも二つある。

```text
(1, 0)
(-1, 0)
```

しかし、DkNNRealQ から coordinatewise transport された kernel は core も beam も非負になる。

つまり、

$$
C \ge 0,\quad S \ge 0
$$

がある。

このため、\((-1,0)\) は出てこない。
だから order dividing 2 が成立しても、残るのは \((1,0)\) だけになる。

ここが今回の本質じゃ。

## order 1 の分類

これは素直。

```lean
semanticKernelPower r 1 = semanticUnitKernel r
```

なので、

```text
semanticKernelPower r 1 = UnitKernel.one Real
```

は、そのまま

```text
semanticUnitKernel r = UnitKernel.one Real
```

と同じ。

さらに既存の

```lean
semanticIdentityKernel_iff_core_eq_one
```

により、core 座標が \(1\) であることとも同値になる。

ここは問題なし。

## order 2 の分類

`semanticKernelFiniteOrder_two_iff_identity` は良い。

証明の骨格はこうじゃ。

Real 側の kernel 座標を \(C,S\) とすると、単位核なので、

$$
C^2+S^2=1
$$

二乗が identity なら、二乗積の core 座標から、

$$
C^2-S^2=1
$$

が出る。

この二つを合わせると、

$$
S^2=0,\quad C^2=1
$$

さらに \(C\ge 0\) なので、

$$
C=1
$$

になる。
すると既存定理により identity kernel。

Lean 側でも、`hcore` から二乗積の core 座標を取り出し、`nlinarith` で閉じている。これは適切じゃ。

## 注意点

ここでいう `SemanticKernelFiniteOrder r 2` は「正確な位数が 2」ではない。
「二乗が identity」、つまり order が 2 を割る、という意味じゃ。

したがって、文書で `product order dividing two` と書いているのは正しい。
「非自明な order two が存在しない」という表現も、この意味なら正しい。

より厳密に言うなら、

```text
exact order 2 の transported first-quadrant kernel は存在しない
```

ということじゃ。

## noncomputable の修正も良い

前回の「noncomputable は不要」という表現を修正したのは正しい。

semantic bridge 全体は `semanticValue` に依存しているので、文脈としては noncomputable。
ただし今回の kernel power そのものは、Real 側の有限再帰と代数だけで、新しい解析的選択を増やしていない。

この整理は正確じゃ。

## 次の自然な方向

次は order 3、order 4 へ行きたくなるが、そこからは一気に難度が上がる。

第一象限 kernel で有限位数を持つなら、角度的には候補が限られる。
しかし角度を使わず座標で行くなら、まずは次の形がよい。

```text
semanticKernelPower r 3 = one
```

から、三倍角に相当する座標多項式を取り出す。
たとえば core 側は \(C^3-3CS^2\) 型になるはずじゃ。

ただし、ここで三角関数は使わない。
あくまで `Vec.star` の反復展開として扱う。

低位数分類を続けるなら、先に補助 API として、

```text
semanticKernelPower_two_core
semanticKernelPower_two_beam
semanticKernelPower_three_core
semanticKernelPower_three_beam
```

のような座標式を用意すると安全じゃ。

## 判定

採用でよい。

今回の成果はこうじゃ。

```text
Real unit kernel 全体では order 2 候補に (-1,0) がある
DkNNRealQ 由来の transported kernel は第一象限に制限される
よって order dividing 2 は identity に潰れる
```

これは非常に DkMath らしい結果じゃ。
source 側に signed kernel を導入しない制約が、Real 側では「第一象限制約」として働き、非自明な二位数を排除している。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
index 08edc968..eb095e80 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
@@ -695,6 +695,69 @@ theorem semanticKernelFiniteOrder_iff
             simpa [semanticOrbit] using semanticKernelPower_act r n z
       _ = id z := congrFun h z
 
+/-- The first real-side kernel power is the transported kernel itself. -/
+@[simp]
+theorem semanticKernelPower_one (r : UnitKernel DkNNRealQ) :
+    semanticKernelPower r 1 = semanticUnitKernel r := by
+  simp [semanticKernelPower]
+
+/-- Product order dividing one is exactly semantic identity-kernel status. -/
+theorem semanticKernelFiniteOrder_one_iff_identity
+    (r : UnitKernel DkNNRealQ) :
+    SemanticKernelFiniteOrder r 1 ↔ SemanticIdentityKernel r := by
+  simp [SemanticKernelFiniteOrder, SemanticIdentityKernel]
+
+/-- Product order dividing one is characterized by semantic core coordinate one. -/
+theorem semanticKernelFiniteOrder_one_iff_core_eq_one
+    (r : UnitKernel DkNNRealQ) :
+    SemanticKernelFiniteOrder r 1 ↔
+      semanticValue (r : Vec DkNNRealQ).core = 1 := by
+  rw [semanticKernelFiniteOrder_one_iff_identity,
+    semanticIdentityKernel_iff_core_eq_one]
+
+/--
+For a transported first-quadrant kernel, product order dividing two already
+forces the neutral kernel.
+
+Over all real unit kernels the square equation also admits `(-1, 0)`. That
+case is excluded here because both semantic coordinates transported from
+`DkNNRealQ` are nonnegative.
+-/
+theorem semanticKernelFiniteOrder_two_iff_identity
+    (r : UnitKernel DkNNRealQ) :
+    SemanticKernelFiniteOrder r 2 ↔ SemanticIdentityKernel r := by
+  let C := semanticValue (r : Vec DkNNRealQ).core
+  let S := semanticValue (r : Vec DkNNRealQ).beam
+  constructor
+  · intro h
+    change semanticKernelPower r 2 = UnitKernel.one ℝ at h
+    have hcore := congrArg (fun k : UnitKernel ℝ => (k : Vec ℝ).core) h
+    have hC : 0 ≤ C := by
+      simpa [C] using semanticUnitKernel_core_nonneg r
+    have hS : 0 ≤ S := by
+      simpa [S] using semanticUnitKernel_beam_nonneg r
+    have hq : C ^ 2 + S ^ 2 = 1 := by
+      simpa [C, S] using semanticUnitKernel_sq_add_sq r
+    have hsquare : C ^ 2 - S ^ 2 = 1 := by
+      simpa [semanticKernelPower, semanticUnitKernel, semanticVec,
+        UnitKernel.star, Vec.star, UnitKernel.one, Vec.one, C, S, pow_two]
+        using hcore
+    apply (semanticIdentityKernel_iff_core_eq_one r).2
+    change C = 1
+    nlinarith [sq_nonneg (C - 1)]
+  · intro h
+    change semanticKernelPower r 2 = UnitKernel.one ℝ
+    rw [SemanticIdentityKernel] at h
+    simp [semanticKernelPower, h]
+
+/-- Product order dividing two is also characterized by semantic core one. -/
+theorem semanticKernelFiniteOrder_two_iff_core_eq_one
+    (r : UnitKernel DkNNRealQ) :
+    SemanticKernelFiniteOrder r 2 ↔
+      semanticValue (r : Vec DkNNRealQ).core = 1 := by
+  rw [semanticKernelFiniteOrder_two_iff_identity,
+    semanticIdentityKernel_iff_core_eq_one]
+
 /-
 [TODO: semantic-cf2d/signed-kernel] Source-level `Vec.star` and
 `KernelFamily` require a ring because their core coordinate uses subtraction.
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index dddec68a..2402f8e4 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -144,6 +144,7 @@ BridgeNNReal / BridgeReal:
   nonidentity transported kernels fix exactly the origin
   real-side kernel powers act as the corresponding function iterates
   kernel-product finite order is equivalent to finite action order
+  product orders dividing one or two force the transported identity kernel
   source-level star and KernelFamily wait for signed DkReal arithmetic
   treat order reflection as a separate heavier task
   compare semantic equality with DkReal.Equiv
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
index 20ca5135..56944edf 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
@@ -105,6 +105,11 @@ semanticKernelPower_act
 unitKernel_eq_one_of_act_eq_id
 SemanticKernelFiniteOrder
 semanticKernelFiniteOrder_iff
+semanticKernelPower_one
+semanticKernelFiniteOrder_one_iff_identity
+semanticKernelFiniteOrder_one_iff_core_eq_one
+semanticKernelFiniteOrder_two_iff_identity
+semanticKernelFiniteOrder_two_iff_core_eq_one
 ```
 
 The transported kernel now acts on real CF2D vectors and preserves `q2`.
@@ -165,6 +170,14 @@ This closes the bridge between kernel product order and finite action order
 without defining multiplication, subtraction, or inverses in the nonnegative
 source.
 
+The first low-order classification is also complete. Product order dividing
+one is equivalent to semantic identity and to semantic core coordinate one.
+For transported first-quadrant kernels the same is true of product order
+dividing two. A general real unit kernel would also admit `(-1, 0)` as a
+square root of the neutral kernel, but coordinatewise transport from
+`DkNNRealQ` makes both semantic coordinates nonnegative and excludes that
+case. Thus no nonidentity transported kernel has order two.
+
 The next structural boundary is source-level `Vec.star` and `KernelFamily`.
 Both require signed arithmetic. They should wait for a signed DkReal layer
 rather than forcing subtraction into `DkNNRealQ`. Until then, further work can
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index 187f615a..ef41a406 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -212,6 +212,26 @@ Archive
 5. 検証:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
 
+### 2026/06/22 04:42 JST (Low-order classification: orders one and two)
+
+1. 修正:
+   - semantic bridge 全体は noncomputable 文脈にあることを明記し、前節の
+     `noncomputable` 不要という表現を限定した。
+2. 実施:
+   - kernel power one が transported kernel 自身であることを証明した。
+   - order dividing one を identity および core coordinate one と分類した。
+   - order dividing two も identity および core coordinate one と分類した。
+3. 数学的理由:
+   - 一般の Real unit kernel では `(-1, 0)` も二乗して中立核になる。
+   - 今回は DkNNRealQ からの座標別 transport により core と beam がともに
+     非負なので、この候補は排除される。
+4. 結論:
+   - transported first-quadrant kernel に非自明な order two は存在しない。
+   - 証明は unit-square 恒等式と二乗積の core 座標だけで閉じ、角度や
+     連続性を使用しない。
+5. 検証:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
+
 ### 2026/06/22 04:09 JST (Minimal periods and finite-order divisibility)
 
 1. 注意点:
@@ -384,7 +404,9 @@ Archive
 3. 結論:
    - finite order は、作用側と kernel 積側のどちらからでも同じ条件として
      扱える。
-   - signed source、角度、連続性、`noncomputable` は不要。
+   - signed source、角度、連続性は不要。
+   - semantic bridge 自体は noncomputable 文脈だが、この反復積の段階では
+     新たな解析的 noncomputable 要素を増やしていない。
 4. 境界:
    - この積は Real 側だけに存在し、非負 source の積を主張しない。
 5. 検証:
````
`````
