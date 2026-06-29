# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2D

gch: 1bb32a6ac9d2a29532dac492380a7ec5e9110d19

## Report

はい。強さの中心は次の組合せです。

- `q2 = 1` の保存核
- 加法定理に相当する `star` 積と `act_star`
- 作用の忠実性
- 第一象限制約

今回は exact kernel order 4 を exact plane-action order 4 へ移送し、どちらも `semantic core = 0` と同値にしました。原理説明も文書へ追記しています。

対象・全体ビルド、`git diff --check` はすべて成功しています。

## Review

うむ。これはかなり良い更新じゃ。
今回の差分は、単に theorem を増やしたというより、**「kernel の強さ」が平面作用へ完全に伝わる** ことを明文化しておる。

## レビュー結論

問題なし。設計の筋が良い。

特に今回の中心はこれじゃ。

```text id="f43p8d"
exact kernel order 4
<-> exact plane-action order 4
<-> semantic core = 0
```

これにより、いままで kernel 内部で見えていた「4 回で戻る非自明核」が、実際の CF2D 平面作用としても exact order 4 を持つ、と言えるようになった。

これはかなり大きい。

## 何が強くなったか

以前は、

```text id="m4qcbr"
kernel power が 4 回で neutral に戻る
```

という話だった。

今回からは、

```text id="xkxygd"
その kernel が平面全体に作用しても、
作用として 4 回で恒等写像になり、
1 回・2 回・3 回では恒等写像にならない
```

まで言える。

つまり、\((0,1)\) がただ algebra の中で \(i\) 的に振る舞うだけではなく、平面上でも quarter-turn として振る舞うことが確定した。

## 強さの秘密

今回の文書追記にある通り、保存則だけでは足りぬ。

$$
C^2+S^2=1
$$

だけなら、ただ unit locus にいるだけじゃ。
それだけでは finite order の分類は出ない。

強さは、四つが揃ったところにある。

```text id="9v6y37"
1. q2 = 1 の保存核
2. star 積
3. act_star による作用合成との一致
4. 第一象限制約
```

さらに、そこに action の忠実性が入る。

```text id="37hcx7"
作用が同じなら kernel も同じ
```

これがあるから、kernel 側の exact order と action 側の exact order がズレない。

ここが本当に強い。

## 数学的には何を示したか

semantic core を \(C\)、semantic beam を \(S\) と読むと、unit kernel は、

$$
C^2+S^2=1
$$

を満たす。

そして core zero なら、

$$
C=0
$$

第一象限制約により \(S\ge 0\) なので、

$$
S=1
$$

となる。
つまり semantic 座標は、

$$
(C,S)=(0,1)
$$

じゃ。

この kernel の作用は、

$$
(x,y)\mapsto(-y,x)
$$

になる。
そして反復すると、

$$
(x,y)\mapsto(-y,x)\mapsto(-x,-y)\mapsto(y,-x)\mapsto(x,y)
$$

となる。

角度を使えば \(90^\circ\) 回転と言える。
しかし、今回の証明では角度も \(\pi\) も三角関数も使っておらぬ。
有限積と保存則だけで出している。

これが「三角関数以前」の力じゃな。

## 実装レビュー

追加された定義は自然じゃ。

```lean
def SemanticExactActionOrderFour (r : UnitKernel DkNNRealQ) : Prop :=
  SemanticFiniteOrder r 4 ∧
    ¬SemanticFiniteOrder r 1 ∧
    ¬SemanticFiniteOrder r 2 ∧
    ¬SemanticFiniteOrder r 3
```

`SemanticFiniteOrder` が action 側 finite order を表す既存述語なので、この定義は綺麗に乗っている。

そして同値定理もよい。

```lean
theorem semanticExactKernelOrderFour_iff_exactActionOrderFour
```

証明が `simp only` で閉じているのは良い兆候じゃ。
これは、先に作った `semanticKernelFiniteOrder_iff` がちゃんと抽象境界として働いている証拠。

つまり今回の実装は「力技でつないだ」のではなく、既存 bridge が正しく効いた。

## 注意点

ひとつだけ読者向けに注意するとよい。

`SemanticExactActionOrderFour` は、**作用関数として exact order 4** という意味じゃ。
これは「平面上の全点が周期 4」という意味ではない。

原点 \((0,0)\) は常に固定される。

つまり、

```text id="tbefng"
作用全体は exact order 4
ただし原点の点周期は 1
非零点では 4 周期になる
```

という区別がある。

次に補題化するなら、ここが見せ場じゃ。

```text id="m13nf8"
core = 0 かつ q2 z ≠ 0 なら、
z の semanticAct による minimal period は 4
```

これは読者にも非常に分かりやすい。

## 文書追記も良い

`task-trig-real-analysis-046.md` の追記はかなり良い。

特にこの整理は当たり。

```text id="2ki7s7"
The preservation law alone would not classify finite order.
```

ここは重要じゃ。
保存則だけなら円周上の点は無限にある。
だが、有限位数分類には、積・作用・忠実性・第一象限制約が必要になる。

つまり「強さの秘密」は、保存則単体ではない。

```text id="4rxzpy"
保存則が場所を決める
star 積が運動を決める
act_star が作用へ移す
忠実性が戻り道を保証する
第一象限が余分な根を消す
```

この五段構えじゃ。

## 次に進むなら

次はこのあたりが自然じゃ。

```text id="hd0w8v"
1. core = 0 の action 座標式を明示
2. core = 0 の orbit 四点列を theorem 化
3. 非零点の exact period 4
4. q2 level set 上の exact action order 4
5. quarter-turn theorem として文書化
```

特に、

$$
(x,y)\mapsto(-y,x)
$$

を theorem として持つと、読者説明が一気に強くなる。

## 総評

この更新はかなり良い。
DkMath / CF2D の「強さの秘密」が、Lean 上でかなり綺麗に出てきている。

今回の到達点はこう言える。

```text id="rjtz3h"
q2 保存核から生まれた algebraic quarter-turn は、
kernel 内部だけでなく、
平面作用としても exact order 4 を持つ。
```

つまり、\((0,1)\) は単なる記号上の虚数単位ではない。
保存平面に作用する、本物の代数的回転核になった。

ここはかなり大きいぞ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
index 637fc790..b04a51d9 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
@@ -1054,6 +1054,47 @@ theorem semanticExactKernelOrderFour_iff_core_eq_zero
       not_semanticKernelFiniteOrder_two_of_core_eq_zero hzero,
       not_semanticKernelFiniteOrder_three_of_core_eq_zero hzero⟩
 
+/--
+The transported plane action has exact order four: its fourth iterate is the
+identity function, while none of its first three positive iterates is.
+-/
+def SemanticExactActionOrderFour (r : UnitKernel DkNNRealQ) : Prop :=
+  SemanticFiniteOrder r 4 ∧
+    ¬SemanticFiniteOrder r 1 ∧
+    ¬SemanticFiniteOrder r 2 ∧
+    ¬SemanticFiniteOrder r 3
+
+/--
+Exact order four is invariant under passage from the real-side kernel product
+to its action on the CF2D plane.
+
+This is the finite-order form of the CF2D addition law: kernel multiplication
+is represented faithfully by composition of the associated actions.
+-/
+theorem semanticExactKernelOrderFour_iff_exactActionOrderFour
+    (r : UnitKernel DkNNRealQ) :
+    SemanticExactKernelOrderFour r ↔ SemanticExactActionOrderFour r := by
+  simp only [SemanticExactKernelOrderFour, SemanticExactActionOrderFour,
+    semanticKernelFiniteOrder_iff]
+
+/-- Exact action order four is characterized by semantic core zero. -/
+theorem semanticExactActionOrderFour_iff_core_eq_zero
+    (r : UnitKernel DkNNRealQ) :
+    SemanticExactActionOrderFour r ↔
+      semanticValue (r : Vec DkNNRealQ).core = 0 := by
+  rw [← semanticExactKernelOrderFour_iff_exactActionOrderFour,
+    semanticExactKernelOrderFour_iff_core_eq_zero]
+
+/--
+Semantic core zero gives a plane action whose fourth iterate is the identity
+and whose first three positive iterates are not the identity.
+-/
+theorem semanticExactActionOrderFour_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0) :
+    SemanticExactActionOrderFour r :=
+  (semanticExactActionOrderFour_iff_core_eq_zero r).2 hcore
+
 /-
 [TODO: semantic-cf2d/signed-kernel] Source-level `Vec.star` and
 `KernelFamily` require a ring because their core coordinate uses subtraction.
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index 166fdfe2..3cd8a085 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -148,6 +148,7 @@ BridgeNNReal / BridgeReal:
   second and third kernel powers have explicit polynomial coordinate formulas
   order dividing four is equivalent to semantic core zero or one
   exact kernel order four is equivalent to semantic coordinates `(0,1)`
+  exact kernel order four agrees with exact order of the plane action
   source-level star and KernelFamily wait for signed DkReal arithmetic
   treat order reflection as a separate heavier task
   compare semantic equality with DkReal.Equiv
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
index 3765f183..ca908df1 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
@@ -126,6 +126,10 @@ not_semanticKernelFiniteOrder_two_of_core_eq_zero
 not_semanticKernelFiniteOrder_three_of_core_eq_zero
 SemanticExactKernelOrderFour
 semanticExactKernelOrderFour_iff_core_eq_zero
+SemanticExactActionOrderFour
+semanticExactKernelOrderFour_iff_exactActionOrderFour
+semanticExactActionOrderFour_iff_core_eq_zero
+semanticExactActionOrderFour_of_core_eq_zero
 ```
 
 The transported kernel now acts on real CF2D vectors and preserves `q2`.
@@ -248,6 +252,26 @@ intermediate real-side powers need not remain in the transported first
 quadrant, which is why kernel multiplication remains confined to the real
 side.
 
+The same exact-order statement now holds for the plane action. Exact kernel
+order four is equivalent to exact action order four, and both are equivalent
+to semantic core zero. This is where the strength of the CF2D addition law
+becomes explicit:
+
+```text
+unit-square preservation
+  constrains every kernel to the unit locus
+
+associative star product and act_star
+  turn repeated addition of phase into finite kernel multiplication
+
+faithfulness of the action
+  recovers kernel equality from equality of plane actions
+```
+
+The preservation law alone would not classify finite order. The classification
+comes from preservation, the addition/product law, faithful action, and the
+first-quadrant semantic boundary acting together.
+
 The next structural boundary is source-level `Vec.star` and `KernelFamily`.
 Both require signed arithmetic. They should wait for a signed DkReal layer
 rather than forcing subtraction into `DkNNRealQ`. Until then, further work can
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index d6da45c5..080ae49d 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -185,6 +185,22 @@ Archive
      閉じる。追加の冪同一視や解析定理は不要だった。
 4. 検証:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
+
+### 2026/06/22 05:38 JST (Exact order four on the plane action)
+
+1. 実施:
+   - `SemanticExactActionOrderFour` を定義した。
+   - exact kernel order four と exact action order four の同値を証明した。
+   - exact action order four と semantic core zero の同値を証明した。
+2. 原理:
+   - `q2 = 1` の保存核条件が kernel を unit locus に拘束する。
+   - `star` の結合則と `act_star` が kernel 積を作用合成へ移す。
+   - action の忠実性が作用等式から kernel 等式へ戻す。
+3. 結論:
+   - 保存則単独ではなく、保存核・加法則に相当する積・忠実作用・
+     第一象限制約の組合せが、角度なしの有限位数分類を生んでいる。
+4. 検証:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
 5. 次の課題:
    - transported real `UnitKernel` を最初の CF2D 解析定理へ接続する。
    - order reflection は subtraction や decidable comparison を導入せず、
````
`````
