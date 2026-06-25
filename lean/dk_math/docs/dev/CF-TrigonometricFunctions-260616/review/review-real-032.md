# Git diff / Report / Review

## Upd: Analysis.DkReal.Order

gch: de313ab6eb2639e7aec998dbb68726896fbfc751

## Report

非負乗法の単調性を実装しました。

- `DkReal.mulNonneg_le_mulNonneg`
- `DkNNReal.mul_le_mul`
- `DkNNRealQ.mul_le_mul`
- 有界下端列と消滅する order defect の積として証明
- docstring、TODO、関連文書を同期

`DkMath.Analysis` と全体 `DkMath` のビルド、`git diff --check` は成功しています。

次は自然数冪の単調性です。

## Review

## 1. 総評

うむ、今回も **合格** じゃ。
加法単調性に続いて、非負乗法の単調性が閉じた。これは `DkNNRealQ` を ordered algebra として扱うための大きな山じゃ。

今回の中心はこれじゃ。

```lean id="t31sw7"
DkReal.mulNonneg_le_mulNonneg
DkNNReal.mul_le_mul
DkNNRealQ.mul_le_mul
```

報告では、有界下端列と消滅する `orderDefect` の積として証明し、`DkMath.Analysis` と全体 `DkMath` の build、`git diff --check` 成功と整理されている。

## 2. 数学的意味

今回示したのは、`DkNNRealQ` 上で

$$
x\le y,\quad z\le w\quad\Rightarrow\quad xz\le yw
$$

が成り立つ、という主張じゃ。

`DkNNRealQ` は非負型なので、乗法は順序を保つはず。今回、その直感を `orderDefect` の収束として形式化している。

代表元の下端点を (a,b,c,d) と見ると、積の差は

$$
ac-bd=a(c-d)+d(a-b)
$$

と分解できる。
ここで (a) と (d) は非負かつ有界、そして (c-d)、(a-b) の正の defect は 0 に収束する。
したがって積の defect も 0 に収束する、という構造じゃ。

## 3. `DkReal.mulNonneg_le_mulNonneg` のレビュー

定理本体はこれじゃ。

```lean id="vj5tuw"
theorem mulNonneg_le_mulNonneg
    {x y z w : DkMath.Analysis.DkReal}
    (hx : Nonnegative x) (hy : Nonnegative y)
    (hz : Nonnegative z) (hw : Nonnegative w)
    (hxy : Le x y) (hzw : Le z w) :
    Le (mulNonneg x z hx hz) (mulNonneg y w hy hw)
```

証明はかなり良い。

左側では、

```lean id="f25fuq"
(x.interval n).lo * orderDefect z w n
```

が 0 に収束することを示している。
これは `orderDefect z w n → 0` と、`x` の lower endpoint が有界であることから出る。

右側では、

```lean id="xu634g"
(w.interval n).lo * orderDefect x y n
```

も同様に 0 に収束する。

そしてこの二つの和で、積の positive defect を上から押さえている。
この証明方針は、前に `equiv_mulNonneg` で使った「有界端点 × 消える差分」と同じ系統で、DkReal の設計に一貫性がある。

## 4. 上界評価は正しい

目標は、各段で

$$
\max(0,x_nz_n-y_nw_n)\le x_n\max(0,z_n-w_n)+w_n\max(0,x_n-y_n)
$$

を示すことじゃ。

コードでは `nlinarith [hx n, hw n]` を使っている。
ここで必要な非負性は (x_n\ge0) と (w_n\ge0)。それぞれ `hx n` と `hw n` から出る。

差分については、

```lean id="3n161l"
z.lo - w.lo ≤ max 0 (z.lo - w.lo)
x.lo - y.lo ≤ max 0 (x.lo - y.lo)
```

を使っている。
したがって `nlinarith` で閉じるのは自然じゃ。

## 5. `DkNNReal` と `DkNNRealQ` への持ち上げ

wrapper 側は、

```lean id="v9k8tu"
theorem mul_le_mul
    {x y z w : DkNNReal} (hxy : Le x y) (hzw : Le z w) :
    Le (mul x z) (mul y w)
```

で、非負性証明を wrapper から取り出して `DkReal.mulNonneg_le_mulNonneg` に渡している。これは綺麗じゃ。

quotient 側は、

```lean id="c91vyo"
theorem mul_le_mul
    {x y z w : DkNNRealQ} (hxy : x ≤ y) (hzw : z ≤ w) :
    x * z ≤ y * w
```

で、`Quotient.inductionOn₂` を二回使って代表元へ降りている。
これは前回の `add_le_add` と同じ構造で、問題なし。

## 6. 現在の到達点

ここまでで `DkNNRealQ` は、

```text id="injij8"
CommSemiring
PartialOrder
add_le_add
mul_le_mul
```

を持つ。

つまり、加法と乗法の両方が順序と両立した。
これはかなり大きい。

まだ正式な ordered semiring typeclass は入れていないが、必要な主要部品のかなり大きいところは揃ってきた。

## 7. 次の `pow` 単調性

報告通り、次は自然数冪の単調性じゃ。

ここは、今回の `mul_le_mul` を使えばかなり綺麗に閉じられるはずじゃ。

狙う形は、

```lean id="rb1cj8"
theorem pow_le_pow
    {x y : DkNNRealQ} (hxy : x ≤ y) (d : ℕ) :
    x ^ d ≤ y ^ d
```

帰納法で、

```text id="jdf2nz"
d = 0:
  1 ≤ 1

d + 1:
  x^(d+1) = x^d * x
  y^(d+1) = y^d * y
  use mul_le_mul ih hxy
```

という形じゃな。

すでに `CommSemiring` と `PartialOrder` があるので、`pow_succ` 系の標準補題が使える可能性が高い。
ただし独自 `Pow` instance と既存 `pow_succ` の simp の相性だけ確認すればよい。

## 8. ordered-semiring instance について

今回で乗法単調性まで来たので、ordered semiring 系 instance が近づいた。

ただし、まだ少し慎重でよい。
Mathlib の ordered semiring hierarchy は、単に `add_le_add` と `mul_le_mul` があるだけではなく、型class によって要求される形が異なる可能性がある。

次に確認すべきなのは、

```text id="l7jn8j"
0 ≤ 1
a ≤ b → c + a ≤ c + b
a ≤ b → 0 ≤ c → c * a ≤ c * b
a ≤ b → 0 ≤ c → a * c ≤ b * c
```

のような標準フィールドに、今の定理をどう合わせるかじゃ。

`DkNNRealQ` は非負型なので \(0\le x\) は全要素で成立するはずじゃ。
いずれ、

```lean id="h6dt92"
zero_le (x : DkNNRealQ) : 0 ≤ x
```

も欲しくなる。

これが通ると、ordered algebra の instance 化がかなり現実的になる。

## 9. 文書同期もよい

docs の更新も正しい。

```text id="2zj8c7"
addition and multiplication monotonicity are proved
power monotonicity remains
```

へ更新されている。
未実装領域が「冪単調性」と「意図する ordered-algebra hierarchy の検証」に絞られた。

これは地図として良い。
今どこまで到達して、何が残っているかが分かりやすい。

## 10. 小さな注意点

`mul_le_mul` という theorem 名は Mathlib 標準名と衝突しやすい。namespace 内なので直ちに問題ではないが、ordered semiring instance を入れた後は標準補題 `mul_le_mul` と混ざる可能性がある。

ただし、今の定理はまさに標準的な意味の `mul_le_mul` なので、名前としては自然じゃ。
将来 instance 化後に混乱が出たら、この独自 theorem は内部補題に寄せてもよい。

また、証明が lower endpoint のみで順序を扱っているため、将来 semantic bridge を作ったら、この order が `NNReal` の order と一致することを必ず確認したい。現段階では PartialOrder と単調性として正しく進んでおる。

## 11. 最終判定

今回の差分は **合格** じゃ。

```text id="iwru3z"
良い点:
  非負乗法の単調性を代表元レベルで証明した
  有界下端列と消える defect の積として処理している
  wrapper と quotient へきれいに持ち上げた
  add_le_add と同じ設計線で統一されている
  ordered-semiring claim はまだ保留している
  docs と TODO が同期している

次の課題:
  自然数冪の単調性
  全要素の zero_le
  ordered-semiring 系 typeclass の要件確認
  totality の検証
  BridgeNNReal との順序比較
```

うむ。
これで `DkNNRealQ` は、**加法も乗法も順序を保つ可換半環商型** になった。次の冪単調性は、今回の `mul_le_mul` を帰納的に使えばかなり見通しがよいぞい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean b/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean
index f250ccda..bd73a2ee 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean
@@ -26,9 +26,9 @@ Mathlib's `Real` is selected.
 `DkReal.Order` defines an asymptotic representative order, proves invariance
 under `DkNNReal.Equiv`, and installs a `PartialOrder` on this quotient.
 
-Addition is monotone for the asymptotic order. Establish monotonicity of
-multiplication and powers before extending the algebraic hierarchy to ordered
-semirings.
+Addition and multiplication are monotone for the asymptotic order. Establish
+power monotonicity and verify the intended ordered-algebra hierarchy before
+installing stronger typeclasses.
 
 [TODO] A semantic map to Mathlib's `NNReal` should be placed in a separate
 bridge module and proved to preserve zero, one, addition, multiplication,
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/Order.lean b/lean/dk_math/DkMath/Analysis/DkReal/Order.lean
index 04bafb73..9a3ef7c6 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/Order.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/Order.lean
@@ -26,9 +26,9 @@ partial order on `DkNNRealQ`.
 [TODO] Prove totality, or identify the additional representation theorem needed
 to derive it.
 
-Addition is monotone for this order. The corresponding results for
-multiplication by nonnegative values and natural powers remain prerequisites
-for ordered-semiring typeclasses.
+Addition and multiplication on nonnegative representations are monotone for
+this order. Natural-power monotonicity remains a prerequisite for the intended
+ordered-semiring API.
 -/
 
 namespace DkMath.Analysis.DkReal
@@ -165,6 +165,61 @@ theorem add_le_add
           le_max_right _ _
         linarith)
 
+/--
+Nonnegative multiplication is monotone for asymptotic order.
+
+The positive defect of a product is bounded by
+
+`x.lo * defect(z,w) + w.lo * defect(x,y)`.
+
+Both lower-endpoint sequences are uniformly bounded, while both defects tend
+to zero.
+-/
+theorem mulNonneg_le_mulNonneg
+    {x y z w : DkMath.Analysis.DkReal}
+    (hx : Nonnegative x) (hy : Nonnegative y)
+    (hz : Nonnegative z) (hw : Nonnegative w)
+    (hxy : Le x y) (hzw : Le z w) :
+    Le (mulNonneg x z hx hz) (mulNonneg y w hy hw) := by
+  have hleft :
+      Filter.Tendsto
+        (fun n => (x.interval n).lo * orderDefect z w n)
+        Filter.atTop (nhds 0) := by
+    simpa only [mul_comm] using
+      hzw.zero_mul_isBoundedUnder_le (isBoundedUnder_norm_lo x hx)
+  have hright :
+      Filter.Tendsto
+        (fun n => (w.interval n).lo * orderDefect x y n)
+        Filter.atTop (nhds 0) := by
+    simpa only [mul_comm] using
+      hxy.zero_mul_isBoundedUnder_le (isBoundedUnder_norm_lo w hw)
+  have hupper :
+      Filter.Tendsto
+        (fun n =>
+          (x.interval n).lo * orderDefect z w n +
+            (w.interval n).lo * orderDefect x y n)
+        Filter.atTop (nhds 0) := by
+    simpa only [zero_add] using hleft.add hright
+  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
+    tendsto_const_nhds hupper
+    (fun n => le_max_left 0 _)
+    (fun n => by
+      simp only [orderDefect, mulNonneg_interval, mulNonnegApprox,
+        GapInterval.mulNonneg_lo]
+      apply max_le
+      · exact add_nonneg
+          (mul_nonneg (hx n) (le_max_left _ _))
+          (mul_nonneg (hw n) (le_max_left _ _))
+      · have hzw' :
+            (z.interval n).lo - (w.interval n).lo ≤
+              max 0 ((z.interval n).lo - (w.interval n).lo) :=
+          le_max_right _ _
+        have hxy' :
+            (x.interval n).lo - (y.interval n).lo ≤
+              max 0 ((x.interval n).lo - (y.interval n).lo) :=
+          le_max_right _ _
+        nlinarith [hx n, hw n])
+
 end DkMath.Analysis.DkReal
 
 namespace DkMath.Analysis.DkNNReal
@@ -185,6 +240,13 @@ theorem add_le_add
     Le (add x z) (add y w) :=
   DkReal.add_le_add hxy hzw
 
+/-- Multiplication of nonnegative representatives is monotone in both arguments. -/
+theorem mul_le_mul
+    {x y z w : DkNNReal} (hxy : Le x y) (hzw : Le z w) :
+    Le (mul x z) (mul y w) :=
+  DkReal.mulNonneg_le_mulNonneg
+    x.nonnegative y.nonnegative z.nonnegative w.nonnegative hxy hzw
+
 end DkMath.Analysis.DkNNReal
 
 namespace DkMath.Analysis.DkNNRealQ
@@ -224,4 +286,14 @@ theorem add_le_add
   intro c d hcd
   exact DkNNReal.add_le_add hab hcd
 
+/-- Quotient multiplication is monotone in both arguments. -/
+theorem mul_le_mul
+    {x y z w : DkNNRealQ} (hxy : x ≤ y) (hzw : z ≤ w) :
+    x * z ≤ y * w := by
+  refine Quotient.inductionOn₂ x y ?_ hxy
+  intro a b hab
+  refine Quotient.inductionOn₂ z w ?_ hzw
+  intro c d hcd
+  exact DkNNReal.mul_le_mul hab hcd
+
 end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index 9a5ab6c2..c7bd4207 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -100,7 +100,7 @@ separate:
 ```text
 Order:
   PartialOrder is implemented via vanishing positive lower-endpoint defect
-  addition monotonicity is proved; multiplication and power monotonicity remain
+  addition and multiplication monotonicity are proved; power monotonicity remains
   investigate totality before any LinearOrder claim
 
 BridgeNNReal / BridgeReal:
diff --git a/lean/dk_math/DkMath/Analysis/docs/DkMath.Analysis_Design_Draft_2026-06-19.md b/lean/dk_math/DkMath/Analysis/docs/DkMath.Analysis_Design_Draft_2026-06-19.md
index 824642a3..d9501f47 100644
--- a/lean/dk_math/DkMath/Analysis/docs/DkMath.Analysis_Design_Draft_2026-06-19.md
+++ b/lean/dk_math/DkMath/Analysis/docs/DkMath.Analysis_Design_Draft_2026-06-19.md
@@ -49,8 +49,8 @@ The next independent tasks are:
 
 1. **Ordered algebra.** `DkReal.Order` now defines order by vanishing positive
    lower-endpoint defect, proves invariance under `Equiv`, and installs a
-   `PartialOrder` on `DkNNRealQ`. Addition is monotone. Next prove monotonicity of
-   multiplication, and powers, and investigate totality before claiming a
+   `PartialOrder` on `DkNNRealQ`. Addition and multiplication are monotone.
+   Next prove monotonicity of powers and investigate totality before claiming a
    `LinearOrder`.
 2. **Semantic evaluation.** In a separate `BridgeNNReal.lean` or
    `BridgeReal.lean`, extract the unique real point of a nested interval
diff --git a/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-CommSemiring-Checkpoint.md b/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-CommSemiring-Checkpoint.md
index ae56c0ee..d3c955e8 100644
--- a/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-CommSemiring-Checkpoint.md
+++ b/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-CommSemiring-Checkpoint.md
@@ -60,8 +60,8 @@ The next phase defines representative order by vanishing positive
 lower-endpoint defect. It is invariant under vanishing-separation equivalence
 and yields a `PartialOrder` on `DkNNRealQ`.
 
-Addition is monotone for this order. Remaining order work is multiplication
-and power monotonicity, together with the question of totality.
+Addition and multiplication are monotone for this order. Remaining order work
+is power monotonicity, together with the question of totality.
 No `LinearOrder` is claimed yet.
 
 ### Semantic Bridge
diff --git a/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md b/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
index f905da72..72986721 100644
--- a/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
+++ b/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
@@ -317,8 +317,8 @@ This completes the first algebraic public surface of the nonnegative
 computable-real quotient. The next phase defines asymptotic order by requiring
 the positive lower-endpoint defect to tend to zero. This relation is compatible
 with `Equiv` and gives `DkNNRealQ` a `PartialOrder`. Ordered-semiring instances
-remain deferred until multiplication and power monotonicity have been proved;
-addition monotonicity is now available.
+remain deferred until power monotonicity and the intended hierarchy have been
+verified; addition and multiplication monotonicity are now available.
 
 Any map to Mathlib's `NNReal` or `Real` should remain in a separate bridge
 module because selecting the represented limit may require `noncomputable`.
````
`````
