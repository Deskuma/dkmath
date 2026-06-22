# Git diff / Report / Review

## Upd: Analysis.DkReal.Order

gch: 27825e509e769f375061fb9ea9bb456906676cd9

## Report

ordered algebra の型クラス化を完了しました。

- `zero_le_one`
- 左右の加法単調性
- 左右の乗法単調性
- `IsOrderedRing DkNNRealQ` instance

この Mathlib 版の `IsOrderedRing` は歴史的名称で、要求する代数構造は `Semiring` です。加法逆元は不要です。

標準補題の解決、対象・全体ビルド、`git diff --check` は成功済みです。canonical order、strict order、linear order は未主張のままです。

## Review

## 1. 総評

うむ、今回も **合格** じゃ。
`DkNNRealQ` の ordered algebra 化が、ついに Mathlib の型クラス層へ接続された。

今回の中心はこれじゃ。

```lean id="isorderedring-core"
zero_le_one
add_le_add_left
add_le_add_right
mul_le_mul_of_nonneg_left
mul_le_mul_of_nonneg_right
instance : IsOrderedRing DkNNRealQ
```

特に重要なのは、`IsOrderedRing` という名前に引っ張られず、現行 Mathlib では semiring-level の ordered compatibility として使っている点じゃな。加法逆元や ring 構造を要求していない、という確認が通っているのは大きい。

## 2. `zero_le_one` は自然

```lean id="zero-le-one"
theorem zero_le_one : (0 : DkNNRealQ) ≤ 1 :=
  zero_le 1
```

これは `DkNNRealQ` が非負値型であることから直ちに出る。
すでに全要素について \(0\le x\) を証明しているので、\(x=1\) とすればよい。

これは `IsOrderedRing` の要求にそのまま合う。

## 3. 左右の加法単調性

```lean id="add-one-sided"
theorem add_le_add_left
    {x y : DkNNRealQ} (hxy : x ≤ y) (z : DkNNRealQ) :
    x + z ≤ y + z :=
  add_le_add hxy (le_refl z)

theorem add_le_add_right
    {x y : DkNNRealQ} (hxy : x ≤ y) (z : DkNNRealQ) :
    z + x ≤ z + y :=
  add_le_add (le_refl z) hxy
```

これは良い。
すでに強い二変数版

```lean id="add-strong"
add_le_add :
  x ≤ y → z ≤ w → x + z ≤ y + w
```

があるので、片側版は反射性で即座に出る。

Mathlib の ordered additive API は片側版を要求することが多いので、この補題を用意したのは正しい。

## 4. 左右の乗法単調性

```lean id="mul-one-sided"
theorem mul_le_mul_of_nonneg_left
    {x y : DkNNRealQ} (hxy : x ≤ y) (z : DkNNRealQ) :
    z * x ≤ z * y :=
  mul_le_mul (le_refl z) hxy

theorem mul_le_mul_of_nonneg_right
    {x y : DkNNRealQ} (hxy : x ≤ y) (z : DkNNRealQ) :
    x * z ≤ y * z :=
  mul_le_mul hxy (le_refl z)
```

ここも正しい。

`DkNNRealQ` は全要素が非負なので、Mathlib 側で要求される「非負因子による乗法単調性」は、より強い二変数版 `mul_le_mul` から出せる。

数学的には、

$$
x\le y
$$

なら任意の \(z\) について、

$$
zx\le zy
$$

かつ、

$$
xz\le yz
$$

が成り立つ。
非負型なので、\(z\ge0\) は自動的に `zero_le z` から来る。今回の instance 内では、要求された非負性引数を `_` で受けて使っていないが、これは「すべての元が非負」というより強い状況だから問題ない。

## 5. `IsOrderedRing` instance は妥当

```lean id="isorderedring-instance"
instance : IsOrderedRing DkNNRealQ where
  add_le_add_left _ _ h z := add_le_add_left h z
  zero_le_one := zero_le_one
  mul_le_mul_of_nonneg_left := by
    intro a _ b c hbc
    exact mul_le_mul_of_nonneg_left hbc a
  mul_le_mul_of_nonneg_right := by
    intro c _ a b hab
    exact mul_le_mul_of_nonneg_right hab c
```

これは良い。

今回の instance は、既に証明済みの構成要素をきれいに詰めている。

```text id="instance-sources"
PartialOrder:
  前段で実装済み

CommSemiring:
  前段で実装済み

add_le_add_left:
  add_le_add から導出

zero_le_one:
  zero_le 1

mul_le_mul_of_nonneg_left / right:
  mul_le_mul から導出
```

instance 本体で新しい数学証明をしていない。これは保守しやすい。

## 6. 名前の注意は文書で十分補えている

`IsOrderedRing` は名前だけ見ると ring を要求しそうに見えるが、今回の文書で「historical name」「algebraic assumption is only `Semiring`」と説明しているのは良い判断じゃ。

ここを残しておくと、未来の自分や Codex が、

```text id="ring-confusion"
DkNNRealQ は ring なのか？
加法逆元があるのか？
```

と誤解しにくい。

`DkNNRealQ` は非負型なので ring ではない。
今回入ったのは、semiring と partial order の両立性を表す predicate としての `IsOrderedRing` じゃ。

## 7. 未主張部分を残したのも正しい

文書で、

```text id="unclaimed"
canonical order
strict order
linear order
```

を未主張のまま残しているのは正しい。

今回到達したのは ordered semiring compatibility であって、まだ次のことは示していない。

```text id="not-yet"
任意の x y について x ≤ y または y ≤ x
x ≤ y が y = x + z と同値
厳密順序との整合性
NNReal の順序との同値
```

特に totality は、内部表現だけで証明するか、semantic bridge から持ち込むか、まだ設計判断が必要じゃ。

## 8. 現在の到達点

これで `DkNNRealQ` はかなり強い。

```text id="ordered-algebra-status"
DkNNRealQ:
  CommSemiring
  PartialOrder
  IsOrderedRing
  zero_le
  add_le_add
  mul_le_mul
  pow_le_pow
```

数学的には、

$$
\boxed{\text{DkNNRealQ は、非負計算可能実数商型として ordered semiring compatibility を持つ。}}
$$

と言ってよい。

もちろん、まだ `LinearOrderedSemiring` や `CanonicallyOrderedCommSemiring` ではない。
だが、ordered algebra の基礎 API としては一段閉じた。

## 9. 次の候補

次に進むなら、候補は三つじゃ。

```text id="next-paths"
1. totality の検証
2. canonical order 性の検証
3. BridgeNNReal / BridgeReal
```

わっちの推奨は、まず短く **ordered algebra checkpoint 文書** を更新して、ここを区切ることじゃ。
その後に totality へ行くか、BridgeNNReal へ行くかを選ぶとよい。

totality を内部だけでやるなら、下端点列の差の正部分か負部分のどちらかが 0 に行く、という形が必要になる。これは一般には少し繊細じゃ。
semantic bridge を作れば、`NNReal` の線形順序から totality を引ける可能性があるが、その場合は `noncomputable` を別ファイルに隔離する必要がある。

## 10. 最終判定

今回の差分は **合格** じゃ。

```text id="review-result"
良い点:
  zero_le_one を追加した
  左右の加法単調性を標準形で用意した
  左右の乗法単調性を標準形で用意した
  IsOrderedRing instance を実装した
  Semiring-level の historical name であることを文書化した
  canonical / strict / linear は未主張のまま残した

次の課題:
  ordered algebra checkpoint の文書化
  totality の検証
  canonical order 性の検証
  BridgeNNReal / BridgeReal での意味論比較
```

うむ。
これはかなり大きい節目じゃ。`DkNNRealQ` は、可換半環、半順序、そして Mathlib の ordered-semiring compatibility まで到達した。Route B の代数・順序の第一核は、ここでかなり綺麗に閉じたと言ってよいぞい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean b/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean
index 8347dd65..56c609ee 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean
@@ -27,8 +27,9 @@ Mathlib's `Real` is selected.
 under `DkNNReal.Equiv`, and installs a `PartialOrder` on this quotient.
 
 Addition, multiplication, and natural powers are monotone for the asymptotic
-order, and zero is the least quotient value. Verify the intended
-ordered-algebra hierarchy before installing stronger typeclasses.
+order, and zero is the least quotient value. `DkReal.Order` packages these
+facts as Mathlib's semiring-level `IsOrderedRing` predicate. Canonical,
+strict, and linear order structures remain unclaimed.
 
 [TODO] A semantic map to Mathlib's `NNReal` should be placed in a separate
 bridge module and proved to preserve zero, one, addition, multiplication,
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/Order.lean b/lean/dk_math/DkMath/Analysis/DkReal/Order.lean
index 879b89d2..977da526 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/Order.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/Order.lean
@@ -28,8 +28,9 @@ to derive it.
 
 Addition, multiplication on nonnegative representations, and natural powers
 are monotone for this order, and zero is the least quotient value. The
-remaining ordered-algebra work is to match these theorems with the intended
-typeclass hierarchy.
+quotient therefore carries Mathlib's `IsOrderedRing` predicate, whose name is
+historical: its algebraic assumption is only `Semiring`. No canonical-order,
+strict-order, or linear-order structure is claimed.
 -/
 
 namespace DkMath.Analysis.DkReal
@@ -305,6 +306,10 @@ theorem zero_le (x : DkNNRealQ) : 0 ≤ x := by
   intro a
   exact DkNNReal.zero_le a
 
+/-- Zero is below one. -/
+theorem zero_le_one : (0 : DkNNRealQ) ≤ 1 :=
+  zero_le 1
+
 /-- Quotient addition is monotone in both arguments. -/
 theorem add_le_add
     {x y z w : DkNNRealQ} (hxy : x ≤ y) (hzw : z ≤ w) :
@@ -315,6 +320,18 @@ theorem add_le_add
   intro c d hcd
   exact DkNNReal.add_le_add hab hcd
 
+/-- Addition by a fixed right summand preserves order. -/
+theorem add_le_add_left
+    {x y : DkNNRealQ} (hxy : x ≤ y) (z : DkNNRealQ) :
+    x + z ≤ y + z :=
+  add_le_add hxy (le_refl z)
+
+/-- Addition by a fixed left summand preserves order. -/
+theorem add_le_add_right
+    {x y : DkNNRealQ} (hxy : x ≤ y) (z : DkNNRealQ) :
+    z + x ≤ z + y :=
+  add_le_add (le_refl z) hxy
+
 /-- Quotient multiplication is monotone in both arguments. -/
 theorem mul_le_mul
     {x y z w : DkNNRealQ} (hxy : x ≤ y) (hzw : z ≤ w) :
@@ -325,6 +342,18 @@ theorem mul_le_mul
   intro c d hcd
   exact DkNNReal.mul_le_mul hab hcd
 
+/-- Multiplication by a fixed left factor preserves order. -/
+theorem mul_le_mul_of_nonneg_left
+    {x y : DkNNRealQ} (hxy : x ≤ y) (z : DkNNRealQ) :
+    z * x ≤ z * y :=
+  mul_le_mul (le_refl z) hxy
+
+/-- Multiplication by a fixed right factor preserves order. -/
+theorem mul_le_mul_of_nonneg_right
+    {x y : DkNNRealQ} (hxy : x ≤ y) (z : DkNNRealQ) :
+    x * z ≤ y * z :=
+  mul_le_mul hxy (le_refl z)
+
 /--
 Natural powers are monotone.
 
@@ -341,4 +370,23 @@ theorem pow_le_pow
       rw [pow_succ_eq, pow_succ_eq]
       exact mul_le_mul ih hxy
 
+/--
+Ordered-semiring compatibility for the quotient.
+
+Despite its historical name, Mathlib's `IsOrderedRing` requires only a
+`Semiring`, a partial order, monotone addition, `0 ≤ 1`, and monotonicity of
+multiplication by nonnegative factors. Every quotient value is nonnegative,
+so the stronger two-variable multiplication theorem supplies both one-sided
+fields.
+-/
+instance : IsOrderedRing DkNNRealQ where
+  add_le_add_left _ _ h z := add_le_add_left h z
+  zero_le_one := zero_le_one
+  mul_le_mul_of_nonneg_left := by
+    intro a _ b c hbc
+    exact mul_le_mul_of_nonneg_left hbc a
+  mul_le_mul_of_nonneg_right := by
+    intro c _ a b hab
+    exact mul_le_mul_of_nonneg_right hab c
+
 end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index 4e864c65..da120c23 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -102,7 +102,8 @@ Order:
   PartialOrder is implemented via vanishing positive lower-endpoint defect
   addition, multiplication, and natural-power monotonicity are proved
   zero is least
-  next package these results into the appropriate ordered-algebra typeclass
+  IsOrderedRing packages semiring-level ordered compatibility
+  canonical, strict, and linear order structures remain open
   investigate totality before any LinearOrder claim
 
 BridgeNNReal / BridgeReal:
diff --git a/lean/dk_math/DkMath/Analysis/docs/DkMath.Analysis_Design_Draft_2026-06-19.md b/lean/dk_math/DkMath/Analysis/docs/DkMath.Analysis_Design_Draft_2026-06-19.md
index 443b7d5c..8fd5e41a 100644
--- a/lean/dk_math/DkMath/Analysis/docs/DkMath.Analysis_Design_Draft_2026-06-19.md
+++ b/lean/dk_math/DkMath/Analysis/docs/DkMath.Analysis_Design_Draft_2026-06-19.md
@@ -50,9 +50,9 @@ The next independent tasks are:
 1. **Ordered algebra.** `DkReal.Order` now defines order by vanishing positive
    lower-endpoint defect, proves invariance under `Equiv`, and installs a
    `PartialOrder` on `DkNNRealQ`. Addition, multiplication, and natural powers
-   are monotone, and zero is least. Next package these results in the
-   appropriate ordered-algebra hierarchy and investigate totality before
-   claiming a `LinearOrder`.
+   are monotone, and zero is least. Mathlib's semiring-level `IsOrderedRing`
+   predicate is installed. Canonical order and totality remain to be
+   investigated before claiming stronger structures.
 2. **Semantic evaluation.** In a separate `BridgeNNReal.lean` or
    `BridgeReal.lean`, extract the unique real point of a nested interval
    representation and prove independence from representatives.
diff --git a/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-CommSemiring-Checkpoint.md b/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-CommSemiring-Checkpoint.md
index a03e2463..5f9e0ac2 100644
--- a/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-CommSemiring-Checkpoint.md
+++ b/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-CommSemiring-Checkpoint.md
@@ -61,8 +61,9 @@ lower-endpoint defect. It is invariant under vanishing-separation equivalence
 and yields a `PartialOrder` on `DkNNRealQ`.
 
 Addition, multiplication, and natural powers are monotone for this order.
-Zero is the least quotient value. Remaining ordered-algebra work is selecting
-the appropriate typeclass hierarchy, together with totality.
+Zero is the least quotient value. These facts provide Mathlib's `IsOrderedRing`
+predicate, which at this version requires only a semiring and partial order.
+Canonical order and totality remain separate questions.
 No `LinearOrder` is claimed yet.
 
 ### Semantic Bridge
diff --git a/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md b/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
index 468542dc..f72c5b0c 100644
--- a/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
+++ b/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
@@ -317,8 +317,9 @@ This completes the first algebraic public surface of the nonnegative
 computable-real quotient. The next phase defines asymptotic order by requiring
 the positive lower-endpoint defect to tend to zero. This relation is compatible
 with `Equiv` and gives `DkNNRealQ` a `PartialOrder`. Ordered-semiring instances
-remain deferred until the intended hierarchy has been verified; zero-minimality
-and addition, multiplication, and natural-power monotonicity are now available.
+now include the semiring-level `IsOrderedRing` predicate. Canonical, strict,
+and linear order structures remain deferred; zero-minimality and addition,
+multiplication, and natural-power monotonicity are available.
 
 Any map to Mathlib's `NNReal` or `Real` should remain in a separate bridge
 module because selecting the represented limit may require `noncomputable`.
````
`````
