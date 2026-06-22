# Git diff / Report / Review

## Upd: Analysis.DkReal.Order

gch: c87a15dfdd60575fc5b28565d673f77ab433d487

## Report

次のチェックポイントとして、加法単調性を実装しました。

- `DkReal.add_le_add`
- `DkNNReal.add_le_add`
- `DkNNRealQ.add_le_add`
- 数学的 docstring と関連文書を同期
- TODO を乗法・冪の単調性、全順序性へ更新

検証済みです。

```text
lake build DkMath.Analysis.DkReal.Order
lake build DkMath.Analysis DkMath
git diff --check
```

次は非負乗法の単調性です。

## Review

## 1. 総評

うむ、今回も **合格** じゃ。
`DkNNRealQ` の `PartialOrder` に対して、最初の演算互換性である **加法単調性** が入った。これは ordered algebra へ進むための正しい第一歩じゃ。

今回の中心はこれじゃ。

```lean id="st855h"
DkReal.add_le_add
DkNNReal.add_le_add
DkNNRealQ.add_le_add
```

報告通り、`DkReal.Order` に加法単調性を追加し、wrapper、quotient へ順に持ち上げている。検証も `lake build DkMath.Analysis.DkReal.Order`、`lake build DkMath.Analysis DkMath`、`git diff --check` 成功とされている。

## 2. 数学的意味

今回示したのは、商型 `DkNNRealQ` 上で、

$$
x\le y,\quad z\le w\quad\Rightarrow\quad x+z\le y+w
$$

という加法の両側単調性じゃ。

順序は lower endpoint defect によって、

$$
\max(0,lo(x_n)-lo(y_n))\to0
$$

と定義されていた。
加法では lower endpoint が単純に足されるので、

$$
lo((x+z)_n)-lo((y+w)_n)=(lo(x_n)-lo(y_n))+(lo(z_n)-lo(w_n))
$$

となる。
したがって正の defect は、二つの defect の和で押さえられる。

$$
\max(0,a+b)\le \max(0,a)+\max(0,b)
$$

この評価で閉じている。方針は完全に自然じゃ。

## 3. `DkReal.add_le_add` のレビュー

```lean id="fd4ywb"
theorem add_le_add
    {x y z w : DkMath.Analysis.DkReal}
    (hxy : Le x y) (hzw : Le z w) :
    Le (add x z) (add y w)
```

この定理は、順序の代表元レベルでの本体じゃ。

証明では、

```lean id="za4re7"
orderDefect x y n + orderDefect z w n
```

が 0 に収束することをまず作り、それを上界として `tendsto_of_tendsto_of_tendsto_of_le_of_le` に渡している。

下界は `le_max_left 0 _` で defect 非負。
上界は endpoint の加法展開後に `linarith`。
これは順序定義と `GapInterval.add` の構造に素直に乗っている。問題なし。

## 4. `DkNNReal.add_le_add` の持ち上げ

```lean id="sb54lq"
theorem add_le_add
    {x y z w : DkNNReal} (hxy : Le x y) (hzw : Le z w) :
    Le (add x z) (add y w) :=
  DkReal.add_le_add hxy hzw
```

これは wrapper 側では単なる委譲で良い。
`DkNNReal.Le` は中身の `DkReal.Le` なので、証明を重ねずに済んでいる。

この設計はきれいじゃ。
代表元レベルの証明を `DkReal` 側へ集中し、wrapper と quotient は持ち上げだけにする流れが維持されている。

## 5. `DkNNRealQ.add_le_add` の quotient 化

```lean id="jmu4vw"
theorem add_le_add
    {x y z w : DkNNRealQ} (hxy : x ≤ y) (hzw : z ≤ w) :
    x + z ≤ y + w
```

ここも良い。

`Quotient.inductionOn₂` で `x,y` と `z,w` を代表元へ戻し、代表元上の `DkNNReal.add_le_add` を適用している。

これは商型上の順序で一番自然な形じゃ。
すでに `le` は `Quotient.liftOn₂` で定義され、`le_congr` により well-defined になっているので、この定理も素直に通る。

## 6. ここで得た構造

ここまでで `DkNNRealQ` は、

```text id="cfvgrn"
CommSemiring
PartialOrder
add_le_add
```

を持つ。

つまり、代数と順序が初めて接続された。

まだ ordered semiring ではないが、加法については順序互換性が確認された。
これは ordered algebra 化の第一関門を越えたということじゃ。

## 7. まだ足りないもの

文書更新でも正しく整理されている通り、残る主な順序互換性は、

```text id="oqpvtp"
非負乗法の単調性
自然数冪の単調性
全順序性の検証
```

じゃ。

特に次の本丸はこれ。

```lean id="vn0utn"
mul_le_mul :
  x ≤ y → z ≤ w → x * z ≤ y * w
```

`DkNNRealQ` は非負型なので、乗法単調性は期待できる。
ただし証明は加法より重い。lower endpoint の積差を扱うので、

$$
ab-cd=a(b-d)+d(a-c)
$$

あるいは単調性向けには、

$$
yz-xw=(y-x)z+x(w-z)
$$

のような分解を使うことになるはずじゃ。

代表元の lower endpoint が非負で有界であることも使う可能性が高い。
前に `equiv_mulNonneg` で使った端点有界性の道が再利用できるかもしれぬ。

## 8. 文書同期も良い

今回の docs 更新は適切じゃ。

```text id="3gms9v"
PartialOrder is implemented
addition monotonicity is proved
multiplication and power monotonicity remain
```

という現在地に更新されている。
特に `DkNNRealQ.lean` の TODO が、「加法・乗法・冪」から「乗法・冪」へ絞られたのは良い。実装済みと未実装の境界が明確になっている。

## 9. 小さな注意点

`add_le_add` という名前は Mathlib 標準にも多くあるので、namespace 内では問題ないが、今後 `open DkMath.Analysis.DkNNRealQ` などをしたときに名前衝突しやすい可能性はある。
ただし、ordered algebra の標準名としては自然なので、今のままでよい。

将来 `OrderedCancelAddCommMonoid` や `OrderedCommSemiring` 系の instance を入れるなら、この定理はそのフィールドや標準補題と重なる。
その段階で必要なら theorem 名を `add_le_add'` などに避難するか、標準 instance へ吸収すればよい。

## 10. 最終判定

今回の差分は **合格** じゃ。

```text id="ql3ikz"
良い点:
  代表元レベルで加法単調性を証明した
  wrapper と quotient へきれいに持ち上げた
  PartialOrder と CommSemiring の接続が始まった
  ordered-semiring claim はまだしていない
  docs と TODO が実装状態に同期している

次の課題:
  非負乗法の単調性
  自然数冪の単調性
  全順序性の検証
  ordered-semiring 系 instance の導入判断
```

うむ。
`DkNNRealQ` は、これで **可換半環、半順序、そして加法単調性** を持つところまで来た。次の山は乗法単調性じゃな。ここが通れば、ordered semiring へかなり近づくぞい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean b/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean
index 3ba7c40a..f250ccda 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean
@@ -26,8 +26,9 @@ Mathlib's `Real` is selected.
 `DkReal.Order` defines an asymptotic representative order, proves invariance
 under `DkNNReal.Equiv`, and installs a `PartialOrder` on this quotient.
 
-[TODO] Establish monotonicity of addition, multiplication, and powers for that
-order before extending the algebraic hierarchy to ordered semirings.
+Addition is monotone for the asymptotic order. Establish monotonicity of
+multiplication and powers before extending the algebraic hierarchy to ordered
+semirings.
 
 [TODO] A semantic map to Mathlib's `NNReal` should be placed in a separate
 bridge module and proved to preserve zero, one, addition, multiplication,
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/Order.lean b/lean/dk_math/DkMath/Analysis/DkReal/Order.lean
index 519fb127..04bafb73 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/Order.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/Order.lean
@@ -26,8 +26,9 @@ partial order on `DkNNRealQ`.
 [TODO] Prove totality, or identify the additional representation theorem needed
 to derive it.
 
-[TODO] Prove compatibility with addition, multiplication by nonnegative
-values, and natural powers before installing ordered-semiring typeclasses.
+Addition is monotone for this order. The corresponding results for
+multiplication by nonnegative values and natural powers remain prerequisites
+for ordered-semiring typeclasses.
 -/
 
 namespace DkMath.Analysis.DkReal
@@ -132,6 +133,38 @@ theorem le_congr
     exact le_trans (equiv_le hxx')
       (le_trans hx'y' (equiv_le (equiv_symm hyy')))
 
+/--
+Stagewise addition is monotone for asymptotic order.
+
+The positive defect of the sum is bounded by the sum of the two positive
+defects, and the latter tends to zero.
+-/
+theorem add_le_add
+    {x y z w : DkMath.Analysis.DkReal}
+    (hxy : Le x y) (hzw : Le z w) :
+    Le (add x z) (add y w) := by
+  have hupper :
+      Filter.Tendsto
+        (fun n => orderDefect x y n + orderDefect z w n)
+        Filter.atTop (nhds 0) := by
+    simpa only [zero_add] using hxy.add hzw
+  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
+    tendsto_const_nhds hupper
+    (fun n => le_max_left 0 _)
+    (fun n => by
+      simp only [orderDefect, add_interval, addApprox, GapInterval.add]
+      apply max_le
+      · exact add_nonneg (le_max_left _ _) (le_max_left _ _)
+      · have hxy' :
+            (x.interval n).lo - (y.interval n).lo ≤
+              max 0 ((x.interval n).lo - (y.interval n).lo) :=
+          le_max_right _ _
+        have hzw' :
+            (z.interval n).lo - (w.interval n).lo ≤
+              max 0 ((z.interval n).lo - (w.interval n).lo) :=
+          le_max_right _ _
+        linarith)
+
 end DkMath.Analysis.DkReal
 
 namespace DkMath.Analysis.DkNNReal
@@ -146,6 +179,12 @@ theorem le_congr
     Le x y ↔ Le x' y' :=
   DkReal.le_congr hxx' hyy'
 
+/-- Addition of nonnegative representatives is monotone in both arguments. -/
+theorem add_le_add
+    {x y z w : DkNNReal} (hxy : Le x y) (hzw : Le z w) :
+    Le (add x z) (add y w) :=
+  DkReal.add_le_add hxy hzw
+
 end DkMath.Analysis.DkNNReal
 
 namespace DkMath.Analysis.DkNNRealQ
@@ -175,4 +214,14 @@ instance : PartialOrder DkNNRealQ where
     intro a b hab hba
     exact Quotient.sound (DkReal.equiv_of_le_of_le hab hba)
 
+/-- Quotient addition is monotone in both arguments. -/
+theorem add_le_add
+    {x y z w : DkNNRealQ} (hxy : x ≤ y) (hzw : z ≤ w) :
+    x + z ≤ y + w := by
+  refine Quotient.inductionOn₂ x y ?_ hxy
+  intro a b hab
+  refine Quotient.inductionOn₂ z w ?_ hzw
+  intro c d hcd
+  exact DkNNReal.add_le_add hab hcd
+
 end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index 9d137dad..9a5ab6c2 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -100,7 +100,7 @@ separate:
 ```text
 Order:
   PartialOrder is implemented via vanishing positive lower-endpoint defect
-  next prove operation monotonicity
+  addition monotonicity is proved; multiplication and power monotonicity remain
   investigate totality before any LinearOrder claim
 
 BridgeNNReal / BridgeReal:
diff --git a/lean/dk_math/DkMath/Analysis/docs/DkMath.Analysis_Design_Draft_2026-06-19.md b/lean/dk_math/DkMath/Analysis/docs/DkMath.Analysis_Design_Draft_2026-06-19.md
index 83dec1a3..824642a3 100644
--- a/lean/dk_math/DkMath/Analysis/docs/DkMath.Analysis_Design_Draft_2026-06-19.md
+++ b/lean/dk_math/DkMath/Analysis/docs/DkMath.Analysis_Design_Draft_2026-06-19.md
@@ -49,7 +49,7 @@ The next independent tasks are:
 
 1. **Ordered algebra.** `DkReal.Order` now defines order by vanishing positive
    lower-endpoint defect, proves invariance under `Equiv`, and installs a
-   `PartialOrder` on `DkNNRealQ`. Next prove monotonicity of addition,
+   `PartialOrder` on `DkNNRealQ`. Addition is monotone. Next prove monotonicity of
    multiplication, and powers, and investigate totality before claiming a
    `LinearOrder`.
 2. **Semantic evaluation.** In a separate `BridgeNNReal.lean` or
diff --git a/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-CommSemiring-Checkpoint.md b/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-CommSemiring-Checkpoint.md
index d867f614..ae56c0ee 100644
--- a/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-CommSemiring-Checkpoint.md
+++ b/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-CommSemiring-Checkpoint.md
@@ -60,7 +60,8 @@ The next phase defines representative order by vanishing positive
 lower-endpoint defect. It is invariant under vanishing-separation equivalence
 and yields a `PartialOrder` on `DkNNRealQ`.
 
-Remaining order work is operation monotonicity and the question of totality.
+Addition is monotone for this order. Remaining order work is multiplication
+and power monotonicity, together with the question of totality.
 No `LinearOrder` is claimed yet.
 
 ### Semantic Bridge
diff --git a/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md b/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
index adc207de..f905da72 100644
--- a/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
+++ b/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
@@ -317,7 +317,8 @@ This completes the first algebraic public surface of the nonnegative
 computable-real quotient. The next phase defines asymptotic order by requiring
 the positive lower-endpoint defect to tend to zero. This relation is compatible
 with `Equiv` and gives `DkNNRealQ` a `PartialOrder`. Ordered-semiring instances
-remain deferred until operation monotonicity has been proved.
+remain deferred until multiplication and power monotonicity have been proved;
+addition monotonicity is now available.
 
 Any map to Mathlib's `NNReal` or `Real` should remain in a separate bridge
 module because selecting the represented limit may require `noncomputable`.
````
`````
