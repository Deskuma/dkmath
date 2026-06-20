# Git diff / Report / Review

## Upd: Analysis.DkReal.Order

gch: 3ed8ee4e06313b67f5d9fa6c5146010590337afc

## Report

`zero_le` を実装しました。

- `DkReal.zero_le`
- `DkNNReal.zero_le`
- `DkNNRealQ.zero_le`

各区間の下端が非負なので、零からの order defect が恒等的にゼロとなる証明です。関連 docstring・設計文書も同期しました。

対象・全体ビルドと `git diff --check` は成功済みです。次は `IsOrderedRing` などへの型クラス化を独立して検証します。

## Review

## 1. 総評

うむ、今回も **合格** じゃ。
`DkNNRealQ` が非負型であることを、順序の側からきちんと閉じた差分じゃな。

今回の中心はこれじゃ。

```lean id="zle-core"
DkReal.zero_le
DkNNReal.zero_le
DkNNRealQ.zero_le
```

これで `DkNNRealQ` は、

```text id="zle-status"
CommSemiring
PartialOrder
add_le_add
mul_le_mul
pow_le_pow
zero_le
```

を持つところまで来た。
ordered algebra 化のための主要な手札は、かなり揃った。

## 2. `DkReal.zero_le` の証明は自然

定理本体はこれじゃな。

```lean id="dkreal-zero-le"
theorem zero_le
    {x : DkMath.Analysis.DkReal} (hx : Nonnegative x) :
    Le (DkMath.Analysis.DkReal.ofRat 0) x
```

順序定義では、

$$
orderDefect(0,x)_n=\max(0,0-lo(x_n))
$$

となる。
`Nonnegative x` なので各段で \(0\le lo(x_n)\)。したがって、

$$
0-lo(x_n)\le0
$$

ゆえに defect は常に 0。

つまり、

$$
orderDefect(0,x)_n=0
$$

が恒等的に成立し、その定数 0 列は 0 に収束する。
この証明は完全に順序定義に沿っている。

## 3. `DkNNReal.zero_le` は良い wrapper 化

```lean id="dknn-zero-le"
theorem zero_le (x : DkNNReal) : Le zero x :=
  DkReal.zero_le x.nonnegative
```

これは wrapper の役割そのものじゃ。
非負性証明を `x.nonnegative` から取り出し、`DkReal.zero_le` に渡している。

余計な再証明がなく、設計が綺麗じゃ。

## 4. `DkNNRealQ.zero_le` も正しい

```lean id="dknnq-zero-le"
theorem zero_le (x : DkNNRealQ) : 0 ≤ x := by
  refine Quotient.inductionOn x ?_
  intro a
  exact DkNNReal.zero_le a
```

商型上では代表元へ降りて、wrapper 側の `zero_le` を使う。
これは自然で問題なし。

これで商型上の任意要素について、

$$
0\le x
$$

が成立した。
`DkNNRealQ` が「非負値型」であることが、順序 API でも見えるようになったわけじゃ。

## 5. 現在の到達点

ここで、かなり重要な節目に来た。

```text id="ordered-surface"
DkNNRealQ:
  可換半環
  半順序
  0 は最小
  加法は単調
  乗法は単調
  自然数冪は単調
```

数学的には、

$$
\boxed{\text{DkNNRealQ は非負計算可能実数商型として、順序付き可換半環の主要性質を満たす。}}
$$

と言ってよい段階じゃ。

ただし、まだ正式な ordered-algebra typeclass を入れたわけではない。
ここを分けているのは正しい。

## 6. 次の typeclass 検証について

報告にある「`IsOrderedRing` など」は、少し注意じゃな。
`DkNNRealQ` は非負型なので、加法逆元を持つ ring ではない。したがって、基本的には **Ring 系ではなく Semiring 系** を見るべきじゃ。

候補としては Mathlib の実際の階層に合わせて、

```lean id="typeclass-candidates"
OrderedCommSemiring
CanonicallyOrderedCommSemiring
OrderedCancelAddCommMonoid
OrderedAddCommMonoid
```

のような方向を確認するのが自然じゃ。

特に `CanonicallyOrderedCommSemiring` 系を狙うなら、単に \(0\le x\) だけでなく、

```text id="canonical-order-risk"
x ≤ y なら、ある z が存在して y = x + z
```

に近い性質が要求される可能性がある。
これは今の asymptotic lower-endpoint order からすぐ軽く出るとは限らないので、まずは要求フィールドを確認するのがよい。

## 7. ordered semiring へ行く前の確認リスト

次の独立検証としては、この順がよさそうじゃ。

```text id="ordered-checklist"
1. Mathlib の対象 typeclass が何を要求するか確認
2. zero_le_one が既存の zero_le から出るか確認
3. add_le_add_left / add_le_add_right を標準形で用意
4. mul_le_mul_left / mul_le_mul_right を標準形で用意
5. 既存 add_le_add / mul_le_mul から instance field に合う形へ変換
```

すでに強めの定理

```lean id="strong-lemmas"
DkNNRealQ.add_le_add
DkNNRealQ.mul_le_mul
```

があるので、多くは片側版に特化すれば出るはずじゃ。

## 8. 文書更新も良い

docs の更新も正しい。

```text id="docs-current"
addition, multiplication, and natural-power monotonicity are proved
zero is least
next package these results into the appropriate ordered-algebra typeclass
```

という現在地になっている。
これは過大主張せず、次の検証対象を明確にしている。

## 9. 小さな注意点

`zero_le` という theorem 名は Mathlib 標準にも広くある。namespace 内では問題ないが、今後 ordered typeclass を導入すると、標準の `zero_le` 補題と見た目が重なる可能性はある。

ただし、内容としてはまさに標準的な `zero_le` なので、この名前でよい。
instance 化後に標準補題で置き換えられるなら、内部補題として残すだけでもよい。

## 10. 最終判定

今回の差分は **合格** じゃ。

```text id="zle-review"
良い点:
  DkReal レベルで zero_le を順序定義から直接証明した
  wrapper と quotient へ綺麗に持ち上げた
  DkNNRealQ が非負型であることを順序上も表現できた
  docs と TODO が現在地に同期している
  ordered typeclass の導入をまだ独立検証にしている

次の課題:
  Mathlib ordered-algebra hierarchy の要件確認
  片側単調性補題の整備
  ordered semiring 系 instance の選定
  totality の検証
  BridgeNNReal での順序比較
```

うむ。
これで `DkNNRealQ` は、可換半環としてだけでなく **0 を最小元に持つ半順序付き非負計算可能実数型** として見えてきた。次は、この手札が Mathlib のどの ordered-algebra class にぴたりとはまるかを見極める段階じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean b/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean
index d3f50a42..8347dd65 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean
@@ -27,8 +27,8 @@ Mathlib's `Real` is selected.
 under `DkNNReal.Equiv`, and installs a `PartialOrder` on this quotient.
 
 Addition, multiplication, and natural powers are monotone for the asymptotic
-order. Prove that zero is least and verify the intended ordered-algebra
-hierarchy before installing stronger typeclasses.
+order, and zero is the least quotient value. Verify the intended
+ordered-algebra hierarchy before installing stronger typeclasses.
 
 [TODO] A semantic map to Mathlib's `NNReal` should be placed in a separate
 bridge module and proved to preserve zero, one, addition, multiplication,
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/Order.lean b/lean/dk_math/DkMath/Analysis/DkReal/Order.lean
index 61d3173b..879b89d2 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/Order.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/Order.lean
@@ -27,9 +27,9 @@ partial order on `DkNNRealQ`.
 to derive it.
 
 Addition, multiplication on nonnegative representations, and natural powers
-are monotone for this order. The remaining ordered-algebra work is to prove
-that zero is least and to match these theorems with the intended typeclass
-hierarchy.
+are monotone for this order, and zero is the least quotient value. The
+remaining ordered-algebra work is to match these theorems with the intended
+typeclass hierarchy.
 -/
 
 namespace DkMath.Analysis.DkReal
@@ -134,6 +134,24 @@ theorem le_congr
     exact le_trans (equiv_le hxx')
       (le_trans hx'y' (equiv_le (equiv_symm hyy')))
 
+/--
+The rational zero approximation is below every nonnegative representation.
+
+At every stage its lower endpoint is zero, so the order defect is identically
+zero by nonnegativity of the other lower endpoint.
+-/
+theorem zero_le
+    {x : DkMath.Analysis.DkReal} (hx : Nonnegative x) :
+    Le (DkMath.Analysis.DkReal.ofRat 0) x := by
+  unfold Le orderDefect
+  simp only [ofRat_interval, GapInterval.singleton_lo, zero_sub]
+  have hzero :
+      (fun n => max 0 (-(x.interval n).lo)) = fun _ => (0 : ℚ) := by
+    funext n
+    exact max_eq_left (neg_nonpos.mpr (hx n))
+  rw [hzero]
+  exact tendsto_const_nhds
+
 /--
 Stagewise addition is monotone for asymptotic order.
 
@@ -235,6 +253,10 @@ theorem le_congr
     Le x y ↔ Le x' y' :=
   DkReal.le_congr hxx' hyy'
 
+/-- Zero is below every nonnegative representative. -/
+theorem zero_le (x : DkNNReal) : Le zero x :=
+  DkReal.zero_le x.nonnegative
+
 /-- Addition of nonnegative representatives is monotone in both arguments. -/
 theorem add_le_add
     {x y z w : DkNNReal} (hxy : Le x y) (hzw : Le z w) :
@@ -277,6 +299,12 @@ instance : PartialOrder DkNNRealQ where
     intro a b hab hba
     exact Quotient.sound (DkReal.equiv_of_le_of_le hab hba)
 
+/-- Zero is the least value of the nonnegative quotient. -/
+theorem zero_le (x : DkNNRealQ) : 0 ≤ x := by
+  refine Quotient.inductionOn x ?_
+  intro a
+  exact DkNNReal.zero_le a
+
 /-- Quotient addition is monotone in both arguments. -/
 theorem add_le_add
     {x y z w : DkNNRealQ} (hxy : x ≤ y) (hzw : z ≤ w) :
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index 09c6bcd2..4e864c65 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -101,7 +101,8 @@ separate:
 Order:
   PartialOrder is implemented via vanishing positive lower-endpoint defect
   addition, multiplication, and natural-power monotonicity are proved
-  next prove that zero is least and inspect ordered-algebra typeclass requirements
+  zero is least
+  next package these results into the appropriate ordered-algebra typeclass
   investigate totality before any LinearOrder claim
 
 BridgeNNReal / BridgeReal:
diff --git a/lean/dk_math/DkMath/Analysis/docs/DkMath.Analysis_Design_Draft_2026-06-19.md b/lean/dk_math/DkMath/Analysis/docs/DkMath.Analysis_Design_Draft_2026-06-19.md
index 0e91f259..443b7d5c 100644
--- a/lean/dk_math/DkMath/Analysis/docs/DkMath.Analysis_Design_Draft_2026-06-19.md
+++ b/lean/dk_math/DkMath/Analysis/docs/DkMath.Analysis_Design_Draft_2026-06-19.md
@@ -50,8 +50,9 @@ The next independent tasks are:
 1. **Ordered algebra.** `DkReal.Order` now defines order by vanishing positive
    lower-endpoint defect, proves invariance under `Equiv`, and installs a
    `PartialOrder` on `DkNNRealQ`. Addition, multiplication, and natural powers
-   are monotone. Next prove that zero is least, inspect the ordered-algebra
-   hierarchy, and investigate totality before claiming a `LinearOrder`.
+   are monotone, and zero is least. Next package these results in the
+   appropriate ordered-algebra hierarchy and investigate totality before
+   claiming a `LinearOrder`.
 2. **Semantic evaluation.** In a separate `BridgeNNReal.lean` or
    `BridgeReal.lean`, extract the unique real point of a nested interval
    representation and prove independence from representatives.
diff --git a/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-CommSemiring-Checkpoint.md b/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-CommSemiring-Checkpoint.md
index 5281b7fb..a03e2463 100644
--- a/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-CommSemiring-Checkpoint.md
+++ b/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-CommSemiring-Checkpoint.md
@@ -61,8 +61,8 @@ lower-endpoint defect. It is invariant under vanishing-separation equivalence
 and yields a `PartialOrder` on `DkNNRealQ`.
 
 Addition, multiplication, and natural powers are monotone for this order.
-Remaining ordered-algebra work includes proving that zero is least and
-selecting the appropriate typeclass hierarchy, together with totality.
+Zero is the least quotient value. Remaining ordered-algebra work is selecting
+the appropriate typeclass hierarchy, together with totality.
 No `LinearOrder` is claimed yet.
 
 ### Semantic Bridge
diff --git a/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md b/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
index c7c090dd..468542dc 100644
--- a/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
+++ b/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
@@ -317,9 +317,8 @@ This completes the first algebraic public surface of the nonnegative
 computable-real quotient. The next phase defines asymptotic order by requiring
 the positive lower-endpoint defect to tend to zero. This relation is compatible
 with `Equiv` and gives `DkNNRealQ` a `PartialOrder`. Ordered-semiring instances
-remain deferred until zero-minimality and the intended hierarchy have been
-verified; addition, multiplication, and natural-power monotonicity are now
-available.
+remain deferred until the intended hierarchy has been verified; zero-minimality
+and addition, multiplication, and natural-power monotonicity are now available.
 
 Any map to Mathlib's `NNReal` or `Real` should remain in a separate bridge
 module because selecting the represented limit may require `noncomputable`.
````
`````
