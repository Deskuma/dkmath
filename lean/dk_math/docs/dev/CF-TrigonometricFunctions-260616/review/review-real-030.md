# Git diff / Report / Review

## Add: Analysis.DkReal.Order

gch: f494fb3a79014d9c1a0438fe5bbb67f9984af516

## Report

レビュアー指摘2点を修正し、新フェーズへ進めました。

- 自然数埋め込みを定数区間列 `k ↦ [n,n]` と明記
- `noncomputable` 不使用の主張を計算可能コアに限定
- `DkReal/Order.lean` を新設
- 漸近的な区間下端比較を定義
- 同値関係との整合性、反射性、推移性、反対称性を証明
- `DkNNRealQ` に `PartialOrder` を実装
- 公開 import、docstring、設計資料、TODO を同期

検証済みです。

```text
lake build DkMath.Analysis.DkReal.Order DkMath.Analysis DkMath
git diff --check
```

次の本線は、加法・非負乗法・冪に対する順序単調性、その後に全順序性または意味論 bridge です。

## Review

## 1. 総評

うむ、今回も **合格** じゃ。
ついに `DkNNRealQ` に順序が入った。前回までで `CommSemiring` が閉じ、今回で `PartialOrder` が商型上に実装された。これは Route B の次フェーズに進んだ差分じゃな。

今回の中心はこれじゃ。

```lean id="oxm7ua"
DkReal.orderDefect
DkReal.Le
DkReal.equiv_of_le_of_le
DkReal.le_congr
DkNNRealQ.PartialOrder
```

報告通り、漸近的な区間下端比較を定義し、`Equiv` との整合性、反射性、推移性、反対称性を証明して、`DkNNRealQ` に `PartialOrder` を入れている。検証も `lake build DkMath.Analysis.DkReal.Order DkMath.Analysis DkMath` と `git diff --check` 成功とされている。

これは良い進み方じゃ。順序を semantic `Real` 評価から持ってくるのではなく、Route B の内部表現から作っている。

## 2. 順序定義の意味

今回の定義はこれじゃな。

```lean id="wicm3u"
def orderDefect (x y : DkReal) (n : ℕ) : ℚ :=
  max 0 ((x.interval n).lo - (y.interval n).lo)

def Le (x y : DkReal) : Prop :=
  Filter.Tendsto (orderDefect x y) Filter.atTop (nhds 0)
```

つまり \(x\le y\) を、

$$
\max(0,lo(x_n)-lo(y_n))\to0
$$

で定義している。

これは「下端点が最終的に \(y\) を正に超える量が 0 に消える」という順序じゃ。
厳密に言えば、各段で \(lo(x_n)\le lo(y_n)\) を要求するのではなく、**正の超過分が消える** ことを要求する。

`Equiv` が separation の 0 収束である以上、この asymptotic order は自然じゃ。代表元の揺れを許して、商上で安定するように設計されている。

## 3. 反射性は問題なし

```lean id="xttali"
theorem le_refl (x : DkReal) : Le x x
```

これは当然、

$$
lo(x_n)-lo(x_n)=0
$$

なので defect は常に 0。問題なしじゃ。

## 4. `equiv_le` が良い

```lean id="s2kxeo"
theorem equiv_le {x y : DkReal} (hxy : Equiv x y) : Le x y
```

これは重要じゃ。
`Equiv x y` なら lower endpoint 差が 0 に収束することを前回すでに証明している。そこから正の部分だけを取った `max 0 (...)` も 0 に収束する。

数学的には、

$$
lo(x_n)-lo(y_n)\to0
$$

なら、

$$
\max(0,lo(x_n)-lo(y_n))\to0
$$

ということじゃ。

これにより、同値な表現は互いに \(\le\) になる。
後で反対称性を quotient equality に落とすための基礎じゃな。

## 5. 推移性も正しい

```lean id="fh1z1g"
theorem le_trans {x y z : DkReal} (hxy : Le x y) (hyz : Le y z) : Le x z
```

証明は、

$$
lo(x_n)-lo(z_n)=(lo(x_n)-lo(y_n))+(lo(y_n)-lo(z_n))
$$

を使い、正の部分を二つの正の部分の和で押さえる形じゃ。

$$
\max(0,a+c)\le\max(0,a)+\max(0,c)
$$

の有理数版になっている。
実装でも `orderDefect x y + orderDefect y z` が 0 に収束し、`orderDefect x z` を上下から挟んでいる。問題なし。

## 6. 反対称性の核が良い

今回の要はこれじゃ。

```lean id="5t0l8b"
theorem equiv_of_le_of_le
    {x y : DkReal} (hxy : Le x y) (hyx : Le y x) :
    Equiv x y
```

互いに \(x\le y\)、\(y\le x\) なら、

$$
\max(0,lo(x_n)-lo(y_n))\to0
$$

かつ、

$$
\max(0,lo(y_n)-lo(x_n))\to0
$$

なので、

$$
|lo(x_n)-lo(y_n)|\to0
$$

が出る。
そして前回の補題、

$$
separation(I_n,J_n)\le |lo(I_n)-lo(J_n)|
$$

で `Equiv` が出る。

これは非常に良い。
商型上の antisymmetry は、代表元ではなく `Equiv` に落とす必要がある。今回の定理がその橋じゃ。

## 7. `le_congr` は quotient lift の鍵

```lean id="yv5xer"
theorem le_congr
    {x x' y y' : DkReal}
    (hxx' : Equiv x x') (hyy' : Equiv y y') :
    Le x y ↔ Le x' y'
```

これは必須補題じゃ。
`DkNNRealQ` の `le` は quotient representative に依存してはいけない。`le_congr` によって、代表元を同値なものへ取り替えても `Le` が保存される。

証明は、

$$
x'\sim x,\quad x\le y,\quad y\sim y'
$$

を `equiv_le` と `le_trans` でつないでいる。これは自然。

## 8. `DkNNRealQ.PartialOrder` は妥当

`DkNNRealQ.le` は、

```lean id="h8kkec"
Quotient.liftOn₂ x y DkNNReal.Le ...
```

で定義されている。well-defined proof は `DkNNReal.le_congr`。
そして `PartialOrder` は、

```lean id="afvgh3"
le_refl
le_trans
le_antisymm
```

を quotient induction で証明している。

特に antisymmetry は、

```lean id="nqdh2v"
Quotient.sound (DkReal.equiv_of_le_of_le hab hba)
```

で落ちている。
これは商型設計として正しい。

## 9. 今回の数学的到達点

ここまでで `DkNNRealQ` は、

```text id="h7sc3g"
CommSemiring
PartialOrder
```

を持つようになった。

ただし、まだ

```text id="cq10ca"
OrderedSemiring
CanonicallyOrderedCommSemiring
LinearOrder
```

ではない。

この区別は重要じゃ。
順序は入ったが、加法・乗法との単調性はまだ証明していない。文書でも「次は加法・非負乗法・冪に対する順序単調性、その後に全順序性または意味論 bridge」と整理されている。

この慎重さは正しい。

## 10. 順序定義についての注意

下端点だけで order を定義している点は、今後必ず検証対象になる。

直感的には、幅が 0 に縮むので下端点の asymptotic comparison だけで値の順序を表せるはずじゃ。
だが、全順序性や semantic `NNReal` 順序との一致を示すには、追加証明が必要になる。

特に次の二つは今後の重要補題じゃ。

```lean id="rqa4dd"
le_total_candidate :
  Le x y ∨ Le y x

le_iff_eval_le_eval :
  x ≤ y ↔ eval x ≤ eval y
```

前者を内部的に示せるか、後者を bridge で示して totality を持ってくるか、ここが次の設計分岐じゃな。

## 11. operation monotonicity の次候補

次に欲しいのは、少なくともこれじゃ。

```lean id="znfaf5"
add_le_add :
  x ≤ y → z ≤ w → x + z ≤ y + w

mul_le_mul_nonneg :
  x ≤ y → z ≤ w → x * z ≤ y * w

pow_mono :
  x ≤ y → x ^ n ≤ y ^ n
```

ただし `DkNNRealQ` は非負型なので、乗法の単調性はかなり期待できる。
内部代表元で見るなら、lower endpoint の defect が加法では足し合わされ、乗法では端点有界性や非負性を使うことになりそうじゃ。

急ぐなら、まず加法単調性からが良い。
加法は `orderDefect` の劣加法だけで閉じるはずじゃ。

## 12. docs 同期も良い

今回の docs 更新は適切じゃ。

```text id="a43vet"
DkReal.Order:
  asymptotic lower-endpoint order
  Equiv compatibility
  PartialOrder on DkNNRealQ
```

と `Analysis-Initial-Layer.md` に追記し、設計ドラフトも「Order design」から「Ordered algebra」へ更新している。
さらに、`DkNNRealQ-CommSemiring-Checkpoint.md` の記述も、PartialOrder は実装済み、残りは単調性と totality と修正されている。

実装進行と文書が同期しているのは良い。

## 13. 最終判定

今回の差分は **合格** じゃ。

```text id="if5nuo"
良い点:
  orderDefect による asymptotic order を定義した
  Equiv との両立を証明した
  quotient 上に PartialOrder を入れた
  antisymmetry を Equiv 経由で正しく処理した
  Real / NNReal evaluation に頼っていない
  ordered-semiring / linear-order claim をまだしていない
  docs と TODO を同期した

次の課題:
  加法単調性
  非負乗法単調性
  冪単調性
  totality の検証
  BridgeNNReal / BridgeReal との順序比較
```

うむ。
`DkNNRealQ` はこれで **可換半環かつ半順序型** になった。次はこの二つを結ぶ段階じゃ。つまり、代数と順序を接続し、`Ordered` な構造へ進めるかを検証する山じゃな。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 80f7f83a..53593a09 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -12,6 +12,7 @@ import DkMath.Analysis.DkReal.Arithmetic
 import DkMath.Analysis.DkReal.Equiv
 import DkMath.Analysis.DkReal.DkNNReal
 import DkMath.Analysis.DkReal.DkNNRealQ
+import DkMath.Analysis.DkReal.Order
 
 #print "file: DkMath.Analysis.DkReal"
 
@@ -29,8 +30,11 @@ Public entry point for the complete Route B algebraic checkpoint:
 All endpoint operations in this import tree remain computable. No represented
 limit in Mathlib's `Real` or `NNReal` is selected here.
 
-[TODO] Define a quotient-compatible order, or derive it from a separately
-isolated semantic evaluation map.
+`DkReal.Order` defines a quotient-compatible asymptotic order and installs a
+`PartialOrder` on `DkNNRealQ`.
+
+[TODO] Prove additive and multiplicative monotonicity, then determine whether
+the quotient order is total before installing ordered-semiring typeclasses.
 
 [TODO] Add `BridgeNNReal.lean` / `BridgeReal.lean` only after proving that the
 chosen evaluation is independent of representatives. Such evaluation may
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean b/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean
index f4ee9e64..3ba7c40a 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean
@@ -23,8 +23,11 @@ This remains a computable representation layer. Quotient elimination is used
 only to define representation-independent operations; no evaluation into
 Mathlib's `Real` is selected.
 
-[TODO] Before adding an order instance, define an order predicate on
-representatives and prove invariance under `DkNNReal.Equiv` in both arguments.
+`DkReal.Order` defines an asymptotic representative order, proves invariance
+under `DkNNReal.Equiv`, and installs a `PartialOrder` on this quotient.
+
+[TODO] Establish monotonicity of addition, multiplication, and powers for that
+order before extending the algebraic hierarchy to ordered semirings.
 
 [TODO] A semantic map to Mathlib's `NNReal` should be placed in a separate
 bridge module and proved to preserve zero, one, addition, multiplication,
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/Order.lean b/lean/dk_math/DkMath/Analysis/DkReal/Order.lean
new file mode 100644
index 00000000..519fb127
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/DkReal/Order.lean
@@ -0,0 +1,178 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Analysis.DkReal.DkNNRealQ
+
+#print "file: DkMath.Analysis.DkReal.Order"
+
+/-!
+# Asymptotic order for DkReal representations
+
+For two interval representations `x` and `y`, define the order defect at stage
+`n` by
+
+`max 0 (x.lo n - y.lo n)`.
+
+The relation `x ≤ y` means that this positive defect tends to zero. It is a
+preorder on representations. Mutual order is equivalent to vanishing
+lower-endpoint distance and therefore implies `DkReal.Equiv`.
+
+The relation is invariant under `Equiv` in both arguments, so it descends to a
+partial order on `DkNNRealQ`.
+
+[TODO] Prove totality, or identify the additional representation theorem needed
+to derive it.
+
+[TODO] Prove compatibility with addition, multiplication by nonnegative
+values, and natural powers before installing ordered-semiring typeclasses.
+-/
+
+namespace DkMath.Analysis.DkReal
+
+/-- Positive lower-endpoint order defect at approximation stage `n`. -/
+def orderDefect
+    (x y : DkMath.Analysis.DkReal) (n : ℕ) : ℚ :=
+  max 0 ((x.interval n).lo - (y.interval n).lo)
+
+/--
+Asymptotic order on interval representations.
+
+`Le x y` states that any positive excess of the lower endpoint of `x` over
+that of `y` vanishes with increasing precision.
+-/
+def Le (x y : DkMath.Analysis.DkReal) : Prop :=
+  Filter.Tendsto (orderDefect x y) Filter.atTop (nhds 0)
+
+/-- Asymptotic order is reflexive. -/
+theorem le_refl (x : DkMath.Analysis.DkReal) : Le x x := by
+  unfold Le orderDefect
+  simp only [sub_self, max_self]
+  exact tendsto_const_nhds
+
+/-- Representation equivalence implies asymptotic order. -/
+theorem equiv_le
+    {x y : DkMath.Analysis.DkReal} (hxy : Equiv x y) :
+    Le x y := by
+  have hlo := equiv_tendsto_lo_sub_zero hxy
+  simpa only [Le, orderDefect, max_comm] using
+    hlo.max tendsto_const_nhds
+
+/-- Asymptotic order is transitive. -/
+theorem le_trans
+    {x y z : DkMath.Analysis.DkReal} (hxy : Le x y) (hyz : Le y z) :
+    Le x z := by
+  have hupper :
+      Filter.Tendsto
+        (fun n => orderDefect x y n + orderDefect y z n)
+        Filter.atTop (nhds 0) := by
+    simpa only [zero_add] using hxy.add hyz
+  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
+    tendsto_const_nhds hupper
+    (fun n => le_max_left 0 _)
+    (fun n => by
+      simp only [orderDefect]
+      have hxy' :
+          (x.interval n).lo - (y.interval n).lo ≤
+            max 0 ((x.interval n).lo - (y.interval n).lo) :=
+        le_max_right _ _
+      have hyz' :
+          (y.interval n).lo - (z.interval n).lo ≤
+            max 0 ((y.interval n).lo - (z.interval n).lo) :=
+        le_max_right _ _
+      apply max_le
+      · exact add_nonneg (le_max_left _ _) (le_max_left _ _)
+      · linarith)
+
+/-- Mutual asymptotic order implies representation equivalence. -/
+theorem equiv_of_le_of_le
+    {x y : DkMath.Analysis.DkReal} (hxy : Le x y) (hyx : Le y x) :
+    Equiv x y := by
+  have hsum :
+      Filter.Tendsto
+        (fun n => orderDefect x y n + orderDefect y x n)
+        Filter.atTop (nhds 0) := by
+    simpa only [zero_add] using hxy.add hyx
+  have habs :
+      Filter.Tendsto
+        (fun n => |(x.interval n).lo - (y.interval n).lo|)
+        Filter.atTop (nhds 0) := by
+    convert hsum using 1
+    · funext n
+      simp only [orderDefect]
+      by_cases h :
+          0 ≤ (x.interval n).lo - (y.interval n).lo
+      · rw [abs_of_nonneg h, max_eq_right h]
+        have hneg :
+            (y.interval n).lo - (x.interval n).lo ≤ 0 := by linarith
+        simp [hneg]
+      · have hneg :
+            (x.interval n).lo - (y.interval n).lo ≤ 0 := le_of_not_ge h
+        have hrev :
+            0 ≤ (y.interval n).lo - (x.interval n).lo := by linarith
+        rw [abs_of_nonpos hneg]
+        simp [hneg, hrev]
+  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
+    tendsto_const_nhds habs
+    (fun n => (x.interval n).separation_nonneg (y.interval n))
+    (fun n => (x.interval n).separation_le_abs_lo_sub_lo (y.interval n))
+
+/-- Equivalent replacement of either argument preserves asymptotic order. -/
+theorem le_congr
+    {x x' y y' : DkMath.Analysis.DkReal}
+    (hxx' : Equiv x x') (hyy' : Equiv y y') :
+    Le x y ↔ Le x' y' := by
+  constructor
+  · intro hxy
+    exact le_trans (equiv_le (equiv_symm hxx'))
+      (le_trans hxy (equiv_le hyy'))
+  · intro hx'y'
+    exact le_trans (equiv_le hxx')
+      (le_trans hx'y' (equiv_le (equiv_symm hyy')))
+
+end DkMath.Analysis.DkReal
+
+namespace DkMath.Analysis.DkNNReal
+
+/-- Asymptotic order lifted to nonnegative representation wrappers. -/
+def Le (x y : DkNNReal) : Prop :=
+  DkReal.Le x.val y.val
+
+/-- Wrapper equivalence preserves asymptotic order in both arguments. -/
+theorem le_congr
+    {x x' y y' : DkNNReal} (hxx' : Equiv x x') (hyy' : Equiv y y') :
+    Le x y ↔ Le x' y' :=
+  DkReal.le_congr hxx' hyy'
+
+end DkMath.Analysis.DkNNReal
+
+namespace DkMath.Analysis.DkNNRealQ
+
+/-- Quotient order induced by asymptotic order on representatives. -/
+def le (x y : DkNNRealQ) : Prop :=
+  Quotient.liftOn₂ x y DkNNReal.Le
+    (by
+      intro a a' b b' haa' hbb'
+      exact propext (DkNNReal.le_congr haa' hbb'))
+
+instance : LE DkNNRealQ where
+  le := le
+
+/-- The quotient order is a partial order. -/
+instance : PartialOrder DkNNRealQ where
+  le_refl x := by
+    refine Quotient.inductionOn x ?_
+    intro a
+    exact DkReal.le_refl a.val
+  le_trans x y z := by
+    refine Quotient.inductionOn₃ x y z ?_
+    intro a b c hab hbc
+    exact DkReal.le_trans hab hbc
+  le_antisymm x y := by
+    refine Quotient.inductionOn₂ x y ?_
+    intro a b hab hba
+    exact Quotient.sound (DkReal.equiv_of_le_of_le hab hba)
+
+end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index 5aaa5f85..9d137dad 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -74,6 +74,10 @@ DkMath.Analysis.DkReal.DkNNRealQ
   quotient-backed nonnegative type with Zero / One / Add / Mul / Pow and
   a canonical NatCast and CommSemiring instance
 
+DkMath.Analysis.DkReal.Order
+  asymptotic lower-endpoint order, Equiv compatibility, and PartialOrder on
+  DkNNRealQ
+
 DkMath.Analysis.DkReal
   public entry point for the computable approximation layer
 ```
@@ -95,10 +99,9 @@ separate:
 
 ```text
 Order:
-  define a representative relation
-  prove Equiv compatibility
-  lift to DkNNRealQ
-  prove partial or linear order laws
+  PartialOrder is implemented via vanishing positive lower-endpoint defect
+  next prove operation monotonicity
+  investigate totality before any LinearOrder claim
 
 BridgeNNReal / BridgeReal:
   select the unique semantic limit
diff --git a/lean/dk_math/DkMath/Analysis/docs/DkMath.Analysis_Design_Draft_2026-06-19.md b/lean/dk_math/DkMath/Analysis/docs/DkMath.Analysis_Design_Draft_2026-06-19.md
index e794a172..83dec1a3 100644
--- a/lean/dk_math/DkMath/Analysis/docs/DkMath.Analysis_Design_Draft_2026-06-19.md
+++ b/lean/dk_math/DkMath/Analysis/docs/DkMath.Analysis_Design_Draft_2026-06-19.md
@@ -47,9 +47,11 @@ Semantic bridge layer:
 
 The next independent tasks are:
 
-1. **Order design.** Define a relation on representatives, prove invariance
-   under `Equiv`, then lift it to `DkNNRealQ`. Do not install an order instance
-   before antisymmetry on quotient values is established.
+1. **Ordered algebra.** `DkReal.Order` now defines order by vanishing positive
+   lower-endpoint defect, proves invariance under `Equiv`, and installs a
+   `PartialOrder` on `DkNNRealQ`. Next prove monotonicity of addition,
+   multiplication, and powers, and investigate totality before claiming a
+   `LinearOrder`.
 2. **Semantic evaluation.** In a separate `BridgeNNReal.lean` or
    `BridgeReal.lean`, extract the unique real point of a nested interval
    representation and prove independence from representatives.
diff --git a/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-CommSemiring-Checkpoint.md b/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-CommSemiring-Checkpoint.md
index 22102e0e..d867f614 100644
--- a/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-CommSemiring-Checkpoint.md
+++ b/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-CommSemiring-Checkpoint.md
@@ -24,7 +24,8 @@ The following data remain in the computable representation layer:
 - quotient operations and natural-number casts.
 
 No point of Mathlib's `Real` or `NNReal` is selected. In particular, the
-Route B import tree contains no `noncomputable` declaration.
+`DkReal` / `DkNNRealQ` computable core contains no `noncomputable`
+declaration.
 
 ## Algebraic Meaning
 
@@ -33,10 +34,11 @@ removes representation dependence. Consequently, laws formerly stated modulo
 `DkNNReal.Equiv` become ordinary equality and support the standard Mathlib
 commutative-semiring API.
 
-The natural-number cast is the constant singleton representation:
+The natural-number cast is the equivalence class of the constant singleton
+interval sequence:
 
 ```text
-n |-> class([n,n], [n,n], ...).
+n |-> class of the sequence k |-> [n,n].
 ```
 
 ## Scope
@@ -54,9 +56,12 @@ This checkpoint does not establish:
 
 ### Order
 
-A representative-level order must be invariant under vanishing-separation
-equivalence. Candidate formulations should be compared before installing
-`LE`, `PartialOrder`, or `LinearOrder`.
+The next phase defines representative order by vanishing positive
+lower-endpoint defect. It is invariant under vanishing-separation equivalence
+and yields a `PartialOrder` on `DkNNRealQ`.
+
+Remaining order work is operation monotonicity and the question of totality.
+No `LinearOrder` is claimed yet.
 
 ### Semantic Bridge
 
diff --git a/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md b/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
index cfd3aa68..adc207de 100644
--- a/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
+++ b/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
@@ -314,11 +314,13 @@ addition, multiplication, powers, and semiring lemmas are therefore available
 through Lean's algebraic hierarchy.
 
 This completes the first algebraic public surface of the nonnegative
-computable-real quotient. Order remains separate: an eventually ordered
-representative relation must be shown compatible with `Equiv`, or derived from
-a later semantic bridge. Likewise, any map to Mathlib's `NNReal` or `Real`
-should remain in a separate bridge module because selecting the represented
-limit may require `noncomputable`.
+computable-real quotient. The next phase defines asymptotic order by requiring
+the positive lower-endpoint defect to tend to zero. This relation is compatible
+with `Equiv` and gives `DkNNRealQ` a `PartialOrder`. Ordered-semiring instances
+remain deferred until operation monotonicity has been proved.
+
+Any map to Mathlib's `NNReal` or `Real` should remain in a separate bridge
+module because selecting the represented limit may require `noncomputable`.
 
 Persistent intersection and equality after a future evaluation into Mathlib's
 `Real` remain comparison principles. Their equivalence with vanishing
````
`````
