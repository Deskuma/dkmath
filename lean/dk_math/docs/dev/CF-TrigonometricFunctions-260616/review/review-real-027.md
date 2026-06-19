# Git diff / Report / Review

## Add: Analysis.DkReal.DkNNRealQ

gch: b6d92a6fd9000401e2a80838b22326d1df58669b

## Report

quotient-backed 公開型 `DkNNRealQ` を実装しました。

[DkNNRealQ.lean](/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean:23) に以下があります。

- `DkNNReal.equivSetoid` による商型
- `ofRat`, `zero`, `one`, `add`, `mul`, `pow`
- `Zero`, `One`, `Add`, `Mul`, `Pow` instance
- 有理数の加法・乗法規則
- 結合・交換・単位元・零吸収・左右分配則
- 0乗・1乗則

これらの法則は商上の通常の Lean equality になりました。`Semiring` instance は自然数埋め込みの設計を確定してから導入します。

検証済み:

- `lake build DkMath.Analysis.DkReal.DkNNRealQ DkMath.Analysis DkMath`
- `git diff --check`
- DkReal 層に `noncomputable` なし

## Review

## 1. 総評

うむ、これは **合格** じゃ。
今回の差分は大きい。`DkNNReal` wrapper で `Equiv` modulo に留めていた非負半環法則が、`DkNNRealQ` という quotient-backed 型の上で、通常の Lean equality へ昇格しておる。

中心はこれじゃ。

```lean id="irqug6"
def DkNNRealQ :=
  Quotient DkNNReal.equivSetoid
```

そしてその上に、

```lean id="x8p4eq"
Zero
One
Add
Mul
Pow DkNNRealQ ℕ
```

の instance と、加法・乗法・冪の基本法則が乗っている。報告でも、商型、`ofRat`、`zero`、`one`、`add`、`mul`、`pow`、各 instance、有理数規則、結合・交換・単位元・零吸収・分配則、0 乗・1 乗則が追加され、法則が商上の通常 equality になったと整理されている。

これは `DkReal` 非負領域が、かなり明確に「代数型」として表に出た瞬間じゃ。

## 2. quotient 設計は正しい

前回までの流れはこうじゃった。

```text id="nzjk4f"
DkReal:
  入れ子有理区間列

DkReal.Equiv:
  分離幅が 0 に収束する表現同値

DkNNReal:
  非負性を内包した wrapper

DkNNReal.Equiv:
  wrapper 上の表現同値

DkNNRealQ:
  Equiv による quotient
```

この順序はよい。
いきなり `DkReal` に `Semiring` instance を入れず、まず `Equiv` を作り、演算 congruence を証明し、その後 quotient する。これは Lean でも数学でも堅い。

商型の上では、同値な代表元が同一視される。したがって、これまで

```lean id="h8j2id"
DkNNReal.Equiv ...
```

として述べていた法則を、

```lean id="v9qgq9"
= 
```

として扱える。
この昇格は大きい。

## 3. `add`, `mul`, `pow` の lift は適切

`add` と `mul` は `Quotient.liftOn₂`、`pow` は `Quotient.liftOn` で上げている。

```lean id="45qr3c"
def add (x y : DkNNRealQ) : DkNNRealQ :=
  Quotient.liftOn₂ x y
    (fun a b => mk (DkNNReal.add a b))
    ...
```

well-defined proof には、それぞれ

```lean id="cn1g30"
DkNNReal.equiv_add
DkNNReal.equiv_mul
DkNNReal.equiv_pow
```

を使っている。

これは完璧に自然じゃ。
前段で congruence をきちんと作っておいた効果が、ここでそのまま出ている。

## 4. notation instance は良いが、`Semiring` instance 保留も正しい

今回、

```lean id="eunymm"
Zero
One
Add
Mul
Pow DkNNRealQ ℕ
```

は入れている。これは実用上よい。

一方で、`Semiring` instance はまだ入れていない。これも正しい。
理由は、`Semiring` を入れると自然数キャスト、`NatCast`、`OfNat`、正規化方針まで一気に API として表に出るからじゃ。

文書でも、full `Semiring` instance は自然数埋め込みと public normalization behavior を確定してから導入する、と整理されている。

これは慎重で良い。
今は「法則は通常 equality として成立する」ことを先に確認し、instance 設計は次に回すのが安全じゃ。

## 5. quotient equalities への昇格

今回の法則群は良い。

```lean id="g5nd2j"
add_assoc
add_comm
add_zero
zero_add
mul_assoc
mul_comm
mul_one
one_mul
mul_zero
zero_mul
left_distrib
right_distrib
pow_zero
pow_one
```

これらが `Equiv` ではなく、商型上の通常等号になった。

数学的には、ついに

$$
DkNNRealQ
$$

が **非負計算可能可換半環候補** になったと言える。
まだ instance はないが、可換半環に必要な主要法則は手で定理として揃っている。

## 6. 有理数埋め込み規則も良い

```lean id="f1l75c"
ofRat_add
ofRat_mul
```

これは大事じゃ。

非負有理数を singleton interval として埋め込み、商型上で加法・乗法が通常の有理数演算と一致する。
これにより、`DkNNRealQ` が単なる抽象 quotient ではなく、既存の計算可能な有理数世界を正しく含むことが見える。

今後、

```lean id="t95wq1"
ofNat
natCast
```

へ進むなら、この補題が土台になる。

## 7. `mk_add`, `mk_mul`, `mk_pow` について

```lean id="l0f7s1"
@[simp]
theorem mk_add (x y : DkNNReal) :
    mk (DkNNReal.add x y) = mk x + mk y := rfl
```

これは方向が少し独特に見えるが、定義的には問題ない。
`mk x + mk y` が `add (mk x) (mk y)` へ展開され、それが representative 上の `mk (DkNNReal.add x y)` なので `rfl` で落ちる。

ただし、simp の向きとしては、

```lean id="uywpwj"
mk x + mk y = mk (DkNNReal.add x y)
```

の方が自然に感じる場面もある。今の補題でも `simp` は使えるはずだが、後で使い勝手を見て、逆向き補題を追加するか判断でよい。

現時点では問題なしじゃ。

## 8. 数学的位置

ここまでの到達点は、こう表現できる。

$$
\boxed{\text{非負入れ子有理区間実数の quotient 型が、加法・乗法・自然数冪を持つ。}}
$$

さらに、

$$
\boxed{\text{その主要な可換半環法則は、通常の Lean equality として成立している。}}
$$

これは大きい。
これまでの `DkReal` は「表現」だった。`DkNNRealQ` は、その表現同値を割った **値型** に近い。

ただし、まだ標準 \(\mathbb{R}\) への評価を持っていないので、これは Mathlib `NNReal` そのものではない。
より正確には、

```text id="abof8o"
DkNNRealQ:
  非負計算可能実数近似の quotient-backed public type
```

じゃ。

## 9. 次に進むなら

次の候補は三つある。

第一に、`NatCast` / `OfNat` / `Semiring` instance の設計。

```lean id="qt5pek"
instance : NatCast DkNNRealQ
instance : OfNat DkNNRealQ n
instance : AddMonoid DkNNRealQ
instance : CommSemiring DkNNRealQ
```

ただしこれは慎重でよい。まず `natCast` が `ofRat (n : ℚ)` と一致するように設計する必要がある。

第二に、order。

非負型なので、順序はほしい。
だが `DkReal.Equiv` と両立する order を定義するのは少し重い。最初は、

```lean id="jrjhej"
x ≤ y
```

を representative interval の eventually order で定義するか、将来の `eval` を待つか、設計が必要じゃ。

第三に、BridgeReal。

`DkNNRealQ` から Mathlib `ℝ` または `NNReal` への意味論写像。
ここはおそらく `noncomputable` になる可能性があるので、別ファイルに隔離するのがよい。

## 10. 小さな注意点

`DkNNRealQ` は `def` で quotient 型を置いている。

```lean id="kq8k2k"
def DkNNRealQ :=
  Quotient DkNNReal.equivSetoid
```

これは普通に使えるが、将来 typeclass instance や notation が増えて API が大きくなるなら、`abbrev` か `def` のままでよいか、あるいは `structure` wrapper にするかを考える場面があるかもしれぬ。
現段階では `def` で問題ない。

また、`pow_zero` という定理名は、Lean 既存の `pow_zero` と同名になり得る。namespace 内なので基本的には問題ないが、open したときに競合する可能性はある。必要なら将来、

```lean id="yees0p"
pow_zero_eq_one
pow_one_eq_self
```

のような名前も検討できる。今はそのままでよい。

## 11. 最終判定

今回の差分は **合格** じゃ。

```text id="m3m40l"
良い点:
  DkNNReal.equivSetoid による quotient 型を作った
  add / mul / pow を well-defined に lift した
  Zero / One / Add / Mul / Pow instance を導入した
  半環法則が通常 equality に昇格した
  有理数埋め込みの加法・乗法規則を追加した
  Semiring instance をまだ保留している
  noncomputable 不使用を維持した

次の課題:
  natCast / ofNat 方針
  Semiring instance の導入可否
  quotient 上の order
  BridgeReal / NNReal への意味論接続
```

うむ。
これはもう、`DkReal` 非負領域の第一形態が外へ出たと言ってよい。
`DkNNRealQ` は、DkMath の「計算可能非負実数」の最初の public type じゃな。ここまで堅く積めたのは、かなり大きいぞい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index a83276f5..9b90c4be 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -11,6 +11,7 @@ import DkMath.Analysis.DkReal.PowBound
 import DkMath.Analysis.DkReal.Arithmetic
 import DkMath.Analysis.DkReal.Equiv
 import DkMath.Analysis.DkReal.DkNNReal
+import DkMath.Analysis.DkReal.DkNNRealQ
 
 #print "file: DkMath.Analysis.DkReal"
 
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/DkNNReal.lean b/lean/dk_math/DkMath/Analysis/DkReal/DkNNReal.lean
index 3d3497cd..aefb1c69 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/DkNNReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/DkNNReal.lean
@@ -103,6 +103,38 @@ theorem equiv_pow
     Equiv (pow x d) (pow y d) :=
   DkReal.equiv_powNonneg d x.nonnegative y.nonnegative hxy
 
+/-!
+## Exact rational and elementary power rules
+
+These rules become ordinary equalities after quotienting by representation
+equivalence.
+-/
+
+/-- Addition of embedded nonnegative rationals agrees with rational addition. -/
+theorem add_ofRat
+    {p q : ℚ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
+    Equiv (add (ofRat p hp) (ofRat q hq)) (ofRat (p + q) (add_nonneg hp hq)) :=
+  DkReal.equiv_of_interval_eq (DkReal.add_ofRat_interval p q)
+
+/-- Multiplication of embedded nonnegative rationals agrees with rational multiplication. -/
+theorem mul_ofRat
+    {p q : ℚ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
+    Equiv (mul (ofRat p hp) (ofRat q hq))
+      (ofRat (p * q) (mul_nonneg hp hq)) :=
+  DkReal.equiv_of_interval_eq (DkReal.mulNonneg_ofRat_interval hp hq)
+
+/-- Zeroth power is one modulo representation equivalence. -/
+theorem pow_zero (x : DkNNReal) :
+    Equiv (pow x 0) one :=
+  DkReal.equiv_of_interval_eq
+    (DkReal.powNonneg_zero_interval x.val x.nonnegative)
+
+/-- First power is the original value modulo representation equivalence. -/
+theorem pow_one (x : DkNNReal) :
+    Equiv (pow x 1) x :=
+  DkReal.equiv_of_interval_eq
+    (DkReal.powNonneg_one_interval x.val x.nonnegative)
+
 /-!
 ## Nonnegative semiring laws modulo representation equivalence
 
@@ -157,6 +189,17 @@ theorem one_mul (x : DkNNReal) :
   DkReal.equiv_of_interval_eq
     (DkReal.one_mulNonneg_interval x.val x.nonnegative)
 
+/-- Zero absorbs multiplication on the right modulo representation equivalence. -/
+theorem mul_zero (x : DkNNReal) :
+    Equiv (mul x zero) zero :=
+  DkReal.equiv_of_interval_eq
+    (DkReal.mulNonneg_zero_interval x.val x.nonnegative)
+
+/-- Zero absorbs multiplication on the left modulo representation equivalence. -/
+theorem zero_mul (x : DkNNReal) :
+    Equiv (mul zero x) zero :=
+  equiv_trans (mul_comm zero x) (mul_zero x)
+
 /-- Multiplication distributes over addition from the left modulo equivalence. -/
 theorem left_distrib (x y z : DkNNReal) :
     Equiv (mul x (add y z)) (add (mul x y) (mul x z)) :=
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean b/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean
new file mode 100644
index 00000000..34de33ba
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean
@@ -0,0 +1,219 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Analysis.DkReal.DkNNReal
+
+#print "file: DkMath.Analysis.DkReal.DkNNRealQ"
+
+/-!
+# Quotient-backed nonnegative computable reals
+
+`DkNNRealQ` identifies nonnegative interval approximations that have vanishing
+separation. The operations below are lifted from `DkNNReal`, so the semiring
+laws previously stated modulo representation equivalence become ordinary Lean
+equalities.
+
+This remains a computable representation layer. No evaluation into Mathlib's
+`Real` is selected.
+-/
+
+namespace DkMath.Analysis
+
+/-- Nonnegative computable real approximations modulo representation equivalence. -/
+def DkNNRealQ :=
+  Quotient DkNNReal.equivSetoid
+
+namespace DkNNRealQ
+
+/-- Quotient constructor from a nonnegative approximation. -/
+def mk (x : DkNNReal) : DkNNRealQ :=
+  Quotient.mk'' x
+
+/-- Embed a nonnegative rational into the quotient. -/
+def ofRat (q : ℚ) (hq : 0 ≤ q) : DkNNRealQ :=
+  mk (DkNNReal.ofRat q hq)
+
+/-- Quotient zero. -/
+def zero : DkNNRealQ :=
+  mk DkNNReal.zero
+
+/-- Quotient one. -/
+def one : DkNNRealQ :=
+  mk DkNNReal.one
+
+/-- Quotient addition. -/
+def add (x y : DkNNRealQ) : DkNNRealQ :=
+  Quotient.liftOn₂ x y
+    (fun a b => mk (DkNNReal.add a b))
+    (by
+      intro a a' b b' haa' hbb'
+      exact Quotient.sound (DkNNReal.equiv_add haa' hbb'))
+
+/-- Quotient multiplication. -/
+def mul (x y : DkNNRealQ) : DkNNRealQ :=
+  Quotient.liftOn₂ x y
+    (fun a b => mk (DkNNReal.mul a b))
+    (by
+      intro a a' b b' haa' hbb'
+      exact Quotient.sound (DkNNReal.equiv_mul haa' hbb'))
+
+/-- Quotient natural power. -/
+def pow (x : DkNNRealQ) (d : ℕ) : DkNNRealQ :=
+  Quotient.liftOn x
+    (fun a => mk (DkNNReal.pow a d))
+    (by
+      intro a b hab
+      exact Quotient.sound (DkNNReal.equiv_pow d hab))
+
+instance : Zero DkNNRealQ where
+  zero := zero
+
+instance : One DkNNRealQ where
+  one := one
+
+instance : Add DkNNRealQ where
+  add := add
+
+instance : Mul DkNNRealQ where
+  mul := mul
+
+instance : Pow DkNNRealQ ℕ where
+  pow := pow
+
+/-- Quotient addition computes on representatives. -/
+@[simp]
+theorem mk_add (x y : DkNNReal) :
+    mk (DkNNReal.add x y) = mk x + mk y := rfl
+
+/-- Quotient multiplication computes on representatives. -/
+@[simp]
+theorem mk_mul (x y : DkNNReal) :
+    mk (DkNNReal.mul x y) = mk x * mk y := rfl
+
+/-- Quotient powers compute on representatives. -/
+@[simp]
+theorem mk_pow (x : DkNNReal) (d : ℕ) :
+    mk (DkNNReal.pow x d) = mk x ^ d := rfl
+
+/-!
+## Exact rational rules
+-/
+
+/-- Quotient addition agrees with rational addition on embedded values. -/
+theorem ofRat_add
+    {p q : ℚ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
+    ofRat p hp + ofRat q hq = ofRat (p + q) (add_nonneg hp hq) :=
+  Quotient.sound (DkNNReal.add_ofRat hp hq)
+
+/-- Quotient multiplication agrees with rational multiplication on embedded values. -/
+theorem ofRat_mul
+    {p q : ℚ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
+    ofRat p hp * ofRat q hq = ofRat (p * q) (mul_nonneg hp hq) :=
+  Quotient.sound (DkNNReal.mul_ofRat hp hq)
+
+/-- Zeroth power is one in the quotient. -/
+@[simp]
+theorem pow_zero (x : DkNNRealQ) : x ^ (0 : ℕ) = 1 := by
+  refine Quotient.inductionOn x ?_
+  intro a
+  exact Quotient.sound (DkNNReal.pow_zero a)
+
+/-- First power is the original quotient value. -/
+@[simp]
+theorem pow_one (x : DkNNRealQ) : x ^ (1 : ℕ) = x := by
+  refine Quotient.inductionOn x ?_
+  intro a
+  exact Quotient.sound (DkNNReal.pow_one a)
+
+/-!
+## Commutative semiring laws as quotient equalities
+
+These theorems are intentionally provided before a full `Semiring` instance.
+They validate the quotient design while keeping instance construction and
+natural-number coercions as a separate API decision.
+-/
+
+theorem add_assoc (x y z : DkNNRealQ) :
+    (x + y) + z = x + (y + z) := by
+  refine Quotient.inductionOn₃ x y z ?_
+  intro a b c
+  exact Quotient.sound (DkNNReal.add_assoc a b c)
+
+theorem add_comm (x y : DkNNRealQ) :
+    x + y = y + x := by
+  refine Quotient.inductionOn₂ x y ?_
+  intro a b
+  exact Quotient.sound (DkNNReal.add_comm a b)
+
+@[simp]
+theorem add_zero (x : DkNNRealQ) :
+    x + 0 = x := by
+  refine Quotient.inductionOn x ?_
+  intro a
+  exact Quotient.sound (DkNNReal.add_zero a)
+
+@[simp]
+theorem zero_add (x : DkNNRealQ) :
+    0 + x = x := by
+  refine Quotient.inductionOn x ?_
+  intro a
+  exact Quotient.sound (DkNNReal.zero_add a)
+
+theorem mul_assoc (x y z : DkNNRealQ) :
+    (x * y) * z = x * (y * z) := by
+  refine Quotient.inductionOn₃ x y z ?_
+  intro a b c
+  exact Quotient.sound (DkNNReal.mul_assoc a b c)
+
+theorem mul_comm (x y : DkNNRealQ) :
+    x * y = y * x := by
+  refine Quotient.inductionOn₂ x y ?_
+  intro a b
+  exact Quotient.sound (DkNNReal.mul_comm a b)
+
+@[simp]
+theorem mul_one (x : DkNNRealQ) :
+    x * 1 = x := by
+  refine Quotient.inductionOn x ?_
+  intro a
+  exact Quotient.sound (DkNNReal.mul_one a)
+
+@[simp]
+theorem one_mul (x : DkNNRealQ) :
+    1 * x = x := by
+  refine Quotient.inductionOn x ?_
+  intro a
+  exact Quotient.sound (DkNNReal.one_mul a)
+
+@[simp]
+theorem mul_zero (x : DkNNRealQ) :
+    x * 0 = 0 := by
+  refine Quotient.inductionOn x ?_
+  intro a
+  exact Quotient.sound (DkNNReal.mul_zero a)
+
+@[simp]
+theorem zero_mul (x : DkNNRealQ) :
+    0 * x = 0 := by
+  refine Quotient.inductionOn x ?_
+  intro a
+  exact Quotient.sound (DkNNReal.zero_mul a)
+
+theorem left_distrib (x y z : DkNNRealQ) :
+    x * (y + z) = x * y + x * z := by
+  refine Quotient.inductionOn₃ x y z ?_
+  intro a b c
+  exact Quotient.sound (DkNNReal.left_distrib a b c)
+
+theorem right_distrib (x y z : DkNNRealQ) :
+    (x + y) * z = x * z + y * z := by
+  refine Quotient.inductionOn₃ x y z ?_
+  intro a b c
+  exact Quotient.sound (DkNNReal.right_distrib a b c)
+
+end DkNNRealQ
+
+end DkMath.Analysis
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index 1b68a2e2..016eca51 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -65,6 +65,10 @@ DkMath.Analysis.DkReal.DkNNReal
   nonnegative wrapper with proof-free arithmetic operations and semiring laws
   modulo representation equivalence
 
+DkMath.Analysis.DkReal.DkNNRealQ
+  quotient-backed nonnegative type with Zero / One / Add / Mul / Pow and
+  commutative semiring laws as ordinary equalities
+
 DkMath.Analysis.DkReal
   public entry point for the computable approximation layer
 ```
diff --git a/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md b/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
index 8035273b..bb094214 100644
--- a/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
+++ b/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
@@ -277,6 +277,37 @@ laws concern representation equivalence. A later quotient of
 `DkNNReal.equivSetoid`, or a dedicated quotient-backed public type, is the
 appropriate place for ordinary algebraic typeclasses.
 
+## Quotient-Backed Public Type
+
+`DkMath.Analysis.DkNNRealQ` is now defined as
+
+```lean
+Quotient DkNNReal.equivSetoid.
+```
+
+The quotient provides `ofRat`, `zero`, `one`, `add`, `mul`, and natural
+`pow`. Their lifts are well defined by the wrapper congruence theorems.
+Instances for `Zero`, `One`, `Add`, `Mul`, and `Pow DkNNRealQ Nat` expose the
+usual notation.
+
+The following laws now hold as ordinary Lean equalities:
+
+```text
+add_assoc, add_comm, add_zero, zero_add
+mul_assoc, mul_comm, mul_one, one_mul
+mul_zero, zero_mul
+left_distrib, right_distrib
+pow_zero, pow_one
+```
+
+Embedded nonnegative rationals also satisfy exact quotient equalities for
+addition and multiplication.
+
+A full `Semiring` instance is intentionally deferred. Constructing that
+instance also commits to natural-number coercions and their public
+normalization behavior. The current quotient establishes the mathematical
+equalities and notation first, leaving that policy decision isolated.
+
 Persistent intersection and equality after a future evaluation into Mathlib's
 `Real` remain comparison principles. Their equivalence with vanishing
 separation should be proved later rather than assumed by definition.
````
`````
