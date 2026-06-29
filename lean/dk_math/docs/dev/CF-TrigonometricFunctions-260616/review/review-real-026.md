# Git diff / Report / Review

## Add: Analysis.DkReal.DkNNReal

gch: 553a303884accce0679b0a12ed095de584c08602

## Report

レビュー推奨の `DkNNReal` wrapper を実装しました。

[DkNNReal.lean](/lean/dk_math/DkMath/Analysis/DkReal/DkNNReal.lean:21) に以下を追加しています。

- 非負性を内包する `DkNNReal`
- `ofRat`, `zero`, `one`
- 証明引数不要の `add`, `mul`, `pow`
- wrapper 上の `Equiv` と `Setoid`
- 各演算の congruence
- 結合・交換・単位元・左右分配則

法則は raw equality ではなく `Equiv` で提示しています。そのため、現段階では `Semiring` や演算記号の instance を導入していません。

検証済み:

- `lake build DkMath.Analysis.DkReal.DkNNReal DkMath.Analysis DkMath`
- `git diff --check`
- DkReal 層に `noncomputable` なし

次候補は `DkNNReal.equivSetoid` の quotient を使った、通常の等号を持つ非負半環型です。

## Review

## 1. 総評

うむ、これは **合格** じゃ。
今回の差分は、かなり良い API 整理になっておる。前回まで `DkReal.mulNonneg` や `DkReal.powNonneg` は、毎回 `Nonnegative` 証明を引数として持ち回る形だった。今回の `DkNNReal` wrapper によって、その証明が型の中へ格納され、利用者側の演算 API がかなり自然になった。

中心はこれじゃ。

```lean id="orybbj"
structure DkNNReal where
  val : DkReal
  nonnegative : DkReal.Nonnegative val
```

これにより、非負領域の演算が、

```lean id="a86sit"
DkNNReal.add
DkNNReal.mul
DkNNReal.pow
```

として、証明引数を表に出さず使えるようになった。報告でも、`DkNNReal` wrapper、`ofRat`、`zero`、`one`、proof-free arithmetic operations、wrapper 上の `Equiv` と `Setoid`、各演算の congruence、半環法則 modulo equivalence が追加されたと整理されている。

これは、次に quotient 型へ進む前の、非常に自然な足場じゃ。

## 2. `DkNNReal` wrapper の意味

数学的には、今回作った `DkNNReal` は

$$
DkReal_{\ge0}
$$

の表現型じゃ。

つまり、ただの `DkReal` ではなく、

```text id="w3zqmn"
値本体:
  val : DkReal

非負性証明:
  nonnegative : DkReal.Nonnegative val
```

を一緒に持つ。

これにより、非負領域でしか安全に定義していない乗法や冪写像を、証明引数なしで扱える。

```lean id="3q6j4x"
def mul (x y : DkNNReal) : DkNNReal
def pow (x : DkNNReal) (d : ℕ) : DkNNReal
```

これは非常に良い。
`DkReal` の一般符号乗法をまだ実装していない現在、非負領域を明示的に wrapper 化するのは、型設計として堅い。

## 3. `ofRat`, `zero`, `one` は自然

```lean id="sunmld"
def ofRat (q : ℚ) (hq : 0 ≤ q) : DkNNReal
def zero : DkNNReal
def one : DkNNReal
```

ここもよい。

ただし、将来的には名前の衝突を考えると、`ofRat` はそのままでよいが、`zero` / `one` を typeclass instance にするのは quotient 後でよい。
現段階では raw wrapper equality ではなく `Equiv` で法則が立っているので、`Zero` / `One` instance を急がない判断は正しい。

## 4. wrapper 上の `Equiv` と `Setoid`

```lean id="gz5lwq"
def Equiv (x y : DkNNReal) : Prop :=
  DkReal.Equiv x.val y.val
```

これは自然じゃ。
`DkNNReal` の表現同値は、中身の `DkReal` 表現同値に委譲する。

```lean id="v2z3hj"
def equivSetoid : Setoid DkNNReal
```

もそのまま `DkReal` 側の反射・対称・推移を使って閉じている。
これで、次の quotient に必要な土台はもうできている。

## 5. 演算 congruence はよく整理されている

今回の `DkNNReal` wrapper は、既存の congruence を綺麗に持ち上げている。

```lean id="yyouas"
equiv_add
equiv_mul
equiv_pow
```

これは良い。

中身では、

```text id="m6zg3d"
DkReal.equiv_add
DkReal.equiv_mulNonneg
DkReal.equiv_powNonneg
```

をそのまま使っている。
つまり、wrapper 側で再証明していない。これは Lean API として正しい。

今回までに `DkReal` 側で積み上げた同値保存定理が、ここで表面 API へ昇格したわけじゃな。

## 6. 半環法則 modulo `Equiv`

今回追加された法則群は、`DkNNReal` の非負半環構造に必要なものじゃ。

```lean id="dox4c7"
add_assoc
add_comm
add_zero
zero_add
mul_assoc
mul_comm
mul_one
one_mul
left_distrib
right_distrib
```

ただし、すべて raw equality ではなく、

```lean id="pz777y"
Equiv ...
```

で述べている。これが大事じゃ。

`DkNNReal` は wrapper であって quotient ではない。
したがって、同じ実数値を表す二つの近似列が raw Lean equality で一致するとは限らない。
ここで `Semiring` instance を入れず、法則を `Equiv` で提示しているのは正しい。

文書にも、raw wrapper に `Add`、`Mul`、`Pow`、`Semiring` instance を導入しない理由が明記されている。`Equiv` による法則を持つ段階であり、通常の algebraic typeclass は将来の quotient 型で導入すべきだ、という整理も正しい。

## 7. 数学的到達点

ここまでで、到達点はこうじゃ。

$$
\boxed{\text{非負 }DkReal\text{ 表現の Setoid 付き半環前構造}}
$$

より実装寄りには、

```text id="vrdj35"
DkNNReal:
  非負性を内包する wrapper

Equiv:
  中身の DkReal.Equiv

演算:
  add / mul / pow

法則:
  Equiv modulo で半環法則が成立

まだ:
  quotient 上の通常等号つき Semiring ではない
```

つまり、`DkNNReal` は quotient 前の **setoid algebra surface** じゃ。
これはかなり良いキャンプ地じゃな。

## 8. 次に quotient へ行く場合

次に作るなら、たとえばこうじゃ。

```lean id="i7ba2c"
def DkNNRealQ := Quotient DkNNReal.equivSetoid
```

または名前を考えて、

```lean id="d09jjj"
def NNComputableReal := Quotient DkNNReal.equivSetoid
```

のような public type を作る。

その上で、

```lean id="p7tagx"
Zero
One
Add
Mul
Pow
```

を定義する。

ただし `Pow` は指数が自然数なので、Lean の通常 instance にする場合は形を慎重に見る必要がある。
まずは quotient 上の関数として、

```lean id="rfflyh"
def addQ
def mulQ
def powQ
```

で始める方が安全じゃ。

## 9. quotient 前に足すとよい補題

quotient に入る前に、次の interval / wrapper simp があると楽になるかもしれぬ。

```lean id="jxi4ux"
ofRat_add
ofRat_mul
pow_zero
pow_one
```

ただし、これも raw equality ではなく `Equiv` で。

例えば、

```lean id="hqh3ki"
theorem add_ofRat
    {p q : ℚ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    Equiv (add (ofRat p hp) (ofRat q hq)) (ofRat (p + q) ...)
```

や、

```lean id="ftcug6"
theorem mul_ofRat
```

があると、quotient 上で `norm_num` 的に使いやすくなる。

もっとも、すでに `DkReal` 側に interval-level の `ofRat` 補題があるので、すぐ作れるはずじゃ。

## 10. 注意点

一点だけ、命名として `DkNNReal` は良いが、namespace が `DkMath.Analysis.DkNNReal` になっている点は確認しておきたい。

ファイルは、

```text id="j91ww7"
DkMath/Analysis/DkReal/DkNNReal.lean
```

だが、namespace は、

```lean id="52cn2v"
namespace DkMath.Analysis
```

の下で `structure DkNNReal` を定義している。
これは意図があるなら良い。`DkNNReal` を `DkReal` の内部ではなく、公開上は `DkMath.Analysis.DkNNReal` として扱いたい、という設計じゃな。

もし内部構造として、

```lean id="q0z7jl"
DkMath.Analysis.DkReal.DkNNReal
```

にしたいなら namespace を変える必要がある。
わっちの感覚では、公開型としては `DkMath.Analysis.DkNNReal` の方がすっきりしておる。だから今のままでよいと思う。

## 11. 最終判定

今回の差分は **合格** じゃ。

```text id="tnzz6e"
良い点:
  非負性を wrapper に内包した
  proof-free add / mul / pow を提供した
  wrapper Equiv / Setoid を定義した
  add / mul / pow の congruence を持ち上げた
  半環法則を Equiv modulo で整備した
  raw equality / Semiring instance をまだ導入していない
  noncomputable 不使用を維持した

次の本丸:
  quotient-backed public type
  quotient 上の Zero / One / Add / Mul
  quotient 上の semiring 法則
  ofRat の quotient API
```

うむ。
これで `DkReal` 非負領域は、かなり明確に **quotient 直前の非負計算可能半環表現** になった。
次に quotient を切れば、これまで `Equiv` で述べていた法則が、通常の Lean equality 上の法則として使えるようになる。ここまでの積み上げはかなり堅いぞい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index c52886d6..a83276f5 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -10,6 +10,7 @@ import DkMath.Analysis.DkReal.Pow
 import DkMath.Analysis.DkReal.PowBound
 import DkMath.Analysis.DkReal.Arithmetic
 import DkMath.Analysis.DkReal.Equiv
+import DkMath.Analysis.DkReal.DkNNReal
 
 #print "file: DkMath.Analysis.DkReal"
 
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/DkNNReal.lean b/lean/dk_math/DkMath/Analysis/DkReal/DkNNReal.lean
new file mode 100644
index 00000000..3d3497cd
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/DkReal/DkNNReal.lean
@@ -0,0 +1,176 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Analysis.DkReal.Equiv
+
+#print "file: DkMath.Analysis.DkReal.DkNNReal"
+
+/-!
+# Nonnegative DkReal wrapper
+
+`DkNNReal` packages a `DkReal` approximation together with stagewise
+nonnegativity. It removes proof arguments from the public nonnegative
+arithmetic operations while retaining the computable interval representation.
+
+Algebraic laws are stated using representation equivalence, not raw structure
+equality. A quotient can be introduced later once its public API is justified.
+-/
+
+namespace DkMath.Analysis
+
+/-- A nonnegative computable real approximation. -/
+structure DkNNReal where
+  val : DkReal
+  nonnegative : DkReal.Nonnegative val
+
+namespace DkNNReal
+
+/-- Embed a nonnegative rational as a constant singleton approximation. -/
+def ofRat (q : ℚ) (hq : 0 ≤ q) : DkNNReal :=
+  ⟨DkReal.ofRat q, DkReal.nonnegative_ofRat hq⟩
+
+/-- The nonnegative zero approximation. -/
+def zero : DkNNReal :=
+  ofRat 0 le_rfl
+
+/-- The nonnegative one approximation. -/
+def one : DkNNReal :=
+  ofRat 1 zero_le_one
+
+/-- Addition of nonnegative approximations. -/
+def add (x y : DkNNReal) : DkNNReal :=
+  ⟨DkReal.add x.val y.val, DkReal.nonnegative_add x.nonnegative y.nonnegative⟩
+
+/-- Multiplication of nonnegative approximations. -/
+def mul (x y : DkNNReal) : DkNNReal :=
+  ⟨DkReal.mulNonneg x.val y.val x.nonnegative y.nonnegative,
+    DkReal.nonnegative_mulNonneg x.nonnegative y.nonnegative⟩
+
+/-- Natural power of a nonnegative approximation. -/
+def pow (x : DkNNReal) (d : ℕ) : DkNNReal :=
+  ⟨DkReal.powNonneg d x.val x.nonnegative,
+    DkReal.nonnegative_powNonneg d x.nonnegative⟩
+
+/-- Wrapper equivalence induced by `DkReal.Equiv`. -/
+def Equiv (x y : DkNNReal) : Prop :=
+  DkReal.Equiv x.val y.val
+
+/-- Wrapper equivalence is reflexive. -/
+theorem equiv_refl (x : DkNNReal) : Equiv x x :=
+  DkReal.equiv_refl x.val
+
+/-- Wrapper equivalence is symmetric. -/
+theorem equiv_symm {x y : DkNNReal} (hxy : Equiv x y) : Equiv y x :=
+  DkReal.equiv_symm hxy
+
+/-- Wrapper equivalence is transitive. -/
+theorem equiv_trans
+    {x y z : DkNNReal} (hxy : Equiv x y) (hyz : Equiv y z) :
+    Equiv x z :=
+  DkReal.equiv_trans hxy hyz
+
+/-- Setoid of nonnegative approximation representations. -/
+def equivSetoid : Setoid DkNNReal where
+  r := Equiv
+  iseqv := ⟨equiv_refl, @equiv_symm, @equiv_trans⟩
+
+/-!
+## Arithmetic congruence
+
+The wrapper operations respect representation equivalence because their
+underlying `DkReal` operations do.
+-/
+
+/-- Addition respects wrapper equivalence. -/
+theorem equiv_add
+    {x x' y y' : DkNNReal} (hxx' : Equiv x x') (hyy' : Equiv y y') :
+    Equiv (add x y) (add x' y') :=
+  DkReal.equiv_add hxx' hyy'
+
+/-- Multiplication respects wrapper equivalence. -/
+theorem equiv_mul
+    {x x' y y' : DkNNReal} (hxx' : Equiv x x') (hyy' : Equiv y y') :
+    Equiv (mul x y) (mul x' y') :=
+  DkReal.equiv_mulNonneg
+    x.nonnegative x'.nonnegative y.nonnegative y'.nonnegative hxx' hyy'
+
+/-- Natural powers respect wrapper equivalence. -/
+theorem equiv_pow
+    (d : ℕ) {x y : DkNNReal} (hxy : Equiv x y) :
+    Equiv (pow x d) (pow y d) :=
+  DkReal.equiv_powNonneg d x.nonnegative y.nonnegative hxy
+
+/-!
+## Nonnegative semiring laws modulo representation equivalence
+
+These are the algebraic laws needed by a future quotient. They intentionally
+use `Equiv`; raw equality would distinguish different interval sequences
+representing the same value.
+-/
+
+/-- Addition is associative modulo representation equivalence. -/
+theorem add_assoc (x y z : DkNNReal) :
+    Equiv (add (add x y) z) (add x (add y z)) :=
+  DkReal.equiv_of_interval_eq (DkReal.add_assoc_interval x.val y.val z.val)
+
+/-- Addition is commutative modulo representation equivalence. -/
+theorem add_comm (x y : DkNNReal) :
+    Equiv (add x y) (add y x) :=
+  DkReal.equiv_of_interval_eq (DkReal.add_comm_interval x.val y.val)
+
+/-- Zero is a right additive identity modulo representation equivalence. -/
+theorem add_zero (x : DkNNReal) :
+    Equiv (add x zero) x :=
+  DkReal.equiv_of_interval_eq (DkReal.add_zero_interval x.val)
+
+/-- Zero is a left additive identity modulo representation equivalence. -/
+theorem zero_add (x : DkNNReal) :
+    Equiv (add zero x) x :=
+  DkReal.equiv_of_interval_eq (DkReal.zero_add_interval x.val)
+
+/-- Multiplication is associative modulo representation equivalence. -/
+theorem mul_assoc (x y z : DkNNReal) :
+    Equiv (mul (mul x y) z) (mul x (mul y z)) :=
+  DkReal.equiv_of_interval_eq
+    (DkReal.mulNonneg_assoc_interval
+      x.val y.val z.val x.nonnegative y.nonnegative z.nonnegative)
+
+/-- Multiplication is commutative modulo representation equivalence. -/
+theorem mul_comm (x y : DkNNReal) :
+    Equiv (mul x y) (mul y x) :=
+  DkReal.equiv_of_interval_eq
+    (DkReal.mulNonneg_comm_interval
+      x.val y.val x.nonnegative y.nonnegative)
+
+/-- One is a right multiplicative identity modulo representation equivalence. -/
+theorem mul_one (x : DkNNReal) :
+    Equiv (mul x one) x :=
+  DkReal.equiv_of_interval_eq
+    (DkReal.mulNonneg_one_interval x.val x.nonnegative)
+
+/-- One is a left multiplicative identity modulo representation equivalence. -/
+theorem one_mul (x : DkNNReal) :
+    Equiv (mul one x) x :=
+  DkReal.equiv_of_interval_eq
+    (DkReal.one_mulNonneg_interval x.val x.nonnegative)
+
+/-- Multiplication distributes over addition from the left modulo equivalence. -/
+theorem left_distrib (x y z : DkNNReal) :
+    Equiv (mul x (add y z)) (add (mul x y) (mul x z)) :=
+  DkReal.equiv_of_interval_eq
+    (DkReal.left_distrib_interval
+      x.val y.val z.val x.nonnegative y.nonnegative z.nonnegative)
+
+/-- Multiplication distributes over addition from the right modulo equivalence. -/
+theorem right_distrib (x y z : DkNNReal) :
+    Equiv (mul (add x y) z) (add (mul x z) (mul y z)) :=
+  DkReal.equiv_of_interval_eq
+    (DkReal.right_distrib_interval
+      x.val y.val z.val x.nonnegative y.nonnegative z.nonnegative)
+
+end DkNNReal
+
+end DkMath.Analysis
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index 1d37acb2..1b68a2e2 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -61,6 +61,10 @@ DkMath.Analysis.DkReal.Equiv
   vanishing interval separation, representation setoid, endpoint convergence,
   and additive, nonnegative multiplicative, and natural-power congruence
 
+DkMath.Analysis.DkReal.DkNNReal
+  nonnegative wrapper with proof-free arithmetic operations and semiring laws
+  modulo representation equivalence
+
 DkMath.Analysis.DkReal
   public entry point for the computable approximation layer
 ```
diff --git a/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md b/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
index 1ac6af4d..8035273b 100644
--- a/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
+++ b/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
@@ -239,6 +239,44 @@ respect the representation setoid. The next design question is whether to
 introduce a quotient or a dedicated wrapper for the nonnegative computable
 semiring API.
 
+## DkNNReal Wrapper
+
+The first public nonnegative arithmetic surface is now the wrapper
+`DkMath.Analysis.DkNNReal`:
+
+```lean
+structure DkNNReal where
+  val : DkReal
+  nonnegative : DkReal.Nonnegative val
+```
+
+It provides:
+
+```lean
+DkNNReal.ofRat
+DkNNReal.zero
+DkNNReal.one
+DkNNReal.add
+DkNNReal.mul
+DkNNReal.pow
+```
+
+The nonnegativity witnesses are carried by the wrapper and no longer appear as
+arguments at each multiplication or power call. All operations remain
+computable transformations of rational interval observations.
+
+`DkNNReal.Equiv` lifts the existing representation equivalence, and
+`DkNNReal.equivSetoid` records it as a setoid. Addition, multiplication, and
+power have congruence theorems on this wrapper. The additive and multiplicative
+identity, associativity, commutativity, and distributivity laws are also
+available modulo `Equiv`.
+
+No `Add`, `Mul`, `Pow`, or `Semiring` instance is introduced on the raw wrapper.
+Such instances would state laws using Lean equality, whereas the established
+laws concern representation equivalence. A later quotient of
+`DkNNReal.equivSetoid`, or a dedicated quotient-backed public type, is the
+appropriate place for ordinary algebraic typeclasses.
+
 Persistent intersection and equality after a future evaluation into Mathlib's
 `Real` remain comparison principles. Their equivalence with vanishing
 separation should be proved later rather than assumed by definition.
````
`````
