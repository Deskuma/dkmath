# Git diff / Report / Review

## Add: CosmicFormula.Rotation.CF2D.Failure

gch: 69557214adbfa0e094c66a8b05dce802b39c59e2

## Report

仕上げました。

`review-trig-004.md` の次段階として、`CF2D` に以下を追加しています。

- [Basic.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Basic.lean): `UnitKernel.star` と `star_one`, `one_star`, `star_assoc`, `star_comm`
- [Trig.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Trig.lean): `KernelFamily.actLevel`, `actLevel_zero`, `actLevel_add`
- [Failure.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Failure.lean): wrong-sign kernel `badStarPlus` と residual `4 * a * b * x * y` の形式化
- [CF2D.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D.lean): `Failure` を入口 import に追加
- [Rotation2D-Implementation.md](/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md): 実装結果と失敗カーネルの差分を追記

検証済みです。

```text
lake build DkMath.CosmicFormula.Rotation.CF2D.Basic
lake build DkMath.CosmicFormula.Rotation.CF2D.Failure
lake build DkMath.CosmicFormula.Rotation.CF2D.Trig
lake build DkMath.CosmicFormula.Rotation
lake build DkMath
git diff --check
```

すべて成功しています。

## Review

## 1. 現在差分の総評

うむ、これは **かなり良い更新** じゃ。
今回の `6955721...` は、単なる補題追加ではなく、`CF2D` の意味を一段締めておる。

今回入ったものは大きく三つじゃ。

```text id="64yjzo"
1. UnitKernel.star による単位核同士の閉包
2. KernelFamily.actLevel による等高線上の作用
3. Failure.lean による「保存が壊れる場合」の形式化
```

報告では、`UnitKernel.star` とその単位元・結合・可換補題、`KernelFamily.actLevel` と作用則、さらに wrong-sign kernel `badStarPlus` と残差 (4abxy) が追加され、`lake build DkMath` と `git diff --check` まで成功している。

結論として、 **採用でよい** 。

## 2. 今回の一番大きな意味

今回の本丸は `Failure.lean` じゃ。

正しい核は、

$$
(a,b)\star(x,y)=(ax-by,\;ay+bx)
$$

であり、

$$
Q((a,b)\star(x,y))=Q(a,b)Q(x,y)
$$

を満たす。

一方、今回追加された失敗核は、

$$
(a,b)\diamond(x,y)=(ax+by,\;ay+bx)
$$

じゃ。

すると、

$$
Q((a,b)\diamond(x,y)) = Q(a,b)Q(x,y)+4abxy
$$

となる。

つまり、余計な残差

$$
4abxy
$$

が出る。

これはものすごく重要じゃ。
なぜなら、これで **「符号配置が少し違うだけで保存が壊れる」** ことが Lean 上で見えるようになったからじゃ。

## 3. 宇宙式だけで足りるか問題への答え

今回の `Failure.lean` によって、答えが少し明確になった。

宇宙式だけで、

$$
Q(x,y)=x^2+y^2
$$

という保存量を置くことはできる。

だが、その保存量を本当に保つ作用を得るには、積の符号構造が正しくなければならない。

つまり、

$$
\boxed{
保存量を置くだけでは足りない。
保存量を保つ符号構造まで必要。
}
$$

じゃ。

正しい `star` では交差 Beam が

$$
-2abxy+2abxy=0
$$

と相殺される。

失敗核 `badStarPlus` では、

$$
+2abxy+2abxy=4abxy
$$

となり、残差が残る。

したがって、宇宙式は基盤としては強い。
しかし、その基盤上に立つ変換核の符号がズレると、保存円は崩れる。

ここで、ぬしの問い

```text id="5k2bk0"
基盤がズレていた場合、どうなっていたか？
```

に対する答えが出た。

$$
\boxed{
ズレていた場合、残差 (4abxy) が出て、円は保存されない。
}
$$

これは見事な検出結果じゃ。

## 4. `UnitKernel.star` の意味

`UnitKernel.star` が入ったことで、単位核たちは単なる「作用するもの」ではなく、 **自分たち同士で閉じる世界** になった。

$$
Q(r)=1,\quad Q(s)=1
$$

なら、

$$
Q(r\star s)=Q(r)Q(s)=1
$$

なので、

$$
r\star s
$$

もまた単位核になる。

これにより、単位核集合は

```text id="k4kkv1"
保存核の表面
```

として振る舞う。

さらに、

```lean id="ngmmnf"
star_one
one_star
star_assoc
star_comm
```

が入ったので、実質的には可換モノイド的な核構造が見えている。

これは今後、`KernelFamily` を

$$
T\to UnitKernel
$$

への準同型として読むための足場になる。

## 5. `actLevel` の意味

`LevelSet R rho2` は、

$$
Q(z)=\rho^2
$$

を満たす点の集合じゃ。

今回、

```lean id="52eayx"
KernelFamily.actLevel
actLevel_zero
actLevel_add
```

が入った。

これは、

$$
R(t)
$$

が任意の平方質量等高線をその内側で動かすことを意味する。

つまり、ここでようやく、

$$
\boxed{
円 = 保存量 (Q) の等高線
}
$$

$$
\boxed{
回転 = その等高線上の自己作用
}
$$

が Lean 上でつながった。

前までは「保存する」という点の定理だった。
今回で「保存面の上を動く」という幾何的読みへ進んだ。

これはかなり大きい。

## 6. 今回の構造的到達点

ここまでで、`CF2D` は次の階段を登った。

```text id="68i2zg"
Vec.q2
  二成分平方質量

Vec.star
  正しい保存核

Vec.q2_star
  保存核の乗法保存

UnitKernel
  平方質量 1 の核

UnitKernel.star
  単位核同士の閉包

LevelSet
  保存量の等高線

KernelFamily
  加法パラメータ付き単位核族

actLevel
  等高線上の作用

Failure
  符号がズレた場合の残差検出
```

これで、単純な三角関数の証明というより、もう **二次保存量に対する正しい変換核の分類入口** になっておる。

## 7. Review 上の軽い注意点

ブロッカーはない。

ただし、将来の整理候補はある。

`UnitKernel.star_one`, `one_star`, `star_assoc`, `star_comm` は、構造体等式なので、今は `cases` と `simp` で通っておる。これは問題ないが、将来補題が増えるなら、

```lean id="1o3gp5"
@[ext]
theorem UnitKernel.ext ...
```

あるいは値だけで比較する補題を先に整えておくと、証明が少し楽になるかもしれぬ。

ただ、現段階では急がなくてよい。
build が通っており、API としても十分じゃ。

## 8. 次にやるなら

今回はかなり進んだので、次は二択じゃ。

### 8.1. 安定路線

`UnitKernel` の構造を少し整理する。

候補：

```lean id="pdp83l"
UnitKernel.ext
UnitKernel.star_val
UnitKernel.act_star
```

特に、

$$
(r\star s)\cdot z=r\cdot(s\cdot z)
$$

に対応する

```lean id="nhq2jv"
UnitKernel.act_star
```

は自然じゃ。

これが入ると、`KernelFamily.act_add` もより単位核モノイドの作用として読める。

### 8.2. 探索路線

`Failure.lean` を広げる。

今は `badStarPlus` だけじゃが、符号パターンは他にもある。

```text id="0uogbo"
(ax - by, ay + bx) 正しい円保存
(ax + by, ay + bx) 残差 +4abxy
(ax - by, ay - bx) 別残差
(ax + by, ay - bx) 双曲的な別世界の可能性
```

ここを全部展開すると、

```text id="pbvm3s"
どの符号配置が円を保存するか
どの符号配置が壊れるか
どの符号配置が双曲保存へ行くか
```

が見える。

これは「基盤がズレた場合」の調査としてとても良い。

## 9. わっちの推奨

今すぐ次へ進めるなら、わっちはこう勧める。

```text id="o32wac"
1. UnitKernel.act_star を追加
2. UnitKernel.ext か val ext 補題を追加
3. Failure.lean に sign-pattern の分類を少し追加
```

ただし、先ほどの偏角・GN 比・和ゲージの話は、まだ実装しない方がよい。
あれは考察資料に封じた通り、探索層じゃ。

いまの `CF2D` は、まず

```text id="u3tfyk"
保存核
等高線作用
失敗核
```

の三点を安定させるのがよい。

## 10. 結論

今回の更新で、`CF2D` は単なる三角関数の抽象化ではなくなった。

$$
\boxed{
正しい符号配置なら保存される。
ズレた符号配置なら残差が出る。
}
$$

これが Lean で確認された。

つまり、宇宙式はただ「円を作る」のではなく、
**円を保存できる変換と、保存できない変換を見分ける** 。

これはとても大きい。

わっちの評価はこうじゃ。

```text id="qk4nsk"
実装品質: 良好
理論的意義: 大きい
採用判断: 採用
次作業: UnitKernel.act_star と Failure sign-pattern 拡張
```

ここまで来ると、三角関数の基盤構築としては、かなり頼もしい足場になっておる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D.lean
index 5ba3aa2a..fd579fea 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D.lean
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D.lean
@@ -5,6 +5,7 @@ Authors: D. and Wise Wolf.
 -/

 import DkMath.CosmicFormula.Rotation.CF2D.Basic
+import DkMath.CosmicFormula.Rotation.CF2D.Failure
 import DkMath.CosmicFormula.Rotation.CF2D.Trig
 import DkMath.CosmicFormula.Rotation.CF2D.Real

diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Basic.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Basic.lean
index c5d56b85..fcb1dbf5 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Basic.lean
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Basic.lean
@@ -166,6 +166,48 @@ theorem coe_q2 [Semiring R] (r : UnitKernel R) : Vec.q2 (r : Vec R) = 1 :=
 def one (R : Type u) [CommRing R] : UnitKernel R :=
   ⟨Vec.one R, by simp [Vec.q2, Vec.one]⟩

+/-- Product of two unit kernels. -/
+def star [CommRing R] (r s : UnitKernel R) : UnitKernel R :=
+  ⟨Vec.star (r : Vec R) (s : Vec R), by
+    rw [Vec.q2_star, coe_q2, coe_q2, one_mul]⟩
+
+@[simp]
+theorem star_val [CommRing R] (r s : UnitKernel R) :
+    (star r s : Vec R) = Vec.star (r : Vec R) (s : Vec R) := rfl
+
+@[simp]
+theorem star_q2 [CommRing R] (r s : UnitKernel R) : Vec.q2 (star r s : Vec R) = 1 :=
+  coe_q2 (star r s)
+
+@[simp]
+theorem star_one [CommRing R] (r : UnitKernel R) : star r (one R) = r := by
+  cases r with
+  | mk val q2_eq_one =>
+      simp [star, one]
+
+@[simp]
+theorem one_star [CommRing R] (r : UnitKernel R) : star (one R) r = r := by
+  cases r with
+  | mk val q2_eq_one =>
+      simp [star, one]
+
+theorem star_assoc [CommRing R] (p q r : UnitKernel R) :
+    star (star p q) r = star p (star q r) := by
+  cases p with
+  | mk pv hp =>
+      cases q with
+      | mk qv hq =>
+          cases r with
+          | mk rv hr =>
+              simp [star, Vec.star_assoc]
+
+theorem star_comm [CommRing R] (r s : UnitKernel R) : star r s = star s r := by
+  cases r with
+  | mk rv hr =>
+      cases s with
+      | mk sv hs =>
+          simp [star, Vec.star_comm]
+
 /-- The action of a unit kernel on a two-component state. -/
 def act [CommRing R] (r : UnitKernel R) (z : Vec R) : Vec R :=
   Vec.star (r : Vec R) z
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Failure.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Failure.lean
new file mode 100644
index 00000000..d2b490ed
--- /dev/null
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Failure.lean
@@ -0,0 +1,71 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.CosmicFormula.Rotation.CF2D.Basic
+
+#print "file: DkMath.CosmicFormula.Rotation.CF2D.Failure"
+
+/-!
+# Failure examples for the CF2D rotation kernel
+
+This file records what breaks when the sign pattern of the two-component kernel
+is changed.  The correct kernel cancels the opposite beam terms.  The plus-plus
+kernel leaves a residual `4 * a * b * x * y`, so it does not preserve `q2` in
+general.
+-/
+
+namespace DkMath
+namespace CosmicFormula
+namespace Rotation
+namespace CF2D
+
+namespace Vec
+
+variable {R : Type u}
+
+/--
+A deliberately wrong two-component product.
+
+The sign in the first coordinate is changed from `a*x - b*y` to `a*x + b*y`.
+-/
+def badStarPlus [Ring R] (r z : Vec R) : Vec R :=
+  ⟨r.core * z.core + r.beam * z.beam,
+    r.core * z.beam + r.beam * z.core⟩
+
+@[simp]
+theorem badStarPlus_core [Ring R] (r z : Vec R) :
+    (badStarPlus r z).core = r.core * z.core + r.beam * z.beam := rfl
+
+@[simp]
+theorem badStarPlus_beam [Ring R] (r z : Vec R) :
+    (badStarPlus r z).beam = r.core * z.beam + r.beam * z.core := rfl
+
+/--
+The wrong sign pattern leaves a residual beam term.
+
+For the correct `star`, this residual is absent and `q2` is multiplicative.
+-/
+theorem q2_badStarPlus [CommRing R] (a b x y : R) :
+    q2 (badStarPlus (Vec.mk a b) (Vec.mk x y))
+      = (a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) + 4 * a * b * x * y := by
+  simp [q2, badStarPlus]
+  ring
+
+theorem q2_badStarPlus_eq_q2_mul_add_residual [CommRing R] (r z : Vec R) :
+    q2 (badStarPlus r z) = q2 r * q2 z + 4 * r.core * r.beam * z.core * z.beam := by
+  cases r with
+  | mk a b =>
+      cases z with
+      | mk x y =>
+          simpa [q2] using q2_badStarPlus (R := R) a b x y
+
+end Vec
+
+end CF2D
+end Rotation
+end CosmicFormula
+end DkMath
+
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Trig.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Trig.lean
index 71820603..577bef6b 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Trig.lean
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Trig.lean
@@ -138,6 +138,29 @@ theorem act_add (F : KernelFamily T R) (t s : T) (z : Vec R) :
     (((F.kernel s : UnitKernel R) : Vec R))
     z

+/-- A kernel family acts on every square-mass level set. -/
+def actLevel (F : KernelFamily T R) (t : T) {rho2 : R}
+    (z : LevelSet R rho2) : LevelSet R rho2 :=
+  LevelSet.act (F.kernel t) z
+
+@[simp]
+theorem actLevel_val (F : KernelFamily T R) (t : T) {rho2 : R}
+    (z : LevelSet R rho2) :
+    (F.actLevel t z).1 = UnitKernel.act (F.kernel t) z.1 := rfl
+
+@[simp]
+theorem actLevel_zero (F : KernelFamily T R) {rho2 : R}
+    (z : LevelSet R rho2) :
+    F.actLevel 0 z = z := by
+  apply Subtype.ext
+  simp [actLevel, F.act_zero]
+
+theorem actLevel_add (F : KernelFamily T R) (t s : T) {rho2 : R}
+    (z : LevelSet R rho2) :
+    F.actLevel (t + s) z = F.actLevel t (F.actLevel s z) := by
+  apply Subtype.ext
+  simp [actLevel, F.act_add]
+
 /-- Core double-angle formula in the abstract unit-kernel family. -/
 theorem C_add_self (F : KernelFamily T R) (t : T) :
     F.C (t + t) = F.C t ^ 2 - F.S t ^ 2 := by
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md b/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md
index 42f5f49e..9c9c5802 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md
@@ -7,6 +7,7 @@ The implementation is under:
 - `DkMath.CosmicFormula.Rotation`
 - `DkMath.CosmicFormula.Rotation.CF2D`
 - `DkMath.CosmicFormula.Rotation.CF2D.Basic`
+- `DkMath.CosmicFormula.Rotation.CF2D.Failure`
 - `DkMath.CosmicFormula.Rotation.CF2D.Trig`
 - `DkMath.CosmicFormula.Rotation.CF2D.Real`

@@ -74,6 +75,31 @@ Thus a "rotation" is not assumed first.  The formal layer finds a
 square-mass-preserving unit-kernel action, and this action receives the
 rotation interpretation.

+Unit kernels also form the algebraic kernel product:
+
+```lean
+UnitKernel.star r s
+
+UnitKernel.star_val :
+  (UnitKernel.star r s : Vec R) = Vec.star (r : Vec R) (s : Vec R)
+
+UnitKernel.star_one :
+  UnitKernel.star r (UnitKernel.one R) = r
+
+UnitKernel.one_star :
+  UnitKernel.star (UnitKernel.one R) r = r
+
+UnitKernel.star_assoc :
+  UnitKernel.star (UnitKernel.star p q) r
+    = UnitKernel.star p (UnitKernel.star q r)
+
+UnitKernel.star_comm :
+  UnitKernel.star r s = UnitKernel.star s r
+```
+
+These lemmas make the unit kernels available as the abstract rotation-kernel
+surface, while the underlying product remains the same `Vec.star` calculation.
+
 ## Level Sets

 `LevelSet R rho2` is the square-mass level set `Vec.q2 z = rho2`.
@@ -139,6 +165,15 @@ KernelFamily.act_add :
   UnitKernel.act (F.kernel (t + s)) z
     = UnitKernel.act (F.kernel t) (UnitKernel.act (F.kernel s) z)

+KernelFamily.actLevel :
+  LevelSet R rho2 -> LevelSet R rho2
+
+KernelFamily.actLevel_zero :
+  F.actLevel 0 z = z
+
+KernelFamily.actLevel_add :
+  F.actLevel (t + s) z = F.actLevel t (F.actLevel s z)
+
 KernelFamily.C_add_self :
   F.C (t + t) = F.C t ^ 2 - F.S t ^ 2

@@ -150,6 +185,31 @@ These are the cosmic-formula versions of the basic trigonometric identities:
 they are derived from conservation and kernel composition, not from existing
 trigonometric API.

+## Failure Kernel
+
+`Failure.lean` records the nearby wrong-sign calculation.  If both coordinates
+use the plus sign
+
+```lean
+Vec.badStarPlus (a,b) (x,y) = (a*x + b*y, a*y + b*x)
+```
+
+then the square mass is not multiplicative.  The residual term is formalized as:
+
+```lean
+Vec.q2_badStarPlus :
+  Vec.q2 (Vec.badStarPlus (Vec.mk a b) (Vec.mk x y))
+    = (a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) + 4 * a * b * x * y
+
+Vec.q2_badStarPlus_eq_q2_mul_add_residual :
+  Vec.q2 (Vec.badStarPlus r z)
+    = Vec.q2 r * Vec.q2 z + 4 * r.core * r.beam * z.core * z.beam
+```
+
+This separates the preservation kernel from a superficially similar but
+non-preserving kernel.  The cancellation in `Vec.q2_star` depends on the
+opposite signs in the two beam cross terms.
+
 ## Additive Group Layer

 When the parameter type has an additive group structure, `Trig.lean` also
````
`````
