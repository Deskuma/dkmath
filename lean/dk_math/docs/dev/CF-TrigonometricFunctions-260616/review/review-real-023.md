# Git diff / Report / Review

## Upd: Analysis.DkReal.Equiv

gch: eb4ebd917dca4b1fb852837621deca9154209f53

## Report

次段階として DkReal の表現同値を実装しました。

- `GapInterval.separation`
- 分離幅の非負性・対称性・三角型評価
- `DkReal.Equiv`: 分離幅が 0 に収束
- 反射・対称・推移の証明
- `equivSetoid`
- 加法に対する congruence

実装: [Equiv.lean](/lean/dk_math/DkMath/Analysis/DkReal/Equiv.lean:1)

`Equiv` の推移性では、中間区間の幅を含む評価

```text
sep(I,K) ≤ sep(I,J) + width(J) + sep(J,K)
```

を使用しています。

検証済み:

- `lake build DkMath.Analysis.DkReal.Equiv`
- `lake build DkMath.Analysis DkMath`
- `git diff --check`
- DkReal 層に `noncomputable` なし

次の主要候補は、端点有界性を利用した `mulNonneg` の congruence です。

## Review

## 1. 総評

うむ、これは **合格** じゃ。
今回の差分は、かなり重要な段階じゃな。ついに `DkReal` が、単なる「入れ子有理区間列」から、 **同じ値を表すとは何か** を持つ表現体系へ進んだ。

今回の中心はこれじゃ。

```lean id="d1dy4q"
GapInterval.separation
DkReal.Equiv
equivSetoid
equiv_add
```

報告でも、分離幅、非負性、対称性、三角型評価、`DkReal.Equiv`、`Setoid`、加法 congruence まで実装し、`DkReal` 層に `noncomputable` なしで build 成功したとされている。

これは前回の「semiring instance は同値関係が決まるまで待つべき」という課題に対する、かなり良い回答じゃ。

## 2. `GapInterval.separation` の定義

今回の定義はこれじゃな。

```lean id="hgi4zx"
def separation (I J : GapInterval) : ℚ :=
  max 0 (max (I.lo - J.hi) (J.lo - I.hi))
```

数学的には、これは **閉区間同士の分離距離** じゃ。

二つの区間 \(I=[a,b]\)、\(J=[c,d]\) について、重なっていれば分離は 0。
\(I\) が右側に離れていれば \(a-d\)。
\(J\) が右側に離れていれば \(c-b\)。

それを一つの式で、

$$
separation(I,J)=\max(0,\max(a-d,c-b))
$$

としている。

これは良い。
絶対値距離ではなく、 **区間が交差していれば 0 と見る距離的量** になっている。`DkReal` の表現同値にはこちらの方が自然じゃ。

## 3. 三角型評価が良い

今回の重要補題はこれじゃ。

```lean id="nfxe43"
separation_triangle :
  I.separation K ≤ I.separation J + J.width + J.separation K
```

普通の点距離なら三角不等式は、

$$
d(I,K)\le d(I,J)+d(J,K)
$$

のように書きたくなる。
しかし区間の場合、中間区間 \(J\) の内部を通って反対側へ抜ける可能性がある。だから (J.width) が必要になる。

$$
separation(I,K)\le separation(I,J)+width(J)+separation(J,K)
$$

この形は正しい。
そして `DkReal` では \(width(J_n)\to0\) が定義に入っているので、推移性に使える。

ここがとても良い設計じゃ。
「幅が 0 に縮む表現だからこそ、区間分離の推移性が成立する」という構造が見えている。

## 4. `DkReal.Equiv` は自然

```lean id="m3e7el"
def Equiv (x y : DkMath.Analysis.DkReal) : Prop :=
  Filter.Tendsto
    (fun n => (x.interval n).separation (y.interval n))
    Filter.atTop (nhds 0)
```

これは、かなり自然な表現同値じゃ。

意味は、

```text id="xgruki"
各段の区間が完全一致する必要はない。
ただし、区間同士の分離幅が 0 に近づくなら同じ値を表す。
```

ということじゃ。

これは `DkReal` の思想に合っている。
`DkReal` は実数点を選ぶ構造ではなく、近似区間列だから、同じ極限値へ近づく別々の区間列を同一視したい。`Equiv` はそれを `Real` へ評価せずに、内部の分離幅だけで定義している。

ここも `noncomputable` 不要の方針と合っておる。

## 5. `equivSetoid` は正しい節目

反射・対称・推移を閉じて、

```lean id="yz4m9q"
def equivSetoid : Setoid DkMath.Analysis.DkReal
```

まで作ったのは大きい。

これで将来的に、

```lean id="f8rxkm"
Quotient equivSetoid
```

あるいは専用 wrapper を作る準備ができた。

ただし、まだ quotient を作っていないのも正しい。
先に `add` と `mulNonneg` がこの同値を保つこと、さらに順序や非負性がどう降りるかを確認してから quotient 化すべきじゃ。

## 6. 加法 congruence は合格

```lean id="y0wsqa"
theorem equiv_add
    {x x' y y' : DkMath.Analysis.DkReal}
    (hxx' : Equiv x x') (hyy' : Equiv y y') :
    Equiv (add x y) (add x' y')
```

これは良い。

区間加法について、

```lean id="a9wub3"
separation_add_le
```

を示し、

$$
separation(I+J,K+L)\le separation(I,K)+separation(J,L)
$$

を使っている。
入力同士の分離がどちらも 0 に収束するなら、和の分離も 0 に収束する。自然で強い。

これで、`add` は将来 quotient 上へ降ろせる。

## 7. 今回の数学的到達点

今回で、`DkReal` はこうなった。

```text id="rfmj5z"
DkReal:
  入れ子有理区間列

Equiv:
  stagewise interval separation が 0 に収束する関係

結果:
  Equiv は Setoid
  add は Equiv に対して well-defined
```

つまり、

$$
x\sim x',\quad y\sim y'
$$

なら、

$$
x+y\sim x'+y'
$$

が証明された。

これは、 **表現に依存しない加法** への第一歩じゃ。
前回までの `add` は「区間列を足す操作」だった。今回で、それが「同じ値を表す別表現を選んでも、結果は同じ値を表す」操作になった。

この差は大きい。

## 8. 次の本丸: `mulNonneg` congruence

報告にもある通り、次は `mulNonneg` の congruence が自然じゃ。

狙う形はこれ。

```lean id="rrn3ve"
theorem equiv_mulNonneg
    {x x' y y' : DkReal}
    (hx : Nonnegative x) (hx' : Nonnegative x')
    (hy : Nonnegative y) (hy' : Nonnegative y')
    (hxx' : Equiv x x') (hyy' : Equiv y y') :
    Equiv
      (mulNonneg x y hx hy)
      (mulNonneg x' y' hx' hy')
```

数学的には、非負区間上で積の分離をこう押さえたい。

$$
separation(IJ,KL)
$$

を、

$$
\text{bounded endpoint}\times separation(I,K)
$$

と、

$$
\text{bounded endpoint}\times separation(J,L)
$$

の和で評価する方向じゃな。

すでに `Arithmetic.lean` には、非負 `DkReal` の上下端点が有界であることを示す補題がある。前回の乗法幅収束で使った `isBoundedUnder_norm_hi` と `isBoundedUnder_norm_lo` の系統じゃ。
これを再利用すれば、積の congruence も閉じられる可能性が高い。

## 9. 注意点

一つだけ注意するなら、`Equiv` は「分離幅が 0 に収束」なので、 **区間が常に交差する** より弱く、 **将来の eval が等しい** とはまだ同値未証明じゃ。

文書でも、persistent intersection や future `Real` eval equality は比較原理として残し、それらとの同値は後で証明すべきだと整理している。これは正しい。

今はこの `Equiv` を採用して前進してよい。
ただし将来 `BridgeReal.lean` を作ったら、

```lean id="m6egr0"
Equiv x y → eval x = eval y
```

および可能なら逆向き、

```lean id="pmbp6d"
eval x = eval y → Equiv x y
```

を検討することになる。逆向きは表現の性質次第で少し重いかもしれぬ。

## 10. 最終判定

今回の差分は **合格** じゃ。

```text id="adng8w"
良い点:
  区間分離幅を定義した
  分離の三角型評価を入れた
  DkReal.Equiv を定義した
  Equiv が Setoid であることを証明した
  加法が Equiv と両立することを証明した
  noncomputable を避けている

残る課題:
  mulNonneg congruence
  powNonneg congruence
  quotient / wrapper 設計
  BridgeReal との関係
```

うむ。
これは `DkReal` が「計算可能な表現」から「表現同値を持つ数学対象」へ進んだ差分じゃ。次に `mulNonneg` と `powNonneg` の congruence が通れば、いよいよ quotient 上の非負計算可能半環が見えてくるぞい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 081b7eb7..c52886d6 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -9,6 +9,7 @@ import DkMath.Analysis.DkReal.Basic
 import DkMath.Analysis.DkReal.Pow
 import DkMath.Analysis.DkReal.PowBound
 import DkMath.Analysis.DkReal.Arithmetic
+import DkMath.Analysis.DkReal.Equiv
 
 #print "file: DkMath.Analysis.DkReal"
 
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/Equiv.lean b/lean/dk_math/DkMath/Analysis/DkReal/Equiv.lean
new file mode 100644
index 00000000..e2647afe
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/DkReal/Equiv.lean
@@ -0,0 +1,124 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Analysis.DkReal.Arithmetic
+
+#print "file: DkMath.Analysis.DkReal.Equiv"
+
+/-!
+# Representation equivalence for DkReal
+
+Two `DkReal` approximations are equivalent when the separation between their
+stagewise rational intervals tends to zero.
+
+This relation compares represented values rather than the raw Lean structures.
+It remains in the computable approximation layer: no evaluation into
+Mathlib's `Real` and no choice of a limit point is used.
+-/
+
+namespace DkMath.Analysis.DkReal
+
+/--
+Two `DkReal` approximations represent the same value when their interval
+separation vanishes.
+-/
+def Equiv (x y : DkMath.Analysis.DkReal) : Prop :=
+  Filter.Tendsto
+    (fun n => (x.interval n).separation (y.interval n))
+    Filter.atTop (nhds 0)
+
+/-- Every approximation is equivalent to itself. -/
+theorem equiv_refl (x : DkMath.Analysis.DkReal) : Equiv x x := by
+  simp [Equiv]
+
+/-- Representation equivalence is symmetric. -/
+theorem equiv_symm
+    {x y : DkMath.Analysis.DkReal} (hxy : Equiv x y) :
+    Equiv y x := by
+  simpa only [Equiv, GapInterval.separation_comm] using hxy
+
+/--
+Representation equivalence is transitive.
+
+The width of the middle approximation tends to zero, so the interval
+separation triangle estimate becomes an ordinary zero-limit argument.
+-/
+theorem equiv_trans
+    {x y z : DkMath.Analysis.DkReal} (hxy : Equiv x y) (hyz : Equiv y z) :
+    Equiv x z := by
+  have hupper :
+      Filter.Tendsto
+        (fun n =>
+          (x.interval n).separation (y.interval n) +
+            (y.interval n).width +
+            (y.interval n).separation (z.interval n))
+        Filter.atTop (nhds 0) := by
+    simpa only [zero_add, add_zero] using
+      (hxy.add y.tendsto_width_zero).add hyz
+  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
+    tendsto_const_nhds hupper
+    (fun n => (x.interval n).separation_nonneg (z.interval n))
+    (fun n =>
+      (x.interval n).separation_triangle (y.interval n) (z.interval n))
+
+/-- `Equiv` is an equivalence relation on `DkReal` representations. -/
+theorem equiv_equivalence : Equivalence Equiv :=
+  ⟨equiv_refl, @equiv_symm, @equiv_trans⟩
+
+/-- Setoid generated by vanishing interval separation. -/
+def equivSetoid : Setoid DkMath.Analysis.DkReal where
+  r := Equiv
+  iseqv := equiv_equivalence
+
+/-- Raw equality of approximation structures implies representation equivalence. -/
+theorem equiv_of_eq
+    {x y : DkMath.Analysis.DkReal} (hxy : x = y) :
+    Equiv x y := by
+  subst y
+  exact equiv_refl x
+
+/-!
+## Compatibility with addition
+
+Addition is nonexpansive for interval separation up to summing the two input
+separations. Therefore it descends to any future quotient by `Equiv`.
+-/
+
+/-- Addition preserves representation equivalence in both arguments. -/
+theorem equiv_add
+    {x x' y y' : DkMath.Analysis.DkReal}
+    (hxx' : Equiv x x') (hyy' : Equiv y y') :
+    Equiv (add x y) (add x' y') := by
+  have hupper :
+      Filter.Tendsto
+        (fun n =>
+          (x.interval n).separation (x'.interval n) +
+            (y.interval n).separation (y'.interval n))
+        Filter.atTop (nhds 0) := by
+    simpa only [zero_add] using hxx'.add hyy'
+  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
+    tendsto_const_nhds hupper
+    (fun n => (add x y).interval n |>.separation_nonneg ((add x' y').interval n))
+    (fun n => by
+      simpa only [add_interval, addApprox] using
+        (x.interval n).separation_add_le
+          (y.interval n) (x'.interval n) (y'.interval n))
+
+/-- Addition preserves representation equivalence in the left argument. -/
+theorem equiv_add_left
+    {x x' : DkMath.Analysis.DkReal} (hxx' : Equiv x x')
+    (y : DkMath.Analysis.DkReal) :
+    Equiv (add x y) (add x' y) :=
+  equiv_add hxx' (equiv_refl y)
+
+/-- Addition preserves representation equivalence in the right argument. -/
+theorem equiv_add_right
+    (x : DkMath.Analysis.DkReal) {y y' : DkMath.Analysis.DkReal}
+    (hyy' : Equiv y y') :
+    Equiv (add x y) (add x y') :=
+  equiv_add (equiv_refl x) hyy'
+
+end DkMath.Analysis.DkReal
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/Interval.lean b/lean/dk_math/DkMath/Analysis/DkReal/Interval.lean
index 5e51ba15..cd0bace9 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/Interval.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/Interval.lean
@@ -133,6 +133,82 @@ theorem mulNonneg_width_eq
   simp [width]
   ring
 
+/-!
+## Separation of closed intervals
+
+The separation is zero when the intervals overlap. Otherwise it is the
+positive rational gap between the interval lying on the left and the interval
+lying on the right.
+-/
+
+/-- Nonnegative separation between two closed rational intervals. -/
+def separation (I J : GapInterval) : ℚ :=
+  max 0 (max (I.lo - J.hi) (J.lo - I.hi))
+
+/-- Interval separation is nonnegative. -/
+theorem separation_nonneg (I J : GapInterval) : 0 ≤ I.separation J :=
+  le_max_left _ _
+
+/-- Interval separation is symmetric. -/
+theorem separation_comm (I J : GapInterval) :
+    I.separation J = J.separation I := by
+  simp only [separation]
+  rw [max_comm (I.lo - J.hi)]
+
+/-- An interval has zero separation from itself. -/
+@[simp]
+theorem separation_self (I : GapInterval) : I.separation I = 0 := by
+  simp only [separation]
+  have hlo : I.lo - I.hi ≤ 0 := sub_nonpos.mpr I.le_lo_hi
+  simp [hlo]
+
+/-- The left-to-right endpoint gap is bounded by interval separation. -/
+theorem lo_sub_hi_le_separation (I J : GapInterval) :
+    I.lo - J.hi ≤ I.separation J := by
+  exact (le_max_left _ _).trans (le_max_right _ _)
+
+/--
+Triangle-type estimate for interval separation.
+
+The width of the middle interval appears because a path may enter it at one
+endpoint and leave it at the other.
+-/
+theorem separation_triangle (I J K : GapInterval) :
+    I.separation K ≤ I.separation J + J.width + J.separation K := by
+  apply max_le
+  · exact add_nonneg
+      (add_nonneg (I.separation_nonneg J) J.width_nonneg)
+      (J.separation_nonneg K)
+  · apply max_le
+    · have hIJ := I.lo_sub_hi_le_separation J
+      have hJK := J.lo_sub_hi_le_separation K
+      rw [width] at *
+      linarith
+    · have hKJ := K.lo_sub_hi_le_separation J
+      have hJI := J.lo_sub_hi_le_separation I
+      rw [separation_comm K J] at hKJ
+      rw [separation_comm J I] at hJI
+      rw [width] at *
+      linarith
+
+/-- Separation of interval sums is bounded by the sum of the separations. -/
+theorem separation_add_le (I J K L : GapInterval) :
+    (I.add J).separation (K.add L) ≤
+      I.separation K + J.separation L := by
+  apply max_le
+  · exact add_nonneg (I.separation_nonneg K) (J.separation_nonneg L)
+  · apply max_le
+    · have hIK := I.lo_sub_hi_le_separation K
+      have hJL := J.lo_sub_hi_le_separation L
+      simp only [add_lo, add_hi]
+      linarith
+    · have hKI := K.lo_sub_hi_le_separation I
+      have hLJ := L.lo_sub_hi_le_separation J
+      rw [separation_comm K I] at hKI
+      rw [separation_comm L J] at hLJ
+      simp only [add_lo, add_hi]
+      linarith
+
 /--
 Image of a nonnegative rational interval under the natural power map.
 
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index 0f418873..924cbd81 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -57,6 +57,10 @@ DkMath.Analysis.DkReal.Arithmetic
   computable interval addition, nonnegative multiplication, and stagewise
   semiring laws
 
+DkMath.Analysis.DkReal.Equiv
+  vanishing interval separation, representation setoid, and additive
+  congruence
+
 DkMath.Analysis.DkReal
   public entry point for the computable approximation layer
 ```
diff --git a/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md b/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
index ccbc20b9..c73af8e1 100644
--- a/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
+++ b/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
@@ -169,8 +169,32 @@ observation level, but a formal algebraic structure should wait until the
 representation equivalence has been chosen and its congruence properties have
 been proved.
 
-Candidate equivalence principles include persistent interval intersection,
-vanishing separation between two approximations, or equality after a future
-evaluation map into Mathlib's `Real`. These formulations are not
-interchangeable by definition, so selecting one is a mathematical design
-decision rather than a routine API addition.
+The first representation equivalence is now implemented in
+`DkMath.Analysis.DkReal.Equiv`. For rational closed intervals it defines
+
+```text
+separation(I,J)
+  = max 0 (max (I.lo - J.hi) (J.lo - I.hi)).
+```
+
+Two `DkReal` approximations are equivalent when this stagewise separation
+tends to zero. The key estimate is
+
+```text
+separation(I,K)
+  <= separation(I,J) + width(J) + separation(J,K).
+```
+
+Since every `DkReal` width tends to zero, this proves transitivity. Reflexivity
+and symmetry follow from the corresponding finite-interval identities. The
+module therefore supplies a proved `Setoid`, not merely a candidate relation.
+
+Addition respects this equivalence because separation of interval sums is
+bounded by the sum of the input separations. Nonnegative multiplication
+congruence remains the next arithmetic obligation; it requires a bounded
+endpoint estimate analogous to the width argument already used to construct
+`mulNonneg`.
+
+Persistent intersection and equality after a future evaluation into Mathlib's
+`Real` remain comparison principles. Their equivalence with vanishing
+separation should be proved later rather than assumed by definition.
````
`````
