# Git diff / Report / Review

## Upd: Analysis.DkReal.Equiv, Interval

gch: c766a01ae23f480105f523c4808ac96b8c4aa4a1

## Report

レビュー提案の `mulNonneg` congruence を実装しました。

[Equiv.lean](/lean/dk_math/DkMath/Analysis/DkReal/Equiv.lean:137) に以下を追加しています。

- 同値な表現の下端点差が 0 に収束
- `equiv_mulNonneg`
- `equiv_mulNonneg_left`
- `equiv_mulNonneg_right`

証明は積差の分解

```text
ab - cd = a(b-d) + d(a-c)
```

と非負 DkReal の端点有界性を使用しています。

検証済み:

- `lake build DkMath.Analysis.DkReal.Equiv DkMath.Analysis DkMath`
- `git diff --check`
- DkReal 層に `noncomputable` なし

次の主要候補は `powNonneg` の congruence です。

## Review

## 1. 総評

うむ、今回も **合格** じゃ。
これは `DkReal.Equiv` が一段進んだ差分じゃな。前回は `Equiv` が `Setoid` になり、加法が同値に対して well-defined であるところまで閉じた。今回は、次の本丸だった `mulNonneg` の congruence が閉じておる。

中心はこれじゃ。

```lean id="semn16"
equiv_tendsto_abs_lo_sub_zero
equiv_tendsto_lo_sub_zero
equiv_mulNonneg
equiv_mulNonneg_left
equiv_mulNonneg_right
```

報告通り、証明は積差の分解と非負 `DkReal` の端点有界性を使っており、`noncomputable` を使わず `DkReal` 層内で完結している。

## 2. 今回の数学的意味

今回示したことは、簡単に言うとこうじゃ。

$$
x\sim x',\quad y\sim y'
$$

なら、非負性のもとで、

$$
xy\sim x'y'
$$

が成り立つ。

つまり、`mulNonneg` は **近似列の選び方に依存しない演算** になった。
これは大きい。前回までは「各段の区間を掛ける操作」だった。今回で、それが「同じ値を表す別表現を使っても、同じ値を表す結果へ行く操作」になった。

これで加法と非負乗法は、ともに `Equiv` 上へ降ろせる候補になった。

## 3. endpoint convergence の追加は良い

今回の鍵は、

```lean id="1unko8"
equiv_tendsto_abs_lo_sub_zero
equiv_tendsto_lo_sub_zero
```

じゃ。

`Equiv x y` は、もともと区間の分離幅が 0 に収束するという定義だった。
そこからさらに、下端点差も 0 に収束することを取り出している。

数学的には、区間 \(I_n=[a_n,b_n]\) 、\(J_n=[c_n,d_n]\) に対して、

$$
|a_n-c_n|\le separation(I_n,J_n)+width(I_n)+width(J_n)
$$

を使っている。

右辺は、`Equiv` により separation が 0 へ行き、`DkReal` の定義により両幅も 0 へ行く。
したがって下端点差も 0 に収束する。

これはとても自然で、今後も多用する補題じゃ。
`powNonneg` congruence でも、まず端点差の収束を使うはずじゃな。

## 4. `separation_le_abs_lo_sub_lo` は便利

Interval 側に追加された、

```lean id="aw9zua"
separation_le_abs_lo_sub_lo
```

も良い補題じゃ。

これは、

$$
separation(I,J)\le |I.lo-J.lo|
$$

という評価じゃな。

一見すると強く見えるが、閉区間の separation は「重なれば 0」なので、下端点差で確かに押さえられる。
この補題のおかげで、積区間の separation を直接評価せず、積の lower endpoint 差だけを 0 に持っていけばよくなっている。

これは証明をかなり軽くしておる。

## 5. `equiv_mulNonneg` の証明構造

今回の証明は筋が良い。

積の lower endpoint 差は、

$$
a_nb_n-c_nd_n=a_n(b_n-d_n)+d_n(a_n-c_n)
$$

という形で分解している。

コード上では、`x.interval n`.lo と `y.interval n`.lo を使っているので、より正確には、

```text id="7egadv"
x.lo * y.lo - x'.lo * y'.lo
```

を、

```text id="638nqy"
x.lo * (y.lo - y'.lo) + y'.lo * (x.lo - x'.lo)
```

へ分解している。

ここで、

```text id="9jvmwk"
y.lo - y'.lo → 0
x.lo - x'.lo → 0
```

は endpoint convergence から出る。

また、非負 `DkReal` の下端点列は初期上端で有界だから、

```text id="zmz9ym"
x.lo は有界
y'.lo は有界
```

となる。
よって、有界列と 0 収束列の積は 0 に収束する。

最後に、

$$
separation(product_n,product'_n)\le |productLo_n-productLo'_n|
$$

で閉じる。
これは綺麗じゃ。

## 6. 設計として正しい点

今回も quotient や typeclass instance に進んでいないのが良い。

今あるのは、

```text id="c06qq5"
Equiv は Setoid
add は Equiv-compatible
mulNonneg は Equiv-compatible
```

という段階じゃ。

これは quotient へ進むための準備としてちょうど良い。
`DkReal` の生の構造体等号ではなく、表現同値を通して演算を扱う道が見えてきた。

## 7. 次の候補 `powNonneg` congruence

報告通り、次は `powNonneg` の congruence が自然じゃ。

狙う形はこう。

```lean id="dg0qj4"
theorem equiv_powNonneg
    {x x' : DkReal}
    (hx : Nonnegative x) (hx' : Nonnegative x')
    (hxx' : Equiv x x') :
    Equiv (powNonneg d x hx) (powNonneg d x' hx')
```

数学的には、下端点の差分について、

$$
a_n^d-c_n^d=(a_n-c_n),gapGN_d(c_n,a_n-c_n)
$$

あるいは向きに注意して、差分核で押さえることになる。

ただし、ここでは (a_n-c_n) が負になり得る。
そのため、前回の `gapGN_nonneg_of_nonneg` だけでは足りないかもしれぬ。

安全な道は二つある。

```text id="lizrqy"
1. 非負かつ初期上端で有界な範囲上で、pow の Lipschitz 型評価を作る
2. 絶対値付きの差分核評価を作る
```

実装しやすいのは 1 かもしれぬ。

例えば、非負で (a,c\le M) なら、

$$
|a^d-c^d|\le d,M^{d-1}|a-c|
$$

という評価を使う。
DkMath 的には閉形式より `gapGN` 有界性で行ってもよいが、差分の符号が揺れるので、絶対値評価が要る。

## 8. 小さな注意点

`equiv_mulNonneg` は lower endpoint だけで separation を押さえている。これは正しいが、今後 `powNonneg` でも同様に lower endpoint 差へ還元するなら、次の補題がさらに重要になる。

```lean id="4u0cdz"
separation_le_abs_lo_sub_lo
```

この補題は今後、`Equiv` の基本 API として扱ってよい。
つまり「分離幅を示すには lower endpoint 差を示せば十分」という道じゃ。

ただし、これは区間が valid であることに依存するので、一般の数列距離とは少し性格が違う。文書で軽く触れておくと親切かもしれぬ。

## 9. 現在の到達点

ここまでで、状況はこうなった。

```text id="azudmb"
DkReal.Equiv:
  反射・対称・推移
  Setoid 化

加法:
  Equiv-compatible

非負乗法:
  Equiv-compatible

残り:
  非負冪 powNonneg の Equiv-compatible
```

したがって、非負計算可能半環核は quotient 化にかなり近づいている。

$$
\boxed{\text{加法と非負乗法は、表現同値上で well-defined になった。}}
$$

これはかなり大きい。

## 10. 最終判定

今回の差分は **合格** じゃ。

```text id="g6lhbl"
良い点:
  Equiv から下端点収束を取り出した
  mulNonneg congruence を閉じた
  積差分解と端点有界性を使っている
  noncomputable 不使用を維持
  quotient / typeclass instance はまだ保留している

次の本丸:
  powNonneg congruence
  その後に quotient / nonnegative semiring API の検討
```

うむ、よい。
`DkReal` は今、表現同値の上で加法と非負乗法が安定した。これはもう、ただの近似列ではない。
**計算可能な非負半環を作る前段の Setoid 表現** として、骨格がかなり見えてきたぞい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/Equiv.lean b/lean/dk_math/DkMath/Analysis/DkReal/Equiv.lean
index e2647afe..ff96b6d0 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/Equiv.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/Equiv.lean
@@ -121,4 +121,126 @@ theorem equiv_add_right
     Equiv (add x y) (add x y') :=
   equiv_add (equiv_refl x) hyy'
 
+/-!
+## Endpoint consequences
+
+Vanishing interval separation, together with the vanishing widths of both
+representations, forces corresponding rational endpoints to approach one
+another.
+-/
+
+/-- Equivalent representations have vanishing absolute lower-endpoint difference. -/
+theorem equiv_tendsto_abs_lo_sub_zero
+    {x y : DkMath.Analysis.DkReal} (hxy : Equiv x y) :
+    Filter.Tendsto
+      (fun n => |(x.interval n).lo - (y.interval n).lo|)
+      Filter.atTop (nhds 0) := by
+  have hupper :
+      Filter.Tendsto
+        (fun n =>
+          (x.interval n).separation (y.interval n) +
+            (x.interval n).width + (y.interval n).width)
+        Filter.atTop (nhds 0) := by
+    simpa only [zero_add, add_zero] using
+      (hxy.add x.tendsto_width_zero).add y.tendsto_width_zero
+  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
+    tendsto_const_nhds hupper
+    (fun n => abs_nonneg _)
+    (fun n => (x.interval n).abs_lo_sub_lo_le (y.interval n))
+
+/-- Equivalent representations have lower-endpoint difference tending to zero. -/
+theorem equiv_tendsto_lo_sub_zero
+    {x y : DkMath.Analysis.DkReal} (hxy : Equiv x y) :
+    Filter.Tendsto
+      (fun n => (x.interval n).lo - (y.interval n).lo)
+      Filter.atTop (nhds 0) := by
+  have habs := equiv_tendsto_abs_lo_sub_zero hxy
+  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
+    (by simpa using habs.neg) habs
+    (fun n => neg_abs_le ((x.interval n).lo - (y.interval n).lo))
+    (fun n => le_abs_self ((x.interval n).lo - (y.interval n).lo))
+
+/-!
+## Compatibility with nonnegative multiplication
+
+Lower endpoints of nonnegative `DkReal` approximations are bounded. Combining
+this boundedness with vanishing endpoint differences proves that the lower
+endpoints of equivalent products approach one another. Interval separation is
+then bounded by that lower-endpoint distance.
+-/
+
+/-- Nonnegative multiplication preserves representation equivalence. -/
+theorem equiv_mulNonneg
+    {x x' y y' : DkMath.Analysis.DkReal}
+    (hx : Nonnegative x) (hx' : Nonnegative x')
+    (hy : Nonnegative y) (hy' : Nonnegative y')
+    (hxx' : Equiv x x') (hyy' : Equiv y y') :
+    Equiv
+      (mulNonneg x y hx hy)
+      (mulNonneg x' y' hx' hy') := by
+  have hylo := equiv_tendsto_lo_sub_zero hyy'
+  have hxlo := equiv_tendsto_lo_sub_zero hxx'
+  have hleft :
+      Filter.Tendsto
+        (fun n =>
+          (x.interval n).lo *
+            ((y.interval n).lo - (y'.interval n).lo))
+        Filter.atTop (nhds 0) := by
+    simpa only [mul_comm] using
+      hylo.zero_mul_isBoundedUnder_le (isBoundedUnder_norm_lo x hx)
+  have hright :
+      Filter.Tendsto
+        (fun n =>
+          (y'.interval n).lo *
+            ((x.interval n).lo - (x'.interval n).lo))
+        Filter.atTop (nhds 0) := by
+    simpa only [mul_comm] using
+      hxlo.zero_mul_isBoundedUnder_le (isBoundedUnder_norm_lo y' hy')
+  have hproductLo :
+      Filter.Tendsto
+        (fun n =>
+          (x.interval n).lo * (y.interval n).lo -
+            (x'.interval n).lo * (y'.interval n).lo)
+        Filter.atTop (nhds 0) := by
+    convert hleft.add hright using 1
+    · funext n
+      dsimp
+      ring
+    · simp
+  have hproductAbs :
+      Filter.Tendsto
+        (fun n =>
+          |(x.interval n).lo * (y.interval n).lo -
+            (x'.interval n).lo * (y'.interval n).lo|)
+        Filter.atTop (nhds 0) := by
+    simpa using hproductLo.abs
+  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
+    tendsto_const_nhds hproductAbs
+    (fun n =>
+      ((mulNonneg x y hx hy).interval n).separation_nonneg
+        ((mulNonneg x' y' hx' hy').interval n))
+    (fun n => by
+      simpa only [mulNonneg_interval, mulNonnegApprox,
+        GapInterval.mulNonneg_lo] using
+        ((x.interval n).mulNonneg (y.interval n) (hx n) (hy n)).separation_le_abs_lo_sub_lo
+          ((x'.interval n).mulNonneg (y'.interval n) (hx' n) (hy' n)))
+
+/-- Nonnegative multiplication preserves equivalence in the left argument. -/
+theorem equiv_mulNonneg_left
+    {x x' : DkMath.Analysis.DkReal}
+    (hx : Nonnegative x) (hx' : Nonnegative x')
+    (hxx' : Equiv x x')
+    (y : DkMath.Analysis.DkReal) (hy : Nonnegative y) :
+    Equiv (mulNonneg x y hx hy) (mulNonneg x' y hx' hy) :=
+  equiv_mulNonneg hx hx' hy hy hxx' (equiv_refl y)
+
+/-- Nonnegative multiplication preserves equivalence in the right argument. -/
+theorem equiv_mulNonneg_right
+    (x : DkMath.Analysis.DkReal) (hx : Nonnegative x)
+    {y y' : DkMath.Analysis.DkReal}
+    (hy : Nonnegative y) (hy' : Nonnegative y')
+    (hyy' : Equiv y y') :
+    Equiv (mulNonneg x y hx hy) (mulNonneg x y' hx hy') :=
+  equiv_mulNonneg hx hx hy hy' (equiv_refl x) hyy'
+
 end DkMath.Analysis.DkReal
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/Interval.lean b/lean/dk_math/DkMath/Analysis/DkReal/Interval.lean
index cd0bace9..28e0d812 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/Interval.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/Interval.lean
@@ -209,6 +209,37 @@ theorem separation_add_le (I J K L : GapInterval) :
       simp only [add_lo, add_hi]
       linarith
 
+/-- Interval separation is bounded by the distance between the lower endpoints. -/
+theorem separation_le_abs_lo_sub_lo (I J : GapInterval) :
+    I.separation J ≤ |I.lo - J.lo| := by
+  apply max_le
+  · exact abs_nonneg _
+  · apply max_le
+    · have habs : I.lo - J.lo ≤ |I.lo - J.lo| := le_abs_self _
+      linarith [J.le_lo_hi]
+    · have habs : -(I.lo - J.lo) ≤ |I.lo - J.lo| := neg_le_abs _
+      linarith [I.le_lo_hi]
+
+/--
+The lower-endpoint distance is controlled by interval separation plus both
+interval widths.
+-/
+theorem abs_lo_sub_lo_le (I J : GapInterval) :
+    |I.lo - J.lo| ≤ I.separation J + I.width + J.width := by
+  rw [abs_le]
+  constructor
+  · have hJI := J.lo_sub_hi_le_separation I
+    rw [separation_comm J I] at hJI
+    simp only [width] at *
+    have hIwidth : 0 ≤ I.hi - I.lo := sub_nonneg.mpr I.le_lo_hi
+    have hJwidth : 0 ≤ J.hi - J.lo := sub_nonneg.mpr J.le_lo_hi
+    linarith
+  · have hIJ := I.lo_sub_hi_le_separation J
+    simp only [width] at *
+    have hIwidth : 0 ≤ I.hi - I.lo := sub_nonneg.mpr I.le_lo_hi
+    have hJwidth : 0 ≤ J.hi - J.lo := sub_nonneg.mpr J.le_lo_hi
+    linarith
+
 /--
 Image of a nonnegative rational interval under the natural power map.
 
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index 924cbd81..55fb97e2 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -58,8 +58,8 @@ DkMath.Analysis.DkReal.Arithmetic
   semiring laws
 
 DkMath.Analysis.DkReal.Equiv
-  vanishing interval separation, representation setoid, and additive
-  congruence
+  vanishing interval separation, representation setoid, endpoint convergence,
+  and additive/nonnegative multiplicative congruence
 
 DkMath.Analysis.DkReal
   public entry point for the computable approximation layer
diff --git a/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md b/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
index c73af8e1..b3c14dd6 100644
--- a/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
+++ b/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
@@ -190,10 +190,28 @@ and symmetry follow from the corresponding finite-interval identities. The
 module therefore supplies a proved `Setoid`, not merely a candidate relation.
 
 Addition respects this equivalence because separation of interval sums is
-bounded by the sum of the input separations. Nonnegative multiplication
-congruence remains the next arithmetic obligation; it requires a bounded
-endpoint estimate analogous to the width argument already used to construct
-`mulNonneg`.
+bounded by the sum of the input separations. Nonnegative multiplication now
+also respects equivalence. The proof first derives
+
+```text
+Equiv(x,y) -> lo(x_n) - lo(y_n) -> 0.
+```
+
+The difference between product lower endpoints is then factored as
+
+```text
+a_n b_n - c_n d_n
+  = a_n (b_n-d_n) + d_n (a_n-c_n).
+```
+
+The endpoint factors are bounded and the difference factors tend to zero.
+Finally, interval separation is bounded by the absolute difference between
+the product lower endpoints. This gives `equiv_mulNonneg` and its one-sided
+variants without evaluating either representation as a Mathlib real number.
+
+The next arithmetic congruence target is `powNonneg`. It should follow from
+the same endpoint-convergence principle together with a uniform bound for the
+finite `gapGN` correction factor.
 
 Persistent intersection and equality after a future evaluation into Mathlib's
 `Real` remain comparison principles. Their equivalence with vanishing
````
`````
