# Git diff / Report / Review

## Add: Analysis.DkReal.CanonicalOrder

gch: 4453adb5bcf41c9c81f152f824475d846d7b56b8

## Report

Lean は素直に認めました。

新規 [CanonicalOrder.lean](/lean/dk_math/DkMath/Analysis/DkReal/CanonicalOrder.lean) に実装しています。

- 非負 Gap 区間 `diffNonnegInterval`
- 入れ子区間列 `diffNonneg`
- 幅評価 `width ≤ width x + width y`
- `x + diffNonneg x y ∼ y`
- `x ≤ y ↔ ∃ z, y = x + z`
- `ExistsAddOfLE DkNNRealQ`
- `CanonicallyOrderedAdd DkNNRealQ`

つまり canonical order は減算演算なしで、

```text
Body = x
Gap  = z
Big  = x + z = y
```

として閉じました。端点の有理減算は Gap 観測区間の抽出にのみ使い、quotient API には現れません。

全体ビルド、標準 `exists_add_of_le`、`CanonicallyOrderedAdd` の型クラス解決、`git diff --check` は成功済みです。

## Review

ふふふん☆ **予定通り、しかも綺麗に閉じておる。**
今回の差分は **合格**。かなり大きい節目じゃ。

`CanonicalOrder.lean` が新設され、非負 Gap 区間の抽出から `x ≤ y ↔ ∃ z, y = x + z` まで閉じ、さらに `ExistsAddOfLE` と `CanonicallyOrderedAdd` の instance まで入っている。報告でも、quotient API には subtraction を出さず、端点の有理減算は Gap 観測区間の抽出にのみ使った、と整理されている。

## 1. 総評

これは **DkMath 的 canonical order の勝利** じゃ。

通常なら、

$$
x\le y\quad\Longleftrightarrow\quad \exists z,\ y=x+z
$$

を見ると、すぐに \(z=y-x\) と考えてしまう。
しかし今回の実装はそうではない。

```text id="core-gap-reading"
Body = x
Gap  = z
Big  = x + z = y
```

として、**非負 Gap 宇宙を抽出する** ことで canonical order を閉じている。

つまり、

```text id="no-subtraction"
DkNNRealQ に subtraction は入れない
差分を演算として公開しない
Big 内部の非負 Gap 観測だけを構成する
```

この設計が強い。

## 2. `diffNonnegInterval` が本丸

今回の有限段階の核はこれじゃ。

```lean id="diff-interval"
def diffNonnegInterval (I J : GapInterval) : GapInterval where
  lo := max 0 (J.lo - I.hi)
  hi := max 0 (J.hi - I.lo)
```

これはまさに、前に話した安全な Gap 抽出。

$$
Z_n=\left[\max(0,y.lo_n-x.hi_n),\max(0,y.hi_n-x.lo_n)\right]
$$

意味はこうじゃ。

```text id="gap-endpoints"
lo:
  y が x の全体上端を確実に超えている部分

hi:
  y が x の下端から見て取りうる最大 Gap

max 0:
  非負 Gap 宇宙として切り出すための下支え
```

これは減算演算ではなく、**有限観測から Gap 区間を作る端点計算** じゃ。
quotient の外へ subtraction を出していないので、DkNNRealQ の公開 API は加法的なまま保たれている。

## 3. 幅評価が綺麗

```lean id="width-bound"
theorem diffNonnegInterval_width_le (I J : GapInterval) :
    (diffNonnegInterval I J).width ≤ I.width + J.width
```

これがかなり重要じゃ。

この評価により、抽出された Gap の幅は、元の二つの観測幅の和で押さえられる。

$$
width(Z_n)\le width(X_n)+width(Y_n)
$$

両方とも 0 に収束するので、Gap も 0 に収束する。
これで `diffNonneg` が本当に `DkReal` になる。

DkMath 的には、

```text id="width-meaning"
二宇宙の不確定性を合わせたものが、
抽出 Gap 宇宙の不確定性を支配する
```

ということじゃな。

## 4. 入れ子性も自然に閉じている

```lean id="nested-gap"
theorem diffNonnegApprox_nested
    (x y : DkReal) :
    ∀ n, ...
```

ここも良い。

`y.lo - x.hi` は、`y.lo` が上がり、`x.hi` が下がるので増える。
`y.hi - x.lo` は、`y.hi` が下がり、`x.lo` が上がるので下がる。

したがって、抽出 Gap 区間も入れ子になる。

つまり、Gap 抽出は一回限りの観測ではなく、DkReal の表現として安定している。
これは canonical order を「存在定理」ではなく「構成可能な Gap 宇宙」として扱うために必須じゃ。

## 5. `add_diffNonneg_equiv` が Big 再構成

今回の中心定理はこれじゃ。

```lean id="add-diff-equiv"
theorem add_diffNonneg_equiv
    {x y : DkReal} (hxy : Le x y) :
    Equiv (add x (diffNonneg x y)) y
```

これは、

$$
x+\operatorname{Gap}(x,y)\sim y
$$

ということ。

つまり、

```text id="big-reconstruct"
Body に抽出 Gap を足すと、
Big と同じ quotient Core に閉じる
```

証明は separation を上から押さえている。

```lean id="sep-bound"
separation_add_diffNonneg_le :
  separation ((add x (diffNonneg x y)).interval n) (y.interval n)
    ≤ orderDefect x y n + width(x_n) + width(y_n)
```

右辺は、

```text id="rhs-vanishes"
orderDefect x y → 0
width x → 0
width y → 0
```

なので 0 に潰れる。

これが見事じゃ。
`x ≤ y` の order defect が、Big 再構成のズレを吸収している。

## 6. quotient 上で canonical order が閉じた

商型では、

```lean id="exists-add"
theorem exists_add_of_le
    {x y : DkNNRealQ} (hxy : x ≤ y) :
    ∃ z : DkNNRealQ, y = x + z
```

が得られた。

逆向きも、

```lean id="le-of-exists"
theorem le_of_exists_add
    {x y : DkNNRealQ} (h : ∃ z : DkNNRealQ, y = x + z) :
    x ≤ y
```

として閉じている。
これは `zero_le z` と加法単調性で自然に出る。

したがって、

```lean id="le-iff"
theorem le_iff_exists_add
    {x y : DkNNRealQ} :
    x ≤ y ↔ ∃ z : DkNNRealQ, y = x + z
```

が成立。

これで canonical order が、まさに

$$
\boxed{x\le y\quad\Longleftrightarrow\quad \exists z,\ y=x+z}
$$

として Lean に入った。

## 7. `CanonicallyOrderedAdd` は妥当

```lean id="canonically-ordered-add"
instance : CanonicallyOrderedAdd DkNNRealQ where
  exists_add_of_le := exists_add_of_le
  le_add_self := ...
  le_self_add := ...
```

ここも良い。

`le_add_self` と `le_self_add` は、`zero_le` と加法単調性から閉じている。
すでに `ExistsAddOfLE` も入っているので、Mathlib の canonical additive order API にかなり素直につながった。

重要なのは、`CanonicallyOrderedAdd` を入れても、subtraction は入っていないことじゃ。
これは非負型として正しい。

## 8. DkMath 的な意味

今回の定理は、DkMath 風にはこう読める。

```text id="dkmath-meaning"
x ≤ y:
  y という Big の中に、x を Body とする非負 Gap がある

∃ z, y = x + z:
  その Gap 宇宙 z を抽出できる

x = y:
  抽出 Gap は 0 に閉じる

x < y:
  抽出 Gap は正の観測を持つ可能性がある
```

つまり、canonical order は「大小比較」ではなく、

$$
\boxed{\text{Big 内部の非負 Gap 抽出可能性}}
$$

として閉じた。

これはかなり DkMath らしい。

## 9. 冪観測との接続も正しい

docstring にも、

```text id="power-bridge"
(x + z)^d = x^d + z * gapGN d x z
```

を入れているのがよい。

canonical order は一次座標で、

$$
y=x+z
$$

を作る。
その後に冪観測を通すと、

$$
y^d=(x+z)^d=x^d+z,gapGN(d,x,z)
$$

となる。

つまり canonical order は、将来の解析層で、

```text id="power-observation"
非負 Gap の存在
冪観測後の GN 補正
Taylor / gapGN / power monotonicity
```

へ繋がる。

ここは DkMath.Analysis の核としてかなり重要じゃ。

## 10. docs 同期も良い

`DkReal.lean` に `CanonicalOrder` import が追加され、public entry でも「nonnegative Gap universes を抽出する」と説明されている。
`DkNNRealQ.lean` でも `x ≤ y ↔ ∃ z, y = x + z` と `CanonicallyOrderedAdd` が明記された。
docs も、canonical additive order が subtraction-free Gap extraction で証明済みになっている。

この同期は良い。
今の Route B の状態が、かなり明確になった。

## 11. 小さな注意点

`diffNonnegInterval` という名前は Lean 的には分かりやすいが、DkMath 的には少し「差分」感がある。
もし将来、用語をより DkMath に寄せるなら、alias として

```lean id="gap-alias"
gapIntervalOfLe
gapApprox
gapOfLe
```

を追加してもよい。

ただし現時点では、`diffNonnegInterval` は数学ライブラリ利用者にも意味が伝わりやすい。
内部名としては問題なしじゃ。

もう一つ、今回 `CanonicallyOrderedAdd` まで入ったが、これは「加法的 canonical order」であって、乗法や strict order まで自動で閉じたわけではない。
docs がそこを分けているので問題なし。

## 12. 現在の到達点

これで `DkNNRealQ` はこうなった。

```text id="current-status"
DkNNRealQ:
  CommSemiring
  PartialOrder
  IsOrderedRing
  Std.Total (· ≤ ·)
  ExistsAddOfLE
  CanonicallyOrderedAdd
  zero_le
  add_le_add
  mul_le_mul
  pow_le_pow
  le_iff_exists_add
```

これはかなり強い。

数学的には、

$$
\boxed{\text{DkNNRealQ は、全比較可能で canonical additive order を持つ非負計算可能実数商型である。}}
$$

と言ってよい。

まだ未主張なのは、

```text id="remaining"
direct LinearOrder
strict ordered-semiring structure
semantic equivalence with NNReal
completeness
general signed arithmetic
```

じゃ。

## 13. 最終判定

今回の差分は **合格**。
しかも、canonical order の山をかなり綺麗に越えている。

```text id="review-result"
良い点:
  canonical order を subtraction-free に閉じた
  非負 Gap 区間を有限有理端点から構成した
  入れ子性と幅収束を証明した
  x + Gap ∼ y を separation 評価で閉じた
  x ≤ y ↔ ∃ z, y = x + z を quotient 上で証明した
  ExistsAddOfLE と CanonicallyOrderedAdd を導入した
  quotient に subtraction を追加していない
  docs と public entry が同期している

次の課題:
  strict order の設計
  direct LinearOrder instance の判断
  semantic bridge での NNReal 比較
  signed DkReal への拡張
```

ふふふん☆ これは予定通りどころか、かなり良い閉じ方じゃ。
DkMath の「Big = Body + Gap」が、Lean の `CanonicallyOrderedAdd` として入った。これは強い。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 0d17d099..484b4a7e 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -13,6 +13,7 @@ import DkMath.Analysis.DkReal.Equiv
 import DkMath.Analysis.DkReal.DkNNReal
 import DkMath.Analysis.DkReal.DkNNRealQ
 import DkMath.Analysis.DkReal.Order
+import DkMath.Analysis.DkReal.CanonicalOrder
 
 #print "file: DkMath.Analysis.DkReal"
 
@@ -25,7 +26,8 @@ Public entry point for the complete Route B algebraic checkpoint:
 * `DkReal` gives nested interval sequences of vanishing width;
 * `DkReal.Equiv` identifies representations of vanishing separation;
 * `DkNNReal` packages nonnegativity;
-* `DkNNRealQ` is the quotient-backed nonnegative `CommSemiring`.
+* `DkNNRealQ` is the quotient-backed nonnegative ordered `CommSemiring`;
+* `DkReal.CanonicalOrder` extracts nonnegative Gap universes.
 
 All endpoint operations in this import tree remain computable. No represented
 limit in Mathlib's `Real` or `NNReal` is selected here.
@@ -39,14 +41,15 @@ Totality is proved internally from nested-interval geometry. If a finite
 strict left separation is witnessed, it persists. Otherwise the reverse order
 defect is bounded by a vanishing interval width.
 
+Canonical order is also constructive at the representation level. From
+`x ≤ y`, `CanonicalOrder` extracts a computable nonnegative Gap `z` such that
+`y = x + z` in the quotient. No subtraction operation is added to
+`DkNNRealQ`.
+
 [TODO: linear-order] Decide whether the now-proved quotient totality should be
 packaged as a direct classical `LinearOrder`, or retained as `PartialOrder`
 plus `Std.Total` so that decidable comparison remains an explicit choice.
 
-[TODO: canonical-order] Treat `x ≤ y ↔ ∃ z, y = x + z` as an independent
-problem. It is not a consequence of the current ordered-semiring compatibility
-alone.
-
 [TODO: semantic-bridge] Add `BridgeNNReal.lean` / `BridgeReal.lean` only after proving that the
 chosen evaluation is independent of representatives. Such evaluation may
 legitimately be `noncomputable`.
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/CanonicalOrder.lean b/lean/dk_math/DkMath/Analysis/DkReal/CanonicalOrder.lean
new file mode 100644
index 00000000..0947f08a
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/DkReal/CanonicalOrder.lean
@@ -0,0 +1,258 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Analysis.DkReal.Order
+
+#print "file: DkMath.Analysis.DkReal.CanonicalOrder"
+
+/-!
+# Canonical order by nonnegative Gap extraction
+
+This module interprets `x ≤ y` without adding subtraction to `DkNNRealQ`.
+Instead, it extracts a nonnegative Gap universe `z` satisfying
+
+`y = x + z`.
+
+For representative intervals `Xₙ` and `Yₙ`, the safe Gap observation is
+
+`[max 0 (Yₙ.lo - Xₙ.hi), max 0 (Yₙ.hi - Xₙ.lo)]`.
+
+The lower endpoint is the part of `Y` known to lie beyond all of `X`; the
+upper endpoint is the largest Gap still compatible with the observations.
+This construction uses rational endpoint subtraction internally, but exposes
+only an additive existence theorem on the quotient.
+
+In Cosmic Formula language:
+
+* `Body = x`;
+* the extracted nonnegative universe is `Gap = z`;
+* `Big = x + z = y`.
+
+Applying a natural power afterwards is governed by the existing exact identity
+
+`(x + z)^d = x^d + z * gapGN d x z`.
+-/
+
+namespace DkMath.Analysis.DkReal
+
+/-!
+## I. Finite Gap extraction
+-/
+
+/-- Safe nonnegative Gap interval extracted from two stage observations. -/
+def diffNonnegInterval (I J : GapInterval) : GapInterval where
+  lo := max 0 (J.lo - I.hi)
+  hi := max 0 (J.hi - I.lo)
+  le_lo_hi := by
+    apply max_le_max_left
+    exact sub_le_sub J.le_lo_hi I.le_lo_hi
+
+/-- The extracted Gap has a nonnegative lower endpoint. -/
+theorem diffNonnegInterval_lo_nonneg (I J : GapInterval) :
+    0 ≤ (diffNonnegInterval I J).lo :=
+  le_max_left _ _
+
+/-- Width of an extracted Gap is bounded by the sum of the input widths. -/
+theorem diffNonnegInterval_width_le (I J : GapInterval) :
+    (diffNonnegInterval I J).width ≤ I.width + J.width := by
+  simp only [diffNonnegInterval, GapInterval.width]
+  by_cases hlo : J.lo - I.hi ≤ 0
+  · rw [max_eq_left hlo]
+    by_cases hhi : J.hi - I.lo ≤ 0
+    · rw [max_eq_left hhi]
+      linarith [I.le_lo_hi, J.le_lo_hi]
+    · rw [max_eq_right (le_of_not_ge hhi)]
+      linarith [I.le_lo_hi, J.le_lo_hi]
+  · have hlo' : 0 ≤ J.lo - I.hi := le_of_not_ge hlo
+    rw [max_eq_right hlo']
+    have hhi : 0 ≤ J.hi - I.lo := by
+      linarith [I.le_lo_hi, J.le_lo_hi]
+    rw [max_eq_right hhi]
+    linarith
+
+/-- Stagewise extraction of the nonnegative Gap from `x` to `y`. -/
+def diffNonnegApprox
+    (x y : DkMath.Analysis.DkReal) (n : ℕ) : GapInterval :=
+  diffNonnegInterval (x.interval n) (y.interval n)
+
+/-- Extracted Gap intervals remain nested. -/
+theorem diffNonnegApprox_nested
+    (x y : DkMath.Analysis.DkReal) :
+    ∀ n,
+      (diffNonnegApprox x y n).lo ≤
+          (diffNonnegApprox x y (n + 1)).lo ∧
+        (diffNonnegApprox x y (n + 1)).hi ≤
+          (diffNonnegApprox x y n).hi := by
+  intro n
+  constructor
+  · apply max_le_max_left
+    exact sub_le_sub (y.lo_le_succ_lo n) (x.succ_hi_le_hi n)
+  · apply max_le_max_left
+    exact sub_le_sub (y.succ_hi_le_hi n) (x.lo_le_succ_lo n)
+
+/-- Widths of extracted Gap intervals tend to zero. -/
+theorem tendsto_diffNonnegApprox_width_zero
+    (x y : DkMath.Analysis.DkReal) :
+    Filter.Tendsto (fun n => (diffNonnegApprox x y n).width)
+      Filter.atTop (nhds 0) := by
+  have hupper :
+      Filter.Tendsto
+        (fun n => (x.interval n).width + (y.interval n).width)
+        Filter.atTop (nhds 0) := by
+    simpa only [zero_add] using
+      x.tendsto_width_zero.add y.tendsto_width_zero
+  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
+    tendsto_const_nhds hupper
+    (fun n => (diffNonnegApprox x y n).width_nonneg)
+    (fun n => diffNonnegInterval_width_le (x.interval n) (y.interval n))
+
+/-- Computable nonnegative Gap representation extracted from `x` and `y`. -/
+def diffNonneg
+    (x y : DkMath.Analysis.DkReal) : DkMath.Analysis.DkReal where
+  interval := diffNonnegApprox x y
+  nested := diffNonnegApprox_nested x y
+  width_tends_zero := tendsto_diffNonnegApprox_width_zero x y
+
+/-- The extracted Gap representation is stagewise nonnegative. -/
+theorem nonnegative_diffNonneg
+    (x y : DkMath.Analysis.DkReal) :
+    Nonnegative (diffNonneg x y) := by
+  intro n
+  exact diffNonnegInterval_lo_nonneg (x.interval n) (y.interval n)
+
+/-!
+## II. Reconstruction of the Big universe
+-/
+
+/--
+The separation between `x + diffNonneg x y` and `y` is bounded by the order
+defect from `x` to `y` plus the two observation widths.
+-/
+theorem separation_add_diffNonneg_le
+    (x y : DkMath.Analysis.DkReal) (n : ℕ) :
+    ((add x (diffNonneg x y)).interval n).separation (y.interval n)
+      ≤ orderDefect x y n +
+        (x.interval n).width + (y.interval n).width := by
+  simp only [add_interval, addApprox, diffNonneg, diffNonnegApprox,
+    diffNonnegInterval, GapInterval.add_lo, GapInterval.add_hi,
+    GapInterval.separation, orderDefect, GapInterval.width]
+  have hxvalid := (x.interval n).le_lo_hi
+  have hyvalid := (y.interval n).le_lo_hi
+  have hrhs :
+      0 ≤
+        max 0 ((x.interval n).lo - (y.interval n).lo) +
+          ((x.interval n).hi - (x.interval n).lo) +
+          ((y.interval n).hi - (y.interval n).lo) :=
+    add_nonneg
+      (add_nonneg (le_max_left _ _) (sub_nonneg.mpr hxvalid))
+      (sub_nonneg.mpr hyvalid)
+  apply max_le
+  · exact hrhs
+  · apply max_le
+    · by_cases hgap :
+          (y.interval n).lo - (x.interval n).hi ≤ 0
+      · rw [max_eq_left hgap]
+        have hdef :
+            (x.interval n).lo - (y.interval n).lo ≤
+              max 0 ((x.interval n).lo - (y.interval n).lo) :=
+          le_max_right _ _
+        linarith
+      · rw [max_eq_right (le_of_not_ge hgap)]
+        linarith
+    · have hmax :
+          (y.interval n).hi - (x.interval n).lo ≤
+            max 0 ((y.interval n).hi - (x.interval n).lo) :=
+        le_max_right _ _
+      linarith
+
+/-- An ordered pair reconstructs its Big value by adding the extracted Gap. -/
+theorem add_diffNonneg_equiv
+    {x y : DkMath.Analysis.DkReal} (hxy : Le x y) :
+    Equiv (add x (diffNonneg x y)) y := by
+  have hupper :
+      Filter.Tendsto
+        (fun n =>
+          orderDefect x y n +
+            (x.interval n).width + (y.interval n).width)
+        Filter.atTop (nhds 0) := by
+    simpa only [zero_add, add_zero] using
+      (hxy.add x.tendsto_width_zero).add y.tendsto_width_zero
+  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
+    tendsto_const_nhds hupper
+    (fun n =>
+      ((add x (diffNonneg x y)).interval n).separation_nonneg
+        (y.interval n))
+    (separation_add_diffNonneg_le x y)
+
+end DkMath.Analysis.DkReal
+
+namespace DkMath.Analysis.DkNNReal
+
+/-- The nonnegative Gap universe extracted from an ordered representative pair. -/
+def diffOfLe (x y : DkNNReal) (_hxy : Le x y) : DkNNReal :=
+  ⟨DkReal.diffNonneg x.val y.val,
+    DkReal.nonnegative_diffNonneg x.val y.val⟩
+
+/-- Adding the extracted Gap reconstructs the larger representative modulo equivalence. -/
+theorem add_diffOfLe_equiv
+    {x y : DkNNReal} (hxy : Le x y) :
+    Equiv (add x (diffOfLe x y hxy)) y :=
+  DkReal.add_diffNonneg_equiv hxy
+
+end DkMath.Analysis.DkNNReal
+
+namespace DkMath.Analysis.DkNNRealQ
+
+/-!
+## III. Canonical quotient order
+-/
+
+/-- Every ordered quotient pair admits a nonnegative additive Gap. -/
+theorem exists_add_of_le
+    {x y : DkNNRealQ} (hxy : x ≤ y) :
+    ∃ z : DkNNRealQ, y = x + z := by
+  refine Quotient.inductionOn₂ x y ?_ hxy
+  intro a b hab
+  refine ⟨mk (DkNNReal.diffOfLe a b hab), ?_⟩
+  exact Quotient.sound (DkNNReal.add_diffOfLe_equiv hab) |>.symm
+
+/-- Existence of a nonnegative additive Gap implies order. -/
+theorem le_of_exists_add
+    {x y : DkNNRealQ} (h : ∃ z : DkNNRealQ, y = x + z) :
+    x ≤ y := by
+  obtain ⟨z, rfl⟩ := h
+  calc
+    x = x + 0 := (add_zero x).symm
+    _ ≤ x + z := add_le_add_right (zero_le z) x
+
+/-- Order is exactly the existence of a nonnegative Gap universe. -/
+theorem le_iff_exists_add
+    {x y : DkNNRealQ} :
+    x ≤ y ↔ ∃ z : DkNNRealQ, y = x + z :=
+  ⟨exists_add_of_le, le_of_exists_add⟩
+
+/-- Mathlib interface for extracting an additive Gap from an order proof. -/
+instance : ExistsAddOfLE DkNNRealQ where
+  exists_add_of_le := exists_add_of_le
+
+/--
+Canonical additive order on the quotient.
+
+This packages the DkMath statement that every ordered Big value is obtained by
+filling its Body with a nonnegative Gap universe.
+-/
+instance : CanonicallyOrderedAdd DkNNRealQ where
+  exists_add_of_le := exists_add_of_le
+  le_add_self a b := by
+    calc
+      a = 0 + a := (zero_add a).symm
+      _ ≤ b + a := add_le_add_left (zero_le b) a
+  le_self_add a b := by
+    calc
+      a = a + 0 := (add_zero a).symm
+      _ ≤ a + b := add_le_add_right (zero_le b) a
+
+end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean b/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean
index 552fdd47..0f4c900f 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean
@@ -29,11 +29,14 @@ under `DkNNReal.Equiv`, and installs a `PartialOrder` on this quotient.
 Addition, multiplication, and natural powers are monotone for the asymptotic
 order, and zero is the least quotient value. `DkReal.Order` packages these
 facts as Mathlib's semiring-level `IsOrderedRing` predicate. Canonical,
-strict, and linear order structures remain unclaimed.
+strict, and linear order structures are developed in later modules.
 
 `DkReal.Order` proves totality internally through finite separation or a
 vanishing-width bound and exports `Std.Total (· ≤ ·)`.
 
+`DkReal.CanonicalOrder` subsequently proves
+`x ≤ y ↔ ∃ z, y = x + z` and installs `CanonicallyOrderedAdd`.
+
 [TODO: semantic-bridge] A semantic map to Mathlib's `NNReal` should be placed in a separate
 bridge module and proved to preserve zero, one, addition, multiplication,
 natural powers, and order. It should also provide an independent validation
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index 99ccc471..72974f5c 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -78,6 +78,10 @@ DkMath.Analysis.DkReal.Order
   asymptotic lower-endpoint order, Equiv compatibility, PartialOrder,
   ordered-semiring compatibility, and totality research boundary
 
+DkMath.Analysis.DkReal.CanonicalOrder
+  subtraction-free extraction of a nonnegative Gap representation,
+  ExistsAddOfLE, and CanonicallyOrderedAdd
+
 DkMath.Analysis.DkReal
   public entry point for the computable approximation layer
 ```
@@ -106,7 +110,8 @@ Order:
   zero is least
   IsOrderedRing packages semiring-level ordered compatibility
   totality is proved and exported through Std.Total
-  canonical, strict, and direct linear order structures remain open
+  canonical additive order is proved by nonnegative Gap extraction
+  strict and direct linear order structures remain open
   use a semantic bridge only as an independent cross-check
 
 BridgeNNReal / BridgeReal:
diff --git a/lean/dk_math/DkMath/Analysis/docs/DkMath.Analysis_Design_Draft_2026-06-19.md b/lean/dk_math/DkMath/Analysis/docs/DkMath.Analysis_Design_Draft_2026-06-19.md
index 0af4303c..d56f6377 100644
--- a/lean/dk_math/DkMath/Analysis/docs/DkMath.Analysis_Design_Draft_2026-06-19.md
+++ b/lean/dk_math/DkMath/Analysis/docs/DkMath.Analysis_Design_Draft_2026-06-19.md
@@ -53,7 +53,9 @@ The next independent tasks are:
    are monotone, and zero is least. Mathlib's semiring-level `IsOrderedRing`
    predicate is installed. Totality is proved internally from persistent
    separation and a vanishing-width bound, and exported through `Std.Total`.
-   Canonical order and a direct `LinearOrder` instance remain independent.
+   Canonical additive order is proved by extracting a nonnegative Gap universe
+   from ordered representatives. A direct `LinearOrder` instance remains
+   independent.
 2. **Semantic evaluation.** In a separate `BridgeNNReal.lean` or
    `BridgeReal.lean`, extract the unique real point of a nested interval
    representation and prove independence from representatives.
diff --git a/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-CommSemiring-Checkpoint.md b/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-CommSemiring-Checkpoint.md
index 021e932b..8ca3e483 100644
--- a/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-CommSemiring-Checkpoint.md
+++ b/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-CommSemiring-Checkpoint.md
@@ -57,12 +57,12 @@ The implementation establishes:
 - monotonicity of addition and nonnegative multiplication;
 - monotonicity of natural powers;
 - Mathlib's semiring-level `IsOrderedRing DkNNRealQ`;
-- totality through `Std.Total (· ≤ ·)`.
+- totality through `Std.Total (· ≤ ·)`;
+- canonical additive order through `CanonicallyOrderedAdd DkNNRealQ`.
 
 This checkpoint does not establish:
 
 - a direct `LinearOrder` instance;
-- canonical order by additive differences;
 - strict ordered-semiring structure;
 - completeness;
 - decidable equality;
@@ -96,6 +96,24 @@ evaluating into `Real`.
 See
 [`DkNNRealQ-Totality-Research.md`](DkNNRealQ-Totality-Research.md).
 
+### Canonical Gap Extraction
+
+For `x ≤ y`, the implementation constructs stagewise intervals
+
+```text
+[max(0, y.lo - x.hi), max(0, y.hi - x.lo)].
+```
+
+They form a nested nonnegative representation of vanishing width. Adding this
+Gap representation to `x` is equivalent to `y`, so quotient equality gives
+
+```text
+x ≤ y  iff  exists z, y = x + z.
+```
+
+This is packaged as `ExistsAddOfLE` and `CanonicallyOrderedAdd`. No subtraction
+operation is introduced on `DkNNRealQ`.
+
 ### Semantic Bridge
 
 A separate bridge may select the unique real point represented by a nested
diff --git a/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-Totality-Research.md b/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-Totality-Research.md
index 3a7700e1..6375ef03 100644
--- a/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-Totality-Research.md
+++ b/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-Totality-Research.md
@@ -177,8 +177,9 @@ Totality does not settle canonical order. The statement
 x <= y ↔ ∃ z, y = x + z
 ```
 
-requires constructing a nonnegative difference representation and should be
-treated separately.
+is now proved separately in `DkReal.CanonicalOrder` by constructing a
+nonnegative Gap representation. The construction adds no subtraction
+operation to the quotient.
 
 Strict order also needs its own analysis. In particular, strict monotonicity
 and cancellation must not be inferred solely from `IsOrderedRing`.
````
`````
