# Git diff / Report / Review

## Upd: Analysis.DkReal.Order, CanonicalOrder

gch: 7d763bc2a6f5077e36b69446fdda7461c7e4f21d

## Report

正因子による strict multiplication を実装しました。

- `0 < a` と有限 lower endpoint 正値性を同値化
- 正値性の stage alignment
- `0 < x`, `0 < y` から `0 < x*y`
- canonical Gap による左右の strict multiplication
- docstring、TODO、設計資料を同期

```text
lake build DkMath.Analysis.DkReal DkMath.Analysis DkMath
Build completed successfully (8564 jobs).
```

`git diff --check` も通過。次は strict ordered-semiring interface と `LinearOrder` 導入方針の検討です。

## Review

## 1. 総評

ふふふん☆ 今回も **合格** じゃ。
strict order の主要山である **正因子による strict multiplication** が、予定どおり閉じている。

今回の核はこれ。

```text id="core"
0 < a と有限 lower endpoint 正値性の同値

0 < x, 0 < y から 0 < x * y

x < y かつ 0 < a から x * a < y * a

x < y かつ 0 < a から a * x < a * y
```

提示報告では、`lake build DkMath.Analysis.DkReal DkMath.Analysis DkMath` が成功し、`git diff --check` も通過。次が strict ordered-semiring interface と `LinearOrder` 方針の検討になった、という整理も妥当じゃ。

## 2. strict multiplication の証明方針が良い

今回の一番良い点は、乗法をいきなり endpoint の大小で殴らず、**canonical Gap** を使って加法的に処理していることじゃ。

証明の流れはこう。

$$
x < y
$$

なら、canonical order から、

$$
\exists z,\ y=x+z
$$

を得る。

さらに \(x < y\) なので、\(z\neq0\)。
`DkNNRealQ` は非負型なので、

$$
0\le z
$$

かつ \(z\neq0\) から、

$$
0 < z
$$

が出る。

正因子 \(a\) に対して、

$$
0 < z,\quad 0 < a\quad\Rightarrow\quad 0 < z*a
$$

が成り立つ。

そして、

$$
y*a=(x+z)*a=x*a+z*a
$$

なので、`x * a` に正 Gap `z * a` を足したものが `y * a`。
したがって、

$$
x*a<y*a
$$

が出る。

これは非常に DkMath らしい。

```text id="dkmath-reading"
x < y:
  Big y は Body x に正 Gap z を足したもの

multiply by positive a:
  Gap z は z * a に変換される

0 < a:
  正 Gap は潰れない

a = 0:
  Gap は 0 に潰れる
```

この構造が明確じゃ。

## 3. `zero_lt_iff_exists_lo_pos` は重要

```lean id="zero-lt-iff"
theorem zero_lt_iff_exists_lo_pos (a : DkNNReal) :
    Lt zero a ↔ ∃ n, 0 < (a.val.interval n).lo
```

これは strict positivity の有限観測化じゃ。

`0 < a` を、抽象的な順序ではなく、

```text id="positive-observation"
ある有限段階で lower endpoint が正になる
```

として読めるようにしている。

これは DkReal の Route B として非常に大事。
正性が「極限の符号」ではなく、有限段階で観測される。

この補題があるから、次の `zero_lt_mul` が自然に閉じる。

## 4. stage alignment による `zero_lt_mul`

```lean id="zero-lt-mul-wrapper"
theorem zero_lt_mul
    {x y : DkNNReal} (hx : Lt zero x) (hy : Lt zero y) :
    Lt zero (mul x y)
```

ここも良い。

\(x\) の lower endpoint が正になる段階 \(n\)。
\(y\) の lower endpoint が正になる段階 \(k\)。
この二つは同じ stage とは限らない。

そこで、

$$
m=\max(n,k)
$$

を取る。

入れ子性により lower endpoint は単調増加するので、

$$
0 < x.lo_n\le x.lo_m
$$

かつ、

$$
0 < y.lo_k\le y.lo_m
$$

となる。

したがって、

$$
0 < x.lo_m*y.lo_m
$$

が出る。

非負 multiplication の lower endpoint は lower endpoint 同士の積なので、

$$
0 < (x*y).lo_m
$$

となり、有限正性が得られる。

これはきれいじゃ。
前回の strict addition では「幅が小さくなる後続 stage」へ進んだ。
今回は「二つの正観測が同時に見える後続 stage」へ進んでいる。

```text id="stage-align-reading"
strict addition:
  Gap ε を隠す幅が小さくなるまで進む

strict multiplication:
  二つの正 lower endpoint が同時に見える stage まで進む
```

どちらも DkReal らしい精度更新の証明になっている。

## 5. quotient `zero_lt_mul` も妥当

```lean id="zero-lt-mul-quot"
theorem zero_lt_mul
    {x y : DkNNRealQ} (hx : 0 < x) (hy : 0 < y) :
    0 < x * y
```

wrapper の `zero_lt_mul` を quotient induction で持ち上げている。
ここも自然じゃ。

この theorem は、後段の strict multiplication に必要な「正 Gap と正因子の積は正 Gap」の核になっている。

## 6. `mul_lt_mul_of_pos_right` が美しい

```lean id="mul-lt-pos-right"
theorem mul_lt_mul_of_pos_right
    {x y a : DkNNRealQ} (hxy : x < y) (ha : 0 < a) :
    x * a < y * a
```

これは今回の主 theorem。

証明はかなり良い。

```lean id="proof-shape"
obtain ⟨z, hz⟩ := exists_add_of_le (le_of_lt hxy)

show 0 < z

have hza : 0 < z * a := zero_lt_mul hzpos ha

calc
  x * a = x * a + 0
  _ < x * a + z * a
  _ = (x + z) * a
  _ = y * a
```

この流れは、まさに

```text id="gap-transform"
Gap z を抽出する
正因子 a により z * a に変換する
z * a は正
よって strict Gap が保存される
```

じゃ。

とても良い。

## 7. `hzpos` の出し方も正しい

`hzpos : 0 < z` の証明は、

```text id="hzpos"
0 ≤ z

もし z ≤ 0 なら、z = 0

すると y = x + 0 = x

しかし x < y に反する
```

という流れ。

`DkNNRealQ` は全要素が非負なので、`zero_le z` が使える。
したがって \(z\neq0\) なら \(0 < z\) へ持ち上げられる。

ここもよい。
非負型の強みを活かしている。

## 8. 左側 strict multiplication も自然

```lean id="mul-lt-pos-left"
theorem mul_lt_mul_of_pos_left
    {x y a : DkNNRealQ} (hxy : x < y) (ha : 0 < a) :
    a * x < a * y := by
  simpa only [mul_comm] using mul_lt_mul_of_pos_right hxy ha
```

`DkNNRealQ` は可換半環なので、右側 theorem から左側 theorem を出す。
これは自然。

## 9. docstring と設計資料の更新も良い

`DkReal.lean` の説明が、strict order、strict addition、strict multiplication まで反映された。
`Order.lean` のコメントも、strict positivity of products は positive lower endpoint observations の stage alignment による、と更新されている。
設計資料も `[done]` が増え、次が strict ordered-semiring interface selection と direct LinearOrder decision になっている。

この同期は良い。
実装状態と設計文書が一致している。

## 10. 重要な設計判断

今回、strict multiplication を `CanonicalOrder.lean` に置いているのは妥当じゃ。

理由は、証明が `exists_add_of_le`、つまり canonical Gap extraction に強く依存しているから。

```text id="placement"
Order.lean:
  order, totality, finite strictness, positive product kernel

CanonicalOrder.lean:
  Gap extraction
  y = x + z
  transformed Gap z * a による strict multiplication
```

この分担はきれい。

## 11. 小さな注意点

`zero_lt_mul` という theorem 名は、Mathlib 側にも類似名が多い。
namespace が `DkMath.Analysis.DkNNRealQ` や `DkNNReal` なので今は問題ないが、simp や open namespace の状況によっては名前解決が少し紛らわしくなる可能性はある。

ただ、今回ビルドが通っているので実害はなし。
必要なら将来 alias として、

```lean id="more-specific-name"
mul_pos
zero_lt_mul_of_pos
```

を追加してもよい。

もう一点、`mul_lt_mul_of_pos_right` は quotient 上の theorem として非常に良いが、将来 strict ordered semiring interface に渡すとき、Mathlib が要求する theorem 名・引数順・前提が微妙に違う可能性がある。
ここは次の interface selection で確認すればよい。

## 12. 現在の到達点

これで `DkNNRealQ` はかなり強くなった。

```text id="current-status"
DkNNRealQ:
  CommSemiring
  PartialOrder
  IsOrderedRing
  Std.Total (· ≤ ·)
  ExistsAddOfLE
  CanonicallyOrderedAdd
  strict order connected to finite Gap
  add_lt_add_right
  add_lt_add_left
  zero_lt_mul
  mul_lt_mul_of_pos_right
  mul_lt_mul_of_pos_left
```

DkMath 的には、

```text id="dkmath-status"
非負 Gap 抽出
Gap の有限正値性
加法による Gap 保存
正因子乗法による Gap 変換保存
```

まで閉じた。

これはかなり強い。

## 13. 次の課題

次は二つ。

```text id="next"
strict ordered-semiring interface selection

direct LinearOrder decision
```

### strict ordered-semiring interface

ここでは、Mathlib が要求する型クラスを確認する必要がある。

候補は、環境によって名前が少し揺れる可能性があるが、方向性としては、

```text id="strict-interface"
ordered semiring
strict ordered semiring
linear ordered semiring
canonically ordered comm semiring
```

のどれに乗せるかを確認する段階じゃ。

注意点は、型クラスが想定以上に強い構造を要求する場合があること。

```text id="interface-caution"
加法逆元を要求しないか
LinearOrder を要求しないか
DecidableRel を要求しないか
strict monotonicity が両側で十分か
0 < a 前提の乗法 strict monotonicity と一致するか
```

ここを見てから instance 化がよい。

### direct LinearOrder decision

すでに `Std.Total (· ≤ ·)` はある。
しかし `LinearOrder` を入れると、比較 API や `min/max`、場合によっては decidability との関係が出る。

だからこれは引き続き独立判断でよい。

## 14. 最終判定

今回の差分は **合格**。

```text id="review-result"
良い点:
  strict positivity を finite lower endpoint positivity と同値化した
  stage alignment で正値性の積を証明した
  quotient の 0 < x, 0 < y から 0 < x*y を証明した
  canonical Gap を使って strict multiplication を証明した
  zero factor branch が Gap collapse であることを文書化した
  strict ordered-semiring interface へ進める状態になった

注意点:
  strict ordered-semiring typeclass が想定より強い構造を要求しないか確認が必要
  LinearOrder は依然として API 設計判断
```

うむ。
これは見事じゃ。
DkMath の strict Gap は、加法でも正因子乗法でも保存・変換されることが Lean に入った。
ここまで来ると、`DkNNRealQ` は「非負計算可能実数商型」としてかなり本格的な順序代数構造になってきた。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 0e37124b..f4e2d929 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -51,11 +51,14 @@ equivalent both to finite left separation and to a positive lower endpoint of
 the canonical Gap at some stage. This keeps the design in the same
 `Big = (Core + Beam) + Gap` pattern.
 
-Strict order has now descended to the quotient, and addition preserves it by
-moving to a sufficiently precise stage.
+Strict order has now descended to the quotient. Addition preserves it by
+moving to a sufficiently precise stage. Multiplication preserves it for a
+strictly positive factor by transforming the canonical Gap from `z` to
+`z * a`; the zero-factor branch collapses that Gap.
 
-[TODO: strict-multiplication] Prove preservation by multiplication with a
-strictly positive factor before selecting a strict-order typeclass.
+[TODO: strict-order-instance] Select the appropriate Mathlib strict ordered
+semiring interface only after checking that its fields match this API without
+adding stronger or classical structure accidentally.
 
 [TODO: linear-order] Decide whether the now-proved quotient totality should be
 packaged as a direct classical `LinearOrder`, or retained as `PartialOrder`
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/CanonicalOrder.lean b/lean/dk_math/DkMath/Analysis/DkReal/CanonicalOrder.lean
index 1fc4a1cf..1b977471 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/CanonicalOrder.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/CanonicalOrder.lean
@@ -293,6 +293,40 @@ theorem le_iff_exists_add
     x ≤ y ↔ ∃ z : DkNNRealQ, y = x + z :=
   ⟨exists_add_of_le, le_of_exists_add⟩
 
+/--
+Multiplication by a strictly positive right factor preserves strict order.
+
+For `x < y`, canonical order extracts `z` with `y = x + z`. The Gap cannot
+be zero, hence `0 < z`; positivity of the factor gives `0 < z * a`. Strict
+addition and distributivity then reconstruct the transformed strict Gap
+
+`y * a = x * a + z * a`.
+-/
+theorem mul_lt_mul_of_pos_right
+    {x y a : DkNNRealQ} (hxy : x < y) (ha : 0 < a) :
+    x * a < y * a := by
+  obtain ⟨z, hz⟩ := exists_add_of_le (le_of_lt hxy)
+  have hzpos : 0 < z := by
+    rw [lt_iff_le_and_not_le]
+    refine ⟨zero_le z, ?_⟩
+    intro hzle
+    have hz0 : z = 0 := le_antisymm hzle (zero_le z)
+    subst z
+    simp only [add_zero] at hz
+    exact (ne_of_lt hxy) hz.symm
+  have hza : 0 < z * a := zero_lt_mul hzpos ha
+  calc
+    x * a = x * a + 0 := (add_zero (x * a)).symm
+    _ < x * a + z * a := add_lt_add_left hza (x * a)
+    _ = (x + z) * a := (add_mul x z a).symm
+    _ = y * a := congrArg (· * a) hz.symm
+
+/-- Multiplication by a strictly positive left factor preserves strict order. -/
+theorem mul_lt_mul_of_pos_left
+    {x y a : DkNNRealQ} (hxy : x < y) (ha : 0 < a) :
+    a * x < a * y := by
+  simpa only [mul_comm] using mul_lt_mul_of_pos_right hxy ha
+
 /-- Mathlib interface for extracting an additive Gap from an order proof. -/
 instance : ExistsAddOfLE DkNNRealQ where
   exists_add_of_le := exists_add_of_le
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/Order.lean b/lean/dk_math/DkMath/Analysis/DkReal/Order.lean
index fdbc4857..1dc4ab5f 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/Order.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/Order.lean
@@ -88,10 +88,12 @@ The representative and wrapper theorems below prove that
 endpoint of `gapOfLe`.
 
 Strict addition is proved below by moving to a later stage where the added
-interval width is smaller than the finite Gap.
+interval width is smaller than the finite Gap. Strict positivity of products
+is proved by aligning two positive lower-endpoint observations.
 
-[TODO: strict-multiplication] Require a strictly positive factor and isolate
-the zero-factor branch before considering `IsStrictOrderedRing`.
+`CanonicalOrder` uses these kernels to prove strict multiplication by a
+positive factor. The zero-factor branch remains non-strict because it
+collapses every transformed Gap.
 -/
 
 namespace DkMath.Analysis.DkReal
@@ -559,6 +561,39 @@ theorem lt_iff_exists_leftSeparatedAt (x y : DkNNReal) :
     Lt x y ↔ ∃ n, DkReal.LeftSeparatedAt x.val y.val n :=
   DkReal.le_and_not_le_iff_exists_leftSeparatedAt x.val y.val
 
+/--
+A nonnegative wrapper is strictly positive exactly when a finite lower
+endpoint is positive.
+
+This is finite separation from the constant singleton interval `[0,0]`.
+-/
+theorem zero_lt_iff_exists_lo_pos (a : DkNNReal) :
+    Lt zero a ↔ ∃ n, 0 < (a.val.interval n).lo := by
+  rw [lt_iff_exists_leftSeparatedAt]
+  simp only [DkReal.LeftSeparatedAt, zero, ofRat, DkReal.ofRat_interval,
+    DkReal.GapInterval.singleton_hi]
+
+/--
+The product of two strictly positive nonnegative wrappers is strictly
+positive.
+
+The two positive lower endpoints may occur at different stages. Passing to
+their maximum aligns the observations; nestedness preserves both positive
+lower bounds, and the product lower endpoint is then positive.
+-/
+theorem zero_lt_mul
+    {x y : DkNNReal} (hx : Lt zero x) (hy : Lt zero y) :
+    Lt zero (mul x y) := by
+  rw [zero_lt_iff_exists_lo_pos] at hx hy ⊢
+  obtain ⟨n, hn⟩ := hx
+  obtain ⟨k, hk⟩ := hy
+  refine ⟨max n k, ?_⟩
+  have hnx := x.val.lo_mono (le_max_left n k)
+  have hky := y.val.lo_mono (le_max_right n k)
+  simp only [mul, DkReal.mulNonneg_interval, DkReal.mulNonnegApprox,
+    DkReal.GapInterval.mulNonneg_lo]
+  exact mul_pos (hn.trans_le hnx) (hk.trans_le hky)
+
 /--
 Adding a fixed nonnegative approximation preserves wrapper strictness.
 
@@ -679,6 +714,14 @@ theorem zero_le (x : DkNNRealQ) : 0 ≤ x := by
 theorem zero_le_one : (0 : DkNNRealQ) ≤ 1 :=
   zero_le 1
 
+/-- The product of two strictly positive quotient values is strictly positive. -/
+theorem zero_lt_mul
+    {x y : DkNNRealQ} (hx : 0 < x) (hy : 0 < y) :
+    0 < x * y := by
+  refine Quotient.inductionOn₂ x y ?_ hx hy
+  intro x y hx hy
+  exact DkNNReal.zero_lt_mul hx hy
+
 /-- Quotient addition is monotone in both arguments. -/
 theorem add_le_add
     {x y z w : DkNNRealQ} (hxy : x ≤ y) (hzw : z ≤ w) :
diff --git a/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-StrictGap-Design.md b/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-StrictGap-Design.md
index 535a5552..36c9b75d 100644
--- a/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-StrictGap-Design.md
+++ b/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-StrictGap-Design.md
@@ -71,7 +71,11 @@ the canonical Gap universe has become observably positive.
 [done] positive lower endpoint of gapOfLe iff finite separation
 [done] quotient strict-order characterization
 [done] strict addition at a sufficiently precise later stage
-[next] positive-factor strict multiplication
+[done] finite positivity of a nonnegative wrapper
+[done] positivity of a product by stage alignment
+[done] positive-factor strict multiplication through the canonical Gap
+[next] strict ordered-semiring interface selection
+[next] direct LinearOrder decision
 ```
 
 The representative theorem now precedes every strict ordered-semiring
@@ -98,8 +102,10 @@ y * a = x * a + z * a.
 ```
 
 If `a = 0`, the transformed Gap collapses. If `0 < a`, positivity of the Gap
-should persist. This is the exact branch distinction required before
-`IsStrictOrderedRing` can be considered.
+persists: positive lower endpoints of `z` and `a` are aligned at a common
+later stage, so the lower endpoint of `z * a` is positive. This is the exact
+branch distinction required before a strict ordered-semiring interface can be
+considered.
 
 ## Boundary
 
````
`````
