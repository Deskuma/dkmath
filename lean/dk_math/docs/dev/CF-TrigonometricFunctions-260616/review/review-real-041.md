# Git diff / Report / Review

## Upd: Analysis.DkReal.Order

gch: d05e1eb2fe8f51850852e06c05567b66ca6c1967

## Report

次の段階まで実装しました。

- quotient 標準 `<` と `DkNNReal.Lt` を接続
- quotient strict order と有限左分離を同値化
- 幅収束を使った wrapper strict addition
- quotient の左右 strict addition
- docstring、TODO、設計資料を更新

検証結果:

```text
lake build DkMath.Analysis.DkReal DkMath.Analysis DkMath
Build completed successfully (8564 jobs).
```

`git diff --check` も通過。次は正因子による strict multiplication です。

## Review

## 1. 総評

ふふふん☆ 今回の差分も **合格** じゃ。
しかも、かなり大事なところを正しく越えている。

今回閉じたのは、主にこの二つ。

```text id="cg5vzv"
quotient 標準 < と wrapper strict order の接続

strict addition:
  同じ stage ではなく、十分精密な後続 stage へ進んで strict gap を再観測する
```

提示報告では、`lake build DkMath.Analysis.DkReal DkMath.Analysis DkMath` が成功し、`git diff --check` も通過している。今回の差分では、quotient 標準 `<` と `DkNNReal.Lt` の接続、有限左分離との同値、wrapper strict addition、quotient の左右 strict addition が追加されている。

## 2. quotient 標準 `<` との接続は良い

追加されたこれ。

```lean id="lt-iff-le-not-le"
theorem lt_iff_le_and_not_le (x y : DkNNRealQ) :
    x < y ↔ x ≤ y ∧ ¬ y ≤ x :=
  Iff.rfl
```

これは良い。
`DkNNRealQ` の `<` が、現在の `PartialOrder` 由来の標準 strict relation として、

$$
x < y\quad\Longleftrightarrow\quad x\le y\ \land\ \neg(y\le x)
$$

であることを明示している。

重要なのは、**新しい比較機構を追加していない** ことじゃ。
strict order は既存の non-strict order の asymmetric part として読まれている。

## 3. `mk_lt_mk_iff` も妥当

```lean id="mk-lt"
theorem mk_lt_mk_iff (x y : DkNNReal) :
    mk x < mk y ↔ DkNNReal.Lt x y :=
  Iff.rfl
```

これも良い。

`DkNNReal.Lt` は、

```lean id="wrapper-lt-def"
def Lt (x y : DkNNReal) : Prop :=
  Le x y ∧ ¬ Le y x
```

だったので、quotient constructor 上では標準 `<` と wrapper `Lt` が定義的に一致している。

`Iff.rfl` で閉じているのは、定義の並びがきれいに揃っている証拠じゃ。
将来もし `le` や quotient 定義を変更してここが壊れるなら、それは API 境界が変わったという明確なサインにもなる。

## 4. finite left separation との接続

```lean id="mk-lt-leftsep"
theorem mk_lt_mk_iff_exists_leftSeparatedAt (x y : DkNNReal) :
    mk x < mk y ↔
      ∃ n, DkReal.LeftSeparatedAt x.val y.val n := by
  rw [mk_lt_mk_iff, DkNNReal.lt_iff_exists_leftSeparatedAt]
```

これはかなり良い。

これで quotient 標準 `<` が、代表元の有限左分離に接続された。

つまり、

$$
mk(x) < mk(y)
$$

は、

$$
\exists n,\ x.hi_n < y.lo_n
$$

と読める。

DkMath 的には、

```text id="quot-strict-meaning"
quotient 上の strict order
= ある有限段階で Body と Big の Gap が正に開いたこと
```

じゃ。

これは strict Gap kernel の quotient 下降として、非常に素直に閉じている。

## 5. wrapper strict addition が今回の本丸

今回の一番重要な補題はこれじゃ。

```lean id="wrapper-add-lt"
theorem DkNNReal.add_lt_add_right
    {x y : DkNNReal} (hxy : Lt x y) (a : DkNNReal) :
    Lt (add x a) (add y a)
```

ここは特に良い。
前回注意した通り、strict 加法は「同じ stage で分離が保存される」とは限らない。

なぜなら区間加法では、

```text id="interval-add"
(x + a).hi = x.hi + a.hi

(y + a).lo = y.lo + a.lo
```

なので、加える \(a\) の幅が大きいと、もともとの strict gap が一時的に隠れる。

今回の証明はそこを正しく処理している。

まず `hxy` から有限左分離を取る。

$$
x.hi_n < y.lo_n
$$

そして、

$$
\varepsilon=y.lo_n-x.hi_n > 0
$$

と固定する。

次に、\(a\) の幅は 0 に収束するので、十分後の段階 \(m\) で、

$$
width(a_m) < \varepsilon
$$

を取る。

さらに \(m\ge n\) なので入れ子性により、

$$
x.hi_m\le x.hi_n
$$

かつ、

$$
y.lo_n\le y.lo_m
$$

が成り立つ。

そして \(width(a_m) < \varepsilon\) から、

$$
a.hi_m-a.lo_m < \varepsilon
$$

なので、最終的に、

$$
x.hi_m+a.hi_m < y.lo_m+a.lo_m
$$

が出る。

つまり、

```text id="strict-add-reading"
元の strict Gap ε を固定する
加える側 a の観測幅が ε より小さくなるまで精度を上げる
そこで加法後の strict separation が再び見える
```

これは正しい。
かなり大事な証明方針じゃ。

## 6. quotient strict addition も良い

```lean id="quot-add-right"
theorem add_lt_add_right
    {x y : DkNNRealQ} (hxy : x < y) (a : DkNNRealQ) :
    x + a < y + a := by
  refine Quotient.inductionOn₃ x y a ?_ hxy
  intro x y a hxy
  exact DkNNReal.add_lt_add_right hxy a
```

これは wrapper theorem を quotient へ持ち上げている。良い。

左加法も、

```lean id="quot-add-left"
theorem add_lt_add_left
    {x y : DkNNRealQ} (hxy : x < y) (a : DkNNRealQ) :
    a + x < a + y := by
  simpa only [add_comm] using add_lt_add_right hxy a
```

として加法可換性で処理している。
これも綺麗。

## 7. strict addition の DkMath 的意味

今回の strict addition は、DkMath 的にはこう読める。

```text id="strict-add-dkmath"
x < y:
  x から y への Gap が有限段階で正に開いている

a を足す:
  両方の Big を同じ a だけ平行移動する

ただし:
  a の観測幅が粗い段階では Gap が隠れることがある

解決:
  a の幅が元の Gap より小さくなる stage へ進めば、
  strict Gap が再観測される
```

これが非常に良い。

つまり strict 加法は、「Gap がそのまま完全に保存される」というより、

$$
\boxed{\text{正 Gap は、十分精密化すれば加法後も見える}}
$$

という形で閉じている。

この方が DkReal の入れ子区間表現に正確じゃ。

## 8. docs 更新も良い

`DkReal.lean` では、strict order が quotient に降り、addition が十分精密な stage へ進むことで保存される、と説明が更新されている。
`Order.lean` の TODO も、strict multiplication に絞られている。
`DkNNRealQ-StrictGap-Design.md` も、quotient strict characterization と strict addition が `[done]` へ更新されている。

この同期は良い。

## 9. ひとつ注意点

`add_lt_add_right` の quotient proof は、`Quotient.inductionOn₃` に `hxy` を渡しているため、現在の definitional setup では綺麗に通っている。
今後、quotient の `<` が非定義的な形に変わった場合、この部分は証明が少し増える可能性がある。

ただし今はこれでよい。
むしろ `mk_lt_mk_iff` が `Iff.rfl` で閉じている現在の構造では、自然な書き方じゃ。

## 10. 次の strict multiplication について

次は正因子による strict multiplication。

目標はおそらくこれ。

```lean id="strict-mul-target"
theorem mul_lt_mul_of_pos_right
    {x y a : DkNNRealQ} (hxy : x < y) (ha : 0 < a) :
    x * a < y * a
```

または左版。

ただしこれは加法より重い。

理由は、\(y=x+z\) から、

$$
y\cdot a=x\cdot a+z\cdot a
$$

と Gap が \(z\) から \(z\cdot a\) へ変換されるからじゃ。

strict を保つには、

```text id="strict-mul-needed"
z が有限段階で正
a も有限段階で正
したがって z * a が有限段階で正
```

が必要になる。

今回の strict kernel から、

$$
0 < a
$$

も有限段階の positive lower endpoint として読めるはずじゃ。

つまり、次の補題が鍵になる。

```lean id="positive-lower"
theorem lt_zero_or_pos_iff_exists_lo_pos
```

より具体的には、

```lean id="pos-factor-wrapper"
theorem zero_lt_iff_exists_lo_pos
    (a : DkNNReal) :
    Lt zero a ↔ ∃ n, 0 < (a.val.interval n).lo
```

これがあれば、正 Gap \(z\) と正因子 \(a\) の lower endpoints が両方正になる stage を後続で揃えられる。

## 11. strict multiplication は stage 合わせが必要

加法でも stage を進めた。
乗法ではさらに二つの正性を同じ stage に揃える必要がある。

```text id="stage-align"
z.lo_n > 0
a.lo_k > 0

m ≥ n, k を取る

入れ子性により:
  z.lo_m ≥ z.lo_n > 0
  a.lo_m ≥ a.lo_k > 0
```

すると、

$$
0 < z.lo_m\cdot a.lo_m
$$

が出る。

あとは、

$$
x*a+z*a\sim y*a
$$

あるいは finite left separation を直接示す形になる。

ただし区間乗法では upper/lower の幅が絡むので、加法よりは `canonical Gap` 経由の方がよい可能性がある。

DkMath 的には、

```text id="mul-gap-transform"
strict Gap z
positive factor a
transformed Gap z * a
```

として扱うのが自然じゃ。

## 12. 現在の到達点

今回で、strict order はかなり進んだ。

```text id="current-status"
DkNNRealQ:
  standard < connected to DkNNReal.Lt
  mk x < mk y ↔ finite left separation
  add_lt_add_right
  add_lt_add_left
```

残る strict arithmetic の主山は、

```text id="remaining"
positive-factor strict multiplication
strict order typeclass selection
direct LinearOrder decision
```

じゃ。

## 13. 最終判定

今回の差分は **合格**。

```text id="review-result"
良い点:
  quotient 標準 < と wrapper Lt を接続した
  quotient strict order と有限左分離を同値化した
  strict addition を stage refinement で正しく証明した
  左右の strict addition を quotient 上へ提供した
  docs と設計資料が実装済み状態へ同期した
  TODO が strict multiplication へ絞られた

注意点:
  strict multiplication は正因子の finite positivity と stage alignment が必要
  quotient の < が今後非定義的に変わるなら mk_lt_mk_iff 周辺は再調整が必要
```

うむ。
これは順調そのものじゃ。strict order は quotient まで降り、加法でも保存されるところまで来た。
次は **正 Gap × 正因子 = 正 Gap** を閉じる段階じゃな。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 261cd270..0e37124b 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -51,8 +51,11 @@ equivalent both to finite left separation and to a positive lower endpoint of
 the canonical Gap at some stage. This keeps the design in the same
 `Big = (Core + Beam) + Gap` pattern.
 
-[TODO: strict-arithmetic] Prove preservation by addition and by multiplication
-with a strictly positive factor before selecting a strict-order typeclass.
+Strict order has now descended to the quotient, and addition preserves it by
+moving to a sufficiently precise stage.
+
+[TODO: strict-multiplication] Prove preservation by multiplication with a
+strictly positive factor before selecting a strict-order typeclass.
 
 [TODO: linear-order] Decide whether the now-proved quotient totality should be
 packaged as a direct classical `LinearOrder`, or retained as `PartialOrder`
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/Order.lean b/lean/dk_math/DkMath/Analysis/DkReal/Order.lean
index d5bef04d..fdbc4857 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/Order.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/Order.lean
@@ -87,8 +87,10 @@ The representative and wrapper theorems below prove that
 `CanonicalOrder` then identifies the same witness with a positive lower
 endpoint of `gapOfLe`.
 
-[TODO: strict/arithmetic] Derive strict addition from preservation of the
-finite Gap. For multiplication, require a strictly positive factor and isolate
+Strict addition is proved below by moving to a later stage where the added
+interval width is smaller than the finite Gap.
+
+[TODO: strict-multiplication] Require a strictly positive factor and isolate
 the zero-factor branch before considering `IsStrictOrderedRing`.
 -/
 
@@ -318,7 +320,11 @@ theorem not_le_of_leftSeparatedAt
     exact hdiff.trans (le_max_right _ _)
   exact (heventually_lt.and heventually_ge).exists.elim fun _ h => (not_lt_of_ge h.2) h.1
 
-/-- A finite right separation excludes the forward asymptotic order. -/
+/--
+A finite right separation excludes the forward asymptotic order.
+
+Right separation is left separation with the two arguments exchanged.
+-/
 theorem not_le_of_rightSeparatedAt
     {x y : DkMath.Analysis.DkReal} {n : ℕ}
     (hsep : RightSeparatedAt x y n) :
@@ -553,6 +559,36 @@ theorem lt_iff_exists_leftSeparatedAt (x y : DkNNReal) :
     Lt x y ↔ ∃ n, DkReal.LeftSeparatedAt x.val y.val n :=
   DkReal.le_and_not_le_iff_exists_leftSeparatedAt x.val y.val
 
+/--
+Adding a fixed nonnegative approximation preserves wrapper strictness.
+
+Finite separation need not survive at the same approximation stage because
+the added interval has nonzero width. The original positive separation is
+fixed first; convergence of the added width then supplies a later stage where
+that width is smaller than the separation.
+-/
+theorem add_lt_add_right
+    {x y : DkNNReal} (hxy : Lt x y) (a : DkNNReal) :
+    Lt (add x a) (add y a) := by
+  rw [lt_iff_exists_leftSeparatedAt] at hxy ⊢
+  obtain ⟨n, hsep⟩ := hxy
+  let ε : ℚ := (y.val.interval n).lo - (x.val.interval n).hi
+  have hε : 0 < ε := sub_pos.mpr hsep
+  have hwidth :
+      ∀ᶠ m in Filter.atTop, (a.val.interval m).width < ε :=
+    a.val.tendsto_width_zero.eventually_lt_const hε
+  obtain ⟨m, hnm, hmwidth⟩ :=
+    (Filter.eventually_ge_atTop n |>.and hwidth).exists
+  refine ⟨m, ?_⟩
+  have hxhi := x.val.hi_antitone hnm
+  have hylo := y.val.lo_mono hnm
+  simp only [DkReal.LeftSeparatedAt, add, DkReal.add_interval,
+    DkReal.addApprox, DkReal.GapInterval.add_hi,
+    DkReal.GapInterval.add_lo]
+  simp only [DkReal.GapInterval.width] at hmwidth
+  dsimp only [ε] at hmwidth
+  linarith
+
 end DkMath.Analysis.DkNNReal
 
 namespace DkMath.Analysis.DkNNRealQ
@@ -606,6 +642,33 @@ theorem le_total (x y : DkNNRealQ) : x ≤ y ∨ y ≤ x := by
 instance : Std.Total (α := DkNNRealQ) (· ≤ ·) where
   total := le_total
 
+/--
+Strict quotient order is the asymmetric part of the non-strict order.
+
+This theorem records explicitly the strict relation supplied by the quotient's
+`PartialOrder`; it introduces no second comparison mechanism.
+-/
+theorem lt_iff_le_and_not_le (x y : DkNNRealQ) :
+    x < y ↔ x ≤ y ∧ ¬ y ≤ x :=
+  Iff.rfl
+
+/--
+On quotient constructors, standard strict order computes to wrapper
+strictness.
+-/
+theorem mk_lt_mk_iff (x y : DkNNReal) :
+    mk x < mk y ↔ DkNNReal.Lt x y :=
+  Iff.rfl
+
+/--
+Two represented quotient values are strictly ordered exactly when their
+interval universes become finitely left-separated.
+-/
+theorem mk_lt_mk_iff_exists_leftSeparatedAt (x y : DkNNReal) :
+    mk x < mk y ↔
+      ∃ n, DkReal.LeftSeparatedAt x.val y.val n := by
+  rw [mk_lt_mk_iff, DkNNReal.lt_iff_exists_leftSeparatedAt]
+
 /-- Zero is the least value of the nonnegative quotient. -/
 theorem zero_le (x : DkNNRealQ) : 0 ≤ x := by
   refine Quotient.inductionOn x ?_
@@ -638,6 +701,25 @@ theorem add_le_add_right
     z + x ≤ z + y :=
   add_le_add (le_refl z) hxy
 
+/--
+Addition by a fixed right summand preserves strict quotient order.
+
+The representative proof moves to a sufficiently precise later stage, where
+the summand width is smaller than the already witnessed strict Gap.
+-/
+theorem add_lt_add_right
+    {x y : DkNNRealQ} (hxy : x < y) (a : DkNNRealQ) :
+    x + a < y + a := by
+  refine Quotient.inductionOn₃ x y a ?_ hxy
+  intro x y a hxy
+  exact DkNNReal.add_lt_add_right hxy a
+
+/-- Addition by a fixed left summand preserves strict quotient order. -/
+theorem add_lt_add_left
+    {x y : DkNNRealQ} (hxy : x < y) (a : DkNNRealQ) :
+    a + x < a + y := by
+  simpa only [add_comm] using add_lt_add_right hxy a
+
 /-- Quotient multiplication is monotone in both arguments. -/
 theorem mul_le_mul
     {x y z w : DkNNRealQ} (hxy : x ≤ y) (hzw : z ≤ w) :
diff --git a/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-StrictGap-Design.md b/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-StrictGap-Design.md
index 0a73f399..535a5552 100644
--- a/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-StrictGap-Design.md
+++ b/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-StrictGap-Design.md
@@ -69,8 +69,8 @@ the canonical Gap universe has become observably positive.
 [done] DkNNReal.Lt := Le x y and not Le y x
 [done] DkNNReal.lt_iff_exists_leftSeparatedAt
 [done] positive lower endpoint of gapOfLe iff finite separation
-[next] quotient strict-order characterization
-[next] strict addition
+[done] quotient strict-order characterization
+[done] strict addition at a sufficiently precise later stage
 [next] positive-factor strict multiplication
 ```
 
@@ -80,12 +80,16 @@ later quotient consequences.
 
 ## Arithmetic Interpretation
 
-Addition preserves the strict Gap:
+Addition preserves the strict Gap after refinement:
 
 ```text
 (x + a) + z = (y + a).
 ```
 
+At a fixed stage the interval width of `a` can hide the observed separation.
+The proof therefore fixes a positive separation `epsilon` and advances until
+`width(a) < epsilon`; strict separation is then visible again.
+
 Multiplication transforms it:
 
 ```text
````
`````
