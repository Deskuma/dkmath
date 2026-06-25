# Git diff / Report / Review

## Upd: Analysis.DkReal.CanonicalOrder

gch: 0098e23c4da8876b806282d69c209465410c24c5

## Report

厳密 Gap kernel の次段階を実装しました。

- 有限左分離から逆順序を否定
- wrapper strict order `Lt` を定義
- `Lt` と有限左分離の同値
- `Lt` と canonical `gapOfLe` の有限段階での正値性を同値化
- docstring、TODO、設計資料を更新

検証済み:

```text
lake build DkMath.Analysis.DkReal DkMath.Analysis DkMath
Build completed successfully (8564 jobs).
```

`git diff --check` も通過しています。次は quotient strict-order characterization、その後に厳密加法・正因子乗法です。

## Review

ふふふん☆ これは **かなり良い差分** じゃ。
今回の差分は **合格**。strict order の本丸である「有限分離」と「抽出 Gap の正値性」が、予定どおり Lean 側に落ちている。

提示報告では、`lake build DkMath.Analysis.DkReal DkMath.Analysis DkMath` が成功し、`git diff --check` も通過している。追加内容も、有限左分離から逆順序を否定し、wrapper strict order `Lt` を定義し、`Lt` と有限左分離、さらに `gapOfLe` の lower endpoint 正値性を同値化した、という流れで整理されている。

## 1. 総評

今回の到達点はこれじゃ。

```text id="strict-gap-core"
Le x y ∧ ¬ Le y x
↔ ∃ n, LeftSeparatedAt x y n
↔ ∃ n, 0 < (gapOfLe x y hxy).interval n.lo
```

つまり strict order が、

```text id="strict-reading"
抽象的な < ではなく、
Big 内部に抽出された Gap が有限段階で正に開いた状態
```

として閉じた。

これは非常に DkMath らしい。

非厳密順序は「defect が 0 に潰れる」。
厳密順序は「ある有限段階で Gap の下端が正になる」。
この対比がかなり綺麗じゃ。

## 2. `not_le_of_leftSeparatedAt` が今回の核

今回の一番重要な補題はこれ。

```lean id="not-le-left"
theorem not_le_of_leftSeparatedAt
    {x y : DkReal} {n : ℕ}
    (hsep : LeftSeparatedAt x y n) :
    ¬ Le y x
```

これは正しい。

有限段階で、

$$
x.hi_n<y.lo_n
$$

がある。そこで、

$$
\varepsilon=y.lo_n-x.hi_n
$$

と置けば、\(\varepsilon>0\)。

入れ子性により、任意の後続段階 \(m\ge n\) で、

$$
y.lo_n\le y.lo_m
$$

かつ、

$$
x.lo_m\le x.hi_m\le x.hi_n
$$

となる。
したがって、

$$
\varepsilon\le y.lo_m-x.lo_m
$$

さらに、

$$
y.lo_m-x.lo_m\le orderDefect(y,x,m)
$$

なので、後続段階で常に

$$
\varepsilon\le orderDefect(y,x,m)
$$

となる。

一方、`Le y x` なら `orderDefect y x` は 0 に収束するので、いずれ \(\varepsilon\) より小さくなる。
これは矛盾。

この証明はかなり強い。
有限 Gap が一度開いたら、逆向き order defect は 0 に潰れられない、ということじゃ。

## 3. `le_and_not_le_iff_exists_leftSeparatedAt` は綺麗

```lean id="le-not-le-iff"
theorem le_and_not_le_iff_exists_leftSeparatedAt
    (x y : DkReal) :
    (Le x y ∧ ¬ Le y x) ↔ ∃ n, LeftSeparatedAt x y n
```

これは今回の strict Gap kernel そのものじゃ。

左から右は、もし finite left separation がなければ、前回の totality 側の補題

```lean id="no-left-to-reverse"
le_of_not_exists_leftSeparatedAt
```

により `Le y x` が出てしまう。
しかし仮定は `¬ Le y x` なので矛盾。

右から左は、有限左分離から `Le x y` と `¬ Le y x` を出すだけ。
これは `le_of_leftSeparatedAt` と `not_le_of_leftSeparatedAt` で閉じる。

これは実に良い。
totality の時に作った「左分離なしなら逆順序」が、ここで strict order の反対側として働いている。

## 4. wrapper strict order `Lt` は妥当

```lean id="wrapper-lt"
def Lt (x y : DkNNReal) : Prop :=
  Le x y ∧ ¬ Le y x
```

これは今の段階では良い判断じゃ。

quotient 上の `<` にいきなり行く前に、代表元 wrapper 側で strictness を定義し、有限分離と結ぶ。
この順序は安全。

```lean id="wrapper-lt-iff"
theorem lt_iff_exists_leftSeparatedAt (x y : DkNNReal) :
    Lt x y ↔ ∃ n, DkReal.LeftSeparatedAt x.val y.val n
```

ここまで来ると、strict order は代表元に対して完全に幾何化された。

```text id="wrapper-lt-meaning"
DkNNReal.Lt x y
とは、
ある有限段階で x の区間全体が y の区間全体より左に分離したこと
```

これは良い。

## 5. `gapOfLe_lo_pos_iff_leftSeparatedAt` が DkMath 的に美しい

```lean id="gap-pos-iff"
theorem gapOfLe_lo_pos_iff_leftSeparatedAt
    (x y : DkNNReal) (hxy : Le x y) (n : ℕ) :
    0 < ((gapOfLe x y hxy).val.interval n).lo ↔
      DkReal.LeftSeparatedAt x.val y.val n
```

これは今回の DkMath 的ハイライトじゃ。

`gapOfLe` の lower endpoint は定義展開すれば、

$$
\max(0,y.lo_n-x.hi_n)
$$

だから、

$$
0<\max(0,y.lo_n-x.hi_n)
$$

は、

$$
x.hi_n<y.lo_n
$$

と同値。

つまり、

```text id="gap-pos-reading"
抽出 Gap の lower endpoint が正
↔ Body と Big が有限段階で厳密分離
```

じゃ。

これはまさに、strict order を「抽出 Gap の有限正値性」として読む補題。

## 6. `lt_iff_exists_gapOfLe_lo_pos` も自然

```lean id="lt-gap-pos"
theorem lt_iff_exists_gapOfLe_lo_pos
    (x y : DkNNReal) (hxy : Le x y) :
    Lt x y ↔ ∃ n, 0 < ((gapOfLe x y hxy).val.interval n).lo
```

これは良い。

ただし一点、`hxy : Le x y` を明示引数として持つ形は自然じゃ。
`gapOfLe x y hxy` は order proof から作る canonical Gap なので、strictness を語る前に forward order が必要になる。

なお、`Lt x y` の左側にはすでに `Le x y` が含まれているので、将来的には便利版として、

```lean id="lt-gap-pos-variant"
theorem lt_iff_exists_gapOfLe_lo_pos'
    (x y : DkNNReal) :
    Lt x y ↔ ∃ hxy : Le x y, ∃ n,
      0 < ((gapOfLe x y hxy).val.interval n).lo
```

のような形を追加してもよい。
ただし今の形の方が実装上は扱いやすい。

## 7. docstring と設計資料の更新も良い

`Order.lean` の説明が「Next difference kernel」から「Strict Gap kernel」へ更新され、TODO も実装済み部分と次課題に分離されている。
`DkNNRealQ-StrictGap-Design.md` も、提案状態から実装状況へ更新されており、`not_le_of_leftSeparatedAt`、代表 strictness と有限左分離の同値、`gapOfLe` の正値性との接続が完了として記録されている。

これは良い。
実装と文書のズレが少ない。

## 8. 今回の数学的意味

今回で、DkNNReal の strict order はこう読めるようになった。

```text id="strict-meaning"
x ≤ y:
  Big の中に Body = x が収まり、非負 Gap が抽出できる

x < y:
  その抽出 Gap が、ある有限段階で正に観測される

x = y:
  双方向に Le が成立し、抽出 Gap は quotient 的に 0 へ潰れる
```

つまり strictness は、無限極限の抽象的な不一致ではない。
有限段階の観測証拠を持つ。

これは DkMath.Analysis の Route B にとってかなり重要じゃ。

## 9. 次の quotient strict characterization

次は報告通り、quotient 側じゃ。

いま wrapper には、

```lean id="wrapper-kernel"
DkNNReal.Lt x y ↔ ∃ n, LeftSeparatedAt x.val y.val n
```

がある。

次は `DkNNRealQ` の標準 `<` と接続する段階じゃ。

おそらく候補は、

```lean id="quot-lt-core"
theorem DkNNRealQ.lt_iff :
    x < y ↔ x ≤ y ∧ ¬ y ≤ x
```

これは標準 API で既に近いものがあるかもしれない。

そのうえで、

```lean id="quot-wrapper-lift"
theorem DkNNRealQ.lt_mk_iff
    (x y : DkNNReal) :
    mk x < mk y ↔ DkNNReal.Lt x y
```

または、

```lean id="quot-lt-leftsep"
theorem DkNNRealQ.mk_lt_mk_iff_exists_leftSeparatedAt
    (x y : DkNNReal) :
    mk x < mk y ↔ ∃ n, DkReal.LeftSeparatedAt x.val y.val n
```

が狙いになる。

ただし `mk` の namespace や notation に合わせて名前は調整じゃ。

## 10. strict addition は次にかなり近い

strict addition は、おそらくすぐ行ける。

目標は、

```lean id="strict-add-target"
theorem add_lt_add_right
    {x y : DkNNRealQ} (h : x < y) (a : DkNNRealQ) :
    x + a < y + a
```

または wrapper で先に、

```lean id="wrapper-strict-add"
theorem DkNNReal.add_lt_add_right
    {x y : DkNNReal} (h : Lt x y) (a : DkNNReal) :
    Lt (add x a) (add y a)
```

代表元側の有限分離で見れば簡単じゃ。
もし \(x.hi_n < y.lo_n\) なら、

$$
x.hi_n+a.hi_n < y.lo_n+a.lo_n
$$

とは必ずしも言えない。ここは注意。

区間加法では、

```text id="interval-add"
(x + a).hi = x.hi + a.hi
(y + a).lo = y.lo + a.lo
```

なので、同じ \(a\) を足しても、(a.hi) と (a.lo) の差がある。
有限分離幅が (a.width) より小さい段階では、分離が潰れて見える可能性がある。

しかし \(a.width_n\to0\) なので、分離 Gap \(\varepsilon > 0\) がある段階以降、十分精度を上げれば \(a.width_m < \varepsilon\) となる。
そこで strict separation が復活する。

つまり strict addition は単純な同段階保存ではなく、

```text id="strict-add-detail"
有限分離 ε を取る
a の幅が ε より小さくなる後続段階を取る
その段階で加法後も左分離する
```

という証明になる。

ここは重要じゃ。
設計資料の「Addition preserves the strict Gap」は概念的には正しいが、区間代表元の同じ stage で保存されるとは限らない。後続段階で保存される、が正確じゃ。

## 11. positive-factor strict multiplication はさらに一段重い

乗法はもっと注意が要る。

$$
y=x+z
$$

なら、

$$
ya=xa+za
$$

だが、strict を保つには \(a\) が正であるだけでなく、有限段階で \(a\) の lower endpoint が正になることが必要になる可能性が高い。

`0 < a` をどう定義するかにもよるが、今回の strict kernel からすれば、

```text id="positive-factor"
0 < a
↔ ∃ n, 0 < a.interval n.lo
```

のような形が欲しい。

そして \(z\) も有限段階で positive lower endpoint を持つ。
すると、積 \(z*a\) の lower endpoint が正になり、strict Gap が保存される。

ここも非常に DkMath 的じゃ。

```text id="mul-strict-gap"
Gap z が正
Factor a が正
変換後 Gap z * a も正
```

ただし `a = 0` branch では Gap が潰れる。
設計資料がこの branch を分けているのは正しい。

## 12. 小さな注意点

`rightSeparatedAt_persistent` や `not_le_of_rightSeparatedAt` は、`leftSeparatedAt_persistent` や `not_le_of_leftSeparatedAt` にそのまま渡している。
これは定義上、`RightSeparatedAt x y` が `LeftSeparatedAt y x` と同じ形なので Lean が通っているなら問題なし。
読みやすさを上げるなら、docstring で「right separation is left separation with arguments swapped」と書いてもよい。

また、`Lt` は wrapper namespace に置かれている。次に quotient 側で標準 `<` とつなぐまでは、`DkNNReal.Lt` と `DkNNRealQ` の `<` が別物である点を docs に一言足してもよいかもしれぬ。

## 13. 現在の到達点

今回でこうなった。

```text id="current-status"
DkReal:
  finite left separation excludes reverse Le
  Le x y ∧ ¬ Le y x ↔ finite left separation

DkNNReal:
  Lt defined as Le x y ∧ ¬ Le y x
  Lt ↔ finite left separation
  Lt ↔ finite positive lower endpoint of gapOfLe

DkNNRealQ:
  quotient strict-order characterization is next
```

つまり strict order の representation kernel は閉じた。
次は quotient API と strict arithmetic。

## 14. 最終判定

今回の差分は **合格**。

```text id="review-result"
良い点:
  finite left separation から reverse order を否定した
  strictness を Le x y ∧ ¬ Le y x として wrapper に定義した
  strictness と finite left separation を同値化した
  canonical gapOfLe の lower endpoint 正値性と finite separation を同値化した
  docs と設計資料を implemented status に更新した
  quotient strict characterization 以降の課題が明確になった

注意点:
  strict addition は同段階保存ではなく、幅が十分小さい後続段階での保存として証明する必要がある
  strict multiplication は positive factor の finite positivity が必要になる
```

うむ。
これで strict Gap の核は通った。
次は quotient strict order へ持ち上げ、それから厳密加法、正因子による厳密乗法じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index f2652ef4..261cd270 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -46,9 +46,13 @@ Canonical order is also constructive at the representation level. From
 `y = x + z` in the quotient. No subtraction operation is added to
 `DkNNRealQ`.
 
-The next strict-order layer should classify this known Gap: zero Gap gives
-equality, while a positive lower Gap observed at a finite stage gives strict
-order. This keeps the design in the same `Big = (Core + Beam) + Gap` pattern.
+The strict-order kernel classifies this known Gap: wrapper strictness is
+equivalent both to finite left separation and to a positive lower endpoint of
+the canonical Gap at some stage. This keeps the design in the same
+`Big = (Core + Beam) + Gap` pattern.
+
+[TODO: strict-arithmetic] Prove preservation by addition and by multiplication
+with a strictly positive factor before selecting a strict-order typeclass.
 
 [TODO: linear-order] Decide whether the now-proved quotient totality should be
 packaged as a direct classical `LinearOrder`, or retained as `PartialOrder`
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/CanonicalOrder.lean b/lean/dk_math/DkMath/Analysis/DkReal/CanonicalOrder.lean
index 9c52362a..1fc4a1cf 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/CanonicalOrder.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/CanonicalOrder.lean
@@ -231,6 +231,36 @@ theorem add_diffOfLe_equiv
     Equiv (add x (diffOfLe x y hxy)) y :=
   DkReal.add_diffNonneg_equiv hxy
 
+/--
+The extracted canonical Gap is positive at stage `n` exactly when the Body
+and Big representatives are strictly separated there.
+-/
+theorem gapOfLe_lo_pos_iff_leftSeparatedAt
+    (x y : DkNNReal) (hxy : Le x y) (n : ℕ) :
+    0 < ((gapOfLe x y hxy).val.interval n).lo ↔
+      DkReal.LeftSeparatedAt x.val y.val n := by
+  simp only [gapOfLe, diffOfLe, DkReal.diffNonneg,
+    DkReal.diffNonnegApprox, DkReal.diffNonnegInterval,
+    DkReal.LeftSeparatedAt]
+  constructor
+  · intro h
+    by_contra hsep
+    have hnonpos :
+        (y.val.interval n).lo - (x.val.interval n).hi ≤ 0 :=
+      sub_nonpos.mpr (le_of_not_gt hsep)
+    rw [max_eq_left hnonpos] at h
+    exact (lt_irrefl 0) h
+  · intro hsep
+    rw [max_eq_right (sub_nonneg.mpr hsep.le)]
+    exact sub_pos.mpr hsep
+
+/-- Strict wrapper order is finite positivity of the extracted canonical Gap. -/
+theorem lt_iff_exists_gapOfLe_lo_pos
+    (x y : DkNNReal) (hxy : Le x y) :
+    Lt x y ↔ ∃ n, 0 < ((gapOfLe x y hxy).val.interval n).lo := by
+  rw [lt_iff_exists_leftSeparatedAt]
+  exact exists_congr fun n => (gapOfLe_lo_pos_iff_leftSeparatedAt x y hxy n).symm
+
 end DkMath.Analysis.DkNNReal
 
 namespace DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/Order.lean b/lean/dk_math/DkMath/Analysis/DkReal/Order.lean
index c25b74b8..d5bef04d 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/Order.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/Order.lean
@@ -68,27 +68,24 @@ quotient therefore carries Mathlib's `IsOrderedRing` predicate, whose name is
 historical: its algebraic assumption is only `Semiring`. No canonical-order,
 strict-order, or linear-order structure is claimed.
 
-## Next difference kernel: strict Gap
+## Strict Gap kernel
 
 Canonical order fills the known frame
 
 `Big = Body + Gap`
 
-by extracting a nonnegative Gap representation. Strict order should not start
-from a new abstract `<`. Its missing kernel is whether that extracted Gap
-collapses to zero or opens positively at finite precision:
+by extracting a nonnegative Gap representation. Strict order does not start
+from a new comparison mechanism. It asks whether that extracted Gap collapses
+to zero or opens positively at finite precision:
 
 * equality: `Big = Body + 0`;
 * strict orientation: at some stage `Body.hi < Big.lo`;
 * finite strict Gap: `0 < Big.lo - Body.hi`.
 
-[TODO: strict/core] Define representative strictness by
-`Le x y ∧ ¬ Le y x`, then prove it is equivalent to
-`∃ n, LeftSeparatedAt x y n`.
-
-[TODO: strict/gap] Relate finite separation to the canonical Gap extraction:
-under strictness, some lower endpoint of `gapOfLe` is positive; conversely a
-positive extracted Gap lower endpoint witnesses strict separation.
+The representative and wrapper theorems below prove that
+`Le x y ∧ ¬ Le y x` is equivalent to `∃ n, LeftSeparatedAt x y n`.
+`CanonicalOrder` then identifies the same witness with a positive lower
+endpoint of `gapOfLe`.
 
 [TODO: strict/arithmetic] Derive strict addition from preservation of the
 finite Gap. For multiplication, require a strictly positive factor and isolate
@@ -291,6 +288,43 @@ theorem le_of_rightSeparatedAt
     Le y x :=
   le_of_leftSeparatedAt hsep
 
+/--
+A finite left separation excludes the reverse asymptotic order.
+
+The witnessed rational Gap remains a positive lower bound for the reverse
+order defect at every later stage, contradicting convergence to zero.
+-/
+theorem not_le_of_leftSeparatedAt
+    {x y : DkMath.Analysis.DkReal} {n : ℕ}
+    (hsep : LeftSeparatedAt x y n) :
+    ¬ Le y x := by
+  intro hyx
+  let ε : ℚ := (y.interval n).lo - (x.interval n).hi
+  have hε : 0 < ε := sub_pos.mpr hsep
+  have heventually_lt :
+      ∀ᶠ m in Filter.atTop, orderDefect y x m < ε :=
+    hyx.eventually_lt_const hε
+  have heventually_ge :
+      ∀ᶠ m in Filter.atTop, ε ≤ orderDefect y x m := by
+    filter_upwards [Filter.eventually_ge_atTop n] with m hnm
+    have hylo := y.lo_mono hnm
+    have hxhi := x.hi_antitone hnm
+    have hxlohi := (x.interval m).le_lo_hi
+    simp only [ε, orderDefect]
+    have hdiff :
+        (y.interval n).lo - (x.interval n).hi ≤
+          (y.interval m).lo - (x.interval m).lo := by
+      linarith
+    exact hdiff.trans (le_max_right _ _)
+  exact (heventually_lt.and heventually_ge).exists.elim fun _ h => (not_lt_of_ge h.2) h.1
+
+/-- A finite right separation excludes the forward asymptotic order. -/
+theorem not_le_of_rightSeparatedAt
+    {x y : DkMath.Analysis.DkReal} {n : ℕ}
+    (hsep : RightSeparatedAt x y n) :
+    ¬ Le x y :=
+  not_le_of_leftSeparatedAt hsep
+
 /-- Stagewise overlap of two representations implies vanishing separation. -/
 theorem equiv_of_forall_overlaps
     {x y : DkMath.Analysis.DkReal}
@@ -329,6 +363,23 @@ theorem le_of_not_exists_leftSeparatedAt
       · exact (x.interval n).width_nonneg
       · linarith)
 
+/--
+Strict representative order is equivalent to a finite observed left
+separation.
+
+This is the strict Gap kernel: non-strict orientation is asymptotic, while
+strict orientation is witnessed at finite rational precision.
+-/
+theorem le_and_not_le_iff_exists_leftSeparatedAt
+    (x y : DkMath.Analysis.DkReal) :
+    (Le x y ∧ ¬ Le y x) ↔ ∃ n, LeftSeparatedAt x y n := by
+  constructor
+  · intro h
+    by_contra hnone
+    exact h.2 (le_of_not_exists_leftSeparatedAt hnone)
+  · rintro ⟨n, hn⟩
+    exact ⟨le_of_leftSeparatedAt hn, not_le_of_leftSeparatedAt hn⟩
+
 /-- The asymptotic order on all `DkReal` representations is total. -/
 theorem le_total_repr (x y : DkMath.Analysis.DkReal) :
     Le x y ∨ Le y x := by
@@ -466,6 +517,10 @@ its public order lemmas have no proof arguments.
 def Le (x y : DkNNReal) : Prop :=
   DkReal.Le x.val y.val
 
+/-- Strict wrapper order: forward order without reverse order. -/
+def Lt (x y : DkNNReal) : Prop :=
+  Le x y ∧ ¬ Le y x
+
 /-- Wrapper equivalence preserves asymptotic order in both arguments. -/
 theorem le_congr
     {x x' y y' : DkNNReal} (hxx' : Equiv x x') (hyy' : Equiv y y') :
@@ -493,6 +548,11 @@ theorem mul_le_mul
 theorem le_total (x y : DkNNReal) : Le x y ∨ Le y x :=
   DkReal.le_total_repr x.val y.val
 
+/-- Wrapper strictness is exactly finite left separation of representatives. -/
+theorem lt_iff_exists_leftSeparatedAt (x y : DkNNReal) :
+    Lt x y ↔ ∃ n, DkReal.LeftSeparatedAt x.val y.val n :=
+  DkReal.le_and_not_le_iff_exists_leftSeparatedAt x.val y.val
+
 end DkMath.Analysis.DkNNReal
 
 namespace DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-StrictGap-Design.md b/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-StrictGap-Design.md
index 1906fe58..0a73f399 100644
--- a/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-StrictGap-Design.md
+++ b/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-StrictGap-Design.md
@@ -61,22 +61,22 @@ Extracted Gap:
 The middle form is the finite Core--Gap separation. The last form says that
 the canonical Gap universe has become observably positive.
 
-## Proposed Lean Sequence
+## Implementation Status
 
 ```text
-1. DkReal.not_le_of_leftSeparatedAt
-2. DkReal.lt_iff_exists_leftSeparatedAt
-3. DkNNReal.Lt := Le x y and not Le y x
-4. DkNNReal.lt_iff_exists_leftSeparatedAt
-5. positive lower endpoint of gapOfLe iff finite separation
-6. quotient strict-order characterization
-7. strict addition
-8. positive-factor strict multiplication
+[done] DkReal.not_le_of_leftSeparatedAt
+[done] representative strictness iff finite left separation
+[done] DkNNReal.Lt := Le x y and not Le y x
+[done] DkNNReal.lt_iff_exists_leftSeparatedAt
+[done] positive lower endpoint of gapOfLe iff finite separation
+[next] quotient strict-order characterization
+[next] strict addition
+[next] positive-factor strict multiplication
 ```
 
-The representative theorem should precede any strict ordered-semiring
-typeclass. It is the actual mathematical kernel; the typeclass is only its
-later packaging.
+The representative theorem now precedes every strict ordered-semiring
+typeclass. It is the mathematical kernel; a typeclass will only package its
+later quotient consequences.
 
 ## Arithmetic Interpretation
 
````
`````
