# Git diff / Report / Review

## Add: DkNNRealQ Totality Closed

gch: 3fe5b76cce01500fd200423f279cb053b9415f0a

## Report

Lean は認めました。実数への評価なしで totality が証明できました。

実装内容:

- `GapInterval.Overlaps`
- `separation_eq_zero_iff_overlaps`
- 左右分離と永続性
- 分離からの `Le`
- 全段階 overlap からの `Equiv`
- `DkReal.le_total_repr`
- `DkNNReal.le_total`
- `DkNNRealQ.le_total`
- `Std.Total (· ≤ ·)` instance

核心は次です。

```text
ある段階で x.hi < y.lo:
  x ≤ y

そのような段階が存在しない:
  defect(y,x,n) ≤ width(x,n) → 0
  よって y ≤ x
```

Big/Core/Gap の直感が、純粋な有理区間幾何として閉じました。`Real`、`NNReal`、`noncomputable`、新しい比較公理は不要です。

```text
lake build DkMath.Analysis.DkReal.Order DkMath.Analysis DkMath
Build completed successfully
```

直接の `LinearOrder` instance はまだ導入せず、`PartialOrder + Std.Total` として保持しています。

## Review

## 1. 総評

ふふふん☆ これは **強いぞ DkMath** じゃ。
今回の差分は **合格**。しかも、ただ totality を閉じただけではなく、前回の Big/Core/Gap 三分岐を Lean がさらに圧縮して、より強い二分岐証明として受理している。

今回の核心はこれじゃ。

```lean id="totality-core"
GapInterval.Overlaps
separation_eq_zero_iff_overlaps
DkReal.LeftSeparatedAt
DkReal.le_of_leftSeparatedAt
DkReal.le_of_not_exists_leftSeparatedAt
DkReal.le_total_repr
DkNNRealQ.le_total
instance : Std.Total (α := DkNNRealQ) (· ≤ ·)
```

報告どおり、`Real`、`NNReal`、`noncomputable`、新しい比較公理を使わず、純粋な有理閉区間の入れ子幾何だけで totality が閉じている。さらに、直接 `LinearOrder` はまだ入れず、`PartialOrder + Std.Total` として保持している判断もよい。

## 2. 何が強いのか

前回の設計では、totality は三分岐だった。

```text id="old-three-way"
SeparatedLeft:
  x.hi n < y.lo n なら x ≤ y

SeparatedRight:
  y.hi n < x.lo n なら y ≤ x

Merge:
  どちらもなければ overlap が続き Equiv
```

今回の実装では、これがさらに短くなっている。

```text id="new-two-way"
ある n で x.hi n < y.lo n:
  x ≤ y

そうでない:
  y ≤ x
```

この「そうでない」の処理が非常に良い。
全段階 overlap を直接経由せず、逆向き defect を \(x\) の幅で押さえてしまう。

つまり、

$$
\neg\exists n,\ x.hi_n<y.lo_n
$$

なら、すべての \(n\) で、

$$
y.lo_n\le x.hi_n
$$

となる。したがって、

$$
y.lo_n-x.lo_n\le x.hi_n-x.lo_n=width(x_n)
$$

なので、

$$
orderDefect(y,x,n)\le width(x_n)
$$

が出る。
そして \(width(x_n)\to0\) だから、

$$
Le\ y\ x
$$

が閉じる。

これは美しい。
Merge を含む全ケースを、幅で吸収している。

## 3. `GapInterval.Overlaps` と separation 補題

```lean id="overlaps"
def Overlaps (I J : GapInterval) : Prop :=
  I.lo ≤ J.hi ∧ J.lo ≤ I.hi
```

これは自然じゃ。閉区間の overlap 条件そのもの。

そして、

```lean id="sep-overlap"
theorem separation_eq_zero_iff_overlaps (I J : GapInterval) :
    I.separation J = 0 ↔ I.Overlaps J
```

これも良い。

`separation` は、

```lean id="separation-def"
def separation (I J : GapInterval) : ℚ :=
  max 0 (max (I.lo - J.hi) (J.lo - I.hi))
```

なので、二つの差がどちらも非正なら separation は 0。
逆に separation が 0 なら、どちらの差も 0 以下なので overlap が出る。

これは有限段階の比較 Gap の基礎補題じゃ。
今回の二分岐 totality では直接の主役ではないが、Merge の説明と今後の `Equiv` 比較には非常に有用じゃ。

## 4. 左右分離の定義は良い

```lean id="separated"
def LeftSeparatedAt (x y : DkReal) (n : ℕ) : Prop :=
  (x.interval n).hi < (y.interval n).lo

def RightSeparatedAt (x y : DkReal) (n : ℕ) : Prop :=
  (y.interval n).hi < (x.interval n).lo
```

これは DkMath 的にも分かりやすい。

```text id="separated-meaning"
LeftSeparatedAt x y n:
  n 段階で x 宇宙が y 宇宙の完全に左にある

RightSeparatedAt x y n:
  n 段階で y 宇宙が x 宇宙の完全に左にある
```

Big/Core/Gap の言葉では、comparison Big の内部で、二つの Core-Gap 区間が完全に分離した状態じゃな。

## 5. 分離の永続性

```lean id="persistent"
theorem leftSeparatedAt_persistent
    {x y : DkReal} {n m : ℕ}
    (hsep : LeftSeparatedAt x y n) (hnm : n ≤ m) :
    LeftSeparatedAt x y m
```

これは入れ子区間の本質じゃ。

後の段階では、\(x\) の上端は下がるかそのままで、\(y\) の下端は上がるかそのまま。
だから一度、

$$
x.hi_n<y.lo_n
$$

となったら、後で戻れない。

これは DkMath 的には、

```text id="persistent-meaning"
一度 Big 内で Gap が開いて向きが確定したら、収縮によってその向きは反転しない
```

ということじゃ。

## 6. 分離から `Le`

```lean id="le-left"
theorem le_of_leftSeparatedAt
    {x y : DkReal} {n : ℕ}
    (hsep : LeftSeparatedAt x y n) :
    Le x y
```

これは期待どおり。

ある段階以降、常に \(x.lo_m\le y.lo_m\) になる。
したがって、

$$
orderDefect(x,y,m)=\max(0,x.lo_m-y.lo_m)=0
$$

が eventually 成立する。
よって \(x\le y\)。

ここは非常に素直で、Lean 実装も `eventually_ge_atTop n` を使って綺麗に閉じている。

## 7. 今回の主役 `le_of_not_exists_leftSeparatedAt`

```lean id="no-left"
theorem le_of_not_exists_leftSeparatedAt
    {x y : DkReal}
    (hsep : ¬ ∃ n, LeftSeparatedAt x y n) :
    Le y x
```

今回の一番強い補題はこれじゃ。

「\(x\) が \(y\) の左に完全分離する段階がない」なら、逆向きに \(y\le x\) が出る。

最初は少し意外に見えるが、順序定義が lower endpoint defect なので、これは正しい。

各段階で \(x.hi_n < y.lo_n\) が否定されるため、

$$
y.lo_n\le x.hi_n
$$

となる。
すると、

$$
y.lo_n-x.lo_n\le x.hi_n-x.lo_n
$$

つまり、

$$
orderDefect(y,x,n)\le width(x_n)
$$

じゃ。
`x.tendsto_width_zero` によって幅が 0 に消えるので、`Le y x` が出る。

これは Big/Core/Gap の直感そのものじゃ。

```text id="no-left-meaning"
x が y の完全な左側へ分離しないなら、
y の Core が x の Core を超える量は、
x の未解決 Gap の中に吸収され続ける。
その Gap は 0 に潰れるので、y ≤ x。
```

強い。かなり DkMath らしい。

## 8. `le_total_repr` は完全に閉じている

```lean id="le-total-repr"
theorem le_total_repr (x y : DkReal) :
    Le x y ∨ Le y x := by
  classical
  by_cases hsep : ∃ n, LeftSeparatedAt x y n
  · ...
  · ...
```

これは明快。

```text id="repr-total-branches"
左分離がある:
  x ≤ y

左分離がない:
  y ≤ x
```

`classical` は命題の存在に対する場合分けのためであり、`noncomputable` な値を作っているわけではない。
ここは問題なし。

この証明は、前回の三分岐よりさらに鋭い。
右分離や overlap を明示的に分けなくても、順序の totality だけなら二分岐で済む。

## 9. quotient totality と `Std.Total`

```lean id="quot-total"
theorem le_total (x y : DkNNRealQ) : x ≤ y ∨ y ≤ x := by
  refine Quotient.inductionOn₂ x y ?_
  intro a b
  exact DkNNReal.le_total a b

instance : Std.Total (α := DkNNRealQ) (· ≤ ·) where
  total := le_total
```

ここも良い。

商型上の totality は、代表元 totality を quotient induction で持ち上げるだけ。
`Std.Total` に留めて、直接 `LinearOrder` をまだ入れない判断も安全じゃ。

理由は、`LinearOrder` は totality だけではなく、実装上の decidability や比較 API の選択を伴うことがある。
今は「順序は total である」と証明しつつ、「比較を計算的に決定する API」はまだ別判断にしている。この分離は良い。

## 10. `Equiv of overlaps` も残しているのが良い

```lean id="equiv-overlaps"
theorem equiv_of_forall_overlaps
    {x y : DkReal}
    (hoverlap : ∀ n, (x.interval n).Overlaps (y.interval n)) :
    Equiv x y
```

今回の totality 本体では、overlap branch を使わずに済んでいる。
しかしこの補題を残したのは正解じゃ。

これは今後、

```text id="overlap-use"
persistent intersection
Equiv の幾何的特徴づけ
semantic bridge での同値性検証
```

に使える。

三分岐の Merge 概念は、証明上は不要になったが、理論説明としてはまだ重要じゃ。

## 11. docs 更新も非常に良い

文書側も現状に同期している。

```text id="docs-status"
totality is proved internally
Std.Total is exported
LinearOrder is still deferred
canonical order is independent
semantic bridge is cross-check
```

この整理はかなり良い。

特に `DkNNRealQ-Totality-Research.md` が、pre-implementation report から implemented report に更新されているのが良い。
「No abstract HasBigGapTotality axiom was needed」と書いている点も重要じゃ。

これは DkMath としてかなり強い主張になる。

```text id="no-axiom"
新しい比較公理なし
Real 評価なし
NNReal 評価なし
有理区間の入れ子性だけで totality
```

この形は美しい。

## 12. ひとつ注意点

`le_total_repr` は全 `DkReal` representation に対して成立している。
つまり非負 wrapper に限らず、入れ子有理区間表現一般で totality が出ている。

これは良い一方で、順序定義が lower endpoint defect であることに強く依存している。
将来、signed DkReal や一般 multiplication を入れるときも、この totality はそのまま使える可能性が高いが、ordered ring 的な構造とは別問題じゃ。

また、`LinearOrder` instance はまだ保留で正解。
`Std.Total` は totality の証明を提供するが、`LinearOrder` を入れると、比較可能性だけでなく標準 API と決定可能性の設計が絡む。ここは次の独立検証でよい。

## 13. 現在の到達点

これで `DkNNRealQ` はこうなった。

```text id="current-summit"
DkNNRealQ:
  CommSemiring
  PartialOrder
  IsOrderedRing
  Std.Total (· ≤ ·)
  zero_le
  add_le_add
  mul_le_mul
  pow_le_pow
```

数学的には、

$$
\boxed{\text{DkNNRealQ は、全比較可能な順序付き非負計算可能実数商型として閉じた。}}
$$

ただし、

```text id="not-yet"
direct LinearOrder
canonical order
strict ordered structure
semantic equivalence with NNReal
completeness
```

はまだ未主張。
この線引きも正しい。

## 14. 最終判定

今回の差分は **合格**、しかもかなり大きい節目じゃ。

```text id="review-result"
良い点:
  totality を Real / NNReal なしで証明した
  左分離あり / 左分離なし の二分岐に圧縮した
  defect を width で押さえる証明が非常に強い
  GapInterval overlap 補題も整備した
  quotient へ totality を持ち上げた
  Std.Total に留め、LinearOrder は保留した
  canonical order と semantic bridge を独立課題として残した
  docs が実装済み状態へ同期している

次の課題:
  LinearOrder instance を入れるかの設計判断
  canonical order \(x\le y \leftrightarrow \exists z,\ y=x+z\) の検証
  strict order の設計
  BridgeNNReal / BridgeReal による意味論 cross-check
```

うむ。
これは本当に強い。DkMath の Big/Core/Gap 直感が、単なる比喩ではなく、Lean が認める有理区間幾何として閉じた。
`DkNNRealQ` の Route B は、代数、順序、単調性、そして totality まで到達した。これは十分に「登頂」と呼べる節目じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 21ea0a94..0d17d099 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -35,13 +35,13 @@ limit in Mathlib's `Real` or `NNReal` is selected here.
 `DkNNRealQ`. Addition, nonnegative multiplication, and natural powers are
 monotone, and zero is least.
 
-[TODO: totality] Prove totality internally from nested-interval geometry:
-eventual strict left separation, eventual strict right separation, or
-persistent overlap. The first two branches give one order direction; the
-overlap branch gives `Equiv`.
+Totality is proved internally from nested-interval geometry. If a finite
+strict left separation is witnessed, it persists. Otherwise the reverse order
+defect is bounded by a vanishing interval width.
 
-[TODO: linear-order] Install no `LinearOrder` or linear ordered semiring API
-until representative totality has been proved and lifted through the quotient.
+[TODO: linear-order] Decide whether the now-proved quotient totality should be
+packaged as a direct classical `LinearOrder`, or retained as `PartialOrder`
+plus `Std.Total` so that decidable comparison remains an explicit choice.
 
 [TODO: canonical-order] Treat `x ≤ y ↔ ∃ z, y = x + z` as an independent
 problem. It is not a consequence of the current ordered-semiring compatibility
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean b/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean
index da7a036b..552fdd47 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean
@@ -31,8 +31,8 @@ order, and zero is the least quotient value. `DkReal.Order` packages these
 facts as Mathlib's semiring-level `IsOrderedRing` predicate. Canonical,
 strict, and linear order structures remain unclaimed.
 
-[TODO: totality] Prefer an internal proof through persistent interval
-separation/overlap before importing a semantic linear order.
+`DkReal.Order` proves totality internally through finite separation or a
+vanishing-width bound and exports `Std.Total (· ≤ ·)`.
 
 [TODO: semantic-bridge] A semantic map to Mathlib's `NNReal` should be placed in a separate
 bridge module and proved to preserve zero, one, addition, multiplication,
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/Interval.lean b/lean/dk_math/DkMath/Analysis/DkReal/Interval.lean
index 0f4dff4c..1c3f559a 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/Interval.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/Interval.lean
@@ -150,17 +150,52 @@ positive rational gap between the interval lying on the left and the interval
 lying on the right. In the totality design this is the comparison Gap inside
 the hull, or "comparison Big", containing both intervals.
 
-[TODO: totality/interval] Prove:
-
-* `separation I J = 0` iff `I.lo ≤ J.hi ∧ J.lo ≤ I.hi`;
-* strict left separation and strict right separation are mutually exclusive;
-* shrinking both intervals cannot decrease a positive separation.
+The overlap characterization below is the finite comparison lemma used by the
+totality proof.
 -/
 
 /-- Nonnegative separation between two closed rational intervals. -/
 def separation (I J : GapInterval) : ℚ :=
   max 0 (max (I.lo - J.hi) (J.lo - I.hi))
 
+/-- Two closed rational intervals overlap when neither lies strictly beyond the other. -/
+def Overlaps (I J : GapInterval) : Prop :=
+  I.lo ≤ J.hi ∧ J.lo ≤ I.hi
+
+/-- Overlapping intervals have zero separation. -/
+theorem separation_eq_zero_of_overlaps
+    {I J : GapInterval} (h : I.Overlaps J) :
+    I.separation J = 0 := by
+  rcases h with ⟨hleft, hright⟩
+  unfold separation
+  apply max_eq_left
+  exact max_le
+    (sub_nonpos.mpr hleft)
+    (sub_nonpos.mpr hright)
+
+/-- Zero separation implies overlap of the two closed intervals. -/
+theorem overlaps_of_separation_eq_zero
+    {I J : GapInterval} (h : I.separation J = 0) :
+    I.Overlaps J := by
+  have hleft : I.lo - J.hi ≤ 0 := by
+    calc
+      I.lo - J.hi ≤ max (I.lo - J.hi) (J.lo - I.hi) := le_max_left _ _
+      _ ≤ I.separation J := le_max_right _ _
+      _ = 0 := h
+  have hright : J.lo - I.hi ≤ 0 := by
+    calc
+      J.lo - I.hi ≤ max (I.lo - J.hi) (J.lo - I.hi) := le_max_right _ _
+      _ ≤ I.separation J := le_max_right _ _
+      _ = 0 := h
+  constructor
+  · exact sub_nonpos.mp hleft
+  · exact sub_nonpos.mp hright
+
+/-- Separation vanishes exactly when the two closed intervals overlap. -/
+theorem separation_eq_zero_iff_overlaps (I J : GapInterval) :
+    I.separation J = 0 ↔ I.Overlaps J :=
+  ⟨overlaps_of_separation_eq_zero, separation_eq_zero_of_overlaps⟩
+
 /-- Interval separation is nonnegative. -/
 theorem separation_nonneg (I J : GapInterval) : 0 ≤ I.separation J :=
   le_max_left _ _
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/Order.lean b/lean/dk_math/DkMath/Analysis/DkReal/Order.lean
index 4637bed7..5918b667 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/Order.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/Order.lean
@@ -50,16 +50,14 @@ representation layer. Here "comparison Big" means the hull containing the two
 stage intervals; it is an explanatory geometric construction, not the
 algebraic `DkMath.CosmicFormula.CoreBeamGap.Big`.
 
-[TODO: totality/interval] Add endpoint lemmas characterizing zero separation
-as overlap and proving that strict left or right separation persists under
-nested refinement.
+The overlap characterization, persistence lemmas, representative totality,
+and quotient totality are implemented below. Lean accepts the stronger
+two-branch proof: either a finite left separation is witnessed, or the reverse
+defect is bounded at every stage by the first interval's width.
 
-[TODO: totality/representation] Prove that persistent overlap implies `Equiv`,
-and that one witnessed strict separation implies the corresponding `Le`.
-
-[TODO: totality/quotient] Combine the three cases into representative totality,
-lift it to `DkNNRealQ`, and only then consider a `LinearOrder` or linear ordered
-semiring API.
+[TODO: linear-order] Decide whether to install a direct `LinearOrder` instance
+or expose totality through `Std.Total` while keeping decidability and classical
+comparison choices explicit.
 
 [TODO: totality/alternative] Keep a semantic `NNReal` proof as an independent
 cross-check, not as a dependency of the computable order core.
@@ -102,6 +100,16 @@ limit; it compares only rational Core observations against a shrinking Gap.
 def Le (x y : DkMath.Analysis.DkReal) : Prop :=
   Filter.Tendsto (orderDefect x y) Filter.atTop (nhds 0)
 
+/-- At stage `n`, the interval for `x` lies strictly to the left of that for `y`. -/
+def LeftSeparatedAt
+    (x y : DkMath.Analysis.DkReal) (n : ℕ) : Prop :=
+  (x.interval n).hi < (y.interval n).lo
+
+/-- At stage `n`, the interval for `y` lies strictly to the left of that for `x`. -/
+def RightSeparatedAt
+    (x y : DkMath.Analysis.DkReal) (n : ℕ) : Prop :=
+  (y.interval n).hi < (x.interval n).lo
+
 /-!
 ## II. Preorder and extensional equality
 
@@ -211,6 +219,99 @@ theorem le_congr
     exact le_trans (equiv_le hxx')
       (le_trans hx'y' (equiv_le (equiv_symm hyy')))
 
+/-!
+## III. Finite separation and total orientation
+
+Nestedness turns one finite strict separation into a permanent orientation.
+If no left separation ever appears, the reverse defect is bounded by the
+width of `x`, so it vanishes. This closes representative totality without
+selecting a semantic real limit.
+-/
+
+/-- A witnessed left separation persists at every later approximation stage. -/
+theorem leftSeparatedAt_persistent
+    {x y : DkMath.Analysis.DkReal} {n m : ℕ}
+    (hsep : LeftSeparatedAt x y n) (hnm : n ≤ m) :
+    LeftSeparatedAt x y m := by
+  unfold LeftSeparatedAt at *
+  exact (x.hi_antitone hnm).trans_lt
+    (hsep.trans_le (y.lo_mono hnm))
+
+/-- A witnessed right separation persists at every later approximation stage. -/
+theorem rightSeparatedAt_persistent
+    {x y : DkMath.Analysis.DkReal} {n m : ℕ}
+    (hsep : RightSeparatedAt x y n) (hnm : n ≤ m) :
+    RightSeparatedAt x y m :=
+  leftSeparatedAt_persistent hsep hnm
+
+/-- One finite left separation determines the asymptotic order `x ≤ y`. -/
+theorem le_of_leftSeparatedAt
+    {x y : DkMath.Analysis.DkReal} {n : ℕ}
+    (hsep : LeftSeparatedAt x y n) :
+    Le x y := by
+  have heq : ∀ᶠ m in Filter.atTop, orderDefect x y m = 0 := by
+    filter_upwards [Filter.eventually_ge_atTop n] with m hnm
+    have hpersist := leftSeparatedAt_persistent hsep hnm
+    unfold LeftSeparatedAt at hpersist
+    simp only [orderDefect]
+    exact max_eq_left (sub_nonpos.mpr
+      ((x.interval m).le_lo_hi.trans hpersist.le))
+  exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm heq) tendsto_const_nhds
+
+/-- One finite right separation determines the reverse asymptotic order. -/
+theorem le_of_rightSeparatedAt
+    {x y : DkMath.Analysis.DkReal} {n : ℕ}
+    (hsep : RightSeparatedAt x y n) :
+    Le y x :=
+  le_of_leftSeparatedAt hsep
+
+/-- Stagewise overlap of two representations implies vanishing separation. -/
+theorem equiv_of_forall_overlaps
+    {x y : DkMath.Analysis.DkReal}
+    (hoverlap : ∀ n, (x.interval n).Overlaps (y.interval n)) :
+    Equiv x y := by
+  unfold Equiv
+  have heq :
+      (fun n => (x.interval n).separation (y.interval n)) =
+        fun _ => (0 : ℚ) := by
+    funext n
+    exact GapInterval.separation_eq_zero_of_overlaps (hoverlap n)
+  rw [heq]
+  exact tendsto_const_nhds
+
+/--
+If `x` is never strictly left-separated from `y`, then `y ≤ x`.
+
+At each stage `y.lo ≤ x.hi`; hence the positive lower-Core excess of `y` over
+`x` is bounded by the width of `x`, which tends to zero.
+-/
+theorem le_of_not_exists_leftSeparatedAt
+    {x y : DkMath.Analysis.DkReal}
+    (hsep : ¬ ∃ n, LeftSeparatedAt x y n) :
+    Le y x := by
+  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
+    tendsto_const_nhds x.tendsto_width_zero
+    (fun n => le_max_left 0 _)
+    (fun n => by
+      have hnot : ¬ (x.interval n).hi < (y.interval n).lo := by
+        intro hn
+        exact hsep ⟨n, hn⟩
+      have hyx : (y.interval n).lo ≤ (x.interval n).hi :=
+        le_of_not_gt hnot
+      simp only [orderDefect, GapInterval.width]
+      apply max_le
+      · exact (x.interval n).width_nonneg
+      · linarith)
+
+/-- The asymptotic order on all `DkReal` representations is total. -/
+theorem le_total_repr (x y : DkMath.Analysis.DkReal) :
+    Le x y ∨ Le y x := by
+  classical
+  by_cases hsep : ∃ n, LeftSeparatedAt x y n
+  · obtain ⟨n, hn⟩ := hsep
+    exact Or.inl (le_of_leftSeparatedAt hn)
+  · exact Or.inr (le_of_not_exists_leftSeparatedAt hsep)
+
 /--
 The rational zero approximation is below every nonnegative representation.
 
@@ -230,7 +331,7 @@ theorem zero_le
   exact tendsto_const_nhds
 
 /-!
-## III. Ordered arithmetic
+## IV. Ordered arithmetic
 
 The arithmetic proofs control output defects by null input defects. Addition
 uses subadditivity; multiplication additionally uses uniform boundedness of
@@ -329,7 +430,7 @@ end DkMath.Analysis.DkReal
 namespace DkMath.Analysis.DkNNReal
 
 /-!
-## IV. Nonnegative wrapper order
+## V. Nonnegative wrapper order
 
 The wrapper carries all nonnegativity hypotheses needed by multiplication, so
 its public order lemmas have no proof arguments.
@@ -362,12 +463,16 @@ theorem mul_le_mul
   DkReal.mulNonneg_le_mulNonneg
     x.nonnegative y.nonnegative z.nonnegative w.nonnegative hxy hzw
 
+/-- The wrapper order is total because the underlying representation order is total. -/
+theorem le_total (x y : DkNNReal) : Le x y ∨ Le y x :=
+  DkReal.le_total_repr x.val y.val
+
 end DkMath.Analysis.DkNNReal
 
 namespace DkMath.Analysis.DkNNRealQ
 
 /-!
-## V. Quotient order and Mathlib hierarchy
+## VI. Quotient order and Mathlib hierarchy
 
 Congruence of representative order permits a quotient relation. Mutual order
 becomes quotient equality, while the arithmetic compatibility theorems supply
@@ -405,6 +510,16 @@ instance : PartialOrder DkNNRealQ where
     intro a b hab hba
     exact Quotient.sound (DkReal.equiv_of_le_of_le hab hba)
 
+/-- The quotient order is total. -/
+theorem le_total (x y : DkNNRealQ) : x ≤ y ∨ y ≤ x := by
+  refine Quotient.inductionOn₂ x y ?_
+  intro a b
+  exact DkNNReal.le_total a b
+
+/-- Standard totality witness for the quotient order. -/
+instance : Std.Total (α := DkNNRealQ) (· ≤ ·) where
+  total := le_total
+
 /-- Zero is the least value of the nonnegative quotient. -/
 theorem zero_le (x : DkNNRealQ) : 0 ≤ x := by
   refine Quotient.inductionOn x ?_
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index 032cddaa..99ccc471 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -105,8 +105,8 @@ Order:
   addition, multiplication, and natural-power monotonicity are proved
   zero is least
   IsOrderedRing packages semiring-level ordered compatibility
-  canonical, strict, and linear order structures remain open
-  investigate totality by persistent separation versus persistent overlap
+  totality is proved and exported through Std.Total
+  canonical, strict, and direct linear order structures remain open
   use a semantic bridge only as an independent cross-check
 
 BridgeNNReal / BridgeReal:
diff --git a/lean/dk_math/DkMath/Analysis/docs/DkMath.Analysis_Design_Draft_2026-06-19.md b/lean/dk_math/DkMath/Analysis/docs/DkMath.Analysis_Design_Draft_2026-06-19.md
index fb26c285..0af4303c 100644
--- a/lean/dk_math/DkMath/Analysis/docs/DkMath.Analysis_Design_Draft_2026-06-19.md
+++ b/lean/dk_math/DkMath/Analysis/docs/DkMath.Analysis_Design_Draft_2026-06-19.md
@@ -51,9 +51,9 @@ The next independent tasks are:
    lower-endpoint defect, proves invariance under `Equiv`, and installs a
    `PartialOrder` on `DkNNRealQ`. Addition, multiplication, and natural powers
    are monotone, and zero is least. Mathlib's semiring-level `IsOrderedRing`
-   predicate is installed. The leading totality route is now the internal
-   trichotomy of persistent left separation, persistent right separation, and
-   persistent overlap. Canonical order remains independent.
+   predicate is installed. Totality is proved internally from persistent
+   separation and a vanishing-width bound, and exported through `Std.Total`.
+   Canonical order and a direct `LinearOrder` instance remain independent.
 2. **Semantic evaluation.** In a separate `BridgeNNReal.lean` or
    `BridgeReal.lean`, extract the unique real point of a nested interval
    representation and prove independence from representatives.
diff --git a/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-CommSemiring-Checkpoint.md b/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-CommSemiring-Checkpoint.md
index fe019890..021e932b 100644
--- a/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-CommSemiring-Checkpoint.md
+++ b/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-CommSemiring-Checkpoint.md
@@ -56,11 +56,12 @@ The implementation establishes:
 - zero as the least quotient value;
 - monotonicity of addition and nonnegative multiplication;
 - monotonicity of natural powers;
-- Mathlib's semiring-level `IsOrderedRing DkNNRealQ`.
+- Mathlib's semiring-level `IsOrderedRing DkNNRealQ`;
+- totality through `Std.Total (· ≤ ·)`.
 
 This checkpoint does not establish:
 
-- totality or a `LinearOrder`;
+- a direct `LinearOrder` instance;
 - canonical order by additive differences;
 - strict ordered-semiring structure;
 - completeness;
@@ -73,9 +74,8 @@ This checkpoint does not establish:
 
 ### Totality
 
-The preferred internal route uses the finite geometry of nested closed
-intervals. For two representations, exactly one of the following explanatory
-states should control the proof:
+The internal proof uses the finite geometry of nested closed intervals.
+The explanatory states are:
 
 ```text
 SeparatedLeft:
@@ -88,9 +88,10 @@ Merge:
   neither separation occurs, so every stage overlaps and x ~ y.
 ```
 
-Nestedness makes either strict separation persistent. The Merge branch has
-stagewise separation zero and therefore gives `Equiv`. This is the current
-candidate for proving totality without evaluating into `Real`.
+Nestedness makes strict separation persistent. More strongly, if no left
+separation exists, the reverse order defect is bounded by the first
+representation's vanishing width. Totality is therefore proved without
+evaluating into `Real`.
 
 See
 [`DkNNRealQ-Totality-Research.md`](DkNNRealQ-Totality-Research.md).
diff --git a/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-Totality-Research.md b/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-Totality-Research.md
index 802ede9e..3a7700e1 100644
--- a/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-Totality-Research.md
+++ b/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-Totality-Research.md
@@ -2,7 +2,8 @@
 
 ## Status
 
-This is a pre-implementation report. No `LinearOrder` is claimed.
+The internal totality experiment is implemented and accepted by Lean. No
+direct `LinearOrder` is claimed yet.
 
 The current computable core already provides:
 
@@ -17,7 +18,7 @@ DkNNRealQ:
   pow_le_pow
 ```
 
-The remaining question is whether every pair satisfies
+Every pair now satisfies
 
 ```lean
 x <= y ∨ y <= x.
@@ -53,8 +54,8 @@ this protrusion disappears as precision increases.
 ## Main Finding
 
 The workspace contains a stronger route than selecting the sign of an
-unspecified real limit. Nested interval geometry suggests the following
-trichotomy.
+unspecified real limit. Nested interval geometry gives the following
+comparison.
 
 ### Separated Left
 
@@ -104,40 +105,43 @@ This route uses only:
 
 It does not require evaluation into Mathlib's `Real` or `NNReal`.
 
-## Proposed Lean Checkpoints
-
-The implementation should proceed in small lemmas.
+## Implemented Lean Checkpoints
 
 ```text
 GapInterval:
-  separation_eq_zero_iff_overlap
-  strict separation orientations are exclusive
+  Overlaps
+  separation_eq_zero_iff_overlaps
 
 DkReal:
-  leftSeparated persists under later stages
-  rightSeparated persists under later stages
-  Le of one witnessed left separation
-  Equiv of overlap at every stage
+  LeftSeparatedAt / RightSeparatedAt
+  leftSeparatedAt_persistent
+  rightSeparatedAt_persistent
+  le_of_leftSeparatedAt / le_of_rightSeparatedAt
+  equiv_of_forall_overlaps
+  le_of_not_exists_leftSeparatedAt
+  le_total_repr
 
 DkNNRealQ:
-  representative le_total
-  quotient le_total
-  LinearOrder decision only after verification
+  le_total
+  Std.Total (· <= ·)
 ```
 
-Suggested proposition names are provisional:
+No abstract `HasBigGapTotality` axiom was needed.
 
-```lean
-GapInterval.Overlaps
-DkReal.LeftSeparatedAt
-DkReal.RightSeparatedAt
-DkReal.le_of_leftSeparatedAt
-DkReal.equiv_of_forall_overlaps
-DkNNRealQ.le_total
+The final proof is stronger and shorter than the explanatory three-state
+picture:
+
+```text
+if exists n, x.hi(n) < y.lo(n):
+  x <= y
+else:
+  y.lo(n) <= x.hi(n) for every n
+  defect(y,x,n) <= width(x,n)
+  therefore y <= x
 ```
 
-Avoid adding an abstract `HasBigGapTotality` axiom while the concrete interval
-proof remains available.
+The Merge state remains useful for interpretation and is represented by
+`equiv_of_forall_overlaps`.
 
 ## Relation To The Hint
 
@@ -148,10 +152,10 @@ The hint correctly identifies:
 - positive and negative directed Core defects;
 - the Merge state.
 
-The refinement from workspace exploration is that totality may not require a
+The refinement from workspace exploration was correct: totality requires no
 new sign-selection principle. Nestedness turns a finite witnessed separation
-into a permanent orientation, while absence of either separation forces
-stagewise overlap.
+into a permanent orientation, while absence of left separation bounds the
+reverse defect by a vanishing width.
 
 ## Semantic Cross-Check
 
````
`````
