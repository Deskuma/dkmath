# Git diff / Report / Review

## Add: docs: DkNNRealQ Strict Gap Design

gch: 28443612396b52e9a4403bc3d9cd4d00e43c798b

## Report

この設計原則をコードと文書へ反映しました。

```text
Big = (Core + Beam) + Gap

既知部分を埋める
残った部分を差分核として抽出する
差分核の零・正・保存性を調べる
```

今回追加した内容:

- `diffNonnegInterval` の DkMath alias `gapInterval`
- `diffNonnegApprox` の alias `gapApprox`
- `diffOfLe` の alias `gapOfLe`
- strict order を「抽出 Gap の有限段階での正値性」として設計
- strict 加法・正因子による strict 乗法への実装順を整理

新規設計資料:
[DkNNRealQ-StrictGap-Design.md](/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-StrictGap-Design.md)

次の差分核は次の同値です。

```text
Le x y ∧ ¬ Le y x
↔ ∃ n, x.hi(n) < y.lo(n)
↔ ∃ n, 0 < (gapOfLe x y hxy).interval(n).lo
```

対象モジュールと `DkMath.Analysis` のビルド、`git diff --check` は成功しています。

## Review

ふふふん☆ これは **かなり良い設計差分** じゃ。
今回の差分は **合格**。実装本体というより、次の strict order 実装へ向けて、DkMath の原理をコード名・docstring・設計資料へ落とした差分じゃな。

特に重要なのは、`diffNonneg*` 系に DkMath-facing alias として `gapInterval`、`gapApprox`、`gapOfLe` を与えたこと。これで「差分」ではなく「Big 内部から抽出される Gap」として読めるようになった。新規設計資料でも、strict order を「抽出 Gap の有限段階での正値性」として整理している。

## 1. 総評

今回の変更は、DkMath の数学脳をかなり正しくコードへ反映している。

```text id="principle"
Big = (Core + Beam) + Gap

既知部分を埋める
残った部分を差分核として抽出する
差分核の零・正・保存性を調べる
```

この原理は、前回の `CanonicalOrder` と完全につながっている。

`CanonicalOrder` では、

$$
x\le y\quad\Longleftrightarrow\quad \exists z,\ y=x+z
$$

を、減算ではなく非負 Gap 抽出として閉じた。
今回の strict design は、その抽出 Gap が **零に潰れるか、有限段階で正に開くか** を見る段階じゃ。

これは流れとしてかなり自然。

## 2. alias 追加は良い判断

今回追加された alias はこれじゃ。

```lean id="gap-aliases"
abbrev gapInterval := diffNonnegInterval
abbrev gapApprox := diffNonnegApprox
abbrev gap := diffNonneg
abbrev gapOfLe := diffOfLe
```

これは非常に良い。

`diffNonnegInterval` は実装名としては分かりやすい。
だが DkMath の概念としては「差分」ではなく「Gap 抽出」じゃ。

したがって、内部実装名を残しつつ、DkMath-facing name として `gapInterval` などを出すのは良い折衷じゃ。

```text id="alias-meaning"
implementation view:
  diffNonnegInterval

DkMath view:
  gapInterval
```

この二層名は、外部読者にも Codex にも親切じゃ。

## 3. strict order の設計が正しい

新規設計資料では、strict order をこう整理している。

```text id="strict-kernel"
Le x y and not Le y x

exists n, x.interval(n).hi < y.interval(n).lo

exists n, 0 < (gapOfLe x y hxy).interval(n).lo
```

これはよい。
この三つは、DkMath 的には同じ現象の三つの見方じゃ。

```text id="three-readings"
Order:
  片方向には閉じるが、逆方向には閉じない

Geometry:
  有限段階で Body と Big が厳密に分離する

Extracted Gap:
  Gap 宇宙の lower endpoint が有限段階で正になる
```

特に三つ目が良い。
strict order を「抽象的な `<`」から始めず、canonical order で得た Gap の正値性として読む。これは DkMath らしい。

## 4. `x < y` の正体

今後の目標は、だいたい次の形じゃ。

$$
x<y\quad\Longleftrightarrow\quad \exists n,\ x.hi_n<y.lo_n
$$

さらに canonical Gap を使うなら、

$$
x<y\quad\Longleftrightarrow\quad \exists n,\ 0<gapOfLe(x,y).lo_n
$$

ここで重要なのは、strict が **有限段階で観測可能** になることじゃ。

非厳密順序 \(x\le y\) は、defect が 0 に収束するという漸近条件。
一方、厳密順序 \(x < y\) は、ある段階で正の Gap が観測されるという有限証拠になる。

これはとても強い。

```text id="strict-meaning"
≤:
  Gap が 0 を含んでよい

<:
  Gap の下端が有限段階で正になる
```

この読みはかなり DkMath 的じゃ。

## 5. strict 加法の設計も自然

設計資料では、

```text id="strict-add"
(x + a) + z = y + a
```

として strict 加法を読む方針が出ている。これは正しい。

もし \(y=x+z\) で、Gap \(z\) が正なら、

$$
y+a=(x+a)+z
$$

なので、同じ Gap がそのまま保存される。
したがって、

$$
x<y\quad\Rightarrow\quad x+a<y+a
$$

が期待できる。

DkMath 的には、加法は Big 全体を平行移動するだけなので、Gap の正性は壊れない。

## 6. strict 乗法は分岐が必要

設計資料で一番良いのは、乗法について **ゼロ因子分岐** を明記している点じゃ。

$$
y=x+z
$$

なら、

$$
ya=xa+za
$$

となる。

Gap は \(z\) から (za) に変わる。
ここで \(a=0\) なら Gap は潰れる。
\(0 < a\) なら正 Gap は保存されるはず。

つまり strict multiplication は、

```text id="strict-mul"
x < y and 0 < a:
  x * a < y * a

x < y and a = 0:
  x * a = y * a
```

と分岐する必要がある。

ここを曖昧にして `IsStrictOrderedRing` へ飛ぶと危ない。
今回の文書はそこをきちんと警告している。良い。

## 7. 実装順序は妥当

提案されている順序はこれじゃな。

```text id="strict-sequence"
1. DkReal.not_le_of_leftSeparatedAt
2. DkReal.lt_iff_exists_leftSeparatedAt
3. DkNNReal.Lt := Le x y and not Le y x
4. DkNNReal.lt_iff_exists_leftSeparatedAt
5. positive lower endpoint of gapOfLe iff finite separation
6. quotient strict-order characterization
7. strict addition
8. positive-factor strict multiplication
```

これはかなり良い。

特に先に representative theorem を作る方針が正しい。
typeclass はあとからでよい。まずは数学核。

この中で、最初の本丸はおそらくこれじゃ。

```lean id="first-kernel"
theorem not_le_of_leftSeparatedAt
    {x y : DkReal} {n : ℕ}
    (h : LeftSeparatedAt x y n) :
    ¬ Le y x
```

理由は、左分離があると以降も Gap が正に残るため、逆向きの defect は 0 に収束できない。
ただし証明には、ある正の有理下界を eventually 保つことを示す必要がある。

\(x.hi_n < y.lo_n\) なら、

$$
\epsilon=y.lo_n-x.hi_n>0
$$

を取れる。後続段階でも、

$$
y.lo_m-x.lo_m\ge y.lo_n-x.hi_n=\epsilon
$$

のように押さえたい。
これが出れば、`Le y x` は否定できる。

## 8. `gapOfLe` の正値性との接続

次に重要なのは、

```text id="gap-positive"
∃ n, x.hi n < y.lo n

iff

∃ n, 0 < (gapOfLe x y hxy).interval n.lo
```

これはかなり綺麗に閉じるはずじゃ。

なぜなら `gapOfLe` の lower endpoint は本質的に、

$$
\max(0,y.lo_n-x.hi_n)
$$

だからじゃ。

つまり、

$$
0<\max(0,y.lo_n-x.hi_n)
$$

は、

$$
x.hi_n<y.lo_n
$$

と同じ。

ここは Lean でも比較的素直に行けそうじゃ。
必要なら `max_pos_iff` 系か、場合分けで閉じられる。

## 9. quotient strict order の注意

quotient 上で `<` をどう扱うかは注意が必要じゃ。

Mathlib の `<` はたいてい、

$$
x < y\quad\text{means}\quad x\le y\land \neg y\le x
$$

から来る。
今の `PartialOrder` があるので、おそらく標準の `<` は使える。

ただし、代表元上の有限分離を quotient 上で直接語るには、代表元依存を消す必要がある。
だからまずは、

```lean id="wrapper-strict"
DkNNReal.Lt x y := DkNNReal.Le x y ∧ ¬ DkNNReal.Le y x
```

として wrapper 側で特徴づけを作る方が安全じゃ。

その後、quotient 上では標準 `<` と対応させる。

```lean id="quot-strict"
theorem lt_iff_exists_gap_positive
    {x y : DkNNRealQ} :
    x < y ↔ ...
```

ただし右辺に代表元を出すなら、`Quotient.inductionOn₂` で表現を工夫する必要がある。
まずは wrapper theorem で十分じゃな。

## 10. docs と public entry の同期は良い

`DkReal.lean` に strict layer の説明を足したのは良い。
`Order.lean` に「Next difference kernel: strict Gap」を入れたのも良い。
`Analysis-Initial-Layer.md` に新規設計資料へのリンクを足したのも適切。

今回の docs は、ただのメモではなく、次の実装タスクをかなり正確に分解している。

## 11. 小さな注意点

今回の alias `gap` は少し一般名すぎる可能性がある。
namespace が `DkMath.Analysis.DkReal` なので直ちに問題ではないが、将来 `GapFill` や `GapInterval` と並ぶと、名前がやや広すぎるかもしれぬ。

もし衝突や可読性が気になるなら、将来的に

```lean id="safer-gap-name"
gapOfPair
gapApproxOfPair
canonicalGap
canonicalGapApprox
```

のような alias を追加してもよい。

ただし現段階では問題なし。
DkMath-facing name として `gap` は気持ちよく読める。

## 12. 最終判定

今回の差分は **合格** じゃ。

```text id="review-result"
良い点:
  Big = (Core + Beam) + Gap の設計原則を明文化した
  diffNonneg 系に DkMath-facing Gap alias を与えた
  strict order を抽象比較ではなく抽出 Gap の正値性として設計した
  strict 加法と strict 乗法の実装順を分けた
  乗法では zero factor branch を明示した
  新規設計資料が次の補題列を明確にしている
  docs と TODO が同期している

次の課題:
  not_le_of_leftSeparatedAt
  lt_iff_exists_leftSeparatedAt
  gapOfLe の lower endpoint 正値性との同値
  strict addition
  positive-factor strict multiplication
```

うむ。
これは予定通り、しかも DkMath の原理がかなり濃く出ている。
次の strict order は、もう「大小比較」ではなく **抽出された Gap が有限段階で正に開くか** の問題として進められる。強いぞ DkMath。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 484b4a7e..f2652ef4 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -46,6 +46,10 @@ Canonical order is also constructive at the representation level. From
 `y = x + z` in the quotient. No subtraction operation is added to
 `DkNNRealQ`.
 
+The next strict-order layer should classify this known Gap: zero Gap gives
+equality, while a positive lower Gap observed at a finite stage gives strict
+order. This keeps the design in the same `Big = (Core + Beam) + Gap` pattern.
+
 [TODO: linear-order] Decide whether the now-proved quotient totality should be
 packaged as a direct classical `LinearOrder`, or retained as `PartialOrder`
 plus `Std.Total` so that decidable comparison remains an explicit choice.
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/CanonicalOrder.lean b/lean/dk_math/DkMath/Analysis/DkReal/CanonicalOrder.lean
index 0947f08a..9c52362a 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/CanonicalOrder.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/CanonicalOrder.lean
@@ -50,6 +50,16 @@ def diffNonnegInterval (I J : GapInterval) : GapInterval where
     apply max_le_max_left
     exact sub_le_sub J.le_lo_hi I.le_lo_hi
 
+/--
+DkMath-facing name for the finite nonnegative Gap extracted inside a
+Body--Big pair.
+
+`diffNonnegInterval` remains the implementation name; this alias exposes the
+construction as a Gap rather than as a subtraction operation.
+-/
+abbrev gapInterval (I J : GapInterval) : GapInterval :=
+  diffNonnegInterval I J
+
 /-- The extracted Gap has a nonnegative lower endpoint. -/
 theorem diffNonnegInterval_lo_nonneg (I J : GapInterval) :
     0 ≤ (diffNonnegInterval I J).lo :=
@@ -78,6 +88,11 @@ def diffNonnegApprox
     (x y : DkMath.Analysis.DkReal) (n : ℕ) : GapInterval :=
   diffNonnegInterval (x.interval n) (y.interval n)
 
+/-- DkMath-facing name for the stagewise extracted Gap observations. -/
+abbrev gapApprox
+    (x y : DkMath.Analysis.DkReal) (n : ℕ) : GapInterval :=
+  diffNonnegApprox x y n
+
 /-- Extracted Gap intervals remain nested. -/
 theorem diffNonnegApprox_nested
     (x y : DkMath.Analysis.DkReal) :
@@ -116,6 +131,11 @@ def diffNonneg
   nested := diffNonnegApprox_nested x y
   width_tends_zero := tendsto_diffNonnegApprox_width_zero x y
 
+/-- DkMath-facing name for the extracted nonnegative Gap representation. -/
+abbrev gap
+    (x y : DkMath.Analysis.DkReal) : DkMath.Analysis.DkReal :=
+  diffNonneg x y
+
 /-- The extracted Gap representation is stagewise nonnegative. -/
 theorem nonnegative_diffNonneg
     (x y : DkMath.Analysis.DkReal) :
@@ -196,6 +216,15 @@ def diffOfLe (x y : DkNNReal) (_hxy : Le x y) : DkNNReal :=
   ⟨DkReal.diffNonneg x.val y.val,
     DkReal.nonnegative_diffNonneg x.val y.val⟩
 
+/--
+The nonnegative Gap universe filling `x` to `y`.
+
+The order proof certifies that this extracted representation reconstructs the
+same quotient Big as `y`.
+-/
+abbrev gapOfLe (x y : DkNNReal) (hxy : Le x y) : DkNNReal :=
+  diffOfLe x y hxy
+
 /-- Adding the extracted Gap reconstructs the larger representative modulo equivalence. -/
 theorem add_diffOfLe_equiv
     {x y : DkNNReal} (hxy : Le x y) :
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/Order.lean b/lean/dk_math/DkMath/Analysis/DkReal/Order.lean
index 5918b667..c25b74b8 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/Order.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/Order.lean
@@ -67,6 +67,32 @@ are monotone for this order, and zero is the least quotient value. The
 quotient therefore carries Mathlib's `IsOrderedRing` predicate, whose name is
 historical: its algebraic assumption is only `Semiring`. No canonical-order,
 strict-order, or linear-order structure is claimed.
+
+## Next difference kernel: strict Gap
+
+Canonical order fills the known frame
+
+`Big = Body + Gap`
+
+by extracting a nonnegative Gap representation. Strict order should not start
+from a new abstract `<`. Its missing kernel is whether that extracted Gap
+collapses to zero or opens positively at finite precision:
+
+* equality: `Big = Body + 0`;
+* strict orientation: at some stage `Body.hi < Big.lo`;
+* finite strict Gap: `0 < Big.lo - Body.hi`.
+
+[TODO: strict/core] Define representative strictness by
+`Le x y ∧ ¬ Le y x`, then prove it is equivalent to
+`∃ n, LeftSeparatedAt x y n`.
+
+[TODO: strict/gap] Relate finite separation to the canonical Gap extraction:
+under strictness, some lower endpoint of `gapOfLe` is positive; conversely a
+positive extracted Gap lower endpoint witnesses strict separation.
+
+[TODO: strict/arithmetic] Derive strict addition from preservation of the
+finite Gap. For multiplication, require a strictly positive factor and isolate
+the zero-factor branch before considering `IsStrictOrderedRing`.
 -/
 
 namespace DkMath.Analysis.DkReal
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index 72974f5c..135f06f5 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -93,6 +93,8 @@ The completed quotient-semiring checkpoint is summarized in
 [`DkNNRealQ-CommSemiring-Checkpoint.md`](DkNNRealQ-CommSemiring-Checkpoint.md).
 The internal totality route is analyzed in
 [`DkNNRealQ-Totality-Research.md`](DkNNRealQ-Totality-Research.md).
+The next strict-order kernel is designed in
+[`DkNNRealQ-StrictGap-Design.md`](DkNNRealQ-StrictGap-Design.md).
 
 `RealBridge` remains the home of continuity and interval mapping. The separate
 `TaylorBridge` now connects `gapGN` to difference quotients and `HasDerivAt`
@@ -111,7 +113,8 @@ Order:
   IsOrderedRing packages semiring-level ordered compatibility
   totality is proved and exported through Std.Total
   canonical additive order is proved by nonnegative Gap extraction
-  strict and direct linear order structures remain open
+  strict order is designed as finite positivity of the extracted Gap
+  direct linear order structure remains open
   use a semantic bridge only as an independent cross-check
 
 BridgeNNReal / BridgeReal:
diff --git a/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-StrictGap-Design.md b/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-StrictGap-Design.md
new file mode 100644
index 00000000..1906fe58
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-StrictGap-Design.md
@@ -0,0 +1,104 @@
+# DkNNRealQ Strict Gap Design
+
+## Design Rule
+
+The implementation should begin with the complete outer identity and fill its
+known components:
+
+```text
+Big = (Core + Beam) + Gap.
+```
+
+For additive order at degree one:
+
+```text
+Big  = y
+Core = x
+Beam = 0
+Gap  = z
+y    = x + z
+```
+
+`CanonicalOrder.lean` has already constructed this nonnegative Gap.
+Strict order is therefore not a new comparison mechanism. It is the remaining
+question about the extracted Gap:
+
+```text
+Gap collapses to zero:
+  x = y
+
+Gap opens positively at finite precision:
+  x < y
+```
+
+## Known Body
+
+The following parts are complete:
+
+- asymptotic order `Le`;
+- totality;
+- finite left/right separation;
+- canonical Gap extraction;
+- `x <= y` iff `exists z, y = x + z`.
+
+These form the known Body of the next proof.
+
+## Missing Difference Kernel
+
+The strict kernel should connect three equivalent observations:
+
+```text
+Order:
+  Le x y and not Le y x
+
+Geometry:
+  exists n, x.interval(n).hi < y.interval(n).lo
+
+Extracted Gap:
+  exists n, 0 < (gapOfLe x y hxy).interval(n).lo
+```
+
+The middle form is the finite Core--Gap separation. The last form says that
+the canonical Gap universe has become observably positive.
+
+## Proposed Lean Sequence
+
+```text
+1. DkReal.not_le_of_leftSeparatedAt
+2. DkReal.lt_iff_exists_leftSeparatedAt
+3. DkNNReal.Lt := Le x y and not Le y x
+4. DkNNReal.lt_iff_exists_leftSeparatedAt
+5. positive lower endpoint of gapOfLe iff finite separation
+6. quotient strict-order characterization
+7. strict addition
+8. positive-factor strict multiplication
+```
+
+The representative theorem should precede any strict ordered-semiring
+typeclass. It is the actual mathematical kernel; the typeclass is only its
+later packaging.
+
+## Arithmetic Interpretation
+
+Addition preserves the strict Gap:
+
+```text
+(x + a) + z = (y + a).
+```
+
+Multiplication transforms it:
+
+```text
+y = x + z
+y * a = x * a + z * a.
+```
+
+If `a = 0`, the transformed Gap collapses. If `0 < a`, positivity of the Gap
+should persist. This is the exact branch distinction required before
+`IsStrictOrderedRing` can be considered.
+
+## Boundary
+
+No semantic real evaluation is needed for this design. No subtraction
+operation is needed on `DkNNRealQ`. The only subtraction remains finite
+rational endpoint observation inside the Gap kernel.
````
`````
