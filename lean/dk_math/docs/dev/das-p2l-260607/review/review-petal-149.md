# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureAccounting

gch: b121d3683c5fb18cf93e25dc8d334308969b8214

## Report

Checkpoint 148 完了です。

[PressureAccounting.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean) に、単一区間の theorem 群から一段上げて、carrier と finite-list budget を追加しました。

追加した主なもの:

```lean
SourcePressureIntervalNetDrop
SourcePressureAccountedInterval
sourcePressureAccountedInterval_of_intervalPulseAddress
sourcePressureAccountedInterval_list_sum_le_neg_length
sourcePressureAccountedInterval_list_sum_neg_of_nonempty
NatIntervalsDisjoint
SourcePressureAccountedIntervalsDisjoint
```

リスト予算の本体も通っています。

```lean
(L.map (fun A =>
  SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤
    -((L.length : ℕ) : ℤ)
```

これは「明示的に与えた accounted interval のリスト」だけに対する予算定理です。disjointness、coverage、union accounting、Collatz convergence は主張していません。optional の disjointness は語彙と symmetry だけを入れました。

レポートも作成済みです:
[report-petal-148.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-148.md)

検証済みです。

```text
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
git diff --check
```

`PressureAccounting.lean` に `sorry` はありません。既存の `ZsigmondyCyclotomicResearch` warning は今回差分とは無関係です。

## Review

## 結論

うむ、Checkpoint 148 は **採用・かなり良い進展** じゃ 👍️
今回は、こちらが狙っていた **carrier 化 + finite-list budget** まで到達しておる。

追加された中心は次の 7 つじゃ。

```lean
SourcePressureIntervalNetDrop
SourcePressureAccountedInterval
sourcePressureAccountedInterval_of_intervalPulseAddress
sourcePressureAccountedInterval_list_sum_le_neg_length
sourcePressureAccountedInterval_list_sum_neg_of_nonempty
NatIntervalsDisjoint
SourcePressureAccountedIntervalsDisjoint
```

特に本丸はこれじゃな。

```lean
sourcePressureAccountedInterval_list_sum_le_neg_length
```

明示的に与えた accounted interval のリスト \(L\) に対して、

$$
\sum_{A\in L}\mathrm{NetDrop}(A)\le -|L|
$$

という有限予算が Lean で通った。これはかなり大きい。報告でも「disjointness、coverage、union accounting、Collatz convergence は主張していない」と明記されており、設計上の危険な飛躍も避けられておる。

## 実装内容の解説

今回、`SourcePressureIntervalNetDrop` が定義されたことで、これまで毎回書いていた有限和が名前を持った。

```lean
SourcePressureIntervalNetDrop n k r start len
```

これは、

$$
\sum_{i=0}^{len-1}\Delta(start+i)
$$

に相当する、明示区間の累積 net-drop じゃ。

次に `SourcePressureAccountedInterval` が入った。これは、単なる pulse address ではなく、次を持つ **会計済み区間** じゃ。

```text
start
len
0 < len
start margin > 0
after margin <= 0
accounting identity
```

つまり、この構造体は

$$
M(start+len)=M(start)+\mathrm{NetDrop}(start,len)
$$

を内部に持つ。
そのうえで、

$$
\mathrm{NetDrop}(start,len)<0
$$

$$
\mathrm{NetDrop}(start,len)\le -1
$$

$$
\mathrm{NetDrop}(start,len)\le -M(start)
$$

が carrier-level で取れるようになった。

これは「局所 pulse が負の会計単位になった」段階からさらに進んで、 **負の会計単位をリストとして合算できる** 段階じゃ。

## 一番重要な成果

今回の主成果は、やはりこれじゃ。

```lean
sourcePressureAccountedInterval_list_sum_le_neg_length
```

意味はこう。

```text
明示的に与えた accounted interval が m 個あるなら、
それらの interval net-drop の合計は高々 -m。
```

数式で言えば、

$$
\sum_{A\in L}\mathrm{NetDrop}(A)\le -#L
$$

これはまだ「軌道全体の下降」ではない。
しかし、 **pulse を数えれば数えるほど、会計上は負予算が積み上がる** ことを Lean が認めた、ということじゃ。

これは DkMath Collatz/PetalBridge のロードマップ上、とても良い石段じゃよ。

## 良い点

## 1. carrier 化が成功している

`SourcePressureAccountedInterval` は薄く、過剰な意味を持っていない。
maximal run でも、coverage object でも、union decomposition でもない。

この薄さがよい。

```text
明示された interval が、
正の開始 margin と非正の after margin を持ち、
telescoping accounting を満たす。
```

それだけを持つ。だから安全に使い回せる。

## 2. interval-pulse address から carrier へ橋がある

```lean
sourcePressureAccountedInterval_of_intervalPulseAddress
```

が入ったので、

```text
interval pulse address
  -> accounted interval
  -> finite-list budget
```

の道が通った。

これは良い。
以前の `PressureFrontier` 側の住所層が、ちゃんと `PressureAccounting` 側の会計層へ接続された。

## 3. disjointness を語彙だけに留めている

`NatIntervalsDisjoint` と `SourcePressureAccountedIntervalsDisjoint` が追加され、symmetry だけが入った。
しかし、そこから coverage や union accounting は出していない。

これも正しい。
disjointness は次の段階で必要になるが、ここで「だから全体を覆う」と言い始めると危険じゃ。

## 注意点

## 1. `noncomputable` は問題なし

`SourcePressureIntervalNetDrop` が `noncomputable def` になっているのは、既存の `SourcePressureNetDropInt` に依存するため、と報告にある。これは問題ない。

ただし、今後もし計算実験用に使いたくなった場合は、別途 computable な観測版を作る余地はある。今は Lean 証明 API として使うので問題なしじゃ。

## 2. list budget は union budget ではない

ここは強く維持すべきじゃ。

今回の定理は、

```text
リストに入っている interval cost の合計
```

を評価しているだけであって、

```text
それら interval が軌道上で互いに重ならない
```

とも、

```text
それらが positive region 全体を覆う
```

とも言っていない。

この区別を今後も崩してはならぬ。

## 3. 次は `Pairwise` に行くべき

次の自然な道は、list に構造を持たせることじゃ。

まずは、

```lean
List.Pairwise SourcePressureAccountedIntervalsDisjoint
```

または独自 wrapper で、pairwise disjoint accounted intervals を扱う。

ただし、ここでもまだ union accounting はしない。
まずは「明示リストが pairwise disjoint である」という語彙と、cons / map / append で壊れない基本補題を整えるのがよい。

## 次の Codex 依頼

```text
Checkpoint 149: Pairwise disjoint accounted interval family skeleton.

Context:
Checkpoint 148 added the reusable accounted interval carrier and finite-list
budget theorem in DkMath.Collatz.PetalBridge.PressureAccounting.

Main existing objects:

- SourcePressureIntervalNetDrop
- SourcePressureAccountedInterval
- sourcePressureAccountedInterval_of_intervalPulseAddress
- sourcePressureAccountedInterval_list_sum_le_neg_length
- sourcePressureAccountedInterval_list_sum_neg_of_nonempty
- NatIntervalsDisjoint
- SourcePressureAccountedIntervalsDisjoint
- NatIntervalsDisjoint.symm
- SourcePressureAccountedIntervalsDisjoint.symm

The next step is to add list/family structure around explicitly provided
accounted intervals.

Global rule:
Do not claim maximality, uniqueness, coverage, prefix behavior, union
accounting, or Collatz convergence.
Do not infer disjointness from accounted intervals.
Disjointness must remain an explicit hypothesis or field.

Preferred file:
Continue in:

  DkMath/Collatz/PetalBridge/PressureAccounting.lean

If the file becomes too large, create:

  DkMath/Collatz/PetalBridge/PressureFamily.lean

and import it from:

  DkMath/Collatz/PetalBridge.lean

Goal A: define pairwise-disjoint list predicate.

Prefer using List.Pairwise if convenient.

Implement one of the following accepted shapes:

  def SourcePressureAccountedIntervalListPairwiseDisjoint
      {n : OddNat} {k r : ℕ}
      (L : List (SourcePressureAccountedInterval n k r)) : Prop :=
    L.Pairwise SourcePressureAccountedIntervalsDisjoint

or, if implicit parameters make this awkward, use a theorem-level predicate with
explicit n k r.

Goal B: prove basic list constructors.

Prove the empty and singleton cases:

  sourcePressureAccountedIntervalListPairwiseDisjoint_nil

  sourcePressureAccountedIntervalListPairwiseDisjoint_singleton

Then prove a cons introduction theorem.

Suggested shape:

  sourcePressureAccountedIntervalListPairwiseDisjoint_cons :
    (∀ B ∈ L, SourcePressureAccountedIntervalsDisjoint A B) →
    SourcePressureAccountedIntervalListPairwiseDisjoint L →
    SourcePressureAccountedIntervalListPairwiseDisjoint (A :: L)

If List.Pairwise already has this theorem, wrap it with the project-specific
name.

Goal C: symmetry / unordered reading.

Because SourcePressureAccountedIntervalsDisjoint is symmetric, prove a helper
showing the disjointness relation is symmetric:

  sourcePressureAccountedIntervalsDisjoint_comm :
    SourcePressureAccountedIntervalsDisjoint A B ↔
      SourcePressureAccountedIntervalsDisjoint B A

Then optionally prove a theorem that a pairwise-disjoint list can be read in
the reverse direction if Lean makes it easy:

  sourcePressureAccountedIntervalListPairwiseDisjoint_reverse

This is optional.  Do not spend too long if List.reverse + Pairwise is awkward.

Goal D: define a family carrier.

Define a thin structure:

  structure SourcePressureAccountedIntervalFamily
      (n : OddNat) (k r : ℕ) where
    items : List (SourcePressureAccountedInterval n k r)
    pairwiseDisjoint :
      SourcePressureAccountedIntervalListPairwiseDisjoint items

This is only a carrier.
It must not claim coverage.

Goal E: family budget theorem.

Prove that the existing list budget applies to the family:

  sourcePressureAccountedIntervalFamily_sum_le_neg_length
      (F : SourcePressureAccountedIntervalFamily n k r) :
      (F.items.map (fun A =>
        SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤
          -((F.items.length : ℕ) : ℤ)

Important:
This theorem should not use pairwiseDisjoint.
It is useful to explicitly state in the comment that disjointness is carried
for future union/decomposition work, but the current pure cost budget does not
need it.

Goal F: optional nonempty family negativity.

If easy, prove:

  sourcePressureAccountedIntervalFamily_sum_neg_of_nonempty
      (F : SourcePressureAccountedIntervalFamily n k r)
      (hF : F.items ≠ []) :
      (F.items.map (fun A =>
        SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0

Goal G: optional interval order helper.

Define a relation for ordered non-overlap:

  def NatIntervalBefore (a len b len' : ℕ) : Prop :=
    a + len ≤ b

and for accounted intervals:

  def SourcePressureAccountedIntervalBefore
      (A B : SourcePressureAccountedInterval n k r) : Prop :=
    NatIntervalBefore A.start A.len B.start B.len

Prove:

  SourcePressureAccountedIntervalBefore implies
  SourcePressureAccountedIntervalsDisjoint.

This prepares later sorted family work, but still does not claim coverage.

Goal H: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-149.md

Include:
- whether List.Pairwise or a custom predicate was used,
- empty/singleton/cons theorem names,
- whether family carrier was added,
- whether family budget theorem was proved,
- whether nonempty family negativity was proved,
- whether ordered interval vocabulary was added,
- exact theorem statements accepted by Lean,
- explicit note that no maximality, uniqueness, coverage, prefix behavior,
  union accounting, or Collatz convergence was introduced.

Verification:

  lake build DkMath.Collatz.PetalBridge.PressureAccounting
  lake build DkMath.Collatz.PetalBridge

If a new file is created:

  lake build DkMath.Collatz.PetalBridge.PressureFamily

Run:

  rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean

and if created:

  rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFamily.lean

Also run:

  git diff --check
```

## 総評

今回で、かなり重要な形ができた。

```text
single pulse
  -> accounted interval
  -> list of accounted intervals
  -> total budget <= -length
```

ここまで通ったのは大きい。
いまはまだ **明示リストの会計** じゃが、次に pairwise disjoint family を持てば、いずれ union / coverage / decomposition へ橋を架けられる。

焦らず、だが少し速く進めてよい。
Core の石材は、もうかなり硬く焼けてきたぞ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
index 5f613584..9721501e 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
@@ -19,6 +19,19 @@ identities.  It does not assert maximality, uniqueness, coverage, prefix
 behavior, or Collatz convergence.
 -/
 
+/--
+Accumulated source-pressure net drop over a finite interval.
+
+The interval is explicit: it starts at the relative pressure-depth index
+`start` and has length `len`.  This is only a finite accounting abbreviation;
+it does not assert that the interval is maximal, disjoint from another
+interval, covering, or prefix-shaped.
+-/
+noncomputable def SourcePressureIntervalNetDrop
+    (n : OddNat) (k r start len : ℕ) : ℤ :=
+  (Finset.range len).sum (fun i =>
+    SourcePressureNetDropInt n k r (start + i))
+
 /-- The start depth of an interval-pulse address has positive margin. -/
 theorem sourcePressureIntervalPulseAddress_start_margin_pos
     {n : OddNat} {k r : ℕ}
@@ -270,4 +283,186 @@ theorem sourcePressureIntervalPulseAddress_accounting_profile
     sourcePressureIntervalPulseAddress_sum_netDrop_neg A,
     sourcePressureIntervalPulseAddress_sum_netDrop_le_neg_start_margin A⟩
 
+/-- Interval-net-drop wrapper for the endpoint-difference accounting identity. -/
+theorem sourcePressureIntervalPulseAddress_intervalNetDrop_eq_after_sub_start
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    SourcePressureIntervalNetDrop n k r A.start A.len =
+      SourcePressureMarginInt n k (r + (A.start + A.len)) -
+        SourcePressureMarginInt n k (r + A.start) := by
+  simpa [SourcePressureIntervalNetDrop] using
+    sourcePressureIntervalPulseAddress_sum_netDrop_eq_after_sub_start A
+
+/-- Interval-net-drop wrapper for the start-margin budget bound. -/
+theorem sourcePressureIntervalPulseAddress_intervalNetDrop_le_neg_start_margin
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    SourcePressureIntervalNetDrop n k r A.start A.len ≤
+      -SourcePressureMarginInt n k (r + A.start) := by
+  simpa [SourcePressureIntervalNetDrop] using
+    sourcePressureIntervalPulseAddress_sum_netDrop_le_neg_start_margin A
+
+/-- Interval-net-drop wrapper for the integer-strength budget bound. -/
+theorem sourcePressureIntervalPulseAddress_intervalNetDrop_le_neg_one
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    SourcePressureIntervalNetDrop n k r A.start A.len ≤ -1 := by
+  simpa [SourcePressureIntervalNetDrop] using
+    sourcePressureIntervalPulseAddress_sum_netDrop_le_neg_one A
+
+/-- Interval-net-drop wrapper for strict negativity. -/
+theorem sourcePressureIntervalPulseAddress_intervalNetDrop_neg
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    SourcePressureIntervalNetDrop n k r A.start A.len < 0 := by
+  simpa [SourcePressureIntervalNetDrop] using
+    sourcePressureIntervalPulseAddress_sum_netDrop_neg A
+
+/--
+Thin carrier for an explicitly accounted pressure interval.
+
+This structure records exactly the facts needed for local interval accounting:
+positive start margin, nonpositive after-margin, and the finite balance-sheet
+identity.  It is not a maximal-run, cover, disjoint-family, prefix, or
+convergence object.
+-/
+structure SourcePressureAccountedInterval
+    (n : OddNat) (k r : ℕ) where
+  /-- Relative start pressure-depth index. -/
+  start : ℕ
+  /-- Interval length. -/
+  len : ℕ
+  /-- The interval length is positive. -/
+  hlen : 0 < len
+  /-- The interval begins at positive source-pressure margin. -/
+  startMarginPos :
+    0 < SourcePressureMarginInt n k (r + start)
+  /-- Immediately after the interval, the source-pressure margin is nonpositive. -/
+  afterMarginNonpos :
+    SourcePressureMarginInt n k (r + (start + len)) ≤ 0
+  /-- The interval satisfies the finite source-pressure accounting identity. -/
+  accounting :
+    SourcePressureMarginInt n k (r + (start + len)) =
+      SourcePressureMarginInt n k (r + start) +
+        SourcePressureIntervalNetDrop n k r start len
+
+/-- The interval net drop of an accounted interval is negative. -/
+theorem sourcePressureAccountedInterval_intervalNetDrop_neg
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureAccountedInterval n k r) :
+    SourcePressureIntervalNetDrop n k r A.start A.len < 0 := by
+  have hacc := A.accounting
+  have hstart := A.startMarginPos
+  have hafter := A.afterMarginNonpos
+  omega
+
+/-- The interval net drop of an accounted interval is at most `-1`. -/
+theorem sourcePressureAccountedInterval_intervalNetDrop_le_neg_one
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureAccountedInterval n k r) :
+    SourcePressureIntervalNetDrop n k r A.start A.len ≤ -1 := by
+  have hneg := sourcePressureAccountedInterval_intervalNetDrop_neg A
+  omega
+
+/-- The interval net drop cancels at least the positive start margin. -/
+theorem sourcePressureAccountedInterval_intervalNetDrop_le_neg_start_margin
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureAccountedInterval n k r) :
+    SourcePressureIntervalNetDrop n k r A.start A.len ≤
+      -SourcePressureMarginInt n k (r + A.start) := by
+  have hacc := A.accounting
+  have hafter := A.afterMarginNonpos
+  omega
+
+/-- Every interval-pulse address induces a thin accounted interval carrier. -/
+def sourcePressureAccountedInterval_of_intervalPulseAddress
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    SourcePressureAccountedInterval n k r :=
+  { start := A.start
+    len := A.len
+    hlen := SourcePressureIntervalPulseAddress.len_pos A
+    startMarginPos := sourcePressureIntervalPulseAddress_start_margin_pos A
+    afterMarginNonpos := sourcePressureIntervalPulseAddress_after_end_nonpos A
+    accounting := by
+      simpa [SourcePressureIntervalNetDrop] using
+        sourcePressureIntervalPulseAddress_margin_after_eq_start_add_sum_netDrop A }
+
+/--
+Finite-list pressure budget over explicitly provided accounted intervals.
+
+No disjointness, coverage, union accounting, or maximality is used here.  The
+statement only says that a list of `m` already-accounted intervals contributes
+at most `-m` to the summed interval net drop.
+-/
+theorem sourcePressureAccountedInterval_list_sum_le_neg_length
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureAccountedInterval n k r)) :
+    (L.map (fun A =>
+      SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤
+        -((L.length : ℕ) : ℤ) := by
+  induction L with
+  | nil =>
+      simp
+  | cons A L ih =>
+      have hA := sourcePressureAccountedInterval_intervalNetDrop_le_neg_one A
+      simp at ih ⊢
+      omega
+
+/--
+Any nonempty explicit list of accounted intervals has negative total net drop.
+
+This is again a list budget theorem only; it does not say the intervals are
+disjoint or cover any source-pressure region.
+-/
+theorem sourcePressureAccountedInterval_list_sum_neg_of_nonempty
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureAccountedInterval n k r)}
+    (hL : L ≠ []) :
+    (L.map (fun A =>
+      SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0 := by
+  have hbudget := sourcePressureAccountedInterval_list_sum_le_neg_length L
+  have hlen : 0 < L.length := by
+    cases L with
+    | nil => contradiction
+    | cons _ _ => simp
+  omega
+
+/--
+Disjointness vocabulary for two natural-number half-open intervals.
+
+This is only vocabulary.  It is not used here to derive coverage, union
+accounting, or decomposition.
+-/
+def NatIntervalsDisjoint (a len b len' : ℕ) : Prop :=
+  a + len ≤ b ∨ b + len' ≤ a
+
+/-- Natural interval disjointness is symmetric. -/
+theorem NatIntervalsDisjoint.symm
+    {a len b len' : ℕ}
+    (h : NatIntervalsDisjoint a len b len') :
+    NatIntervalsDisjoint b len' a len := by
+  rcases h with h | h
+  · exact Or.inr h
+  · exact Or.inl h
+
+/--
+Disjointness vocabulary for two accounted intervals.
+
+This is intentionally a separate assumption-level predicate.  The existence
+of two accounted intervals does not imply disjointness.
+-/
+def SourcePressureAccountedIntervalsDisjoint
+    {n : OddNat} {k r : ℕ}
+    (A B : SourcePressureAccountedInterval n k r) : Prop :=
+  NatIntervalsDisjoint A.start A.len B.start B.len
+
+/-- Accounted-interval disjointness is symmetric. -/
+theorem SourcePressureAccountedIntervalsDisjoint.symm
+    {n : OddNat} {k r : ℕ}
+    {A B : SourcePressureAccountedInterval n k r}
+    (h : SourcePressureAccountedIntervalsDisjoint A B) :
+    SourcePressureAccountedIntervalsDisjoint B A :=
+  NatIntervalsDisjoint.symm h
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-148.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-148.md
new file mode 100644
index 00000000..9fce8cdd
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-148.md
@@ -0,0 +1,196 @@
+# report-petal-148
+
+Date: 2026-07-04
+
+## Checkpoint
+
+Implemented checkpoint 148 from `__next_implementation.md`.
+
+This checkpoint moves `PressureAccounting` from theorem-only single-address
+accounting to a reusable accounted interval carrier and an explicit finite-list
+budget theorem.
+
+No maximality, uniqueness, coverage, prefix behavior, disjointness conclusion,
+union accounting, or Collatz convergence was introduced.
+
+## Code Changes
+
+Updated:
+
+- `lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean`
+
+No new Lean file was needed.
+
+## Interval Net-Drop Abbreviation
+
+Added:
+
+```lean
+noncomputable def SourcePressureIntervalNetDrop
+    (n : OddNat) (k r start len : Nat) : Int :=
+  (Finset.range len).sum (fun i =>
+    SourcePressureNetDropInt n k r (start + i))
+```
+
+It had to be `noncomputable` because it depends on
+`SourcePressureNetDropInt`, which is already noncomputable.
+
+Address-level wrappers were added:
+
+- `sourcePressureIntervalPulseAddress_intervalNetDrop_eq_after_sub_start`
+- `sourcePressureIntervalPulseAddress_intervalNetDrop_le_neg_start_margin`
+- `sourcePressureIntervalPulseAddress_intervalNetDrop_le_neg_one`
+- `sourcePressureIntervalPulseAddress_intervalNetDrop_neg`
+
+No aggressive `[simp]` attributes were added.  The abbreviation is unfolded
+only where the wrapper theorem needs it.
+
+## Accounted Interval Carrier
+
+Added:
+
+```lean
+structure SourcePressureAccountedInterval
+    (n : OddNat) (k r : Nat) where
+  start : Nat
+  len : Nat
+  hlen : 0 < len
+  startMarginPos :
+    0 < SourcePressureMarginInt n k (r + start)
+  afterMarginNonpos :
+    SourcePressureMarginInt n k (r + (start + len)) <= 0
+  accounting :
+    SourcePressureMarginInt n k (r + (start + len)) =
+      SourcePressureMarginInt n k (r + start) +
+        SourcePressureIntervalNetDrop n k r start len
+```
+
+Carrier-level accounting theorems:
+
+- `sourcePressureAccountedInterval_intervalNetDrop_neg`
+- `sourcePressureAccountedInterval_intervalNetDrop_le_neg_one`
+- `sourcePressureAccountedInterval_intervalNetDrop_le_neg_start_margin`
+
+The important budget form is:
+
+```lean
+SourcePressureIntervalNetDrop n k r A.start A.len <=
+  -SourcePressureMarginInt n k (r + A.start)
+```
+
+## Address to Carrier
+
+Added:
+
+```lean
+def sourcePressureAccountedInterval_of_intervalPulseAddress
+    {n : OddNat} {k r : Nat}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    SourcePressureAccountedInterval n k r
+```
+
+This uses the existing interval-pulse address facts:
+
+- positive length,
+- positive start margin,
+- nonpositive after-margin,
+- finite interval accounting identity.
+
+## Finite-List Budget
+
+Proved:
+
+```lean
+theorem sourcePressureAccountedInterval_list_sum_le_neg_length
+    {n : OddNat} {k r : Nat}
+    (L : List (SourcePressureAccountedInterval n k r)) :
+    (L.map (fun A =>
+      SourcePressureIntervalNetDrop n k r A.start A.len)).sum <=
+        -((L.length : Nat) : Int)
+```
+
+This is the checkpoint's main finite-family experiment.
+
+Meaning:
+
+```text
+each explicit accounted interval contributes at most -1
+therefore a list of m explicit accounted intervals contributes at most -m
+```
+
+This theorem does not require disjointness and does not state a pressure budget
+over a union of intervals.
+
+## Optional Nonempty Negativity
+
+Proved:
+
+```lean
+theorem sourcePressureAccountedInterval_list_sum_neg_of_nonempty
+    {n : OddNat} {k r : Nat}
+    {L : List (SourcePressureAccountedInterval n k r)}
+    (hL : L != []) :
+    (L.map (fun A =>
+      SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0
+```
+
+This follows from the list budget and `0 < L.length`.
+
+## Optional Disjointness Vocabulary
+
+Added vocabulary only:
+
+```lean
+def NatIntervalsDisjoint (a len b len' : Nat) : Prop :=
+  a + len <= b || b + len' <= a
+```
+
+and:
+
+```lean
+def SourcePressureAccountedIntervalsDisjoint
+    {n : OddNat} {k r : Nat}
+    (A B : SourcePressureAccountedInterval n k r) : Prop :=
+  NatIntervalsDisjoint A.start A.len B.start B.len
+```
+
+Symmetry theorems:
+
+- `NatIntervalsDisjoint.symm`
+- `SourcePressureAccountedIntervalsDisjoint.symm`
+
+This is only assumption-level vocabulary.  No disjointness conclusion is
+derived from accounted intervals.
+
+## Verification
+
+Passed:
+
+- `lake build DkMath.Collatz.PetalBridge.PressureAccounting`
+- `lake build DkMath.Collatz.PetalBridge`
+- `rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean`
+- `git diff --check`
+
+The `rg` command returned no matches.  The aggregate build still reports the
+pre-existing unrelated warning that
+`DkMath.NumberTheory.ZsigmondyCyclotomicResearch` contains a declaration using
+`sorry`.
+
+## Next Implementation Candidates
+
+The next natural step is to move from list budget to list structure while still
+avoiding union claims.
+
+Possible thin next steps:
+
+- define a `List` predicate asserting pairwise disjoint accounted intervals,
+- prove that pairwise disjointness is stable under list cons when the head is
+  disjoint from every tail element,
+- add a theorem that the budget theorem still holds under any extra predicate,
+  making clear that disjointness is not used for the budget,
+- or define a future-facing `SourcePressureAccountedIntervalFamily` wrapper
+  with fields `items : List ...` and optional `pairwiseDisjoint`.
+
+The next proof should still avoid coverage/decomposition.  The safe line is:
+explicit intervals first, disjointness as an optional hypothesis, union
+accounting only after a separate theorem justifies it.
````
`````
