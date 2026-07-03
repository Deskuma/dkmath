# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureAccounting

gch: f6a6cdcd2ca06ca22ca78f13db5ab80d7925c397

## Report

Checkpoint 149 完了です。

[PressureAccounting.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean) に、`List.Pairwise` ベースの pairwise-disjoint family skeleton を追加しました。

主な追加:

```lean
SourcePressureAccountedIntervalListPairwiseDisjoint
sourcePressureAccountedIntervalListPairwiseDisjoint_nil
sourcePressureAccountedIntervalListPairwiseDisjoint_singleton
sourcePressureAccountedIntervalListPairwiseDisjoint_cons
sourcePressureAccountedIntervalsDisjoint_comm
sourcePressureAccountedIntervalListPairwiseDisjoint_reverse
SourcePressureAccountedIntervalFamily
sourcePressureAccountedIntervalFamily_sum_le_neg_length
sourcePressureAccountedIntervalFamily_sum_neg_of_nonempty
NatIntervalBefore
SourcePressureAccountedIntervalBefore
NatIntervalsDisjoint.of_before
SourcePressureAccountedIntervalsDisjoint.of_before
```

family budget は `pairwiseDisjoint` を使わず、明示リストの cost budget として通しています。disjointness は将来の union/decomposition 用の明示フィールドであり、coverage や union accounting はまだ主張していません。

レポートも作成済みです:
[report-petal-149.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-149.md)

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

うむ、Checkpoint 149 は **採用** じゃ 👍️
かなり良い。`PressureAccounting` は、単一区間の会計から **明示 family / pairwise-disjoint skeleton** へ進んだ。

今回の主な追加は、`List.Pairwise` ベースの `SourcePressureAccountedIntervalListPairwiseDisjoint`、family carrier の `SourcePressureAccountedIntervalFamily`、family budget、非空 family の負性、そして ordered interval vocabulary じゃ。しかも、family budget では `pairwiseDisjoint` を使っておらず、「明示リストの cost budget」としてだけ通している。これは設計上かなり健全じゃ。

## 実装内容の解説

今回の流れはこうじゃ。

```text
accounted interval
  -> explicit list
  -> pairwise-disjoint list predicate
  -> family carrier
  -> family budget
```

つまり、前回までに得た

$$
\mathrm{NetDrop}(A)\le -1
$$

を、明示 family に対して

$$
\sum_{A\in F.items}\mathrm{NetDrop}(A)\le -|F.items|
$$

へ持ち上げた。

Lean 定理では、

```lean
sourcePressureAccountedIntervalFamily_sum_le_neg_length
```

がそれじゃな。

ここで重要なのは、これはまだ **union accounting** ではないことじゃ。
「リストに入っている interval cost を足すと負になる」だけであり、「それらが軌道上の領域を覆う」とは言っていない。報告でも、coverage や union accounting、Collatz convergence は入れていないと明記されている。

## 良い点

## 1. `List.Pairwise` を使ったのがよい

独自再発明ではなく、Lean の標準的な list 構造に乗せている。
今後 `reverse`、`append`、`map`、`sublist` などへ進むとき、これは効く。

`sourcePressureAccountedIntervalListPairwiseDisjoint_reverse` まで通しているのもよい。disjointness が対称関係であることを使って、リストの向きに依存しない読みを確保しておる。

## 2. Family carrier が薄い

`SourcePressureAccountedIntervalFamily` は、

```lean
items : List (SourcePressureAccountedInterval n k r)
pairwiseDisjoint : SourcePressureAccountedIntervalListPairwiseDisjoint items
```

だけを持つ。

これはかなりよい。
coverage も maximality も sortedness も持っていない。
つまり、将来の分解定理に備えた **器** として安全じゃ。

## 3. `NatIntervalBefore` はよい下準備

`NatIntervalBefore a len b len' := a + len ≤ b` は、後の sorted family に必要な片方向関係じゃ。
`_len'` が未使用なのは少し不格好に見えるが、二つの区間を受け取る関係として arity を合わせるためなら許容範囲じゃ。

次にやるなら、

```lean
before -> disjoint
```

だけでなく、

```lean
A before B
B before C
->
A before C
```

のような推移性を小さく入れると、sorted chain へ進みやすい。

## 注意点

まだ union / coverage は絶対に言わない方がよい。

今あるのは、

```text
明示 family の各 interval は負予算を持つ
```

であって、

```text
その family が positive region 全体を覆う
```

ではない。

この境界線は守れている。
今回の実装は安全圏の中でペースを上げられておる。

## 例の \(1\to4\to2\to1\) Petal 巡回について

タイミングとしては、 **そろそろ入れてよい** 。
ただし `PressureAccounting` には入れない方がよい。これは pressure family ではなく、Collatz の最小巡回・Petal 境界の局所 obstruction じゃ。

置き場所は新規に薄く、

```text
DkMath/Collatz/PetalBridge/OneCycle.lean
```

あるいは既存の Collatz 基礎層に近い場所がよい。

まず証明すべき小補題はこれじゃ。

$$
3n+1=2^h n\Rightarrow n=1\land h=2
$$

ただし、この命題はそのままだと \(h=0,1\) や \(n=0\) 周りを丁寧に扱う必要がある。正確には、

```lean
0 < n
3 * n + 1 = 2 ^ h * n
```

から、

```lean
n = 1 ∧ h = 2
```

を目指す。

数学的には簡単じゃ。

* \(h=0\): \(3n+1=n\) は正の \(n\) で不可能
* \(h=1\): \(3n+1=2n\) は不可能
* \(h=2\): \(3n+1=4n\) なので \(n=1\)
* \(h\ge3\): \(2^h n\ge8n\) で、\(3n+1=2^h n\) は \(n\ge1\) では無理

これが通ると、

```text
1 -> 4 -> 2 -> 1 の相似 Petal 巡回は n=1 の特異点だけ
```

が形式的に言える。

ただし、これは **全ての非自明周期の否定ではない** 。
あくまで「一段で同じ odd state に戻る scaled one-cycle obstruction」じゃ。ここをコメントで明記するのが大事じゃな。

## 次の Codex 依頼

今回は二本立てがよい。
主線は family constructors / sorted skeleton。副線として one-cycle obstruction を入れる。Codex に少し推論させるなら、one-cycle はちょうどよい小山じゃ。

```text
Checkpoint 150: Family constructors plus the scaled 1-4-2-1 one-cycle obstruction.

Context:
Checkpoint 149 added pairwise-disjoint accounted interval list/family skeletons
to DkMath.Collatz.PetalBridge.PressureAccounting.

Main existing objects:
- SourcePressureAccountedInterval
- SourcePressureAccountedIntervalFamily
- SourcePressureAccountedIntervalListPairwiseDisjoint
- sourcePressureAccountedIntervalFamily_sum_le_neg_length
- sourcePressureAccountedIntervalFamily_sum_neg_of_nonempty
- NatIntervalBefore
- SourcePressureAccountedIntervalBefore
- NatIntervalsDisjoint.of_before
- SourcePressureAccountedIntervalsDisjoint.of_before

Global rule for the pressure-family work:
Do not claim maximality, uniqueness, coverage, prefix behavior, union accounting,
or Collatz convergence.
Disjointness remains an explicit field/hypothesis.

Part A: family constructors.

In DkMath/Collatz/PetalBridge/PressureAccounting.lean, add thin constructors:

1. Empty family

  def sourcePressureAccountedIntervalFamily_nil
      (n : OddNat) (k r : Nat) :
      SourcePressureAccountedIntervalFamily n k r

2. Singleton family

  def sourcePressureAccountedIntervalFamily_singleton
      {n : OddNat} {k r : Nat}
      (A : SourcePressureAccountedInterval n k r) :
      SourcePressureAccountedIntervalFamily n k r

3. Cons family

  def sourcePressureAccountedIntervalFamily_cons
      {n : OddNat} {k r : Nat}
      (A : SourcePressureAccountedInterval n k r)
      (F : SourcePressureAccountedIntervalFamily n k r)
      (hhead : forall B in F.items,
        SourcePressureAccountedIntervalsDisjoint A B) :
      SourcePressureAccountedIntervalFamily n k r

Use the existing pairwise-disjoint cons theorem.

Part B: named family budget corollaries.

Add named corollaries for singleton and cons if easy:

- sourcePressureAccountedIntervalFamily_singleton_sum_le_neg_one
- sourcePressureAccountedIntervalFamily_cons_sum_le_neg_length

These are convenience wrappers only.

Part C: sorted/before skeleton.

Add small helpers around ordered non-overlap:

1. Compositional theorem for natural intervals:

  NatIntervalBefore.trans_like
      (hAB : NatIntervalBefore a len b len')
      (hBC : NatIntervalBefore b len' c len'') :
      NatIntervalBefore a len c len''

If the exact theorem name is awkward, choose a Lean-friendly name.

2. Accounted interval version:

  SourcePressureAccountedIntervalBefore.trans_like

3. A two-element sorted family constructor:

  sourcePressureAccountedIntervalFamily_pair_of_before
      (A B : SourcePressureAccountedInterval n k r)
      (hAB : SourcePressureAccountedIntervalBefore A B) :
      SourcePressureAccountedIntervalFamily n k r

This should build [A, B] with pairwise disjointness derived from before -> disjoint.
Do not claim coverage.

Part D: scaled 1 -> 4 -> 2 -> 1 one-cycle obstruction.

Create a new file if appropriate:

  DkMath/Collatz/PetalBridge/OneCycle.lean

and import it from:

  DkMath/Collatz/PetalBridge.lean

The purpose is to formalize that the scaled one-step odd cycle equation

  3*n + 1 = 2^h * n

has only the positive natural solution n = 1, h = 2.

Preferred theorem:

  theorem collatz_scaled_one_cycle_eq_one
      {n h : Nat}
      (hn : 0 < n)
      (hcycle : 3 * n + 1 = 2 ^ h * n) :
      n = 1 ∧ h = 2

If this exact statement is hard, prove supporting lemmas first:

- collatz_scaled_one_cycle_h_ne_zero
- collatz_scaled_one_cycle_h_ne_one
- collatz_scaled_one_cycle_h_eq_two_of_le_two
- collatz_scaled_one_cycle_h_not_ge_three

or use Nat.lt_trichotomy / omega / nlinarith as Lean accepts.

Important comment:
This theorem only rules out scaled copies of the 1 -> 4 -> 2 -> 1 one-cycle
where one odd accelerated step returns to the same odd state.
It does not rule out arbitrary nontrivial Collatz cycles.

Optional corollary:

  theorem collatz_scaled_one_cycle_unique :
      3 * n + 1 = 4 * n -> n = 1

or:

  theorem collatz_one_four_two_one_scaled_boundary_unique
      {n : Nat} (hn : 0 < n)
      (h : 3 * n + 1 = 4 * n) :
      n = 1

Part E: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-150.md

Include:
- which family constructors were added,
- whether singleton/cons budget corollaries were added,
- whether sorted/before skeleton was extended,
- whether OneCycle.lean was created,
- exact theorem statement accepted for the scaled one-cycle obstruction,
- explicit note that one-cycle uniqueness does not prove general Collatz cycle
  uniqueness or convergence,
- explicit note that pressure-family work still does not introduce maximality,
  uniqueness, coverage, prefix behavior, union accounting, or Collatz convergence.

Verification:

  lake build DkMath.Collatz.PetalBridge.PressureAccounting
  lake build DkMath.Collatz.PetalBridge

If OneCycle.lean is created:

  lake build DkMath.Collatz.PetalBridge.OneCycle

Run:

  rg -n "\\bsorry\\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean

If OneCycle.lean is created:

  rg -n "\\bsorry\\b" lean/dk_math/DkMath/Collatz/PetalBridge/OneCycle.lean

Also run:

  git diff --check
```

## 総評

今回で family skeleton は立った。
次は、family を作る constructor を整えつつ、例の \(1\to4\to2\to1\) の唯一性を横に置くのがよい。

この小補題は、DkMath 的にはかなり象徴的じゃ。
「最小 Petal 巡回は確かに存在する。しかし、それを外側へ相似コピーすることはできない」
この線が Lean で固まると、Collatz/PetalBridge の物語が一段締まるぞ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
index 9721501e..d9e9c18c 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
@@ -465,4 +465,137 @@ theorem SourcePressureAccountedIntervalsDisjoint.symm
     SourcePressureAccountedIntervalsDisjoint B A :=
   NatIntervalsDisjoint.symm h
 
+/--
+Pairwise-disjointness predicate for an explicit list of accounted intervals.
+
+This is only list structure.  It does not assert that the list covers a region,
+is maximal, is sorted, or gives a union accounting theorem.
+-/
+def SourcePressureAccountedIntervalListPairwiseDisjoint
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureAccountedInterval n k r)) : Prop :=
+  L.Pairwise SourcePressureAccountedIntervalsDisjoint
+
+/-- The empty accounted-interval list is pairwise disjoint. -/
+theorem sourcePressureAccountedIntervalListPairwiseDisjoint_nil
+    {n : OddNat} {k r : ℕ} :
+    SourcePressureAccountedIntervalListPairwiseDisjoint
+      ([] : List (SourcePressureAccountedInterval n k r)) :=
+  List.Pairwise.nil
+
+/-- A singleton accounted-interval list is pairwise disjoint. -/
+theorem sourcePressureAccountedIntervalListPairwiseDisjoint_singleton
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureAccountedInterval n k r) :
+    SourcePressureAccountedIntervalListPairwiseDisjoint [A] := by
+  simp [SourcePressureAccountedIntervalListPairwiseDisjoint]
+
+/--
+Cons constructor for pairwise-disjoint accounted-interval lists.
+
+The head interval must be explicitly disjoint from every tail interval.  No
+disjointness is inferred from accounting data alone.
+-/
+theorem sourcePressureAccountedIntervalListPairwiseDisjoint_cons
+    {n : OddNat} {k r : ℕ}
+    {A : SourcePressureAccountedInterval n k r}
+    {L : List (SourcePressureAccountedInterval n k r)}
+    (hhead : ∀ B ∈ L, SourcePressureAccountedIntervalsDisjoint A B)
+    (htail : SourcePressureAccountedIntervalListPairwiseDisjoint L) :
+    SourcePressureAccountedIntervalListPairwiseDisjoint (A :: L) :=
+  List.Pairwise.cons hhead htail
+
+/-- Accounted-interval disjointness can be read in either order. -/
+theorem sourcePressureAccountedIntervalsDisjoint_comm
+    {n : OddNat} {k r : ℕ}
+    {A B : SourcePressureAccountedInterval n k r} :
+    SourcePressureAccountedIntervalsDisjoint A B ↔
+      SourcePressureAccountedIntervalsDisjoint B A :=
+  ⟨SourcePressureAccountedIntervalsDisjoint.symm,
+    SourcePressureAccountedIntervalsDisjoint.symm⟩
+
+/--
+Pairwise-disjoint accounted intervals remain pairwise disjoint after reversing
+the explicit list.
+
+This uses symmetry of the disjointness relation only; it still does not say
+anything about coverage or union accounting.
+-/
+theorem sourcePressureAccountedIntervalListPairwiseDisjoint_reverse
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureAccountedInterval n k r)}
+    (h : SourcePressureAccountedIntervalListPairwiseDisjoint L) :
+    SourcePressureAccountedIntervalListPairwiseDisjoint L.reverse := by
+  unfold SourcePressureAccountedIntervalListPairwiseDisjoint at h ⊢
+  exact h.reverse.imp (fun hBA =>
+    SourcePressureAccountedIntervalsDisjoint.symm hBA)
+
+/--
+Thin carrier for an explicit family of accounted intervals.
+
+The pairwise-disjoint field is stored for later decomposition work.  The
+current budget theorem below does not use it, because the budget is only over
+the explicitly listed interval costs.
+-/
+structure SourcePressureAccountedIntervalFamily
+    (n : OddNat) (k r : ℕ) where
+  /-- Explicit accounted intervals. -/
+  items : List (SourcePressureAccountedInterval n k r)
+  /-- Explicit pairwise-disjointness hypothesis for future union/decomposition work. -/
+  pairwiseDisjoint :
+    SourcePressureAccountedIntervalListPairwiseDisjoint items
+
+/--
+Family budget inherited from the list budget.
+
+The proof does not use `pairwiseDisjoint`: disjointness is stored for later
+union/decomposition work, while this theorem only sums the explicit interval
+costs already present in the family.
+-/
+theorem sourcePressureAccountedIntervalFamily_sum_le_neg_length
+    {n : OddNat} {k r : ℕ}
+    (F : SourcePressureAccountedIntervalFamily n k r) :
+    (F.items.map (fun A =>
+      SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤
+        -((F.items.length : ℕ) : ℤ) :=
+  sourcePressureAccountedInterval_list_sum_le_neg_length F.items
+
+/-- A nonempty accounted-interval family has negative total explicit net drop. -/
+theorem sourcePressureAccountedIntervalFamily_sum_neg_of_nonempty
+    {n : OddNat} {k r : ℕ}
+    (F : SourcePressureAccountedIntervalFamily n k r)
+    (hF : F.items ≠ []) :
+    (F.items.map (fun A =>
+      SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0 :=
+  sourcePressureAccountedInterval_list_sum_neg_of_nonempty hF
+
+/--
+Ordered non-overlap for two natural-number half-open intervals.
+
+This is a direction-sensitive helper for future sorted-family work.
+-/
+def NatIntervalBefore (a len b _len' : ℕ) : Prop :=
+  a + len ≤ b
+
+/-- Ordered non-overlap implies ordinary interval disjointness. -/
+theorem NatIntervalsDisjoint.of_before
+    {a len b len' : ℕ}
+    (h : NatIntervalBefore a len b len') :
+    NatIntervalsDisjoint a len b len' :=
+  Or.inl h
+
+/-- Ordered non-overlap for two accounted intervals. -/
+def SourcePressureAccountedIntervalBefore
+    {n : OddNat} {k r : ℕ}
+    (A B : SourcePressureAccountedInterval n k r) : Prop :=
+  NatIntervalBefore A.start A.len B.start B.len
+
+/-- Ordered accounted intervals are disjoint. -/
+theorem SourcePressureAccountedIntervalsDisjoint.of_before
+    {n : OddNat} {k r : ℕ}
+    {A B : SourcePressureAccountedInterval n k r}
+    (h : SourcePressureAccountedIntervalBefore A B) :
+    SourcePressureAccountedIntervalsDisjoint A B :=
+  NatIntervalsDisjoint.of_before h
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-149.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-149.md
new file mode 100644
index 00000000..82f9b057
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-149.md
@@ -0,0 +1,161 @@
+# report-petal-149
+
+Date: 2026-07-04
+
+## Checkpoint
+
+Implemented checkpoint 149 from `__next_implementation.md`.
+
+This checkpoint adds pairwise-disjoint list structure and a thin family carrier
+around explicitly provided accounted intervals.
+
+No maximality, uniqueness, coverage, prefix behavior, union accounting, or
+Collatz convergence was introduced.  Disjointness remains an explicit
+hypothesis/field; it is not inferred from accounted intervals.
+
+## Code Changes
+
+Updated:
+
+- `lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean`
+
+No new Lean file was created.
+
+## Pairwise Predicate
+
+Used `List.Pairwise` directly through a project-facing wrapper:
+
+```lean
+def SourcePressureAccountedIntervalListPairwiseDisjoint
+    {n : OddNat} {k r : Nat}
+    (L : List (SourcePressureAccountedInterval n k r)) : Prop :=
+  L.Pairwise SourcePressureAccountedIntervalsDisjoint
+```
+
+Constructor/projection helpers added:
+
+- `sourcePressureAccountedIntervalListPairwiseDisjoint_nil`
+- `sourcePressureAccountedIntervalListPairwiseDisjoint_singleton`
+- `sourcePressureAccountedIntervalListPairwiseDisjoint_cons`
+
+The cons theorem has the accepted shape:
+
+```lean
+theorem sourcePressureAccountedIntervalListPairwiseDisjoint_cons
+    {n : OddNat} {k r : Nat}
+    {A : SourcePressureAccountedInterval n k r}
+    {L : List (SourcePressureAccountedInterval n k r)}
+    (hhead : forall B in L, SourcePressureAccountedIntervalsDisjoint A B)
+    (htail : SourcePressureAccountedIntervalListPairwiseDisjoint L) :
+    SourcePressureAccountedIntervalListPairwiseDisjoint (A :: L)
+```
+
+## Symmetry
+
+Added:
+
+- `sourcePressureAccountedIntervalsDisjoint_comm`
+- `sourcePressureAccountedIntervalListPairwiseDisjoint_reverse`
+
+The reverse theorem was added as an extra useful lemma.  It uses symmetry of
+`SourcePressureAccountedIntervalsDisjoint` and does not add any coverage or
+union interpretation.
+
+## Family Carrier
+
+Added:
+
+```lean
+structure SourcePressureAccountedIntervalFamily
+    (n : OddNat) (k r : Nat) where
+  items : List (SourcePressureAccountedInterval n k r)
+  pairwiseDisjoint :
+    SourcePressureAccountedIntervalListPairwiseDisjoint items
+```
+
+This is only a carrier.  The `pairwiseDisjoint` field is stored for future
+union/decomposition work, but the budget theorem below does not use it.
+
+## Family Budget
+
+Proved:
+
+```lean
+theorem sourcePressureAccountedIntervalFamily_sum_le_neg_length
+    {n : OddNat} {k r : Nat}
+    (F : SourcePressureAccountedIntervalFamily n k r) :
+    (F.items.map (fun A =>
+      SourcePressureIntervalNetDrop n k r A.start A.len)).sum <=
+        -((F.items.length : Nat) : Int)
+```
+
+This is just the existing list budget applied to the family items.
+Disjointness is intentionally unused.
+
+## Nonempty Family Negativity
+
+Proved:
+
+```lean
+theorem sourcePressureAccountedIntervalFamily_sum_neg_of_nonempty
+    {n : OddNat} {k r : Nat}
+    (F : SourcePressureAccountedIntervalFamily n k r)
+    (hF : F.items != []) :
+    (F.items.map (fun A =>
+      SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0
+```
+
+## Ordered Interval Vocabulary
+
+Added optional ordered non-overlap vocabulary:
+
+```lean
+def NatIntervalBefore (a len b _len' : Nat) : Prop :=
+  a + len <= b
+```
+
+and:
+
+```lean
+def SourcePressureAccountedIntervalBefore
+    {n : OddNat} {k r : Nat}
+    (A B : SourcePressureAccountedInterval n k r) : Prop :=
+  NatIntervalBefore A.start A.len B.start B.len
+```
+
+Helper theorems:
+
+- `NatIntervalsDisjoint.of_before`
+- `SourcePressureAccountedIntervalsDisjoint.of_before`
+
+This prepares sorted-family work.  It does not claim coverage or decomposition.
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
+The next safe step is to add family construction helpers while keeping union
+claims out of scope.
+
+Possible next moves:
+
+- family constructors for `nil`, singleton, and cons,
+- prove the family budget for singleton and cons as named corollaries,
+- define a sorted-family predicate using `SourcePressureAccountedIntervalBefore`,
+- prove sorted-before implies pairwise-disjoint for very small shapes first
+  such as two-element lists.
+
+The boundary remains clear: explicit family/list structure is fine; union
+accounting and coverage require separate future theorems.
````
`````
