# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureAccounting

gch: 63baabee60d6202cc6b9555b82cd4f372fd239ef

## Report

cp154 を実装しました。今回は [PressureAccounting.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean) のみ更新し、新規 Lean ファイルは作っていません。

追加内容:

- `SourcePressureIntervalPulseAddressFamily`
- `nil` / `singleton` / `cons` constructors
- family-level sorted / failure predicates
- `sourcePressureIntervalPulseAddressFamily_sorted_or_failure`
- sorted family から accounted family への lift
- length / budget / nonempty negative budget wrappers
- 既存 producer `sourcePressureIntervalPulseAddress_of_localIsland` から singleton family への薄い bridge

`PressureFrontier.lean` を確認しましたが、canonical な address list producer は見つからなかったため、list producer は作っていません。コードコメントにも、failure は order obstruction であり overlap 証拠ではない、と明記しています。

レポート追加済み:
[report-petal-154.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-154.md)

確認:

- `lake build DkMath.Collatz.PetalBridge.PressureAccounting` 通過
- `lake build DkMath.Collatz.PetalBridge.PressureFrontier` 通過
- `lake build DkMath.Collatz.PetalBridge` 通過
- 対象 2 ファイルの `sorry` 検索ヒットなし
- `git diff --check` 通過

既存の `ZsigmondyCyclotomicResearch` の `sorry` warning は今回範囲外です。

## Review

## 結論

うむ、Checkpoint 154 は **採用** じゃ 👍️
今回も main root に集中できておる。`PressureAccounting.lean` のみ更新し、新規 Lean ファイルも作らず、`OneCycle` / `ValuationFlowBridge` / ABC / NumberTheory へは触れていない。これは指示どおりで良い。

今回の中心は、

```text id="s67qoc"
SourcePressureIntervalPulseAddress
  -> explicit family carrier
  -> sorted / failure split
  -> sorted branch で accounted family
  -> budget
```

という family wrapper の確立じゃな。`PressureFrontier.lean` を確認し、canonical な address list producer は見つからなかったため、list producer を捏造せず、既存の `sourcePressureIntervalPulseAddress_of_localIsland` から singleton family だけを作った判断も正しい。

## 実装内容の解説

## 1. `SourcePressureIntervalPulseAddressFamily`

追加された carrier はこれじゃ。

```lean id="5pgli4"
structure SourcePressureIntervalPulseAddressFamily
    (n : OddNat) (k r : ℕ) where
  items : List (SourcePressureIntervalPulseAddress n k r)
```

これは非常に良い薄さじゃ。
fields は `items` のみ。coverage、maximality、uniqueness、prefix、disjointness、union accounting、convergence を一切持たない。

つまりこれは、

```text id="d6uq26"
明示的に与えられた address list を包むだけの箱
```

じゃ。

この薄さが今は重要じゃな。

## 2. constructors は十分

追加された constructor 群も自然じゃ。

```lean id="07g4rq"
sourcePressureIntervalPulseAddressFamily_nil
sourcePressureIntervalPulseAddressFamily_singleton
sourcePressureIntervalPulseAddressFamily_singleton_of_address
sourcePressureIntervalPulseAddressFamily_singleton_of_localIsland
sourcePressureIntervalPulseAddressFamily_cons
```

特に `singleton_of_localIsland` は良い。
既存 producer が一つの `SourcePressureIntervalPulseAddress` を出せるなら、それを singleton family として包む。だが、そこから「全 island を列挙した」とは言わない。ここが安全じゃ。

## 3. sorted / failure family predicates

family-level の predicate も良い。

```lean id="16af3t"
SourcePressureIntervalPulseAddressFamilySortedBefore
SourcePressureIntervalPulseAddressFamilyHasSortedBeforeFailure
sourcePressureIntervalPulseAddressFamily_sorted_or_failure
```

これにより、明示 family は必ず、

```text id="yjnjwv"
sorted branch
または
failure branch
```

へ分岐できる。

そしてコメントで、failure は order obstruction であり overlap 証拠ではない、と明記されている。これも良い。
ここは今後も絶対に崩さぬ方がよい。

## 4. sorted family から accounted family への lift

追加された bridge はこれじゃ。

```lean id="o3n4c4"
sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily
```

これで、

```text id="x4f379"
SourcePressureIntervalPulseAddressFamily
  + sorted
  -> SourcePressureAccountedIntervalFamily
```

ができるようになった。

さらに、

```lean id="rsj0e4"
sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily_length
sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily_sum_le_neg_length
sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily_sum_neg_of_nonempty
```

まで揃った。

つまり sorted branch では、

```text id="jgiq0u"
family length を保つ
net drop sum ≤ -length
nonempty なら net drop sum < 0
```

まで一気に読める。

これは main root の API としてかなりよい。

## 注意点

## 1. まだ canonical producer ではない

今回の report にある通り、canonical な address list producer は見つかっていない。
これは重要じゃ。

いまあるのは、

```text id="6svuut"
明示 family を包む API
localIsland 1 個から singleton family を作る API
```

まで。

まだ、

```text id="bidudc"
orbit window から全 pulse address list を生成する
frontier object から canonical list を得る
```

はない。

ここを急いで捏造しなかったのは正しい。

## 2. failure は overlap ではない

これは何度でも言っておく価値がある。

```text id="rnxvdc"
¬ A before B
```

は、

```text id="f8w4xw"
A と B が overlap している
```

ではない。

単に順序が逆な場合もある。
だから今の failure API は、あくまで

```text id="jer4ik"
sorted-before failure
```

であって、overlap theorem ではない。

この注意が source comment に入ったのは大きい。

## 数学的な意味

今回で main root の形はこうなった。

```text id="7rhzq8"
localIsland
  -> interval-pulse address
  -> singleton address family

explicit address list
  -> address family
  -> sorted/failure split

sorted address family
  -> accounted interval family
  -> negative budget
```

これは、かなり実体に近い。

特に重要なのは、`SourcePressureIntervalPulseAddress` がもう単発の住所ではなく、family-level の会計単位へ上がったことじゃ。

今後の目標は、

```text id="0bocgo"
localIsland の明示リスト
  -> address family
  -> sorted/failure
  -> budget
```

へ進めることになる。

## 次の重点

次も **main root 専念** じゃ。
横道は禁止でよい。

次は `SourcePressureLocalIsland` の list を扱うのが自然じゃ。
ただし `SourcePressureLocalIsland n k r j` は `j` に依存しているので、list 化するなら `Σ j, SourcePressureLocalIsland n k r j` の形が安全じゃ。

つまり、

```lean id="nr8yon"
List (Σ j : ℕ, SourcePressureLocalIsland n k r j)
```

を明示 local-island witness list として受け取り、それを address family へ変換する。

これは producer-facing だが、coverage は言わない。
あくまで「与えられた local island witnesses を family にする」だけじゃ。

## 次の Codex 依頼

```text id="7m4bs0"
Checkpoint 155: Main root only — lift explicit local-island witness lists to pulse-address families.

Scope:
Focus only on the main root.

Allowed files:
- DkMath/Collatz/PetalBridge/PressureAccounting.lean
- DkMath/Collatz/PetalBridge/PressureFrontier.lean

Do not modify:
- OneCycle.lean
- ValuationFlowBridge.lean
- ABC files
- NumberTheory files

unless a build/import issue forces a tiny fix.

Context:
Checkpoint 154 added the explicit pulse-address family carrier:

  SourcePressureIntervalPulseAddressFamily

and connected it to sorted/failure predicates and accounted-family budget
wrappers.

Existing relevant objects:

- SourcePressureLocalIsland
- sourcePressureIntervalPulseAddress_of_localIsland
- SourcePressureIntervalPulseAddress
- SourcePressureIntervalPulseAddressFamily
- sourcePressureIntervalPulseAddressFamily_singleton_of_localIsland
- SourcePressureIntervalPulseAddressFamilySortedBefore
- SourcePressureIntervalPulseAddressFamilyHasSortedBeforeFailure
- sourcePressureIntervalPulseAddressFamily_sorted_or_failure
- sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily
- sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily_sum_le_neg_length
- sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily_sum_neg_of_nonempty

Global rules:
- Do not claim maximality.
- Do not claim uniqueness of pressure families.
- Do not claim coverage.
- Do not claim prefix behavior.
- Do not claim union accounting.
- Do not claim Collatz convergence.
- Keep all statements about explicitly supplied local-island witnesses or
  explicitly supplied interval-pulse addresses.
- Failure means sorted-before failure, not overlap, unless extra hypotheses
  prove overlap.

Main goal:
Add an explicit local-island witness list layer and convert it to
SourcePressureIntervalPulseAddressFamily.

Important:
Because SourcePressureLocalIsland is indexed by a depth `j`, use a sigma type
for explicit lists:

  List (Σ j : Nat, SourcePressureLocalIsland n k r j)

Do not invent a canonical producer of all local islands.

Part A: local-island witness alias.

Add a type alias if helpful:

  abbrev SourcePressureLocalIslandWitness
      (n : OddNat) (k r : Nat) :=
    Σ j : Nat, SourcePressureLocalIsland n k r j

If abbrev causes namespace or elaboration friction, skip it and use the sigma
type directly.

Part B: convert one local-island witness to an address.

Define:

  def sourcePressureIntervalPulseAddress_of_localIslandWitness
      {n : OddNat} {k r : Nat}
      (W : Σ j : Nat, SourcePressureLocalIsland n k r j) :
      SourcePressureIntervalPulseAddress n k r :=
    sourcePressureIntervalPulseAddress_of_localIsland n k r W.1 W.2

Adjust field access if Lean prefers `W.fst` / `W.snd`.

Part C: convert a local-island witness list to an address family.

Define:

  def sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList
      {n : OddNat} {k r : Nat}
      (L : List (Σ j : Nat, SourcePressureLocalIsland n k r j)) :
      SourcePressureIntervalPulseAddressFamily n k r :=
    { items := L.map sourcePressureIntervalPulseAddress_of_localIslandWitness }

Prove length wrapper:

  theorem sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList_length
      ...
      :
      (sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList L).items.length =
        L.length

Part D: sorted/failure split for local-island witness lists.

Define sorted/failure predicates by using the produced address family:

  def SourcePressureLocalIslandWitnessListSortedBefore
      {n : OddNat} {k r : Nat}
      (L : List (Σ j : Nat, SourcePressureLocalIsland n k r j)) : Prop :=
    SourcePressureIntervalPulseAddressFamilySortedBefore
      (sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList L)

  def SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
      {n : OddNat} {k r : Nat}
      (L : List (Σ j : Nat, SourcePressureLocalIsland n k r j)) : Prop :=
    SourcePressureIntervalPulseAddressFamilyHasSortedBeforeFailure
      (sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList L)

Prove:

  theorem sourcePressureLocalIslandWitnessList_sorted_or_failure
      {n : OddNat} {k r : Nat}
      (L : List (Σ j : Nat, SourcePressureLocalIsland n k r j)) :
      SourcePressureLocalIslandWitnessListSortedBefore L ∨
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L

Part E: sorted local-island witness list to accounted family.

Define:

  def sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList
      {n : OddNat} {k r : Nat}
      (L : List (Σ j : Nat, SourcePressureLocalIsland n k r j))
      (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
      SourcePressureAccountedIntervalFamily n k r :=
    sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily
      (sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList L)
      hsorted

Prove wrappers:

  theorem sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList_length
      ...
      :
      (sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList
        L hsorted).items.length = L.length

  theorem sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList_sum_le_neg_length
      ...
      :
      (((sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList
        L hsorted).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤
          -((L.length : Nat) : Int)

  theorem sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList_sum_neg_of_nonempty
      ...
      (hL : L ≠ []) :
      (((sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList
        L hsorted).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0

Part F: singleton local-island witness wrappers.

Add convenience wrappers if easy:

  def sourcePressureIntervalPulseAddressFamily_singleton_of_localIslandWitness
      (W : Σ j : Nat, SourcePressureLocalIsland n k r j) :
      SourcePressureIntervalPulseAddressFamily n k r

  theorem sourcePressureIntervalPulseAddressFamily_singleton_of_localIslandWitness_length
      ...
      :
      (...).items.length = 1

Part G: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-155.md

Include:
- whether the sigma alias was added,
- exact name for the local-island witness type or conversion,
- conversion theorem/function names,
- sorted/failure predicates for local-island witness lists,
- sorted-or-failure theorem,
- accounted-family lift and budget wrappers,
- singleton local-island witness wrappers if added,
- explicit note that this checkpoint does not enumerate all local islands,
- explicit note that it does not introduce maximality, uniqueness, coverage,
  prefix behavior, union accounting, or Collatz convergence.

Verification:

  lake build DkMath.Collatz.PetalBridge.PressureAccounting
  lake build DkMath.Collatz.PetalBridge.PressureFrontier
  lake build DkMath.Collatz.PetalBridge

Run:

  rg -n "\\bsorry\\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
  rg -n "\\bsorry\\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean

Also run:

  git diff --check
```

## 総評

よいぞ。
今回は address family carrier が立った。

次は、その family の材料をもう一段実体寄りにして、

```text id="b78q7z"
local island witness list
  -> address family
  -> sorted/failure
  -> accounted family
  -> budget
```

へ進む。

まだ coverage は言わない。
まだ「全 island を列挙した」とも言わない。
ただし、明示的に与えた local island witnesses を安全に会計する道は、かなり太くなってきた。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
index fe8c7806..3db563e9 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
@@ -1162,6 +1162,132 @@ theorem sourcePressureIntervalPulseAddressListHasSortedBeforeFailure_pair_iff
   rw [sourcePressureAccountedIntervalListHasSortedBeforeFailure_pair_iff]
   exact not_congr sourcePressureIntervalPulseAddressBefore_iff_accountedBefore.symm

+/--
+Thin family carrier for explicit interval-pulse addresses.
+
+This wrapper intentionally stores only the supplied address list.  It has no
+coverage, maximality, uniqueness, prefix, disjointness, or union-accounting
+field.  Those properties must be supplied later by separate hypotheses.
+-/
+structure SourcePressureIntervalPulseAddressFamily
+    (n : OddNat) (k r : ℕ) where
+  /-- Explicit interval-pulse addresses. -/
+  items : List (SourcePressureIntervalPulseAddress n k r)
+
+/--
+Empty explicit interval-pulse-address family.
+
+This does not say that the ambient pressure window has no pulses.
+-/
+def sourcePressureIntervalPulseAddressFamily_nil
+    (n : OddNat) (k r : ℕ) :
+    SourcePressureIntervalPulseAddressFamily n k r :=
+  { items := [] }
+
+/--
+Singleton explicit interval-pulse-address family.
+
+This packages one already supplied address and makes no maximality or coverage
+claim.
+-/
+def sourcePressureIntervalPulseAddressFamily_singleton
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    SourcePressureIntervalPulseAddressFamily n k r :=
+  { items := [A] }
+
+/-- Alias for callers that want the producer-facing wording. -/
+def sourcePressureIntervalPulseAddressFamily_singleton_of_address
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    SourcePressureIntervalPulseAddressFamily n k r :=
+  sourcePressureIntervalPulseAddressFamily_singleton A
+
+/--
+Singleton family produced from a local pressure island.
+
+This is the only producer bridge added in this checkpoint.  It uses the
+existing `sourcePressureIntervalPulseAddress_of_localIsland` producer from
+`PressureFrontier` and packages that one explicit address as a singleton
+family.  It does not enumerate all local islands or cover an orbit window.
+-/
+def sourcePressureIntervalPulseAddressFamily_singleton_of_localIsland
+    (n : OddNat) (k r j : ℕ)
+    (hisland : SourcePressureLocalIsland n k r j) :
+    SourcePressureIntervalPulseAddressFamily n k r :=
+  sourcePressureIntervalPulseAddressFamily_singleton
+    (sourcePressureIntervalPulseAddress_of_localIsland n k r j hisland)
+
+/--
+Cons an explicit interval-pulse address onto an explicit family.
+
+This is ordinary list construction only; it does not infer sorting,
+disjointness, or union accounting.
+-/
+def sourcePressureIntervalPulseAddressFamily_cons
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r)
+    (F : SourcePressureIntervalPulseAddressFamily n k r) :
+    SourcePressureIntervalPulseAddressFamily n k r :=
+  { items := A :: F.items }
+
+@[simp]
+theorem sourcePressureIntervalPulseAddressFamily_nil_length
+    (n : OddNat) (k r : ℕ) :
+    (sourcePressureIntervalPulseAddressFamily_nil n k r).items.length = 0 := by
+  rfl
+
+@[simp]
+theorem sourcePressureIntervalPulseAddressFamily_singleton_length
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    (sourcePressureIntervalPulseAddressFamily_singleton A).items.length = 1 := by
+  rfl
+
+@[simp]
+theorem sourcePressureIntervalPulseAddressFamily_cons_length
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r)
+    (F : SourcePressureIntervalPulseAddressFamily n k r) :
+    (sourcePressureIntervalPulseAddressFamily_cons A F).items.length =
+      F.items.length + 1 := by
+  simp [sourcePressureIntervalPulseAddressFamily_cons]
+
+/--
+Family-level adjacent sortedness for explicit interval-pulse addresses.
+
+This is just list sortedness on `F.items`.
+-/
+def SourcePressureIntervalPulseAddressFamilySortedBefore
+    {n : OddNat} {k r : ℕ}
+    (F : SourcePressureIntervalPulseAddressFamily n k r) : Prop :=
+  SourcePressureIntervalPulseAddressListSortedBefore F.items
+
+/--
+Family-level adjacent sorted-before failure.
+
+This is an order obstruction only.  It does not imply interval overlap:
+reversed order is also a sorted-before failure.
+-/
+def SourcePressureIntervalPulseAddressFamilyHasSortedBeforeFailure
+    {n : OddNat} {k r : ℕ}
+    (F : SourcePressureIntervalPulseAddressFamily n k r) : Prop :=
+  SourcePressureIntervalPulseAddressListHasSortedBeforeFailure F.items
+
+/--
+Every explicit interval-pulse-address family is either adjacent-sorted or
+carries an adjacent sorted-before failure.
+
+This is not a coverage, maximality, prefix, union-accounting, or convergence
+statement.
+-/
+theorem sourcePressureIntervalPulseAddressFamily_sorted_or_failure
+    {n : OddNat} {k r : ℕ}
+    (F : SourcePressureIntervalPulseAddressFamily n k r) :
+    SourcePressureIntervalPulseAddressFamilySortedBefore F ∨
+      SourcePressureIntervalPulseAddressFamilyHasSortedBeforeFailure F :=
+  sourcePressureIntervalPulseAddressList_sorted_or_failure F.items
+
 /--
 Build an accounted family from an adjacent-sorted interval-pulse-address list.

@@ -1219,6 +1345,60 @@ theorem
   simpa [sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList]
     using sourcePressureIntervalPulseAddressList_sum_neg_of_nonempty hL

+/--
+Lift a sorted explicit interval-pulse-address family to an accounted interval
+family.
+
+The sorted hypothesis packages the converted intervals as pairwise disjoint.
+No coverage or union accounting is introduced.
+-/
+def sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily
+    {n : OddNat} {k r : ℕ}
+    (F : SourcePressureIntervalPulseAddressFamily n k r)
+    (hsorted : SourcePressureIntervalPulseAddressFamilySortedBefore F) :
+    SourcePressureAccountedIntervalFamily n k r :=
+  sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList
+    F.items hsorted
+
+@[simp]
+theorem sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily_length
+    {n : OddNat} {k r : ℕ}
+    (F : SourcePressureIntervalPulseAddressFamily n k r)
+    (hsorted : SourcePressureIntervalPulseAddressFamilySortedBefore F) :
+    (sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily
+      F hsorted).items.length = F.items.length := by
+  simp [sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily]
+
+/-- Budget wrapper for a sorted explicit interval-pulse-address family. -/
+theorem sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily_sum_le_neg_length
+    {n : OddNat} {k r : ℕ}
+    (F : SourcePressureIntervalPulseAddressFamily n k r)
+    (hsorted : SourcePressureIntervalPulseAddressFamilySortedBefore F) :
+    (((sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily
+      F hsorted).items).map
+      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤
+        -((F.items.length : ℕ) : ℤ) := by
+  simpa [sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily]
+    using
+      sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList_sum_le_neg_length
+        F.items hsorted
+
+/--
+Nonempty budget wrapper for a sorted explicit interval-pulse-address family.
+-/
+theorem sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily_sum_neg_of_nonempty
+    {n : OddNat} {k r : ℕ}
+    (F : SourcePressureIntervalPulseAddressFamily n k r)
+    (hsorted : SourcePressureIntervalPulseAddressFamilySortedBefore F)
+    (hF : F.items ≠ []) :
+    (((sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily
+      F hsorted).items).map
+      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0 := by
+  simpa [sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily]
+    using
+      sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList_sum_neg_of_nonempty
+        hsorted hF
+
 /-- Singleton sorted-family budget wrapper. -/
 theorem sourcePressureAccountedIntervalFamily_sorted_singleton_sum_le_neg_one
     {n : OddNat} {k r : ℕ}
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-154.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-154.md
new file mode 100644
index 00000000..c6b0fd80
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-154.md
@@ -0,0 +1,193 @@
+# report-petal-154
+
+Checkpoint: 154
+
+Subject: main root only; explicit interval-pulse-address family carrier and
+bridge to pressure accounting.
+
+## Summary
+
+This checkpoint extended:
+
+```text
+DkMath.Collatz.PetalBridge.PressureAccounting
+```
+
+No new Lean file was created.
+
+No `OneCycle`, `ValuationFlowBridge`, ABC, or NumberTheory files were modified.
+
+The new API wraps explicitly supplied `SourcePressureIntervalPulseAddress`
+lists as a thin family carrier and connects that carrier to the sorted/failure
+and budget API from checkpoint 153.
+
+## Family Carrier
+
+Added:
+
+```lean
+structure SourcePressureIntervalPulseAddressFamily
+    (n : OddNat) (k r : Nat) where
+  items : List (SourcePressureIntervalPulseAddress n k r)
+```
+
+This carrier intentionally has no fields for:
+
+```text
+coverage
+maximality
+uniqueness
+prefix behavior
+disjointness
+union accounting
+convergence
+```
+
+It is just an explicit list wrapper.
+
+## Constructors
+
+Added:
+
+```lean
+def sourcePressureIntervalPulseAddressFamily_nil
+def sourcePressureIntervalPulseAddressFamily_singleton
+def sourcePressureIntervalPulseAddressFamily_cons
+```
+
+Also added:
+
+```lean
+def sourcePressureIntervalPulseAddressFamily_singleton_of_address
+```
+
+This is an alias for callers that want producer-facing wording.
+
+Length wrappers were added:
+
+```lean
+theorem sourcePressureIntervalPulseAddressFamily_nil_length
+theorem sourcePressureIntervalPulseAddressFamily_singleton_length
+theorem sourcePressureIntervalPulseAddressFamily_cons_length
+```
+
+## Sorted / Failure Predicates
+
+Added:
+
+```lean
+def SourcePressureIntervalPulseAddressFamilySortedBefore
+def SourcePressureIntervalPulseAddressFamilyHasSortedBeforeFailure
+```
+
+and:
+
+```lean
+theorem sourcePressureIntervalPulseAddressFamily_sorted_or_failure
+```
+
+The failure predicate is explicitly documented in the source:
+
+```text
+Family sorted-before failure is an order obstruction only.
+It does not imply interval overlap; reversed order is also a failure.
+```
+
+## Accounted-Family Lift
+
+Added:
+
+```lean
+def sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily
+```
+
+and wrappers:
+
+```lean
+theorem sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily_length
+theorem sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily_sum_le_neg_length
+theorem sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily_sum_neg_of_nonempty
+```
+
+The sorted hypothesis is used only to package the converted interval-pulse
+addresses as an accounted family.  The budget remains an explicit-list cost
+sum, not union accounting.
+
+## Producer Search Result
+
+`PressureFrontier.lean` was searched for list-producing frontier objects.
+
+Found:
+
+```lean
+def sourcePressureIntervalPulseAddress_of_localIsland
+```
+
+This produces one `SourcePressureIntervalPulseAddress` from one
+`SourcePressureLocalIsland`.
+
+No canonical producer of address lists was found in this checkpoint.
+
+Therefore no list producer was fabricated.
+
+Only the thin singleton producer bridge was added:
+
+```lean
+def sourcePressureIntervalPulseAddressFamily_singleton_of_localIsland
+```
+
+This packages the existing single-address producer into a singleton family.
+It does not enumerate all local islands and does not cover an orbit window.
+
+## Non-Claims
+
+This checkpoint does not introduce:
+
+```text
+maximality
+uniqueness
+coverage
+prefix behavior
+union accounting
+Collatz convergence
+```
+
+All statements remain about explicitly supplied or explicitly singleton-produced
+interval-pulse addresses.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureAccounting
+lake build DkMath.Collatz.PetalBridge.PressureFrontier
+lake build DkMath.Collatz.PetalBridge
+rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+```
+
+The `rg` checks returned no matches.
+
+The build still reports the existing unrelated warning:
+
+```text
+DkMath.NumberTheory.ZsigmondyCyclotomicResearch uses sorry
+```
+
+That warning is outside checkpoint 154.
+
+## Next Inference
+
+The next step should remain producer-facing but conservative:
+
+```text
+frontier object
+  -> explicit address or address list, if already available
+  -> SourcePressureIntervalPulseAddressFamily
+  -> sorted/failure split
+  -> accounted-family budget only on the sorted branch
+```
+
+Do not invent coverage.  A coverage or maximality theorem should only appear
+after a real frontier producer carries those hypotheses.
````
`````
