# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis

gch: 6610989878289e40bb1da5463720d94ab196c502

## Report

cp185 を完了しました。

`PressureAdjacentDiagnosis.lean` に、二要素 list の normal form を追加しました。

追加内容:

- `SourcePressureLocalIslandWitnessAdjacentPairInList.two_iff_head`
- `.two_eq`
- `SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_two_reversed`
- `.exists_reversed_of_two`
- `.two_iff`
- `sourcePressureLocalIslandWitnessList_failure_two_exists_reversed_of_noAdjacentOverlap`

これで diagnostic の最小形を `[W1, W2]` かつ `W2 before W1` として扱えるようになりました。あくまで二要素 list 専用で、任意 list の canonical diagnosis や列挙、union accounting には踏み込んでいません。

検証済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b" ...
git diff --check
```

対象 3 ファイルの no-sorry は no match。`git diff --check` も通過です。

レポートも追加しました。

`lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-185.md`

## Review

## 結論

うむ、Checkpoint 185 は **採用** じゃ 👍️
これで diagnostic carrier の **二要素 list における最小正規形** が固まった。

追加された中心は、

```lean id="gx4e1t"
SourcePressureLocalIslandWitnessAdjacentPairInList.two_iff_head
SourcePressureLocalIslandWitnessAdjacentPairInList.two_eq
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_two_reversed
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_reversed_of_two
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.two_iff
sourcePressureLocalIslandWitnessList_failure_two_exists_reversed_of_noAdjacentOverlap
```

じゃな。これで diagnostic の最小形を `[W1, W2]` かつ `W2 before W1` として扱えるようになった。一方で、任意 list の canonical diagnosis、列挙、union accounting には踏み込んでいない。境界管理もよい。

## 実装レビュー

## 1. `two_iff_head` が良い土台

```lean id="3ysxui"
SourcePressureLocalIslandWitnessAdjacentPairInList.two_iff_head
```

により、二要素 list `[W1, W2]` の adjacent pair は head pair `W1, W2` だけだと固定できた。

これは小さいが重要じゃ。
以後、二要素 list に diagnostic があれば、その pair は必ず `W1, W2` だと Lean が理解できる。

## 2. `of_two_reversed` で最小構成が閉じた

```lean id="766xty"
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_two_reversed
```

はとても良い。

```text id="mlzx1v"
W2 before W1
  -> diagnostic [W1, W2]
```

という最小生成を与えている。

しかも budget `≤ -2`、sum `< 0`、length `= 2` は既存 reversed-pair family theorem から供給しているので、証明責任もきれいに分離されている。

## 3. `exists_reversed_of_two` と `two_iff` が正規形を完成させた

二要素 list に diagnostic があるなら、

```text id="dzeevm"
∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1
```

へ戻せる。

つまり、

```text id="i73zzm"
diagnostic [W1, W2]
  ↔
W2 before W1 と pair-local facts
```

という正規形ができた。

これは今後、三要素以上の list を head / tail に分解するための基礎になる。

## 数学的意味

今回の到達点はこうじゃ。

```text id="jry8vp"
diagnostic の最小単位は、
二つの witness W1, W2 の逆順関係 W2 before W1 である。
```

DkMath 的に言えば、

```text id="xewv73"
回収可能な局所破綻は、
最小形では二項取引として現れる。
```

これはかなり良い。
これまで「diagnostic は one pair-local family」と言っていたが、今回それが `[W1, W2]` の正規形として Lean 上で固定された。

## 注意点

## 1. 任意 list の canonical diagnosis ではない

今回の canonical 性は **二要素 list 限定** じゃ。

まだ次は言っていない。

```text id="b6q8xx"
長い list で最初の diagnostic を選ぶ
全 diagnostic を列挙する
最左 diagnostic を定義する
```

ここは未到達。

## 2. `two_iff` の reverse 側は supplied facts を使わない

`two_iff` の reverse direction は、与えられた budget facts を replay せず、`of_two_reversed` で既存 theorem から再構成している。これは問題ない。むしろ証明が安定する。

ただし下流で「渡した facts と同一の証明項」を期待する設計には向かない。
現状では Prop なので問題なしじゃ。

## 次の checkpoint 方針

次は report の Next inference 通り、**三要素 list の分解** が自然じゃ。

狙いは、

```text id="tdc4pj"
diagnostic [W1, W2, W3]
  -> head pair W1 W2 の reversed diagnostic
     or tail pair W2 W3 の diagnostic
```

じゃ。

これは任意 list の列挙ではない。
三要素 list 限定の bounded decomposition じゃ。

## 次の Codex 指示

```text id="mprt6q"
Checkpoint 186: Main root only — length-three decomposition for the bundled diagnostic carrier.

Scope:
Focus on the refactored Collatz/PetalBridge pressure modules.

Primary target file:
- DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean

Allowed supporting file, only if needed:
- DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean

Do not modify:
- PressureAccounting.lean unless import/order forces a tiny fix
- OneCycle.lean
- ValuationFlowBridge.lean
- ABC files
- NumberTheory files

Do not rename or rewrite previous theorem statements.

Context:
Checkpoint 185 added the length-two normal form:

- SourcePressureLocalIslandWitnessAdjacentPairInList.two_iff_head
- SourcePressureLocalIslandWitnessAdjacentPairInList.two_eq
- SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_two_reversed
- SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_reversed_of_two
- SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.two_iff
- sourcePressureLocalIslandWitnessList_failure_two_exists_reversed_of_noAdjacentOverlap

The diagnostic represents one recovered adjacent pair and its pair-local
accounted family.

Global guardrails:
- Do not claim global local-island coverage.
- Do not claim maximality.
- Do not claim uniqueness for arbitrary lists.
- Do not claim prefix behavior.
- Do not claim arbitrary list sorting.
- Do not claim canonical first diagnosis for arbitrary lists.
- Do not enumerate all diagnoses.
- Do not claim union accounting.
- Do not claim overlap repair.
- Do not claim Collatz convergence.
- Keep all statements local to explicitly supplied witness lists.
- Recovered budgets remain pair-local.
- Do not aggregate multiple recovered pairs.
- Do not create a list-wide accounted interval union.
- Do not prove disjointness between multiple recovered families.

Main goal:
Add a bounded length-three decomposition for the bundled diagnostic carrier.
For `[W1, W2, W3]`, a diagnostic is either:
- the head pair `W1, W2`, represented by a reversed-before witness
  `SourcePressureLocalIslandWitnessBefore W2 W1`; or
- a diagnostic in the tail list `[W2, W3]`.

Part A: adjacent-pair length-three head-or-tail decomposition.

Prove either an iff or an extractor.

Preferred theorem:

  theorem SourcePressureLocalIslandWitnessAdjacentPairInList.three_head_or_tail
      {n : OddNat} {k r : Nat}
      {W1 W2 W3 A B : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureLocalIslandWitnessAdjacentPairInList [W1, W2, W3] A B) :
      (A = W1 ∧ B = W2) ∨
        SourcePressureLocalIslandWitnessAdjacentPairInList [W2, W3] A B

Suggested proof:
- cases h.
- head case: left, simp.
- tail case: right, exact the tail proof.

If the inductive structure makes this awkward, prove an iff form:

  SourcePressureLocalIslandWitnessAdjacentPairInList [W1, W2, W3] A B ↔
    (A = W1 ∧ B = W2) ∨
      SourcePressureLocalIslandWitnessAdjacentPairInList [W2, W3] A B

Part B: diagnostic length-three head-or-tail decomposition.

Prove:

  theorem
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_head_or_tail
      {n : OddNat} {k r : Nat}
      {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
      (h :
        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
          [W1, W2, W3]) :
      (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
        let F :=
          sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
            W1 W2 hrev
        (((F.items).map
          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
          (((F.items).map
            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
          F.items.length = 2)
      ∨
        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
          [W2, W3]

Suggested proof:
- unpack h.exists_pair to get A B hin hrev hbudget hneg hlen.
- apply Part A to hin.
- head branch:
  substitute A = W1, B = W2 and return left with hrev and stored facts.
- tail branch:
  build right using
    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
    with the tail address and the same hrev, hbudget, hneg, hlen.

Part C: diagnostic length-three iff, optional.

If Part B is easy, optionally prove:

  theorem
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_iff_head_or_tail
      {n : OddNat} {k r : Nat}
      {W1 W2 W3 : SourcePressureLocalIslandWitness n k r} :
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
        [W1, W2, W3] ↔
      ((∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
        let F :=
          sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
            W1 W2 hrev
        (((F.items).map
          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
          (((F.items).map
            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
          F.items.length = 2)
       ∨
        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
          [W2, W3])

Reverse direction:
- left branch:
  use `of_two_reversed hrev`, then lift with `.of_tail`.
  More directly:
    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail
      (SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_two_reversed hrev)
- right branch:
  use `.of_tail`.

Do not force the iff if dependent proof terms make it noisy.  The head-or-tail
extractor is enough.

Part D: failure + no-overlap length-three corollary.

Only if Part B succeeds, prove:

  theorem
      sourcePressureLocalIslandWitnessList_failure_three_diagnostic_head_or_tail_of_noAdjacentOverlap
      {n : OddNat} {k r : Nat}
      {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
      (h :
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2, W3])
      (hno :
        SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
          [W1, W2, W3]) :
      (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
        let F :=
          sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
            W1 W2 hrev
        (((F.items).map
          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
          (((F.items).map
            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
          F.items.length = 2)
      ∨
        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
          [W2, W3]

Suggested proof:
- first obtain diagnostic from:
  sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
- then apply `.three_head_or_tail`.

Part E: optional fully normalized length-three corollary.

Only if easy, combine the tail two-element normal form so the result becomes:

  either W2 before W1
  or W3 before W2

with the corresponding pair-local facts.

Name suggestion:

  sourcePressureLocalIslandWitnessList_failure_three_exists_reversed_pair_of_noAdjacentOverlap

But do not force this.  It may duplicate too much statement text.

Part F: do not introduce aggregation.

Do not prove:
- a list of all diagnostics,
- canonical first diagnosis for arbitrary lists,
- sum over all recovered diagnostics,
- disjointness between multiple recovered families,
- union accounting,
- coverage,
- overlap repair.

Part G: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-186.md

Include:
- adjacent-pair length-three head-or-tail theorem;
- diagnostic length-three head-or-tail theorem;
- optional iff theorem if added;
- optional failure + no-overlap corollary if added;
- explicit note that this is only a three-element explicit-list bounded decomposition;
- explicit note that no aggregation, union accounting, coverage, maximality,
  uniqueness for arbitrary lists, sorting, canonical first diagnosis for
  arbitrary lists, enumeration, overlap repair, or Collatz convergence was
  introduced;
- verification results.

Verification:

  lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
  lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
  lake build DkMath.Collatz.PetalBridge.PressureAccounting
  lake build DkMath.Collatz.PetalBridge.PressureFrontier
  lake build DkMath.Collatz.PetalBridge

Run no-sorry checks:

  rg -n "\\bsorry\\b" \
    DkMath/Collatz/PetalBridge/PressureAccounting.lean \
    DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
    DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean

Also run:

  git diff --check
```

## 総評

cp185 は大きい。
これで diagnostic の最小形が、

```text id="bnhv2c"
[W1, W2] かつ W2 before W1
```

として固定された。

次は三要素分解じゃ。

```text id="yv128p"
diagnostic [W1, W2, W3]
  -> head pair W1,W2
     or tail pair W2,W3
```

ここまで固まると、任意 list に行く前の bounded decomposition がかなり安定する。
まだ合算しない。まだ列挙しない。
まずは三要素の分岐構造を Lean に刻むのがよい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
index f41c2920..4ee290c3 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
@@ -278,6 +278,35 @@ theorem SourcePressureLocalIslandWitnessAdjacentPairInList.singleton_false
   intro h
   exact h
 
+/--
+In a two-element explicit witness list, the only adjacent-pair address is the
+head pair.
+
+This is a two-element normal form only.  It does not choose a canonical pair in
+longer lists and does not enumerate diagnostics.
+-/
+theorem SourcePressureLocalIslandWitnessAdjacentPairInList.two_iff_head
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 A B : SourcePressureLocalIslandWitness n k r} :
+    SourcePressureLocalIslandWitnessAdjacentPairInList [W1, W2] A B ↔
+      A = W1 ∧ B = W2 := by
+  constructor
+  · intro h
+    rcases h with hhead | htail
+    · exact hhead
+    · exact False.elim
+        (SourcePressureLocalIslandWitnessAdjacentPairInList.singleton_false htail)
+  · rintro ⟨rfl, rfl⟩
+    exact SourcePressureLocalIslandWitnessAdjacentPairInList.head
+
+/-- Extract the head-pair equality from a two-element adjacent-pair address. -/
+theorem SourcePressureLocalIslandWitnessAdjacentPairInList.two_eq
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 A B : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureLocalIslandWitnessAdjacentPairInList [W1, W2] A B) :
+    A = W1 ∧ B = W2 :=
+  SourcePressureLocalIslandWitnessAdjacentPairInList.two_iff_head.mp h
+
 /--
 A list-level carrier for "some adjacent pair in this explicit list has an
 adjacent diagnosis".
@@ -966,6 +995,87 @@ theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyD
     (SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail_tail
       h)
 
+set_option linter.style.longLine false in
+/--
+Build the bundled diagnostic directly from a reversed two-witness list.
+
+For `[W1, W2]`, the only adjacent-pair address is the head pair `W1, W2`.
+Thus a witness that `W2` is before `W1` gives the recovered pair-local
+accounted family immediately.
+-/
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_two_reversed
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (hrev : SourcePressureLocalIslandWitnessBefore W2 W1) :
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+      [W1, W2] :=
+  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
+    SourcePressureLocalIslandWitnessAdjacentPairInList.head
+    hrev
+    (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_le_neg_two
+      W1 W2 hrev)
+    (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg
+      W1 W2 hrev)
+    (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length
+      W1 W2 hrev)
+
+set_option linter.style.longLine false in
+/--
+Extract the reversed-before witness and the bundled pair-local facts from a
+two-element diagnostic.
+
+This is a two-element explicit-list normal form only.  It does not choose a
+canonical diagnostic in longer lists.
+-/
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_reversed_of_two
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (h :
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+        [W1, W2]) :
+    ∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
+      let F :=
+        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+          W1 W2 hrev
+      (((F.items).map
+        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
+        (((F.items).map
+          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
+        F.items.length = 2 := by
+  rcases h.exists_pair with ⟨A, B, hin, hrev, hbudget, hneg, hlen⟩
+  rcases SourcePressureLocalIslandWitnessAdjacentPairInList.two_eq hin with
+    ⟨rfl, rfl⟩
+  exact ⟨hrev, hbudget, hneg, hlen⟩
+
+set_option linter.style.longLine false in
+/--
+Two-element normal form for the bundled diagnostic carrier.
+
+The equivalence is only for the explicit two-witness list `[W1, W2]`.  It does
+not assert uniqueness or canonical selection for arbitrary lists.
+-/
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.two_iff
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r} :
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+      [W1, W2] ↔
+    ∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
+      let F :=
+        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+          W1 W2 hrev
+      (((F.items).map
+        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
+        (((F.items).map
+          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
+        F.items.length = 2 := by
+  constructor
+  · exact
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_reversed_of_two
+  · rintro ⟨hrev, _hbudget, _hneg, _hlen⟩
+    exact
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_two_reversed
+        hrev
+
 /--
 Expose the actual pair-local accounted interval family object stored by the
 recovered adjacent-family carrier.
@@ -1152,6 +1262,34 @@ theorem
   (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_no_overlap
     h hno).toDiagnostic
 
+set_option linter.style.longLine false in
+/--
+Two-element consumer form: failure plus named no-adjacent-overlap yields the
+reversed-before witness for the only adjacent pair.
+
+This is only the `[W1, W2]` normal form.  It does not select a canonical pair in
+longer lists.
+-/
+theorem
+    sourcePressureLocalIslandWitnessList_failure_two_exists_reversed_of_noAdjacentOverlap
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2])
+    (hno :
+      SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction [W1, W2]) :
+    ∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
+      let F :=
+        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+          W1 W2 hrev
+      (((F.items).map
+        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
+        (((F.items).map
+          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
+        F.items.length = 2 :=
+  (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
+    h hno).exists_reversed_of_two
+
 set_option linter.style.longLine false in
 /--
 Failure plus named no-adjacent-overlap, projected directly to the pair-local
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-185.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-185.md
new file mode 100644
index 00000000..87df2402
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-185.md
@@ -0,0 +1,191 @@
+# report-petal-185
+
+Date: 2026-07-06
+
+## Scope
+
+Checkpoint 185 adds a length-two normal form for the bundled recovered
+accounted-family diagnostic carrier in
+`DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis`.
+
+This is only about the explicit two-witness list `[W1, W2]`.  It does not choose
+a canonical diagnostic in longer lists and does not enumerate all diagnostics.
+
+## Adjacent-pair normal form
+
+Added:
+
+```lean
+theorem
+  SourcePressureLocalIslandWitnessAdjacentPairInList.two_iff_head
+```
+
+For a two-element explicit witness list, the only adjacent-pair address is the
+head pair:
+
+```lean
+SourcePressureLocalIslandWitnessAdjacentPairInList [W1, W2] A B ↔
+  A = W1 ∧ B = W2
+```
+
+Also added the extractor:
+
+```lean
+theorem
+  SourcePressureLocalIslandWitnessAdjacentPairInList.two_eq
+```
+
+This is a convenience projection used by the diagnostic normal form.
+
+## Diagnostic constructor
+
+Added:
+
+```lean
+theorem
+  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_two_reversed
+```
+
+For `[W1, W2]`, a witness
+
+```lean
+SourcePressureLocalIslandWitnessBefore W2 W1
+```
+
+directly constructs the bundled diagnostic.  The budget facts are supplied by
+the existing reversed-pair accounted-family theorems:
+
+- `sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_le_neg_two`
+- `sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg`
+- `sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length`
+
+## Diagnostic extractor
+
+Added:
+
+```lean
+theorem
+  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_reversed_of_two
+```
+
+This extracts the reversed-before witness and the bundled pair-local facts from
+a diagnostic on `[W1, W2]`.
+
+The proof uses `two_eq` to normalize the stored adjacent-pair address to
+`A = W1` and `B = W2`, then returns the stored reversed-pair family facts.
+
+## Iff form
+
+Added:
+
+```lean
+theorem
+  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.two_iff
+```
+
+This packages the constructor and extractor into a two-element normal-form
+equivalence.
+
+The reverse direction uses the existing reversed-pair theorems again through
+`of_two_reversed`, so the supplied existential facts do not need to be replayed.
+
+## Failure + no-overlap corollary
+
+Added:
+
+```lean
+theorem
+  sourcePressureLocalIslandWitnessList_failure_two_exists_reversed_of_noAdjacentOverlap
+```
+
+For a two-element list, sorted-before failure plus the named no-adjacent-overlap
+predicate yields the reversed-before witness for the only possible adjacent
+pair and returns the paired budget facts.
+
+## Guardrails preserved
+
+This checkpoint did not introduce:
+
+- global local-island coverage;
+- maximality;
+- uniqueness for arbitrary lists;
+- prefix behavior;
+- arbitrary list sorting;
+- canonical first diagnosis for arbitrary lists;
+- enumeration of all diagnoses;
+- union accounting;
+- overlap repair;
+- Collatz convergence;
+- aggregation of multiple recovered pairs;
+- a list-wide accounted interval union;
+- disjointness between multiple recovered families.
+
+Recovered budgets remain pair-local.
+
+## File-size check
+
+Current line counts:
+
+```text
+1494 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+1391 lean/dk_math/DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
+1896 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+```
+
+`PressureAdjacentDiagnosis.lean` remains below the 2000-line split threshold.
+
+## Verification
+
+Builds:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
+lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
+lake build DkMath.Collatz.PetalBridge.PressureAccounting
+lake build DkMath.Collatz.PetalBridge.PressureFrontier
+lake build DkMath.Collatz.PetalBridge
+```
+
+All completed successfully.
+
+Known unrelated warning:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
+
+This warning is outside the checkpoint scope and was not modified.
+
+No-sorry check on the targeted pressure files:
+
+```text
+rg -n "\bsorry\b" \
+  DkMath/Collatz/PetalBridge/PressureAccounting.lean \
+  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
+  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+```
+
+Result: no matches.  `rg` exited with code `1`, which is the expected no-match
+result.
+
+Whitespace check:
+
+```text
+git diff --check
+```
+
+Result: passed.
+
+## Next inference
+
+The diagnostic carrier now has a clean minimal two-element normal form:
+
+```text
+[W1, W2] with W2 before W1
+```
+
+The next safe extension is probably another bounded structural theorem, for
+example a length-three decomposition that says a diagnostic on `[W1, W2, W3]`
+is either the head-pair normal form or a tail-lifted two-element normal form.
+That should still avoid arbitrary enumeration and list-wide accounting.
````
`````
