# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis

gch: 746127951a3702ab994dd39fbbde87892109efb0

## Report

cp184 を完了しました。

`PressureAdjacentDiagnosis.lean` に、diagnostic carrier の基本構造 API を追加しました。

追加内容:

- `SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.nil_false`
- `.singleton_false`
- `.of_tail`
- `.of_tail_tail`
- `.of_tail_tail_tail`

`of_tail` は同じ pair-local family をそのまま保ち、隣接ペアの list address だけを tail lift します。aggregation、union accounting、coverage、列挙、canonical first diagnosis には踏み込んでいません。

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

`lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-184.md`

## Review

## 結論

うむ、Checkpoint 184 は **採用** じゃ 👍️
`Diagnostic` carrier に、空 list / singleton の否定と、tail lift 系の構文 API が入った。

追加された中心は、

```lean id="wgs4dc"
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.nil_false
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.singleton_false
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail_tail
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail_tail_tail
```

じゃな。`of_tail` は同じ pair-local family、同じ `hrev`、同じ budget facts を保ち、隣接 pair の list address だけを tail lift する。aggregation、union accounting、coverage、列挙、canonical first diagnosis には踏み込んでいない。境界管理はよい。

## 実装レビュー

## 1. nil / singleton false は自然

diagnostic は必ず adjacent pair を含む。

したがって、

```lean id="bnvpef"
[]
[W]
```

には diagnostic が存在しない。

これは `SourcePressureLocalIslandWitnessAdjacentPairInList.nil_false` / `.singleton_false` に落としていて、実装も意味も素直じゃ。

## 2. `of_tail` はかなり重要

今回の本命はこれじゃ。

```lean id="5ykmzt"
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail
```

これは、

```text id="ifvtg9"
W2 :: rest に diagnostic があるなら、
W1 :: W2 :: rest にも diagnostic がある
```

を言う。

ただし新しい diagnostic を探しているのではない。
既存の diagnostic を、list の外側へ一段持ち上げているだけじゃ。

ここが大事。

```text id="1x4k6u"
same A B
same hrev
same pair-local family
same budget ≤ -2
same sum < 0
same length = 2
```

変わるのは list address だけ。
この設計は安全じゃ。

## 3. bounded tail helpers も妥当

```lean id="jkj6sc"
of_tail_tail
of_tail_tail_tail
```

は、既存の adjacent-diagnosis API と同じ雰囲気で、短い明示 list の構文証明に使いやすい。

任意長 recursive lift には踏み込んでいない。
これも正しい。

## 数学的意味

今回で、diagnostic は list 構文の中を移動できるようになった。

```text id="l0eczu"
tail 側で発見された pair-local diagnostic は、
head を追加しても失われない。
```

これは当然に見えるが、Lean では重要じゃ。
今後、failure の one-step split や tail branch を扱うとき、tail 側の diagnostic を元 list に戻す補題として使える。

DkMath 的には、

```text id="f8e2cp"
局所回収会計は、
明示 list の外側に head が追加されても保存される。
```

ということじゃな。

## 注意点

## 1. `of_tail` は探索ではない

これは「tail に diagnostic があるなら lifted list にもある」という補題であって、

```text id="3rzj9v"
list 内を探索して diagnostic を見つける
```

わけではない。

探索・分類・enumeration ではない。
ここは守れている。

## 2. bounded helper は便利だが増やしすぎ注意

`of_tail_tail_tail` までは実用上よい。
しかし今後 `of_tail_tail_tail_tail` のように無限に増やすのは避けたい。

次は tail helper を伸ばすより、**最小形である length-two diagnostic の正規形** を固める方がよい。

## 次の checkpoint 方針

次は、report の Next inference に近く、

```text id="xcey6v"
length two が diagnostic の最小実体である
```

を Lean API として固定するのが良い。

つまり、

```text id="f5edn1"
[W1, W2] に diagnostic があるなら、
それは head adjacent pair W1 W2 から来ている。
```

また逆に、

```text id="7n13yx"
W2 before W1 があれば、
[W1, W2] は直接 diagnostic を持つ。
```

この二方向を作る。

これにより、diagnostic の最小形が明確になる。

## 次の Codex 指示

```text id="qkhask"
Checkpoint 185: Main root only — length-two normal form for the bundled diagnostic carrier.

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
Checkpoint 184 added structural API for the bundled diagnostic carrier:

- SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.nil_false
- SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.singleton_false
- SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail
- SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail_tail
- SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail_tail_tail

The diagnostic still represents one recovered adjacent pair and its pair-local
accounted family.

Global guardrails:
- Do not claim global local-island coverage.
- Do not claim maximality.
- Do not claim uniqueness.
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
Add length-two normal-form helpers for the bundled diagnostic carrier.
For a two-element explicit witness list `[W1, W2]`, any adjacent-pair address is
the head pair, and a reversed-before witness `SourcePressureLocalIslandWitnessBefore W2 W1`
directly gives the diagnostic.

Part A: length-two adjacent-pair address normal form.

If not already available, prove:

  theorem SourcePressureLocalIslandWitnessAdjacentPairInList.two_iff_head
      {n : OddNat} {k r : Nat}
      {W1 W2 A B : SourcePressureLocalIslandWitness n k r} :
      SourcePressureLocalIslandWitnessAdjacentPairInList [W1, W2] A B ↔
        A = W1 ∧ B = W2

Suggested proof:
- forward:
  intro h
  cases h
  - head case: simp
  - tail case: contradiction using
    SourcePressureLocalIslandWitnessAdjacentPairInList.singleton_false
- backward:
  rintro ⟨rfl, rfl⟩
  exact SourcePressureLocalIslandWitnessAdjacentPairInList.head

If the existing inductive constructors make exact equality hard, split this into
a weaker extractor theorem instead:

  theorem SourcePressureLocalIslandWitnessAdjacentPairInList.two_eq
      (h : SourcePressureLocalIslandWitnessAdjacentPairInList [W1, W2] A B) :
      A = W1 ∧ B = W2

Part B: construct a diagnostic directly from a reversed length-two pair.

Prove:

  theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_two_reversed
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      (hrev : SourcePressureLocalIslandWitnessBefore W2 W1) :
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
        [W1, W2]

Suggested proof:
- use `.of_pair`
- adjacent address is `SourcePressureLocalIslandWitnessAdjacentPairInList.head`
- budget facts should come from existing reversed-pair facts:
  sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_le_neg_two
  sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg
  sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length

Part C: extract the reversed-before witness from a length-two diagnostic.

Prove:

  theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_reversed_of_two
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      (h :
        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
          [W1, W2]) :
      ∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
        let F :=
          sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
            W1 W2 hrev
        (((F.items).map
          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
          (((F.items).map
            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
          F.items.length = 2

Suggested proof:
- unpack `h.exists_pair` to get A B hin hrev hbudget hneg hlen.
- use Part A to obtain `A = W1` and `B = W2`.
- substitute.
- return hrev and the three facts.

If dependent substitution of `hrev` becomes annoying, use `cases` on the pair
address directly instead of proving Part A separately:
- `cases hin`
- head case gives the desired pair
- tail case contradicts singleton false.

Part D: optional iff theorem.

If Parts B and C are easy, prove:

  theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.two_iff
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r} :
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
        [W1, W2] ↔
      ∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
        let F :=
          sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
            W1 W2 hrev
        (((F.items).map
          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
          (((F.items).map
            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
          F.items.length = 2

Do not force the iff if dependent equality makes it costly.  Constructor and
extractor theorems are enough.

Part E: optional failure + no-overlap length-two corollary.

Only if easy, prove:

  theorem
      sourcePressureLocalIslandWitnessList_failure_two_exists_reversed_of_noAdjacentOverlap
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      (h :
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2])
      (hno :
        SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction [W1, W2]) :
      ∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
        let F :=
          sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
            W1 W2 hrev
        (((F.items).map
          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
          (((F.items).map
            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
          F.items.length = 2

Proof:
- use
  sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
- then apply the Part C extractor.

Part F: do not introduce aggregation.

Do not prove:
- a list of all diagnostics,
- a canonical first diagnosis for arbitrary lists,
- sum over all recovered diagnostics,
- disjointness between multiple recovered families,
- union accounting,
- coverage,
- overlap repair.

Part G: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-185.md

Include:
- adjacent-pair length-two normal form theorem, if added;
- direct diagnostic constructor from a reversed length-two pair;
- extractor from length-two diagnostic to reversed-before witness;
- optional iff theorem if added;
- optional failure + noAdjacentOverlap length-two corollary if added;
- explicit note that this is only a two-element explicit-list normal form;
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

cp184 は良い構文補助じゃ。
diagnostic が list の tail 側に埋もれていても、head を足して持ち上げられるようになった。

次は **二要素 list の正規形**。
これで diagnostic の最小形が、

```text id="o6c9us"
[W1, W2] with W2 before W1
```

として固定される。

そこまで閉じれば、diagnostic は「局所二項回収会計」としてかなり扱いやすくなるぞ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
index ed8b4519..f41c2920 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
@@ -880,6 +880,92 @@ theorem
   rcases h.exists_pair with ⟨A, B, hin, hrev, _hbudget, _hneg, hlen⟩
   exact ⟨A, B, hin, hrev, hlen⟩

+/--
+The empty explicit witness list cannot carry a recovered accounted-family
+diagnostic, because it contains no adjacent pair address.
+-/
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.nil_false
+    {n : OddNat} {k r : ℕ} :
+    ¬ SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+      ([] : List (SourcePressureLocalIslandWitness n k r)) := by
+  rintro ⟨A, B, hin, _⟩
+  exact SourcePressureLocalIslandWitnessAdjacentPairInList.nil_false hin
+
+set_option linter.style.longLine false in
+/--
+A singleton explicit witness list cannot carry a recovered accounted-family
+diagnostic, because it contains no adjacent pair address.
+-/
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.singleton_false
+    {n : OddNat} {k r : ℕ}
+    {W : SourcePressureLocalIslandWitness n k r} :
+    ¬ SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic [W] := by
+  rintro ⟨A, B, hin, _⟩
+  exact SourcePressureLocalIslandWitnessAdjacentPairInList.singleton_false hin
+
+set_option linter.style.longLine false in
+/--
+Lift a recovered accounted-family diagnostic through a newly supplied head.
+
+The recovered family, reversed-before witness, and all budget facts are
+unchanged.  Only the adjacent-pair address is transported from the tail list to
+the larger enclosing list.
+-/
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    (h :
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+        (W2 :: rest)) :
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+      (W1 :: W2 :: rest) := by
+  rcases h.exists_pair with ⟨A, B, hin, hrev, hbudget, hneg, hlen⟩
+  exact
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
+      (SourcePressureLocalIslandWitnessAdjacentPairInList.tail hin)
+      hrev hbudget hneg hlen
+
+set_option linter.style.longLine false in
+/--
+Two-step bounded tail lift for a recovered accounted-family diagnostic.
+
+This is just a small composition helper; it still transports one existing
+pair-local diagnostic and does not scan the list.
+-/
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail_tail
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    (h :
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+        (W3 :: rest)) :
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+      (W1 :: W2 :: W3 :: rest) :=
+  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail
+    (SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail
+      h)
+
+set_option linter.style.longLine false in
+/--
+Three-step bounded tail lift for a recovered accounted-family diagnostic.
+
+This mirrors the older adjacent-diagnosis convenience API while staying
+bounded and pair-local.
+-/
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail_tail_tail
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 W4 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    (h :
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+        (W4 :: rest)) :
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+      (W1 :: W2 :: W3 :: W4 :: rest) :=
+  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail
+    (SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail_tail
+      h)
+
 /--
 Expose the actual pair-local accounted interval family object stored by the
 recovered adjacent-family carrier.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-184.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-184.md
new file mode 100644
index 00000000..d45c2ef2
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-184.md
@@ -0,0 +1,150 @@
+# report-petal-184
+
+Date: 2026-07-06
+
+## Scope
+
+Checkpoint 184 adds basic list-structure API for the bundled recovered
+accounted-family diagnostic carrier in
+`DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis`.
+
+The diagnostic remains a carrier for one recovered adjacent pair and its
+pair-local accounted family.  This checkpoint only makes that carrier easier to
+move through explicit list syntax.
+
+## Implemented theorem surface
+
+Added empty-list impossibility:
+
+```lean
+theorem
+  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.nil_false
+```
+
+This follows by unpacking the diagnostic and using the fact that the empty list
+has no adjacent pair address.
+
+Added singleton impossibility:
+
+```lean
+theorem
+  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.singleton_false
+```
+
+This similarly reduces to the existing singleton adjacent-pair impossibility.
+
+Added tail lift:
+
+```lean
+theorem
+  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail
+```
+
+This transports a diagnostic from `W2 :: rest` to `W1 :: W2 :: rest`.
+
+The lifted diagnostic is the same pair-local family:
+
+- same recovered pair `A B`;
+- same reversed-before witness `hrev`;
+- same budget `≤ -2`;
+- same strict negativity `< 0`;
+- same `items.length = 2`.
+
+Only the list address changes, via
+`SourcePressureLocalIslandWitnessAdjacentPairInList.tail`.
+
+Added bounded tail-composition helpers:
+
+```lean
+theorem
+  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail_tail
+
+theorem
+  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail_tail_tail
+```
+
+These are small convenience compositions.  No arbitrary recursive lift was
+introduced.
+
+## Guardrails preserved
+
+This checkpoint did not introduce:
+
+- global local-island coverage;
+- maximality;
+- uniqueness;
+- prefix behavior;
+- arbitrary list sorting;
+- canonical first diagnosis;
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
+1356 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
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
+The diagnostic now has the same basic syntactic mobility as the older adjacent
+diagnosis carrier.  A safe next step is to add bounded negative facts for short
+lists, such as proving that length two is the first possible carrier shape only
+when an explicit recovered adjacent pair is supplied.  That should still stay
+away from arbitrary enumeration or global accounting.
````
`````
