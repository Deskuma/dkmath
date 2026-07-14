# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition

gch: bc137db1eaaa944c671c73876d3bd166734036f5

## Report

実装完了です。

[PressureDiagnosticDecomposition.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean) に、任意リスト向けの branch split を追加しました。

```lean
sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_or_adjacentOverlap
```

これは no-overlap 仮定を使わず、失敗から

- named pair diagnostic が存在する
- adjacent overlap obstruction がある

のどちらかへ分岐させる補題です。既存の recovered-or-overlap theorem を named diagnostic vocabulary に持ち上げただけなので、coverage / canonical diagnosis / aggregation / overlap repair などは主張していません。

レポートも追加しました。

[report-petal-196.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-196.md)

検証済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
git diff --check
```

対象 pressure files の `sorry` / `admit` チェックも一致なしです。既知の unrelated warning `ZsigmondyCyclotomicResearch.lean:152` はそのままです。

## Review

## 結論

**採用** じゃ。

今回の主追加は次の 1 本。

```lean
sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_or_adjacentOverlap
```

対象ファイルは次じゃ。

```text
DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
```

これは、任意リストの sorted-before failure から、

```lean
(∃ A B,
  SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
    SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic A B)
∨
  SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
```

へ分岐する theorem じゃな。添付 report でも、既存の `sourcePressureLocalIslandWitnessList_failure_exists_recovered_or_overlap` を named diagnostic vocabulary に持ち上げたものだと説明されておる。

## 実装レビュー

よい点は、**no-overlap 仮定を混ぜずに branch split を出している** ことじゃ。

証明も薄くて正しい。既存 theorem を `rcases` し、recovered branch では

```lean
SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic.of_before hrev
```

で named pair-local predicate へ詰め直しておる。`_hbudget` を捨てている点もよい。ここで budget 情報を強化したり、accounting aggregation へ踏み込んだりしていない。

これはまさに、

```text
carrier に既にある recovered witness を
downstream 用の named diagnostic predicate へ射影する
```

という wrapper theorem じゃ。

依存関係も自然じゃ。`PressureDiagnosticDecomposition.lean` に置くのが妥当で、`PressureAccounting` や `PressureFrontier` 側へ無理に依存を増やしていない。

報告上、次は通っておる。

```text
lake build DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
git diff --check
```

対象 pressure files の `sorry` / `admit` も一致なし、既知の `ZsigmondyCyclotomicResearch.lean:152` warning は unrelated として切り分けられておる。

## 数学的意味

これは **arbitrary-list branch split layer** じゃ。

より正確には、

```text
sorted-before failure
  → named recovered pair-local diagnostic
    or adjacent overlap obstruction
```

という分解を、任意リスト向けに出した checkpoint じゃな。

DkMath 語彙で言えば、これは **Adjacent Diagnosis layer** と **Overlap Obstruction layer** の境界にある theorem じゃ。

recovered branch は、

```text
ある adjacent pair が
pair-local recovered accounted family diagnostic を持つ
```

というだけ。

overlap branch は、

```text
隣接 overlap obstruction がある
```

というだけ。

ゆえに、この theorem は **overlap を repair していない** 。また、no-overlap 仮定を使って recovered branch だけに潰してもいない。ここが良い。

## 注意点

この checkpoint で言えたことは、次じゃ。

```text
任意リストの sorted-before failure から、
少なくとも一つの named recovered pair-local diagnostic があるか、
隣接 overlap obstruction がある。
```

まだ言っていないことは、次じゃ。

```text
これは fixed explicit list に限る話ではなく arbitrary list だが、
得られるのは existential projection だけである。
```

```text
これは pair-local であり、list-wide aggregation ではない。
```

```text
これは overlap を repair していない。
```

```text
これは all diagnostics enumeration ではない。
```

```text
これは canonical first diagnosis ではない。
```

```text
これは recovered families 間の disjointness を主張しない。
```

```text
これは Collatz convergence を主張しない。
```

命名については、`pairDiagnostic` という短縮が少し広く見えるが、statement 側で `SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic` まで明示されているので許容範囲じゃ。

## 次の checkpoint 方針

次は、新 theorem を増やすより **audit-only / consumer-map checkpoint** がよい。

理由は、report 自身が述べている通り、no-overlap を使用点で合成する theorem は既に

```lean
sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap
```

として存在する形になっているからじゃ。

したがって次の最小手は、

```text
branch split without no-overlap
↓
no-overlap consumer
↓
downstream usage point
```

の導線が重複なく通っているかを確認すること。

ここで慌てて arbitrary-list recursion、canonical first pair、all diagnostics enumeration へ進むのは、たわけた欲張りじゃ。今は API の二段構えが崩れていないかを見る段階じゃな。

## 次の Codex 指示

```text
Checkpoint: petal-197

Main goal:
  Audit the downstream shape of the arbitrary-list diagnostic API after
  `sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_or_adjacentOverlap`.
  Do not add a new theorem unless an actually missing wrapper is found.
  The goal is to confirm that the API has the intended two-stage shape:
    1. branch split without no-overlap;
    2. recovered diagnostic extraction only under no-overlap.

Primary target file:
  DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean

Allowed supporting files:
  docs/dev/das-p2l-260607/review/report-petal-197.md

Do not modify:
  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
  DkMath/Collatz/PetalBridge/PressureAccounting.lean
  DkMath/Collatz/PetalBridge/PressureFrontier.lean
  DkMath/Collatz/PetalBridge.lean
  Any non-Collatz files

Context:
  Checkpoint 196 added:
    `sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_or_adjacentOverlap`

  This theorem is the arbitrary-list branch split:
    sorted-before failure implies either
      some adjacent pair has the named pair-local recovered diagnostic,
    or
      an adjacent overlap obstruction exists.

  It deliberately does not assume no-overlap and does not repair overlap.

Candidate theorem / existing theorem to audit:
  Confirm that the following theorem exists and is the intended no-overlap consumer:

  theorem
      sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      (h :
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
      (hno :
        SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L) :
      ∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
            A B

  Do not implement this theorem again if it already exists.

Suggested proof strategy if the wrapper is missing:
  - Start from
      `sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_or_adjacentOverlap h`.
  - In the recovered branch, return the existential directly.
  - In the overlap branch, contradict `hno`.
  - Use existing no-overlap / overlap contradiction lemmas only.
  - Do not unfold list recursion manually.

Guardrails:
  Do not add:
    - length-six decomposition;
    - arbitrary-list decomposition beyond existential projection;
    - arbitrary-list recursion;
    - canonical first diagnosis for arbitrary lists;
    - enumeration of all diagnostics;
    - aggregation over multiple recovered diagnostics;
    - list-wide interval union accounting;
    - coverage;
    - maximality;
    - uniqueness for arbitrary lists;
    - sorting theorems;
    - overlap repair;
    - disjointness between multiple recovered families;
    - Collatz convergence.

Report path:
  docs/dev/das-p2l-260607/review/report-petal-197.md

Report requirements:
  - State whether this was audit-only or whether one missing wrapper was added.
  - List the exact theorem names inspected.
  - Confirm that the two-stage API is:
      branch split without no-overlap,
      then no-overlap consumer.
  - Explicitly state that no overlap repair, aggregation, canonical diagnosis,
    or Collatz convergence was added.

Verification commands:
  lake build DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
  lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
  lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
  lake build DkMath.Collatz.PetalBridge.PressureAccounting
  lake build DkMath.Collatz.PetalBridge.PressureFrontier
  lake build DkMath.Collatz.PetalBridge

No-sorry check:
  rg -n "\bsorry\b|admit" \
    DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean \
    DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean \
    DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
    DkMath/Collatz/PetalBridge/PressureAccounting.lean \
    DkMath/Collatz/PetalBridge/PressureFrontier.lean

Git diff hygiene:
  git diff --check
```

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
index c35d44f6..1e409a10 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
@@ -789,6 +789,39 @@ theorem
   (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
     h hno).exists_reversed_of_two
 
+set_option linter.style.longLine false in
+/--
+Branch split for sorted-before failure using the named pair-local recovered
+diagnostic predicate.
+
+This is the named-surface version of
+`sourcePressureLocalIslandWitnessList_failure_exists_recovered_or_overlap`.
+No no-overlap assumption is used here: the overlap obstruction remains the
+right-hand branch.  The recovered branch only repackages one adjacent recovered
+pair into `SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic`;
+it does not enumerate diagnostics, choose a canonical pair, aggregate families,
+repair overlap, or prove coverage.
+-/
+theorem
+    sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_or_adjacentOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L) :
+    (∃ A B,
+      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+        SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+          A B) ∨
+      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L := by
+  rcases sourcePressureLocalIslandWitnessList_failure_exists_recovered_or_overlap h
+      with hrec | hoverlap
+  · rcases hrec with ⟨A, B, hin, hrev, _hbudget⟩
+    exact Or.inl
+      ⟨A, B, hin,
+        SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic.of_before
+          hrev⟩
+  · exact Or.inr hoverlap
+
 set_option linter.style.longLine false in
 /--
 Failure plus named no-adjacent-overlap yields some named pair-local recovered
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-196.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-196.md
new file mode 100644
index 00000000..7d4ba9e9
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-196.md
@@ -0,0 +1,131 @@
+# report-petal-196
+
+## Checkpoint
+
+Checkpoint 196 closes the arbitrary-list branch split requested by the
+reviewer.
+
+The implemented theorem is:
+
+```lean
+theorem
+    sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_or_adjacentOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L) :
+    (∃ A B,
+      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+        SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+          A B) ∨
+      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
+```
+
+## Implementation
+
+The theorem was added to:
+
+```text
+DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
+```
+
+It is a named-surface wrapper over the existing arbitrary-list theorem:
+
+```lean
+sourcePressureLocalIslandWitnessList_failure_exists_recovered_or_overlap
+```
+
+The recovered branch is repackaged into the named pair-local predicate
+`SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic`
+using:
+
+```lean
+SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic.of_before
+```
+
+The existing recovered budget witness is intentionally not strengthened.  The
+new theorem only exposes the already available branch split in the diagnostic
+vocabulary used downstream.
+
+## Guardrails
+
+This theorem does not assume no-overlap.  The overlap obstruction is preserved
+as the right-hand branch.
+
+It does not claim:
+
+- global coverage,
+- canonical diagnosis,
+- enumeration of all failing adjacent pairs,
+- aggregation of recovered families,
+- overlap repair,
+- disjointness between recovered families,
+- Collatz convergence.
+
+The theorem remains an arbitrary-list existential projection: under sorted-
+before failure, either some adjacent pair has the named recovered diagnostic,
+or an adjacent overlap obstruction is present.
+
+## Verification
+
+Commands run from `lean/dk_math`:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
+lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
+lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
+lake build DkMath.Collatz.PetalBridge.PressureAccounting
+lake build DkMath.Collatz.PetalBridge.PressureFrontier
+lake build DkMath.Collatz.PetalBridge
+```
+
+All builds passed.
+
+No-sorry check over the requested pressure files:
+
+```text
+rg -n "\bsorry\b|admit" \
+  DkMath/Collatz/PetalBridge/PressureAccounting.lean \
+  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
+  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean \
+  DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
+```
+
+Result: no matches.
+
+The known unrelated warning remains:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
+
+This was not touched.
+
+Line counts after the checkpoint:
+
+```text
+  1130 DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
+  1356 DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+  1391 DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
+  1896 DkMath/Collatz/PetalBridge/PressureAccounting.lean
+  1517 DkMath/Collatz/PetalBridge/PressureFrontier.lean
+  7290 total
+```
+
+## Next inference
+
+The next natural consumer is a small downstream theorem that combines this
+branch split with a no-overlap assumption only at the usage point.  That is
+already essentially present as the existing no-overlap consumer:
+
+```lean
+sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap
+```
+
+So the current API now has the intended two-stage shape:
+
+1. branch split without no-overlap,
+2. recovered diagnostic extraction with no-overlap.
+
+This keeps the overlap obstruction visible instead of silently discarding it.
````
`````
