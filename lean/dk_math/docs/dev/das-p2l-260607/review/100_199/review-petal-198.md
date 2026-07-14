# Git diff / Report / Review

## Add: docs: report 197

gch: 34c492bbb58b17c1c916e6dc9778337d0c8a3f69

## Report

cp197 完了です。今回は監査のみで、Lean theorem の追加は不要でした。

確認したところ、意図した二段構えは既に成立しています。

```lean
sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_or_adjacentOverlap
```

が no-overlap なしの branch split、

```lean
sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap
```

が no-overlap 付きの recovered diagnostic 抽出 consumer です。

レポートを追加しました。

[report-petal-197.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-197.md)

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

指定 pressure files の `sorry` / `admit` チェックは一致なしです。既知の `ZsigmondyCyclotomicResearch.lean:152` の unrelated `sorry` warning はそのままです。

## Review

## 結論

**採用** じゃ。

今回の checkpoint は **audit-only / docs-only** として採用する。Lean theorem の追加はなく、`report-petal-197.md` の追加のみじゃ。報告では、目的だった二段構えが既に成立していることが確認されておる。すなわち、

```lean
sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_or_adjacentOverlap
```

が no-overlap なしの branch split、

```lean
sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap
```

が no-overlap 付きの recovered diagnostic 抽出 consumer じゃ。

## 実装レビュー

今回は theorem を足さずに監査で止めた判断がよい。

前 checkpoint の目的は、

```text
branch split without no-overlap
↓
no-overlap consumer
```

という二段 API が既にあるか確認することだった。今回の report は、その通りに既存 theorem を確認し、重複 theorem を追加していない。これはかなり大事じゃ。似た wrapper を増やしすぎると、後で `PressureDiagnosticDecomposition` が「同じことを少し違う名前で言う定理」の森になってしまう。

確認された流れも自然じゃ。

```text
sorted-before failure
  -> pairDiagnostic-or-adjacentOverlap

sorted-before failure + no-adjacent-overlap
  -> exists pairDiagnostic
```

この形なら、overlap obstruction を branch split 側では見えるまま残し、no-overlap を渡した使用点で初めて recovered diagnostic へ落とせる。層の切り分けとして綺麗じゃ。

また、report は guardrails もよく守っておる。overlap repair、canonical first diagnosis、all diagnostics enumeration、aggregation、coverage、Collatz convergence などを追加していないと明記している。

## 数学的意味

これは **新しい数学的証明力を増やした checkpoint ではなく、API 境界の監査 checkpoint** じゃ。

DkMath 語彙で言えば、今回確認されたのは次の分離じゃな。

```text
Adjacent Diagnosis layer:
  recovered pair-local diagnostic を named predicate として取り出す

Overlap Obstruction layer:
  adjacent overlap obstruction を別 branch として残す

No-overlap consumer layer:
  no-overlap 仮定を与えた後に recovered branch だけへ落とす
```

つまり、今回の成果は **branch split 前後の層混入がないことの確認** じゃ。

これは Core / Beam / Gap で言えば、局所診断 Core の出口を整えた段階であって、Beam 的な伝播や list-wide aggregation へはまだ進んでいない。

## 注意点

今回言えたことは、次じゃ。

```text
任意リストの sorted-before failure に対して、
overlap を隠さない branch split と、
no-overlap 仮定後の recovered diagnostic extraction が、
既存 API として揃っている。
```

まだ言っていないことは、次じゃ。

```text
これは arbitrary-list existential projection であり、
canonical first diagnosis ではない。
```

```text
これは pair-local diagnostic の抽出であり、
list-wide aggregation ではない。
```

```text
これは overlap を repair していない。
```

```text
これは recovered families 間の disjointness を言っていない。
```

```text
これは Collatz convergence を主張しない。
```

そして、今回 theorem 追加なしだったため、Lean 側の主張面積は増えていない。これは安全じゃ。監査で済むところを無理に theorem 化しなかったのは、よい判断じゃよ。

## build / no-sorry / diff check

report によると、以下は通っておる。

```text
lake build DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
```

指定 pressure files の `sorry` / `admit` チェックも一致なし。`git diff --check` も通過。既知の `ZsigmondyCyclotomicResearch.lean:152` の `sorry` warning は unrelated として扱われている。

ファイルサイズも `PressureDiagnosticDecomposition.lean` が 1130 行で、report 上の 2000 行 refactor threshold にはまだ達していない。ここも妥当じゃ。

## 次の checkpoint 方針

次は **consumer-map を一段だけ下流へ進める** のがよい。

ただし、新 theorem を足す前に、まず `PressureFrontier` / `PressureAccounting` 側で、この二段 API を使う自然な地点が既にあるかを監査するのがよい。見つかった場合だけ、薄い wrapper を 1 本追加する。

狙いは、

```text
sorted-before failure
  -> pairDiagnostic-or-adjacentOverlap
  -> no-overlap consumer
  -> downstream frontier/accounting theorem
```

の導線を確認することじゃ。

ここでまだ足してはいけないものは、arbitrary-list aggregation、union accounting、overlap repair、disjointness、canonical first diagnosis じゃ。ぬしよ、ここで欲を出すと森で迷うぞい。

## 次の Codex 指示

```text
Checkpoint: petal-198

Main goal:
  Audit downstream usage points for the already-confirmed two-stage arbitrary-list
  diagnostic API.  Do not add broad new theory.  Add at most one thin downstream
  wrapper only if there is a clear existing consumer gap.

Primary target file:
  DkMath/Collatz/PetalBridge/PressureFrontier.lean

Allowed supporting files:
  DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
  DkMath/Collatz/PetalBridge/PressureAccounting.lean
  docs/dev/das-p2l-260607/review/report-petal-198.md

Do not modify:
  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
  DkMath/Collatz/PetalBridge.lean
  Any non-Collatz files

Context:
  Checkpoint 196 added:
    `sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_or_adjacentOverlap`

  Checkpoint 197 was audit-only and confirmed that the intended two-stage API
  already exists:
    1. branch split without no-overlap;
    2. recovered diagnostic extraction with no-overlap.

  The confirmed no-overlap consumer is:
    `sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap`

Main audit question:
  Is there an existing downstream theorem in `PressureFrontier.lean` or
  `PressureAccounting.lean` that should consume the no-overlap pair diagnostic
  API directly, instead of using lower-level carrier vocabulary?

Candidate theorem shape, only if a clear missing wrapper is found:
  theorem
      <frontier_or_accounting_name>_of_sortedBeforeFailure_of_noAdjacentOverlap
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      (h :
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
      (hno :
        SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L) :
      ∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic A B

  Prefer reusing the existing theorem directly:
    `sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap`

Suggested proof strategy if a wrapper is genuinely needed:
  - Apply
      `sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap h hno`.
  - Do not unfold arbitrary list recursion.
  - Do not reconstruct pair diagnostics manually.
  - Do not introduce new diagnostic predicates.

Guardrails:
  Do not add:
    - length-six decomposition;
    - arbitrary-list recursive decomposition;
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
  docs/dev/das-p2l-260607/review/report-petal-198.md

Report requirements:
  - State whether this was audit-only or whether one thin wrapper was added.
  - List the exact downstream theorem names inspected.
  - Confirm whether `PressureFrontier` / `PressureAccounting` already have
    suitable consumers.
  - Explicitly state that no aggregation, overlap repair, canonical diagnosis,
    coverage, or Collatz convergence was added.
  - Include line-count status for the touched files.

Verification commands:
  lake build DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
  lake build DkMath.Collatz.PetalBridge.PressureAccounting
  lake build DkMath.Collatz.PetalBridge.PressureFrontier
  lake build DkMath.Collatz.PetalBridge

No-sorry check:
  rg -n "\bsorry\b|admit" \
    DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean \
    DkMath/Collatz/PetalBridge/PressureAccounting.lean \
    DkMath/Collatz/PetalBridge/PressureFrontier.lean

Git diff hygiene:
  git diff --check
```

## Diff

`````md
````diff
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-197.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-197.md
new file mode 100644
index 00000000..b65ebcc6
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-197.md
@@ -0,0 +1,131 @@
+# report-petal-197
+
+## Checkpoint
+
+Checkpoint 197 was an audit-only checkpoint.
+
+No Lean theorem was added.  The requested no-overlap consumer already exists,
+and the arbitrary-list diagnostic API has the intended two-stage shape.
+
+## Theorems inspected
+
+The branch split without no-overlap is:
+
+```lean
+sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_or_adjacentOverlap
+```
+
+It states that sorted-before failure gives either:
+
+1. some adjacent pair carrying
+   `SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic`,
+2. or an adjacent overlap obstruction.
+
+The no-overlap consumer is:
+
+```lean
+sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap
+```
+
+It states that sorted-before failure plus
+`SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L`
+extracts an existential adjacent pair with the named pair-local recovered
+diagnostic.
+
+The consumer is currently implemented through the existing carrier theorem:
+
+```lean
+sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
+```
+
+and then projects:
+
+```lean
+.exists_pairDiagnostic
+```
+
+## API shape confirmed
+
+The downstream shape is now:
+
+```text
+sorted-before failure
+  -> pairDiagnostic-or-adjacentOverlap
+
+sorted-before failure + no-adjacent-overlap
+  -> exists pairDiagnostic
+```
+
+This is the desired separation:
+
+1. The branch split does not hide overlap and does not require no-overlap.
+2. The recovered diagnostic extraction is only claimed once no-overlap is
+   supplied.
+
+## Guardrails
+
+No overlap repair was added.
+
+No theorem was added for:
+
+- length-six decomposition,
+- arbitrary-list recursive decomposition,
+- canonical first diagnosis,
+- enumeration of all diagnostics,
+- aggregation over multiple recovered diagnostics,
+- list-wide interval union accounting,
+- coverage,
+- maximality,
+- uniqueness,
+- sorting,
+- disjointness between multiple recovered families,
+- Collatz convergence.
+
+The present API remains local to explicit adjacent-pair witnesses.
+
+## File-size status
+
+The primary file remains below the 2,000-line refactoring threshold:
+
+```text
+  1130 DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
+```
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
+Result: all builds passed.
+
+No-sorry check over the requested files:
+
+```text
+rg -n "\bsorry\b|admit" \
+  DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean \
+  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean \
+  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
+  DkMath/Collatz/PetalBridge/PressureAccounting.lean \
+  DkMath/Collatz/PetalBridge/PressureFrontier.lean
+```
+
+Result: no matches.
+
+`git diff --check` passed.
+
+Known unrelated warning:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
+
+This checkpoint did not touch that file.
````
`````
