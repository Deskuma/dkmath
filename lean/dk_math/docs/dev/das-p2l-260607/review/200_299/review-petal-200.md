# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.PressureAutomaton

gch: c185d0aac37b808132a505a27eb929343604feab

## Report

cp199 実装完了です。

新しく [PressureAutomaton.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAutomaton.lean) を追加し、`PressureDiagnosticDecomposition` の既存証明を automaton 風 API として薄く公開しました。

追加した主な API:

```lean
def SourcePressureFailureResolution
theorem sourcePressureFailureResolution_of_sortedBeforeFailure
theorem sourcePressureFailureResolution_recovered_of_noAdjacentOverlap
```

`PressureAutomaton.lean` は指定どおり `PressureDiagnosticDecomposition` だけを import しています。公開 aggregator [PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean) にも `PressureDiagnosticDecomposition` の直後で import を追加しました。

レポートも追加済みです。

[report-petal-199.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-199.md)

検証済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureAutomaton
lake build DkMath.Collatz.PetalBridge
git diff --check
```

指定 6 ファイルの `sorry` / `admit` チェックも一致なしです。既知の unrelated warning `ZsigmondyCyclotomicResearch.lean:152` はそのままです。

## Review

## 結論

**採用** じゃ。

Checkpoint 199 は、狙い通り **Lean が認めた局所 pressure failure-resolution を、上位の automaton API として命名しただけ** になっておる。

追加された主 API は次の 3 つ。

```lean
def SourcePressureFailureResolution

theorem sourcePressureFailureResolution_of_sortedBeforeFailure

theorem sourcePressureFailureResolution_recovered_of_noAdjacentOverlap
```

新ファイルは次。

```text
DkMath/Collatz/PetalBridge/PressureAutomaton.lean
```

これは `PressureDiagnosticDecomposition` の既存証明を automaton 風に公開する薄い surface であり、report でも「new mathematical strength ではない」と明記されておる。

## 実装レビュー

かなり良い。

まず import が正しい。

```lean
import DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
```

`PressureAutomaton.lean` は `PressureDiagnosticDecomposition` だけを import しており、下位の `PressureFrontier` / `PressureAccounting` / `PressureAdjacentDiagnosis` へ逆流していない。これは cp198 の import-direction audit をきちんと受けた実装じゃ。

公開 aggregator 側も、

```lean
import DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
import DkMath.Collatz.PetalBridge.PressureAutomaton
```

の順で追加されており、層の向きが自然じゃ。

証明も薄い。
`sourcePressureFailureResolution_of_sortedBeforeFailure` は既存の

```lean
sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_or_adjacentOverlap
```

の wrapper。

`sourcePressureFailureResolution_recovered_of_noAdjacentOverlap` は既存の

```lean
sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap
```

の wrapper。

つまり、ここで新しい証明構造を作っていない。これは正しい。今回欲しかったのは新しい theorem power ではなく、**命令表として読める API 名** じゃからな。

## 数学的意味

これは **Pressure Automaton surface** じゃ。

いままでの構造は、実装上はこう見えていた。

```text
sorted-before failure
  -> pairDiagnostic-or-adjacentOverlap

sorted-before failure + no-adjacent-overlap
  -> exists pairDiagnostic
```

今回これを、上位語彙として

```text
sorted-before failure
  -> SourcePressureFailureResolution
```

と読めるようにした。

つまり、Lean が認めた局所会計機械の状態遷移を、

```text
failure
  -> resolution state
  -> recovered branch / overlap obstruction branch
```

として名前付きにしたわけじゃ。

DkMath 語彙で言えば、

```text
Core:
  PressureFrontier / PressureAccounting にある局所会計

Automaton:
  failure が recovered / obstruction に分岐する命令表

Gap:
  overlap obstruction として残る未解決 branch
```

ここまでが綺麗に分かれた。

## 既存実装との接続

現在の pressure stack は report の通り、こうなった。

```text
PressureFrontier
  <- PressureAccounting
    <- PressureLocalWitnessObstruction
      <- PressureAdjacentDiagnosis
        <- PressureDiagnosticDecomposition
          <- PressureAutomaton
```

この並びは良い。
`PressureAutomaton` は下位の定義を増やさず、既存 decomposition surface を「読むための層」として置かれている。

これで、次からは `PressureDiagnosticDecomposition` の長い theorem 名を直接読むのではなく、

```lean
SourcePressureFailureResolution
```

を主語にできる。

これは今後かなり効く。
「コラッツ予想の機械語バイナリコードを解読する」という意味では、今回の checkpoint は、命令列に mnemonic を付けた段階じゃ。

## 注意点

今回まだ言っていないことは明確じゃ。

```text
これは arbitrary-list recursive decomposition ではない。
```

```text
これは canonical first diagnosis ではない。
```

```text
これは all diagnostics enumeration ではない。
```

```text
これは recovered families の aggregation ではない。
```

```text
これは overlap repair ではない。
```

```text
これは interval union accounting ではない。
```

```text
これは coverage / maximality / uniqueness を主張しない。
```

```text
これは Collatz convergence を主張しない。
```

この境界を守れているので採用じゃ。

ただし、`PressureAccounting.lean` が 1896 行まで来ている。まだ 2000 行未満ではあるが、今後この近辺に追加実装を戻すのは避けたい。上位面を増やすなら、今回のように別ファイルを置く方が安全じゃ。

## build / no-sorry / diff check

報告では次が通っておる。

```text
lake build DkMath.Collatz.PetalBridge.PressureAutomaton
lake build DkMath.Collatz.PetalBridge
git diff --check
```

指定 6 ファイルの `sorry` / `admit` チェックも一致なし。既知の unrelated warning `ZsigmondyCyclotomicResearch.lean:152` はそのまま、target には混ざっていない。

## 次の checkpoint 方針

次は theorem を足す前に、**Beam 側の所有者を決める audit checkpoint** がよい。

今回 `PressureAutomaton` により、局所 failure resolution の命令表はできた。
次に必要なのは、

```text
この automaton state が、時間方向・深さ方向へどう伝播するか
```

をどの module が所有するかじゃ。

候補名はまだ決め打ちしない方がよい。

```text
PressureBeam
PressurePropagation
PressureAutomatonBeam
PressureTemporal
```

あたりが候補になるが、いきなり作るより、まず既存の

```text
DriftBudget
PressureDecay
PressureFrontier
PressureAccounting
PressureAutomaton
```

の責務を確認して、Beam 層の置き場所を決めるべきじゃ。

## 次の Codex 指示

```text
Checkpoint: petal-200

Main goal:
  Audit where the next Beam-facing propagation layer should live after
  `PressureAutomaton`.  Do not add new Lean theorems in this checkpoint unless
  the audit discovers a tiny missing import or documentation-only fix.

Primary target file:
  docs/dev/das-p2l-260607/review/report-petal-200.md

Allowed supporting files:
  DkMath/Collatz/PetalBridge/PressureAutomaton.lean
  DkMath/Collatz/PetalBridge/DriftBudget.lean
  DkMath/Collatz/PetalBridge/PressureDecay.lean
  DkMath/Collatz/PetalBridge/PressureFrontier.lean
  DkMath/Collatz/PetalBridge/PressureAccounting.lean

Do not modify:
  DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
  Any non-Collatz files

Context:
  Checkpoint 199 added `PressureAutomaton.lean`, an upper-level API surface
  above `PressureDiagnosticDecomposition`.

  The current stack is:

    PressureFrontier
      <- PressureAccounting
        <- PressureLocalWitnessObstruction
          <- PressureAdjacentDiagnosis
            <- PressureDiagnosticDecomposition
              <- PressureAutomaton

  `PressureAutomaton` names the already proved local failure-resolution state:

    sorted-before failure
      -> SourcePressureFailureResolution

  and the no-overlap extraction:

    sorted-before failure + no-adjacent-overlap
      -> recovered adjacent pair diagnostic

Audit questions:
  1. Which existing module currently owns local pressure drift / net-drop
     propagation?
  2. Which existing module owns interval pulse production?
  3. Which existing module owns explicit witness-list accounting?
  4. Should the next Beam-facing layer be a new upper module above
     `PressureAutomaton`, or should it be documentation-only for now?
  5. What should the new module be called if needed later:
       `PressureBeam`,
       `PressurePropagation`,
       `PressureAutomatonBeam`,
       or another name?

Expected output:
  Prefer report-only.  The report should produce a module ownership map and a
  recommendation for the next implementation checkpoint.

Guardrails:
  Do not add:
    - arbitrary-list recursive decomposition;
    - canonical first diagnosis;
    - enumeration of all diagnostics;
    - aggregation over multiple recovered diagnostics;
    - interval union accounting;
    - overlap repair;
    - coverage;
    - maximality;
    - uniqueness;
    - sorting theorem;
    - disjointness between multiple recovered families;
    - Collatz convergence.

Report requirements:
  - State that this checkpoint is audit-only unless a tiny documentation/import
    fix is made.
  - Include the current pressure import chain.
  - Explain the difference between:
      Core/local accounting,
      Automaton/failure resolution,
      Beam/propagation.
  - Recommend the owner module for future Beam-facing propagation.
  - Explicitly state that no propagation theorem, convergence theorem,
    aggregation theorem, or overlap repair theorem was added.

Verification commands:
  lake build DkMath.Collatz.PetalBridge.PressureAutomaton
  lake build DkMath.Collatz.PetalBridge

No-sorry check:
  rg -n "\bsorry\b|admit" \
    DkMath/Collatz/PetalBridge/PressureAutomaton.lean \
    DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean \
    DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean \
    DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
    DkMath/Collatz/PetalBridge/PressureAccounting.lean \
    DkMath/Collatz/PetalBridge/PressureFrontier.lean \
    DkMath/Collatz/PetalBridge/PressureDecay.lean \
    DkMath/Collatz/PetalBridge/DriftBudget.lean

Git diff hygiene:
  git diff --check
```

## わっちの総合判断

よし。これは前進じゃ。

cp198 で依存方向を守り、cp199 でその上に `PressureAutomaton` を置いた。
これで、局所会計の「命令表」ができた。

次は Beam じゃ。
ただし、Beam はいきなり theorem ではなく、まず **どの module が時間方向伝播を所有するか** を決める。ここを間違えると、せっかく整理した会計機械がまた絡まる。

コラッツの機械語解読としては、今は命令語が見え始めたところじゃ。
次は命令列の制御フロー、つまり Beam の制御構造を読む段に入る。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index cf6da7e1..8a2ca946 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -22,6 +22,7 @@ import DkMath.Collatz.PetalBridge.PressureAccounting
 import DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
 import DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
 import DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
+import DkMath.Collatz.PetalBridge.PressureAutomaton
 import DkMath.Collatz.PetalBridge.OneCycle
 import DkMath.Collatz.PetalBridge.ValuationFlowBridge
 import DkMath.Collatz.PetalBridge.Collision
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAutomaton.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAutomaton.lean
new file mode 100644
index 00000000..eded9bbe
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAutomaton.lean
@@ -0,0 +1,89 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
+
+#print "file: DkMath.Collatz.PetalBridge.PressureAutomaton"
+
+namespace DkMath.Collatz
+
+/-
+Checkpoint 199: upper-level pressure automaton surface.
+
+This file is deliberately above `PressureDiagnosticDecomposition`.  It gives a
+readable automaton-style name to the already proved local failure-resolution
+surface:
+
+```text
+sorted-before failure
+  -> recovered adjacent pair diagnostic
+     or adjacent overlap obstruction
+```
+
+No new proof strength is introduced here.  In particular, this layer does not
+enumerate diagnostics, choose a canonical first diagnosis, aggregate recovered
+families, repair overlap, prove coverage, or prove Collatz convergence.
+-/
+
+/--
+Automaton-style resolution state for an explicit local-island witness list
+whose sorted-before order has failed.
+
+The state has exactly two branches:
+
+* some adjacent pair has the named pair-local recovered diagnostic;
+* or an adjacent overlap obstruction is present.
+
+This is only a name for the already proved diagnostic decomposition surface.
+Overlap remains an obstruction branch.
+-/
+def SourcePressureFailureResolution
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
+  (∃ A B,
+    SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+        A B) ∨
+    SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
+
+/--
+Sorted-before failure enters the pressure failure-resolution automaton.
+
+This theorem is a naming wrapper around
+`sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_or_adjacentOverlap`.
+It does not add a new decomposition theorem; it only exposes the existing
+branch split as a single automaton-style state.
+-/
+theorem sourcePressureFailureResolution_of_sortedBeforeFailure
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L) :
+    SourcePressureFailureResolution L :=
+  sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_or_adjacentOverlap
+    h
+
+/--
+If the overlap branch is excluded, sorted-before failure resolves to a
+recovered adjacent pair diagnostic.
+
+This is the automaton-facing name for
+`sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap`.
+The no-overlap hypothesis is consumed here; without it, overlap remains a
+separate obstruction branch.
+-/
+theorem sourcePressureFailureResolution_recovered_of_noAdjacentOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
+    (hno : SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L) :
+    ∃ A B,
+      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+        SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+          A B :=
+  sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap
+    h hno
+
+end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-199.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-199.md
new file mode 100644
index 00000000..28636ac6
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-199.md
@@ -0,0 +1,177 @@
+# report-petal-199
+
+## Checkpoint
+
+Checkpoint 199 added a thin upper-level pressure automaton surface.
+
+The new file is:
+
+```text
+DkMath/Collatz/PetalBridge/PressureAutomaton.lean
+```
+
+This is not new mathematical strength.  It names the already proved
+failure-resolution surface from `PressureDiagnosticDecomposition` in an
+automaton-style vocabulary.
+
+## Import Chain
+
+The pressure stack now has the following upper-level shape:
+
+```text
+PressureFrontier
+  <- PressureAccounting
+    <- PressureLocalWitnessObstruction
+      <- PressureAdjacentDiagnosis
+        <- PressureDiagnosticDecomposition
+          <- PressureAutomaton
+```
+
+`PressureAutomaton.lean` imports only:
+
+```lean
+import DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
+```
+
+The public aggregator now imports it immediately after
+`PressureDiagnosticDecomposition`:
+
+```lean
+import DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
+import DkMath.Collatz.PetalBridge.PressureAutomaton
+```
+
+Lower pressure modules were not modified.
+
+## Added API
+
+The new automaton-state predicate is:
+
+```lean
+def SourcePressureFailureResolution
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
+  (∃ A B,
+    SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+        A B) ∨
+    SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
+```
+
+It has exactly two branches:
+
+1. an adjacent pair has the named recovered diagnostic;
+2. an adjacent overlap obstruction remains visible.
+
+The entry theorem is:
+
+```lean
+theorem sourcePressureFailureResolution_of_sortedBeforeFailure
+```
+
+It is a wrapper around:
+
+```lean
+sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_or_adjacentOverlap
+```
+
+The no-overlap extraction theorem is:
+
+```lean
+theorem sourcePressureFailureResolution_recovered_of_noAdjacentOverlap
+```
+
+It is a wrapper around:
+
+```lean
+sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap
+```
+
+## Boundary
+
+This module is deliberately above the diagnostic decomposition layer.  It is a
+readable command table for the local pressure machine:
+
+```text
+sorted-before failure
+  -> failure resolution
+
+failure resolution + no-adjacent-overlap
+  -> recovered adjacent pair diagnostic
+```
+
+Overlap is not repaired.  It remains an obstruction branch unless the caller
+supplies no-overlap.
+
+## Guardrails
+
+No theorem was added for:
+
+- arbitrary-list recursive decomposition,
+- canonical first diagnosis,
+- enumeration of all diagnostics,
+- aggregation over multiple recovered diagnostics,
+- interval union accounting,
+- overlap repair,
+- coverage,
+- maximality,
+- uniqueness,
+- sorting theorem,
+- disjointness between multiple recovered families,
+- Collatz convergence.
+
+## Line-Count Status
+
+```text
+    89 DkMath/Collatz/PetalBridge/PressureAutomaton.lean
+  1130 DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
+  1356 DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+  1391 DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
+  1896 DkMath/Collatz/PetalBridge/PressureAccounting.lean
+  1517 DkMath/Collatz/PetalBridge/PressureFrontier.lean
+  7379 total
+```
+
+All pressure files remain under the 2,000-line split threshold.
+
+## Verification
+
+Commands run from `lean/dk_math`:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureAutomaton
+lake build DkMath.Collatz.PetalBridge
+```
+
+Result: both builds passed.
+
+No-sorry check:
+
+```text
+rg -n "\bsorry\b|admit" \
+  DkMath/Collatz/PetalBridge/PressureAutomaton.lean \
+  DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean \
+  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean \
+  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
+  DkMath/Collatz/PetalBridge/PressureAccounting.lean \
+  DkMath/Collatz/PetalBridge/PressureFrontier.lean
+```
+
+Result: no matches.
+
+Known unrelated warning observed in local build logs:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
+
+This checkpoint did not touch that file.
+
+## Next Inference
+
+The local automaton surface is now named.  The next natural work should stay
+above this layer: either a Beam-facing bridge that consumes
+`SourcePressureFailureResolution`, or an audit checkpoint deciding which
+future module should own propagation over time.  That should not be pushed
+back into `PressureFrontier` or `PressureAccounting`.
````
`````
