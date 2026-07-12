# Git diff / Report / Review

## Upd: docs: report 232

gch: 48a04256b0bdf0f214423fe3d39e6fcf6b6b066e

## Report

cp232 は no-code で閉じました。

判断は Branch B です。`SourcePressureFailureResolution` 自体がすでに recovered / overlap の branch-kind classifier なので、Beam 側へ大きな分岐 theorem を増やす必要は今のところありません。右 endpoint / 両 endpoint wrapper も、具体 caller がないため追加していません。

作成したもの:

`lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-232.md`

内容は Pulse diagnostic API の棚卸しです。

- explicit `W ∈ L`
- seed
- failureResolution
- recovered adjacent pair left/right
- overlap pair-preserving
- overlap anonymous

`git diff --check` は通っています。Lean コード変更はありません。

## Review

## 結論

**採用** じゃ。
cp232 は no-code checkpoint として正しい判断。

今回取った Branch は **Branch B**。

```text id="lq5wme"
current API is sufficient
```

つまり、いまは Beam 側に巨大な branch-kind-preserving theorem を増やさず、

```text id="gue93k"
SourcePressureFailureResolution:
  recovered / overlap の分岐判定

PressureBeam.Pulse:
  分岐選択後、または匿名でよい場合の local diagnostic 抽出
```

という役割分担で止めた。これは良い。

## レビュー

今回の判断はかなり戦略的じゃ。

`SourcePressureFailureResolution L` は、すでに構造として

```lean id="piz3mw"
(∃ A B,
  SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
    SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic A B) ∨
  SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
```

という branch-kind classifier になっている。
ここへさらに Beam 側で大きな分岐 theorem を重ねると、

```text id="7m5s34"
既存 classifier の再包装
```

になりやすい。

今は caller がいない。
なら、no-code で API map を整理するのが正解じゃ。

## API 棚卸しの価値

今回の report は、今後の戦略表として使える。

現状の Beam Pulse diagnostic surface はこう。

```text id="z01p58"
explicit W ∈ L:
  sourcePressureBeamPulse_witness_singleton_full_diagnostic

seed:
  exists_sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_seed

failureResolution:
  exists_sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_failureResolution

recovered adjacent pair:
  sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_left
  sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_right

overlap pair-preserving:
  exists_sourcePressureBeamPulse_leftWitness_full_diagnostic_of_adjacentOverlapObstruction

overlap anonymous:
  exists_sourcePressureBeamPulse_witness_full_diagnostic_of_adjacentOverlapObstruction
```

これで caller は粒度を選べる。

```text id="k728uo"
分岐 identity が必要:
  recovered adjacent pair / overlap pair-preserving を使う

匿名 witness で十分:
  seed / failureResolution / overlap anonymous を使う
```

ここまで整理できていれば、今すぐ theorem を増やさなくてよい。

## True Beam / Boundary / False Beam / Gap

## True Beam

今回の True Beam は、既存 API が coherent だと確認できたことじゃ。

```text id="l5ua4j"
explicit witness
seed
failureResolution
recovered pair
overlap pair-preserving
overlap anonymous
```

の surface がそろっている。

## Boundary

分岐判定の責務は `SourcePressureFailureResolution` に置く。
Pulse は local diagnostic extraction に留める。

```text id="w1soz3"
Automaton / failureResolution:
  branch を選ぶ

Pulse:
  選ばれた branch から local diagnostic を出す
```

この境界が良い。

## False Beam

否定 theorem は不要。
今回は「追加しない」が正しい checkpoint じゃ。

## Gap

残る Gap は caller-driven。

```text id="fkk0ap"
branch-kind-preserving Beam classifier
right-endpoint overlap diagnostic
both-endpoint overlap diagnostic
```

どれも可能だが、必要な caller が出るまでは追加しない。
この判断はよい。

## 注意点

`SourcePressureBeamSeed L` と `SourcePressureFailureResolution L` の重複は report にもある通り、軽い重複として存在する。

ただし、これは今は消さないほうがよい。
Beam-facing name と automaton/failure-resolution name は、使う層が違う。

```text id="ilp5zk"
SourcePressureFailureResolution:
  下層の分岐状態

SourcePressureBeamSeed:
  Beam 側から読む入口
```

この読み替えがレビュー上の可読性を上げているので、現時点では許容。

## 次の checkpoint 方針

次は Pulse に wrapper を足すのではなく、**上位 caller がどこで必要になるか**を見る段階じゃ。

候補としては、`PressureAutomaton` またはその上の Beam-facing classifier が、現在の diagnostic surfaces を実際に使うかどうか。

ただし、次も分岐 Goal で構える。

## 次の Codex 指示

```text id="rkkhlb"
Checkpoint: petal-233

Primary Goal:
  Move upward from the completed Pulse diagnostic API and investigate whether a
  concrete higher-level caller now needs these diagnostics.

Context:
  cp232 closed with no Lean code.  The current Pulse diagnostic surfaces are
  considered sufficient until a concrete caller appears.

  Current public diagnostic surfaces include:
    - explicit W ∈ L -> full singleton diagnostic
    - SourcePressureBeamSeed L -> ∃ W ∈ L, full singleton diagnostic
    - SourcePressureFailureResolution L -> ∃ W ∈ L, full singleton diagnostic
    - AdjacentPairInList L A B -> full diagnostic for A / B
    - overlap obstruction -> pair-preserving diagnostic for left endpoint
    - overlap obstruction -> anonymous ∃ W diagnostic

Strategic Branch Goals:

  Branch A: a higher-level theorem already has SourcePressureFailureResolution
    Inspect likely callers above or around `PressureAutomaton`.

    If a theorem has:
      SourcePressureFailureResolution L

    and only needs an anonymous diagnostic, use:
      exists_sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_failureResolution

    Add at most one caller theorem if it clearly removes proof noise.

  Branch B: a higher-level theorem needs branch-kind preservation
    If a caller must distinguish recovered vs overlap, do not use the anonymous
    theorem too early.

    Instead report whether the caller needs:
      recovered adjacent pair left/right diagnostic
      overlap pair-preserving diagnostic

    Add a branch-kind-preserving theorem only if the caller genuinely needs it
    and the statement remains small.

  Branch C: a caller needs overlap right or both endpoints
    If actual caller evidence appears for:
      right endpoint overlap diagnostic
      both-endpoint overlap diagnostic

    add the smallest wrapper needed.
    Do not add for symmetry alone.

  Branch D: current API is sufficient and no caller exists
    Add no Lean code.

    Report:
      - what modules were inspected;
      - which diagnostic surfaces would be used if needed;
      - why no theorem should be added now.

  Branch E: missing relation blocks use
    If a caller cannot use the Pulse API because it lacks:
      SourcePressureFailureResolution L
      SourcePressureBeamSeed L
      AdjacentPairInList L A B
      overlap obstruction
      explicit W ∈ L

    report the exact missing relation as the next Gap.

Files to inspect:
  DkMath/Collatz/PetalBridge/PressureAutomaton.lean
  DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
  DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
  DkMath/Collatz/PetalBridge/PressureBeam/Core.lean

Implementation rules:
  Use #check, #print, and scratch lemmas.
  Inspect actual caller shapes before adding any theorem.
  Add no more than one theorem.
  Prefer no-code report if current API is sufficient.
  Do not expand Pulse API for symmetry or aesthetic completeness.

Guardrails:
  Do not add:
    - list-wide coverage;
    - witness-family aggregation;
    - arbitrary witness selection;
    - canonical target selection;
    - arbitrary target transport;
    - overlap repair;
    - disjointness;
    - propagation;
    - Collatz convergence.

Dependency guardrail:
  Lower modules must not import Beam.
  Any Beam-facing theorem belongs in PressureBeam/Pulse.lean or a higher
  Beam-facing module.

Report requirements:
  - State which Branch was taken.
  - State which branches were inspected but not taken.
  - If no code was added, explain why the current Pulse API is sufficient.
  - If code was added, identify the concrete caller that justified it.
  - If blocked, identify the exact missing relation.
  - Classify results as True Beam / Boundary / False Beam / Gap.
  - Predict the next branch to attack.
  - Confirm no dependency inversion.
  - Confirm no coverage, aggregation, overlap repair, disjointness, or
    canonical selection.

Verification if code changes:
  lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
  lake build DkMath.Collatz.PetalBridge.PressureBeam
  lake build DkMath.Collatz.PetalBridge
  no-sorry grep over inspected pressure files
  git diff --check

If no Lean code changes:
  git diff --check
  report only
```

## 待ち構え

次の戻りは、おそらくこうじゃ。

```text id="zazr34"
Branch D:
  no caller exists, no-code
```

この場合は Pulse diagnostic API を一旦閉じて、次の戦線へ移る。

```text id="y7h2ja"
Branch A:
  actual theoremが failureResolution -> anonymous diagnostic を欲しがる
```

この場合は 1 本だけ caller theorem を追加。

```text id="c2xwox"
Branch B:
  branch-kind preservation が必要
```

この場合は、recovered / overlap を分ける theorem を慎重に設計。

```text id="xb86hq"
Branch E:
  higher caller がそもそも failureResolution を持っていない
```

この場合は、その missing relation が次の攻略対象。

## 総合判断

cp232 は成功。
no-code で止まれたことが良い。

ここで wrapper を増やしていたら API が太った。
今回は「今は足りている」と判断し、API map を固定した。

これは戦略として強い。

## Diff

`````md
````diff
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-232.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-232.md
new file mode 100644
index 00000000..98f2570e
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-232.md
@@ -0,0 +1,255 @@
+# report-petal-232
+
+## Checkpoint
+
+`petal-232`
+
+## Goal
+
+Audit the current Beam Pulse diagnostic surfaces and decide whether to add a
+higher-level failure-resolution classifier theorem.
+
+## Branch Taken
+
+Branch B was taken: the current API is sufficient.
+
+No Lean theorem was added in this checkpoint.
+
+## Reason
+
+`SourcePressureFailureResolution L` is already the branch-kind classifier:
+
+```lean
+def SourcePressureFailureResolution
+    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
+  (∃ A B,
+    SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+        A B) ∨
+    SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
+```
+
+The Beam Pulse layer already has:
+
+```lean
+SourcePressureFailureResolution L
+  -> ∃ W, W ∈ L ∧ full singleton diagnostic for W
+```
+
+Adding a new branch-kind-preserving Beam theorem is possible, but the statement
+would be large and no concrete caller currently needs it.  The better public
+surface for now is:
+
+```text
+use SourcePressureFailureResolution for branch-kind inspection;
+use Pulse theorems only after choosing a branch or when an anonymous diagnostic
+is enough.
+```
+
+## Current Diagnostic API Map
+
+Explicit witness:
+
+```lean
+sourcePressureBeamPulse_witness_singleton_full_diagnostic
+```
+
+Use when the caller already has:
+
+```text
+W ∈ L
+```
+
+Beam seed:
+
+```lean
+exists_sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_seed
+```
+
+Use when the caller has:
+
+```text
+SourcePressureBeamSeed L
+```
+
+Failure resolution:
+
+```lean
+exists_sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_failureResolution
+```
+
+Use when the caller has:
+
+```text
+SourcePressureFailureResolution L
+```
+
+and does not care which branch produced the witness.
+
+Recovered adjacent pair:
+
+```lean
+sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_left
+sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_right
+```
+
+Use when the caller already has an addressed adjacent pair:
+
+```text
+SourcePressureLocalIslandWitnessAdjacentPairInList L A B
+```
+
+Overlap, pair-preserving:
+
+```lean
+exists_sourcePressureBeamPulse_leftWitness_full_diagnostic_of_adjacentOverlapObstruction
+```
+
+Use when the caller needs to keep:
+
+```text
+A, B,
+AdjacentPairInList L A B,
+PairOverlapObstruction A B
+```
+
+and attach the full singleton diagnostic to the left endpoint `A`.
+
+Overlap, anonymous:
+
+```lean
+exists_sourcePressureBeamPulse_witness_full_diagnostic_of_adjacentOverlapObstruction
+```
+
+Use when the caller only needs:
+
+```text
+∃ W, W ∈ L ∧ full singleton diagnostic for W
+```
+
+from an adjacent-overlap obstruction.
+
+## Branches Inspected But Not Taken
+
+Branch A:
+
+- Not taken.
+- A branch-kind-preserving Beam classifier can be constructed by splitting
+  `SourcePressureFailureResolution`.
+- It would duplicate the existing classifier plus current Pulse surfaces, and
+  no caller currently needs the larger theorem.
+
+Branch C:
+
+- Not taken.
+- No concrete caller needs the right endpoint of an overlap pair.
+
+Branch D:
+
+- Not taken.
+- No concrete caller needs both endpoints of an overlap pair.
+
+Branch E:
+
+- Mild duplication exists:
+
+```text
+SourcePressureBeamSeed L
+```
+
+is currently a Beam-facing name for:
+
+```text
+SourcePressureFailureResolution L
+```
+
+The duplicated seed/failure-resolution Pulse theorems are intentional for API
+readability and should not be removed yet.
+
+## Classification
+
+True Beam:
+
+- No new theorem added.
+- The existing Pulse API is coherent and covers the currently visible caller
+  shapes.
+
+Boundary:
+
+- Branch-kind inspection should happen at `SourcePressureFailureResolution`.
+- Pulse should stay as the local diagnostic extraction layer.
+
+False Beam:
+
+- None added.
+
+Gap:
+
+- A branch-kind-preserving Beam classifier remains possible if a caller needs
+  it.
+- Right-endpoint and both-endpoint overlap wrappers remain possible but should
+  remain caller-driven.
+
+## Dependency Direction
+
+No dependency inversion was introduced.
+
+No Lean code changed in this checkpoint.  Lower diagnostic modules still do not
+import Beam.
+
+## Guardrails
+
+No theorem claims:
+
+- list-wide coverage;
+- witness-family aggregation;
+- arbitrary witness selection;
+- canonical target selection;
+- arbitrary target transport;
+- overlap repair;
+- disjointness;
+- propagation;
+- Collatz convergence.
+
+## Verification
+
+No Lean code changed for cp232.
+
+Workspace hygiene check:
+
+```text
+git diff --check
+```
+
+completed successfully.
+
+The prior cp231 build gate already verified the current Pulse surface:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
+lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
+lake build DkMath.Collatz.PetalBridge.PressureBeam
+lake build DkMath.Collatz.PetalBridge
+```
+
+## Next Branch To Attack
+
+Move upward only when a concrete caller appears.
+
+Natural next candidates:
+
+```text
+1. branch-kind-preserving Beam classifier
+2. right-endpoint overlap diagnostic
+3. both-endpoint overlap diagnostic
+```
+
+Until then, keep the current split:
+
+```text
+Automaton layer:
+  choose recovered vs overlap
+
+Pulse layer:
+  extract local singleton Beam diagnostics
+```
````
`````
