# Git diff / Report / Review

## Add; docs: review petal 200

gch: 02daadea9bb91ee500a11362f0c650b5d7a60849

## Report

cp200 完了です。

今回は監査のみで、Lean 定理は追加していません。新規 report として [report-petal-200.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-200.md) を作成し、次の Beam-facing 層は `PressureAutomaton` の上に新規 `DkMath.Collatz.PetalBridge.PressureBeam` として置くのが自然、という判断を記録しました。

検証結果:

- `lake build DkMath.Collatz.PetalBridge.PressureAutomaton` passed
- `lake build DkMath.Collatz.PetalBridge` passed
- pressure 系対象ファイルの no-sorry check は一致なし
- `git diff --check` passed

既知の `ZsigmondyCyclotomicResearch.lean` の既存 `sorry` warning は今回も replay されましたが、今回の作業範囲外です。

## Review

## 結論

**閉じている。だが、閉じたのは「局所 Core + Automaton」までじゃ。**

つまり、今閉じているのはこれ。

```text id="oowdar"
局所 pressure 会計
  -> interval pulse / witness accounting
  -> sorted-before failure
  -> failure resolution automaton
  -> recovered diagnostic or overlap obstruction
```

これは Lean が認めた局所機械として、かなり綺麗に閉じておる。

ただし、まだ閉じていないのはこれ。

```text id="i214io"
その局所 automaton state が、
時間方向・軌道方向・Beam 方向へどう伝播するか
```

つまり **Collatz 大域収束はまだ閉じていない**。
しかし、そこへ向かうための **局所会計オートマトンの Core は閉じた** と見てよい。

## cp200 の判定

**採用** じゃ。

今回の `review-petal-201.md` は、cp200 の audit-only checkpoint。Lean theorem は追加せず、次の Beam-facing 層の置き場所を決める監査に徹している。報告では、新しい Beam-facing 層は `PressureAutomaton` の上に `DkMath.Collatz.PetalBridge.PressureBeam` として置くのが自然、と結論しておる。

これは正しい判断じゃ。

現在の effective stack はこう整理されている。

```text id="xsy4e7"
DriftBudget
  <- PressureDecay
    <- PressureFrontier
      <- PressureAccounting
        <- PressureLocalWitnessObstruction
          <- PressureAdjacentDiagnosis
            <- PressureDiagnosticDecomposition
              <- PressureAutomaton
```

ここまでで、

```text id="h5loff"
Core/local accounting:
  PressureDecay / PressureFrontier / PressureAccounting

Automaton/failure resolution:
  PressureDiagnosticDecomposition / PressureAutomaton

Beam/propagation:
  次に新設する PressureBeam
```

という分離が見えた。これは大きい。

## 何が閉じたか

閉じたのは、次の局所系じゃ。

```text id="6chouc"
pressure margin と net-drop の局所遷移
```

```text id="m6ocza"
local island / interval pulse の生成
```

```text id="yuqg08"
explicit witness-list accounting
```

```text id="qs3i6h"
sorted-before failure の検出
```

```text id="3j2iyk"
failure が recovered diagnostic か overlap obstruction へ分岐する automaton
```

この意味で、ぬしの言う「会計システム」は閉じた。
少なくとも、局所圧力がどう記録され、失敗がどう診断されるかは、Lean 上で一つの機械として読める段階になっている。

## 何がまだ閉じていないか

未閉じなのは、次じゃ。

```text id="s8qy6f"
局所 failure resolution を、次の時間窓へ運ぶ定理
```

```text id="wp9og1"
複数の local automaton state を Beam として連鎖させる定義
```

```text id="z9mbld"
overlap obstruction が時間方向に蓄積するのか、吸収されるのかの分類
```

```text id="z0thc9"
局所 Big から大域 Big への持ち上げ
```

つまり、今は **命令語は読めた**。
次は **命令列の制御フロー** を読む段階じゃ。

## 次に収束すべき実装

次は `PressureBeam.lean` の新設でよい。
ただし、まだ強い theorem は足さない。

最初の `PressureBeam` は、薄い interface でよい。

候補はこうじゃ。

```lean id="zw1c7a"
import DkMath.Collatz.PetalBridge.PressureAutomaton
```

そして、最初に置くなら定義だけ。

```lean id="4f02eg"
def SourcePressureBeamState
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
  SourcePressureFailureResolution L
```

ただし、この名前が単なる alias すぎるなら、初回は **report-only で設計を固める** 方がよい。

本当に Lean に入れる価値があるのは、次のような「Beam index」が見えてからじゃ。

```lean id="h4s7lj"
structure SourcePressureBeamNode where
  -- local witness list
  -- local resolution state
  -- next window / next index relation
```

まだこの `next` の具体形がないなら、`PressureBeam.lean` は急がず、次 checkpoint は design-only でもよい。

## わっちの判断

いまの局面はこうじゃ。

```text id="71x5dp"
Core:
  閉じた

Automaton:
  閉じた

Beam:
  入口が見えた

Global Big:
  まだ
```

だから、問いへの答えは、

**「局所会計オートマトンとしては閉じた。コラッツ大域収束としてはまだ閉じていない。次は `PressureBeam` で伝播構造を作る段階」**

じゃ。

## 次の Codex 指示

```text id="ctunln"
Checkpoint: petal-201

Main goal:
  Start the Beam-facing layer above `PressureAutomaton`, but keep it thin.
  The goal is not to prove propagation or convergence yet.  The goal is to
  create the correct upper module boundary for future Beam/time/orbit transport
  of local pressure automaton states.

Primary target file:
  DkMath/Collatz/PetalBridge/PressureBeam.lean

Allowed supporting files:
  DkMath/Collatz/PetalBridge.lean
  docs/dev/das-p2l-260607/review/report-petal-201.md

Imports:
  `PressureBeam.lean` should import only:
    DkMath.Collatz.PetalBridge.PressureAutomaton

Do not modify:
  DkMath/Collatz/PetalBridge/PressureDecay.lean
  DkMath/Collatz/PetalBridge/PressureFrontier.lean
  DkMath/Collatz/PetalBridge/PressureAccounting.lean
  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
  DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
  DkMath/Collatz/PetalBridge/PressureAutomaton.lean
  Any non-Collatz files

Context:
  The local Core/accounting system and failure-resolution automaton are now
  named and no-sorry.

  Current stack:

    DriftBudget
      <- PressureDecay
        <- PressureFrontier
          <- PressureAccounting
            <- PressureLocalWitnessObstruction
              <- PressureAdjacentDiagnosis
                <- PressureDiagnosticDecomposition
                  <- PressureAutomaton

  The next upper layer should be:

    PressureAutomaton
      <- PressureBeam

Purpose of `PressureBeam`:
  Provide a future home for Beam-facing propagation of local pressure automaton
  states.  This checkpoint should not prove propagation, convergence, coverage,
  or aggregation.

Suggested minimal content:
  - module header explaining that Beam is the propagation layer above the
    local pressure automaton;
  - possibly a very thin alias/predicate only if it is genuinely useful;
  - otherwise report-only is acceptable.

Possible definition, only if useful:

  def SourcePressureBeamSeed
      {n : OddNat} {k r : ℕ}
      (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
    SourcePressureFailureResolution L

Do not add this alias if it provides no downstream value yet.  Prefer a
documentation-only skeleton if no precise Beam theorem is ready.

Guardrails:
  Do not add:
    - propagation theorem;
    - convergence theorem;
    - global coverage;
    - arbitrary-list recursive decomposition;
    - canonical first diagnosis;
    - enumeration of all diagnostics;
    - aggregation over multiple recovered diagnostics;
    - interval union accounting;
    - overlap repair;
    - maximality;
    - uniqueness;
    - sorting theorem;
    - disjointness between multiple recovered families.

Report requirements:
  - State whether Lean code was added or whether this remained design-only.
  - Explain that Core/local accounting and Automaton/failure resolution are
    now closed as local machinery.
  - Explain that Beam/global propagation is not yet closed.
  - Record the intended import direction:
      PressureAutomaton <- PressureBeam
  - Explicitly state that no propagation, convergence, aggregation, coverage,
    or overlap repair theorem was added.

Verification commands:
  lake build DkMath.Collatz.PetalBridge.PressureBeam
  lake build DkMath.Collatz.PetalBridge

No-sorry check:
  rg -n "\bsorry\b|admit" \
    DkMath/Collatz/PetalBridge/PressureBeam.lean \
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

うむ。ここまで来たなら、次は焦らず `PressureBeam` じゃ。
局所機械は閉じた。次はその機械が走る「軌道上の配線」を見る。

## Diff

`````md
````diff
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-200.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-200.md
new file mode 100644
index 00000000..e0b84feb
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-200.md
@@ -0,0 +1,248 @@
+# report-petal-200
+
+## Checkpoint
+
+`petal-200` is an audit-only checkpoint.
+
+No Lean theorem was added.  No import change was needed.  The purpose of this
+checkpoint is to decide where the next Beam-facing pressure propagation layer
+should live after `PressureAutomaton`.
+
+## Current Pressure Chain
+
+The lower drift/accounting chain is:
+
+```text
+DriftBudget
+  <- PressureDecay
+    <- PressureFrontier
+      <- PressureAccounting
+```
+
+The current diagnostic/automaton chain is:
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
+So the effective stack for the pressure series is:
+
+```text
+DriftBudget
+  <- PressureDecay
+    <- PressureFrontier
+      <- PressureAccounting
+        <- PressureLocalWitnessObstruction
+          <- PressureAdjacentDiagnosis
+            <- PressureDiagnosticDecomposition
+              <- PressureAutomaton
+```
+
+## Ownership Map
+
+### Local pressure drift / net-drop propagation
+
+Owner: `DkMath.Collatz.PetalBridge.PressureDecay`
+
+This module owns the local margin and net-drop vocabulary:
+
+- `SourcePressureMarginInt`
+- `SourceRetentionDropInt`
+- `SourceContinuationDropInt`
+- `SourcePressureNetDropInt`
+- local transition theorems such as
+  `sourcePressureMarginStepDiff_eq` and
+  `sourcePressureMargin_next_eq_current_add_netDrop`
+- local sign-change and pulse predicates:
+  `SourcePressureSignChangeUp`,
+  `SourcePressureSignChangeDown`,
+  `SourcePressurePulse`,
+  `SourcePressureSignPulse`
+
+`DriftBudget` supplies lower residue/tail-count drift budgets, but the
+pressure-margin transition language itself starts in `PressureDecay`.
+
+### Interval pulse production
+
+Owner: `DkMath.Collatz.PetalBridge.PressureFrontier`
+
+This module owns the frontier and local-island producers:
+
+- `SourcePressureFrontier`
+- `SourcePressureLocalIsland`
+- `ExistsSourcePressureLocalIslandBelow`
+- `SourcePressureIntervalPulse`
+- `SourcePressureIntervalPulseAddress`
+- local-island-to-pulse/address constructors such as
+  `sourcePressureIntervalPulse_singleton_of_localIsland` and
+  `sourcePressureIntervalPulseAddress_of_localIsland`
+
+This is the right level for producing a pulse from a local pressure event.  It
+does not own witness-list accounting or diagnostic decomposition.
+
+### Explicit witness-list accounting
+
+Owner: `DkMath.Collatz.PetalBridge.PressureAccounting`
+
+This module owns explicit carrier/list accounting:
+
+- `SourcePressureIntervalNetDrop`
+- `SourcePressureAccountedInterval`
+- `SourcePressureAccountedIntervalFamily`
+- sorted-before/failure carriers for accounted interval lists
+- `SourcePressureLocalIslandWitness`
+- conversion from local-island witnesses to pulse-address families
+- singleton and sorted-list accounting theorems
+
+This is the Core/local accounting layer.  It is intentionally witness-local:
+it accounts for explicitly supplied witnesses and does not claim global
+coverage, maximality, uniqueness, or convergence.
+
+### Failure resolution automaton
+
+Owner: `DkMath.Collatz.PetalBridge.PressureAutomaton`
+
+This module currently names the already-proved diagnostic state:
+
+```text
+sorted-before failure
+  -> recovered adjacent pair diagnostic
+     or adjacent overlap obstruction
+```
+
+It also exposes the no-overlap consumer:
+
+```text
+sorted-before failure + no-adjacent-overlap
+  -> recovered adjacent pair diagnostic
+```
+
+This is not a propagation layer.  It is a state-resolution API above
+`PressureDiagnosticDecomposition`.
+
+## Core / Automaton / Beam Split
+
+### Core/local accounting
+
+Core/local accounting is the finite arithmetic layer:
+
+- pressure margin and net-drop arithmetic;
+- pulse and local-island production;
+- explicit interval accounting;
+- explicit witness-list accounting.
+
+This layer only speaks about data it is given.  It must not silently become a
+global coverage theorem.
+
+### Automaton/failure resolution
+
+The automaton layer is a named control state over explicit witness lists.
+It does not advance time, build a Beam, or repair overlap.  Its role is to say
+what a local sorted-before failure means:
+
+```text
+recover a pair-local diagnostic, or expose overlap as the obstruction.
+```
+
+This is the current role of `PressureAutomaton`.
+
+### Beam/propagation
+
+Beam-facing propagation is the next conceptual layer.  It should consume
+`SourcePressureFailureResolution` and decide how local states are transported
+along a Beam/time/orbit direction.
+
+That layer should not be inserted into `PressureDecay`, `PressureFrontier`, or
+`PressureAccounting`, because those files are lower-level producers and
+accountants.  It should also not be inserted into
+`PressureDiagnosticDecomposition`, because that file should remain the local
+branch split, not a propagation controller.
+
+## Recommendation
+
+Create a new upper module above `PressureAutomaton` when the first real
+Beam-facing statement is ready.
+
+Recommended name:
+
+```text
+DkMath.Collatz.PetalBridge.PressureBeam
+```
+
+Reason:
+
+- `PressureBeam` names the intended mathematical subject directly.
+- `PressurePropagation` is accurate but too broad; it could also describe
+  lower margin-transition facts already owned by `PressureDecay`.
+- `PressureAutomatonBeam` over-couples the future layer to the implementation
+  detail that the previous layer is called `PressureAutomaton`.
+
+Suggested future import direction:
+
+```lean
+import DkMath.Collatz.PetalBridge.PressureAutomaton
+```
+
+The first `PressureBeam` checkpoint should stay thin: define Beam-facing
+predicates or wrappers only after a concrete downstream theorem needs them.
+
+## Guardrails Confirmed
+
+This checkpoint did not add:
+
+- a propagation theorem;
+- a convergence theorem;
+- an aggregation theorem;
+- an overlap repair theorem;
+- arbitrary-list recursive decomposition;
+- canonical first diagnosis;
+- enumeration of all diagnostics;
+- interval union accounting;
+- coverage, maximality, uniqueness, or sorting theorems.
+
+## Verification
+
+Executed commands:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureAutomaton
+lake build DkMath.Collatz.PetalBridge
+rg -n "\bsorry\b|admit" \
+  DkMath/Collatz/PetalBridge/PressureAutomaton.lean \
+  DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean \
+  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean \
+  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
+  DkMath/Collatz/PetalBridge/PressureAccounting.lean \
+  DkMath/Collatz/PetalBridge/PressureFrontier.lean \
+  DkMath/Collatz/PetalBridge/PressureDecay.lean \
+  DkMath/Collatz/PetalBridge/DriftBudget.lean
+git diff --check
+```
+
+Result:
+
+- `lake build DkMath.Collatz.PetalBridge.PressureAutomaton`: passed.
+- `lake build DkMath.Collatz.PetalBridge`: passed.
+- no-sorry check over the pressure files listed above: no matches.
+- `git diff --check`: passed.
+
+The builds still replay the known unrelated warning in
+`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean` about an existing
+`sorry`.  This checkpoint did not touch that file.
+
+## Next Checkpoint
+
+If the next step is still Beam-facing, add:
+
+```text
+DkMath.Collatz.PetalBridge.PressureBeam
+```
+
+as a new upper module importing `PressureAutomaton`.  Keep it as a thin
+interface until there is a precise theorem that transports a local
+`SourcePressureFailureResolution` state along a concrete Beam index.
````
`````
