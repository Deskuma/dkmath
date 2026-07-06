# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.PressureBeam

gch: 7c1b25f57ff53b27664d3bade0339c8dbf82993f

## Report

cp201 完了です。

`PressureAutomaton` の上位に [PressureBeam.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean) を新設し、集約 import に追加しました。中身は薄い境界だけで、`SourcePressureBeamSeed` と既存 Automaton API の Beam-facing wrapper 2本に留めています。伝播・収束・集約・coverage・overlap repair は追加していません。

レポートは [report-petal-201.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-201.md) に作成しました。

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureBeam` passed
- `lake build DkMath.Collatz.PetalBridge` passed
- pressure 系 no-sorry check は一致なし
- `git diff --check` passed

既知の `ZsigmondyCyclotomicResearch.lean` の既存 `sorry` warning は replay されましたが、今回の範囲外です。

## Review

## 結論

ここから始まるのは、**Beam の設計**じゃ。

より正確には、

```text id="vltglc"
局所会計オートマトン
  から
時間方向・軌道方向の伝播構造
  へ移る段階
```

が始まる。

cp201 で `PressureBeam.lean` が追加され、`PressureAutomaton` の上に Beam-facing 境界ができた。追加されたのは `SourcePressureBeamSeed` と wrapper theorem 2 本だけで、伝播・収束・集約・coverage・overlap repair はまだ追加されていない。これは report にも明記されておる。

つまり、**機械は起動した。だがまだ走行路は敷かれていない**。

## いま閉じたもの

ここまでで閉じたのは、局所側じゃ。

```text id="l1d6pk"
Core:
  margin / net-drop / pulse / witness accounting

Automaton:
  sorted-before failure
    -> recovered diagnostic or overlap obstruction

BeamSeed:
  local automaton state を Beam へ渡す入口
```

`PressureBeam.lean` は次の import 境界を固定した。

```text id="mrljhi"
PressureAutomaton
  <- PressureBeam
```

全体ではこうじゃ。

```text id="fzq4eq"
DriftBudget
  <- PressureDecay
    <- PressureFrontier
      <- PressureAccounting
        <- PressureLocalWitnessObstruction
          <- PressureAdjacentDiagnosis
            <- PressureDiagnosticDecomposition
              <- PressureAutomaton
                <- PressureBeam
```

これで、局所会計機械の出力を Beam 側へ渡す「ポート」ができた。

## ここから始まるもの

ここから始まるのは、次の 3 つじゃ。

## 1. Beam transport の定義

まず必要なのは、

```text id="tqi5dk"
seed at one explicit witness list
  -> named candidate transport target
```

という形の **明示的な輸送先** じゃ。

まだ大域伝播ではない。
まずは、「この局所 seed は、どこへ運ばれる候補なのか」を型として持たせる段階じゃな。

たとえば将来的には、

```lean id="5zxob5"
structure SourcePressureBeamTransportTarget where
  -- source witness list
  -- target witness list or target index
  -- relation between them
```

のような器が必要になるかもしれぬ。

ただし、今すぐ structure を作るなら、フィールドはかなり慎重に選ぶべきじゃ。
まだ `time index`、`orbit index`、`Beam index` のどれを主語にするかが確定していない。

## 2. overlap obstruction の意味づけ

いま overlap は repair されていない。
そして、それで正しい。

しかし Beam に入ると、overlap obstruction は次のどちらかに分かれるはずじゃ。

```text id="1eaq3y"
局所的な詰まりとして消費される obstruction
```

または、

```text id="3jbx6m"
次の Beam state へ持ち越される obstruction
```

ここがかなり大事じゃ。

いまは overlap を悪者として潰していない。
それは、将来的に overlap が **次の Beam を生む Gap** になる可能性があるからじゃ。

DkMath 的に言えば、

```text id="rxkb9k"
recovered branch:
  Core に回収される

overlap obstruction branch:
  Beam か Gap に持ち越される
```

という分岐が見えてくる。

## 3. 局所 Big から Beam Big へ

いまの Core は局所会計じゃ。

次は、

```text id="yij6lv"
一つの Beam seed が、どれだけの範囲を支配するか
```

を見る。

ただし、ここでもいきなり coverage は言わない。

最初に必要なのは、せいぜい次の程度じゃ。

```text id="zhyn7v"
explicit seed
explicit target
explicit relation
```

つまり、

```text id="3zglek"
この seed は、この candidate target に接続できる
```

まで。

そこから後で、

```text id="lqrk8v"
複数 seed の連鎖
```

```text id="atxryu"
overlap の処理
```

```text id="97w93x"
Beam family
```

```text id="xayh7v"
大域 Big
```

へ進む。

## まだ始まっていないもの

念のため、ここははっきり言っておく。

まだ始まっていないのは、

```text id="6tgn1t"
Collatz convergence proof
```

```text id="77q97h"
全軌道 coverage
```

```text id="sfm41o"
任意 list の canonical transport
```

```text id="nueu84"
複数 recovered family の aggregation
```

```text id="kbermr"
overlap repair
```

```text id="w8owz4"
global disjointness
```

ここへ行くには、Beam transport の最小核が必要じゃ。

## 次に収束すべき実装

次 checkpoint は、`PressureBeam` に **transport target の名前だけ**を置くのがよい。

ただし、証明はまだ薄くてよい。

おすすめは、まず predicate の設計から。

```lean id="lcx910"
def SourcePressureBeamTransportCandidate
    {n : OddNat} {k r : ℕ}
    (L₀ L₁ : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
  SourcePressureBeamSeed L₀ ∧
    SourcePressureBeamSeed L₁
```

しかしこれは弱すぎる。
単に seed が 2 つあるだけで、transport ではない。

だから、現時点で本当に必要なのは、たぶん **design-only audit** じゃ。

次はこう問うべきじゃな。

```text id="pjrwf2"
Beam transport の index は何か？
```

候補は 3 つある。

```text id="4mzyex"
1. time/orbit step index
2. pressure-depth index
3. witness-list address / interval address
```

このどれを Beam の主軸にするかで、今後の定義が変わる。

## わっちの見立て

いちばん自然なのは、まず **pressure-depth index** じゃ。

理由は、すでに局所会計の中心が (M(j+1)=M(j)+\Delta(j)) で、(j) が depth 方向の隣接遷移を担っているからじゃ。

つまり、最初の Beam は時間軌道ではなく、

```text id="kqky2g"
depth-Beam
```

として始めるのが安全に見える。

時間方向 orbit Beam は、その後でよい。
いきなり Collatz 軌道時間へ接続すると、主張が大きくなりすぎる。

## 次の Codex 指示

```text id="bfilza"
Checkpoint: petal-202

Main goal:
  Audit the correct index axis for the first Beam transport layer.
  Do not add a transport theorem yet.  Decide whether the first Beam transport
  should be depth-indexed, orbit-time-indexed, or witness-address-indexed.

Primary target file:
  docs/dev/das-p2l-260607/review/report-petal-202.md

Allowed supporting files:
  DkMath/Collatz/PetalBridge/PressureBeam.lean
  DkMath/Collatz/PetalBridge/PressureDecay.lean
  DkMath/Collatz/PetalBridge/PressureFrontier.lean
  DkMath/Collatz/PetalBridge/PressureAccounting.lean

Do not modify:
  DkMath/Collatz/PetalBridge/PressureAutomaton.lean
  DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
  Any non-Collatz files

Audit questions:
  1. What is the most natural first Beam transport axis?
     - pressure-depth index;
     - orbit-time index;
     - witness-list / interval-address index.
  2. Which existing definitions expose that axis?
  3. Which axis can support a thin first theorem without claiming coverage,
     aggregation, or convergence?
  4. Should the first Beam target be a structure, a predicate, or report-only?
  5. What exact statement should be attempted in the next Lean checkpoint?

Expected recommendation:
  Prefer depth-indexed Beam transport first, unless the audit finds that the
  existing code already has a better explicit address/transport relation.

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
  - State that this checkpoint is audit-only.
  - Explain that `PressureBeam` currently contains only `SourcePressureBeamSeed`
    and Beam-facing wrappers.
  - Compare the three possible axes:
      depth,
      orbit time,
      witness/interval address.
  - Recommend the safest first axis.
  - Give the exact next proposed Lean definition/theorem shape.
  - State explicitly that no propagation, convergence, coverage, aggregation,
    or overlap repair was added.

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

## ひとことで言うと

ここから始まるのは、

**局所機械から伝播機械への移行**じゃ。

Core は会計。
Automaton は診断。
Beam は伝播。

いま、Beam の入口に立った。
次は「どの軸に沿って伝播を読むか」を決める。これを間違えなければ、コラッツ機械語の制御フローが見えてくる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 8a2ca946..69790f7e 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -23,6 +23,7 @@ import DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
 import DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
 import DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
 import DkMath.Collatz.PetalBridge.PressureAutomaton
+import DkMath.Collatz.PetalBridge.PressureBeam
 import DkMath.Collatz.PetalBridge.OneCycle
 import DkMath.Collatz.PetalBridge.ValuationFlowBridge
 import DkMath.Collatz.PetalBridge.Collision
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
new file mode 100644
index 00000000..ccca07ee
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
@@ -0,0 +1,85 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.PressureAutomaton
+
+#print "file: DkMath.Collatz.PetalBridge.PressureBeam"
+
+namespace DkMath.Collatz
+
+/-
+Checkpoint 201: Beam-facing pressure boundary.
+
+This file is deliberately above `PressureAutomaton`:
+
+```text
+PressureAutomaton
+  <- PressureBeam
+```
+
+The lower files already own the local machinery:
+
+* `PressureDecay` owns local margin/net-drop transitions;
+* `PressureFrontier` owns local-island and interval-pulse production;
+* `PressureAccounting` owns explicit witness-list accounting;
+* `PressureAutomaton` owns the local failure-resolution state.
+
+`PressureBeam` is the future home for Beam/time/orbit propagation of those
+local automaton states.  This checkpoint only creates the boundary and the
+first Beam-facing seed name.  It does not prove propagation, convergence,
+coverage, aggregation, overlap repair, uniqueness, maximality, sorting, or
+disjointness between multiple recovered families.
+-/
+
+/--
+Beam-facing seed state for a local pressure witness list.
+
+At this stage a Beam seed is exactly the local failure-resolution state already
+provided by `PressureAutomaton`.  The new name marks the handoff point from
+local automaton analysis to future Beam/time/orbit transport.
+
+This is intentionally only an alias-like predicate.  It does not assert that
+the seed propagates, covers a global interval, aggregates with other seeds, or
+repairs overlap.
+-/
+def SourcePressureBeamSeed
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
+  SourcePressureFailureResolution L
+
+/--
+Sorted-before failure produces a Beam seed.
+
+This is only the Beam-facing name for the automaton entry theorem
+`sourcePressureFailureResolution_of_sortedBeforeFailure`.  It creates no new
+propagation principle.
+-/
+theorem sourcePressureBeamSeed_of_sortedBeforeFailure
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L) :
+    SourcePressureBeamSeed L :=
+  sourcePressureFailureResolution_of_sortedBeforeFailure h
+
+/--
+If adjacent overlap is excluded, a Beam seed exposes a recovered adjacent-pair
+diagnostic.
+
+This is still pair-local.  It does not aggregate recovered diagnostics across a
+Beam and does not turn no-overlap into a global disjointness theorem.
+-/
+theorem sourcePressureBeamSeed_recovered_of_sortedBeforeFailure_of_noAdjacentOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
+    (hno : SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L) :
+    ∃ A B,
+      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+        SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+          A B :=
+  sourcePressureFailureResolution_recovered_of_noAdjacentOverlap h hno
+
+end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-201.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-201.md
new file mode 100644
index 00000000..4caad07e
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-201.md
@@ -0,0 +1,148 @@
+# report-petal-201
+
+## Checkpoint
+
+`petal-201` starts the Beam-facing layer above `PressureAutomaton`.
+
+Lean code was added, but only as a thin upper boundary:
+
+- new module: `DkMath.Collatz.PetalBridge.PressureBeam`
+- aggregator import added to `DkMath.Collatz.PetalBridge`
+- no lower pressure modules were modified
+
+## Import Direction
+
+The intended import direction is now fixed as:
+
+```text
+PressureAutomaton
+  <- PressureBeam
+```
+
+The full pressure chain is:
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
+                <- PressureBeam
+```
+
+`PressureBeam.lean` imports only:
+
+```lean
+import DkMath.Collatz.PetalBridge.PressureAutomaton
+```
+
+## Added API
+
+The new Beam layer introduces:
+
+```lean
+def SourcePressureBeamSeed
+```
+
+This is intentionally an alias-like predicate:
+
+```text
+SourcePressureBeamSeed L := SourcePressureFailureResolution L
+```
+
+It marks the handoff from local automaton analysis to future Beam/time/orbit
+transport.
+
+Two wrapper theorems were added:
+
+```lean
+sourcePressureBeamSeed_of_sortedBeforeFailure
+sourcePressureBeamSeed_recovered_of_sortedBeforeFailure_of_noAdjacentOverlap
+```
+
+Both are Beam-facing names for already proved `PressureAutomaton` facts.  They
+do not add proof strength.
+
+## Local Machinery Status
+
+Core/local accounting and Automaton/failure resolution are now closed as local
+machinery:
+
+- `PressureDecay` owns margin/net-drop transitions.
+- `PressureFrontier` owns local-island and interval-pulse production.
+- `PressureAccounting` owns explicit witness-list accounting.
+- `PressureAutomaton` owns local failure resolution.
+- `PressureBeam` names the Beam-facing seed state above that local automaton.
+
+Beam/global propagation is not closed yet.  The next layer still needs a
+concrete statement describing how a Beam seed is transported along a time,
+orbit, or Beam index.
+
+## Guardrails
+
+This checkpoint did not add:
+
+- a propagation theorem;
+- a convergence theorem;
+- aggregation over multiple recovered diagnostics;
+- global coverage;
+- interval union accounting;
+- overlap repair;
+- arbitrary-list recursive decomposition;
+- canonical first diagnosis;
+- enumeration of all diagnostics;
+- maximality;
+- uniqueness;
+- sorting theorem;
+- disjointness between multiple recovered families.
+
+Recovered diagnostics remain pair-local.  Overlap remains an obstruction
+unless explicitly excluded by a hypothesis.
+
+## Verification
+
+Executed commands:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureBeam
+lake build DkMath.Collatz.PetalBridge
+rg -n "\bsorry\b|admit" \
+  DkMath/Collatz/PetalBridge/PressureBeam.lean \
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
+- `lake build DkMath.Collatz.PetalBridge.PressureBeam`: passed.
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
+The next natural theorem should not be global propagation yet.  A safer next
+step is to define the first explicit Beam transport predicate above
+`SourcePressureBeamSeed`, with all inputs supplied explicitly:
+
+```text
+seed at one explicit witness list
+  -> named candidate transport target
+```
+
+No claim about coverage, uniqueness, aggregation, or convergence should be
+introduced until that transport target is concrete.
````
`````
