# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam.Pulse

gch: 5043a40649151756e7ed25cd99c0209cb549d03e

## Report

cp239 完了です。

今回は Branch C です。既存 API を調べた結果、`SourcePressureBeamCenteredLocalPulseBox` から直接 `neighbor candidate` や `transport obstruction` へ進む relation はまだありませんでした。既存の隣接・閉塞 API は list/pair ベースなので、box 単体から伝播を主張するのはまだ早いです。

追加したのは、local pulse box から sign/target 部分だけを取り出す projection lemma です。

- `SourcePressureBeamCenteredLocalPulseBox.signs`

レポート:
[report-petal-239.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-239.md)

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureDecay`
- `lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse`
- `lake build DkMath.Collatz.PetalBridge.PressureBeam`
- `lake build DkMath.Collatz.PetalBridge`
- no-sorry grep 対象範囲一致なし
- `git diff --check`

すべて通過しています。次は `SourcePressureBeamNeighborCandidate` か `SourcePressureBeamPulseTransportResolution` のような薄い relation を定義できるかが焦点です。

## Review

## 結論

**採用。これは安全な見送りじゃ。**

cp239 は、`SourcePressureBeamCenteredLocalPulseBox` から直接 neighbor / transport / obstruction へ進む relation がまだ無いことを確認し、無理な propagation theorem を作らず、必要最小限の projection lemma だけを追加している。これは正しい判断じゃ。

追加 theorem は 1 本。

```lean id="twkqj3"
SourcePressureBeamCenteredLocalPulseBox.signs
```

これは local pulse box から、

```text id="nq1uxy"
W ∈ L
previous margin ≤ 0
center margin > 0
addressed target at W.val
next margin ≤ 0
```

だけを取り出す projection lemma じゃ。

## 実装レビュー

実装は薄くて良い。

`SourcePressureBeamCenteredLocalPulseBox` には、

```text id="ylcy1q"
sign transition
height boxes
jump boxes
```

が全部入っている。
しかし多くの caller は、まず sign/target だけを使うはずじゃ。

そこで、

```lean id="de9v0a"
SourcePressureBeamCenteredLocalPulseBox.signs
```

を追加して、巨大な `rcases hbox with ...` を避けられるようにした。

これは API の実用性を上げる projection であり、数学的主張を増やしていない。
neighbor、transport、propagation、obstruction を勝手に推論していない点が良い。

## 数学的意味

cp238 で local pulse box はできた。

```text id="8bs2ry"
local pulse box:
  sign + height + jump
```

cp239 では、そのうち最初に使う核だけを取り出した。

```text id="l5r4vr"
local pulse box
  -> sign/target facts
```

DkMath 的には、

```text id="uz3znx"
Core:
  boxed local pulse

True Beam:
  active sign pattern を projection として使える

Boundary:
  one witness W の局所事実だけ

Gap:
  box から neighbor / transport / obstruction へ進む relation は未定義
```

という段階じゃ。

## 重要な発見

今回の一番大きな収穫は、実は theorem 追加そのものではない。

見つかった Gap が明確になったことじゃ。

```text id="dcsoql"
SourcePressureBeamCenteredLocalPulseBox n k r L W
  -> ∃ W', NeighborCandidate L W W'
```

または、

```text id="ej8rla"
SourcePressureBeamCenteredLocalPulseBox n k r L W
  -> TransportObstruction L W ∨ ∃ W', NeighborCandidate L W W'
```

この relation がまだない。
既存の adjacent / obstruction machinery は list/pair ベースであり、box 単体から隣接 witness を生むものではない、と整理されている。

これは非常に重要じゃ。
ここを誤ると、

```text id="c4r4jc"
boxed pulse がある
  -> だから隣へ運べる
```

という過大主張になる。

## 次の方針

次は、いきなり transport theorem を狙うのではなく、**既存 list/pair machinery と local pulse box を接続するための明示的な relation** を作るのがよい。

ただし、relation は「box から勝手に neighbor が出る」としてはいけない。

正しい形は、

```text id="g88imf"
box + explicit adjacent-pair/list hypothesis
  -> neighbor candidate surface
```

じゃ。

つまり、次は **明示的隣接仮説つきの bridge** を狙う。

## 次の Codex 指示

```text id="wxaan4"
Checkpoint: petal-240

Primary Goal:
  Define or discover the first explicit neighbor-candidate surface connecting
  a boxed local pulse to existing list/pair adjacency machinery.

Context:
  cp238 introduced:

    SourcePressureBeamCenteredLocalPulseBox

  cp239 added:

    SourcePressureBeamCenteredLocalPulseBox.signs

  cp239 also confirmed that there is currently no theorem of the form:

    SourcePressureBeamCenteredLocalPulseBox n k r L W
      -> ∃ W', NeighborCandidate L W W'

  The existing machinery is list/pair based:
    - SourcePressureLocalIslandWitnessAdjacentPairInList
    - SourcePressureLocalIslandWitnessAdjacentDiagnosis
    - SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
    - SourcePressureFailureResolution

  Therefore the next step must not infer a neighbor from the box alone.
  It should connect the box to explicit adjacent-pair hypotheses.

Strategic Branch Goals:

  Branch A: define a thin explicit neighbor candidate predicate
    If no existing predicate already serves this role, define a Beam-facing
    predicate in `PressureBeam/Pulse.lean` or a nearby Beam-facing module:

      def SourcePressureBeamNeighborCandidate
          {n : OddNat} {k r : ℕ}
          (L : List (SourcePressureLocalIslandWitness n k r))
          (W W' : SourcePressureLocalIslandWitness n k r) : Prop :=
        SourcePressureLocalIslandWitnessAdjacentPairInList L W W' ∨
        SourcePressureLocalIslandWitnessAdjacentPairInList L W' W

    Use this only as a naming surface for explicit adjacency.
    Do not claim that a boxed pulse produces such a candidate.

  Branch B: explicit adjacent pair to neighbor candidate
    If Branch A defines the predicate, add tiny constructors:

      theorem sourcePressureBeamNeighborCandidate_of_adjacentPair_left
          (h : SourcePressureLocalIslandWitnessAdjacentPairInList L W W') :
          SourcePressureBeamNeighborCandidate L W W'

      theorem sourcePressureBeamNeighborCandidate_of_adjacentPair_right
          (h : SourcePressureLocalIslandWitnessAdjacentPairInList L W' W) :
          SourcePressureBeamNeighborCandidate L W W'

    Add these only if they improve usability.

  Branch C: boxed pulse plus explicit neighbor candidate
    If the predicate is available, add a consumer theorem that does not prove
    propagation, but packages usable facts:

      theorem SourcePressureBeamCenteredLocalPulseBox.signs_of_neighborCandidate
          (hbox : SourcePressureBeamCenteredLocalPulseBox n k r L W)
          (hneigh : SourcePressureBeamNeighborCandidate L W W') :
          SourcePressureBeamNeighborCandidate L W W' ∧
            W ∈ L ∧
            SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0 ∧
            0 < SourcePressureMarginInt n k (r + W.val) ∧
            SourcePressureBeamAddressedDepthTarget L W.val ∧
            SourcePressureMarginInt n k (r + W.val + 1) ≤ 0

    This is only a local consumer surface.
    It must not assert that W' has a pulse box or diagnostic.

  Branch D: existing relation already enough
    If an existing theorem/predicate already expresses neighbor candidate,
    do not introduce a new name.

    Report the exact existing name and add only a projection/alias if clearly
    useful.

  Branch E: list-level failure is the real bridge
    If the only meaningful next relation is list-level:

      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L
        -> SourcePressureFailureResolution L

    then do not force a neighbor-candidate predicate.

    Report that propagation must be mediated by list-level failure/resolution,
    not by one boxed witness.

Implementation rules:
  - Use #check, #print, and scratch lemmas.
  - Do not infer adjacency from `SourcePressureBeamCenteredLocalPulseBox`.
  - Add no theorem claiming that W' exists from hbox alone.
  - Add at most one small predicate and at most two tiny constructor/projection
    lemmas.
  - Prefer no-code report if existing names are sufficient.

Files to inspect:
  DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
  DkMath/Collatz/PetalBridge/PressureBeam/Core.lean
  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
  DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
  DkMath/Collatz/PetalBridge/PressureAutomaton.lean

Search terms:
  AdjacentPairInList
  AdjacentDiagnosis
  Neighbor
  Candidate
  Transport
  Obstruction
  FailureResolution
  SortedBeforeFailure
  SourcePressureBeamCenteredLocalPulseBox

Guardrails:
  Do not add:
    - neighbor existence from box alone;
    - propagation;
    - list-wide coverage;
    - witness-family aggregation;
    - canonical witness selection;
    - arbitrary target transport;
    - overlap repair;
    - disjointness;
    - monotone trend;
    - global Big bounds;
    - Collatz convergence.

Verification if code changes:
  lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
  lake build DkMath.Collatz.PetalBridge.PressureBeam
  lake build DkMath.Collatz.PetalBridge
  no-sorry grep over inspected pressure files
  git diff --check

Report requirements:
  - State which Branch was taken.
  - If a neighbor predicate is added, explain that it is explicit adjacency,
    not derived propagation.
  - If no code is added, identify the existing relation or exact missing bridge.
  - Classify as True Beam / Boundary / False Beam / Gap.
  - Predict whether the next branch should connect neighbor candidates to
    adjacent-pair diagnostics or remain list-level.
```

## 待ち構え

次の理想はこれ。

```text id="mlf4gd"
boxed local pulse
  + explicit adjacent-pair relation
  -> neighbor candidate surface
```

ただし、ここで重要なのは、

```text id="ro56tt"
box から neighbor を作らない
```

ことじゃ。

neighbor は list/pair 構造から来る。
box はその witness の局所診断を運ぶ。

この役割分担を崩さずに接続できれば、Core から Beam への橋が安全に伸びる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
index 194ade98..222c242e 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
@@ -393,6 +393,32 @@ def SourcePressureBeamCenteredLocalPulseBox
                       SourcePressureNetDropInt n k r W.val ≤
                         3 * (k : ℤ))

+/--
+Project the sign-and-target part of a centered local pulse box.
+
+This is the cp239 Branch C consumer surface.  It exposes the part that a future
+neighbor/transport theorem will usually need first, while leaving the finite
+height and jump boxes inside `SourcePressureBeamCenteredLocalPulseBox` for
+callers that need quantitative bounds.
+
+No neighboring witness, transport, propagation, or obstruction is inferred
+from this projection.
+-/
+theorem SourcePressureBeamCenteredLocalPulseBox.signs
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W : SourcePressureLocalIslandWitness n k r}
+    (hbox : SourcePressureBeamCenteredLocalPulseBox n k r L W) :
+    W ∈ L ∧
+      SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0 ∧
+        0 < SourcePressureMarginInt n k (r + W.val) ∧
+          SourcePressureBeamAddressedDepthTarget L W.val ∧
+            SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 := by
+  rcases hbox with
+    ⟨hmem, hprev, hcenter, haddr, hnext, _hprevBox, _hcenterBox,
+      _hnextBox, _hentryJumpBox, _hexitJumpBox⟩
+  exact ⟨hmem, hprev, hcenter, haddr, hnext⟩
+
 /--
 A Beam seed exposes one witness whose centered pulse is inside the finite
 local pulse box.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-239.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-239.md
new file mode 100644
index 00000000..237217d0
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-239.md
@@ -0,0 +1,203 @@
+# report-petal-239
+
+## Checkpoint
+
+`petal-239`
+
+## Summary
+
+Implemented Branch C.
+
+I inspected the current pressure files for a direct neighbor/transport relation
+from:
+
+```lean
+SourcePressureBeamCenteredLocalPulseBox n k r L W
+```
+
+to a neighboring witness or transport candidate.  The existing code has strong
+adjacent-pair and obstruction machinery, but it is list/pair based:
+
+```text
+SourcePressureLocalIslandWitnessAdjacentPairInList
+SourcePressureLocalIslandWitnessAdjacentDiagnosis
+SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+SourcePressureFailureResolution
+```
+
+There is not yet a direct relation of the form:
+
+```text
+boxed local pulse at W
+  -> neighboring candidate W'
+```
+
+or:
+
+```text
+boxed local pulse at W
+  -> transport obstruction
+```
+
+So this checkpoint adds only a small projection lemma for the most immediately
+useful part of the cp238 box.
+
+## Added Theorem
+
+```lean
+theorem SourcePressureBeamCenteredLocalPulseBox.signs
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W : SourcePressureLocalIslandWitness n k r}
+    (hbox : SourcePressureBeamCenteredLocalPulseBox n k r L W) :
+    W ∈ L ∧
+      SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0 ∧
+        0 < SourcePressureMarginInt n k (r + W.val) ∧
+          SourcePressureBeamAddressedDepthTarget L W.val ∧
+            SourcePressureMarginInt n k (r + W.val + 1) ≤ 0
+```
+
+This theorem is local and witness-relative.  It simply projects the sign and
+target part of the cp238 local pulse box.  It does not infer a neighboring
+witness, transport, propagation, or obstruction.
+
+## Search Result
+
+Files inspected:
+
+```text
+DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
+DkMath/Collatz/PetalBridge/PressureBeam/Core.lean
+DkMath/Collatz/PetalBridge/PressureAutomaton.lean
+DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
+DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
+DkMath/Collatz/PetalBridge/PressureDecay.lean
+DkMath/Collatz/PetalBridge/PressureFrontier.lean
+DkMath/Collatz/PetalBridge/PressureAccounting.lean
+```
+
+Useful existing surfaces:
+
+```lean
+SourcePressureFailureResolution
+sourcePressureFailureResolution_of_sortedBeforeFailure
+sourcePressureFailureResolution_recovered_of_noAdjacentOverlap
+
+SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
+SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+exists_adjacentPairInList_pairOverlapObstruction_of_overlapObstruction
+sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_or_adjacentOverlap
+```
+
+These are about explicit list failure, adjacent pairs, recovered diagnostics,
+and overlap obstruction.  They do not currently consume a single boxed pulse
+witness and produce a neighbor.
+
+## Missing Relation
+
+The exact missing propagation relation is one of the following:
+
+```text
+SourcePressureBeamCenteredLocalPulseBox n k r L W
+  -> ∃ W', NeighborCandidate L W W'
+```
+
+or:
+
+```text
+SourcePressureBeamCenteredLocalPulseBox n k r L W
+  -> TransportObstruction L W ∨ ∃ W', NeighborCandidate L W W'
+```
+
+There is also a possible list-mediated version:
+
+```text
+SourcePressureBeamCenteredLocalPulseBox n k r L W
+  -> SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L
+  -> SourcePressureFailureResolution L
+```
+
+but that requires an explicit list-level failure hypothesis.  The box alone
+does not provide list failure.
+
+## How cp238 Should Be Consumed
+
+The cp238 box is best treated as a local diagnostic carrier:
+
+```text
+boxed pulse
+  -> sign/target facts
+  -> height/jump facts
+  -> future neighbor or obstruction theorem
+```
+
+This checkpoint added the first projection:
+
+```text
+boxed pulse -> sign/target facts
+```
+
+The quantitative height/jump projection can be added next if caller noise
+appears around the boxed bounds.
+
+## Big / Core / Beam / Gap Classification
+
+- Core:
+  cp238 local pulse box remains the primary carrier.
+
+- True Beam:
+  the sign/target projection is now a named theorem, so callers can use the
+  active pulse shape without unpacking all height and jump bounds.
+
+- Boundary:
+  the theorem only exposes facts already present in the box for one witness
+  `W ∈ L`.
+
+- False Beam:
+  no transport, neighbor selection, propagation, or obstruction follows from
+  the box alone.
+
+- Gap:
+  the missing object is a real neighbor-candidate or transport-obstruction
+  relation connecting one boxed pulse to adjacent witness/list structure.
+
+## Next Branch Prediction
+
+The next useful branch is to introduce a thin local relation only if it matches
+existing list machinery.  Candidate names:
+
+```text
+SourcePressureBeamNeighborCandidate
+SourcePressureBeamPulseTransportObstruction
+SourcePressureBeamPulseTransportResolution
+```
+
+The safest next step is not to assert propagation, but to define or discover a
+small relation that says what it means for a boxed pulse to have a neighboring
+candidate.  Once that relation exists, the current adjacent-pair and overlap
+obstruction API can be connected without overstating global behavior.
+
+## Verification
+
+Commands run:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureDecay
+lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
+lake build DkMath.Collatz.PetalBridge.PressureBeam
+lake build DkMath.Collatz.PetalBridge
+rg -n "sorry|admit" <pressure-file-scope>
+git diff --check
+```
+
+Results:
+
+```text
+PressureDecay build: pass
+PressureBeam.Pulse build: pass
+PressureBeam build: pass
+PetalBridge build: pass
+no-sorry grep: no matches in inspected pressure scope
+git diff --check: pass
+```
````
`````
