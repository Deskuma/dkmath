# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.PressureState

gch: 3fa5cd9047d829d633b6b2fbb7875f640c226046

## Report

軽い状態名レイヤを実装しました。

新規: [PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean)
公開 import: [PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean)

入れたものは、まず mnemonic 用の名前表です。

```lean
inductive SourcePressureStateName
  | sortedFailure
  | failureResolution
  | recoveredAdjacent
  | adjacentOverlap
  | beamSeed
  | centeredPulseBox
  | neighborCandidate
  | orientedNeighborDiagnostic
```

加えて、既存の `Prop` を状態名として読む alias と、薄い状態遷移 theorem を追加しました。流れとしては：

```text
SortedFailure -> FailureResolution -> BeamSeed
RecoveredAdjacent -> FailureResolution
AdjacentOverlap -> FailureResolution
CenteredPulseBox + NeighborCandidate -> signs
NeighborCandidate -> W' centered diagnostic
oriented adjacency + diagnosis -> OrientedNeighborDiagnostic
```

重要な注意として、コード中に「`CenteredPulseBox -> BeamSeed` はまだ提供しない」と明記しました。これは下流証拠から上流 seed を作ってしまう誤った逆流を防ぐためです。

レポートも追加しました: [report-petal-244.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-244.md)

検証済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
```

`PressureState.lean` / `PressureAutomaton.lean` / `PressureBeam/Pulse.lean` の `sorry|admit` は no match、`git diff --check` も通過です。既存の staged `review-petal-243.md` は触っていません。

## Consider

### 未確認状態

そうですね。ここでいう `Gap` は「偽」ではなく、まだ状態名や遷移が付いていない未分類領域です。

今の状態表で見ると、だいたいこうです。

```text
Core:
  SortedFailure
  FailureResolution
  RecoveredAdjacent
  AdjacentOverlap
  BeamSeed

Beam:
  CenteredPulseBox
  NeighborCandidate
  OrientedNeighborDiagnostic

Gap:
  未確認 / 未接続 / 未分類の状態
```

Lean 側で次に自然なのは、`Gap` を **正体不明の一枚岩** にせず、種類だけ分けることです。

候補はこのあたりです。

```lean
inductive SourcePressureGapName where
  | noSeedYet
  | noPulseBoxYet
  | noNeighborYet
  | noOrientationYet
  | noDiagnosticYet
  | unresolvedOverlap
  | untransportedDiagnostic
```

ただし、これは証明というより「未到達メモ」です。Lean theorem にするなら、まずは `Prop` で薄く：

```lean
def SourcePressureGapState
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
  True
```

みたいにしてしまうと弱すぎる。なので最初は source comment の表で十分かもしれません。

実装するなら、良い落とし所はこれです。

```lean
inductive SourcePressureUnknownStateName where
  | missingFailureInput
  | unresolvedResolutionBranch
  | missingPulseBox
  | missingNeighborCandidate
  | missingOrientation
  | missingAdjacentDiagnosis
  | unresolvedOverlapObstruction
  | missingTransport
```

そして `PressureState.lean` のコメントに「Gap taxonomy」として置く。
証明可能なものだけ theorem にする。

現時点の一番大事な Gap はたぶんこれです。

```text
NeighborCandidate L W W'
```

だけでは、

```text
AdjacentDiagnosis L W W'
```

も

```text
AdjacentDiagnosis L W' W
```

も出ない。

つまり、

```text
N -> D
```

はまだ足りない。
必要なのは orientation と diagnosis の追加証拠。

ここが「未確認状態」の中心ですね。

次にやるなら、`PressureState.lean` に `Gap taxonomy` をコメントで置き、形式化できる最小限として：

```lean
inductive SourcePressureGapName
```

だけ追加するのがよさそうです。これは将来の全状態ビット表の空欄ラベルになります。

## Review

採用とし、命名だけ先にしておく。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 69790f7e..b86c53e5 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -24,6 +24,7 @@ import DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
 import DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
 import DkMath.Collatz.PetalBridge.PressureAutomaton
 import DkMath.Collatz.PetalBridge.PressureBeam
+import DkMath.Collatz.PetalBridge.PressureState
 import DkMath.Collatz.PetalBridge.OneCycle
 import DkMath.Collatz.PetalBridge.ValuationFlowBridge
 import DkMath.Collatz.PetalBridge.Collision
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
new file mode 100644
index 00000000..163313fa
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -0,0 +1,282 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.PressureBeam
+
+#print "file: DkMath.Collatz.PetalBridge.PressureState"
+
+namespace DkMath.Collatz
+
+/-
+Mnemonic state layer for the source-pressure proof automaton.
+
+This file is intentionally a thin naming layer over the already proved
+pressure/Beam predicates.  The goal is not to create an executable automaton
+yet.  The current goal is a readable state table:
+
+```text
+SortedFailure
+  -> FailureResolution
+  -> BeamSeed
+  -> CenteredPulseBox
+  -> NeighborCandidate
+  -> OrientedNeighborDiagnostic
+```
+
+Each state below is still a `Prop`: it means that the proof currently has
+evidence for that named local configuration.  Transitions are theorem arrows
+between those named states.  This keeps the automaton Lean-native: movement is
+movement of evidence, not computation over an unproved global process.
+
+Important guardrail for future work:
+
+* these names do not assert total coverage of all possible lists;
+* they do not choose canonical witnesses or canonical adjacent pairs;
+* they do not repair overlap;
+* they do not propagate local diagnostics;
+* they do not prove Collatz convergence.
+
+The eventual "mnemonic table" can refine these names into bit patterns.  For
+now, the bits are deliberately informal and local:
+
+* `F`: sorted-before failure is present;
+* `R`: failure has resolved into recovered-pair or overlap evidence;
+* `S`: Beam seed state is available;
+* `P`: a centered local pulse box is available for a supplied witness;
+* `N`: an explicit neighbor candidate is available;
+* `D`: an oriented adjacent diagnosis is available.
+-/
+
+/-- Mnemonic names for the current proof-automaton nodes. -/
+inductive SourcePressureStateName where
+  | sortedFailure
+  | failureResolution
+  | recoveredAdjacent
+  | adjacentOverlap
+  | beamSeed
+  | centeredPulseBox
+  | neighborCandidate
+  | orientedNeighborDiagnostic
+  deriving DecidableEq, Repr
+
+/--
+State bit `F`: sorted-before failure has been observed for the supplied
+witness list.
+-/
+def SourcePressureSortedFailureState
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
+  SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L
+
+/--
+State bit `R`: the local failure-resolution automaton has split the failure
+into recovered-adjacent evidence or adjacent-overlap obstruction.
+-/
+def SourcePressureFailureResolutionState
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
+  SourcePressureFailureResolution L
+
+/--
+Recovered branch of the resolution state: some addressed adjacent pair carries
+the named pair-local recovered diagnostic.
+-/
+def SourcePressureRecoveredAdjacentState
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
+  ∃ A B,
+    SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+        A B
+
+/--
+Overlap branch of the resolution state: adjacent overlap is present as an
+obstruction on the supplied witness list.
+-/
+def SourcePressureAdjacentOverlapState
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
+  SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
+
+/--
+State bit `S`: Beam-facing seed state.  This is the Beam name for failure
+resolution.
+-/
+def SourcePressureBeamSeedState
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
+  SourcePressureBeamSeed L
+
+/--
+State bit `P`: a centered local pulse box is available for one supplied
+witness.
+-/
+def SourcePressureCenteredPulseBoxState
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (W : SourcePressureLocalIslandWitness n k r) : Prop :=
+  SourcePressureBeamCenteredLocalPulseBox n k r L W
+
+/--
+State bit `N`: an explicit symmetric neighbor candidate is available for two
+supplied witnesses.
+-/
+def SourcePressureNeighborCandidateState
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (W W' : SourcePressureLocalIslandWitness n k r) : Prop :=
+  SourcePressureBeamNeighborCandidate L W W'
+
+/--
+State bit `D`: an oriented adjacent diagnosis is available and the two
+endpoints expose their centered Beam diagnostics.
+
+The orientation is part of the state.  The first component is the ordered
+adjacent-pair address; the second component is the lower adjacent diagnosis;
+the remaining components are Beam-centered endpoint diagnostics.
+-/
+def SourcePressureOrientedNeighborDiagnosticState
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (W W' : SourcePressureLocalIslandWitness n k r) : Prop :=
+  SourcePressureLocalIslandWitnessAdjacentPairInList L W W' ∧
+    SourcePressureLocalIslandWitnessAdjacentDiagnosis L W W' ∧
+      SourcePressureBeamMassBalanceLeftInt n k r (W.val - 1) <
+        SourcePressureBeamMassBalanceRightInt n k r (W.val - 1) ∧
+        SourcePressureBeamAddressedDepthTarget L W.val ∧
+          SourcePressureBeamMassBalanceRightInt n k r W.val ≤
+            SourcePressureBeamMassBalanceLeftInt n k r W.val ∧
+            SourcePressureBeamMassBalanceLeftInt n k r (W'.val - 1) <
+              SourcePressureBeamMassBalanceRightInt n k r (W'.val - 1) ∧
+              SourcePressureBeamAddressedDepthTarget L W'.val ∧
+                SourcePressureBeamMassBalanceRightInt n k r W'.val ≤
+                  SourcePressureBeamMassBalanceLeftInt n k r W'.val
+
+/-- Generic proof-automaton transition: evidence for `S` can be moved to `T`. -/
+def SourcePressureStateTransition (S T : Prop) : Prop :=
+  S → T
+
+/-- `F -> R`: sorted-before failure enters the failure-resolution state. -/
+theorem sourcePressureSortedFailureState_to_failureResolutionState
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h : SourcePressureSortedFailureState L) :
+    SourcePressureFailureResolutionState L :=
+  sourcePressureFailureResolution_of_sortedBeforeFailure h
+
+/-- `R -> S`: failure resolution is exactly the Beam seed handoff state. -/
+theorem sourcePressureFailureResolutionState_to_beamSeedState
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h : SourcePressureFailureResolutionState L) :
+    SourcePressureBeamSeedState L :=
+  h
+
+/-- `S -> R`: the Beam seed state can be read back as failure resolution. -/
+theorem sourcePressureBeamSeedState_to_failureResolutionState
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h : SourcePressureBeamSeedState L) :
+    SourcePressureFailureResolutionState L :=
+  h
+
+/-- `F -> S`: sorted-before failure reaches the Beam seed handoff state. -/
+theorem sourcePressureSortedFailureState_to_beamSeedState
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h : SourcePressureSortedFailureState L) :
+    SourcePressureBeamSeedState L :=
+  sourcePressureBeamSeed_of_sortedBeforeFailure h
+
+/-- Recovered adjacent evidence is the recovered branch of resolution. -/
+theorem sourcePressureRecoveredAdjacentState_to_failureResolutionState
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h : SourcePressureRecoveredAdjacentState L) :
+    SourcePressureFailureResolutionState L :=
+  Or.inl h
+
+/-- Adjacent overlap evidence is the overlap branch of resolution. -/
+theorem sourcePressureAdjacentOverlapState_to_failureResolutionState
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h : SourcePressureAdjacentOverlapState L) :
+    SourcePressureFailureResolutionState L :=
+  Or.inr h
+
+/-- Split the failure-resolution state into its two mnemonic branches. -/
+theorem sourcePressureFailureResolutionState_cases
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h : SourcePressureFailureResolutionState L) :
+    SourcePressureRecoveredAdjacentState L ∨
+      SourcePressureAdjacentOverlapState L :=
+  h
+
+/-
+`P -> S`: a centered local pulse box remembers the witness membership part of
+the Beam seed surface only through its enclosing list state.
+
+This theorem is intentionally not provided yet.  A pulse box alone does not
+construct `SourcePressureBeamSeedState L`; the seed is an upstream state.
+Keeping this absence explicit prevents a common false transition in the future
+mnemonic table.
+-/
+
+/-- `P -> N + signs`: reuse the existing boxed-pulse and neighbor projection. -/
+theorem sourcePressureCenteredPulseBoxState_signs_of_neighborCandidateState
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (hbox : SourcePressureCenteredPulseBoxState L W)
+    (hneigh : SourcePressureNeighborCandidateState L W W') :
+    SourcePressureBeamNeighborCandidate L W W' ∧
+      W ∈ L ∧
+        SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0 ∧
+          0 < SourcePressureMarginInt n k (r + W.val) ∧
+            SourcePressureBeamAddressedDepthTarget L W.val ∧
+              SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 :=
+  SourcePressureBeamCenteredLocalPulseBox.signs_of_neighborCandidate
+    hbox hneigh
+
+/--
+`N -> centered diagnostic for W'`: neighbor-candidate state exposes the
+neighbor endpoint diagnostic.
+-/
+theorem sourcePressureNeighborCandidateState_right_center_full_diagnostic
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (hneigh : SourcePressureNeighborCandidateState L W W') :
+    SourcePressureBeamMassBalanceLeftInt n k r (W'.val - 1) <
+      SourcePressureBeamMassBalanceRightInt n k r (W'.val - 1) ∧
+      SourcePressureBeamAddressedDepthTarget L W'.val ∧
+        SourcePressureBeamMassBalanceRightInt n k r W'.val ≤
+          SourcePressureBeamMassBalanceLeftInt n k r W'.val :=
+  sourcePressureBeamNeighborCandidate_right_center_full_diagnostic hneigh
+
+/--
+Forward oriented adjacent diagnosis enters mnemonic state `D`.
+
+The underlying Beam theorem also returns the symmetric neighbor candidate.
+This mnemonic state keeps only the ordered diagnostic orientation and the two
+endpoint centered diagnostics.
+-/
+theorem sourcePressureOrientedNeighborDiagnosticState_of_forward
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (hin : SourcePressureLocalIslandWitnessAdjacentPairInList L W W')
+    (hdiag : SourcePressureLocalIslandWitnessAdjacentDiagnosis L W W') :
+    SourcePressureOrientedNeighborDiagnosticState L W W' := by
+  rcases
+    sourcePressureBeamNeighborCandidate_forward_center_full_diagnostics_of_adjacentDiagnosis
+      hin hdiag with
+    ⟨_hneigh, hdiag', hWentry, hWaddr, hWexit, hW'entry, hW'addr, hW'exit⟩
+  exact
+    ⟨hin, hdiag', hWentry, hWaddr, hWexit, hW'entry, hW'addr, hW'exit⟩
+
+end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-244.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-244.md
new file mode 100644
index 00000000..5e94a93d
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-244.md
@@ -0,0 +1,195 @@
+# Report: petal-244
+
+## Branch
+
+Implemented the first mnemonic state-management layer for the source-pressure
+proof automaton.
+
+The goal was not to build an executable global automaton.  The goal was to
+name the current proof states and make the local state transitions readable.
+
+## Implemented File
+
+New file:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+```
+
+Public import updated:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge.lean
+```
+
+## State Names
+
+Added a small mnemonic enum:
+
+```lean
+inductive SourcePressureStateName where
+  | sortedFailure
+  | failureResolution
+  | recoveredAdjacent
+  | adjacentOverlap
+  | beamSeed
+  | centeredPulseBox
+  | neighborCandidate
+  | orientedNeighborDiagnostic
+```
+
+This is only a name table.  The real states are still `Prop` aliases over the
+existing proof surfaces.
+
+## Prop State Aliases
+
+Added:
+
+```lean
+def SourcePressureSortedFailureState L : Prop
+def SourcePressureFailureResolutionState L : Prop
+def SourcePressureRecoveredAdjacentState L : Prop
+def SourcePressureAdjacentOverlapState L : Prop
+def SourcePressureBeamSeedState L : Prop
+def SourcePressureCenteredPulseBoxState L W : Prop
+def SourcePressureNeighborCandidateState L W W' : Prop
+def SourcePressureOrientedNeighborDiagnosticState L W W' : Prop
+def SourcePressureStateTransition (S T : Prop) : Prop := S → T
+```
+
+The intended mnemonic bits are recorded in source comments:
+
+```text
+F : sorted-before failure
+R : failure resolution
+S : Beam seed
+P : centered pulse box
+N : explicit neighbor candidate
+D : oriented adjacent diagnosis
+```
+
+## Transitions
+
+Added thin transition theorems:
+
+```lean
+theorem sourcePressureSortedFailureState_to_failureResolutionState
+theorem sourcePressureFailureResolutionState_to_beamSeedState
+theorem sourcePressureBeamSeedState_to_failureResolutionState
+theorem sourcePressureSortedFailureState_to_beamSeedState
+theorem sourcePressureRecoveredAdjacentState_to_failureResolutionState
+theorem sourcePressureAdjacentOverlapState_to_failureResolutionState
+theorem sourcePressureFailureResolutionState_cases
+theorem sourcePressureCenteredPulseBoxState_signs_of_neighborCandidateState
+theorem sourcePressureNeighborCandidateState_right_center_full_diagnostic
+theorem sourcePressureOrientedNeighborDiagnosticState_of_forward
+```
+
+## Important Negative Design Point
+
+The source code explicitly records that this false transition is not provided:
+
+```text
+CenteredPulseBoxState L W -> BeamSeedState L
+```
+
+A pulse box is downstream evidence.  It does not construct the upstream seed
+state.  This is important for the future mnemonic table because it prevents a
+common but invalid reversal of the proof flow.
+
+## Current Automaton Reading
+
+The current proof-flow can now be read as:
+
+```text
+SortedFailure
+  -> FailureResolution
+  -> BeamSeed
+  -> CenteredPulseBox
+  + NeighborCandidate
+  -> endpoint signs / centered diagnostics
+  + oriented adjacency
+  -> OrientedNeighborDiagnostic
+```
+
+This is still local and witness/list-relative.
+
+## Guardrails Preserved
+
+No theorem added:
+
+- global coverage;
+- canonical witness selection;
+- canonical adjacent pair selection;
+- overlap repair;
+- propagation;
+- arbitrary transport;
+- aggregation;
+- monotone trend;
+- Collatz convergence.
+
+## Next Branch Prediction
+
+The next useful branch is the actual mnemonic bit table.
+
+Candidate light design:
+
+```lean
+structure SourcePressureStateBits where
+  hasFailure : Bool
+  hasResolution : Bool
+  hasBeamSeed : Bool
+  hasPulseBox : Bool
+  hasNeighbor : Bool
+  hasOrientedDiagnostic : Bool
+```
+
+But this should remain a human-readable naming table unless a caller needs
+Boolean computation.  The proof-carrying states are currently more useful than
+raw `Bool` states.
+
+An immediate theorem branch, if needed, is a small exclusion/absence layer for
+known false transitions:
+
+```text
+PulseBox alone does not produce BeamSeed
+NeighborCandidate alone does not produce orientation
+NeighborCandidate alone does not produce oriented diagnosis
+```
+
+Those are better kept as source comments until a concrete caller needs them as
+formal negation theorems.
+
+## Verification
+
+Commands run from:
+
+```text
+lean/dk_math
+```
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureState
+lake build DkMath.Collatz.PetalBridge
+```
+
+No-sorry check:
+
+```text
+rg -n "sorry|admit" \
+  PressureState.lean \
+  PressureAutomaton.lean \
+  PressureBeam/Pulse.lean
+```
+
+Result: no matches.
+
+Whitespace check:
+
+```text
+git diff --check
+```
+
+Result: passed.
````
`````
