# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: a71ac3f09848e278f0184e63f062374bd7139c94

## Report

RecoveredAdjacentState から OrientedNeighborDiagnosticState への接続を実装しました。

更新: [PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean)

追加 theorem:

```lean
theorem sourcePressureRecoveredAdjacentState_to_exists_orientedNeighborDiagnosticState
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureRecoveredAdjacentState L) :
    ∃ W W',
      SourcePressureOrientedNeighborDiagnosticState L W W'
```

懸念されていた bridge:

```text
PairHasRecoveredAccountedFamilyDiagnostic -> AdjacentDiagnosis
```

は不足していませんでした。`PairHasRecovered...` の中に `hrev` と `hbudget` があり、既存 constructor の

```lean
SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered hrev hbudget
```

で `AdjacentDiagnosis` を作れました。

レポート: [report-petal-246.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-246.md)

検証済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

これで recovered branch については `missingAdjacentDiagnosis` の Gap が一つ埋まりました。NeighborCandidate 単独から orientation/diagnosis が出るわけではない、という境界は維持しています。

## Review

## 判定

**採用。Recovered branch が状態遷移表に接続された。**

追加 theorem：

```lean
theorem sourcePressureRecoveredAdjacentState_to_exists_orientedNeighborDiagnosticState
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureRecoveredAdjacentState L) :
    ∃ W W',
      SourcePressureOrientedNeighborDiagnosticState L W W'
```

これで、

```text
RecoveredAdjacent
  -> OrientedNeighborDiagnostic
```

が通った。

## 増えた事実

懸念していた bridge は不要だった。

```text
PairHasRecoveredAccountedFamilyDiagnostic
  -> AdjacentDiagnosis
```

は、`hrec` を開くと `hrev` と `hbudget` が出て、

```lean
SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered hrev hbudget
```

で作れた。

つまり recovered branch は、すでに adjacent diagnosis を内包していた。

流れはこれ。

```text
RecoveredAdjacentState L
  -> ∃ A B,
       AdjacentPairInList L A B
       ∧ PairHasRecoveredAccountedFamilyDiagnostic A B
  -> AdjacentDiagnosis L A B
  -> OrientedNeighborDiagnosticState L A B
```

## 状態表の更新

現在の positive path はこうなった。

```text
SortedFailure
  -> FailureResolution
  -> BeamSeed
  -> CenteredPulseBox

RecoveredAdjacent
  -> OrientedNeighborDiagnostic
```

そして Beam 側ではすでに、

```text
NeighborCandidate
  -> W' membership
  -> W' centered diagnostic
```

もある。

かなり接続が進んだ。

## 次に攻める場所

次は **FailureResolution から recovered / overlap の二分岐を状態遷移として処理する** のがよい。

狙いはこれ。

```lean
theorem sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_overlapState
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureFailureResolutionState L) :
    (∃ W W',
      SourcePressureOrientedNeighborDiagnosticState L W W') ∨
      SourcePressureAdjacentOverlapState L
```

これは通る可能性が高い。

証明筋：

```lean
rcases sourcePressureFailureResolutionState_cases h with hrec | hover
· exact Or.inl (sourcePressureRecoveredAdjacentState_to_exists_orientedNeighborDiagnosticState hrec)
· exact Or.inr hover
```

これが通ると、

```text
FailureResolution
  -> OrientedNeighborDiagnostic
     or AdjacentOverlap
```

になる。

つまり `R` 状態が、次の状態へ一段進む。

## 次の Codex 指示

```text
Goal:
  Connect FailureResolutionState to either OrientedNeighborDiagnosticState
  or AdjacentOverlapState.

Add in PressureState.lean:

  theorem sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_overlapState
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      (h : SourcePressureFailureResolutionState L) :
      (∃ W W',
        SourcePressureOrientedNeighborDiagnosticState L W W') ∨
        SourcePressureAdjacentOverlapState L

Use:
  sourcePressureFailureResolutionState_cases
  sourcePressureRecoveredAdjacentState_to_exists_orientedNeighborDiagnosticState

Proof:
  split recovered / overlap.
  recovered -> left
  overlap -> right

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 現在の評価

これは良い。
`missingAdjacentDiagnosis` の recovered 側が埋まった。

次で `FailureResolution` 全体を、

```text
diagnostic path
or overlap path
```

へ落とせる。
状態遷移表が動き始めた。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index 9a677b91..07bb129e 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -383,4 +383,43 @@ theorem sourcePressureOrientedNeighborDiagnosticState_of_forward
   exact
     ⟨hin, hdiag', hWentry, hWaddr, hWexit, hW'entry, hW'addr, hW'exit⟩
 
+/--
+Recovered adjacent state enters the oriented neighbor diagnostic state.
+
+This fills the first recovered-branch Gap slot:
+
+```text
+RecoveredAdjacent
+  -- attachAdjacentDiagnosis + attachForwardOrientation -->
+OrientedNeighborDiagnostic
+```
+
+The recovered state already stores both ingredients needed here:
+
+* the ordered adjacent-pair address `hin`;
+* the named pair-local recovered diagnostic `hrec`.
+
+Opening `hrec` gives the reversed-before witness and budget bound required by
+`SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered`.  The endpoint
+Beam diagnostics are then supplied by
+`sourcePressureOrientedNeighborDiagnosticState_of_forward`.
+
+No canonical pair is selected beyond the existential pair already stored in
+the recovered state, and no coverage, aggregation, transport, or convergence
+is claimed.
+-/
+theorem sourcePressureRecoveredAdjacentState_to_exists_orientedNeighborDiagnosticState
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h : SourcePressureRecoveredAdjacentState L) :
+    ∃ W W',
+      SourcePressureOrientedNeighborDiagnosticState L W W' := by
+  rcases h with ⟨A, B, hin, hrec⟩
+  rcases hrec with ⟨hrev, hbudget, _hneg, _hlen⟩
+  let hdiag : SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B :=
+    SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered hrev hbudget
+  exact
+    ⟨A, B,
+      sourcePressureOrientedNeighborDiagnosticState_of_forward hin hdiag⟩
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-246.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-246.md
new file mode 100644
index 00000000..0f6feaba
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-246.md
@@ -0,0 +1,114 @@
+# Report: petal-246
+
+## Goal
+
+Connect:
+
+```text
+SourcePressureRecoveredAdjacentState
+  -> exists SourcePressureOrientedNeighborDiagnosticState
+```
+
+## Result
+
+Implemented successfully.
+
+Updated file:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+```
+
+Added theorem:
+
+```lean
+theorem sourcePressureRecoveredAdjacentState_to_exists_orientedNeighborDiagnosticState
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h : SourcePressureRecoveredAdjacentState L) :
+    ∃ W W',
+      SourcePressureOrientedNeighborDiagnosticState L W W'
+```
+
+## Bridge Found
+
+The possible missing bridge was:
+
+```text
+PairHasRecoveredAccountedFamilyDiagnostic -> AdjacentDiagnosis
+```
+
+This bridge was not missing.
+
+`SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic`
+already stores:
+
+```lean
+∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
+  budget ≤ -2 ∧ negative ∧ length = 2
+```
+
+The lower adjacent diagnosis constructor only needs the first two pieces:
+
+```lean
+SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered hrev hbudget
+```
+
+So the proof path is:
+
+```text
+RecoveredAdjacentState L
+  -> exists A B, AdjacentPairInList L A B + PairHasRecovered...
+  -> AdjacentDiagnosis L A B
+  -> OrientedNeighborDiagnosticState L A B
+```
+
+## Gap Filled
+
+This fills the recovered-branch version of:
+
+```text
+missingAdjacentDiagnosis
+```
+
+with opcode reading:
+
+```text
+attachAdjacentDiagnosis + attachForwardOrientation
+```
+
+It does not fill the general case:
+
+```text
+NeighborCandidate alone -> OrientedNeighborDiagnostic
+```
+
+That still needs orientation and diagnosis evidence.
+
+## Guardrails
+
+No theorem added:
+
+- canonical pair selection beyond the existential pair already stored;
+- list-wide coverage;
+- aggregation;
+- overlap repair;
+- transport;
+- propagation;
+- Collatz convergence.
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
+git diff --check
+```
````
`````
