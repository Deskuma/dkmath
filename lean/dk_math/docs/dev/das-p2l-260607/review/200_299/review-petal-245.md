# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: 1aea31710cb7cd758a6e8261c76fb7b62ce8c70f

## Report

`Gap` と `opcode` の名前表を先に追加しました。

更新: [PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean)

追加した Gap 名:

```lean
inductive SourcePressureGapName where
  | missingFailureInput
  | unresolvedResolutionBranch
  | missingBeamSeed
  | missingPulseBox
  | missingNeighborCandidate
  | missingOrientation
  | missingAdjacentDiagnosis
  | unresolvedOverlapObstruction
  | missingTransport
  | missingCanonicalSelection
  | missingCoverage
  | missingAggregation
```

追加した opcode 名:

```lean
inductive SourcePressureOpcodeName where
  | enterFailureResolution
  | splitResolution
  | enterBeamSeed
  | extractPulseBox
  | projectNeighborMembership
  | projectNeighborDiagnostic
  | attachForwardOrientation
  | attachReverseOrientation
  | attachAdjacentDiagnosis
  | closeAsOverlapObstruction
  | markNoTransport
  | markNoCoverage
  | markNoCanonicalSelection
```

今回は名前だけです。証明 opcode の割り当ては後続で行えるように、コメントで以下のテーブル形を固定しました。

```text
state bits + gap name -- assigned opcode --> next named state
```

レポートも追加しました: [report-petal-245.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-245.md)

検証済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
```

`PressureState.lean` の `sorry|admit` は no match、`git diff --check` も通過です。

## Review

## 状況認識

ロードマップを書いている間に、かなり進んでいた。
認識を更新すると、**Phase 1 は完了、Phase 2/3 はかなり前進、さらに予定外に State 管理層まで入った**。

## 進んだ内容

## cp241: NeighborCandidate から W' を診断可能にした

追加：

```lean
sourcePressureBeamNeighborCandidate_left_mem
sourcePressureBeamNeighborCandidate_right_mem
sourcePressureBeamNeighborCandidate_right_center_full_diagnostic
```

これで、

```text
NeighborCandidate L W W'
  -> W ∈ L
  -> W' ∈ L
  -> W' centered full diagnostic
```

が通った。
これはロードマップ Phase 1 の本命そのもの。完了じゃ。

## cp242: oriented adjacent diagnosis へ接続した

追加：

```lean
sourcePressureBeamNeighborCandidate_forward_center_full_diagnostics_of_adjacentDiagnosis
sourcePressureBeamNeighborCandidate_reverse_center_full_diagnostics_of_adjacentDiagnosis
```

これで caller が向きを明示すれば、

```text
AdjacentPairInList L W W'
+ AdjacentDiagnosis L W W'
  -> NeighborCandidate L W W'
  -> W centered diagnostic
  -> W' centered diagnostic
```

が取れる。

reverse も同様。
これは Phase 2 / Phase 3 の入口まで進んでいる。

## cp244: PressureState 層が生えた

新規：

```text
DkMath.Collatz.PetalBridge.PressureState
```

追加された状態名：

```lean
SourcePressureStateName.sortedFailure
SourcePressureStateName.failureResolution
SourcePressureStateName.recoveredAdjacent
SourcePressureStateName.adjacentOverlap
SourcePressureStateName.beamSeed
SourcePressureStateName.centeredPulseBox
SourcePressureStateName.neighborCandidate
SourcePressureStateName.orientedNeighborDiagnostic
```

さらに Prop alias と薄い state transition theorem が入った。

流れはこう読める。

```text
SortedFailure
  -> FailureResolution
  -> BeamSeed
  -> CenteredPulseBox
  + NeighborCandidate
  -> signs / diagnostics
  + oriented adjacency
  -> OrientedNeighborDiagnostic
```

これはかなり良い。
証明部品が「点」から「状態遷移図」になり始めた。

## cp245: Gap / opcode 名表が入った

追加：

```lean
SourcePressureGapName
SourcePressureOpcodeName
```

Gap は、未接続セルの名前表。

```lean
missingFailureInput
unresolvedResolutionBranch
missingBeamSeed
missingPulseBox
missingNeighborCandidate
missingOrientation
missingAdjacentDiagnosis
unresolvedOverlapObstruction
missingTransport
missingCanonicalSelection
missingCoverage
missingAggregation
```

opcode は、今後その Gap を埋める proof move の名前表。

```lean
enterFailureResolution
splitResolution
enterBeamSeed
extractPulseBox
projectNeighborMembership
projectNeighborDiagnostic
attachForwardOrientation
attachReverseOrientation
attachAdjacentDiagnosis
closeAsOverlapObstruction
markNoTransport
markNoCoverage
markNoCanonicalSelection
```

これで表の形が固定された。

```text
state bits + gap name -- assigned opcode --> next named state
```

ここは「証明そのもの」ではなく、今後の探索盤面の定義。良い。

## 現在の到達点

いまの証明状態はこう。

```text
Failure / Resolution 系:
  SortedFailure
    -> FailureResolution
    -> BeamSeed

Pulse 系:
  BeamSeed
    -> CenteredPulseBox

Neighbor 系:
  NeighborCandidate
    -> endpoint membership
    -> W' centered diagnostic

Orientation 系:
  oriented AdjacentPairInList + AdjacentDiagnosis
    -> NeighborCandidate
    -> both endpoint centered diagnostics
    -> OrientedNeighborDiagnosticState

State 系:
  上記を PressureState.lean で名前付き状態遷移として整理
```

つまり、ロードマップ上ではここまで進んだ。

```text
Phase 1: Neighbor を診断可能にする
  完了

Phase 2: Neighbor の向きを取り出す
  forward/reverse theorem で実質前進

Phase 3: AdjacentPair diagnostic へ接続
  oriented adjacent diagnosis surface まで到達

追加 Phase:
  PressureState / Gap / Opcode の状態管理層を開始
```

## 今の未接続点

次に攻めるべき Gap は、かなり絞れた。

```text
OrientedNeighborDiagnostic
  -> recovered / overlap branch classification
```

または、

```text
FailureResolution
  -> exists oriented neighbor diagnostic
```

どちらを先にやるか。

わっちの判断では、次は **FailureResolution から状態表へ入れる存在定理** が本命。

いまは個別部品として、

```text
oriented adjacency + diagnosis -> OrientedNeighborDiagnostic
```

はある。
しかし上流の `FailureResolution L` から、

```text
∃ W W', OrientedNeighborDiagnosticState L W W'
```

へ入る道がまだ状態表として強くない。

ここを撃つと、状態機械が一気に動き出す。

## 次の攻め筋

次はこれ。

```text
SourcePressureFailureResolutionState L
  -> SourcePressureRecoveredAdjacentState L
     ∨ SourcePressureAdjacentOverlapState L
```

これは既に `cases` がある。

そのうえで recovered branch から、

```text
∃ A B,
  AdjacentPairInList L A B
  ∧ PairHasRecoveredAccountedFamilyDiagnostic A B
```

が取れる。

次に必要なのは、

```text
PairHasRecoveredAccountedFamilyDiagnostic A B
  -> AdjacentDiagnosis L A B
```

または既存定義上、これがすでに `AdjacentDiagnosis` の一部なら、その抽出。

狙う theorem はこう。

```lean
sourcePressureRecoveredAdjacentState_to_orientedNeighborDiagnosticState
```

形：

```lean
theorem sourcePressureRecoveredAdjacentState_to_exists_orientedNeighborDiagnosticState
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureRecoveredAdjacentState L) :
    ∃ W W',
      SourcePressureOrientedNeighborDiagnosticState L W W'
```

これが通れば、状態遷移はこうなる。

```text
RecoveredAdjacent
  -> OrientedNeighborDiagnostic
```

かなり大きい。

## 次の Codex 指示・短縮版

```text
Goal:
  Connect RecoveredAdjacentState to OrientedNeighborDiagnosticState.

Inspect:
  SourcePressureRecoveredAdjacentState
  SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
  SourcePressureLocalIslandWitnessAdjacentDiagnosis
  sourcePressureOrientedNeighborDiagnosticState_of_forward

Try:
  theorem sourcePressureRecoveredAdjacentState_to_exists_orientedNeighborDiagnosticState
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      (h : SourcePressureRecoveredAdjacentState L) :
      ∃ W W',
        SourcePressureOrientedNeighborDiagnosticState L W W'

Proof idea:
  rcases h with ⟨A, B, hin, hrec⟩
  derive or extract AdjacentDiagnosis L A B from hrec
  exact ⟨A, B, sourcePressureOrientedNeighborDiagnosticState_of_forward hin hdiag⟩

If blocked:
  Report exact missing bridge:
    PairHasRecoveredAccountedFamilyDiagnostic -> AdjacentDiagnosis

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 判定

今回の進みは良い。

特に大きいのは、

```text
NeighborCandidate
  -> endpoint diagnostics
```

と、

```text
state names + gap names + opcode names
```

が入ったこと。

今後は theorem を増やすだけではなく、**どの opcode がどの gap を埋めたか**で進捗を読める。

次は、

```text
RecoveredAdjacent
  -> OrientedNeighborDiagnostic
```

を狙う。
ここが通れば、状態遷移表の positive path がかなり繋がる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index 163313fa..9a677b91 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -62,6 +62,110 @@ inductive SourcePressureStateName where
   | orientedNeighborDiagnostic
   deriving DecidableEq, Repr

+/--
+Mnemonic names for currently unfilled or unconfirmed regions of the
+source-pressure proof automaton.
+
+These are intentionally names only.  They are the future opcode slots for
+places where the proof-flow can get stuck because one required piece of
+evidence has not yet been supplied or derived.
+
+The key distinction is:
+
+* a Gap name is not a contradiction;
+* a Gap name is not a theorem saying that evidence is impossible;
+* a Gap name is a stable label for "this transition has no assigned proof
+  opcode yet".
+
+Future work can attach proof-producing opcodes, impossibility theorems, or
+obstruction witnesses to these names one by one.
+-/
+inductive SourcePressureGapName where
+  /-- No sorted-before failure input has been supplied yet. -/
+  | missingFailureInput
+  /-- Failure resolution has not yet been split into recovered/overlap. -/
+  | unresolvedResolutionBranch
+  /-- A Beam seed is not yet available from the current evidence. -/
+  | missingBeamSeed
+  /-- A centered pulse box has not yet been produced for the selected witness. -/
+  | missingPulseBox
+  /-- A neighbor candidate has not yet been supplied by explicit adjacency. -/
+  | missingNeighborCandidate
+  /-- A symmetric neighbor candidate is known, but no ordered orientation is fixed. -/
+  | missingOrientation
+  /-- Orientation is known, but adjacent diagnosis evidence is not yet attached. -/
+  | missingAdjacentDiagnosis
+  /-- Overlap has appeared and remains an unresolved obstruction. -/
+  | unresolvedOverlapObstruction
+  /-- A local diagnostic exists, but no transport/propagation theorem applies. -/
+  | missingTransport
+  /-- A local witness is known, but no canonical selection principle is available. -/
+  | missingCanonicalSelection
+  /-- Local evidence exists, but list-wide coverage has not been proved. -/
+  | missingCoverage
+  /-- Local families exist, but no safe aggregation theorem has been assigned. -/
+  | missingAggregation
+  deriving DecidableEq, Repr
+
+/--
+Mnemonic opcode names for proof steps that may later fill Gap slots.
+
+At this stage these are labels, not executable code.  They name the kinds of
+proof-producing moves already visible in the project:
+
+* enter a state from existing evidence;
+* split a branch;
+* project endpoint facts;
+* attach an orientation;
+* attach a lower adjacent diagnosis;
+* close a branch as obstruction.
+
+Keeping these names separate from `SourcePressureGapName` makes the intended
+table shape explicit:
+
+```text
+state bits + gap name -- assigned opcode --> next named state
+```
+-/
+inductive SourcePressureOpcodeName where
+  | enterFailureResolution
+  | splitResolution
+  | enterBeamSeed
+  | extractPulseBox
+  | projectNeighborMembership
+  | projectNeighborDiagnostic
+  | attachForwardOrientation
+  | attachReverseOrientation
+  | attachAdjacentDiagnosis
+  | closeAsOverlapObstruction
+  | markNoTransport
+  | markNoCoverage
+  | markNoCanonicalSelection
+  deriving DecidableEq, Repr
+
+/-
+Gap/opcode table notes.
+
+Current named states already cover the positive path up to oriented local
+diagnostics.  The first important unfilled cells are:
+
+```text
+NeighborCandidate alone
+  -> missingOrientation
+  -> missingAdjacentDiagnosis
+
+CenteredPulseBox alone
+  -> missingBeamSeed
+
+OrientedNeighborDiagnostic
+  -> missingTransport
+  -> missingCoverage
+```
+
+These are not Lean theorems yet.  They are the mnemonic slots that future
+formal impossibility lemmas or additional bridge theorems can target.
+-/
+
 /--
 State bit `F`: sorted-before failure has been observed for the supplied
 witness list.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-245.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-245.md
new file mode 100644
index 00000000..3a0cc53a
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-245.md
@@ -0,0 +1,130 @@
+# Report: petal-245
+
+## Branch
+
+Added mnemonic names for the unfilled Gap regions and future proof opcodes.
+
+This checkpoint intentionally assigns names first.  It does not yet assign
+proofs to every opcode slot.
+
+## Updated File
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+```
+
+## Added Gap Names
+
+```lean
+inductive SourcePressureGapName where
+  | missingFailureInput
+  | unresolvedResolutionBranch
+  | missingBeamSeed
+  | missingPulseBox
+  | missingNeighborCandidate
+  | missingOrientation
+  | missingAdjacentDiagnosis
+  | unresolvedOverlapObstruction
+  | missingTransport
+  | missingCanonicalSelection
+  | missingCoverage
+  | missingAggregation
+```
+
+These are names only.
+
+They mean:
+
+```text
+this transition has no assigned proof opcode yet
+```
+
+They do not mean contradiction, impossibility, or failure of the mathematics.
+
+## Added Opcode Names
+
+```lean
+inductive SourcePressureOpcodeName where
+  | enterFailureResolution
+  | splitResolution
+  | enterBeamSeed
+  | extractPulseBox
+  | projectNeighborMembership
+  | projectNeighborDiagnostic
+  | attachForwardOrientation
+  | attachReverseOrientation
+  | attachAdjacentDiagnosis
+  | closeAsOverlapObstruction
+  | markNoTransport
+  | markNoCoverage
+  | markNoCanonicalSelection
+```
+
+These names describe proof-producing moves or formally recorded blockage
+markers.  They are not executable automaton instructions yet.
+
+## Table Shape
+
+The intended future table is now explicit in source comments:
+
+```text
+state bits + gap name -- assigned opcode --> next named state
+```
+
+First unfilled cells:
+
+```text
+NeighborCandidate alone
+  -> missingOrientation
+  -> missingAdjacentDiagnosis
+
+CenteredPulseBox alone
+  -> missingBeamSeed
+
+OrientedNeighborDiagnostic
+  -> missingTransport
+  -> missingCoverage
+```
+
+## Why This Is Useful
+
+This gives stable labels for the regions that are not yet filled.  Future
+agents can attach one of three things to each Gap name:
+
+- a positive bridge theorem;
+- a formal impossibility/negative theorem;
+- an obstruction witness.
+
+That matches the project strategy: name the unknown region first, then assign
+proof opcodes as the surrounding theorem network becomes strong enough.
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
+rg -n "sorry|admit" lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
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
