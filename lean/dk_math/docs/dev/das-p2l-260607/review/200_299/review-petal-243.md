# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam.Pulse

gch: 90bd1a473575524d6f9f06ec93c1c195bf20bd20

## Report

続行分も実装しました。

[PressureBeam/Pulse.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean) に、oriented adjacent-pair diagnosis から Beam neighbor candidate と両端 centered diagnostic をまとめて取り出す theorem を 2 つ追加しました。

- `sourcePressureBeamNeighborCandidate_forward_center_full_diagnostics_of_adjacentDiagnosis`
- `sourcePressureBeamNeighborCandidate_reverse_center_full_diagnostics_of_adjacentDiagnosis`

forward/reverse の向きは caller が `AdjacentPairInList` と `AdjacentDiagnosis` で明示します。対称な neighbor candidate だけから向きを推測せず、box から neighbor を生成する主張もしていません。

レポートも追加しました: [report-petal-242.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-242.md)

検証済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
```

対象 pressure files の `sorry|admit` grep は no match、`git diff --check` も通過です。現状 `Pulse.lean` は既存 staged 分にさらに変更が乗っていて、`report-petal-241.md` は staged、`report-petal-242.md` は untracked です。

## Consider

### ステート管理、状態遷移を書けるか？：オートマトンの動きを追う

書けます。しかも今の構造なら、いきなり重い有限オートマトンにせず、段階的に書くのが自然です。

現在の `PressureAutomaton.lean` はすでに「状態名」を持っています。

```lean
def SourcePressureFailureResolution L : Prop :=
  recovered adjacent pair ∨ adjacent overlap obstruction
```

これはまだ「状態遷移機械」ではなく、**失敗状態をどう解決するかの分岐状態**です。

次に足すなら、こういう層が良いです。

```lean
inductive SourcePressureState
  | sorted
  | sortedFailure
  | recovered
  | overlap
  | beamSeed
  | beamNeighbor
  | gap
```

ただし最初から `inductive` に閉じ込めるより、Lean 的にはまず **遷移関係** を `Prop` として書く方が安全です。

```lean
def SourcePressureTransition (S T : Prop) : Prop :=
  S → T
```

より実用的には、既存定理に名前を与えて、

```text
SortedBeforeFailure
  -> FailureResolution

FailureResolution
  -> BeamSeed

BeamSeed
  -> exists centered pulse box

NeighborCandidate + orientation
  -> adjacent diagnostic + endpoint diagnostics
```

という **状態遷移ラベル付き theorem 群** にする。

たとえば今の流れはこう読めます。

```text
Failure
  -> Resolution
  -> Seed
  -> CenteredPulseBox
  -> NeighborCandidate
  -> OrientedAdjacentDiagnostic
```

ここで重要なのは、状態遷移を「計算」ではなく「証拠の移動」として書くことです。

```lean
State A -- theorem --> State B
```

ですね。

次の実装候補はかなり明確で、

```lean
DkMath.Collatz.PetalBridge.PressureState
```

のような薄いファイルを作って、

```lean
def SourcePressureAutomatonState ... : Prop
def SourcePressureStateTransition ... : Prop
```

を置くよりも、まずは既存状態を束ねるコメント付き alias が良さそうです。

候補:

```lean
def SourcePressureRecoveredState L : Prop := ...
def SourcePressureOverlapState L : Prop := ...
def SourcePressureBeamSeedState L : Prop := SourcePressureBeamSeed L
def SourcePressureNeighborState L W W' : Prop :=
  SourcePressureBeamNeighborCandidate L W W'
```

そして theorem:

```lean
theorem sourcePressureFailureResolution_to_beamSeed :
  SourcePressureFailureResolution L → SourcePressureBeamSeed L
```

これは既存で definitionally 同じなら薄く通るはずです。

結論として、**書けます**。
ただし「実行する automaton」ではなく、今はまず **証明状態の遷移図を Lean theorem として固定する automaton** が良いです。これなら既存の `FailureResolution`, `BeamSeed`, `PulseBox`, `NeighborCandidate`, `AdjacentDiagnosis` がそのまま状態ノードになります。

---

軽く、状態名を定義していく。それらのどれかに落ちる。が、解るように成れば網羅しやすい。
最終的に欲しいのはニーモニック表。全状態ビットに対する命名。のような。

---

## Review

-

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
index 21d932bc..9a8b652a 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
@@ -522,6 +522,83 @@ theorem sourcePressureBeamNeighborCandidate_right_center_full_diagnostic
   sourcePressureBeamPulse_witness_singleton_full_diagnostic_at_center
     (sourcePressureBeamNeighborCandidate_right_mem hneigh)

+/--
+Forward-oriented Beam surface for an explicit adjacent-pair diagnosis.
+
+The orientation data is part of the input:
+
+* `hin` says that `W` is immediately before `W'` in `L`;
+* `hdiag` is the existing adjacent diagnosis for that ordered pair.
+
+The theorem only re-exposes that ordered diagnostic together with the Beam
+neighbor candidate and the centered singleton diagnostics for both endpoints.
+It does not infer an orientation from a symmetric candidate, does not transport
+diagnostics across the pair, and does not classify the pair as repaired,
+overlapping, or globally covering anything.
+-/
+theorem sourcePressureBeamNeighborCandidate_forward_center_full_diagnostics_of_adjacentDiagnosis
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (hin : SourcePressureLocalIslandWitnessAdjacentPairInList L W W')
+    (hdiag : SourcePressureLocalIslandWitnessAdjacentDiagnosis L W W') :
+    SourcePressureBeamNeighborCandidate L W W' ∧
+      SourcePressureLocalIslandWitnessAdjacentDiagnosis L W W' ∧
+        SourcePressureBeamMassBalanceLeftInt n k r (W.val - 1) <
+          SourcePressureBeamMassBalanceRightInt n k r (W.val - 1) ∧
+          SourcePressureBeamAddressedDepthTarget L W.val ∧
+            SourcePressureBeamMassBalanceRightInt n k r W.val ≤
+              SourcePressureBeamMassBalanceLeftInt n k r W.val ∧
+              SourcePressureBeamMassBalanceLeftInt n k r (W'.val - 1) <
+                SourcePressureBeamMassBalanceRightInt n k r (W'.val - 1) ∧
+                SourcePressureBeamAddressedDepthTarget L W'.val ∧
+                  SourcePressureBeamMassBalanceRightInt n k r W'.val ≤
+                    SourcePressureBeamMassBalanceLeftInt n k r W'.val := by
+  have hneigh : SourcePressureBeamNeighborCandidate L W W' := Or.inl hin
+  have hleft :=
+    sourcePressureBeamPulse_witness_singleton_full_diagnostic_at_center
+      (sourcePressureLocalIslandWitnessAdjacentPairInList_left_mem hin)
+  have hright :=
+    sourcePressureBeamNeighborCandidate_right_center_full_diagnostic hneigh
+  exact ⟨hneigh, hdiag, hleft.1, hleft.2.1, hleft.2.2, hright⟩
+
+/--
+Reverse-oriented Beam surface for an explicit adjacent-pair diagnosis.
+
+This is the symmetric orientation case for a neighbor candidate stated as
+`SourcePressureBeamNeighborCandidate L W W'`: the actual ordered adjacent pair
+is `W'` before `W`, and the adjacent diagnosis is kept in that orientation.
+
+As in the forward theorem, this is only a packaging bridge.  It does not infer
+orientation from a box or from the symmetric candidate alone, and it does not
+claim transport, propagation, repair, aggregation, or convergence.
+-/
+theorem sourcePressureBeamNeighborCandidate_reverse_center_full_diagnostics_of_adjacentDiagnosis
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (hin : SourcePressureLocalIslandWitnessAdjacentPairInList L W' W)
+    (hdiag : SourcePressureLocalIslandWitnessAdjacentDiagnosis L W' W) :
+    SourcePressureBeamNeighborCandidate L W W' ∧
+      SourcePressureLocalIslandWitnessAdjacentDiagnosis L W' W ∧
+        SourcePressureBeamMassBalanceLeftInt n k r (W.val - 1) <
+          SourcePressureBeamMassBalanceRightInt n k r (W.val - 1) ∧
+          SourcePressureBeamAddressedDepthTarget L W.val ∧
+            SourcePressureBeamMassBalanceRightInt n k r W.val ≤
+              SourcePressureBeamMassBalanceLeftInt n k r W.val ∧
+              SourcePressureBeamMassBalanceLeftInt n k r (W'.val - 1) <
+                SourcePressureBeamMassBalanceRightInt n k r (W'.val - 1) ∧
+                SourcePressureBeamAddressedDepthTarget L W'.val ∧
+                  SourcePressureBeamMassBalanceRightInt n k r W'.val ≤
+                    SourcePressureBeamMassBalanceLeftInt n k r W'.val := by
+  have hneigh : SourcePressureBeamNeighborCandidate L W W' := Or.inr hin
+  have hleft :=
+    sourcePressureBeamPulse_witness_singleton_full_diagnostic_at_center
+      (sourcePressureLocalIslandWitnessAdjacentPairInList_right_mem hin)
+  have hright :=
+    sourcePressureBeamNeighborCandidate_right_center_full_diagnostic hneigh
+  exact ⟨hneigh, hdiag, hleft.1, hleft.2.1, hleft.2.2, hright⟩
+
 /--
 A Beam seed exposes one witness whose centered pulse is inside the finite
 local pulse box.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-242.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-242.md
new file mode 100644
index 00000000..5e451f78
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-242.md
@@ -0,0 +1,189 @@
+# Report: petal-242
+
+## Branch
+
+Continued from the petal-241 next-branch prediction.
+
+Taken branch:
+
+- Beam-facing oriented adjacent-pair diagnostics.
+
+The implementation stays in `PressureBeam/Pulse.lean` because the new theorems
+are Beam-facing wrappers over existing lower adjacent-diagnosis carriers.
+
+## Implemented Theorems
+
+File:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
+```
+
+Added:
+
+```lean
+theorem sourcePressureBeamNeighborCandidate_forward_center_full_diagnostics_of_adjacentDiagnosis
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (hin : SourcePressureLocalIslandWitnessAdjacentPairInList L W W')
+    (hdiag : SourcePressureLocalIslandWitnessAdjacentDiagnosis L W W') :
+    SourcePressureBeamNeighborCandidate L W W' ∧
+      SourcePressureLocalIslandWitnessAdjacentDiagnosis L W W' ∧
+        SourcePressureBeamMassBalanceLeftInt n k r (W.val - 1) <
+          SourcePressureBeamMassBalanceRightInt n k r (W.val - 1) ∧
+          SourcePressureBeamAddressedDepthTarget L W.val ∧
+            SourcePressureBeamMassBalanceRightInt n k r W.val ≤
+              SourcePressureBeamMassBalanceLeftInt n k r W.val ∧
+              SourcePressureBeamMassBalanceLeftInt n k r (W'.val - 1) <
+                SourcePressureBeamMassBalanceRightInt n k r (W'.val - 1) ∧
+                SourcePressureBeamAddressedDepthTarget L W'.val ∧
+                  SourcePressureBeamMassBalanceRightInt n k r W'.val ≤
+                    SourcePressureBeamMassBalanceLeftInt n k r W'.val
+```
+
+```lean
+theorem sourcePressureBeamNeighborCandidate_reverse_center_full_diagnostics_of_adjacentDiagnosis
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (hin : SourcePressureLocalIslandWitnessAdjacentPairInList L W' W)
+    (hdiag : SourcePressureLocalIslandWitnessAdjacentDiagnosis L W' W) :
+    SourcePressureBeamNeighborCandidate L W W' ∧
+      SourcePressureLocalIslandWitnessAdjacentDiagnosis L W' W ∧
+        SourcePressureBeamMassBalanceLeftInt n k r (W.val - 1) <
+          SourcePressureBeamMassBalanceRightInt n k r (W.val - 1) ∧
+          SourcePressureBeamAddressedDepthTarget L W.val ∧
+            SourcePressureBeamMassBalanceRightInt n k r W.val ≤
+              SourcePressureBeamMassBalanceLeftInt n k r W.val ∧
+              SourcePressureBeamMassBalanceLeftInt n k r (W'.val - 1) <
+                SourcePressureBeamMassBalanceRightInt n k r (W'.val - 1) ∧
+                SourcePressureBeamAddressedDepthTarget L W'.val ∧
+                  SourcePressureBeamMassBalanceRightInt n k r W'.val ≤
+                    SourcePressureBeamMassBalanceLeftInt n k r W'.val
+```
+
+## Meaning
+
+The cp241 theorem gave:
+
+```text
+SourcePressureBeamNeighborCandidate L W W'
+  -> W' centered singleton diagnostic
+```
+
+This checkpoint adds the orientation-aware version:
+
+```text
+AdjacentPairInList L W W'
+  + AdjacentDiagnosis L W W'
+  -> Beam neighbor candidate
+  -> centered diagnostics for both W and W'
+  -> same oriented adjacent diagnosis is preserved
+```
+
+and the reverse case:
+
+```text
+AdjacentPairInList L W' W
+  + AdjacentDiagnosis L W' W
+  -> Beam neighbor candidate for W,W'
+  -> centered diagnostics for both W and W'
+  -> same reverse-oriented adjacent diagnosis is preserved
+```
+
+The point is that the symmetric Beam candidate is not used to guess an
+orientation.  The caller supplies the orientation by giving the ordered
+adjacent-pair address and the ordered adjacent diagnosis.
+
+## Classification
+
+Core:
+
+- The explicit ordered adjacent-pair evidence is retained.
+- The existing adjacent diagnosis is retained in its original orientation.
+
+True Beam:
+
+- Both endpoints expose their centered entry comparison at `val - 1`.
+
+Boundary:
+
+- The orientation is an input boundary condition.
+- The symmetric `SourcePressureBeamNeighborCandidate` is only reconstructed
+  from the supplied orientation.
+
+False Beam:
+
+- Both endpoints expose their centered exit comparison at `val`.
+
+Gap:
+
+- The theorem still does not classify the ordered diagnosis branch as recovered
+  or overlap.
+- It does not repair overlap, transport diagnostics, aggregate witnesses,
+  choose a canonical pair, prove coverage, or imply Collatz convergence.
+
+## Next Branch Prediction
+
+The next useful branch is probably a small elimination wrapper:
+
+```text
+Beam oriented neighbor diagnostic
+  -> recovered branch evidence
+   ∨ overlap obstruction evidence
+```
+
+However, this should be added only if a caller starts destructing
+`SourcePressureLocalIslandWitnessAdjacentDiagnosis` repeatedly.  For now, the
+current surface is deliberately conservative: it preserves the ordered
+diagnosis carrier without opening it.
+
+The automaton/failure-resolution branch remains useful later:
+
+```text
+SourcePressureFailureResolution L
+  -> exists ordered adjacent pair A B
+  -> Beam-facing oriented adjacent diagnostic surface
+```
+
+That branch should wait until a caller actually wants to enter from
+`SourcePressureFailureResolution`.
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
+lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
+lake build DkMath.Collatz.PetalBridge.PressureBeam
+lake build DkMath.Collatz.PetalBridge
+```
+
+No-sorry check over inspected pressure files:
+
+```text
+rg -n "sorry|admit" \
+  PressureBeam/Pulse.lean \
+  PressureBeam/Core.lean \
+  PressureAdjacentDiagnosis.lean \
+  PressureLocalWitnessObstruction.lean \
+  PressureDiagnosticDecomposition.lean \
+  PressureAutomaton.lean
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
