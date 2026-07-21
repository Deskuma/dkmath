# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam.Pulse

gch: 858ea815b63fb4ab4bcb5a80b261bb0e892431c1

## Report

cp241 実装完了です。

[PressureBeam/Pulse.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean) に以下を追加しました。

- `sourcePressureBeamNeighborCandidate_left_mem`
- `sourcePressureBeamNeighborCandidate_right_mem`
- `sourcePressureBeamNeighborCandidate_right_center_full_diagnostic`

いずれも明示された `SourcePressureBeamNeighborCandidate` の adjacency から取り出すだけで、`W` の box から `W'` を生成する主張や、`W'` の pulse box、transport/propagation は主張していません。

レポートも追加しました: [report-petal-241.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-241.md)

検証済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
```

対象 pressure files の `sorry|admit` grep は no match、`git diff --check` も通過です。

## Director

### Next Branch Prediction

The next natural branch is to connect neighbor candidates to oriented
adjacent-pair diagnostics.

Candidate shape:

```text
SourcePressureBeamNeighborCandidate L W W'
  + orientation data
  -> Beam-facing adjacent diagnostic surface for W and W'
```

If a caller wants to stay at the automaton layer instead, the alternative is a
failure-resolution branch:

```text
SourcePressureFailureResolution L
  -> exists adjacent candidate W W'
  -> neighbor-centered diagnostic for W'
```

The oriented route is probably cleaner for the current Beam work because it
keeps the local witness/list-relative contract explicit.

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
index d6df30b0..21d932bc 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
@@ -459,6 +459,69 @@ theorem SourcePressureBeamCenteredLocalPulseBox.signs_of_neighborCandidate
               SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 :=
   ⟨hneigh, hbox.signs⟩

+/--
+The left endpoint of an explicit Beam neighbor candidate is in the witness
+list.
+
+This is only an adjacency projection.  It does not infer a neighbor from a
+local pulse box, does not assert that either endpoint has a pulse box, and does
+not transport any diagnostic information.
+-/
+theorem sourcePressureBeamNeighborCandidate_left_mem
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (hneigh : SourcePressureBeamNeighborCandidate L W W') :
+    W ∈ L := by
+  rcases hneigh with hleft | hright
+  · exact sourcePressureLocalIslandWitnessAdjacentPairInList_left_mem hleft
+  · exact sourcePressureLocalIslandWitnessAdjacentPairInList_right_mem hright
+
+/--
+The right endpoint of an explicit Beam neighbor candidate is in the witness
+list.
+
+The witness `W'` is available because it is one endpoint of the supplied
+symmetric adjacent-pair evidence.  This is not derived from
+`SourcePressureBeamCenteredLocalPulseBox`, and it does not claim propagation or
+transport from `W` to `W'`.
+-/
+theorem sourcePressureBeamNeighborCandidate_right_mem
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (hneigh : SourcePressureBeamNeighborCandidate L W W') :
+    W' ∈ L := by
+  rcases hneigh with hleft | hright
+  · exact sourcePressureLocalIslandWitnessAdjacentPairInList_right_mem hleft
+  · exact sourcePressureLocalIslandWitnessAdjacentPairInList_left_mem hright
+
+/--
+An explicit Beam neighbor candidate exposes the neighboring witness's centered
+singleton diagnostic.
+
+This theorem is the safe cp241 neighbor bridge:
+
+* adjacency gives `W' ∈ L`;
+* membership lets the existing singleton theorem read the centered diagnostic
+  at `W'.val`.
+
+It deliberately does not say that `W'` has a centered local pulse box, that a
+box for `W` creates the neighbor, or that any transport/propagation succeeds.
+-/
+theorem sourcePressureBeamNeighborCandidate_right_center_full_diagnostic
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (hneigh : SourcePressureBeamNeighborCandidate L W W') :
+    SourcePressureBeamMassBalanceLeftInt n k r (W'.val - 1) <
+      SourcePressureBeamMassBalanceRightInt n k r (W'.val - 1) ∧
+      SourcePressureBeamAddressedDepthTarget L W'.val ∧
+        SourcePressureBeamMassBalanceRightInt n k r W'.val ≤
+          SourcePressureBeamMassBalanceLeftInt n k r W'.val :=
+  sourcePressureBeamPulse_witness_singleton_full_diagnostic_at_center
+    (sourcePressureBeamNeighborCandidate_right_mem hneigh)
+
 /--
 A Beam seed exposes one witness whose centered pulse is inside the finite
 local pulse box.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-241.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-241.md
new file mode 100644
index 00000000..225945f3
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-241.md
@@ -0,0 +1,180 @@
+# Report: petal-241
+
+## Branch
+
+Taken branches:
+
+- Branch A: membership projections.
+- Branch B: centered diagnostic for the neighboring witness.
+
+Branch C was intentionally left for a later caller.  The centered full
+diagnostic is the stronger and cleaner Beam-facing surface for this checkpoint.
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
+theorem sourcePressureBeamNeighborCandidate_left_mem
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (hneigh : SourcePressureBeamNeighborCandidate L W W') :
+    W ∈ L
+```
+
+```lean
+theorem sourcePressureBeamNeighborCandidate_right_mem
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (hneigh : SourcePressureBeamNeighborCandidate L W W') :
+    W' ∈ L
+```
+
+```lean
+theorem sourcePressureBeamNeighborCandidate_right_center_full_diagnostic
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (hneigh : SourcePressureBeamNeighborCandidate L W W') :
+    SourcePressureBeamMassBalanceLeftInt n k r (W'.val - 1) <
+      SourcePressureBeamMassBalanceRightInt n k r (W'.val - 1) ∧
+      SourcePressureBeamAddressedDepthTarget L W'.val ∧
+        SourcePressureBeamMassBalanceRightInt n k r W'.val ≤
+          SourcePressureBeamMassBalanceLeftInt n k r W'.val
+```
+
+## Theorem Chain
+
+The membership projections split the symmetric neighbor candidate:
+
+```lean
+SourcePressureBeamNeighborCandidate L W W'
+```
+
+into one of:
+
+```lean
+SourcePressureLocalIslandWitnessAdjacentPairInList L W W'
+SourcePressureLocalIslandWitnessAdjacentPairInList L W' W
+```
+
+Then they use the existing adjacent-pair membership lemmas:
+
+```lean
+sourcePressureLocalIslandWitnessAdjacentPairInList_left_mem
+sourcePressureLocalIslandWitnessAdjacentPairInList_right_mem
+```
+
+The centered diagnostic theorem uses:
+
+```lean
+sourcePressureBeamNeighborCandidate_right_mem
+sourcePressureBeamPulse_witness_singleton_full_diagnostic_at_center
+```
+
+So the diagnostic for `W'` comes from explicit adjacency giving `W' ∈ L`, then
+from the existing singleton diagnostic for any witness in the list.
+
+It does not come from `SourcePressureBeamCenteredLocalPulseBox`.  No theorem
+claims that a box around `W` produces a neighbor, that `W'` has its own local
+pulse box, or that any transport from `W` to `W'` succeeds.
+
+## Classification
+
+Core:
+
+- Explicit adjacency is now enough to recover both endpoint memberships.
+
+True Beam:
+
+- The neighboring witness `W'` exposes the entry mass-balance comparison at
+  `W'.val - 1`.
+
+Boundary:
+
+- The candidate itself is still an input boundary condition.  Neighbor
+  existence is not inferred from a pulse box.
+
+False Beam:
+
+- The neighboring witness `W'` exposes the exit mass-balance comparison at
+  `W'.val`.
+
+Gap:
+
+- The relation between `W` and `W'` is still not classified as recovered,
+  overlap, obstruction, or repair.
+- No propagation, transport success, coverage, aggregation, canonical
+  selection, disjointness, monotone trend, global Big bound, or Collatz
+  convergence was added.
+
+## Next Branch Prediction
+
+The next natural branch is to connect neighbor candidates to oriented
+adjacent-pair diagnostics.
+
+Candidate shape:
+
+```text
+SourcePressureBeamNeighborCandidate L W W'
+  + orientation data
+  -> Beam-facing adjacent diagnostic surface for W and W'
+```
+
+If a caller wants to stay at the automaton layer instead, the alternative is a
+failure-resolution branch:
+
+```text
+SourcePressureFailureResolution L
+  -> exists adjacent candidate W W'
+  -> neighbor-centered diagnostic for W'
+```
+
+The oriented route is probably cleaner for the current Beam work because it
+keeps the local witness/list-relative contract explicit.
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
