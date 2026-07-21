# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam.Pulse

gch: 9a430585a7995ee1161f7eb54c8db19ff85f1224

## Report

cp240 完了です。

`PressureBeam/Pulse.lean` に、明示的な隣接関係だけを包む Beam-facing surface を追加しました。

追加:

- `SourcePressureBeamNeighborCandidate`
- `SourcePressureBeamCenteredLocalPulseBox.signs_of_neighborCandidate`

重要点として、`SourcePressureBeamCenteredLocalPulseBox` から neighbor を作っていません。neighbor はあくまで `SourcePressureLocalIslandWitnessAdjacentPairInList` 由来の明示的 list adjacency です。box はその witness の局所診断を運ぶだけ、という役割分担を維持しています。

レポート:
[report-petal-240.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-240.md)

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse`
- `lake build DkMath.Collatz.PetalBridge.PressureBeam`
- `lake build DkMath.Collatz.PetalBridge`
- no-sorry grep 対象範囲一致なし
- `git diff --check`

すべて通過しています。

## Review

## 結論

**採用。これは安全に Beam へ橋を伸ばした一手じゃ。**

cp240 は、`SourcePressureBeamCenteredLocalPulseBox` から neighbor を勝手に生成せず、明示的な list adjacency だけを Beam-facing な名前で包んだ。ここが重要じゃ。

追加はこの 2 つ。

```lean id="ap1gn0"
SourcePressureBeamNeighborCandidate
```

```lean id="fg0m5r"
SourcePressureBeamCenteredLocalPulseBox.signs_of_neighborCandidate
```

`NeighborCandidate` は、

```lean id="j6cvx7"
SourcePressureLocalIslandWitnessAdjacentPairInList L W W' ∨
  SourcePressureLocalIslandWitnessAdjacentPairInList L W' W
```

という対称 wrapper。
つまり、

```text id="i7bpf1"
box が neighbor を作るのではない
neighbor は明示的な list adjacency から来る
box は W の局所診断を運ぶだけ
```

という役割分担が守られている。

## 実装レビュー

これは良い薄さじゃ。

`SourcePressureBeamNeighborCandidate` は、既存の `SourcePressureLocalIslandWitnessAdjacentPairInList` を Beam 側から読みやすくする名前であり、まだ transport / propagation / coverage を主張していない。

`signs_of_neighborCandidate` も、

```text id="bqt1no"
boxed local pulse for W
+
explicit neighbor candidate W'
```

から、

```text id="capxxl"
neighbor candidate unchanged
+
W の sign/target facts
```

を返すだけ。
`W'` が pulse box を持つとも、transport が成功するとも言っていない。ここは非常に安全。

## 数学的意味

cp238 で局所 pulse box ができた。

```text id="ks6s2n"
W:
  sign + height + jump を持つ boxed local pulse
```

cp240 で、その `W` に対して、別 witness `W'` が list 上で隣接する、という Beam-facing な関係名ができた。

```text id="byblj7"
W --neighbor-- W'
```

ただし、これはまだ「伝播」ではない。
これは **隣接候補を明示的に持った状態で、W の局所診断を使えるようにした** だけじゃ。

DkMath 語彙で言えば、

```text id="mu8np8"
Core:
  explicit adjacent-pair relation

True Beam:
  boxed pulse と neighbor candidate を同時に持てる

Boundary:
  neighbor は list 構造由来

False Beam:
  box 単体から neighbor は出ない

Gap:
  neighbor candidate から adjacent-pair diagnostics / failure-resolution へ繋ぐ橋
```

## 次に狙うべきところ

次の本命は、`NeighborCandidate` から **隣接 witness の membership / centered diagnostic** を取り出すことじゃ。

なぜなら `NeighborCandidate L W W'` は `Or` なので、向きが二通りある。

```text id="ga8vpg"
W  before W'
W' before W
```

しかし、どちらの場合でも、`W' ∈ L` は取れるはず。
そして `W' ∈ L` が取れれば、cp234 の centered diagnostic theorem を使って、`W'` 側の centered diagnostic も得られる。

つまり次は、

```text id="grnq25"
neighbor candidate
  -> W' ∈ L
  -> centered full diagnostic for W'
```

が安全な橋じゃ。

これは propagation ではない。
ただし、**隣接候補もまた診断可能な witness である** ことを出す。

## 次の Codex 指示

```text id="q0osg5"
Checkpoint: petal-241

Primary Goal:
  Connect `SourcePressureBeamNeighborCandidate` to membership and centered
  diagnostics for the neighboring witness `W'`.

Context:
  cp240 added:

    SourcePressureBeamNeighborCandidate L W W'

  defined as explicit symmetric adjacency:

    AdjacentPairInList L W W' ∨ AdjacentPairInList L W' W

  and added:

    SourcePressureBeamCenteredLocalPulseBox.signs_of_neighborCandidate

  This still does not infer a neighbor from a box.  The neighbor candidate must
  be supplied explicitly from list adjacency.

  The next safe bridge is:
    neighbor candidate -> W' ∈ L
    neighbor candidate -> centered diagnostic for W'

Strategic Branch Goals:

  Branch A: membership projections
    Add small theorems in `PressureBeam/Pulse.lean` or the smallest appropriate
    Beam-facing module:

      theorem sourcePressureBeamNeighborCandidate_left_mem
          {L : List (SourcePressureLocalIslandWitness n k r)}
          {W W' : SourcePressureLocalIslandWitness n k r}
          (hneigh : SourcePressureBeamNeighborCandidate L W W') :
          W ∈ L

      theorem sourcePressureBeamNeighborCandidate_right_mem
          {L : List (SourcePressureLocalIslandWitness n k r)}
          {W W' : SourcePressureLocalIslandWitness n k r}
          (hneigh : SourcePressureBeamNeighborCandidate L W W') :
          W' ∈ L

    These should split on the `Or` and use existing adjacent-pair membership
    lemmas, likely:
      sourcePressureLocalIslandWitnessAdjacentPairInList_left_mem
      sourcePressureLocalIslandWitnessAdjacentPairInList_right_mem

    If exact names differ, inspect with #check/#print.

  Branch B: centered diagnostic for neighbor
    If Branch A succeeds, add one theorem:

      theorem sourcePressureBeamNeighborCandidate_right_center_full_diagnostic
          {L : List (SourcePressureLocalIslandWitness n k r)}
          {W W' : SourcePressureLocalIslandWitness n k r}
          (hneigh : SourcePressureBeamNeighborCandidate L W W') :
          SourcePressureBeamMassBalanceLeftInt n k r (W'.val - 1) <
            SourcePressureBeamMassBalanceRightInt n k r (W'.val - 1) ∧
          SourcePressureBeamAddressedDepthTarget L W'.val ∧
            SourcePressureBeamMassBalanceRightInt n k r W'.val ≤
              SourcePressureBeamMassBalanceLeftInt n k r W'.val

    This should consume:
      sourcePressureBeamNeighborCandidate_right_mem
      sourcePressureBeamPulse_witness_singleton_full_diagnostic_at_center

    Do not claim `W'` has a local pulse box.
    Do not claim transport succeeds.

  Branch C: centered signs for neighbor
    If a sign-level theorem is more useful and direct, add:

      theorem sourcePressureBeamNeighborCandidate_right_center_margin_signs
          ...
          SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
          0 < SourcePressureMarginInt n k (r + W'.val) ∧
          SourcePressureBeamAddressedDepthTarget L W'.val ∧
          SourcePressureMarginInt n k (r + W'.val + 1) ≤ 0

    Only add this if it is thin and uses existing centered diagnostic/sign API.

  Branch D: avoid over-API
    If adding all of the above feels too much, prioritize:
      1. right membership
      2. right centered diagnostic

    Leave sign-level or box-level wrappers for later callers.

  Branch E: oriented adjacent diagnostics are better
    If the existing adjacent-pair theorems already give better diagnostics for
    both endpoints depending on orientation, do not duplicate too much.

    Report the exact theorem chain and add only a tiny alias if useful.

Implementation rules:
  - Use #check, #print, and scratch lemmas.
  - Split on the `Or` in `SourcePressureBeamNeighborCandidate`.
  - Do not infer neighbor existence from a boxed pulse.
  - Do not assert that the neighbor has a pulse box.
  - Add no more than three small theorems.
  - Keep everything local and witness/list-relative.

Guardrails:
  Do not add:
    - propagation;
    - transport success;
    - list-wide coverage;
    - witness-family aggregation;
    - canonical witness selection;
    - arbitrary target transport;
    - overlap repair;
    - disjointness;
    - monotone trend;
    - global Big bounds;
    - Collatz convergence.

Verification:
  lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
  lake build DkMath.Collatz.PetalBridge.PressureBeam
  lake build DkMath.Collatz.PetalBridge
  no-sorry grep over inspected pressure files
  git diff --check

Report requirements:
  - State which Branch was taken.
  - Show exact theorem statements.
  - Explain that neighbor membership/diagnostic comes from explicit adjacency,
    not from the local pulse box.
  - Classify results as True Beam / Boundary / False Beam / Gap.
  - Predict whether the next branch should connect neighbor candidates to
    oriented adjacent-pair diagnostics or failure-resolution branches.
```

## 待ち構え

次に期待するのはこれ。

```text id="d8vuhj"
SourcePressureBeamNeighborCandidate L W W'
  -> W' ∈ L
  -> centered diagnostic for W'
```

これが通れば、

```text id="fzuspt"
boxed pulse W
+
neighbor candidate W'
```

から、`W` の sign/target と `W'` の centered diagnostic を同時に使えるようになる。

そこまで行ってから、初めて

```text id="dgj5yw"
W と W' の関係が recovered なのか overlap obstruction なのか
```

へ進むのが安全じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
index 222c242e..d6df30b0 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
@@ -419,6 +419,46 @@ theorem SourcePressureBeamCenteredLocalPulseBox.signs
       _hnextBox, _hentryJumpBox, _hexitJumpBox⟩
   exact ⟨hmem, hprev, hcenter, haddr, hnext⟩

+/--
+Beam-facing neighbor-candidate surface for explicit adjacent witnesses.
+
+This is only a symmetric naming wrapper around the existing list/pair address
+predicate.  It deliberately does not say that a boxed pulse produces a
+neighbor.  The neighbor candidate must come from explicit list adjacency:
+
+* either `W` is immediately before `W'` in `L`;
+* or `W'` is immediately before `W` in `L`.
+
+No propagation, transport, coverage, sorting, or overlap repair is asserted.
+-/
+def SourcePressureBeamNeighborCandidate
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (W W' : SourcePressureLocalIslandWitness n k r) : Prop :=
+  SourcePressureLocalIslandWitnessAdjacentPairInList L W W' ∨
+    SourcePressureLocalIslandWitnessAdjacentPairInList L W' W
+
+/--
+Consume a boxed local pulse together with an explicit neighbor candidate.
+
+The theorem only packages the supplied adjacency candidate with the sign and
+target facts projected from the box.  It does not assert that `W'` has a pulse
+box, that transport succeeds, or that a neighbor exists from the box alone.
+-/
+theorem SourcePressureBeamCenteredLocalPulseBox.signs_of_neighborCandidate
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (hbox : SourcePressureBeamCenteredLocalPulseBox n k r L W)
+    (hneigh : SourcePressureBeamNeighborCandidate L W W') :
+    SourcePressureBeamNeighborCandidate L W W' ∧
+      W ∈ L ∧
+        SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0 ∧
+          0 < SourcePressureMarginInt n k (r + W.val) ∧
+            SourcePressureBeamAddressedDepthTarget L W.val ∧
+              SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 :=
+  ⟨hneigh, hbox.signs⟩
+
 /--
 A Beam seed exposes one witness whose centered pulse is inside the finite
 local pulse box.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-240.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-240.md
new file mode 100644
index 00000000..33a88f9c
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-240.md
@@ -0,0 +1,169 @@
+# report-petal-240
+
+## Checkpoint
+
+`petal-240`
+
+## Summary
+
+Implemented Branch A plus the Branch C consumer surface.
+
+The new neighbor surface is intentionally explicit-adjacency based.  It does
+not infer a neighbor from a boxed local pulse.  The role split is:
+
+```text
+SourcePressureBeamCenteredLocalPulseBox
+  carries local sign/height/jump diagnostics for W
+
+SourcePressureBeamNeighborCandidate
+  carries explicit list adjacency between W and W'
+```
+
+This keeps the cp239 guardrail intact:
+
+```text
+box alone does not create a neighbor
+```
+
+## Added Predicate
+
+```lean
+def SourcePressureBeamNeighborCandidate
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (W W' : SourcePressureLocalIslandWitness n k r) : Prop :=
+  SourcePressureLocalIslandWitnessAdjacentPairInList L W W' ∨
+    SourcePressureLocalIslandWitnessAdjacentPairInList L W' W
+```
+
+Meaning:
+
+```text
+W and W' are adjacent in the explicit witness list L,
+in either order.
+```
+
+This is only a symmetric Beam-facing name for the existing list/pair adjacency
+predicate.  It does not claim transport, propagation, coverage, sorting,
+overlap repair, or convergence.
+
+## Added Consumer Theorem
+
+```lean
+theorem SourcePressureBeamCenteredLocalPulseBox.signs_of_neighborCandidate
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (hbox : SourcePressureBeamCenteredLocalPulseBox n k r L W)
+    (hneigh : SourcePressureBeamNeighborCandidate L W W') :
+    SourcePressureBeamNeighborCandidate L W W' ∧
+      W ∈ L ∧
+        SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0 ∧
+          0 < SourcePressureMarginInt n k (r + W.val) ∧
+            SourcePressureBeamAddressedDepthTarget L W.val ∧
+              SourcePressureMarginInt n k (r + W.val + 1) ≤ 0
+```
+
+This theorem consumes:
+
+```text
+boxed local pulse for W
++ explicit neighbor candidate W'
+```
+
+and returns:
+
+```text
+the neighbor candidate unchanged
++ sign/target facts for W
+```
+
+It does not assert that `W'` has a pulse box, that `W'` is reachable by
+transport, or that a neighbor exists from `hbox` alone.
+
+## Branch Notes
+
+I did not add separate left/right constructor lemmas in this checkpoint.
+The predicate is an `Or`, so callers can construct it directly with:
+
+```lean
+Or.inl hAdjacentLeft
+Or.inr hAdjacentRight
+```
+
+Keeping the first surface small leaves room for the next checkpoint to decide
+whether named constructors are actually useful at call sites.
+
+## Big / Core / Beam / Gap Classification
+
+- Core:
+  the existing `SourcePressureLocalIslandWitnessAdjacentPairInList` relation is
+  now available through a Beam-facing symmetric name.
+
+- True Beam:
+  local pulse diagnostics can now be combined with an explicitly supplied
+  neighbor candidate without unpacking unrelated box components.
+
+- Boundary:
+  the neighbor candidate is supplied by list structure.  It is not derived from
+  the pulse box.
+
+- False Beam:
+  no propagation, no transport success, no neighbor existence from one boxed
+  witness, and no statement about `W'`'s own diagnostics is proved.
+
+- Gap:
+  the next missing bridge is from neighbor candidates to adjacent-pair
+  diagnostics or failure-resolution branches.
+
+## Next Branch Prediction
+
+The next useful branch should connect:
+
+```text
+SourcePressureBeamNeighborCandidate L W W'
+```
+
+to existing adjacent-pair machinery:
+
+```text
+SourcePressureLocalIslandWitnessAdjacentDiagnosis
+SourcePressureFailureResolution
+SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+```
+
+There are two plausible directions:
+
+1. Add tiny left/right constructor aliases if caller code becomes noisy.
+2. Prove a consumer theorem:
+
+```text
+neighbor candidate
++ adjacent diagnosis on the oriented pair
+-> Beam-facing neighbor diagnostic surface
+```
+
+The second direction is more valuable if a concrete caller needs to combine
+local pulse boxes with recovered/overlap adjacent-pair diagnostics.
+
+## Verification
+
+Commands run:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
+lake build DkMath.Collatz.PetalBridge.PressureBeam
+lake build DkMath.Collatz.PetalBridge
+rg -n "sorry|admit" <inspected-pressure-file-scope>
+git diff --check
+```
+
+Results:
+
+```text
+PressureBeam.Pulse build: pass
+PressureBeam build: pass
+PetalBridge build: pass
+no-sorry grep: no matches in inspected pressure scope
+git diff --check: pass
+```
````
`````
