# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam.Pulse

gch: c737688b34ac8be88009d2fd4471cf96efdf73d8

## Report

cp228 完了です。

[Pulse.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean) に Branch A の identity-preserving theorem を 2 本追加しました。

```lean
sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_left
sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_right
```

内容はそれぞれ:

```text
AdjacentPairInList L A B -> full diagnostic for A
AdjacentPairInList L A B -> full diagnostic for B
```

 recovered branch が持つ `A B` の witness identity を潰さず、`AdjacentPairInList` から `A ∈ L` / `B ∈ L` を復元して cp226 の full diagnostic に渡しています。coverage、canonical selection、aggregation、overlap repair は入れていません。

レポートも追加しました。

[report-petal-228.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-228.md)

確認済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
rg -n "sorry|admit" ...PressureBeam + inspected pressure files
git diff --check
```

すべて通過。既知の unrelated warning は `ZsigmondyCyclotomicResearch.lean` の `sorry` のみです。

## Review

## 結論

**採用** じゃ。
cp228 は、分岐 Goal 戦略がちゃんと効いた checkpoint になっている。

今回取った Branch は **Branch A**。

```text id="b3y6du"
AdjacentPairInList L A B
  -> full diagnostic for A

AdjacentPairInList L A B
  -> full diagnostic for B
```

を、それぞれ identity-preserving theorem として追加している。

```lean id="srtq9w"
sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_left
sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_right
```

これは良い。
cp227 の existential diagnostic は「どこかの W」を返していたが、cp228 は recovered adjacent-pair branch の `A` / `B` という witness identity を潰さずに保持した。戦略の質が一段上がっている。

## 実装レビュー

実装の意味は明確じゃ。

左側 theorem は、

```text id="5p0u68"
SourcePressureLocalIslandWitnessAdjacentPairInList L A B
  -> A ∈ L
  -> full diagnostic for A
```

右側 theorem は、

```text id="tx6a2n"
SourcePressureLocalIslandWitnessAdjacentPairInList L A B
  -> B ∈ L
  -> full diagnostic for B
```

を行っている。

どちらも `sourcePressureBeamPulse_witness_singleton_full_diagnostic` を使っているので、entry / depth / exit の証明を再構築していない。これは正しい。

## 小さな改善候補

実装上、`A ∈ L` と `B ∈ L` の取り出しを、それぞれ induction で直接書いている。

これは通っているので問題ではない。
ただし、今後同じ形を使うなら、次のような小さな projection theorem を切り出す価値がある。

```lean id="zt66nn"
sourcePressureLocalIslandWitnessAdjacentPairInList_left_mem
sourcePressureLocalIslandWitnessAdjacentPairInList_right_mem
```

これは `PressureBeam.Pulse` に置くより、可能なら `AdjacentPairInList` を定義している低位モジュール側に置くのが自然じゃ。
ただし、低位モジュール編集を避けたいなら、Pulse 側に private/local helper 的に置く判断もあり得る。

次回の分岐 Goal に入れる価値がある。

## 戦略評価

今回の report は良い。
Branch A を取り、Branch B / C / D / E を検討したうえで、

```text id="byo1ld"
Overlap obstruction still lacks a compact Beam-facing branch-specific
membership projection.
```

まで Gap を細分化できている。

これは、前回までの単発 Goal より明らかに良くなっている。

```text id="xg1amj"
generic existential diagnostic
  -> recovered adjacent pair の A/B identity
  -> 次は overlap obstruction の witness projection
```

という進軍線が見えている。

## True Beam / Boundary / False Beam / Gap

## True Beam

今回の True Beam はこれ。

```text id="8x91n6"
AdjacentPairInList L A B
  -> full diagnostic for A
```

```text id="qnoqny"
AdjacentPairInList L A B
  -> full diagnostic for B
```

つまり、recovered adjacent-pair branch が持つ両 witness を、どちらも singleton pulse diagnostic に接続できた。

## Boundary

これは local address consumer theorem。
`AdjacentPairInList L A B` が与えられている場合だけ、A/B の identity を保つ。

```text id="z7caku"
supplied adjacent pair only
```

という境界が守られている。

## False Beam

今回は否定 theorem なし。
無理に obstruction を追加していないのは正しい。

## Gap

残る Gap は overlap branch。

```text id="b5xo78"
SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
  -> ∃ W ∈ L, W has full singleton diagnostic
```

または、より branch identity を保つなら、

```text id="8w7uet"
overlap obstruction
  -> obstructing adjacent pair A B
  -> full diagnostic for A or B
```

じゃ。

ただし、overlap obstruction が再帰的・存在的なら、まずは existential 版が安全。

## 次の checkpoint 方針

次は **Branch B: overlap obstruction witness projection** を攻めるのが自然じゃ。
ただし、その前に **Branch 0: AdjacentPairInList membership projection を切り出すか** も同時に検討したい。

理由は、cp228 の 2 theorem がどちらも同じ induction を持っているからじゃ。
次に overlap でも adjacent pair membership を使うなら、helper 化で proof noise が減る。

## 次の Codex 指示

```text id="wu5825"
Checkpoint: petal-229

Primary Goal:
  Refine the cp228 branch-specific diagnostic work by investigating the overlap
  obstruction branch, while also checking whether adjacent-pair membership
  projections should be factored out.

Context:
  cp228 added identity-preserving recovered adjacent-pair diagnostics:

    AdjacentPairInList L A B -> full diagnostic for A
    AdjacentPairInList L A B -> full diagnostic for B

  The remaining branch-specific Gap is the overlap obstruction branch.

Strategic Branch Goals:

  Branch 0: reusable adjacent-pair membership projections
    Inspect the definition of:

      SourcePressureLocalIslandWitnessAdjacentPairInList L A B

    If there are no existing projections for:

      A ∈ L
      B ∈ L

    and the projections are reusable, add small helper theorem(s), preferably in
    the module that defines `AdjacentPairInList`.

    Candidate names:

      sourcePressureLocalIslandWitnessAdjacentPairInList_left_mem
      sourcePressureLocalIslandWitnessAdjacentPairInList_right_mem

    If editing the lower module would create dependency or scope issues, keep
    the helpers in the smallest safe Beam-facing module or add no helper and
    report why.

    Do not change public theorem statements from cp228 unless the refactor is
    purely mechanical and build-safe.

  Branch A: overlap obstruction exposes an adjacent pair
    Inspect:

      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L

    If it exposes an adjacent pair A B with:

      SourcePressureLocalIslandWitnessAdjacentPairInList L A B

    then add an existential theorem:

      overlap obstruction
        -> ∃ W ∈ L, full singleton diagnostic for W

    Prefer using the adjacent-pair left diagnostic unless the structure clearly
    prefers the right side.

    Do not claim canonical selection.  The theorem is existential.

  Branch B: overlap obstruction exposes left/right identity clearly
    If the overlap branch preserves named A/B identities cleanly, and theorem
    statements remain small, add at most one identity-preserving theorem:

      overlap branch -> full diagnostic for A

    or

      overlap branch -> full diagnostic for B

    Add both only if both are equally direct and useful.

  Branch C: overlap obstruction only gives recursive existence
    If the overlap predicate is recursive and does not expose a stable named
    adjacent pair at the public surface, do not force identity preservation.

    Add no Lean code unless an existential theorem is direct.
    Report the exact recursive hiding point.

  Branch D: overlap branch already feeds seed/failureResolution existential
    If the only clean route is still:

      overlap obstruction
        -> failure resolution / seed
        -> ∃ W full diagnostic

    then add no duplicate theorem.
    Report that cp227 already covers the existential surface.

  Branch E: obstruction or contradiction found
    If a proposed overlap-side witness cannot feed the singleton diagnostic or
    lacks membership, record the obstruction.
    Add a negative theorem only if it is local and useful.

Implementation rules:
  Use `#check`, `#print`, and scratch lemmas.
  Let the workspace choose the branch.
  Add no more than two small theorems.
  Prefer reusable membership projections or one existential overlap theorem.
  Stop if the theorem statement becomes large or duplicates cp227/cp228.

Files to inspect:
  DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
  DkMath/Collatz/PetalBridge/PressureBeam/Core.lean
  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
  DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
  DkMath/Collatz/PetalBridge/PressureAutomaton.lean

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
  Do not make lower diagnostic modules import PressureBeam.
  If a lower helper is added, it must not depend on Beam vocabulary.
  Beam-facing diagnostic bridges should remain in PressureBeam/Pulse.lean or a
  higher Beam-facing module.

Report requirements:
  - State which Branch was taken.
  - State which branches were inspected but not taken.
  - If helper projections were added, explain where and why.
  - If overlap theorem was added, identify whether it is existential or
    identity-preserving.
  - If no theorem was added, identify the precise missing relation.
  - Classify results as True Beam / Boundary / False Beam / Gap.
  - Predict the next branch to attack.
  - Confirm no dependency inversion.
  - Confirm no coverage, aggregation, overlap repair, or canonical selection.

Verification:
  lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
  lake build DkMath.Collatz.PetalBridge.PressureBeam
  lake build DkMath.Collatz.PetalBridge
  no-sorry grep over PressureBeam split files and inspected pressure files
  git diff --check
```

## 一歩先ゆく推論

次の分岐は、おそらくこうなる。

```text id="eu9465"
Branch 0 が通る:
  AdjacentPairInList -> A ∈ L / B ∈ L が helper 化される
  -> cp228 theorem が将来短くなる
  -> overlap branch theorem でも使える
```

または、

```text id="yjz689"
Branch A が通る:
  overlap obstruction -> ∃ W ∈ L, full diagnostic
  -> failureResolution の overlap 側にも診断 witness が立つ
```

もし、

```text id="vlzu5v"
Branch C:
  overlap obstruction が recursive で identity を隠す
```

なら、それはそれで収穫じゃ。
その場合、次は overlap obstruction 用の public projection API を低位 module に作るかどうかを判断する。

## 総合判断

cp228 は成功。
しかも戦略的に良い。

今回、recovered adjacent pair の両側 `A` / `B` を identity-preserving に保持できた。
次は overlap branch。
ただし、その前に membership projection helper を調べる。

これが次の布陣じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
index 36d77a15..fa72bfcd 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
@@ -282,5 +282,97 @@ theorem exists_sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_fail
                   (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) := by
   exact exists_sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_seed h

+/--
+An addressed adjacent pair preserves the left witness identity for the full
+local singleton diagnostic.
+
+This is the cp228 Branch A left-side bridge.  The recovered branch of
+`SourcePressureFailureResolution` exposes an adjacent pair `A B` through
+`SourcePressureLocalIslandWitnessAdjacentPairInList L A B`; this theorem keeps
+the left witness `A` rather than collapsing immediately to an arbitrary
+existential witness.
+
+The proof only extracts `A ∈ L` from the adjacent-pair address and then applies
+`sourcePressureBeamPulse_witness_singleton_full_diagnostic`.  It does not
+select a canonical pair, aggregate over pairs, or claim coverage.
+-/
+theorem sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_left
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {A B : SourcePressureLocalIslandWitness n k r}
+    (hin : SourcePressureLocalIslandWitnessAdjacentPairInList L A B) :
+    SourcePressureBeamMassBalanceLeftInt n k r
+        ((sourcePressureIntervalPulseAddress_of_localIslandWitness A).start - 1) <
+      SourcePressureBeamMassBalanceRightInt n k r
+        ((sourcePressureIntervalPulseAddress_of_localIslandWitness A).start - 1) ∧
+      SourcePressureBeamAddressedDepthTarget L
+        ((sourcePressureIntervalPulseAddress_of_localIslandWitness A).start +
+          (sourcePressureIntervalPulseAddress_of_localIslandWitness A).len - 1) ∧
+        SourcePressureBeamMassBalanceRightInt n k r
+          ((sourcePressureIntervalPulseAddress_of_localIslandWitness A).start +
+            (sourcePressureIntervalPulseAddress_of_localIslandWitness A).len - 1) ≤
+          SourcePressureBeamMassBalanceLeftInt n k r
+            ((sourcePressureIntervalPulseAddress_of_localIslandWitness A).start +
+              (sourcePressureIntervalPulseAddress_of_localIslandWitness A).len - 1) := by
+  have hmem : A ∈ L := by
+    induction L generalizing A B with
+    | nil =>
+        exact False.elim hin
+    | cons W1 rest ih =>
+        cases rest with
+        | nil =>
+            exact False.elim hin
+        | cons W2 rest =>
+            rcases hin with hhead | htail
+            · rcases hhead with ⟨hA, _hB⟩
+              simp [hA]
+            · exact List.mem_cons_of_mem W1 (ih htail)
+  exact sourcePressureBeamPulse_witness_singleton_full_diagnostic hmem
+
+/--
+An addressed adjacent pair preserves the right witness identity for the full
+local singleton diagnostic.
+
+This is the cp228 Branch A right-side bridge.  It is symmetric in spirit to
+the left-side bridge, but it is kept as a separate theorem because downstream
+recovered-pair callers may care whether the diagnostic came from `A` or `B`.
+
+The theorem only extracts `B ∈ L` from the adjacent-pair address and applies
+the existing singleton full diagnostic.  It does not prefer this side globally
+or assert that both sides cover a larger interval.
+-/
+theorem sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_right
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {A B : SourcePressureLocalIslandWitness n k r}
+    (hin : SourcePressureLocalIslandWitnessAdjacentPairInList L A B) :
+    SourcePressureBeamMassBalanceLeftInt n k r
+        ((sourcePressureIntervalPulseAddress_of_localIslandWitness B).start - 1) <
+      SourcePressureBeamMassBalanceRightInt n k r
+        ((sourcePressureIntervalPulseAddress_of_localIslandWitness B).start - 1) ∧
+      SourcePressureBeamAddressedDepthTarget L
+        ((sourcePressureIntervalPulseAddress_of_localIslandWitness B).start +
+          (sourcePressureIntervalPulseAddress_of_localIslandWitness B).len - 1) ∧
+        SourcePressureBeamMassBalanceRightInt n k r
+          ((sourcePressureIntervalPulseAddress_of_localIslandWitness B).start +
+            (sourcePressureIntervalPulseAddress_of_localIslandWitness B).len - 1) ≤
+          SourcePressureBeamMassBalanceLeftInt n k r
+            ((sourcePressureIntervalPulseAddress_of_localIslandWitness B).start +
+              (sourcePressureIntervalPulseAddress_of_localIslandWitness B).len - 1) := by
+  have hmem : B ∈ L := by
+    induction L generalizing A B with
+    | nil =>
+        exact False.elim hin
+    | cons W1 rest ih =>
+        cases rest with
+        | nil =>
+            exact False.elim hin
+        | cons W2 rest =>
+            rcases hin with hhead | htail
+            · rcases hhead with ⟨_hA, hB⟩
+              simp [hB]
+            · exact List.mem_cons_of_mem W1 (ih htail)
+  exact sourcePressureBeamPulse_witness_singleton_full_diagnostic hmem
+

 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-228.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-228.md
new file mode 100644
index 00000000..d23f87a6
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-228.md
@@ -0,0 +1,218 @@
+# report-petal-228
+
+## Checkpoint
+
+`petal-228`
+
+## Goal
+
+Refine the cp227 existential diagnostic by checking whether
+`SourcePressureFailureResolution L` can preserve branch-specific witness
+identity.
+
+cp227 already had:
+
+```text
+SourcePressureFailureResolution L
+  -> exists W in L
+       such that W's singleton pulse has the full local diagnostic
+```
+
+cp228 asks whether the branch source can be kept visible.
+
+## Branch Taken
+
+Branch A was taken.
+
+The recovered branch exposes:
+
+```lean
+∃ A B,
+  SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+    SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic A B
+```
+
+The useful identity carrier is the adjacent-pair address:
+
+```lean
+SourcePressureLocalIslandWitnessAdjacentPairInList L A B
+```
+
+It preserves the names `A` and `B`.  From that address, the Pulse layer can
+recover both memberships:
+
+```lean
+A ∈ L
+B ∈ L
+```
+
+and then apply:
+
+```lean
+sourcePressureBeamPulse_witness_singleton_full_diagnostic
+```
+
+## Added Theorems
+
+Added in `DkMath.Collatz.PetalBridge.PressureBeam.Pulse`:
+
+```lean
+theorem sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_left
+```
+
+This preserves the left recovered-pair witness identity:
+
+```text
+AdjacentPairInList L A B
+  -> full local singleton diagnostic for A
+```
+
+Also added:
+
+```lean
+theorem sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_right
+```
+
+This preserves the right recovered-pair witness identity:
+
+```text
+AdjacentPairInList L A B
+  -> full local singleton diagnostic for B
+```
+
+Both theorems are local address consumers.  They do not use the recovered
+budget diagnostic itself; they use the adjacent-pair address carried by that
+branch.  This keeps the proof surface small and avoids duplicating recovered
+diagnostic data.
+
+## Branches Inspected But Not Taken
+
+Branch B:
+
+- The overlap obstruction branch is recursive over neighboring pairs.
+- It can produce existence through the existing seed/failure-resolution route,
+  but preserving a specific overlap-side witness identity would require a
+  branch-specific overlap-address projection.
+- That projection was not added here because cp228 already used its two-theorem
+  budget on the clearer recovered-pair left/right identities.
+
+Branch C:
+
+- Both branches can eventually expose witnesses existentially.
+- Only the recovered adjacent-pair branch currently exposes clean named
+  identities `A` and `B` at the theorem surface.
+
+Branch D:
+
+- Not taken for the recovered branch: identity is not hidden there.
+- Partially applies to overlap: the current overlap predicate exposes a
+  recursive obstruction, but not a named public `W ∈ L` projection in the Beam
+  Pulse layer.
+
+Branch E:
+
+- No obstruction or contradiction was found.  Both `A` and `B` can feed the
+  singleton diagnostic once membership is extracted.
+
+## Classification
+
+True Beam:
+
+- Recovered adjacent-pair left witness identity is preserved.
+- Recovered adjacent-pair right witness identity is preserved.
+- Both sides feed the same full local singleton diagnostic without canonical
+  selection.
+
+Boundary:
+
+- These theorems are address-local.  They only consume one supplied
+  `AdjacentPairInList L A B`.
+
+False Beam:
+
+- None added.  No negative theorem was needed.
+
+Gap:
+
+- Overlap obstruction still lacks a compact Beam-facing branch-specific
+  membership projection.
+- A future theorem could target:
+
+```text
+SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
+  -> exists W in L
+       such that W is one side of the obstructing adjacent pair
+       and W has the full singleton diagnostic
+```
+
+This should stay existential unless a caller needs left/right overlap identity.
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
+- propagation;
+- Collatz convergence.
+
+## Dependency Direction
+
+No dependency inversion was introduced.
+
+The new theorems were placed in:
+
+```text
+DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
+```
+
+No lower diagnostic or automaton module imports `PressureBeam`.
+
+## Verification
+
+Commands run from `lean/dk_math`:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
+lake build DkMath.Collatz.PetalBridge.PressureBeam
+lake build DkMath.Collatz.PetalBridge
+```
+
+All builds completed successfully.
+
+Additional checks from repository root:
+
+```text
+rg -n "sorry|admit" lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam \
+  lean/dk_math/DkMath/Collatz/PetalBridge/PressureAutomaton.lean \
+  lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean \
+  lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean \
+  lean/dk_math/DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
+```
+
+No matches were found.
+
+Known unrelated warning observed during builds:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
+
+## Next Branch To Attack
+
+The next natural branch is the overlap obstruction witness projection:
+
+```text
+overlap obstruction
+  -> exists adjacent obstructing pair
+  -> choose one named side locally
+  -> full singleton diagnostic for that side
+```
+
+The safest version is existential.  A left/right-specific overlap API should
+wait until a caller needs that exact identity.
````
`````
