# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam.Pulse

gch: 37a79412c61df9be72840a8ed5cadae0174143be

## Report

cp231 完了です。

今回は caller 調査の結果、右 endpoint 専用 wrapper はまだ不要と判断しました。一方で `PressureBeam/Core.lean` に既に匿名の overlap-to-depth surface があるため、それに対応する Pulse 側の匿名 full diagnostic surface を 1 本だけ追加しました。

追加:

`PressureBeam/Pulse.lean`

```lean
exists_sourcePressureBeamPulse_witness_full_diagnostic_of_adjacentOverlapObstruction
```

これは cp230 の pair-preserving theorem を弱めるだけです。`A`, `B`, overlap obstruction を保持したい caller は cp230 の theorem を使い、単に `∃ W ∈ L` と full singleton diagnostic が欲しい caller は今回の theorem を使えます。canonical selection や coverage は主張していません。

検証済み:

- `lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis`
- `lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse`
- `lake build DkMath.Collatz.PetalBridge.PressureBeam`
- `lake build DkMath.Collatz.PetalBridge`
- no-sorry/admit scan passed
- `git diff --check` passed

`report-petal-231.md` も作成済みです。

## Review

## 結論

**採用** じゃ。
cp231 は、前回の方針どおり **caller-driven** に判断できている。

今回取った Branch は **Branch B**。

```text id="x4l3ox"
overlap obstruction
  -> ∃ W ∈ L, W has full singleton Beam diagnostic
```

右 endpoint wrapper を機械的に足さず、既存 caller 形を見たうえで、匿名 witness surface だけを追加した。これは良い判断じゃ。

## 実装レビュー

追加 theorem はこれ。

```lean id="qk3x6t"
exists_sourcePressureBeamPulse_witness_full_diagnostic_of_adjacentOverlapObstruction
```

意味は、

```text id="u8jcg2"
SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
  -> ∃ W ∈ L, full singleton Beam diagnostic for W
```

じゃ。

証明は cp230 の pair-preserving theorem を弱めるだけ。

```lean id="xfnjh8"
exists_sourcePressureBeamPulse_leftWitness_full_diagnostic_of_adjacentOverlapObstruction
```

から `A B hin hobspair hdiag` を取り出し、`A` を匿名 witness `W` として返している。

```lean id="d48a40"
⟨A, sourcePressureLocalIslandWitnessAdjacentPairInList_left_mem hin, hdiag⟩
```

この形は安全じゃ。
overlap recursion を再実行していないし、canonical selection も主張していない。
あくまで「cp230 が保存していた pair identity を、caller が不要な場合に捨てる」だけ。

## 戦略評価

今回の良い点は、右 endpoint wrapper を足さなかったことじゃ。

```text id="kp2x48"
sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_right
```

は既にある。だから、右 endpoint が必要ならいつでも wrapper は作れる。
しかし、現時点で caller が見つかっていないなら、対称性だけで API を増やさないほうがよい。

一方で、`PressureBeam/Core.lean` に既に匿名 overlap-to-depth surface があるため、それに対応する Pulse-level full diagnostic surface を作った、という判断は筋が通っている。

## True Beam / Boundary / False Beam / Gap

## True Beam

今回の True Beam はこれ。

```text id="zb6nl6"
adjacent overlap obstruction
  -> anonymous full singleton diagnostic witness
```

cp230 は pair-preserving surface。

```text id="shjjn3"
∃ A B, addressed pair ∧ pair overlap obstruction ∧ full diagnostic for A
```

cp231 は anonymous surface。

```text id="di1f79"
∃ W ∈ L, full diagnostic for W
```

これで caller が必要な粒度に応じて選べる。

## Boundary

今回の theorem は、pair identity を意図的に忘れる。
これは boundary として明確じゃ。

```text id="oslppe"
pair identity が必要:
  cp230 を使う

pair identity が不要:
  cp231 を使う
```

この切り分けができた。

## False Beam

否定 theorem はなし。
今回も obstruction の修理や否定は不要。

## Gap

残る Gap は二つ。

```text id="khkq71"
right endpoint overlap wrapper
```

```text id="byh8xu"
both-endpoint overlap diagnostic
```

どちらも caller が必要になったら足す。
今は未追加で正しい。

## 注意点

今回の theorem は「匿名 witness」と言っているが、内部的には cp230 の左 endpoint `A` を使っている。

これは問題ない。
ただし、説明としては常に、

```text id="ulxlua"
canonical selection ではない
cp230 の一つの overlap pair から左 endpoint を弱めただけ
```

を添えるのがよい。

「匿名」だからといって、全 overlap pair から自然に選ばれる代表ではない。
ここを曖昧にしないのが大事じゃ。

## 次の checkpoint 方針

次は、overlap wrapper をさらに増やすより、**現在そろった Pulse surfaces を整理して、上位から何が使えるかを見る**のがよい。

現状の public overlap surfaces はこう。

```text id="cmf3ke"
cp230:
  overlap obstruction
    -> ∃ A B,
         addressed pair
         ∧ pair overlap obstruction
         ∧ full diagnostic for A

cp231:
  overlap obstruction
    -> ∃ W ∈ L,
         full diagnostic for W
```

この二つでかなり使える。
次は `SourcePressureFailureResolution` 側の分岐と、overlap/recovered/seed の surface をまとめて比較する段階じゃ。

## 次の Codex 指示

```text id="h65bq5"
Checkpoint: petal-232

Primary Goal:
  Audit the current Beam Pulse diagnostic surfaces and decide whether the next
  theorem should connect them to a higher-level failure-resolution classifier,
  or whether the existing surfaces are sufficient.

Context:
  Recent checkpoints produced these surfaces:

  Explicit witness:
    W ∈ L
      -> full singleton diagnostic for W

  Beam seed:
    SourcePressureBeamSeed L
      -> ∃ W ∈ L, full singleton diagnostic for W

  Failure resolution:
    SourcePressureFailureResolution L
      -> ∃ W ∈ L, full singleton diagnostic for W

  Recovered adjacent pair:
    AdjacentPairInList L A B
      -> full diagnostic for A
    AdjacentPairInList L A B
      -> full diagnostic for B

  Overlap obstruction:
    overlap obstruction
      -> ∃ A B,
           AdjacentPairInList L A B
           ∧ PairOverlapObstruction A B
           ∧ full diagnostic for A

    overlap obstruction
      -> ∃ W ∈ L, full diagnostic for W

Strategic Branch Goals:

  Branch A: higher-level failure-resolution classifier can preserve branch kind
    Inspect whether `SourcePressureFailureResolution L` can be split into:

      recovered branch
      overlap branch

    and whether each branch can produce the appropriate diagnostic surface.

    If yes, add a theorem only if it preserves useful branch information.

    Candidate shape:
      failure resolution
        -> recovered diagnostic OR overlap diagnostic

    Do not force this if theorem statements become too large.

  Branch B: existing surfaces already cover caller needs
    If current seed / failureResolution / overlap / adjacent-pair surfaces are
    sufficient, add no Lean code.

    Write a report listing the public diagnostic API and the recommended usage:
      - explicit W ∈ L
      - seed
      - failureResolution
      - recovered adjacent pair
      - overlap pair-preserving
      - overlap anonymous

  Branch C: caller needs right endpoint overlap diagnostic
    If a concrete caller needs the right endpoint of an overlap pair, add the
    symmetric right wrapper.

    It should consume:
      exists_adjacentPairInList_pairOverlapObstruction_of_overlapObstruction
      sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_right

    Do not add it merely for symmetry.

  Branch D: caller needs both endpoint overlap diagnostics
    If a concrete caller needs both A and B diagnostics, add one paired theorem
    rather than two separate wrappers.

    Add this only if it clearly reduces proof noise.

  Branch E: API duplication detected
    If some theorem is now redundant with another public surface, do not remove
    it yet unless purely mechanical and safe.

    Report the duplication and recommend whether future cleanup is needed.

Implementation rules:
  Use #check, #print, and scratch lemmas.
  Inspect actual caller shapes before adding theorem surfaces.
  Add no more than one theorem.
  Prefer no-code report if current API is sufficient.
  Do not expand API for symmetry alone.

Files to inspect:
  DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
  DkMath/Collatz/PetalBridge/PressureBeam/Core.lean
  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
  DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
  DkMath/Collatz/PetalBridge/PressureAutomaton.lean
  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean

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
  Lower modules must not import Beam.
  Beam-facing theorem surfaces belong in PressureBeam/Pulse.lean or a higher
  Beam-facing module.

Report requirements:
  - State which Branch was taken.
  - State which branches were inspected but not taken.
  - If no code was added, provide a concise API map of the current diagnostic
    surfaces.
  - If code was added, identify the caller need that justified it.
  - Classify results as True Beam / Boundary / False Beam / Gap.
  - Predict the next branch to attack.
  - Confirm no dependency inversion.
  - Confirm no coverage, aggregation, overlap repair, disjointness, or
    canonical selection.

Verification if code changes:
  lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
  lake build DkMath.Collatz.PetalBridge.PressureBeam
  lake build DkMath.Collatz.PetalBridge
  no-sorry grep over inspected pressure files
  git diff --check
```

## 待ち構え

次の戻りは、たぶんこのどれかじゃ。

```text id="m2q3yj"
Branch B:
  current API is sufficient
```

この場合は、いったん Pulse diagnostic API を閉じて次の層へ移る。

```text id="frwq1k"
Branch A:
  failureResolution branch-kind preserving theorem が通る
```

この場合は、recovered/overlap の二分岐を上位 classifier として読める。

```text id="d0f2r4"
Branch C/D:
  right or both endpoint が caller で必要
```

この場合だけ wrapper を追加する。

## 総合判断

cp231 は成功。
対称 wrapper を機械的に増やさず、anonymous caller surface だけを追加した。
これは戦略が効いている。

次は、Pulse diagnostic API の棚卸しと、failure-resolution classifier へ上げる必要があるかの判断じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
index 7e88c827..2e9ebeee 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
@@ -394,5 +394,49 @@ theorem
       sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_left
         hin⟩
 
+/--
+An adjacent-overlap obstruction exposes some listed witness with the full
+singleton pulse diagnostic.
+
+This is the intentionally weaker caller surface for users that only need an
+existential pulse diagnostic and do not care which endpoint of the obstructing
+adjacent pair produced it.  It consumes the cp230 left-witness wrapper, so it
+does not re-run the overlap recursion and does not introduce a canonical
+selection principle: the witness is merely the left endpoint supplied by one
+addressed overlap pair.
+
+The stronger pair-preserving theorem remains
+`exists_sourcePressureBeamPulse_leftWitness_full_diagnostic_of_adjacentOverlapObstruction`.
+Use this weaker theorem only when preserving `A`, `B`, and the pair-overlap
+obstruction would be caller noise.
+-/
+theorem exists_sourcePressureBeamPulse_witness_full_diagnostic_of_adjacentOverlapObstruction
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hobs :
+      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
+    ∃ W : SourcePressureLocalIslandWitness n k r,
+      W ∈ L ∧
+        SourcePressureBeamMassBalanceLeftInt n k r
+            ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start - 1) <
+          SourcePressureBeamMassBalanceRightInt n k r
+            ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start - 1) ∧
+          SourcePressureBeamAddressedDepthTarget L
+            ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
+              (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) ∧
+            SourcePressureBeamMassBalanceRightInt n k r
+              ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
+                (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) ≤
+              SourcePressureBeamMassBalanceLeftInt n k r
+                ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
+                  (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) := by
+  rcases
+    exists_sourcePressureBeamPulse_leftWitness_full_diagnostic_of_adjacentOverlapObstruction
+      hobs with
+    ⟨A, B, hin, _hobspair, hdiag⟩
+  exact
+    ⟨A, sourcePressureLocalIslandWitnessAdjacentPairInList_left_mem hin,
+      hdiag⟩
+
 
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-231.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-231.md
new file mode 100644
index 00000000..9d906cd8
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-231.md
@@ -0,0 +1,193 @@
+# report-petal-231
+
+## Checkpoint
+
+`petal-231`
+
+## Goal
+
+Decide whether to add the next overlap-diagnostic surface after cp230.
+
+The key rule was: do not add symmetric or anonymous wrappers mechanically.
+Inspect actual caller shape first.
+
+## Caller Inspection
+
+The right-endpoint theorem:
+
+```lean
+sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_right
+```
+
+exists, but no current higher-level caller was found that specifically needs
+the right endpoint `B` of an overlap pair.
+
+However, `PressureBeam/Core.lean` already has an anonymous overlap-to-depth
+surface:
+
+```lean
+exists_sourcePressureBeamSeedContainsDepth_of_adjacentOverlapObstruction
+```
+
+That theorem intentionally forgets the exact pair identity and returns an
+existential listed witness depth.  The matching Pulse-level caller surface is:
+
+```text
+adjacent overlap obstruction
+  -> exists W in L with full singleton Beam diagnostic
+```
+
+So Branch B was taken.
+
+## Added Theorem
+
+Added in `DkMath.Collatz.PetalBridge.PressureBeam.Pulse`:
+
+```lean
+theorem exists_sourcePressureBeamPulse_witness_full_diagnostic_of_adjacentOverlapObstruction
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hobs :
+      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
+    ∃ W : SourcePressureLocalIslandWitness n k r,
+      W ∈ L ∧
+        ... full singleton Beam diagnostic for W ...
+```
+
+It consumes the stronger cp230 theorem:
+
+```lean
+exists_sourcePressureBeamPulse_leftWitness_full_diagnostic_of_adjacentOverlapObstruction
+```
+
+and projects `A ∈ L` via:
+
+```lean
+sourcePressureLocalIslandWitnessAdjacentPairInList_left_mem
+```
+
+The theorem does not re-run the overlap recursion.  It only weakens the
+pair-preserving surface when a caller does not need `A`, `B`, or the explicit
+pair-overlap obstruction.
+
+## Branches Inspected But Not Taken
+
+Branch A:
+
+- Not taken.
+- No caller currently required the right endpoint `B` specifically.
+- The existing cp228 right endpoint theorem remains available if that need
+  appears later.
+
+Branch C:
+
+- Not taken.
+- No caller needed both endpoint diagnostics simultaneously.
+
+Branch D:
+
+- Not taken.
+- cp230 was strong enough, but the anonymous overlap-to-depth style already
+  exists in `PressureBeam/Core.lean`; the new Pulse theorem is the matching
+  full-diagnostic surface.
+
+Branch E:
+
+- Not taken.
+- The caller bridge is available: overlap obstruction is already a direct
+  hypothesis in the new theorem.
+
+## Classification
+
+True Beam:
+
+- Adjacent overlap obstruction now has an anonymous full singleton diagnostic
+  surface.
+
+Boundary:
+
+- The theorem deliberately forgets pair identity.
+- It should be used only when preserving pair identity would be caller noise.
+- The witness is not canonical; it is obtained by weakening the cp230 left
+  endpoint theorem.
+
+False Beam:
+
+- None added.
+
+Gap:
+
+- Right endpoint overlap wrapper remains unadded.
+- Both-endpoint overlap diagnostic remains unadded.
+- These should be added only when actual callers need them.
+
+## Dependency Direction
+
+No dependency inversion was introduced.
+
+Only `PressureBeam/Pulse.lean` changed.  Lower diagnostic modules still do not
+import Beam.
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
+- disjointness;
+- propagation;
+- Collatz convergence.
+
+## Verification
+
+Commands run from `lean/dk_math`:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
+lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
+lake build DkMath.Collatz.PetalBridge.PressureBeam
+lake build DkMath.Collatz.PetalBridge
+```
+
+All builds completed successfully.
+
+No-sorry/admit scan over the inspected pressure files returned no matches:
+
+```text
+rg -n "sorry|admit" lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam lean/dk_math/DkMath/Collatz/PetalBridge/PressureAutomaton.lean lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean lean/dk_math/DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
+```
+
+`git diff --check` completed successfully.
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
+Next useful branch should remain caller-driven.
+
+If downstream work needs the right side of the obstructing pair, add:
+
+```text
+overlap obstruction
+  -> exists A B, addressed pair, pair-overlap obstruction,
+     and full diagnostic for B
+```
+
+If downstream work needs both endpoints, add one paired theorem rather than
+two independent wrappers.
+
+Otherwise, keep cp230 plus cp231 as the public overlap Beam surface:
+
+```text
+pair-preserving surface for precise callers
+anonymous witness surface for callers that only need one pulse diagnostic
+```
````
`````
