# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam.Pulse

gch: 008e0405e382a5187aa1044236ac904dbeb9d397

## Report

cp229 を完了しました。

`PressureAdjacentDiagnosis.lean` に、隣接ペア住所から左右 witness の membership を取り出す薄い補題を追加しました。

- `sourcePressureLocalIslandWitnessAdjacentPairInList_left_mem`
- `sourcePressureLocalIslandWitnessAdjacentPairInList_right_mem`

それに合わせて `PressureBeam/Pulse.lean` の cp228 theorem は、局所再帰を持たずにこの下層補題を使う形へ整理しました。Beam 側の public theorem statement は変えていません。

検証済みです。

- `lake build DkMath.Collatz.PetalBridge` passed
- no-sorry/admit scan passed for inspected Pressure files
- `git diff --check` passed

`report-petal-229.md` も新規作成し、次の Gap として「overlap obstruction から addressed adjacent obstructing pair を取り出す下層 projection」を明記しています。

## Review

## 結論

**採用** じゃ。
cp229 は、分岐戦略として良い進み方になっている。

今回取ったのは **Branch 0**。

```text id="yhfo5e"
AdjacentPairInList L A B
  -> A ∈ L

AdjacentPairInList L A B
  -> B ∈ L
```

を、下層の `PressureAdjacentDiagnosis.lean` に切り出した。
これは正しい配置じゃ。Beam 語彙を使わない純粋な list-address projection なので、`PressureBeam/Pulse.lean` に置くより、定義元に近い層へ置くのが自然じゃ。

## 実装レビュー

追加 theorem はこの 2 本。

```lean id="hrgsks"
sourcePressureLocalIslandWitnessAdjacentPairInList_left_mem
sourcePressureLocalIslandWitnessAdjacentPairInList_right_mem
```

意味は明快。

```text id="xn10rh"
SourcePressureLocalIslandWitnessAdjacentPairInList L A B
  -> A ∈ L
```

```text id="dbpmhk"
SourcePressureLocalIslandWitnessAdjacentPairInList L A B
  -> B ∈ L
```

これにより、cp228 の Beam 側 theorem は局所再帰を持たずに、下層 projection を呼ぶだけになった。

```lean id="t3elw8"
sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_left
sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_right
```

の public theorem statement を変えずに、proof noise を減らした。これは良い mechanical refinement じゃ。

## 戦略評価

今回の良さは、**Branch 0 を先に閉じたこと**じゃ。

前回の cp228 では、A/B identity-preserving diagnostic は通ったが、証明内部に `AdjacentPairInList` から membership を取り出す induction が重複していた。

今回それを下層補題として切り出したことで、次の overlap branch に入る準備ができた。

```text id="otz94m"
overlap obstruction
  -> adjacent pair address
  -> left/right membership projection
  -> full singleton diagnostic
```

このルートが綺麗になる。

## True Beam / Boundary / False Beam / Gap

## True Beam

今回の True Beam は構造補助じゃ。

```text id="rsnilt"
AdjacentPairInList L A B
  -> A ∈ L
```

```text id="l11pb9"
AdjacentPairInList L A B
  -> B ∈ L
```

この membership projection によって、recovered-pair diagnostic の A/B identity を保ちやすくなった。

## Boundary

これは list-address local な補題。
与えられた `AdjacentPairInList L A B` の端点が `L` に含まれる、というだけ。

```text id="o9grma"
pair is addressed in L
  -> endpoints are members of L
```

以上は言っていない。

## False Beam

否定 theorem はなし。
今回の問題は obstruction ではなく API 形状だったので、これは妥当。

## Gap

残る Gap は report 通り、overlap obstruction から addressed adjacent pair を取り出す projection じゃ。

欲しい形はこれ。

```text id="z66uj3"
SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
  -> ∃ A B,
       SourcePressureLocalIslandWitnessAdjacentPairInList L A B
       ∧ PairOverlapObstruction A B
```

この下層 projection ができれば、Beam 側は薄い wrapper で済む。

```text id="mm0q33"
overlap obstruction
  -> ∃ A B, AdjacentPairInList L A B
  -> A ∈ L or B ∈ L
  -> full singleton diagnostic
```

## 注意点

今回 overlap theorem を追加しなかったのは良い判断じゃ。
Branch 0 の 2 theorem が先に必要だった。

ただし、次 checkpoint ではいよいよ overlap address projection を攻めるべきじゃ。
ここでまた generic existential だけに戻ると、cp228 で得た branch identity の流れが弱くなる。

## 次の checkpoint 方針

次は **overlap obstruction address projection** を主戦場にする。

ただし、分岐 Goal で構える。

重要なのは、最終的な Beam diagnostic theorem に飛ばず、まず下層で

```text id="tgp0pt"
overlap obstruction
  -> addressed adjacent pair
```

が取れるかを調べることじゃ。

それが取れた場合だけ、Beam 側で thin wrapper を足す。

## 次の Codex 指示

```text id="ra44s5"
Checkpoint: petal-230

Primary Goal:
  Build or reject the lower-layer overlap address projection needed for a
  Beam-facing overlap diagnostic.

Context:
  cp229 added reusable adjacent-pair membership projections:

    sourcePressureLocalIslandWitnessAdjacentPairInList_left_mem
    sourcePressureLocalIslandWitnessAdjacentPairInList_right_mem

  These live in `PressureAdjacentDiagnosis.lean` and do not mention Beam.

  cp228 already has Beam-facing diagnostics for an addressed adjacent pair:

    AdjacentPairInList L A B -> full diagnostic for A
    AdjacentPairInList L A B -> full diagnostic for B

  The remaining Gap is:

    overlap obstruction
      -> addressed adjacent obstructing pair

Strategic Branch Goals:

  Branch A: overlap obstruction directly exposes a head adjacent pair
    Inspect:

      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L

    If the head case exposes witnesses A B and an adjacent-pair address:

      SourcePressureLocalIslandWitnessAdjacentPairInList L A B

    add a lower-layer projection theorem that returns the addressed pair
    existentially.

    Candidate shape:

      theorem exists_adjacentPairInList_of_overlapObstruction
          {L : List (SourcePressureLocalIslandWitness n k r)}
          (h : SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
          ∃ A B,
            SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
              <the local pair overlap obstruction predicate for A B>

    Codex should discover the exact pair-overlap predicate name from the
    workspace.  Do not invent it.

  Branch B: overlap obstruction is recursive over the tail
    If the predicate is recursive and the tail case gives an addressed pair in
    the tail, prove that the same pair is also addressed in the full list.

    This may require a helper:

      AdjacentPairInList tail A B
        -> AdjacentPairInList (head :: tail) A B

    Add this helper only if it is lower-layer, small, and reusable.

  Branch C: overlap obstruction exposes only existence, not stable pair identity
    If the structure gives only an existential obstruction without stable A/B
    names, add an existential projection only.

    Do not force left/right identity preservation.

  Branch D: overlap obstruction already routes through failureResolution/seed
    If the only clean theorem is already covered by cp227:

      failureResolution -> ∃ W full diagnostic

    add no duplicate Beam theorem.
    Report that branch-specific overlap identity remains hidden.

  Branch E: pair overlap predicate is missing or too large
    If there is no compact pair-level obstruction predicate to include in the
    theorem statement, consider a weaker projection:

      overlap obstruction
        -> ∃ A B, AdjacentPairInList L A B

    Add this only if it is mathematically useful and does not hide important
    assumptions.

  Branch F: obstruction or contradiction found
    If an apparent overlap witness cannot be addressed in L or cannot provide
    membership, record the obstruction.
    Add a negative theorem only if local and useful.

Implementation rules:
  Use #check, #print, and scratch lemmas.
  Let Lean determine the exact theorem shape.
  Prefer lower-layer projection theorems that do not import Beam.
  Add no more than two small theorems.
  If theorem statements become large, stop and report the precise blocker.

Files to inspect:
  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
  DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
  DkMath/Collatz/PetalBridge/PressureAutomaton.lean
  DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean

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
  Lower projection theorems must not import Beam.
  Beam-facing wrappers, if any, belong only in PressureBeam/Pulse.lean or an
  upper Beam module.

Report requirements:
  - State which Branch was taken.
  - State which branches were inspected but not taken.
  - If a lower projection was added, show its exact theorem statement and why it
    belongs below Beam.
  - If a Beam wrapper was added, show which lower projection it consumes.
  - If no theorem was added, identify the exact missing relation or API blocker.
  - Classify results as True Beam / Boundary / False Beam / Gap.
  - Predict the next branch to attack.
  - Confirm no dependency inversion.
  - Confirm no coverage, aggregation, overlap repair, or canonical selection.

Verification:
  lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
  lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
  lake build DkMath.Collatz.PetalBridge.PressureBeam
  lake build DkMath.Collatz.PetalBridge
  no-sorry grep over inspected pressure files
  git diff --check
```

## 待ち構え

次の戻りは、おそらく三択じゃ。

```text id="yxx61l"
A:
  overlap obstruction -> ∃ A B, AdjacentPairInList L A B ∧ overlap A B
  が通る
```

この場合、次は Beam 側で

```text id="gf9o8j"
overlap obstruction
  -> ∃ W ∈ L, full diagnostic for W
```

を薄く足せる。

```text id="qo48wc"
B:
  tail recursion helper が必要になる
```

この場合は、`AdjacentPairInList` の cons-lift helper を下層に追加するのが次手。

```text id="ps6jyv"
C:
  overlap predicate が pair identity を隠している
```

この場合は、overlap obstruction の public projection API 設計が次手。
無理に Beam wrapper へ進まない。

## 総合判断

cp229 は成功。
Branch 0 を先に閉じたことで、次の overlap branch を攻める準備が整った。

これはまさに、戦略の質が上がった動きじゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
index f41c2920..9ff320d4 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
@@ -278,6 +278,62 @@ theorem SourcePressureLocalIslandWitnessAdjacentPairInList.singleton_false
   intro h
   exact h

+/--
+The left witness of an addressed adjacent pair is a member of the addressed
+list.
+
+This is a pure address projection for
+`SourcePressureLocalIslandWitnessAdjacentPairInList`.  It does not inspect the
+pair diagnosis, does not choose a canonical pair, and does not claim coverage
+of all witnesses in the list.
+-/
+theorem sourcePressureLocalIslandWitnessAdjacentPairInList_left_mem
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {A B : SourcePressureLocalIslandWitness n k r}
+    (hin : SourcePressureLocalIslandWitnessAdjacentPairInList L A B) :
+    A ∈ L := by
+  induction L generalizing A B with
+  | nil =>
+      exact False.elim hin
+  | cons W1 rest ih =>
+      cases rest with
+      | nil =>
+          exact False.elim hin
+      | cons W2 rest =>
+          rcases hin with hhead | htail
+          · rcases hhead with ⟨hA, _hB⟩
+            simp [hA]
+          · exact List.mem_cons_of_mem W1 (ih htail)
+
+/--
+The right witness of an addressed adjacent pair is a member of the addressed
+list.
+
+This is the right-side companion to
+`sourcePressureLocalIslandWitnessAdjacentPairInList_left_mem`.  It is still
+only an address projection; it does not make the adjacent pair canonical and
+does not aggregate diagnostics.
+-/
+theorem sourcePressureLocalIslandWitnessAdjacentPairInList_right_mem
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {A B : SourcePressureLocalIslandWitness n k r}
+    (hin : SourcePressureLocalIslandWitnessAdjacentPairInList L A B) :
+    B ∈ L := by
+  induction L generalizing A B with
+  | nil =>
+      exact False.elim hin
+  | cons W1 rest ih =>
+      cases rest with
+      | nil =>
+          exact False.elim hin
+      | cons W2 rest =>
+          rcases hin with hhead | htail
+          · rcases hhead with ⟨_hA, hB⟩
+            simp [hB]
+          · exact List.mem_cons_of_mem W1 (ih htail)
+
 /--
 A list-level carrier for "some adjacent pair in this explicit list has an
 adjacent diagnosis".
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
index fa72bfcd..b919ca09 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
@@ -314,20 +314,8 @@ theorem sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPai
           SourcePressureBeamMassBalanceLeftInt n k r
             ((sourcePressureIntervalPulseAddress_of_localIslandWitness A).start +
               (sourcePressureIntervalPulseAddress_of_localIslandWitness A).len - 1) := by
-  have hmem : A ∈ L := by
-    induction L generalizing A B with
-    | nil =>
-        exact False.elim hin
-    | cons W1 rest ih =>
-        cases rest with
-        | nil =>
-            exact False.elim hin
-        | cons W2 rest =>
-            rcases hin with hhead | htail
-            · rcases hhead with ⟨hA, _hB⟩
-              simp [hA]
-            · exact List.mem_cons_of_mem W1 (ih htail)
-  exact sourcePressureBeamPulse_witness_singleton_full_diagnostic hmem
+  exact sourcePressureBeamPulse_witness_singleton_full_diagnostic
+    (sourcePressureLocalIslandWitnessAdjacentPairInList_left_mem hin)

 /--
 An addressed adjacent pair preserves the right witness identity for the full
@@ -359,20 +347,8 @@ theorem sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPai
           SourcePressureBeamMassBalanceLeftInt n k r
             ((sourcePressureIntervalPulseAddress_of_localIslandWitness B).start +
               (sourcePressureIntervalPulseAddress_of_localIslandWitness B).len - 1) := by
-  have hmem : B ∈ L := by
-    induction L generalizing A B with
-    | nil =>
-        exact False.elim hin
-    | cons W1 rest ih =>
-        cases rest with
-        | nil =>
-            exact False.elim hin
-        | cons W2 rest =>
-            rcases hin with hhead | htail
-            · rcases hhead with ⟨_hA, hB⟩
-              simp [hB]
-            · exact List.mem_cons_of_mem W1 (ih htail)
-  exact sourcePressureBeamPulse_witness_singleton_full_diagnostic hmem
+  exact sourcePressureBeamPulse_witness_singleton_full_diagnostic
+    (sourcePressureLocalIslandWitnessAdjacentPairInList_right_mem hin)


 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-229.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-229.md
new file mode 100644
index 00000000..70f1df92
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-229.md
@@ -0,0 +1,206 @@
+# report-petal-229
+
+## Checkpoint
+
+`petal-229`
+
+## Goal
+
+Refine the cp228 branch-specific diagnostic work by investigating:
+
+- reusable adjacent-pair membership projections;
+- the overlap obstruction branch.
+
+## Branch Taken
+
+Branch 0 was taken.
+
+The definition:
+
+```lean
+SourcePressureLocalIslandWitnessAdjacentPairInList L A B
+```
+
+is a pure list-address predicate.  It already preserves the names `A` and `B`,
+but cp228 had to re-prove membership extraction locally in `PressureBeam/Pulse`.
+
+The reusable projection layer belongs in the lower module that defines the
+address predicate, because it uses no Beam vocabulary.
+
+## Added Theorems
+
+Added in `DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis`:
+
+```lean
+theorem sourcePressureLocalIslandWitnessAdjacentPairInList_left_mem
+```
+
+Meaning:
+
+```text
+AdjacentPairInList L A B -> A in L
+```
+
+Also added:
+
+```lean
+theorem sourcePressureLocalIslandWitnessAdjacentPairInList_right_mem
+```
+
+Meaning:
+
+```text
+AdjacentPairInList L A B -> B in L
+```
+
+These are pure address projections.  They do not inspect pair diagnostics,
+choose a canonical pair, enumerate pairs, or claim list coverage.
+
+## Refactor
+
+The cp228 Pulse theorems were mechanically shortened to use these helpers:
+
+```lean
+sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_left
+sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_right
+```
+
+Their public theorem statements were not changed.
+
+## Branches Inspected But Not Taken
+
+Branch A:
+
+- `SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L` is a
+  recursive neighboring-pair obstruction.
+- It can expose a head obstruction or recurse into the tail, but there is not
+  yet a compact public projection that returns an addressed pair
+  `AdjacentPairInList L A B`.
+- Because the two-theorem budget was already used for reusable membership
+  projections, no overlap theorem was added in this checkpoint.
+
+Branch B:
+
+- Left/right overlap identity was not added.  The overlap branch needs a public
+  pair-address extraction first.
+
+Branch C:
+
+- This is the current state for overlap: recursive existence is visible in the
+  definition, but branch-specific identity is not packaged as a reusable API.
+
+Branch D:
+
+- cp227 still covers the generic existential surface through
+  failure-resolution/seed.
+- cp229 does not duplicate that theorem.
+
+Branch E:
+
+- No contradiction was found.  The missing piece is API shape, not a false
+  mathematical claim.
+
+## Classification
+
+True Beam:
+
+- Adjacent-pair left membership is now a reusable theorem.
+- Adjacent-pair right membership is now a reusable theorem.
+- cp228 recovered-pair diagnostics now consume these projections.
+
+Boundary:
+
+- These helpers are list-address local.  They only say the addressed pair's
+  two endpoints are members of the explicit list.
+
+False Beam:
+
+- None added.
+
+Gap:
+
+- Overlap obstruction needs a compact address projection such as:
+
+```text
+SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
+  -> exists A B,
+       AdjacentPairInList L A B
+       and PairOverlapObstruction A B
+```
+
+Once that exists, the left side can immediately feed:
+
+```lean
+sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_left
+```
+
+to obtain an existential overlap-side full diagnostic.
+
+## Dependency Direction
+
+No dependency inversion was introduced.
+
+The helper projections were placed in:
+
+```text
+DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+```
+
+They depend only on the adjacent-pair address predicate.  Beam-facing theorem
+consumption remains in:
+
+```text
+DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
+```
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
+rg -n "sorry|admit" lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam lean/dk_math/DkMath/Collatz/PetalBridge/PressureAutomaton.lean lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean lean/dk_math/DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
+git diff --check
+```
+
+All builds completed successfully.
+
+The no-sorry/admit scan returned no matches in the inspected pressure files.
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
+Next checkpoint should target the overlap address projection:
+
+```text
+overlap obstruction
+  -> exists adjacent obstructing pair with AdjacentPairInList
+```
+
+That theorem belongs in the lower obstruction/diagnosis layer and should not
+mention Beam.  After it exists, the Beam-facing overlap diagnostic should be a
+thin existential wrapper.
````
`````
