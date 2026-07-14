# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam.Pulse

gch: 24aea1668da8f2de5f426e4dc749d27c75789edd

## Report

cp230 完了です。

`PressureAdjacentDiagnosis.lean` に下層 projection を追加しました。

`exists_adjacentPairInList_pairOverlapObstruction_of_overlapObstruction`

これで `SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L` から、実際に `L` 内で隣接している `A B` と、その `SourcePressureLocalIslandWitnessPairOverlapObstruction A B` を取り出せます。Beam 非依存です。

さらに `PressureBeam/Pulse.lean` に薄い wrapper も追加しました。

`exists_sourcePressureBeamPulse_leftWitness_full_diagnostic_of_adjacentOverlapObstruction`

こちらは下層 projection を消費して、overlap pair の左 witness `A` に full singleton Beam diagnostic を接続します。pair identity と overlap evidence は結論に残してあります。

検証済み:

- `lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis`
- `lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse`
- `lake build DkMath.Collatz.PetalBridge.PressureBeam`
- `lake build DkMath.Collatz.PetalBridge`
- no-sorry/admit scan passed for inspected Pressure files
- `git diff --check` passed

`report-petal-230.md` も作成済みです。次は必要なら右 witness 版 wrapper、または pair identity を捨てた匿名 `∃ W ∈ L` surface に進めます。

## Review

## 結論

**採用** じゃ。
cp230 は、前回の Gap だった

```text id="lx5gpn"
overlap obstruction
  -> addressed adjacent obstructing pair
```

を、きちんと下層 projection と Beam-facing wrapper に分けて閉じている。
これはかなり良い進軍じゃ。

今回の追加は大きく 2 段。

```lean id="xw425t"
exists_adjacentPairInList_pairOverlapObstruction_of_overlapObstruction
```

これは下層 `PressureAdjacentDiagnosis.lean` 側。

```lean id="tj5zsv"
exists_sourcePressureBeamPulse_leftWitness_full_diagnostic_of_adjacentOverlapObstruction
```

これは上層 `PressureBeam/Pulse.lean` 側。

下層では Beam 語彙を使わず、上層でだけ Beam diagnostic に接続している。依存方向が綺麗じゃ。

## 実装レビュー

下層 projection の意味はこれ。

```text id="x0sdoe"
SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
  -> ∃ A B,
       SourcePressureLocalIslandWitnessAdjacentPairInList L A B
       ∧ SourcePressureLocalIslandWitnessPairOverlapObstruction A B
```

これはとても良い。
overlap obstruction が「どこかで隣接 overlap がある」という情報を持っているだけでなく、実際に `L` 内で隣接している `A B` と、その pair-local obstruction を取り出せるようになった。

しかも、tail case では

```lean id="y1og9q"
SourcePressureLocalIslandWitnessAdjacentPairInList.tail
```

で address を full list 側へ持ち上げている。
ここは正しい。tail 内の隣接 pair は、head を付けても隣接 pair として生きている。

## Beam wrapper の評価

Beam 側 wrapper は左 witness `A` に full diagnostic を接続している。

```text id="m85bns"
overlap obstruction
  -> ∃ A B,
       addressed pair A B
       ∧ pair overlap obstruction A B
       ∧ full singleton diagnostic for A
```

ここで `A B`、address predicate、pair overlap evidence を結論に残しているのが良い。
匿名 witness に潰さず、branch identity を保持している。

また、左を「グローバル canonical target」と主張していない。
あくまで named left endpoint wrapper じゃ。ここも安全。

## True Beam / Boundary / False Beam / Gap

## True Beam

今回の True Beam はこれ。

```text id="nbggpl"
adjacent overlap obstruction
  -> addressed adjacent pair with pair-local overlap obstruction
```

さらに、

```text id="j6xien"
addressed overlap pair
  -> left witness full singleton diagnostic
```

まで進んだ。

これで overlap branch も、recovered adjacent pair branch と同じく、identity-preserving diagnostic に接続できるようになった。

## Boundary

今回の theorem は adjacent-pair local。

```text id="v3xo1r"
one obstructing adjacent pair
```

を取り出しているだけで、list 全体 coverage ではない。
左 endpoint も「この theorem の named side」であり、全体の標準選択ではない。

## False Beam

否定 theorem はなし。
今回は obstruction を修理するのではなく、obstruction の所在を取り出した。
だから false theorem を増やす必要はない。

## Gap

残る Gap は report の通り、二つ。

```text id="zpq3fo"
right endpoint wrapper はまだ無い
```

```text id="iipx9v"
anonymous witness surface はまだ無い
```

つまり、

```text id="vm82vl"
overlap obstruction
  -> full diagnostic for B
```

と、

```text id="v6sd0j"
overlap obstruction
  -> ∃ W ∈ L, full diagnostic for W
```

は、まだ caller-driven optional branch じゃ。

## 戦略評価

これは良い分岐処理じゃ。

前回の予測では、

```text id="sj398u"
A:
  overlap obstruction -> ∃ A B, AdjacentPairInList L A B ∧ overlap A B
```

が通る可能性を見ていた。
今回まさにそれが通った。

しかも Branch B の tail recursion も処理され、追加 helper は不要だった。
`AdjacentPairInList.tail` が既にあったので、Lean の現場判断として最小手で済んでいる。

## 注意点

一点だけ戦略的注意。

今回、左 witness wrapper を追加した。これは良い。
ただし、次に右 witness wrapper を無条件で追加すると、API が対称 wrapper で膨らみ始める。

右が必要な caller があるなら追加。
そうでなければ、今は left wrapper と lower projection だけで十分じゃ。

今の強い public surface はむしろ下層 projection。

```lean id="ip4uf4"
exists_adjacentPairInList_pairOverlapObstruction_of_overlapObstruction
```

これがあれば、必要に応じて left / right / anonymous を作れる。
だから、次は caller を見て分岐するのがよい。

## 次の checkpoint 方針

次は **caller-driven branch** にする。

つまり、いきなり右 wrapper や匿名 wrapper を足すのではなく、

```text id="s5d9vn"
今後の上位 theorem は何を欲しがるか？
```

を見る。

ただし、待ち構える分岐は明確にしておく。

```text id="w066k5"
Branch A:
  right endpoint identity が必要

Branch B:
  left/right identity は不要で、anonymous ∃ W surface が必要

Branch C:
  pair-level overlap evidence を保ったまま、両 endpoint diagnostic が必要

Branch D:
  既存 left wrapper で十分

Branch E:
  さらに下層 projection が必要
```

## 次の Codex 指示

```text id="wrzwh8"
Checkpoint: petal-231

Primary Goal:
  Decide the next overlap-diagnostic surface based on actual caller needs.
  Do not add symmetric or anonymous wrappers mechanically.

Context:
  cp230 added the lower overlap projection:

    exists_adjacentPairInList_pairOverlapObstruction_of_overlapObstruction

  and one Beam-facing wrapper:

    exists_sourcePressureBeamPulse_leftWitness_full_diagnostic_of_adjacentOverlapObstruction

  The lower projection preserves:
    A
    B
    AdjacentPairInList L A B
    PairOverlapObstruction A B

  The Beam wrapper currently attaches the full singleton diagnostic to the left
  witness A.

Strategic Branch Goals:

  Branch A: caller needs right endpoint identity
    Inspect likely higher-level callers.

    If a caller needs the right witness B specifically, add the symmetric wrapper:

      overlap obstruction
        -> ∃ A B,
             AdjacentPairInList L A B
             ∧ PairOverlapObstruction A B
             ∧ full singleton diagnostic for B

    It should consume:
      exists_adjacentPairInList_pairOverlapObstruction_of_overlapObstruction
      sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_right

    Do not add it merely for symmetry unless caller evidence exists.

  Branch B: caller only needs anonymous witness diagnostic
    If callers do not care whether the witness is A or B, add a weaker surface:

      overlap obstruction
        -> ∃ W, W ∈ L ∧ full singleton diagnostic for W

    This should consume the existing left wrapper or lower projection.
    It must not claim canonical selection.

  Branch C: caller needs both endpoint diagnostics
    If a caller needs to compare both sides of the overlap pair, add one paired
    theorem:

      overlap obstruction
        -> ∃ A B,
             AdjacentPairInList L A B
             ∧ PairOverlapObstruction A B
             ∧ full diagnostic for A
             ∧ full diagnostic for B

    Add this only if it clearly reduces proof noise.
    Otherwise report it as future possible.

  Branch D: existing cp230 left wrapper is sufficient
    If no caller needs right, anonymous, or paired surfaces, add no Lean code.

    Report that the current strongest useful surface is:
      lower projection + left Beam wrapper

  Branch E: missing caller bridge
    If a higher-level theorem cannot consume cp230 because it lacks an overlap
    obstruction hypothesis or works through failure resolution/seed instead,
    report the exact missing relation.

Implementation rules:
  Use #check, #print, and scratch lemmas.
  Inspect actual callers before adding wrapper surfaces.
  Add no more than one theorem unless both endpoints are clearly demanded by
  the same caller.
  Prefer consuming existing cp230/cp228 theorems rather than rebuilding proofs.
  Stop if the theorem statement becomes large or duplicates existing surfaces.

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
  Beam-facing wrappers belong only in PressureBeam/Pulse.lean or a higher
  Beam-facing module.

Report requirements:
  - State which Branch was taken.
  - State which branches were inspected but not taken.
  - If a theorem was added, explain the caller need that justified it.
  - If no theorem was added, explain why cp230 is sufficient.
  - Classify results as True Beam / Boundary / False Beam / Gap.
  - Predict the next branch to attack.
  - Confirm no dependency inversion.
  - Confirm no coverage, aggregation, overlap repair, disjointness, or
    canonical selection.

Verification:
  lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
  lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
  lake build DkMath.Collatz.PetalBridge.PressureBeam
  lake build DkMath.Collatz.PetalBridge
  no-sorry grep over inspected pressure files
  git diff --check
```

## 待ち構え

次の返答は、おそらく次のどれかじゃ。

```text id="vdayqy"
A:
  right wrapper が必要な caller が見つかる
```

その場合は右 endpoint wrapper を追加してよい。

```text id="sig01w"
B:
  anonymous ∃ W wrapper が caller noise を減らす
```

その場合は匿名 surface を追加してよい。ただし canonical selection ではない。

```text id="x3c7zf"
C:
  both endpoint diagnostic が必要
```

これは強いが theorem statement が大きくなる。必要性が明確な場合だけ。

```text id="ehcx4v"
D:
  既存 cp230 で十分
```

この場合は no-code report が正解。

## 総合判断

cp230 は成功。
overlap branch の下層 projection が通ったことで、戦略木の重要な Gap が閉じた。

次は wrapper を増やすのではなく、caller の必要性を見て、必要な surface だけを足す段階じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
index 9ff320d4..15d8bbea 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
@@ -334,6 +334,45 @@ theorem sourcePressureLocalIslandWitnessAdjacentPairInList_right_mem
             simp [hB]
           · exact List.mem_cons_of_mem W1 (ih htail)
 
+/--
+An adjacent-overlap obstruction exposes one addressed neighboring pair and its
+pair-local overlap obstruction.
+
+This is the cp230 lower-layer overlap projection.  It follows the same
+recursive address structure as
+`SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction`: the head
+case returns the head pair, while the tail case lifts the tail address through
+the newly supplied head.  It does not import Beam vocabulary, repair the
+overlap, choose a canonical pair among several possibilities, or claim list
+coverage.
+-/
+theorem exists_adjacentPairInList_pairOverlapObstruction_of_overlapObstruction
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hobs :
+      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
+    ∃ A B,
+      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+        SourcePressureLocalIslandWitnessPairOverlapObstruction A B := by
+  induction L with
+  | nil =>
+      exact False.elim hobs
+  | cons W1 rest ih =>
+      cases rest with
+      | nil =>
+          exact False.elim hobs
+      | cons W2 rest =>
+          rcases hobs with hhead | htail
+          · exact
+              ⟨W1, W2,
+                SourcePressureLocalIslandWitnessAdjacentPairInList.head,
+                hhead⟩
+          · rcases ih htail with ⟨A, B, hin, hobspair⟩
+            exact
+              ⟨A, B,
+                SourcePressureLocalIslandWitnessAdjacentPairInList.tail hin,
+                hobspair⟩
+
 /--
 A list-level carrier for "some adjacent pair in this explicit list has an
 adjacent diagnosis".
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
index b919ca09..7e88c827 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
@@ -350,5 +350,49 @@ theorem sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPai
   exact sourcePressureBeamPulse_witness_singleton_full_diagnostic
     (sourcePressureLocalIslandWitnessAdjacentPairInList_right_mem hin)
 
+/--
+An adjacent-overlap obstruction exposes a branch-specific left witness with
+the full singleton pulse diagnostic.
+
+This is the Beam-facing cp230 wrapper over
+`exists_adjacentPairInList_pairOverlapObstruction_of_overlapObstruction`.  The
+lower theorem supplies the addressed adjacent pair and the pair-local overlap
+obstruction; this wrapper only applies the existing left-side singleton
+diagnostic for that addressed pair.
+
+The conclusion keeps the addressed pair and the overlap obstruction visible.
+It does not repair the overlap, choose a canonical obstructing pair, aggregate
+several pairs, transport the diagnostic to arbitrary targets, or claim
+coverage of the witness list.
+-/
+theorem
+    exists_sourcePressureBeamPulse_leftWitness_full_diagnostic_of_adjacentOverlapObstruction
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hobs :
+      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
+    ∃ A B,
+      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+        SourcePressureLocalIslandWitnessPairOverlapObstruction A B ∧
+          SourcePressureBeamMassBalanceLeftInt n k r
+              ((sourcePressureIntervalPulseAddress_of_localIslandWitness A).start - 1) <
+            SourcePressureBeamMassBalanceRightInt n k r
+              ((sourcePressureIntervalPulseAddress_of_localIslandWitness A).start - 1) ∧
+            SourcePressureBeamAddressedDepthTarget L
+              ((sourcePressureIntervalPulseAddress_of_localIslandWitness A).start +
+                (sourcePressureIntervalPulseAddress_of_localIslandWitness A).len - 1) ∧
+              SourcePressureBeamMassBalanceRightInt n k r
+                ((sourcePressureIntervalPulseAddress_of_localIslandWitness A).start +
+                  (sourcePressureIntervalPulseAddress_of_localIslandWitness A).len - 1) ≤
+                SourcePressureBeamMassBalanceLeftInt n k r
+                  ((sourcePressureIntervalPulseAddress_of_localIslandWitness A).start +
+                    (sourcePressureIntervalPulseAddress_of_localIslandWitness A).len - 1) := by
+  rcases exists_adjacentPairInList_pairOverlapObstruction_of_overlapObstruction hobs with
+    ⟨A, B, hin, hobspair⟩
+  exact
+    ⟨A, B, hin, hobspair,
+      sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_left
+        hin⟩
+
 
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-230.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-230.md
new file mode 100644
index 00000000..30a0fc0c
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-230.md
@@ -0,0 +1,244 @@
+# report-petal-230
+
+## Checkpoint
+
+`petal-230`
+
+## Goal
+
+Close the overlap-address Gap left by cp229:
+
+```text
+adjacent overlap obstruction
+  -> addressed adjacent obstructing pair
+```
+
+Then, if the lower projection is clean, add one thin Beam-facing wrapper.
+
+## Branch Taken
+
+Branch A was taken, with the recursive tail handling from Branch B.
+
+The obstruction predicate:
+
+```lean
+SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
+```
+
+is recursive over neighboring pairs.  The head case exposes the pair-local
+predicate:
+
+```lean
+SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2
+```
+
+and the tail case preserves the same addressed pair through:
+
+```lean
+SourcePressureLocalIslandWitnessAdjacentPairInList.tail
+```
+
+No new cons-lift helper was needed because cp229 already found the address
+API in `PressureAdjacentDiagnosis.lean`.
+
+## Added Lower Projection
+
+Added in `DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis`:
+
+```lean
+theorem exists_adjacentPairInList_pairOverlapObstruction_of_overlapObstruction
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hobs :
+      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
+    ∃ A B,
+      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+        SourcePressureLocalIslandWitnessPairOverlapObstruction A B
+```
+
+This belongs below Beam because it only relates:
+
+- explicit witness-list overlap obstruction;
+- adjacent-pair address;
+- pair-local overlap obstruction.
+
+It imports no Beam vocabulary and does not mention mass balance.
+
+## Added Beam Wrapper
+
+Added in `DkMath.Collatz.PetalBridge.PressureBeam.Pulse`:
+
+```lean
+theorem
+    exists_sourcePressureBeamPulse_leftWitness_full_diagnostic_of_adjacentOverlapObstruction
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hobs :
+      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
+    ∃ A B,
+      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+        SourcePressureLocalIslandWitnessPairOverlapObstruction A B ∧
+          ... full singleton Beam diagnostic for A ...
+```
+
+This wrapper consumes:
+
+```lean
+exists_adjacentPairInList_pairOverlapObstruction_of_overlapObstruction
+```
+
+and then applies:
+
+```lean
+sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_left
+```
+
+The result keeps `A`, `B`, the address predicate, and the overlap obstruction
+visible.  It does not collapse the branch into an anonymous witness unless a
+caller chooses to do so later.
+
+## Branches Inspected But Not Taken
+
+Branch B:
+
+- Tail recursion was needed, but the required address lift already existed as
+  `SourcePressureLocalIslandWitnessAdjacentPairInList.tail`.
+- No new helper was added.
+
+Branch C:
+
+- Not taken.  The overlap predicate did preserve stable pair identity through
+  the recursive definition.
+
+Branch D:
+
+- Not taken.  cp227's generic `failureResolution -> exists full diagnostic`
+  remains valid, but cp230 now provides overlap-specific identity.
+
+Branch E:
+
+- Not taken.  A compact pair-level predicate already exists:
+  `SourcePressureLocalIslandWitnessPairOverlapObstruction`.
+
+Branch F:
+
+- No contradiction was found.
+
+## Classification
+
+True Beam:
+
+- Adjacent overlap obstruction now exposes an addressed pair with pair-local
+  overlap obstruction.
+- Beam Pulse can now attach the full singleton diagnostic to the left witness
+  of that addressed obstructing pair.
+
+Boundary:
+
+- The theorem is still adjacent-pair local.
+- The Beam wrapper chooses the left endpoint only as a named branch-specific
+  surface, not as a canonical global target.
+
+False Beam:
+
+- None added.
+
+Gap:
+
+- There is no right-endpoint overlap Beam wrapper yet.
+- There is no generic anonymous projection:
+
+```text
+overlap obstruction -> exists W in L with full diagnostic
+```
+
+This can now be derived, but adding it should wait until a caller needs the
+weaker anonymous surface.
+
+## Dependency Direction
+
+No dependency inversion was introduced.
+
+The lower projection is in:
+
+```text
+DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+```
+
+The Beam-facing wrapper is in:
+
+```text
+DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
+```
+
+No lower module imports Beam.
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
+The next useful branch is optional and caller-driven.
+
+If a caller wants the right endpoint of the overlap pair:
+
+```text
+overlap obstruction
+  -> exists A B, addressed pair and full diagnostic for B
+```
+
+then add the symmetric Beam wrapper using:
+
+```lean
+sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_right
+```
+
+If a caller does not care about pair identity:
+
+```text
+overlap obstruction
+  -> exists W, W in L and full diagnostic for W
+```
+
+can be added as a weaker public surface.  This should wait until it removes
+real caller noise, because the current cp230 theorem preserves more useful
+branch identity.
````
`````
