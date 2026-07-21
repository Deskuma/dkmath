# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam

gch: 0fe37fb8a16b30153b61cecc435ca5ed4e3ab2af

## Report

cp204 完了です。

[PressureBeam.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean) に seed list と target depth を結ぶ最小 relation を追加しました。

- `SourcePressureBeamSeedContainsDepth`
- `sourcePressureBeamDepthTarget_of_seedContainsDepth`

`SourcePressureLocalIslandWitness` は subtype なので、depth は `W.val`、local-island proof は `W.property` でした。`W.property.2.1` から `IsSourcePressureDepth n k r W.val` が取れるため、exact-depth containment なら Beam depth target まで Lean が通しました。

重要な境界として、これはまだ `SourcePressureBeamSeed L -> target` ではありません。あくまで

```text
L contains witness at j -> target at j
```

です。raw seed だけから任意 target を出す主張は、引き続き Gap として [report-petal-204.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-204.md) に記録しました。

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureBeam` passed
- `lake build DkMath.Collatz.PetalBridge` passed
- pressure 系 no-sorry check は一致なし
- `git diff --check` passed

既知の `ZsigmondyCyclotomicResearch.lean` の既存 `sorry` warning は今回も replay されましたが、作業範囲外です。

## Review

## 結論

**採用** じゃ。

cp204 はかなり良い。
前回の Gap だった

```text id="zqh7st"
seed list L --?--> target depth j
```

に対して、Lean に聞いた結果、最小 relation がくっきり見えた。

追加されたのは次の 2 つ。

```lean id="n95zgy"
def SourcePressureBeamSeedContainsDepth

theorem sourcePressureBeamDepthTarget_of_seedContainsDepth
```

そして、`SourcePressureLocalIslandWitness` の実体も明確になった。

```lean id="ruozwp"
abbrev SourcePressureLocalIslandWitness
    (n : OddNat) (k r : ℕ) :=
  { j : ℕ // SourcePressureLocalIsland n k r j }
```

つまり depth は `W.val`、local-island proof は `W.property`。
さらに `W.property.2.1` から `IsSourcePressureDepth n k r W.val` が取れる。これで exact-depth containment から Beam depth target まで Lean が通った。

## 実装レビュー

今回の relation はよい。

```lean id="ss4p55"
def SourcePressureBeamSeedContainsDepth
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r))
    (j : ℕ) : Prop :=
  ∃ W ∈ L, W.val = j
```

これは過不足が少ない。
「seed が target を生む」とは言っていない。
「list が exact-depth witness を含む」とだけ言っている。

そして theorem も安全じゃ。

```lean id="s7lzzk"
theorem sourcePressureBeamDepthTarget_of_seedContainsDepth
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hcontains : SourcePressureBeamSeedContainsDepth L j) :
    SourcePressureBeamDepthTarget n k r j := by
  rcases hcontains with ⟨W, _hmem, hdepth⟩
  subst hdepth
  exact W.property.2.1
```

これは非常に良い True Beam。
`W.property` の中に local-island proof があり、その中に depth target が入っていることを Lean が認めた。

ここで重要なのは、`SourcePressureBeamSeed L` を使っていないことじゃ。
これは欠点ではない。むしろ正確な境界じゃ。

```text id="ndk7kz"
SourcePressureBeamSeed L:
  list の failure-resolution state

SourcePressureBeamSeedContainsDepth L j:
  list-address relation

SourcePressureBeamDepthTarget n k r j:
  target depth property
```

この 3 つが分離された。

## 数学的意味

今回で、Gap が一段 Core に変わった。

以前の Gap はこれだった。

```text id="zcdift"
seed list L と target depth j の間に関係がない
```

今回、それがこうなった。

```text id="9zxb46"
L contains W with W.val = j
  -> j is a Beam depth target
```

DkMath 哲学で言えば、

```text id="0rt0k1"
Core:
  witness W は depth W.val を持つ

True Beam:
  exact-depth witness containment から BeamDepthTarget が出る

Gap:
  raw SourcePressureBeamSeed L だけでは、まだ target depth j を選べない
```

ここがかなり明瞭になった。

## True Beam / False Beam / Gap

## True Beam

今回の True Beam はこれ。

```lean id="x1bf0h"
SourcePressureBeamSeedContainsDepth L j
  -> SourcePressureBeamDepthTarget n k r j
```

これは「list-address relation から target relation へ」の最初の橋じゃ。

## False Beam

今回も negated theorem は追加されていない。
これは問題ない。

## Gap

まだ残る Gap はこれ。

```text id="fdyr5s"
SourcePressureBeamSeed L
  だけから
target depth j
  をどう選ぶか
```

report でも、raw seed だけから任意 target を出す主張は under-specified として残している。これは False ではなく、まだ relation が足りない Gap じゃ。

## 次の一歩先ゆく推論

次に Lean へ聞くべきことが見えた。

いまは、

```text id="8fa2fy"
containsDepth -> target
```

が通った。

次は、

```text id="pot2yf"
seed -> exists containsDepth
```

が通るかを試す価値がある。

なぜなら `SourcePressureBeamSeed L` は、定義上は `SourcePressureFailureResolution L` であり、これは recovered pair diagnostic か overlap obstruction の分岐だったはずじゃ。
もし両 branch が「隣接 pair in list」を含むなら、Lean は次を通すかもしれぬ。

```lean id="sluwq8"
theorem exists_sourcePressureBeamSeedContainsDepth_of_seed
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hseed : SourcePressureBeamSeed L) :
    ∃ j, SourcePressureBeamSeedContainsDepth L j
```

これは大事な実験じゃ。
通れば、raw seed は「任意の target」は選べないが、「少なくとも何らかの target depth を含む」と言える。

さらに通るなら次。

```lean id="xxfske"
theorem exists_sourcePressureBeamDepthTarget_of_seed
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hseed : SourcePressureBeamSeed L) :
    ∃ j, SourcePressureBeamDepthTarget n k r j
```

これは **seed から存在的 target へ** の最初の Beam transport 入口になる。
ただし、これは global propagation ではない。local list 内の existential target extraction じゃ。

ここは Lean に聞く価値が高い。

## 注意点

まだ次は言っていない。

```text id="y07whn"
seed から任意の j へ target が出る
```

```text id="59idki"
seed が target range を cover する
```

```text id="h0uxm9"
複数 seed が aggregate する
```

```text id="v5fbs5"
overlap が repair される
```

```text id="f6la42"
Beam が時間方向に伝播する
```

```text id="p8x98q"
Collatz convergence
```

まだここは行かない。

次にやるのは、**existential target extraction** の実験じゃ。

## 次の Codex 指示

```text id="z1bie8"
Checkpoint: petal-205

Main goal:
  Ask Lean whether a raw `SourcePressureBeamSeed L` contains at least one
  explicit depth target.  This is an experimental True/False Beam checkpoint.
  Do not prove arbitrary target transport, coverage, aggregation, overlap repair,
  or convergence.

Primary target file:
  DkMath/Collatz/PetalBridge/PressureBeam.lean

Allowed supporting files:
  docs/dev/das-p2l-260607/review/report-petal-205.md

Do not modify:
  DkMath/Collatz/PetalBridge/PressureDecay.lean
  DkMath/Collatz/PetalBridge/PressureFrontier.lean
  DkMath/Collatz/PetalBridge/PressureAccounting.lean
  DkMath/Collatz/PetalBridge/PressureAutomaton.lean
  DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
  Any non-Collatz files

DkMath philosophy:
  Beams means Beam x2.

  Core:
    facts accepted by Lean.

  True Beam:
    facts Lean proves from the current Core.

  False Beam:
    negated facts, obstruction facts, or explicit rejected overclaims.

  Gap:
    statements that are under-specified because a relation is missing.

  The goal is to grow Core by fixing both True and False observations.
  Do not merely inspect the code.  Try small Lean statements and let Lean decide.

Current Core:
  SourcePressureBeamSeed
  SourcePressureBeamDepthTarget
  SourcePressureBeamSeedContainsDepth
  sourcePressureBeamDepthTarget_iff_margin_pos
  sourcePressureBeamDepthTarget_of_margin_pos
  sourcePressureMargin_pos_of_beamDepthTarget
  sourcePressureBeamDepthTarget_of_seedContainsDepth

Current known Gap:
  SourcePressureBeamSeed L does not imply an arbitrary target depth `j`.

Required experiments:

  Experiment T1:
    Try to prove that a raw Beam seed contains at least one explicit witness
    depth.

    Candidate theorem:

      theorem exists_sourcePressureBeamSeedContainsDepth_of_seed
          {n : OddNat} {k r : ℕ}
          {L : List (SourcePressureLocalIslandWitness n k r)}
          (hseed : SourcePressureBeamSeed L) :
          ∃ j, SourcePressureBeamSeedContainsDepth L j

    Proof strategy:
      - unfold `SourcePressureBeamSeed`;
      - unfold `SourcePressureFailureResolution`;
      - split on recovered branch / overlap branch;
      - in the recovered branch, use the adjacent pair in list to extract a
        witness and its depth;
      - in the overlap branch, inspect whether the obstruction also carries an
        adjacent pair in list.
      - If the overlap branch does not expose a list member, do not force it.
        Record the missing projection as Gap.

  Experiment T2:
    If T1 passes, try to prove that a raw Beam seed gives an existential Beam
    depth target.

      theorem exists_sourcePressureBeamDepthTarget_of_seed
          {n : OddNat} {k r : ℕ}
          {L : List (SourcePressureLocalIslandWitness n k r)}
          (hseed : SourcePressureBeamSeed L) :
          ∃ j, SourcePressureBeamDepthTarget n k r j

    Proof strategy:
      - use T1 to obtain `j` and `SourcePressureBeamSeedContainsDepth L j`;
      - apply `sourcePressureBeamDepthTarget_of_seedContainsDepth`.

  Experiment T3:
    If T2 passes, try a stronger paired statement:

      theorem exists_sourcePressureBeamSeedContainsDepth_and_target_of_seed
          {n : OddNat} {k r : ℕ}
          {L : List (SourcePressureLocalIslandWitness n k r)}
          (hseed : SourcePressureBeamSeed L) :
          ∃ j,
            SourcePressureBeamSeedContainsDepth L j ∧
              SourcePressureBeamDepthTarget n k r j

  Experiment G1:
    Re-test the overclaim in scratch only:

      SourcePressureBeamSeed L -> SourcePressureBeamDepthTarget n k r j

    Do not commit it.  It should remain Gap unless Lean unexpectedly proves it
    with the given arbitrary `j`.

  Experiment F1:
    If T1 fails, identify which branch fails:
      - recovered branch lacks list-member projection;
      - overlap branch lacks list-member projection;
      - the predicate was too opaque;
      - or some theorem name is missing.

    Record this as False Beam only if Lean proves a negated or obstruction
    theorem.  Otherwise record it as Gap.

Guardrails:
  Do not add:
    - arbitrary target transport;
    - propagation theorem over time/orbit;
    - convergence theorem;
    - global coverage;
    - arbitrary-list recursive decomposition;
    - canonical first diagnosis;
    - enumeration of all diagnostics;
    - aggregation over multiple recovered diagnostics;
    - interval union accounting;
    - overlap repair;
    - maximality;
    - uniqueness;
    - sorting theorem;
    - disjointness between multiple recovered families.

Report requirements:
  The report must contain:
    1. Situation analysis.
    2. What Lean experiments were tried.
    3. True Beam facts that passed.
    4. False Beam / Gap observations.
    5. Which branch failed if a theorem did not pass.
    6. One-step-ahead Wise Wolf inference.
    7. Experimental lemma table with passed / failed / under-specified.
    8. Explicit statement that no arbitrary target transport, propagation,
       convergence, coverage, aggregation, or overlap repair theorem was added.

Verification commands:
  lake build DkMath.Collatz.PetalBridge.PressureBeam
  lake build DkMath.Collatz.PetalBridge

No-sorry check:
  rg -n "\bsorry\b|admit" \
    DkMath/Collatz/PetalBridge/PressureBeam.lean \
    DkMath/Collatz/PetalBridge/PressureAutomaton.lean \
    DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean \
    DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean \
    DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
    DkMath/Collatz/PetalBridge/PressureAccounting.lean \
    DkMath/Collatz/PetalBridge/PressureFrontier.lean \
    DkMath/Collatz/PetalBridge/PressureDecay.lean \
    DkMath/Collatz/PetalBridge/DriftBudget.lean

Git diff hygiene:
  git diff --check
```

## まとめ

うむ、これはかなり進んだ。

今回で、

```text id="4a97zp"
witness exact depth containment
  -> Beam depth target
```

が Core になった。

次は、

```text id="hgk5yg"
Beam seed
  -> exists witness depth
  -> exists Beam depth target
```

が通るかを Lean に聞く。

これが通れば、Beam は「任意 target」ではなく、**存在的 target 抽出**として最初の輸送を持つ。
ここから本当の Beam が始まる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
index 74bd5939..97a54952 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
@@ -134,4 +134,36 @@ theorem sourcePressureMargin_pos_of_beamDepthTarget
     0 < SourcePressureMarginInt n k (r + j) :=
   (sourcePressureBeamDepthTarget_iff_margin_pos n k r j).1 h

+/--
+An explicit Beam seed witness list contains a witness at relative depth `j`.
+
+`SourcePressureLocalIslandWitness` is a subtype
+`{ j : ℕ // SourcePressureLocalIsland n k r j }`, so the actual depth field is
+`W.val`.  This relation is the first seed-to-depth connector.  It only says
+that the supplied list contains an exact-depth witness; it does not claim that
+the list is complete, sorted, maximal, or globally covering.
+-/
+def SourcePressureBeamSeedContainsDepth
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (j : ℕ) : Prop :=
+  ∃ W ∈ L, W.val = j
+
+/--
+If a supplied Beam seed witness list contains an exact-depth local-island
+witness, then that depth is a Beam depth target.
+
+This is not a real propagation theorem from `SourcePressureBeamSeed L`.
+The proof uses only the explicit containment relation and the local-island
+proof carried by the witness.
+-/
+theorem sourcePressureBeamDepthTarget_of_seedContainsDepth
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hcontains : SourcePressureBeamSeedContainsDepth L j) :
+    SourcePressureBeamDepthTarget n k r j := by
+  rcases hcontains with ⟨W, _hmem, hdepth⟩
+  subst hdepth
+  exact W.property.2.1
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-204.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-204.md
new file mode 100644
index 00000000..e613e77b
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-204.md
@@ -0,0 +1,233 @@
+# report-petal-204
+
+## Situation Analysis
+
+`petal-204` fills the previous Gap:
+
+```text
+seed list L --?--> target depth j
+```
+
+The goal was not to prove Beam propagation.  The goal was to ask Lean for the
+smallest explicit relation connecting a supplied witness list to a target
+depth.
+
+The result is an exact-depth containment relation:
+
+```lean
+SourcePressureBeamSeedContainsDepth L j
+```
+
+This relation says that the supplied list contains a local-island witness whose
+stored depth is exactly `j`.
+
+## Actual Field Names Discovered
+
+`SourcePressureLocalIslandWitness` is not a structure with named fields.  It is
+a subtype abbreviation:
+
+```lean
+abbrev SourcePressureLocalIslandWitness
+    (n : OddNat) (k r : ℕ) :=
+  { j : ℕ // SourcePressureLocalIsland n k r j }
+```
+
+Therefore the actual usable fields are the standard subtype projections:
+
+- witness depth: `W.val`
+- local-island proof: `W.property`
+
+The local-island proof has the shape:
+
+```lean
+SourcePressureLocalIsland n k r W.val
+```
+
+and since
+
+```lean
+SourcePressureLocalIsland n k r j
+  := 0 < j ∧
+     IsSourcePressureDepth n k r j ∧
+     ¬ IsSourcePressureDepth n k r (j - 1) ∧
+     ¬ IsSourcePressureDepth n k r (j + 1)
+```
+
+the target-depth positivity part is available as:
+
+```lean
+W.property.2.1
+```
+
+with type:
+
+```lean
+IsSourcePressureDepth n k r W.val
+```
+
+## Added Relation
+
+Added:
+
+```lean
+def SourcePressureBeamSeedContainsDepth
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (j : ℕ) : Prop :=
+  ∃ W ∈ L, W.val = j
+```
+
+This is the weakest exact-depth relation found in the current Core.  It does
+not say that the list is a seed, complete, sorted, maximal, or covering.
+
+## True Beam Facts That Passed
+
+Added:
+
+```lean
+theorem sourcePressureBeamDepthTarget_of_seedContainsDepth
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hcontains : SourcePressureBeamSeedContainsDepth L j) :
+    SourcePressureBeamDepthTarget n k r j
+```
+
+Result: passed.
+
+Lean accepted this because exact-depth containment gives a witness `W` with
+`W.val = j`, and `W.property.2.1` proves that the witness depth is a selected
+source pressure depth.
+
+## False Beam / Gap Observations
+
+### Gap: raw seed still does not imply arbitrary target
+
+The overbroad statement remains under-specified:
+
+```text
+SourcePressureBeamSeed L -> SourcePressureBeamDepthTarget n k r j
+```
+
+Reason: a seed state alone says that the list has a failure-resolution state.
+It does not say that the list contains a witness at the particular target
+depth `j`.
+
+This was not committed as a theorem.
+
+### Gap converted to Core: exact-depth list containment
+
+The previous missing relation is now partly filled:
+
+```text
+L contains a witness W with W.val = j
+  -> depth target at j
+```
+
+This is a True Beam fact, but it is still local and explicit.
+
+## Was a Seed-to-Target Theorem Added?
+
+Yes, but only in the exact-containment sense:
+
+```text
+SourcePressureBeamSeedContainsDepth L j
+  -> SourcePressureBeamDepthTarget n k r j
+```
+
+No theorem was added from `SourcePressureBeamSeed L` alone to a target depth.
+
+## One-Step-Ahead Wise Wolf Inference
+
+The next split is now visible:
+
+```text
+seed state
+  versus
+seed list address
+```
+
+`SourcePressureBeamSeed L` is an automaton/failure-resolution state.  It does
+not by itself choose a target depth.
+
+`SourcePressureBeamSeedContainsDepth L j` is a list-address relation.  It does
+choose a target depth, but only because a witness at that exact depth is
+already present in the list.
+
+The next safe experiment is to connect the two without overclaiming:
+
+```lean
+theorem sourcePressureBeamDepthTarget_of_seed_and_containsDepth
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (_hseed : SourcePressureBeamSeed L)
+    (hcontains : SourcePressureBeamSeedContainsDepth L j) :
+    SourcePressureBeamDepthTarget n k r j
+```
+
+This theorem would intentionally ignore `_hseed`: its value is documentation
+and API shape.  It states that a seed plus an explicit address relation gives a
+target, while preventing future agents from pretending that seed alone is
+enough.
+
+Whether to add that wrapper should be decided in the next checkpoint.
+
+## Experimental Lemma Table
+
+| Experiment | Statement | Result |
+| --- | --- | --- |
+| Field inspection | witness depth is accessible as `W.val` | passed |
+| Field inspection | witness proof is accessible as `W.property` | passed |
+| R1 | define exact-depth list containment | passed |
+| T1 | containment implies Beam depth target | passed |
+| F1 | raw seed implies arbitrary target | under-specified / not committed |
+
+## Guardrails Confirmed
+
+This checkpoint did not add:
+
+- a real propagation theorem;
+- a convergence theorem;
+- global coverage;
+- arbitrary-list recursive decomposition;
+- canonical first diagnosis;
+- enumeration of all diagnostics;
+- aggregation over multiple recovered diagnostics;
+- interval union accounting;
+- overlap repair;
+- maximality;
+- uniqueness;
+- sorting theorem;
+- disjointness between multiple recovered families.
+
+The added theorem is local to an explicitly supplied list membership witness.
+
+## Verification
+
+Executed commands:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureBeam
+lake build DkMath.Collatz.PetalBridge
+rg -n "\bsorry\b|admit" \
+  DkMath/Collatz/PetalBridge/PressureBeam.lean \
+  DkMath/Collatz/PetalBridge/PressureAutomaton.lean \
+  DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean \
+  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean \
+  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
+  DkMath/Collatz/PetalBridge/PressureAccounting.lean \
+  DkMath/Collatz/PetalBridge/PressureFrontier.lean \
+  DkMath/Collatz/PetalBridge/PressureDecay.lean \
+  DkMath/Collatz/PetalBridge/DriftBudget.lean
+git diff --check
+```
+
+Result:
+
+- `lake build DkMath.Collatz.PetalBridge.PressureBeam`: passed.
+- `lake build DkMath.Collatz.PetalBridge`: passed.
+- no-sorry check over the pressure files listed above: no matches.
+- `git diff --check`: passed.
+
+The builds still replay the known unrelated warning in
+`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean` about an existing
+`sorry`.  This checkpoint did not touch that file.
````
`````
