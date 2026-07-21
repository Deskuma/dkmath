# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam

gch: f13e144fd656248f9ba06311012e2819183417bb

## Report

cp203 完了です。

[PressureBeam.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean) に True Beam API を2本追加しました。

- `sourcePressureBeamDepthTarget_of_margin_pos`
- `sourcePressureMargin_pos_of_beamDepthTarget`

これで depth target まわりは三点セットになりました。

```text
Target iff margin_pos
Target of margin_pos
margin_pos of Target
```

G1 の `SourcePressureBeamSeed L -> SourcePressureBeamDepthTarget n k r j` は、`L` と `j` の関係がないため Gap として [report-petal-203.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-203.md) に記録しました。False ではなく、seed-to-depth relation 不足です。

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureBeam` passed
- `lake build DkMath.Collatz.PetalBridge` passed
- pressure 系 no-sorry check は一致なし
- `git diff --check` passed

既知の `ZsigmondyCyclotomicResearch.lean` の既存 `sorry` warning は今回も replay されましたが、作業範囲外です。

## Review

## 結論

うむ。**かなりくっきりした。**

今回の cp203 は **採用** じゃ。

理由は明確で、今回から作業が「設計を眺める」から「Lean に小さな実験補題を聞いて、True Beam / Gap を記録する」段階に入ったからじゃ。

追加された True Beam API はこの 2 本。

```lean id="dffvqb"
sourcePressureBeamDepthTarget_of_margin_pos
sourcePressureMargin_pos_of_beamDepthTarget
```

これにより、depth target 周りは三点セットになった。

```text id="gfbxca"
Target iff margin_pos
Target of margin_pos
margin_pos of Target
```

report でも、G1 の `SourcePressureBeamSeed L -> SourcePressureBeamDepthTarget n k r j` は False ではなく、`L` と `j` の関係が足りない **Gap / under-specified** として記録されている。これは非常によい整理じゃ。

## 実装レビュー

今回の追加は安全で、意味がある。

`PressureBeam.lean` に追加された constructor 側はこれ。

```lean id="as269z"
theorem sourcePressureBeamDepthTarget_of_margin_pos
    (n : OddNat) (k r j : ℕ)
    (h : 0 < SourcePressureMarginInt n k (r + j)) :
    SourcePressureBeamDepthTarget n k r j :=
  (sourcePressureBeamDepthTarget_iff_margin_pos n k r j).2 h
```

projection 側はこれ。

```lean id="bjrd38"
theorem sourcePressureMargin_pos_of_beamDepthTarget
    (n : OddNat) (k r j : ℕ)
    (h : SourcePressureBeamDepthTarget n k r j) :
    0 < SourcePressureMarginInt n k (r + j) :=
  (sourcePressureBeamDepthTarget_iff_margin_pos n k r j).1 h
```

これはまさに `iff` の左右を True Beam API として明示化しただけじゃ。
新しい強い主張はない。だが、今後の実験ではこの 2 本が効く。

Lean 的には、`SourcePressureBeamDepthTarget` を開く・作る操作が定理名で固定された。
これにより、次に seed-to-depth relation を作るとき、target 側の処理が簡単になる。

## 数学的意味

今回で、Beam の最初の観測点がはっきりした。

```text id="tmq3fe"
BeamDepthTarget
  は
SourcePressureMarginInt n k (r + j) > 0
  と同値
```

つまり Beam target とは、今の段階では **正の pressure margin を持つ depth 点** じゃ。

これはよい。
なぜなら、Beam をまだ「伝播」として定義していないうちから、Beam の target 側を pressure margin の正値として固定できたからじゃ。

DkMath 哲学で言えば、

```text id="0y4qw2"
Core:
  SourcePressureBeamDepthTarget ↔ margin_pos

True Beam:
  margin_pos から target を作れる
  target から margin_pos を取り出せる

Gap:
  seed list L と target depth j の接続関係がまだない
```

ここまで見えた。

## 既存実装との接続

今回の `SourcePressureBeamDepthTarget` は、前 checkpoint で `IsSourcePressureDepth` の Beam-facing name として入ったものじゃ。
今回追加された 2 本は、それを `SourcePressureMarginInt` の正値と行き来するための API になっている。

つまり現在の Beam 層はこうなった。

```text id="5hmum2"
SourcePressureBeamSeed
  局所 automaton state の Beam 側入口

SourcePressureBeamDepthTarget
  pressure-depth 軸上の target 点

sourcePressureBeamDepthTarget_iff_margin_pos
  target と margin positivity の同値

sourcePressureBeamDepthTarget_of_margin_pos
  margin positivity から target を作る

sourcePressureMargin_pos_of_beamDepthTarget
  target から margin positivity を得る
```

これは小さいが、かなり整った API じゃ。

## True Beam / False Beam / Gap

今回の記録はよい。

## True Beam

True Beam はこの 3 本。

```lean id="sl84m4"
sourcePressureBeamDepthTarget_iff_margin_pos
sourcePressureBeamDepthTarget_of_margin_pos
sourcePressureMargin_pos_of_beamDepthTarget
```

これで、target 側は完全に開閉できる。

## False Beam

今回は新しい False Beam theorem はない。

これは悪くない。
無理に否定 theorem を作らず、まだ関係が足りないものを Gap として扱ったのが正しい。

## Gap

今回の Gap はこれ。

```text id="xgyyab"
seed list L --?--> target depth j
```

この Gap が、次の本丸じゃ。

`SourcePressureBeamSeed L` は witness list 上の automaton state。
`SourcePressureBeamDepthTarget n k r j` は単一 depth 点。
この二つは型として別の世界を見ている。

だから、次に必要なのは、

```text id="pw7jt1"
L の中の witness が j を指している
```

または、

```text id="uwnvj0"
L の中の witness が作る interval address が j を含んでいる
```

のどちらかじゃ。

report でも、この二択が明記されておる。安全な次手は前者、「target depth is the witness value itself」だと整理されている。

## 注意点

まだ言っていないことを確認しておく。

```text id="ng4m7h"
これは transport theorem ではない。
```

```text id="6zg6jk"
これは seed が target に届くことを言っていない。
```

```text id="2v12uw"
これは Beam family を構成していない。
```

```text id="9nvtka"
これは interval union accounting ではない。
```

```text id="xdhlqy"
これは coverage / uniqueness / maximality ではない。
```

```text id="g3e3lz"
これは overlap repair ではない。
```

```text id="x2zse8"
これは Collatz convergence ではない。
```

この境界は守れておる。

## build / no-sorry / diff check

report によると、次は通っている。

```text id="hsikv8"
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
```

pressure 系 no-sorry check は一致なし、`git diff --check` も通過。既知の `ZsigmondyCyclotomicResearch.lean` の既存 `sorry` warning は今回も replay されたが、作業範囲外として扱われている。

## 次の checkpoint 方針

次は、`seed list L --?--> target depth j` の Gap を埋める。

ただし、いきなり transport theorem はまだ早い。
まずは **relation predicate** を作る。

一番安全な候補はこれ。

```lean id="n5enxj"
def SourcePressureBeamSeedContainsDepth
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r))
    (j : ℕ) : Prop :=
  ∃ W ∈ L, W.j = j
```

ただし、`SourcePressureLocalIslandWitness` のフィールド名が本当に `j` かは Lean に聞く必要がある。ここは推測せず、Codex に「#check / 実験で確認せよ」と指示するのがよい。

この relation が通れば、次に試す True Beam は、

```lean id="yjaoum"
theorem sourcePressureBeamDepthTarget_of_seedContainsDepth
```

ではない。
これもまだ足りない可能性がある。

なぜなら、`W.j = j` があっても、`j` が positive margin target であるには、witness 側に `IsSourcePressureDepth` または margin positivity が入っている必要があるからじゃ。

だから次 checkpoint の実験は、

```text id="yji784"
witness から target depth positivity を取り出せるか？
```

を Lean に聞くこと。

## 次の Codex 指示

```text id="ix1ao0"
Checkpoint: petal-204

Main goal:
  Fill the current Gap between a Beam seed witness list `L` and a target depth
  `j` by asking Lean for the smallest explicit seed-to-depth relation.
  Do not prove transport yet.  First define and test the relation.

Primary target file:
  DkMath/Collatz/PetalBridge/PressureBeam.lean

Allowed supporting files:
  docs/dev/das-p2l-260607/review/report-petal-204.md

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

  Grow Core by fixing both True and False observations.  Do not skip useful
  facts because they look obvious.  Ask Lean.

Current Core:
  SourcePressureBeamSeed
  SourcePressureBeamDepthTarget
  sourcePressureBeamDepthTarget_iff_margin_pos
  sourcePressureBeamDepthTarget_of_margin_pos
  sourcePressureMargin_pos_of_beamDepthTarget

Current Gap:
  seed list L --?--> target depth j

Required Lean exploration:
  First inspect the actual fields / constructors of
  `SourcePressureLocalIslandWitness`.

  Use `#check`, `#print`, or small scratch theorems to determine:
    - whether a witness has an explicit depth field;
    - what that field is named;
    - whether the witness directly carries `IsSourcePressureDepth`;
    - whether the witness directly gives
        0 < SourcePressureMarginInt n k (r + j).

Experiment R1:
  Define the weakest relation saying that a seed list contains a witness at
  target depth `j`.

  Candidate shape, adjust field names to actual code:

    def SourcePressureBeamSeedContainsDepth
        {n : OddNat} {k r : ℕ}
        (L : List (SourcePressureLocalIslandWitness n k r))
        (j : ℕ) : Prop :=
      ∃ W ∈ L, <witnessDepth W> = j

  If the witness stores an address rather than a bare depth, name the relation
  accordingly and report the exact field.

Experiment T1:
  If a witness at depth `j` directly implies margin positivity, try to prove:

    theorem sourcePressureBeamDepthTarget_of_seedContainsDepth
        {n : OddNat} {k r j : ℕ}
        {L : List (SourcePressureLocalIslandWitness n k r)}
        (hcontains : SourcePressureBeamSeedContainsDepth L j) :
        SourcePressureBeamDepthTarget n k r j

  Commit this only if Lean proves it without adding hidden global assumptions.

Experiment G1:
  If T1 fails because containment alone is too weak, record the minimal missing
  witness fact:
    - witness contains depth but not positivity;
    - witness contains interval address, not exact depth;
    - target depth must be endpoint / inside interval;
    - or another explicit relation.

Experiment F1:
  Try a deliberately overbroad relation in scratch only:

    SourcePressureBeamSeed L -> SourcePressureBeamDepthTarget n k r j

  Do not commit it.  Record again as Gap unless Lean unexpectedly proves it.

Guardrails:
  Do not add:
    - real transport theorem;
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
    2. Actual field names discovered for `SourcePressureLocalIslandWitness`.
    3. True Beam facts that passed.
    4. False Beam / Gap observations.
    5. Whether `SourcePressureBeamSeedContainsDepth` or another relation was
       added.
    6. Whether any seed-to-target theorem was added.
    7. One-step-ahead Wise Wolf inference.
    8. Experimental lemma table with passed / failed / under-specified.
    9. Explicit statement that no propagation, convergence, coverage,
       aggregation, or overlap repair theorem was added.

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

## 一歩先ゆく推論

次の山は、たぶん二段階になる。

## 第一段

```text id="z6nzeh"
witness list contains exact depth
```

これは list-address relation。

## 第二段

```text id="kx6j7p"
witness depth implies BeamDepthTarget
```

これは target relation。

もし `SourcePressureLocalIslandWitness` が local island 証明を持っているなら、第二段は通る可能性が高い。
もし witness が interval address だけを持つなら、exact depth ではなく、

```text id="dy1k0b"
target depth lies inside interval address
```

が必要になる。

この差が、次の実験でくっきりするはずじゃ。

## まとめ

ぬしの言う通り、状況はくっきりしてきた。

今見えているのは、

```text id="5t8k3z"
Core:
  BeamDepthTarget ↔ margin_pos

True Beam:
  target constructor / target projection

Gap:
  seed list L と target depth j の接続

次実験:
  witness が j をどう持っているか Lean に聞く
```

ここまで明瞭になった。
次は `SourcePressureLocalIslandWitness` の内部を Lean に聞く段階じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
index 9c4a2ff3..74bd5939 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
@@ -108,4 +108,30 @@ theorem sourcePressureBeamDepthTarget_iff_margin_pos
       0 < SourcePressureMarginInt n k (r + j) :=
   isSourcePressureDepth_iff_margin_pos n k r j

+/--
+Construct a Beam depth target from positive source-pressure margin.
+
+This is the True Beam constructor side of
+`sourcePressureBeamDepthTarget_iff_margin_pos`.  It remains local to one
+explicit depth and does not connect any Beam seed to that depth.
+-/
+theorem sourcePressureBeamDepthTarget_of_margin_pos
+    (n : OddNat) (k r j : ℕ)
+    (h : 0 < SourcePressureMarginInt n k (r + j)) :
+    SourcePressureBeamDepthTarget n k r j :=
+  (sourcePressureBeamDepthTarget_iff_margin_pos n k r j).2 h
+
+/--
+Project positive source-pressure margin from a Beam depth target.
+
+This is the True Beam projection side of
+`sourcePressureBeamDepthTarget_iff_margin_pos`.  It is not a propagation
+result; it only opens the target predicate at the same explicit depth.
+-/
+theorem sourcePressureMargin_pos_of_beamDepthTarget
+    (n : OddNat) (k r j : ℕ)
+    (h : SourcePressureBeamDepthTarget n k r j) :
+    0 < SourcePressureMarginInt n k (r + j) :=
+  (sourcePressureBeamDepthTarget_iff_margin_pos n k r j).1 h
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-203.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-203.md
new file mode 100644
index 00000000..0410d1b8
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-203.md
@@ -0,0 +1,229 @@
+# report-petal-203
+
+## Situation Analysis
+
+`petal-203` is the first small Lean experiment checkpoint for the Beam layer.
+
+The current Beam Core before this checkpoint was:
+
+```lean
+SourcePressureBeamSeed
+sourcePressureBeamSeed_of_sortedBeforeFailure
+sourcePressureBeamSeed_recovered_of_sortedBeforeFailure_of_noAdjacentOverlap
+SourcePressureBeamDepthTarget
+sourcePressureBeamDepthTarget_iff_margin_pos
+```
+
+The Beam layer is still intentionally local.  It names a seed state and a
+depth target, but it does not transport a seed to a target.
+
+## Review of What Was Tried
+
+### Experiment T1
+
+Tried and kept:
+
+```lean
+theorem sourcePressureBeamDepthTarget_of_margin_pos
+    (n : OddNat) (k r j : ℕ)
+    (h : 0 < SourcePressureMarginInt n k (r + j)) :
+    SourcePressureBeamDepthTarget n k r j
+```
+
+Result: passed.
+
+This is the constructor side of
+`sourcePressureBeamDepthTarget_iff_margin_pos`.
+
+### Experiment T2
+
+Tried and kept:
+
+```lean
+theorem sourcePressureMargin_pos_of_beamDepthTarget
+    (n : OddNat) (k r j : ℕ)
+    (h : SourcePressureBeamDepthTarget n k r j) :
+    0 < SourcePressureMarginInt n k (r + j)
+```
+
+Result: passed.
+
+This is the projection side of
+`sourcePressureBeamDepthTarget_iff_margin_pos`.
+
+### Experiment G1
+
+Overclaim considered:
+
+```text
+SourcePressureBeamSeed L -> SourcePressureBeamDepthTarget n k r j
+```
+
+Result: Gap / under-specified.
+
+Reason: `SourcePressureBeamSeed L` is a predicate on an explicit witness list
+`L`, while `SourcePressureBeamDepthTarget n k r j` is a predicate at a single
+relative depth `j`.  The current hypotheses do not relate the list `L` to the
+target depth `j`.
+
+This is not recorded as a False Beam theorem, because the statement may become
+true after adding the missing relation.  It is a missing-structure problem.
+
+### Experiment G2
+
+Candidate missing relation:
+
+```lean
+SourcePressureBeamSeedTargetsDepth L n k r j
+```
+
+Result: report-only.
+
+The fields are not yet obvious enough to implement.  A relation of this kind
+must specify how a seed witness list points at, contains, reaches, or justifies
+the target depth.  Those alternatives are different claims, and choosing one
+too early would hard-code a transport interpretation.
+
+## True Beam / False Beam / Gap
+
+### True Beam
+
+The following facts are now part of the Beam Core:
+
+```lean
+sourcePressureBeamDepthTarget_iff_margin_pos
+sourcePressureBeamDepthTarget_of_margin_pos
+sourcePressureMargin_pos_of_beamDepthTarget
+```
+
+Together they form the first complete local target API:
+
+```text
+Target iff margin_pos
+Target of margin_pos
+margin_pos of Target
+```
+
+### False Beam
+
+No new negated theorem was added.
+
+The main overclaim was not proved and not committed, but it is better recorded
+as Gap rather than False Beam because it lacks a required relation instead of
+contradicting current Core.
+
+### Gap
+
+Missing relation:
+
+```text
+seed list L  --?-->  target depth j
+```
+
+Without this relation, a theorem from `SourcePressureBeamSeed L` to
+`SourcePressureBeamDepthTarget n k r j` is under-specified.
+
+## Next Codex Instruction
+
+Do not attempt a direct seed-to-depth transport theorem yet.
+
+Next, design the minimal explicit relation between a Beam seed and a depth
+target.  The first relation should be a predicate, not a theorem.  It should
+avoid coverage, aggregation, uniqueness, maximality, and overlap repair.
+
+Possible names:
+
+```lean
+SourcePressureBeamSeedTargetsDepth
+SourcePressureBeamSeedContainsDepth
+SourcePressureBeamSeedSupportsDepth
+```
+
+Recommended direction: use `TargetsDepth` only if the relation is intended to
+be directional.  Use `ContainsDepth` only if the target depth is literally
+extracted from a witness or interval address.
+
+## One-Step-Ahead Inference from Wise Wolf
+
+The next useful distinction is:
+
+```text
+list-address relation
+  versus
+depth-target relation
+```
+
+The Beam seed currently carries a list of local-island witnesses.  Each witness
+has a value `j` and can be converted to an interval-pulse address.  Therefore
+there are at least two possible target relations:
+
+```text
+1. target depth is the witness value itself
+2. target depth lies inside the interval-pulse address produced by a witness
+```
+
+The second is stronger and closer to propagation/accounting, but it also risks
+introducing interval membership and union reasoning too early.  The safer next
+experiment is the first one: name a relation saying that a depth is one of the
+explicit witness depths in the seed list.
+
+## Experimental Lemmas Requested by Wise Wolf
+
+| Experiment | Statement | Result |
+| --- | --- | --- |
+| T1 | margin positivity constructs a Beam depth target | passed |
+| T2 | Beam depth target projects margin positivity | passed |
+| G1 | arbitrary seed implies arbitrary target depth | under-specified |
+| G2 | minimal seed-to-depth relation | report-only |
+
+## Guardrails Confirmed
+
+This checkpoint did not add:
+
+- a propagation theorem;
+- a convergence theorem;
+- global coverage;
+- aggregation over multiple recovered diagnostics;
+- interval union accounting;
+- overlap repair;
+- arbitrary-list recursive decomposition;
+- canonical first diagnosis;
+- enumeration of all diagnostics;
+- maximality;
+- uniqueness;
+- sorting theorem;
+- disjointness between multiple recovered families.
+
+The added theorems are local True Beam API wrappers around the existing target
+equivalence only.
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
