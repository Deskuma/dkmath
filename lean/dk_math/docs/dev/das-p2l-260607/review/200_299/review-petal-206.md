# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam

gch: 39816079771dbafb3ebad511fc86d06868f14db5

## Report

cp205 完了です。

[PressureBeam.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean) に、raw `SourcePressureBeamSeed L` から存在的に depth target を抽出する補題群を追加しました。

追加した主な theorem:

- `sourcePressureBeamSeedContainsDepth_of_adjacentPairInList_left`
- `exists_sourcePressureBeamSeedContainsDepth_of_adjacentOverlapObstruction`
- `exists_sourcePressureBeamSeedContainsDepth_of_seed`
- `exists_sourcePressureBeamDepthTarget_of_seed`
- `exists_sourcePressureBeamSeedContainsDepth_and_target_of_seed`

ポイントは、任意の `j` への target transport ではなく、seed 内の明示 witness から `∃ j` を取り出す形に閉じたことです。Overlap branch も list-addressed だったので、Gap ではなく True Beam として通りました。

レポートも追加しました:
[report-petal-205.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-205.md)

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureBeam` passed
- `lake build DkMath.Collatz.PetalBridge` passed
- 指定 pressure files の `sorry/admit` check: no matches
- `git diff --check` passed

既知の unrelated warning として `ZsigmondyCyclotomicResearch.lean` の既存 `sorry` warning は残っています。

## Review

## 結論

**採用** じゃ。
cp205 はかなり大きい。

今回、ついに Beam は単なる target 名から一歩進んで、**raw seed から存在的 depth target を抽出できる** ところまで Lean が通した。

追加された主 theorem は次。

```lean id="3xvcv8"
sourcePressureBeamSeedContainsDepth_of_adjacentPairInList_left

exists_sourcePressureBeamSeedContainsDepth_of_adjacentOverlapObstruction

exists_sourcePressureBeamSeedContainsDepth_of_seed

exists_sourcePressureBeamDepthTarget_of_seed

exists_sourcePressureBeamSeedContainsDepth_and_target_of_seed
```

ポイントはここじゃ。

```text id="e31k94"
任意の j への transport ではない。
しかし、seed が内包する witness から ∃ j を抽出できる。
```

これは **Gap が True Beam に変わった** と見てよい。
特に overlap branch も list-addressed だったため、Gap ではなく True Beam として通った点が大きい。

## 実装レビュー

良い実装じゃ。

まず recovered branch では、隣接 pair の left witness から depth を取り出している。

```lean id="4fbz8v"
theorem sourcePressureBeamSeedContainsDepth_of_adjacentPairInList_left
```

これは `SourcePressureLocalIslandWitnessAdjacentPairInList L A B` から `A.val` が `L` に含まれることを示す list-address projection じゃ。
canonical pair を選んでいない。all pair enumeration もしていない。安全。

次に overlap branch でも、少なくとも一つの contained depth が取れることを示している。

```lean id="tc74hx"
theorem exists_sourcePressureBeamSeedContainsDepth_of_adjacentOverlapObstruction
```

これは重要じゃ。
overlap は repair されていないが、**obstruction branch も list-addressed である**ことが Lean で固定された。
つまり overlap は「情報が消える枝」ではなく、「少なくとも witness depth を持つ枝」として Core に乗った。

そして raw seed から、

```lean id="hhlpt2"
theorem exists_sourcePressureBeamSeedContainsDepth_of_seed
```

が通った。

さらに、

```lean id="f2hal0"
theorem exists_sourcePressureBeamDepthTarget_of_seed
```

が通った。

これは Beam の最初の存在的 target extraction じゃ。
伝播 theorem ではないが、Beam seed が空虚でない target を持つことは Lean が認めた。

最後に paired statement。

```lean id="27ntw3"
theorem exists_sourcePressureBeamSeedContainsDepth_and_target_of_seed
```

同じ `j` について containment と target を同時に持つ。
これは今後の API にとても使いやすい。

## 数学的意味

今回で、Beam は次の段階へ入った。

以前は、

```text id="br6i7f"
SourcePressureBeamSeed L
```

は単に local failure-resolution の Beam-facing name だった。

今は、

```text id="8izihp"
SourcePressureBeamSeed L
  -> ∃ j, SourcePressureBeamSeedContainsDepth L j
  -> ∃ j, SourcePressureBeamDepthTarget n k r j
```

まで行ける。

つまり Beam seed は、少なくとも一つの depth target を持つ。
これは小さいが、概念的には大きい。

DkMath 語彙ではこうじゃ。

```text id="dfavqb"
Core:
  seed は addressed witness data を含む

True Beam:
  seed から存在的 depth target が抽出できる

Gap:
  seed から任意の外部 j へ target は出ない
```

この区別が極めて重要じゃ。

## True Beam / False Beam / Gap

## True Beam

今回の True Beam は強い。

```text id="g3rov1"
Recovered branch:
  adjacent pair in list -> contained depth
```

```text id="9ms9a5"
Overlap branch:
  adjacent overlap obstruction -> exists contained depth
```

```text id="ec7tim"
Raw seed:
  seed -> exists contained depth
```

```text id="4z4eae"
Raw seed:
  seed -> exists Beam depth target
```

```text id="g52sbu"
Raw seed:
  seed -> exists j, containedDepth L j ∧ depthTarget j
```

ここまで通った。
これは、Beam seed が空の飾りではなく、実際に pressure-depth 軸上の target へ接続できることを示している。

## False Beam

今回も negated theorem はなし。
ただし、これは問題ではない。

## Gap

残る Gap は明確じゃ。

```text id="uc3ecp"
SourcePressureBeamSeed L
  -> SourcePressureBeamDepthTarget n k r j
```

任意の `j` へは行けない。
存在的に `j` が出るだけじゃ。

これは report でも「known Gap remains」として明確に記録されている。

## ここでかなり状況が変わった

以前は、

```text id="12u26f"
seed と target の間に relation がない
```

だった。

cp204 で、

```text id="2ymuml"
containsDepth -> target
```

が通った。

cp205 で、

```text id="zrqetz"
seed -> exists containsDepth
```

と

```text id="3cmf2y"
seed -> exists target
```

が通った。

つまり、Beam の入口はこう閉じた。

```text id="w33g8n"
seed
  -> addressed existential depth
  -> depth target
```

これは **存在的 Beam seed target extraction** と呼んでよい。

## 注意点

まだ言っていないこと。

```text id="pwuina"
任意 depth への target transport ではない。
```

```text id="sbof5b"
time/orbit propagation ではない。
```

```text id="p08rk1"
Beam family の aggregation ではない。
```

```text id="b6zja8"
interval union accounting ではない。
```

```text id="eq7th3"
overlap repair ではない。
```

```text id="lcrkfv"
coverage / maximality / uniqueness ではない。
```

```text id="bulum7"
Collatz convergence ではない。
```

この境界は守れておる。

## 次の checkpoint 方針

report の一歩先推論にある通り、次は paired existential を thin carrier として名前付けするのがよい。

候補はこれ。

```lean id="gktq44"
def SourcePressureBeamAddressedDepthTarget
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r))
    (j : ℕ) : Prop :=
  SourcePressureBeamSeedContainsDepth L j ∧
    SourcePressureBeamDepthTarget n k r j
```

そして wrapper theorem。

```lean id="fmldgb"
theorem exists_sourcePressureBeamAddressedDepthTarget_of_seed
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hseed : SourcePressureBeamSeed L) :
    ∃ j, SourcePressureBeamAddressedDepthTarget L j
```

これは新しい強主張ではなく、既に通った paired theorem の API 包装じゃ。

ただし、ここでも `coverage` や `canonical selection` には行かない。

## 次の Codex 指示

```text id="8ehlaa"
Checkpoint: petal-206

Main goal:
  Package the paired existential Beam target extraction as a named addressed
  carrier.  This checkpoint should not add new propagation strength.  It should
  give a reusable API name to the already proved fact:
    seed -> exists j, containsDepth L j ∧ depthTarget j

Primary target file:
  DkMath/Collatz/PetalBridge/PressureBeam.lean

Allowed supporting files:
  docs/dev/das-p2l-260607/review/report-petal-206.md

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
    under-specified statements where a relation is missing.

  Grow Core by fixing both True and False observations.  Do not merely inspect
  code; ask Lean small questions.

Current Core:
  SourcePressureBeamSeed
  SourcePressureBeamDepthTarget
  SourcePressureBeamSeedContainsDepth
  sourcePressureBeamDepthTarget_of_seedContainsDepth
  exists_sourcePressureBeamSeedContainsDepth_of_seed
  exists_sourcePressureBeamDepthTarget_of_seed
  exists_sourcePressureBeamSeedContainsDepth_and_target_of_seed

Current known Gap:
  SourcePressureBeamSeed L -> SourcePressureBeamDepthTarget n k r j
  for arbitrary external `j`.

Required implementation:

  Define a named addressed target carrier:

    def SourcePressureBeamAddressedDepthTarget
        {n : OddNat} {k r : ℕ}
        (L : List (SourcePressureLocalIslandWitness n k r))
        (j : ℕ) : Prop :=
      SourcePressureBeamSeedContainsDepth L j ∧
        SourcePressureBeamDepthTarget n k r j

  Add projection helpers:

    theorem sourcePressureBeamSeedContainsDepth_of_addressedDepthTarget
        ...
        (h : SourcePressureBeamAddressedDepthTarget L j) :
        SourcePressureBeamSeedContainsDepth L j

    theorem sourcePressureBeamDepthTarget_of_addressedDepthTarget
        ...
        (h : SourcePressureBeamAddressedDepthTarget L j) :
        SourcePressureBeamDepthTarget n k r j

  Add constructor helper:

    theorem sourcePressureBeamAddressedDepthTarget_mk
        ...
        (hcontains : SourcePressureBeamSeedContainsDepth L j)
        (htarget : SourcePressureBeamDepthTarget n k r j) :
        SourcePressureBeamAddressedDepthTarget L j

  Add existential extraction from seed:

    theorem exists_sourcePressureBeamAddressedDepthTarget_of_seed
        {n : OddNat} {k r : ℕ}
        {L : List (SourcePressureLocalIslandWitness n k r)}
        (hseed : SourcePressureBeamSeed L) :
        ∃ j, SourcePressureBeamAddressedDepthTarget L j

    Proof strategy:
      use `exists_sourcePressureBeamSeedContainsDepth_and_target_of_seed`.

Experimental checks:
  T1:
    Confirm the carrier projections pass.

  T2:
    Confirm the carrier constructor passes.

  T3:
    Confirm seed -> exists addressed carrier passes.

  G1:
    In scratch only, retry arbitrary target:
      SourcePressureBeamSeed L -> SourcePressureBeamAddressedDepthTarget L j
    This should remain Gap because arbitrary `j` is not selected by seed.

Guardrails:
  Do not add:
    - arbitrary target transport;
    - canonical target selection;
    - propagation over time or orbit;
    - convergence theorem;
    - global coverage;
    - arbitrary-list recursive decomposition;
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
    2. What carrier was added.
    3. True Beam facts that passed.
    4. False Beam / Gap observations.
    5. Confirmation that this is packaging, not new propagation.
    6. One-step-ahead Wise Wolf inference.
    7. Experimental lemma table with passed / failed / under-specified.
    8. Explicit statement that no arbitrary target transport, canonical
       selection, propagation, convergence, coverage, aggregation, or overlap
       repair theorem was added.

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

次の次は、carrier を作ったあとに、おそらくこうなる。

```text id="j42ypd"
AddressedDepthTarget
  -> margin_pos
```

これは projection 合成で通るはず。

候補 theorem。

```lean id="g2s31l"
theorem sourcePressureMargin_pos_of_addressedDepthTarget
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureBeamAddressedDepthTarget L j) :
    0 < SourcePressureMarginInt n k (r + j)
```

これは `sourcePressureBeamDepthTarget_of_addressedDepthTarget` と `sourcePressureMargin_pos_of_beamDepthTarget` の合成。

この theorem は自明だが、DkMath 哲学では固定してよい。
なぜなら addressed carrier から実際の pressure margin positivity を取り出す命令語になるからじゃ。

## 総合判断

cp205 で、Beam はかなり具体化した。

```text id="twg7c5"
local seed
  -> exists addressed depth
  -> exists target
```

ここまで Lean が通った。

次はこれを carrier に包む。
そのあと、carrier から margin positivity を取り出す。
その先でようやく「この target が次のどこへ動くか」という transport に入る。

いまは順調じゃ。Core が育っておる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
index 97a54952..66f7c7b1 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
@@ -166,4 +166,109 @@ theorem sourcePressureBeamDepthTarget_of_seedContainsDepth
   subst hdepth
   exact W.property.2.1

+/--
+An addressed adjacent pair in a witness list exposes the left witness depth as
+contained in that list.
+
+This is a list-address projection.  It does not choose a canonical adjacent
+pair and does not aggregate over all adjacent pairs.
+-/
+theorem sourcePressureBeamSeedContainsDepth_of_adjacentPairInList_left
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {A B : SourcePressureLocalIslandWitness n k r}
+    (hin : SourcePressureLocalIslandWitnessAdjacentPairInList L A B) :
+    SourcePressureBeamSeedContainsDepth L A.val := by
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
+            exact ⟨A, by simp [hA], rfl⟩
+          · rcases ih htail with ⟨W, hmem, hdepth⟩
+            exact ⟨W, by simp [hmem], hdepth⟩
+
+/--
+An adjacent-overlap obstruction in a witness list still exposes at least one
+explicit witness depth from that list.
+
+This is not overlap repair.  It only records that the obstruction branch is
+also list-addressed, so an existential depth can be extracted.
+-/
+theorem exists_sourcePressureBeamSeedContainsDepth_of_adjacentOverlapObstruction
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hobs : SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
+    ∃ j, SourcePressureBeamSeedContainsDepth L j := by
+  induction L with
+  | nil =>
+      exact False.elim hobs
+  | cons W1 rest ih =>
+      cases rest with
+      | nil =>
+          exact False.elim hobs
+      | cons W2 rest =>
+          rcases hobs with _hhead | htail
+          · exact ⟨W1.val, W1, by simp, rfl⟩
+          · rcases ih htail with ⟨j, W, hmem, hdepth⟩
+            exact ⟨j, W, by simp [hmem], hdepth⟩
+
+/--
+A raw Beam seed contains at least one explicit witness depth.
+
+This is the first existential target-extraction fact from the Beam seed state.
+It is still not arbitrary target transport: the depth is produced
+existentially from the addressed recovered or overlap branch.
+-/
+theorem exists_sourcePressureBeamSeedContainsDepth_of_seed
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hseed : SourcePressureBeamSeed L) :
+    ∃ j, SourcePressureBeamSeedContainsDepth L j := by
+  unfold SourcePressureBeamSeed at hseed
+  unfold SourcePressureFailureResolution at hseed
+  rcases hseed with hrecovered | hobs
+  · rcases hrecovered with ⟨A, B, hin, _hdiag⟩
+    exact ⟨A.val, sourcePressureBeamSeedContainsDepth_of_adjacentPairInList_left hin⟩
+  · exact exists_sourcePressureBeamSeedContainsDepth_of_adjacentOverlapObstruction hobs
+
+/--
+A raw Beam seed produces some Beam depth target.
+
+The target depth is existentially extracted from the seed's addressed witness
+data.  This theorem deliberately does not say that an arbitrary depth is a
+target.
+-/
+theorem exists_sourcePressureBeamDepthTarget_of_seed
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hseed : SourcePressureBeamSeed L) :
+    ∃ j, SourcePressureBeamDepthTarget n k r j := by
+  rcases exists_sourcePressureBeamSeedContainsDepth_of_seed hseed with
+    ⟨j, hcontains⟩
+  exact ⟨j, sourcePressureBeamDepthTarget_of_seedContainsDepth hcontains⟩
+
+/--
+A raw Beam seed produces an explicit contained depth together with the
+corresponding Beam depth target.
+
+This pairs the list-address relation and the target relation for the same
+existential depth.
+-/
+theorem exists_sourcePressureBeamSeedContainsDepth_and_target_of_seed
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hseed : SourcePressureBeamSeed L) :
+    ∃ j,
+      SourcePressureBeamSeedContainsDepth L j ∧
+        SourcePressureBeamDepthTarget n k r j := by
+  rcases exists_sourcePressureBeamSeedContainsDepth_of_seed hseed with
+    ⟨j, hcontains⟩
+  exact ⟨j, hcontains, sourcePressureBeamDepthTarget_of_seedContainsDepth hcontains⟩
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-205.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-205.md
new file mode 100644
index 00000000..9456fa8a
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-205.md
@@ -0,0 +1,203 @@
+# report-petal-205
+
+## Situation
+
+Checkpoint `petal-205` asked whether a raw `SourcePressureBeamSeed L`
+contains at least one explicit depth target.
+
+The important boundary is:
+
+```text
+SourcePressureBeamSeed L
+  -> exists contained witness depth
+  -> exists Beam depth target
+```
+
+This is existential extraction from already supplied witness data.  It is not
+arbitrary target transport.
+
+## Lean Experiments
+
+### T1: raw seed contains some explicit witness depth
+
+Implemented:
+
+```lean
+theorem exists_sourcePressureBeamSeedContainsDepth_of_seed
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hseed : SourcePressureBeamSeed L) :
+    ∃ j, SourcePressureBeamSeedContainsDepth L j
+```
+
+Result: passed.
+
+The proof splits `SourcePressureFailureResolution` into recovered and overlap
+branches.
+
+### T2: raw seed gives some Beam depth target
+
+Implemented:
+
+```lean
+theorem exists_sourcePressureBeamDepthTarget_of_seed
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hseed : SourcePressureBeamSeed L) :
+    ∃ j, SourcePressureBeamDepthTarget n k r j
+```
+
+Result: passed.
+
+This uses T1 plus `sourcePressureBeamDepthTarget_of_seedContainsDepth`.
+
+### T3: paired contained-depth and target statement
+
+Implemented:
+
+```lean
+theorem exists_sourcePressureBeamSeedContainsDepth_and_target_of_seed
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hseed : SourcePressureBeamSeed L) :
+    ∃ j,
+      SourcePressureBeamSeedContainsDepth L j ∧
+        SourcePressureBeamDepthTarget n k r j
+```
+
+Result: passed.
+
+This fixes the same existential depth on both the list-address side and target
+side.
+
+## Branch Analysis
+
+Recovered branch:
+
+```text
+SourcePressureLocalIslandWitnessAdjacentPairInList L A B
+  -> SourcePressureBeamSeedContainsDepth L A.val
+```
+
+Implemented helper:
+
+```lean
+theorem sourcePressureBeamSeedContainsDepth_of_adjacentPairInList_left
+```
+
+The left witness of the addressed adjacent pair is enough to expose an exact
+depth contained in `L`.
+
+Overlap branch:
+
+```text
+SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
+  -> exists contained depth
+```
+
+Implemented helper:
+
+```lean
+theorem exists_sourcePressureBeamSeedContainsDepth_of_adjacentOverlapObstruction
+```
+
+The obstruction predicate is recursive over adjacent list pairs, so the head
+overlap branch exposes the first witness depth, and the tail branch lifts the
+recursive witness back into the larger list.
+
+## True Beam Facts
+
+| theorem | status | meaning |
+| --- | --- | --- |
+| `sourcePressureBeamSeedContainsDepth_of_adjacentPairInList_left` | passed | an addressed recovered pair exposes the left witness depth |
+| `exists_sourcePressureBeamSeedContainsDepth_of_adjacentOverlapObstruction` | passed | an adjacent-overlap obstruction still exposes some listed depth |
+| `exists_sourcePressureBeamSeedContainsDepth_of_seed` | passed | raw seed contains some explicit witness depth |
+| `exists_sourcePressureBeamDepthTarget_of_seed` | passed | raw seed produces some Beam depth target |
+| `exists_sourcePressureBeamSeedContainsDepth_and_target_of_seed` | passed | same existential depth carries both containment and target facts |
+
+## False Beam / Gap
+
+The known Gap remains:
+
+```text
+SourcePressureBeamSeed L -> SourcePressureBeamDepthTarget n k r j
+```
+
+for arbitrary `j`.
+
+The implemented theorems do not try to prove this.  The data in a raw seed only
+selects existential witness depths from `L`; it does not identify every external
+depth as a target.
+
+No new negated theorem was needed in this checkpoint.
+
+## Guardrails Kept
+
+No theorem was added for:
+
+- arbitrary target transport;
+- propagation over time or orbit;
+- convergence;
+- global coverage;
+- arbitrary-list recursive decomposition;
+- canonical first diagnosis;
+- enumeration of all diagnostics;
+- aggregation over multiple recovered diagnostics;
+- interval union accounting;
+- overlap repair;
+- maximality;
+- uniqueness;
+- sorting;
+- disjointness between multiple recovered families.
+
+## One-Step-Ahead Inference
+
+The next safe surface is an addressed existential target carrier, for example:
+
+```text
+SourcePressureBeamSeed L
+  -> exists j, SourcePressureBeamSeedContainsDepth L j
+               and SourcePressureBeamDepthTarget n k r j
+```
+
+This checkpoint already proves that theorem directly.  The next useful layer
+should therefore avoid re-proving the same fact and instead decide whether a
+named structure or predicate is worth adding around this paired existential.
+
+A safe candidate would be a thin addressed carrier, not an aggregation layer:
+
+```lean
+def SourcePressureBeamAddressedDepthTarget
+    (L : List (SourcePressureLocalIslandWitness n k r)) (j : ℕ) : Prop :=
+  SourcePressureBeamSeedContainsDepth L j ∧
+    SourcePressureBeamDepthTarget n k r j
+```
+
+That would be an API convenience only.  It should not claim coverage, canonical
+selection, overlap repair, or list-wide accounting.
+
+## Verification
+
+Commands run:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureBeam
+lake build DkMath.Collatz.PetalBridge
+rg -n "\bsorry\b|admit" DkMath/Collatz/PetalBridge/PressureBeam.lean ...
+git diff --check
+```
+
+Results:
+
+- `lake build DkMath.Collatz.PetalBridge.PressureBeam`: passed.
+- `lake build DkMath.Collatz.PetalBridge`: passed.
+- no-sorry check over the requested pressure files: no matches.
+- `git diff --check`: passed.
+
+Known unrelated build warning remains:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
+
````
`````
