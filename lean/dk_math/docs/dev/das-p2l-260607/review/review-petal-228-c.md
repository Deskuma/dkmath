# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam.Pulse

gch: 02ba120049179e1faabad2990e894eeb85848e9c

## Report

Branch C も実装実験して、Lean が通しました。

追加した theorem:

```lean
exists_sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_failureResolution
```

場所: [Pulse.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean)

内容はこれです。

```text
SourcePressureFailureResolution L
  -> ∃ W ∈ L, W の singleton pulse に full local diagnostic がある
```

証明は薄く、`SourcePressureBeamSeed` が `SourcePressureFailureResolution` の Beam-facing wrapper なので、前の Branch B theorem をそのまま再利用しています。`PressureAutomaton` 側には Beam vocabulary を入れていません。

[report-petal-227.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-227.md) も更新済み。Branch C は「候補」から「実装済み」に昇格し、次の Gap はより細かく「recovered adjacent pair / overlap branch のどの witness かを保持するか」に移りました。

確認済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
rg -n "sorry|admit" ...PressureBeam + inspected pressure files
git diff --check
```

すべて通過。既知の unrelated warning は `ZsigmondyCyclotomicResearch.lean` の `sorry` だけです。

## Review

## 結論

**採用** じゃ。
そして、これは明確に **戦略の質が上がっている**。

今回の流れは良い。

```text id="o9jxxx"
cp227-a:
  Branch B を発見して seed -> ∃ witness diagnostic を実装

cp227-b:
  revised report として Branch A-F の戦略整理を追加

cp227-c:
  Branch C も実験し、failureResolution -> ∃ witness diagnostic を実装
```

つまり「一つ見つけて終わり」ではなく、

```text id="ufb612"
Branch B が通った
  -> なら Branch C は薄い橋として通るか？
  -> 通った
  -> 次の Gap は branch-specific witness identity へ移った
```

まで進んでいる。
これはかなり良い。  

## 採用対象

最終的には **cp227-c を採用** じゃ。
cp227-a / cp227-b は発展途中、cp227-c が戦略分岐後の完成形と見るのがよい。

追加 theorem は 2 本。

```lean id="r302bw"
exists_sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_seed
```

```lean id="dgd5xv"
exists_sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_failureResolution
```

前者は Branch B。

```text id="z0n4b2"
SourcePressureBeamSeed L
  -> ∃ W ∈ L, W の singleton pulse に full diagnostic
```

後者は Branch C。

```text id="m0zg2p"
SourcePressureFailureResolution L
  -> ∃ W ∈ L, W の singleton pulse に full diagnostic
```

Branch C は、`SourcePressureBeamSeed` が `SourcePressureFailureResolution` の Beam-facing wrapper なので、Branch B theorem をそのまま再利用している。薄いが意味のある caller convenience じゃ。

## 実装レビュー

Branch B の実装は良い。

```lean id="u3ax9c"
rcases exists_sourcePressureBeamSeedContainsDepth_of_seed hseed with
  ⟨_, W, hmem, _⟩
exact
  ⟨W, hmem,
    sourcePressureBeamPulse_witness_singleton_full_diagnostic hmem⟩
```

ここで canonical witness を選んでいない。
seed が既に持っている existential witness を開いて、その witness に full diagnostic を適用しているだけ。

これは安全じゃ。

Branch C も良い。

```lean id="svwsx2"
exact exists_sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_seed h
```

これは wrapper として薄い。
しかし、caller がまだ `SourcePressureFailureResolution L` の表面にいる場合、Beam seed に手動で読み替えなくてよい。
つまり、API としては便利で、依存方向も壊していない。

## 戦略面の評価

今回の最大の成果は、theorem そのものより **Branch 思考が動いたこと**じゃ。

report は、

```text id="zf2wto"
Branch B was taken first
Branch C was then implemented as an experiment
```

と整理している。さらに、Branch C の実装後、次の Gap が

```text id="tbnyd5"
recovered adjacent pair / overlap branch
  -> branch-specific chosen side witness
  -> full diagnostic
```

へ細分化された。

これは良い。
単に「failureResolution から full diagnostic が出た」で止まらず、

```text id="fo2szt"
では、その diagnostic の witness は recovered branch の左なのか右なのか？
overlap branch のどの witness なのか？
```

という次の戦場を見つけている。

## True Beam / Boundary / False Beam / Gap

## True Beam

今回の True Beam はこれ。

```text id="h5pgeo"
SourcePressureBeamSeed L
  -> ∃ W ∈ L, full local singleton diagnostic
```

さらに、

```text id="kgqv0v"
SourcePressureFailureResolution L
  -> ∃ W ∈ L, full local singleton diagnostic
```

まで上がった。

これは、seed / failure resolution の段階から、少なくとも一つの witness diagnostic を得られるという局所的・存在的成果じゃ。

## Boundary

これは existential theorem。
つまり、特定の canonical witness を選ぶものではなく、

```text id="gtggel"
少なくとも一つ存在する
```

という境界に留めている。
ここが安全。

## False Beam

今回、否定 theorem は不要。
無理に obstruction を追加していないのは正しい。

## Gap

新しい Gap はより鋭くなった。

```text id="xnntcl"
failureResolution から full diagnostic は出る

だが、
recovered adjacent pair branch のどの witness か
overlap obstruction branch のどの witness か
までは保持していない
```

これは次の branch-specific theorem の候補じゃ。
ただし、必要になるまで追加しない判断も正しい。

## 注意点

Branch C theorem は便利だが、やや wrapper 色が強い。

```text id="lpffow"
SourcePressureBeamSeed L
```

と

```text id="nueabx"
SourcePressureFailureResolution L
```

が定義的に近いなら、両方の public theorem を持つかどうかは API 判断になる。
今回は「caller が failureResolution 表面にいる場合の convenience」として採用できる。

ただし今後、同じ型の wrapper を増やしすぎると API が膨らむ。
次からは、

```text id="kxatsx"
この theorem が branch identity を保存するか？
それとも単なる表面名の違いか？
```

を見て取捨選択するとよい。

## 次の checkpoint 方針

次は、report の Next Branch 通り、

```text id="et2abx"
branch-specific witness identity
```

を攻めるかどうかじゃ。

ただし、ここも分岐 Goal で行く。

重要なのは、Branch C 一般はもう通った。
次はより精密に、

```text id="xm1vuz"
recovered adjacent pair branch
  -> 左 witness の full diagnostic
  -> 右 witness の full diagnostic
  -> どちらが自然か

overlap obstruction branch
  -> obstruction に含まれる witness の full diagnostic
  -> どれを取り出すべきか
```

を調べる。

## 次の Codex 指示

```text id="qulser"
Checkpoint: petal-228

Primary Goal:
  Refine the cp227 existential diagnostic by investigating whether
  `SourcePressureFailureResolution L` can preserve branch-specific witness
  identity.

Context:
  cp227 established:

    SourcePressureBeamSeed L
      -> ∃ W ∈ L, full local singleton diagnostic

  and:

    SourcePressureFailureResolution L
      -> ∃ W ∈ L, full local singleton diagnostic

  This is useful, but it forgets which branch of the failure resolution supplied
  the witness.

Strategic Branch Goals:

  Branch A: recovered adjacent-pair branch exposes explicit witnesses
    Inspect the recovered / adjacent-pair side of `SourcePressureFailureResolution`.

    If it exposes witnesses A B with membership in L, try to prove one or both:

      recovered branch -> full diagnostic for A
      recovered branch -> full diagnostic for B

    Only add the theorem if the branch identity is preserved clearly.

    Do not choose arbitrarily if both sides are symmetric and no caller needs a
    preferred side.  In that case, report the symmetry.

  Branch B: overlap obstruction branch exposes an explicit witness
    Inspect the overlap-obstruction side.

    If it exposes a witness W ∈ L, try to prove:

      overlap branch -> full diagnostic for W

    If it exposes only existence, keep the theorem existential.
    Do not repair overlap or claim disjointness.

  Branch C: both branches expose witnesses
    If both recovered and overlap branches expose explicit witnesses, add at
    most one theorem per branch, only if the theorem statements remain small.

    Prefer branch-specific theorems that preserve identity over another generic
    existential theorem.

  Branch D: failure resolution hides witness identity
    If `SourcePressureFailureResolution L` only exposes enough to prove the
    existential diagnostic but not branch-specific identity, add no Lean code.

    Report the exact hiding point:
      recovered pair relation?
      overlap obstruction predicate?
      seed existential projection?
      missing membership projection?

  Branch E: obstruction or contradiction found
    If a proposed branch-specific witness cannot be a Beam target or cannot
    feed the singleton pulse diagnostic, record this as False Beam / obstruction.
    Add a negative theorem only if it is local and useful.

Files to inspect:
  DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
  DkMath/Collatz/PetalBridge/PressureBeam/Core.lean
  DkMath/Collatz/PetalBridge/PressureAutomaton.lean
  DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean

Implementation rules:
  Use `#check`, `#print`, and scratch lemmas.
  Let the workspace decide which branch is real.
  Add no more than two small theorems.
  Prefer identity-preserving branch theorems over generic existential wrappers.
  If theorem statements become large or duplicate cp227, stop and report.

Guardrails:
  Do not add:
    - list-wide coverage;
    - witness-family aggregation;
    - arbitrary witness selection;
    - canonical target selection;
    - arbitrary target transport;
    - overlap repair;
    - propagation;
    - Collatz convergence.

Dependency guardrail:
  Do not make lower diagnostic modules import PressureBeam.
  Put any Beam-facing bridge in PressureBeam/Pulse.lean or another upper
  Beam-facing module.

Report requirements:
  - State which Branch was taken.
  - State which branches were inspected but not taken.
  - If theorem added, state which witness identity it preserves.
  - If no theorem added, identify the precise hiding/missing relation.
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

ここからは、単なる存在補題ではなく **由来付き witness** が欲しい。

今は、

```text id="zdbxka"
failureResolution
  -> どこかの W
  -> full diagnostic
```

まで来た。

次に欲しいのは、

```text id="pjs67i"
recovered adjacent pair の左 W
  -> full diagnostic

recovered adjacent pair の右 W
  -> full diagnostic

overlap obstruction の witness
  -> full diagnostic
```

のような branch identity じゃ。

ただし、これは必要になった時だけでよい。
API を膨らませすぎると、せっかくの分割後 Pulse が重くなる。

## 総合判断

今回の三段ファイル提出は、戦略の質向上として成功じゃ。

```text id="l65tz2"
単発 Goal
  から
Branch B
  さらに
Branch C
  そして
次の branch-specific Gap
```

へ進んだ。

これでよい。
この形で次も進めよう。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
index 414503d4..36d77a15 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
@@ -247,5 +247,40 @@ theorem exists_sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_seed
     ⟨W, hmem,
       sourcePressureBeamPulse_witness_singleton_full_diagnostic hmem⟩
 
+/--
+Failure resolution also exposes one witness whose singleton pulse has the full
+local entry-depth-exit diagnostic.
+
+This is the cp227-r1 Branch C experiment.  It is intentionally placed in the
+Beam-facing Pulse layer, not in `PressureAutomaton`: lower diagnostic and
+automaton modules must not import Beam vocabulary.
+
+The proof is deliberately thin.  `SourcePressureBeamSeed` is the Beam-facing
+name for `SourcePressureFailureResolution`, so this theorem only enters the
+seed bridge and reuses the Branch B theorem above.  It does not add a new
+failure-resolution decomposition, choose a canonical witness, repair overlap,
+or claim list coverage.
+-/
+theorem exists_sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_failureResolution
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h : SourcePressureFailureResolution L) :
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
+  exact exists_sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_seed h
+
 
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-227.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-227.md
index 2721b8e5..563453cd 100644
--- a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-227.md
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-227.md
@@ -24,9 +24,9 @@ and packages the local singleton pulse diagnostic:
 - center/right: `SourcePressureBeamAddressedDepthTarget L ...`;
 - exit: `right <= left`.
 
-## Branch Taken
+## Branches Taken
 
-Branch B was taken:
+Branch B was taken first:
 
 ```text
 caller exists but only has Beam seed
@@ -60,6 +60,15 @@ and `SourcePressureBeamSeedContainsDepth L j` unfolds to:
 
 So the seed can safely feed the full diagnostic existentially.
 
+Branch C was then implemented as an experiment:
+
+```text
+failure resolution -> Beam seed wrapper -> existential witness diagnostic
+```
+
+This is valid because `SourcePressureBeamSeed L` is definitionally the
+Beam-facing name for `SourcePressureFailureResolution L`.
+
 ## Added Theorem
 
 Added in `DkMath.Collatz.PetalBridge.PressureBeam.Pulse`:
@@ -87,6 +96,26 @@ It does not rebuild the pulse facts manually.  It opens the seed existential,
 keeps the extracted witness explicit, and applies the full diagnostic package
 to that witness membership.
 
+Also added:
+
+```lean
+theorem exists_sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_failureResolution
+```
+
+Meaning:
+
+```text
+SourcePressureFailureResolution L
+  -> exists W in L
+       such that W's singleton pulse has the full local entry-depth-exit
+       diagnostic.
+```
+
+This theorem intentionally stays in the Beam-facing Pulse layer.  It does not
+move Beam vocabulary into `PressureAutomaton`; it only lets a caller that still
+has the automaton/failure-resolution state enter the same existential
+diagnostic surface.
+
 ## Branches Inspected But Not Taken
 
 Branch A:
@@ -95,21 +124,12 @@ Branch A:
 - The Pulse API itself has explicit-membership theorems, but adding another
   direct alias there would only duplicate the cp226 theorem.
 
-Branch C:
-
-- `PressureAutomaton` exposes `SourcePressureFailureResolution L`, with either
-  a recovered adjacent pair or an overlap obstruction.
-- The recovered branch gives an adjacent-pair relation, and the overlap branch
-  is list-addressed, but the clean exposed Beam-facing route is already
-  mediated by `SourcePressureBeamSeed`.
-- A direct failure-resolution theorem may be useful later, but it would be a
-  higher duplicate of the seed route unless a caller specifically works before
-  entering Beam seed vocabulary.
-
 Branch D:
 
 - Multiple possible caller surfaces exist, but the seed route is the smallest
   one with the fewest new assumptions after explicit `W ∈ L`.
+- Branch C was still added as a caller convenience for code that has not yet
+  switched to Beam seed vocabulary.
 
 Branch E:
 
@@ -126,6 +146,8 @@ True Beam:
 - `W ∈ L -> full local singleton diagnostic` is already proved by cp226.
 - `SourcePressureBeamSeed L -> ∃ W ∈ L, full local singleton diagnostic` is now
   proved by cp227-r1.
+- `SourcePressureFailureResolution L -> ∃ W ∈ L, full local singleton
+  diagnostic` is also proved by the Branch C experiment.
 
 Boundary:
 
@@ -140,17 +162,19 @@ False Beam:
 
 Gap:
 
-- A direct automaton-level bridge from
-  `SourcePressureFailureResolution L` to the full diagnostic may be possible,
-  but it is currently unnecessary because `SourcePressureBeamSeed L` is exactly
-  the Beam-facing wrapper of that state.
-- If a future caller must stay at `PressureAutomaton` level, the missing bridge
-  to inspect is:
+- The direct automaton/failure-resolution bridge is no longer missing at the
+  existential diagnostic level.
+- The remaining gap is more specific:
 
 ```text
-failure/obstruction branch -> explicit W ∈ L -> full diagnostic
+recovered adjacent pair / overlap branch
+  -> branch-specific chosen side witness
+  -> full diagnostic
 ```
 
+That would be stronger documentation for a particular branch, but it should not
+be added unless a caller needs the branch-specific witness identity.
+
 ## Dependency Direction
 
 No dependency inversion was introduced.
@@ -165,7 +189,7 @@ No lower diagnostic module imports `PressureBeam`.
 
 ## Guardrails
 
-The new theorem does not claim:
+The new theorems do not claim:
 
 - list-wide coverage;
 - witness-family aggregation;
@@ -176,8 +200,8 @@ The new theorem does not claim:
 - propagation;
 - Collatz convergence.
 
-It is local explicit-witness API consumption, lifted existentially from the
-Beam seed.
+They are local explicit-witness API consumption, lifted existentially from the
+Beam seed and then from the failure-resolution wrapper.
 
 ## Verification
 
@@ -210,16 +234,21 @@ declaration uses `sorry`
 
 ## Next Branch To Attack
 
-The next useful branch is Branch C, but only if a caller needs to remain at the
-automaton/failure-resolution level.
+The next useful branch is no longer the generic Branch C bridge; that now
+exists.
 
-Candidate future theorem:
+The next precise branch is branch-specific witness identity:
 
 ```text
-SourcePressureFailureResolution L
-  -> exists W in L
-       such that W's singleton pulse has the full local diagnostic
+recovered adjacent pair branch
+  -> left witness A in L
+  -> full diagnostic for A
+
+overlap obstruction branch
+  -> one obstruction witness in L
+  -> full diagnostic for that witness
 ```
 
-This should be added only when it removes real caller noise.  For current Beam
-work, the seed theorem is the cleaner public surface.
+This should only be attacked if a caller needs to preserve which side of the
+failure-resolution branch produced the diagnostic.  Otherwise the new
+failure-resolution existential theorem is enough and keeps the API smaller.
````
`````
