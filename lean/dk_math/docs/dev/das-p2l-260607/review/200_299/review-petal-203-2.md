# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam

gch: f38dcec6ebb847bf3d9153f25f9d8dbdb7f45dae

## Report

cp202 を提案どおり続行して実装しました。

[PressureBeam.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean) に追加:

- `SourcePressureBeamDepthTarget`
- `sourcePressureBeamDepthTarget_iff_margin_pos`

これは `IsSourcePressureDepth` と `isSourcePressureDepth_iff_margin_pos` の Beam-facing な名前付けです。`SourcePressureBeamSeed L -> SourcePressureBeamDepthTarget ...` のような transport theorem はまだ置いていません。seed と depth target の関係が明示されていないため、ここで止めるのが正しい境界です。

[report-petal-202.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-202.md) も、監査のみから実装続行済みの内容に同期しました。

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureBeam` passed
- `lake build DkMath.Collatz.PetalBridge` passed
- pressure 系 no-sorry check は一致なし
- `git diff --check` passed

既知の `ZsigmondyCyclotomicResearch.lean` の既存 `sorry` warning は今回も replay されましたが、作業範囲外です。

## Review

## 了解。方針を修正する

うむ、ぬしの指摘は正しい。
わっちが少し「構造を眺めて安全側に止める」へ寄りすぎていた。

ここからは、DkMath / Collatz PetalBridge の作業スタイルを次に戻す。

```text id="h8o9my"
状況分析
レビュー
解説
次の Codex 指示
一歩先ゆく推論
賢狼が試してほしい実験補題
```

そして、判断はなるべく Lean に聞く。

```text id="i2kbmc"
推測で止めない。
小さな theorem / lemma / def を試す。
通ったものを True Beam として固定する。
通らない・主張が足りない・反例が見えるものを False Beam / Gap として記録する。
```

## DkMath 哲学としての Beams

忘れぬよう、ここを今後の Codex 指示にも入れる。

DkMath の **Beams** は単なる伝播線ではない。
**Beam x2** じゃ。

```text id="pxxe4q"
Core:
  Lean が認めた事実

True Beam:
  Core から真として伸びる観測事実

False Beam:
  Core から偽・未成立・ obstruction として伸びる観測事実

Gap:
  True / False のどちらにもまだ固定できない未解明領域
```

この True / False Beams を積むことで、事実の Core が太る。
その結果、Gap は必然的に小さくなる。

これはとても大事じゃ。
今後は「自明そうだから省略」ではなく、**自明でも Lean で固定する**。
特に Collatz のような機械語解析では、小さな True / False の固定が命令表になる。

## cp202 のレビュー

今回の `review-petal-203-1.md` は audit-only 版で、最初の Beam 軸として pressure-depth index が最も安全だと結論している。理由は、`PressureDecay` の `r + j` / net-drop / pulse、`PressureFrontier` の `IsSourcePressureDepth`、`PressureAccounting` の `start/len` がすでに depth 軸で揃っているからじゃ。

その後の `review-petal-203-2.md` では、audit 結果に従って実装まで進めている。`PressureBeam.lean` に次を追加しておる。

```lean id="adzr9c"
def SourcePressureBeamDepthTarget

theorem sourcePressureBeamDepthTarget_iff_margin_pos
```

これは `IsSourcePressureDepth` と `isSourcePressureDepth_iff_margin_pos` の Beam-facing な名前付けで、`SourcePressureBeamSeed L -> SourcePressureBeamDepthTarget ...` のような transport theorem はまだ置いていない。seed と depth target の関係が未指定なので、ここで止めた判断は正しい。

## 判定

**採用** じゃ。

理由は次。

```text id="38mcrk"
pressure-depth 軸を Beam の最初の target axis として固定した
```

```text id="6e78jr"
SourcePressureBeamDepthTarget は既存 IsSourcePressureDepth の薄い Beam-facing 名である
```

```text id="ztaxm6"
margin positivity への同値補題も既存 theorem の wrapper に留まっている
```

```text id="d2u6mr"
seed -> target transport は未指定なので追加していない
```

```text id="w0d3ii"
build / no-sorry / git diff check が通っている
```

これは安全で、かつ一歩進んでいる。

## ここからの次手は「実験補題 checkpoint」

次は report-only ではなく、Lean に聞く checkpoint にするのがよい。

ただし、危険な theorem を本体に残さない。
Codex にはこう指示する。

```text id="m6bb7z"
実験補題を小さく試す。
通ったものだけ本実装に残す。
通らなかったものは report に False Beam / Gap として記録する。
```

Lean で「False」を固定する方法は二種類ある。

```text id="seyxjw"
1. 反例や否定 theorem として Lean で証明できる False Beam
```

```text id="9v6cq7"
2. まだ statement の入力が足りず、証明対象にしてはいけない Gap
```

後者を「Lean theorem として失敗したから偽」とは言わない。
そこは慎重に、

```text id="tt8m34"
under-specified
missing relation
not yet a theorem
```

として report に記録する。

## 次の Codex 指示

```text id="tv3kai"
Checkpoint: petal-203

Main goal:
  Run a small Lean experiment checkpoint for the first Beam layer.
  Do not merely inspect code.  Ask Lean which tiny Beam facts are already true.
  Keep passed facts as True Beam facts.  Record failed or under-specified
  statements as False Beam / Gap observations in the report, but do not commit
  failing Lean code.

Primary target file:
  DkMath/Collatz/PetalBridge/PressureBeam.lean

Allowed supporting files:
  docs/dev/das-p2l-260607/review/report-petal-203.md

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
    observations that Lean proves from the current Core.

  False Beam:
    negated facts, obstruction facts, or explicitly rejected overclaims.

  Gap:
    statements that are not false but are under-specified and need more
    structure before they can be made into Lean theorems.

  The goal is to grow Core by fixing both True and False observations.
  Do not skip a fact just because it looks obvious.  If it is useful, ask Lean.

Current Core:
  `SourcePressureBeamSeed`
  `sourcePressureBeamSeed_of_sortedBeforeFailure`
  `sourcePressureBeamSeed_recovered_of_sortedBeforeFailure_of_noAdjacentOverlap`
  `SourcePressureBeamDepthTarget`
  `sourcePressureBeamDepthTarget_iff_margin_pos`

Required experiments:

  Experiment T1:
    Try to prove a direct constructor for depth targets from margin positivity.

    Expected theorem shape:

      theorem sourcePressureBeamDepthTarget_of_margin_pos
          (n : OddNat) (k r j : ℕ)
          (h : 0 < SourcePressureMarginInt n k (r + j)) :
          SourcePressureBeamDepthTarget n k r j

    This should likely follow from
      `sourcePressureBeamDepthTarget_iff_margin_pos`.

  Experiment T2:
    Try to prove the reverse projection.

    Expected theorem shape:

      theorem sourcePressureMargin_pos_of_beamDepthTarget
          (n : OddNat) (k r j : ℕ)
          (h : SourcePressureBeamDepthTarget n k r j) :
          0 < SourcePressureMarginInt n k (r + j)

    This should likely follow from
      `sourcePressureBeamDepthTarget_iff_margin_pos`.

  Experiment G1:
    Try, in a scratch buffer only, the overclaim:

      SourcePressureBeamSeed L -> SourcePressureBeamDepthTarget n k r j

    Do not commit this theorem unless it is unexpectedly provable with the
    current hypotheses.  It is expected to be under-specified because there is
    no relation between witness list `L` and target depth `j`.

    Record the result in the report as Gap:
      missing seed-to-depth relation.

  Experiment G2:
    Try to identify the minimal missing relation needed for a future
    seed-to-depth theorem.  Do not implement it unless it is only a definition
    and its fields are clearly justified by existing names.

    Candidate relation name, only if useful:

      SourcePressureBeamSeedTargetsDepth L n k r j

    Prefer report-only if the fields are not obvious.

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
  2. Review of what was tried.
  3. Explanation of True Beam / False Beam / Gap results.
  4. Next Codex instruction.
  5. One-step-ahead inference from Wise Wolf:
       what should be tried after this checkpoint.
  6. Experimental lemmas Wise Wolf requested, with results:
       passed / failed / under-specified.
  7. Explicit statement that no propagation, convergence, coverage,
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

T1 / T2 が通れば、次にやるべきはこれじゃ。

```text id="r7hm1h"
BeamDepthTarget の True Beam API を完成させる
```

つまり、

```text id="6f6odu"
Target iff margin_pos
Target of margin_pos
margin_pos of Target
```

の三点セットを固定する。

これは小さいが大事じゃ。
なぜなら次の seed-to-depth transport を試すとき、target 側の扱いが簡単になるからじゃ。

その次に初めて、

```text id="tcm2t2"
SourcePressureBeamSeedTargetsDepth
```

のような関係を設計する。
ここで `L` と `j` をどう結ぶかが本丸じゃ。

## ここで始まる研究

ここからは、単なる Beam ではない。
**True Beam / False Beam の二本束で、Lean が認める事実地図を作る段階**じゃ。

コラッツ機械語を読むなら、

```text id="zltapy"
命令が実行される条件
命令が実行されない条件
未定義命令として残る条件
```

を全部記録する必要がある。

ぬしの言う通り、Lean が答えを導いてくれる。
わっちは次から、Codex への指示にも必ず「実験補題」を入れる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
index ccca07ee..9c4a2ff3 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
@@ -82,4 +82,30 @@ theorem sourcePressureBeamSeed_recovered_of_sortedBeforeFailure_of_noAdjacentOve
           A B :=
   sourcePressureFailureResolution_recovered_of_noAdjacentOverlap h hno

+/--
+Depth-indexed Beam target for local pressure.
+
+This is the first explicit Beam-facing target axis.  It is deliberately the
+pressure-depth axis `(r + j)`, because that is the native axis of the local
+margin/net-drop machinery below this file.  The predicate only names a target
+at one explicit relative pressure depth; it does not assert that a Beam seed
+reaches the target, that targets cover a range, or that targets aggregate.
+-/
+def SourcePressureBeamDepthTarget
+    (n : OddNat) (k r j : ℕ) : Prop :=
+  IsSourcePressureDepth n k r j
+
+/--
+Beam depth targets are exactly positive source-pressure margins.
+
+This is only the Beam-facing spelling of
+`isSourcePressureDepth_iff_margin_pos`.  It is not a transport theorem from a
+Beam seed to a target depth.
+-/
+theorem sourcePressureBeamDepthTarget_iff_margin_pos
+    (n : OddNat) (k r j : ℕ) :
+    SourcePressureBeamDepthTarget n k r j ↔
+      0 < SourcePressureMarginInt n k (r + j) :=
+  isSourcePressureDepth_iff_margin_pos n k r j
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-202.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-202.md
index 97fd7280..cbe37d75 100644
--- a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-202.md
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-202.md
@@ -2,10 +2,11 @@

 ## Checkpoint

-`petal-202` is audit-only.
+`petal-202` started as an audit-only checkpoint, then continued with the
+small implementation that the audit recommended.

-No Lean code was added in this checkpoint.  The purpose was to decide the
-first safe index axis for Beam transport above `PressureBeam`.
+The first safe index axis for Beam transport above `PressureBeam` was audited,
+and the resulting thin depth-indexed target was added to `PressureBeam.lean`.

 ## Current Beam Boundary

@@ -14,9 +15,12 @@ first safe index axis for Beam transport above `PressureBeam`.
 - `SourcePressureBeamSeed`
 - `sourcePressureBeamSeed_of_sortedBeforeFailure`
 - `sourcePressureBeamSeed_recovered_of_sortedBeforeFailure_of_noAdjacentOverlap`
+- `SourcePressureBeamDepthTarget`
+- `sourcePressureBeamDepthTarget_iff_margin_pos`

 These are Beam-facing names for the local `PressureAutomaton` state.  They do
-not propagate anything yet.
+not propagate anything yet.  `SourcePressureBeamDepthTarget` is only the
+Beam-facing depth target name for `IsSourcePressureDepth`.

 The import direction remains:

@@ -127,7 +131,7 @@ Reason:
 - A theorem would be premature because no transport target has been fixed yet.
 - A predicate gives the next checkpoint a named surface without overclaiming.

-Suggested definition for the next checkpoint:
+Implemented definition:

 ```lean
 /--
@@ -142,11 +146,11 @@ def SourcePressureBeamDepthTarget
   IsSourcePressureDepth n k r j
 ```

-This would require `PressureBeam` to continue importing only
+This required `PressureBeam` to continue importing only
 `PressureAutomaton`, because `IsSourcePressureDepth` is already available
 through the import chain.

-Then the first thin theorem to attempt should be only a naming bridge:
+Implemented thin theorem:

 ```lean
 theorem sourcePressureBeamDepthTarget_iff_margin_pos
@@ -218,6 +222,14 @@ The builds still replay the known unrelated warning in

 ## Next Checkpoint

-Implement `SourcePressureBeamDepthTarget` in `PressureBeam.lean`, plus the
-thin equivalence theorem to margin positivity.  Stop there unless a downstream
-statement supplies an explicit seed-to-depth relation.
+The next checkpoint should not repeat the depth-target naming work; it is now
+implemented.  The next safe step is to define an explicit seed-to-depth
+relation shape before proving any transport theorem.  In particular, avoid a
+statement of the form
+
+```text
+SourcePressureBeamSeed L -> SourcePressureBeamDepthTarget n k r j
+```
+
+until the relation between the seed list `L` and the target depth `j` is
+supplied explicitly.
````
`````
