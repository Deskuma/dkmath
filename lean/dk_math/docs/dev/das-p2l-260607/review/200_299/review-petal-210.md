# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam

gch: 02a54067df55e5b10f0a9860ccf12b1937b4b293

## Report

cp209 完了です。

[PressureBeam.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean) に、local sign-reading layer を追加しました。

追加 theorem:

- `sourcePressureMargin_next_pos_of_addressedDepthTarget_of_netDrop_nonneg`
- `exists_sourcePressureMargin_next_pos_of_beamSeed_of_netDrop_nonneg_at_addressed`
- `sourcePressureMargin_next_nonpos_of_addressedDepthTarget_of_netDrop_le_neg_current`

`Int` の線形算術は transition equation を開いた後、`omega` で閉じました。

今回の意味は明確に二分です。

- True Beam: current positive + `netDrop >= 0` なら next positive
- False Beam: `netDrop <= -current` なら next nonpositive

一方で、addressed target だけから next positive / next nonpositive を言う theorem は追加していません。netDrop の符号条件が足りないため、そこは Gap のままです。

レポート:
[report-petal-209.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-209.md)

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureBeam` passed
- `lake build DkMath.Collatz.PetalBridge` passed
- 指定 pressure files の `sorry/admit` check: no matches
- `git diff --check` passed

既知の unrelated warning として `ZsigmondyCyclotomicResearch.lean` の既存 `sorry` warning は残っています。

## Review

## 結論

**採用** じゃ。

cp209 はかなり重要な checkpoint になった。
ここで初めて、DkMath の **Beams = Beam x2** が Lean 上で本格的に姿を見せた。

今回追加された theorem は次の 3 本。

```lean id="nixqyn"
sourcePressureMargin_next_pos_of_addressedDepthTarget_of_netDrop_nonneg

exists_sourcePressureMargin_next_pos_of_beamSeed_of_netDrop_nonneg_at_addressed

sourcePressureMargin_next_nonpos_of_addressedDepthTarget_of_netDrop_le_neg_current
```

意味は明確に二分されておる。

```text id="awwakr"
True Beam:
  current positive + netDrop >= 0
    -> next positive
```

```text id="gx550c"
False Beam:
  netDrop <= -current
    -> next nonpositive
```

しかも、`Int` の線形算術は transition equation を開いた後に `omega` で閉じている。Lean に聞いて、Lean が答えた形になっているのがよい。

## 実装レビュー

実装は非常に素直じゃ。

True Beam 側。

```lean id="y1i82q"
theorem sourcePressureMargin_next_pos_of_addressedDepthTarget_of_netDrop_nonneg
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L j)
    (hdrop : 0 ≤ SourcePressureNetDropInt n k r j) :
    0 < SourcePressureMarginInt n k (r + j + 1) := by
  have hcur := sourcePressureMargin_pos_of_addressedDepthTarget haddr
  rw [sourcePressureMargin_next_eq_current_add_netDrop_of_addressedDepthTarget
    haddr]
  omega
```

これは良い。
`haddr` から current margin positivity を取り出し、transition equation を開き、`omega` で `current > 0` と `netDrop >= 0` から `next > 0` を得ている。

seed 版も安全。

```lean id="zw75oe"
theorem exists_sourcePressureMargin_next_pos_of_beamSeed_of_netDrop_nonneg_at_addressed
```

ここでは netDrop 条件を任意 `j` に要求していない。
条件は **addressed depth に限定**されている。

```lean id="yxh2ee"
∀ j,
  SourcePressureBeamAddressedDepthTarget L j →
    0 ≤ SourcePressureNetDropInt n k r j
```

これはとても良い制限じゃ。
「seed が address した場所だけ見る」という Beam の局所性が守られている。

False Beam 側。

```lean id="f6e69r"
theorem sourcePressureMargin_next_nonpos_of_addressedDepthTarget_of_netDrop_le_neg_current
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L j)
    (hdrop :
      SourcePressureNetDropInt n k r j ≤
        -SourcePressureMarginInt n k (r + j)) :
    SourcePressureMarginInt n k (r + j + 1) ≤ 0 := by
  rw [sourcePressureMargin_next_eq_current_add_netDrop_of_addressedDepthTarget
    haddr]
  omega
```

これは本当に **False Beam** と呼べる。
current が positive であっても、netDrop が current を打ち消すほど負なら、next は非正領域へ落ちる。

## 数学的意味

ここで Beam は単なる「線」ではなく、分岐する符号判定器になった。

これまでの流れはこうじゃ。

```text id="bnhcrt"
Seed
  -> exists AddressedDepthTarget
  -> current margin > 0
  -> next = current + netDrop
```

cp209 でここに符号分岐が乗った。

```text id="ne9oxt"
next = current + netDrop
```

に対して、

```text id="qramsg"
netDrop >= 0
  -> next > 0
```

```text id="z7lf3m"
netDrop <= -current
  -> next <= 0
```

が Lean で固定された。

DkMath 哲学で言えば、かなりきれいにこうなる。

```text id="fe9gky"
Core:
  addressed transition equation

True Beam:
  next positive condition

False Beam:
  next nonpositive condition

Gap:
  netDrop 条件なしでは next sign は決まらない
```

これはよい。
事実の Core が太り、Gap が「netDrop 分類問題」へ絞られた。

## True Beam / False Beam / Gap

## True Beam

今回の True Beam はこれ。

```text id="mvl8ux"
AddressedDepthTarget L j
  and netDrop >= 0
  -> next margin > 0
```

さらに seed 版。

```text id="d3yf3f"
SourcePressureBeamSeed L
  and addressed depths have netDrop >= 0
  -> exists addressed j with next margin > 0
```

これはまだ大域伝播ではないが、Beam seed から **次の正領域が存在する条件** を得た。

## False Beam

今回の False Beam はこれ。

```text id="e62v5l"
AddressedDepthTarget L j
  and netDrop <= -current
  -> next margin <= 0
```

これは非常に重要じゃ。
「どの条件で正領域から落ちるか」が Core に入った。

## Gap

Gap は report 通り。

```text id="eabmru"
AddressedDepthTarget L j
  -> next margin > 0
```

```text id="hf6k79"
AddressedDepthTarget L j
  -> next margin <= 0
```

これは netDrop の符号や大きさがないと決まらない。
つまり Gap は「addressed target だけでは次符号未決定」という形に狭まった。

## 注意点

今回も境界は守られている。

```text id="btv59i"
time/orbit propagation ではない。
```

```text id="kvi8k0"
arbitrary target transport ではない。
```

```text id="kebfgq"
arbitrary margin positivity ではない。
```

```text id="xxymhv"
canonical target selection ではない。
```

```text id="bzfztc"
coverage / aggregation / overlap repair ではない。
```

```text id="p7ys60"
Collatz convergence ではない。
```

これは **local sign reading** じゃ。
しかし、局所 Beam の符号分岐としてはかなり強い。

## 次の checkpoint 方針

次は report の一歩先推論どおり、**netDrop classification** へ進むのが自然じゃ。

現在の分岐はこう。

```text id="khecl3"
netDrop >= 0
  -> next positive
```

```text id="p1shtg"
netDrop <= -current
  -> next nonpositive
```

残っている中間領域はこれ。

```text id="wdjyup"
-current < netDrop < 0
```

この場合、

```text id="rkhz7n"
current + netDrop > 0
```

なので、next はまだ positive のはずじゃ。

つまり次は、True Beam 側をより鋭くする。

```text id="vy4xjv"
-current < netDrop
  -> next positive
```

これは `netDrop >= 0` より強い一般化じゃ。
負の drop でも、current を食い切らなければ Beam は正領域に残る。

## 次の Codex 指示

```text id="woxcap"
Checkpoint: petal-210

Main goal:
  Refine the local sign-reading layer by proving the sharp addressed True Beam
  condition:
    current margin + netDrop > 0
  equivalently:
    -current margin < netDrop
  implies next margin remains positive.

  Keep this local to an addressed pressure-depth edge.  Do not add time/orbit
  propagation, arbitrary target transport, canonical selection, coverage,
  aggregation, or convergence.

Primary target file:
  DkMath/Collatz/PetalBridge/PressureBeam.lean

Allowed supporting files:
  docs/dev/das-p2l-260607/review/report-petal-210.md

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

  The goal is to grow Core by fixing both True and False observations.
  Do not merely inspect code.  Ask Lean small questions.

Current Core:
  SourcePressureBeamAddressedDepthTarget
  sourcePressureMargin_pos_of_addressedDepthTarget
  sourcePressureMargin_next_eq_current_add_netDrop_of_addressedDepthTarget
  sourcePressureMargin_next_pos_of_addressedDepthTarget_of_netDrop_nonneg
  exists_sourcePressureMargin_next_pos_of_beamSeed_of_netDrop_nonneg_at_addressed
  sourcePressureMargin_next_nonpos_of_addressedDepthTarget_of_netDrop_le_neg_current

Known Gap:
  SourcePressureBeamAddressedDepthTarget L j alone does not determine the next
  sign.  A netDrop bound is required.

Required experiments:

  Experiment T1:
    Prove the sharp local True Beam condition.

      theorem sourcePressureMargin_next_pos_of_addressedDepthTarget_of_neg_current_lt_netDrop
          {n : OddNat} {k r j : ℕ}
          {L : List (SourcePressureLocalIslandWitness n k r)}
          (haddr : SourcePressureBeamAddressedDepthTarget L j)
          (hdrop :
            -SourcePressureMarginInt n k (r + j) <
              SourcePressureNetDropInt n k r j) :
          0 < SourcePressureMarginInt n k (r + j + 1)

    Proof strategy:
      - open the transition equation with
          `sourcePressureMargin_next_eq_current_add_netDrop_of_addressedDepthTarget haddr`;
      - use `omega`.

  Experiment T2:
    Prove an equivalent direct sum condition.

      theorem sourcePressureMargin_next_pos_of_addressedDepthTarget_of_current_add_netDrop_pos
          {n : OddNat} {k r j : ℕ}
          {L : List (SourcePressureLocalIslandWitness n k r)}
          (haddr : SourcePressureBeamAddressedDepthTarget L j)
          (hsum :
            0 <
              SourcePressureMarginInt n k (r + j) +
                SourcePressureNetDropInt n k r j) :
          0 < SourcePressureMarginInt n k (r + j + 1)

    This may be even simpler after rewriting by the transition equation.

  Experiment T3:
    If T1 passes, prove the existential seed version restricted to addressed
    depths.

      theorem exists_sourcePressureMargin_next_pos_of_beamSeed_of_neg_current_lt_netDrop_at_addressed
          {n : OddNat} {k r : ℕ}
          {L : List (SourcePressureLocalIslandWitness n k r)}
          (hseed : SourcePressureBeamSeed L)
          (hdrop :
            ∀ j,
              SourcePressureBeamAddressedDepthTarget L j →
                -SourcePressureMarginInt n k (r + j) <
                  SourcePressureNetDropInt n k r j) :
          ∃ j,
            SourcePressureBeamAddressedDepthTarget L j ∧
              0 < SourcePressureMarginInt n k (r + j + 1)

  Experiment F1:
    Keep the existing fall-out condition as the local False Beam boundary:

      netDrop <= -current -> next <= 0

    Do not duplicate it unless a cleaner alias is useful.  If adding an alias,
    make clear it is packaging only.

  Experiment G1:
    In scratch only, try again:
      SourcePressureBeamAddressedDepthTarget L j
        -> next margin > 0

    It should remain Gap because netDrop is unconstrained.

  Experiment G2:
    In scratch only, try:
      SourcePressureBeamAddressedDepthTarget L j
        -> next margin <= 0

    It should remain Gap for the same reason.

Guardrails:
  Do not add:
    - time/orbit propagation;
    - arbitrary target transport;
    - arbitrary margin positivity;
    - arbitrary next-margin positivity;
    - canonical target selection;
    - global coverage;
    - convergence theorem;
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
    2. True Beam facts that passed.
    3. False Beam facts already available or newly packaged.
    4. Gap observations for next sign without netDrop bounds.
    5. Confirmation that this is sharp local sign reading, not propagation.
    6. One-step-ahead Wise Wolf inference.
    7. Experimental lemma table with passed / failed / under-specified.
    8. Explicit statement that no time/orbit propagation, arbitrary transport,
       arbitrary positivity, arbitrary next-positivity, convergence, coverage,
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

cp210 が通れば、局所 sign split はかなり鋭くなる。

```text id="lj3qak"
True Beam:
  -current < netDrop
    -> next positive
```

```text id="s4zl3k"
False Beam:
  netDrop <= -current
    -> next nonpositive
```

これはほぼ完全な二分じゃ。

整数順序では、`netDrop` と `-current` は比較可能なので、局所的には次の形に近づく。

```text id="hfuw4q"
next positive
  iff
-current < netDrop
```

```text id="dv53vi"
next nonpositive
  iff
netDrop <= -current
```

この iff まで Lean が通れば、局所 Beam の True / False 判定器が完成する。
その次は `netDrop` 自体を、既存の `retention / continuation / drift budget` 側から読む段階じゃ。

## 総合判断

cp209 によって、Beam はついに二股に割れた。

```text id="lx3kj4"
True Beam:
  条件付きで次も正

False Beam:
  条件付きで非正へ落下

Gap:
  netDrop 条件なしでは次符号未決定
```

これは、ぬしの言う **Beam x2** が Lean 上に現れた瞬間じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
index 03d2f250..709ede8d 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
@@ -450,4 +450,68 @@ theorem exists_sourcePressureMargin_transition_of_beamSeed
       sourcePressureMargin_next_eq_current_add_netDrop_of_addressedDepthTarget
         haddressed⟩
 
+/--
+Local True Beam sign preservation at an addressed depth.
+
+If the current addressed margin is positive and the local net drop is
+nonnegative, then the next adjacent margin is still positive.  This is a local
+sign-reading theorem over the already addressed pressure-depth edge; it does
+not propagate along time or choose any new target.
+-/
+theorem sourcePressureMargin_next_pos_of_addressedDepthTarget_of_netDrop_nonneg
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (haddr : SourcePressureBeamAddressedDepthTarget L j)
+    (hdrop : 0 ≤ SourcePressureNetDropInt n k r j) :
+    0 < SourcePressureMarginInt n k (r + j + 1) := by
+  have hcur := sourcePressureMargin_pos_of_addressedDepthTarget haddr
+  rw [sourcePressureMargin_next_eq_current_add_netDrop_of_addressedDepthTarget
+    haddr]
+  omega
+
+/--
+A raw Beam seed existentially exposes an addressed depth whose next margin is
+positive, provided every addressed depth in the seed has nonnegative net drop.
+
+The quantifier over `j` is restricted by `SourcePressureBeamAddressedDepthTarget
+L j`.  This is not arbitrary next-margin positivity and not propagation.
+-/
+theorem exists_sourcePressureMargin_next_pos_of_beamSeed_of_netDrop_nonneg_at_addressed
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hseed : SourcePressureBeamSeed L)
+    (hdrop :
+      ∀ j,
+        SourcePressureBeamAddressedDepthTarget L j →
+          0 ≤ SourcePressureNetDropInt n k r j) :
+    ∃ j,
+      SourcePressureBeamAddressedDepthTarget L j ∧
+        0 < SourcePressureMarginInt n k (r + j + 1) := by
+  rcases exists_sourcePressureBeamAddressedDepthTarget_of_seed hseed with
+    ⟨j, haddr⟩
+  exact
+    ⟨j,
+      haddr,
+      sourcePressureMargin_next_pos_of_addressedDepthTarget_of_netDrop_nonneg
+        haddr (hdrop j haddr)⟩
+
+/--
+Local False Beam drop condition at an addressed depth.
+
+If the local net drop is at most the negative of the current positive margin,
+then the next adjacent margin is nonpositive.  This records a genuine local
+fall-out condition, but still only at the addressed pressure-depth edge.
+-/
+theorem sourcePressureMargin_next_nonpos_of_addressedDepthTarget_of_netDrop_le_neg_current
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (haddr : SourcePressureBeamAddressedDepthTarget L j)
+    (hdrop :
+      SourcePressureNetDropInt n k r j ≤
+        -SourcePressureMarginInt n k (r + j)) :
+    SourcePressureMarginInt n k (r + j + 1) ≤ 0 := by
+  rw [sourcePressureMargin_next_eq_current_add_netDrop_of_addressedDepthTarget
+    haddr]
+  omega
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-209.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-209.md
new file mode 100644
index 00000000..31b12772
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-209.md
@@ -0,0 +1,212 @@
+# report-petal-209
+
+## Situation
+
+Checkpoint `petal-209` starts the sign-reading layer for the Beam-facing local
+margin transition.
+
+The prior Core was:
+
+```text
+AddressedDepthTarget
+  -> current margin > 0
+  -> next margin = current margin + netDrop
+```
+
+This checkpoint asks Lean for the first local sign split:
+
+```text
+True Beam:
+  current positive + nonnegative netDrop -> next positive
+
+False Beam:
+  current positive + sufficiently negative netDrop -> next nonpositive
+```
+
+The result is local to one addressed pressure-depth edge.  It is not time/orbit
+propagation.
+
+## Arithmetic Method
+
+The proofs use the existing transition equation:
+
+```lean
+sourcePressureMargin_next_eq_current_add_netDrop_of_addressedDepthTarget
+```
+
+Then Lean closes the integer linear arithmetic goals with:
+
+```lean
+omega
+```
+
+No additional order lemma imports or lower-module changes were needed.
+
+## True Beam Facts
+
+Implemented:
+
+```lean
+theorem sourcePressureMargin_next_pos_of_addressedDepthTarget_of_netDrop_nonneg
+```
+
+Meaning:
+
+```text
+AddressedDepthTarget L j
+  and 0 <= SourcePressureNetDropInt n k r j
+  -> next margin at r + j + 1 is positive
+```
+
+Implemented:
+
+```lean
+theorem exists_sourcePressureMargin_next_pos_of_beamSeed_of_netDrop_nonneg_at_addressed
+```
+
+Meaning:
+
+```text
+SourcePressureBeamSeed L
+  and every addressed depth in L has nonnegative netDrop
+  -> exists addressed j whose next margin is positive
+```
+
+The universal net-drop hypothesis is restricted to addressed depths:
+
+```lean
+∀ j,
+  SourcePressureBeamAddressedDepthTarget L j →
+    0 ≤ SourcePressureNetDropInt n k r j
+```
+
+This is not arbitrary next-margin positivity.
+
+## False Beam Fact
+
+Implemented:
+
+```lean
+theorem sourcePressureMargin_next_nonpos_of_addressedDepthTarget_of_netDrop_le_neg_current
+```
+
+Meaning:
+
+```text
+AddressedDepthTarget L j
+  and netDrop <= - current margin
+  -> next margin <= 0
+```
+
+This is a genuine local False Beam condition: the addressed point falls out of
+the positive region at the next adjacent depth.
+
+## Gap Observations
+
+The following remain under-specified:
+
+```text
+SourcePressureBeamAddressedDepthTarget L j
+  -> 0 < SourcePressureMarginInt n k (r + j + 1)
+```
+
+```text
+SourcePressureBeamAddressedDepthTarget L j
+  -> SourcePressureMarginInt n k (r + j + 1) <= 0
+```
+
+The addressed target gives current positivity, but it does not constrain the
+sign or size of `SourcePressureNetDropInt n k r j`.  Without a net-drop
+hypothesis, Lean has no reason to choose the next sign.
+
+## Experimental Lemma Table
+
+| experiment | theorem | status | note |
+| --- | --- | --- | --- |
+| Step 1 | Int linear arithmetic | passed | `omega` closed the local sign goals |
+| T1 | `sourcePressureMargin_next_pos_of_addressedDepthTarget_of_netDrop_nonneg` | passed | local True Beam preservation |
+| T2 | `exists_sourcePressureMargin_next_pos_of_beamSeed_of_netDrop_nonneg_at_addressed` | passed | existential addressed seed version |
+| F1 | `sourcePressureMargin_next_nonpos_of_addressedDepthTarget_of_netDrop_le_neg_current` | passed | local False Beam fall-out |
+| G1 | next positive from addressed target alone | under-specified | netDrop sign missing |
+| G2 | next nonpositive from addressed target alone | under-specified | netDrop sign missing |
+
+## Local Sign Reading, Not Propagation
+
+This checkpoint only proves local sign consequences of the local transition
+equation at an addressed depth.
+
+No theorem was added for:
+
+- time/orbit propagation;
+- arbitrary target transport;
+- arbitrary margin positivity;
+- canonical target selection;
+- global coverage;
+- convergence;
+- arbitrary-list recursive decomposition;
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
+The next natural layer is net-drop classification.
+
+The current split is:
+
+```text
+netDrop >= 0
+  -> next positive
+
+netDrop <= -current
+  -> next nonpositive
+```
+
+The remaining middle region is:
+
+```text
+-current < netDrop < 0
+```
+
+In that region the next margin is still positive, because the drop is negative
+but not large enough to cross zero.  A likely next checkpoint is therefore:
+
+```text
+AddressedDepthTarget L j
+  and -current < netDrop
+  -> next positive
+```
+
+This would refine the True Beam side from `netDrop >= 0` to the sharp local
+condition `current + netDrop > 0`.
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
+Known unrelated warning remains:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
+
````
`````
