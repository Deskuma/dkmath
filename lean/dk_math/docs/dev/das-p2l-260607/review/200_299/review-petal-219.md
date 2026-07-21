# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam

gch: 784d9b03ffa753bca0967bc546c3faceccf886d8

## Report

cp218 実装完了です。

[PressureBeam.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean) に、上流 sign-change / local-island から Beam mass-balance 比較へ接続する薄い補題を追加しました。

追加した主な定理:

```lean
sourcePressureBeamMassBalanceLeft_lt_right_of_signChangeUp
sourcePressureBeamMassBalanceRight_le_left_of_signChangeDown
sourcePressureBeamMassBalanceLeft_lt_right_of_localIsland_left
sourcePressureBeamMassBalanceRight_le_left_of_localIsland_right
```

`DriftBudget` や `PressureAccounting` はまだ interval / aggregate 寄りで、任意 addressed edge の `left < right` を直接供給する層ではありませんでした。現時点での直接入力は `PressureDecay` / `PressureFrontier` の sign-change 層です。この判断はコード中コメントと [report-petal-218.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-218.md) に記録しました。

検証:

```text
lake build DkMath.Collatz.PetalBridge.PressureBeam  passed
lake build DkMath.Collatz.PetalBridge               passed
no-sorry grep over inspected pressure files          no matches
git diff --check                                     passed
```

既知の unrelated warning として `ZsigmondyCyclotomicResearch.lean` の既存 `sorry` は引き続き表示されます。

## Review

## 結論

**採用** じゃ。
cp218 は、かなり良い方向転換になっている。

ここまで `PressureBeam` では局所 classifier を作ってきたが、cp218 ではようやく問いが変わった。

```text id="c9wkdw"
局所 edge をどう分類するか？
```

から、

```text id="grcvgy"
その分類に必要な left < right / right <= left は、上流のどこから来るのか？
```

へ移った。

Codex は現場調査の結果、`DriftBudget` や `PressureAccounting` はまだ interval / aggregate 寄りで、任意 addressed edge の `left < right` を直接供給する層ではないと判断している。そのうえで、直接入力として `PressureDecay` / `PressureFrontier` の sign-change 層を使い、薄い bridge theorem を追加している。これは良い現場判断じゃ。

## 実装レビュー

追加された主 theorem はこの 4 本。

```lean id="i4d2qo"
sourcePressureBeamMassBalanceLeft_lt_right_of_signChangeUp
sourcePressureBeamMassBalanceRight_le_left_of_signChangeDown
sourcePressureBeamMassBalanceLeft_lt_right_of_localIsland_left
sourcePressureBeamMassBalanceRight_le_left_of_localIsland_right
```

かなり筋がよい。

まず、upward sign change から True Beam 側。

```lean id="gv0v43"
SourcePressureSignChangeUp n k r j
  -> SourcePressureBeamMassBalanceLeftInt n k r j <
       SourcePressureBeamMassBalanceRightInt n k r j
```

これは、`hchange.2` が next margin positivity を持っており、既存の

```lean id="w086c1"
sourcePressureMargin_next_pos_iff_massBalanceLeft_lt_right
```

で `left < right` に戻している。
つまり、上流の sign-change を Beam mass-balance 比較へ接続している。

downward sign change も同様。

```lean id="cp1des"
SourcePressureSignChangeDown n k r j
  -> SourcePressureBeamMassBalanceRightInt n k r j <=
       SourcePressureBeamMassBalanceLeftInt n k r j
```

こちらは nonpositive なので、False / Boundary 側の non-strict comparison になる。
strict false まで言わないのが正しい。

## localIsland との接続

local island からの 2 本も良い。

```lean id="qqmz1v"
sourcePressureBeamMassBalanceLeft_lt_right_of_localIsland_left
```

これは `j - 1` の left edge を明示している。
ここが大事じゃ。

```text id="tm4t0t"
local island at j
  -> left edge is j - 1
  -> signChangeUp
  -> left < right
```

一方で右 edge。

```lean id="jmq6uc"
sourcePressureBeamMassBalanceRight_le_left_of_localIsland_right
```

こちらは `j` そのものを right edge として、

```text id="n5pwpi"
local island at j
  -> right edge is j
  -> signChangeDown
  -> right <= left
```

へ接続している。

これは「arbitrary target transport」ではなく、**島が指定する exact edge における bridge** なので安全じゃ。

## 数学的意味

cp217 までで、局所 classifier はこう閉じていた。

```text id="rd16zp"
nextMargin = right - left
```

そして、

```text id="scs3kb"
left < right  -> positive
left = right  -> zero boundary
right < left  -> negative
```

だった。

cp218 で初めて、上流からこの比較を供給する道ができた。

```text id="q3ow2o"
signChangeUp
  -> left < right
  -> True Beam
```

```text id="vzae97"
signChangeDown
  -> right <= left
  -> False / Boundary Beam
```

さらに、

```text id="zrsj28"
localIsland left edge
  -> True Beam source

localIsland right edge
  -> False / Boundary source
```

まで来た。

これはかなり重要じゃ。
Beam classifier が、単なる後段の判定器ではなく、`PressureFrontier` の local island 構造と接続し始めた。

## True Beam / Boundary / False Beam / Gap

## True Beam

今回の True Beam はこれ。

```text id="g4vtda"
SourcePressureSignChangeUp
  -> left < right
```

および、

```text id="qiatj5"
SourcePressureLocalIsland n k r j
  -> left edge j - 1 で left < right
```

これは、local island の入口側が正領域へ上がることを Beam mass-balance 側から読めるようにした。

## False / Boundary Beam

今回の False / Boundary はこれ。

```text id="xk9djf"
SourcePressureSignChangeDown
  -> right <= left
```

および、

```text id="wospdm"
SourcePressureLocalIsland n k r j
  -> right edge j で right <= left
```

non-strict なので、zero boundary と strict false の両方を含む。
ここで strict false を要求しなかったのは正しい。

## Gap

Gap は report の通り。

```text id="uc81n8"
DriftBudget / PressureAccounting は、
任意 addressed edge の left < right を直接供給する層ではまだない
```

ただし、ここは将来有望じゃ。

特に `PressureAccounting` には interval-pulse / list-family accounting がある。
しかし今の時点では、それを arbitrary addressed edge に接続するには、exact edge address が必要になる。

つまり次の Gap はこれ。

```text id="h4zr0u"
interval-pulse address / local witness edge
  -> exact edge sign-change
  -> Beam mass-balance comparison
```

このルートが次に見えている。

## 評価

今回のよい点は、Codex が「全部を無理に theorem 化」しなかったことじゃ。

`DriftBudget` や `PressureAccounting` を見て、

```text id="hlwazf"
ここは将来入力にはなるが、今すぐ arbitrary addressed edge に left < right を供給する層ではない
```

と切り分けている。

そのうえで、いま直接つながる `PressureDecay` / `PressureFrontier` の sign-change 層だけを bridge している。
これは、こちらが望んでいた **現場の判断** そのものじゃ。

## 注意点

今回も境界は守れている。

```text id="kjb1w5"
time / orbit propagation ではない
arbitrary target transport ではない
global coverage ではない
aggregation over all witnesses ではない
overlap repair ではない
canonical next target selection ではない
Collatz convergence ではない
```

これは edge-local bridge。
上流から分類器へ入力を渡すだけじゃ。

## 次の checkpoint 方針

次は report の候補通り、**interval-pulse address から Beam mass-balance API への接続**を調べるのが自然じゃ。

ただし、これは少し危険域に入る。
interval は list / family / aggregate の匂いがあるので、任意 coverage に飛ばないようにする必要がある。

狙いはあくまで exact edge。

```text id="b7layd"
left edge:
  A.start - 1

right edge:
  A.start + A.len - 1
```

この exact edge に addressed target がある場合だけ、Beam comparison へつなぐ。

## 次の Codex 指示

```text id="wq1fj3"
Checkpoint: petal-219

Goal:
  Investigate whether interval-pulse addresses can be connected to the Beam
  mass-balance API at exact edges.

Context:
  cp218 found that the immediate upstream source of Beam mass-balance comparison
  is the edge-local sign-change layer:

    signChangeUp   -> left < right
    signChangeDown -> right <= left

  Local islands already feed those sign changes.

  The next candidate source is the interval-pulse / local witness address layer
  in `PressureAccounting`.

Main question:
  Can an interval-pulse address provide a sign-change, next-margin sign, or
  mass-balance comparison at its exact left/right edge?

Modules to inspect:
  - DkMath.Collatz.PetalBridge.PressureAccounting
  - DkMath.Collatz.PetalBridge.PressureFrontier
  - DkMath.Collatz.PetalBridge.PressureDecay
  - DkMath.Collatz.PetalBridge.PressureBeam

Codex should use workspace judgment:
  - inspect definitions of interval-pulse addresses;
  - inspect theorem names around:
      sourcePressureIntervalPulseAddress_left_netDrop_pos
      sourcePressureIntervalPulseAddress_right_netDrop_neg
      interval pulse left/right edge
      local island witness to interval pulse address
  - use `#check`, `#print`, and scratch lemmas;
  - determine exact edge indices before adding any theorem.

Possible target shapes, only if Lean supports them naturally:

  theorem sourcePressureBeamMassBalanceLeft_lt_right_of_intervalPulse_left
      ...
      (haddr : SourcePressureBeamAddressedDepthTarget L <leftEdge>)
      (hpulse : <interval pulse address predicate>) :
      SourcePressureBeamMassBalanceLeftInt n k r <leftEdge> <
        SourcePressureBeamMassBalanceRightInt n k r <leftEdge>

  theorem sourcePressureBeamMassBalanceRight_le_left_of_intervalPulse_right
      ...
      (haddr : SourcePressureBeamAddressedDepthTarget L <rightEdge>)
      (hpulse : <interval pulse address predicate>) :
      SourcePressureBeamMassBalanceRightInt n k r <rightEdge> <=
        SourcePressureBeamMassBalanceLeftInt n k r <rightEdge>

But do not force these shapes.
If the available interval-pulse theorems only talk about netDrop positivity /
negativity and not next-margin sign, record the exact missing bridge.

Allowed outcomes:
  1. Add small exact-edge bridge theorem(s) from interval-pulse address to Beam
     mass-balance comparison.
  2. Add theorem(s) from interval-pulse address to sign-change, if that is the
     missing reusable layer.
  3. Add no Lean code and write a report identifying the precise missing
     relation.

Guardrails:
  Do not add:
    - arbitrary target transport;
    - global interval coverage;
    - aggregation over witness families;
    - overlap repair;
    - canonical next target selection;
    - Collatz convergence.

Report requirements:
  - Explain which interval-pulse definitions/theorems were inspected.
  - State exact left/right edge index shapes discovered.
  - State whether Lean could connect interval pulse to sign-change or directly
    to Beam mass-balance.
  - If no theorem was added, identify the missing relation precisely.
  - Classify findings as True Beam / Boundary / False Beam / Gap.
  - Make clear this is exact-edge bridge investigation, not interval coverage.

Verification if code changes:
  lake build DkMath.Collatz.PetalBridge.PressureBeam
  lake build DkMath.Collatz.PetalBridge
  no-sorry grep over pressure files
  git diff --check
```

## 一歩先ゆく推論

この先は、かなり面白い。

いまの構造はこう。

```text id="uw94n6"
local classifier:
  nextMargin = right - left

direct source:
  signChangeUp / signChangeDown

island source:
  localIsland left/right edge
```

次に interval-pulse が接続できれば、

```text id="zkhl18"
witness / interval address
  -> edge sign
  -> mass-balance comparison
  -> Beam decision
```

という道が開く。

これにより、`PressureAccounting` の witness-list 体系が、ようやく `PressureBeam` の classifier に値を入れ始める。
ただし、ここで global coverage に飛ばないこと。exact edge の橋に留めることが重要じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
index 3b13eac4..17404aa6 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
@@ -1122,4 +1122,92 @@ theorem sourcePressureMargin_next_sign_massBalance_trichotomy_of_addressedDepthT
       (sourcePressureMargin_next_neg_iff_massBalanceRight_lt_left haddr).2 hgt
     exact ⟨hneg, hgt⟩

+/-
+Upstream inequality-source bridge.
+
+Checkpoint 218 changes the question from "how do we classify an addressed
+edge once `left` and `right` are known?" to "which upstream predicates can
+supply `left < right`, equality, or the false-side comparison?"  The immediate
+source is not the aggregate drift/accounting layer: those theorems speak about
+finite intervals, sums, tails, or bounded witness lists.  The direct local
+input is the sign-change layer from `PressureDecay`/`PressureFrontier`.
+
+The lemmas below intentionally remain edge-local.  They do not transport an
+arbitrary target, aggregate recovered intervals, repair overlap, choose a
+canonical next target, or assert convergence.  They only say that an upstream
+sign change at the same addressed edge feeds the already-closed Beam
+mass-balance classifier.
+-/
+
+/--
+An upstream upward sign change supplies the True Beam mass-balance inequality.
+
+This is the first direct source of
+`SourcePressureBeamMassBalanceLeftInt < SourcePressureBeamMassBalanceRightInt`.
+The addressed target supplies the Beam reading of the edge; the sign-change
+predicate supplies positivity of the next margin at that same edge.
+-/
+theorem sourcePressureBeamMassBalanceLeft_lt_right_of_signChangeUp
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (haddr : SourcePressureBeamAddressedDepthTarget L j)
+    (hchange : SourcePressureSignChangeUp n k r j) :
+    SourcePressureBeamMassBalanceLeftInt n k r j <
+      SourcePressureBeamMassBalanceRightInt n k r j :=
+  (sourcePressureMargin_next_pos_iff_massBalanceLeft_lt_right haddr).1
+    hchange.2
+
+/--
+An upstream downward sign change supplies the False/Boundary Beam comparison.
+
+The result is non-strict because `SourcePressureSignChangeDown` records that
+the next margin is nonpositive.  The strict false branch is recovered by the
+existing theorem `sourcePressureMargin_next_neg_iff_massBalanceRight_lt_left`
+when a strictly negative next margin is available.
+-/
+theorem sourcePressureBeamMassBalanceRight_le_left_of_signChangeDown
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (haddr : SourcePressureBeamAddressedDepthTarget L j)
+    (hchange : SourcePressureSignChangeDown n k r j) :
+    SourcePressureBeamMassBalanceRightInt n k r j ≤
+      SourcePressureBeamMassBalanceLeftInt n k r j :=
+  (sourcePressureMargin_next_nonpos_iff_massBalanceRight_le_left haddr).1
+    hchange.2
+
+/--
+A local pressure island supplies the True Beam inequality on its left edge.
+
+The address is deliberately for `j - 1`, the exact left edge produced by
+`sourcePressureSignChangeUp_of_localIsland`.  This is not arbitrary target
+transport.
+-/
+theorem sourcePressureBeamMassBalanceLeft_lt_right_of_localIsland_left
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (haddr : SourcePressureBeamAddressedDepthTarget L (j - 1))
+    (hisland : SourcePressureLocalIsland n k r j) :
+    SourcePressureBeamMassBalanceLeftInt n k r (j - 1) <
+      SourcePressureBeamMassBalanceRightInt n k r (j - 1) :=
+  sourcePressureBeamMassBalanceLeft_lt_right_of_signChangeUp haddr
+    (sourcePressureSignChangeUp_of_localIsland n k r j hisland)
+
+/--
+A local pressure island supplies the False/Boundary Beam comparison on its
+right edge.
+
+The address is for the same right edge `j` as
+`sourcePressureSignChangeDown_of_localIsland`.  The theorem remains local to
+that edge and does not account for an entire island family.
+-/
+theorem sourcePressureBeamMassBalanceRight_le_left_of_localIsland_right
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (haddr : SourcePressureBeamAddressedDepthTarget L j)
+    (hisland : SourcePressureLocalIsland n k r j) :
+    SourcePressureBeamMassBalanceRightInt n k r j ≤
+      SourcePressureBeamMassBalanceLeftInt n k r j :=
+  sourcePressureBeamMassBalanceRight_le_left_of_signChangeDown haddr
+    (sourcePressureSignChangeDown_of_localIsland n k r j hisland)
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-218.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-218.md
new file mode 100644
index 00000000..77025379
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-218.md
@@ -0,0 +1,254 @@
+# report-petal-218
+
+## Checkpoint
+
+`petal-218`
+
+## Goal
+
+Investigate where the addressed Beam mass-balance inequality can come from
+upstream.
+
+The local classifier is already closed in `PressureBeam`:
+
+```lean
+nextMargin = right - left
+```
+
+and cp217 packages the local trichotomy:
+
+```text
+positive / zero / negative
+paired with
+left < right / left = right / right < left
+```
+
+This checkpoint therefore asks for upstream sources of:
+
+```lean
+SourcePressureBeamMassBalanceLeftInt n k r j <
+  SourcePressureBeamMassBalanceRightInt n k r j
+```
+
+or the boundary / false-side alternatives.
+
+## Modules inspected
+
+### `DkMath.Collatz.PetalBridge.DriftBudget`
+
+This module contains global and semi-global drift-budget facts:
+
+- two-layer and three-layer drift lower bounds;
+- prefix drift budgets;
+- residue-address drift bridges;
+- delayed depth-two / tail-reservoir budgets.
+
+These are useful for later pressure-budget work, but they do not directly
+supply the addressed edge-local inequality
+
+```lean
+left < right
+```
+
+for an arbitrary `SourcePressureBeamAddressedDepthTarget L j`.
+
+Classification: `Gap` for immediate local Beam input.
+
+### `DkMath.Collatz.PetalBridge.PressureDecay`
+
+This module provides the key edge-local sign-change vocabulary:
+
+- `SourcePressureSignChangeUp`
+- `SourcePressureSignChangeDown`
+- `SourcePressureMarginJumpUp`
+- `SourcePressureNetDropPositive`
+- margin transition identities.
+
+These predicates are exactly local to one adjacent pressure-depth edge, so
+they are compatible with the addressed Beam classifier.
+
+Classification:
+
+- `True Beam`: upward sign change gives next-margin positivity.
+- `False Beam / Boundary`: downward sign change gives next-margin nonpositivity.
+
+### `DkMath.Collatz.PetalBridge.PressureFrontier`
+
+This module connects local islands to sign changes:
+
+- `sourcePressureSignChangeUp_of_localIsland`
+- `sourcePressureSignChangeDown_of_localIsland`
+- `sourcePressureNetDropPositive_of_localIsland_left`
+- `sourcePressureCrosses_of_localIsland_left`
+- `sourcePressureFalls_of_localIsland_right`
+
+This gives a concrete upstream source for Beam comparisons:
+
+- the left edge of a local island is a True Beam source;
+- the right edge of a local island is a False/Boundary source.
+
+Classification:
+
+- `True Beam`: local-island left edge.
+- `False Beam / Boundary`: local-island right edge.
+
+### `DkMath.Collatz.PetalBridge.PressureAccounting`
+
+This module provides interval-pulse and list/family accounting:
+
+- `sourcePressureIntervalPulseAddress_left_netDrop_pos`
+- `sourcePressureIntervalPulseAddress_right_netDrop_neg`
+- interval net-drop negativity;
+- sorted-family sum bounds;
+- accounted interval budgets.
+
+These are strong future inputs, but they are interval/list level.  They do not
+directly become a mass-balance inequality at an arbitrary addressed `j`
+without choosing the corresponding edge address.
+
+Classification: promising `Gap` toward future interval-to-Beam edge bridges.
+
+### `PressureLocalWitnessObstruction`, `PressureAdjacentDiagnosis`, `PressureDiagnosticDecomposition`
+
+These modules organize witness-list order failures, overlap obstructions, and
+bounded adjacent diagnosis.  They are intentionally local to explicit witness
+lists and adjacent pairs.
+
+They do not provide a global inequality source, but they can select explicit
+witness-derived edges.  That matches the project guardrail: no global coverage,
+no arbitrary target transport, no overlap repair.
+
+Classification: witness-selection infrastructure, not direct inequality.
+
+## Lean changes
+
+File changed:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
+```
+
+Added a code-comment research note and four thin bridge theorems:
+
+```lean
+theorem sourcePressureBeamMassBalanceLeft_lt_right_of_signChangeUp
+theorem sourcePressureBeamMassBalanceRight_le_left_of_signChangeDown
+theorem sourcePressureBeamMassBalanceLeft_lt_right_of_localIsland_left
+theorem sourcePressureBeamMassBalanceRight_le_left_of_localIsland_right
+```
+
+These theorems do not add propagation.  They only feed existing upstream
+edge-local predicates into the already-closed Beam mass-balance classifier.
+
+## Classification of findings
+
+### True Beam
+
+An upward sign change at the same addressed edge gives:
+
+```lean
+SourcePressureBeamMassBalanceLeftInt n k r j <
+  SourcePressureBeamMassBalanceRightInt n k r j
+```
+
+Local-island left edges provide this upstream condition through
+`sourcePressureSignChangeUp_of_localIsland`.
+
+### Boundary
+
+The exact equality boundary remains the existing cp216 API:
+
+```lean
+SourcePressureBeamMassBalanceLeftInt n k r j =
+  SourcePressureBeamMassBalanceRightInt n k r j
+```
+
+No new upstream equality source was found in this checkpoint.
+
+### False Beam
+
+A downward sign change at the same addressed edge gives the non-strict
+False/Boundary comparison:
+
+```lean
+SourcePressureBeamMassBalanceRightInt n k r j ≤
+  SourcePressureBeamMassBalanceLeftInt n k r j
+```
+
+Local-island right edges provide this upstream condition through
+`sourcePressureSignChangeDown_of_localIsland`.
+
+The strict false branch still requires the existing stricter next-margin
+negative input:
+
+```lean
+sourcePressureMargin_next_neg_iff_massBalanceRight_lt_left
+```
+
+### Gap
+
+No aggregate theorem in `DriftBudget` or `PressureAccounting` currently
+supplies `left < right` for an arbitrary addressed target.  The next viable
+route is an explicit edge bridge:
+
+```text
+interval-pulse address / local witness edge
+  -> sign-change or next-margin sign at that exact edge
+  -> Beam mass-balance comparison
+```
+
+This should remain edge-local unless a later theorem supplies a precise
+coverage or disjointness hypothesis.
+
+## Verification
+
+Commands run:
+
+```bash
+lake build DkMath.Collatz.PetalBridge.PressureBeam
+lake build DkMath.Collatz.PetalBridge
+rg -n "\bsorry\b|admit" \
+  lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean \
+  lean/dk_math/DkMath/Collatz/PetalBridge/DriftBudget.lean \
+  lean/dk_math/DkMath/Collatz/PetalBridge/PressureDecay.lean \
+  lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean \
+  lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean \
+  lean/dk_math/DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
+  lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean \
+  lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
+```
+
+Results:
+
+- `lake build DkMath.Collatz.PetalBridge.PressureBeam`: passed.
+- `lake build DkMath.Collatz.PetalBridge`: passed.
+- no-sorry grep over the inspected pressure files: no matches.
+
+Known unrelated warning still appears during builds:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
+
+## Next candidate
+
+The next natural checkpoint is to connect interval-pulse addresses more
+directly to the Beam mass-balance API.
+
+Candidate shapes:
+
+```lean
+theorem sourcePressureBeamMassBalanceLeft_lt_right_of_intervalPulse_left
+theorem sourcePressureBeamMassBalanceRight_lt_left_of_intervalPulse_right
+```
+
+These should require an addressed target at exactly the pulse edge:
+
+```text
+left edge:  A.start - 1
+right edge: A.start + A.len - 1
+```
+
+This would keep the route local and avoid any claim about arbitrary target
+transport or global family coverage.
````
`````
