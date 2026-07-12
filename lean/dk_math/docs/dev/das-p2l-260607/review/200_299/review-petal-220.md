# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam

gch: 27584dc13c860e2f3906a2f0ce3e90c83d220f29

## Report

cp219 実装完了です。

[PressureBeam.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean) に interval-pulse address から Beam mass-balance API への exact-edge bridge を追加しました。

追加定理:

```lean
sourcePressureBeamMassBalanceLeft_lt_right_of_intervalPulse_left
sourcePressureBeamMassBalanceRight_le_left_of_intervalPulse_right
sourcePressureMargin_next_pos_of_intervalPulse_left
sourcePressureMargin_next_nonpos_of_intervalPulse_right
```

調査結果として、interval-pulse address はすでに `PressureFrontier` 側で exact edge の sign-change を持っていました。

```text
left edge  = A.start - 1
right edge = A.start + A.len - 1
```

なので今回は missing relation ではなく、既存 sign-change を cp218 の Beam classifier に接続するだけで通りました。内容は [report-petal-219.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-219.md) に整理済みです。

検証:

```text
lake build DkMath.Collatz.PetalBridge.PressureBeam  passed
lake build DkMath.Collatz.PetalBridge               passed
no-sorry grep over inspected pressure files          no matches
git diff --check                                     passed
```

既知の unrelated warning として `ZsigmondyCyclotomicResearch.lean` の既存 `sorry` は引き続き表示されています。

## Review

## 結論

**採用** じゃ。
cp219 は良い。しかも、今回も Codex が現場でちゃんと判断している。

狙いは、

```text id="e46ui1"
interval-pulse address
  -> exact edge
  -> Beam mass-balance comparison
```

だった。調査の結果、`PressureFrontier` 側にはすでに exact edge の sign-change API があり、

```text id="cdrzq1"
left edge  = A.start - 1
right edge = A.start + A.len - 1
```

として接続できることが確認された。つまり今回は missing relation ではなく、既存の sign-change を cp218 の Beam classifier に接続するだけで通った、という整理になっている。これはかなり良い。

## 実装レビュー

追加された定理はこの 4 本。

```lean id="jt30wv"
sourcePressureBeamMassBalanceLeft_lt_right_of_intervalPulse_left
sourcePressureBeamMassBalanceRight_le_left_of_intervalPulse_right
sourcePressureMargin_next_pos_of_intervalPulse_left
sourcePressureMargin_next_nonpos_of_intervalPulse_right
```

どれも exact-edge local statement になっている。

左 edge 側は、

```text id="dq7fep"
A.start - 1
```

で `signChangeUp` を取り、

```text id="haevvt"
left < right
```

へ接続する。

右 edge 側は、

```text id="qxuoap"
A.start + A.len - 1
```

で `signChangeDown` を取り、

```text id="ba4yva"
right <= left
```

へ接続する。

ここで重要なのは、`haddr` を同じ exact edge に要求していることじゃ。

```text id="p5hc16"
interval-pulse の edge
  と
Beam addressed target の edge
```

が一致している場合だけ通す。
これにより、arbitrary target transport や global coverage へ飛んでいない。

## 数学的意味

cp218 では、

```text id="r2nbwu"
signChangeUp   -> left < right
signChangeDown -> right <= left
```

までだった。

cp219 で、

```text id="ok0d4i"
interval-pulse left edge
  -> signChangeUp
  -> left < right
```

```text id="xy3r18"
interval-pulse right edge
  -> signChangeDown
  -> right <= left
```

まで接続された。

つまり、Beam classifier に入力を与える上流構造として、

```text id="gkp461"
local island
interval pulse address
sign change
```

が使えるようになってきた。

これはかなり大きい。
`PressureAccounting` / `PressureFrontier` 側の witness/interval 情報が、`PressureBeam` の mass-balance decision surface に入る道が見え始めている。

## True Beam / False Beam / Gap

## True Beam

今回の True Beam はこれ。

```text id="rawhpr"
interval-pulse address at left edge
and
addressed Beam target at A.start - 1

  -> left < right
  -> nextMargin positive
```

sign 版の theorem も入っているので、caller は mass-balance inequality を経由せず、直接 next positivity を使える。

## False / Boundary Beam

右 edge は non-strict じゃ。

```text id="x7cy6k"
interval-pulse address at right edge
and
addressed Beam target at A.start + A.len - 1

  -> right <= left
  -> nextMargin nonpositive
```

これは False / Boundary。
strict false ではない。`SourcePressureSignChangeDown` が nonpositive なので、この扱いは正しい。

## Gap

今回の report が明確にしている Gap はこれ。

```text id="x3wnjw"
interval-pulse exact edge
  and
Beam addressed target edge
```

が同じ index であることを、まだ外から与える必要がある。

つまり、

```text id="oo8r27"
interval-pulse がある
```

だけでは、

```text id="rci390"
その edge が Beam addressed target である
```

とは言っていない。

この Gap を残したのは正しい。
ここを勝手に埋めると、target transport や coverage を言ってしまう危険がある。

## 注意点

今回も境界は守れている。

```text id="ngorgj"
arbitrary target transport ではない
global interval coverage ではない
aggregation over witness families ではない
overlap repair ではない
canonical next target selection ではない
Collatz convergence ではない
```

これは exact-edge bridge。
局所の橋として採用できる。

## 次の checkpoint 方針

次は report の候補通り、

```text id="p7w9t8"
local-island witness
  -> interval-pulse address
  -> exact left/right edge
  -> addressed Beam target at same edge
```

を調査するのが自然じゃ。

ただし、ここはかなり重要な分岐じゃ。

今の Gap は「address alignment」。
つまり、pulse edge と Beam addressed target をどう同一視するか。

これは単純に theorem を足すというより、Codex に現場で調べさせるべき。

```text id="lsyoj6"
SourcePressureLocalIslandWitness はどの depth を address しているのか

SourcePressureIntervalPulseAddress は witness から作れるのか

left edge / right edge は witness depth とどう対応するのか

containsDepth relation から edge target を取り出せるのか
```

このあたりを調査させるのが良い。

## 次の Codex 指示

```text id="sp0437"
Checkpoint: petal-220

Goal:
  Investigate the remaining address-alignment gap between interval-pulse exact
  edges and Beam addressed targets.

Context:
  cp219 connected interval-pulse addresses to Beam mass-balance comparisons at
  exact edges, but only when a Beam addressed target is supplied at the same
  edge.

  The remaining gap is:

    interval-pulse exact edge
      and
    Beam addressed target edge

  must align explicitly.

Main question:
  Can witness-derived structures already supply
  `SourcePressureBeamAddressedDepthTarget L edge`
  for the exact interval-pulse left or right edge?

Modules to inspect:
  - DkMath.Collatz.PetalBridge.PressureBeam
  - DkMath.Collatz.PetalBridge.PressureAccounting
  - DkMath.Collatz.PetalBridge.PressureFrontier
  - DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
  - DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
  - DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition

Codex should use workspace judgment:
  - inspect `SourcePressureLocalIslandWitness`;
  - inspect how witness depths relate to local islands;
  - inspect interval-pulse address constructors and projections;
  - inspect whether witness lists contain the left edge, right edge, island
    center, or some derived depth;
  - use `#check`, `#print`, and scratch lemmas;
  - decide whether a theorem can be added safely or whether this should remain
    a report-only Gap.

Do not force a theorem.

Possible useful outcomes:

  Outcome 1:
    Add an exact-edge theorem if Lean shows that a witness/list relation can
    supply the addressed target at the interval-pulse left edge.

  Outcome 2:
    Add an exact-edge theorem if Lean shows that a witness/list relation can
    supply the addressed target at the interval-pulse right edge.

  Outcome 3:
    Add a smaller bridge from witness/list containment to addressed target at
    the appropriate edge, if that is the real missing reusable layer.

  Outcome 4:
    Add no Lean code and report the exact mismatch:
      - witness depth is island center, not edge;
      - interval-pulse edge is `start - 1` or `start + len - 1`;
      - `SourcePressureBeamAddressedDepthTarget` requires exact containment;
      - no existing theorem maps witness depth to pulse edge target.

Guardrails:
  Do not add:
    - arbitrary target transport;
    - global interval coverage;
    - aggregation over all witness families;
    - canonical target selection;
    - overlap repair;
    - Collatz convergence.

Report requirements:
  - Explain what Codex inspected.
  - State exact witness-depth and pulse-edge shapes discovered.
  - State whether address alignment is already available or missing.
  - If a theorem is added, classify it as an exact-edge bridge.
  - If no theorem is added, identify the precise missing relation.
  - Classify findings as True Beam / Boundary / False Beam / Gap.
  - Make clear this is address-alignment investigation, not coverage or
    propagation.

Verification if code changes:
  lake build DkMath.Collatz.PetalBridge.PressureBeam
  lake build DkMath.Collatz.PetalBridge
  no-sorry grep over inspected pressure files
  git diff --check
```

## 一歩先ゆく推論

ここが次の大事な山じゃな。

現在の構造は、

```text id="gqwsyd"
interval pulse
  -> exact edge sign-change
  -> Beam mass-balance comparison
```

まで来た。

でも、Beam 側にはまだ

```text id="o09xcz"
SourcePressureBeamAddressedDepthTarget L edge
```

が必要。

つまり次は、

```text id="nfd12r"
witness/list address
  -> exact edge addressed target
```

を得られるかどうか。

もしこれが通れば、かなり強い。

```text id="uk7nxh"
witness / interval pulse
  -> addressed Beam target
  -> mass-balance comparison
  -> next sign
```

という流れができる。

ただし、もし witness が island center を持つだけで、edge を持たないなら、ここは Gap として残すべきじゃ。
無理に transport してはいけない。

## 総合判断

cp219 は成功。
そして次の課題ははっきりした。

```text id="c63kpy"
分類器はある。
interval pulse も edge sign-change を持つ。
残るは、Beam addressed target と edge の alignment。
```

ここは Codex の現場調査力を使うのが正解じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
index 17404aa6..0ac72101 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
@@ -1210,4 +1210,89 @@ theorem sourcePressureBeamMassBalanceRight_le_left_of_localIsland_right
   sourcePressureBeamMassBalanceRight_le_left_of_signChangeDown haddr
     (sourcePressureSignChangeDown_of_localIsland n k r j hisland)
 
+/-
+Interval-pulse exact-edge bridge.
+
+Checkpoint 219 connects the interval-pulse address layer back into the Beam
+classifier.  The important point is that the edge indices are not invented:
+
+* left edge  = `A.start - 1`
+* right edge = `A.start + A.len - 1`
+
+`PressureFrontier` already stores sign-change facts at exactly these edges via
+`sourcePressureIntervalPulseAddress_left_signChange` and
+`sourcePressureIntervalPulseAddress_right_signChange`.  Therefore the Beam
+bridge is only a local exact-edge composition through the cp218 sign-change
+API.  It does not assert interval coverage, family aggregation, overlap repair,
+or target transport.
+-/
+
+/--
+An interval-pulse address supplies the True Beam mass-balance inequality at
+its exact left edge.
+
+The addressed target hypothesis is for `A.start - 1`, matching the edge stored
+by `sourcePressureIntervalPulseAddress_left_signChange`.
+-/
+theorem sourcePressureBeamMassBalanceLeft_lt_right_of_intervalPulse_left
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (A : SourcePressureIntervalPulseAddress n k r)
+    (haddr : SourcePressureBeamAddressedDepthTarget L (A.start - 1)) :
+    SourcePressureBeamMassBalanceLeftInt n k r (A.start - 1) <
+      SourcePressureBeamMassBalanceRightInt n k r (A.start - 1) :=
+  sourcePressureBeamMassBalanceLeft_lt_right_of_signChangeUp haddr
+    (sourcePressureIntervalPulseAddress_left_signChange A)
+
+/--
+An interval-pulse address supplies the False/Boundary Beam comparison at its
+exact right edge.
+
+The addressed target hypothesis is for `A.start + A.len - 1`, matching the
+edge stored by `sourcePressureIntervalPulseAddress_right_signChange`.
+-/
+theorem sourcePressureBeamMassBalanceRight_le_left_of_intervalPulse_right
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (A : SourcePressureIntervalPulseAddress n k r)
+    (haddr :
+      SourcePressureBeamAddressedDepthTarget L (A.start + A.len - 1)) :
+    SourcePressureBeamMassBalanceRightInt n k r (A.start + A.len - 1) ≤
+      SourcePressureBeamMassBalanceLeftInt n k r (A.start + A.len - 1) :=
+  sourcePressureBeamMassBalanceRight_le_left_of_signChangeDown haddr
+    (sourcePressureIntervalPulseAddress_right_signChange A)
+
+/--
+An interval-pulse address supplies next-margin positivity at its exact left
+edge.
+
+This is a caller-friendly sign statement parallel to the mass-balance form.
+It remains exact-edge only.
+-/
+theorem sourcePressureMargin_next_pos_of_intervalPulse_left
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (A : SourcePressureIntervalPulseAddress n k r)
+    (haddr : SourcePressureBeamAddressedDepthTarget L (A.start - 1)) :
+    0 < SourcePressureMarginInt n k (r + (A.start - 1) + 1) :=
+  sourcePressureMargin_next_pos_of_massBalanceLeft_lt_right haddr
+    (sourcePressureBeamMassBalanceLeft_lt_right_of_intervalPulse_left A haddr)
+
+/--
+An interval-pulse address supplies next-margin nonpositivity at its exact right
+edge.
+
+This is the sign-form companion of
+`sourcePressureBeamMassBalanceRight_le_left_of_intervalPulse_right`.
+-/
+theorem sourcePressureMargin_next_nonpos_of_intervalPulse_right
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (A : SourcePressureIntervalPulseAddress n k r)
+    (haddr :
+      SourcePressureBeamAddressedDepthTarget L (A.start + A.len - 1)) :
+    SourcePressureMarginInt n k (r + (A.start + A.len - 1) + 1) ≤ 0 :=
+  sourcePressureMargin_next_nonpos_of_massBalanceRight_le_left haddr
+    (sourcePressureBeamMassBalanceRight_le_left_of_intervalPulse_right A haddr)
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-219.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-219.md
new file mode 100644
index 00000000..5ea17ebb
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-219.md
@@ -0,0 +1,226 @@
+# report-petal-219
+
+## Checkpoint
+
+`petal-219`
+
+## Goal
+
+Investigate whether interval-pulse addresses can be connected to the Beam
+mass-balance API at exact edges.
+
+The cp218 result established the direct local route:
+
+```text
+signChangeUp   -> left < right
+signChangeDown -> right <= left
+```
+
+This checkpoint checks whether the interval-pulse address layer supplies those
+sign-change inputs.
+
+## Definitions and theorems inspected
+
+### `SourcePressureIntervalPulse`
+
+Located in `PressureFrontier`.
+
+It packages:
+
+```lean
+SourcePressureRun n k r a len
+SourcePressureRunHasLeftCrossing n k r a len
+SourcePressureRunHasRightFall n k r a len
+```
+
+The important boundary predicates are:
+
+```lean
+SourcePressureRunHasLeftCrossing n k r a len
+  = 0 < a ∧ SourcePressureSignChangeUp n k r (a - 1)
+
+SourcePressureRunHasRightFall n k r a len
+  = SourcePressureSignChangeDown n k r (a + len - 1)
+```
+
+### `SourcePressureIntervalPulseAddress`
+
+Located in `PressureFrontier`.
+
+It stores:
+
+```lean
+start : Nat
+len   : Nat
+hpulse : SourcePressureIntervalPulse n k r start len
+```
+
+The exact edge shapes are therefore:
+
+```text
+left edge  = A.start - 1
+right edge = A.start + A.len - 1
+```
+
+### Existing exact-edge sign-change API
+
+Already available:
+
+```lean
+sourcePressureIntervalPulseAddress_left_signChange
+sourcePressureIntervalPulseAddress_right_signChange
+```
+
+These are stronger than just net-drop positivity/negativity.  They directly
+supply:
+
+```lean
+SourcePressureSignChangeUp n k r (A.start - 1)
+SourcePressureSignChangeDown n k r (A.start + A.len - 1)
+```
+
+The `PressureAccounting` lemmas:
+
+```lean
+sourcePressureIntervalPulseAddress_left_netDrop_pos
+sourcePressureIntervalPulseAddress_right_netDrop_neg
+```
+
+are useful derived facts, but the sign-change bridge was already present in
+the upstream address layer.
+
+## Lean changes
+
+File changed:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
+```
+
+Added exact-edge interval-pulse bridge comments and four theorems:
+
+```lean
+theorem sourcePressureBeamMassBalanceLeft_lt_right_of_intervalPulse_left
+theorem sourcePressureBeamMassBalanceRight_le_left_of_intervalPulse_right
+theorem sourcePressureMargin_next_pos_of_intervalPulse_left
+theorem sourcePressureMargin_next_nonpos_of_intervalPulse_right
+```
+
+These are all exact-edge local statements.  They do not transport arbitrary
+targets, aggregate interval families, repair overlap, or claim coverage.
+
+## Classification
+
+### True Beam
+
+An interval-pulse address supplies a True Beam inequality at its exact left
+edge:
+
+```lean
+SourcePressureBeamMassBalanceLeftInt n k r (A.start - 1) <
+  SourcePressureBeamMassBalanceRightInt n k r (A.start - 1)
+```
+
+provided the Beam addressed-target carrier is also supplied at that same edge:
+
+```lean
+SourcePressureBeamAddressedDepthTarget L (A.start - 1)
+```
+
+### False Beam / Boundary
+
+An interval-pulse address supplies the non-strict false/boundary comparison at
+its exact right edge:
+
+```lean
+SourcePressureBeamMassBalanceRightInt n k r (A.start + A.len - 1) ≤
+  SourcePressureBeamMassBalanceLeftInt n k r (A.start + A.len - 1)
+```
+
+provided the Beam addressed-target carrier is also supplied at that same edge:
+
+```lean
+SourcePressureBeamAddressedDepthTarget L (A.start + A.len - 1)
+```
+
+This is non-strict because the right boundary stores
+`SourcePressureSignChangeDown`, which says the next margin is nonpositive.
+Strict false still requires a strictly negative next margin.
+
+### Boundary
+
+No new equality-specific upstream source was added.  The equality boundary
+remains the existing mass-balance equality API in `PressureBeam`.
+
+### Gap
+
+The remaining gap is not interval-pulse-to-sign-change.  That bridge already
+exists.
+
+The remaining gap is address alignment:
+
+```text
+interval-pulse exact edge
+  and
+Beam addressed target edge
+```
+
+must be supplied for the same index.  This is intentional: the theorem should
+not invent target transport or claim that every pulse edge is automatically a
+Beam addressed target.
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
+  lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean \
+  lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean \
+  lean/dk_math/DkMath/Collatz/PetalBridge/PressureDecay.lean
+git diff --check
+```
+
+Results:
+
+- `lake build DkMath.Collatz.PetalBridge.PressureBeam`: passed.
+- `lake build DkMath.Collatz.PetalBridge`: passed.
+- no-sorry grep over inspected files: no matches.
+- `git diff --check`: passed.
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
+The next natural bridge is not another local classifier.  The classifier now
+accepts:
+
+```text
+local island
+interval pulse address
+sign change
+```
+
+The next useful question is whether witness-derived pulse addresses can supply
+the required Beam addressed-target carrier at the same exact edge, without
+claiming global coverage.
+
+Candidate direction:
+
+```text
+local-island witness
+  -> interval-pulse address
+  -> exact left/right edge
+  -> addressed Beam target at the same edge
+```
+
+This should remain an explicit witness/edge theorem, not a family coverage or
+canonical target selection theorem.
````
`````
