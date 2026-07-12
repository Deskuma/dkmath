# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam

gch: ce37a083ea3e2cd8b79c0253e1851a923db73f78

## Report

cp221 実装完了です。

[PressureBeam.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean) に Beam-facing crossing-edge target を追加しました。

追加した中心 API:

```lean
def SourcePressureBeamCrossingEdgeTarget

sourcePressureBeamCrossingEdgeTarget_current_nonpos
sourcePressureBeamCrossingEdgeTarget_next_pos
not_sourcePressureBeamDepthTarget_of_crossingEdgeTarget

sourcePressureMargin_next_pos_iff_massBalanceLeft_lt_right_edge
sourcePressureMargin_next_nonpos_iff_massBalanceRight_le_left_edge

sourcePressureBeamMassBalanceLeft_lt_right_of_crossingEdgeTarget
sourcePressureBeamCrossingEdgeTarget_of_intervalPulse_left
sourcePressureBeamMassBalanceLeft_lt_right_of_intervalPulse_left_crossing
sourcePressureBeamCrossingEdgeTarget_of_localIslandWitness_intervalPulse_left
sourcePressureBeamMassBalanceLeft_lt_right_of_localIslandWitness_intervalPulse_left
```

判断としては、`SourcePressureSignChangeUp` は数学的には十分ですが、Beam 層では `DepthTarget` と `CrossingEdgeTarget` を分ける価値がありました。左 edge は positive depth ではなく、`nonpositive -> positive` の境界なので、`SourcePressureBeamDepthTarget` に押し込まない形で True Beam mass-balance 比較へ接続しました。

整理レポートは [report-petal-221.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-221.md) に追加済みです。

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
cp221 はかなり良い。特に、cp220 で見えた非対称性をそのまま放置せず、語彙として整理したのが大きい。

今回の中心はこれ。

```lean id="mxihkf"
def SourcePressureBeamCrossingEdgeTarget
    (n : OddNat) (k r j : ℕ) : Prop :=
  SourcePressureSignChangeUp n k r j
```

数学的には `SourcePressureSignChangeUp` の薄い別名じゃが、Beam 層では意味がある。
`DepthTarget` は「現在 depth が positive」、`CrossingEdgeTarget` は「現在 nonpositive から次が positive へ入る edge」。この違いを名前で分けたのは正しい。

## 実装レビュー

追加された主な API はこのあたり。

```lean id="v4mwjr"
SourcePressureBeamCrossingEdgeTarget

sourcePressureBeamCrossingEdgeTarget_current_nonpos
sourcePressureBeamCrossingEdgeTarget_next_pos
not_sourcePressureBeamDepthTarget_of_crossingEdgeTarget

sourcePressureMargin_next_pos_iff_massBalanceLeft_lt_right_edge
sourcePressureMargin_next_nonpos_iff_massBalanceRight_le_left_edge

sourcePressureBeamMassBalanceLeft_lt_right_of_crossingEdgeTarget
sourcePressureBeamCrossingEdgeTarget_of_intervalPulse_left
sourcePressureBeamMassBalanceLeft_lt_right_of_intervalPulse_left_crossing
sourcePressureBeamCrossingEdgeTarget_of_localIslandWitness_intervalPulse_left
sourcePressureBeamMassBalanceLeft_lt_right_of_localIslandWitness_intervalPulse_left
```

特に重要なのは、addressed-target 仮定なしの edge-local classifier を追加した点じゃ。

```lean id="lkg0my"
sourcePressureMargin_next_pos_iff_massBalanceLeft_lt_right_edge
sourcePressureMargin_next_nonpos_iff_massBalanceRight_le_left_edge
```

これはかなり効いている。
cp220 で分かった通り、left edge は positive depth ではない。だから `SourcePressureBeamAddressedDepthTarget` を要求してはいけない。

今回の修正で、

```text id="mo9ivh"
left crossing edge
  -> next margin positive
  -> left < right
```

を、positive current depth target に押し込まずに表現できた。これは正しい。

## 数学的意味

今回の整理で、Beam の target 語彙がかなり自然になった。

```text id="z3cu8j"
SourcePressureBeamDepthTarget:
  current margin > 0 の depth

SourcePressureBeamCrossingEdgeTarget:
  current margin <= 0 かつ next margin > 0 の edge
```

つまり、

```text id="y02yla"
depth target
```

と

```text id="ej9faw"
edge target
```

を混同しなくなった。

これはかなり重要じゃ。
Collatz pressure の絵としては、positive island に「入る境界」と「中にいる点」は別物。
cp220 の obstruction はまさにそれを Lean が教えてくれた。

今回の cp221 は、その教訓を API に反映したものじゃ。

## True Beam / Boundary / False Beam / Gap

## True Beam

True Beam 側は大きく進んだ。

```text id="eak0jo"
interval-pulse left edge
  -> CrossingEdgeTarget
  -> left < right
```

さらに witness-derived 版も入った。

```text id="ilyelu"
local-island witness
  -> singleton pulse left edge
  -> CrossingEdgeTarget
  -> left < right
```

これで、以前は `DepthTarget` にできなかった left edge が、正しい語彙で True Beam に接続された。

## Boundary

今回、等号境界は新規には増えていない。
これは妥当じゃ。

crossing edge は `next margin > 0` なので、境界 `next margin = 0` ではない。
境界 API は既存の `massBalanceLeft = right` / `nextMargin = 0` 側に任せてよい。

## False Beam

今回は falling/downward 側の新語彙は追加していない。
ただし edge-local false classifier は追加された。

```lean id="d5pzfh"
sourcePressureMargin_next_nonpos_iff_massBalanceRight_le_left_edge
```

このため、将来 `SourcePressureSignChangeDown` を Beam-facing に包めば、

```text id="uam7u0"
FallingEdgeTarget
  -> right <= left
```

を addressed-target なしで表現できる。

## Gap

残る Gap は、report にある通り、対称な falling-edge vocabulary を入れるかどうかじゃ。

```lean id="zyv3m8"
def SourcePressureBeamFallingEdgeTarget
    (n : OddNat) (k r j : Nat) : Prop :=
  SourcePressureSignChangeDown n k r j
```

これを追加する価値はありそうじゃ。
なぜなら、cp221 で edge-local classifier ができたため、right edge も `DepthTarget` 経由ではなく、falling edge として直接読めるようになるからじゃ。

## 注意点

今回も境界は守れている。

```text id="fhur2b"
arbitrary target transport ではない
global interval coverage ではない
aggregation over witness families ではない
canonical target selection ではない
overlap repair ではない
Collatz convergence ではない
```

これは語彙整理と exact-edge algebra。
過剰主張はない。

## 次の checkpoint 方針

次は、対称 API として `FallingEdgeTarget` を追加する価値があるかを Codex に判断させるのがよい。

ただし、単なる左右対称の美しさだけで追加するのではなく、次の観点で調べさせる。

```text id="olvvz4"
right edge を addressed-target 経由せず、
falling edge として直接 right <= left に接続できるか？
```

これはたぶん有用じゃ。
cp219 の右 edge bridge は `haddr` を要求していた。
でも falling edge API があれば、`SourcePressureSignChangeDown` から直接 `right <= left` を取れるので、right edge も edge vocabulary で統一できる。

## 次の Codex 指示

```text id="s4m5id"
Checkpoint: petal-222

Goal:
  Decide whether to add a symmetric Beam-facing falling-edge target vocabulary.

Context:
  cp221 added:

    SourcePressureBeamCrossingEdgeTarget

  as a Beam-facing vocabulary for:

    SourcePressureSignChangeUp

  This fixed the left-edge route:

    interval-pulse left edge
      -> crossing edge target
      -> next margin positive
      -> left < right

  without incorrectly requiring `SourcePressureBeamDepthTarget`.

Main question:
  Should the Beam layer also introduce:

    SourcePressureBeamFallingEdgeTarget

  as a Beam-facing vocabulary for `SourcePressureSignChangeDown`?

Candidate idea, only if useful:

    def SourcePressureBeamFallingEdgeTarget
        (n : OddNat) (k r j : Nat) : Prop :=
      SourcePressureSignChangeDown n k r j

Possible useful wrappers:
  - falling edge exposes positive/current-side condition if available
  - falling edge exposes next nonpositivity
  - falling edge cannot be a crossing-edge target at the same edge
  - falling edge feeds:
      SourcePressureBeamMassBalanceRightInt n k r j <=
        SourcePressureBeamMassBalanceLeftInt n k r j
    using the edge-local false classifier
  - interval-pulse right edge gives falling-edge target
  - local-island witness singleton pulse right edge gives falling-edge target
  - interval-pulse right edge gives right <= left without requiring
    `SourcePressureBeamAddressedDepthTarget`

Codex should inspect:
  - exact shape of `SourcePressureSignChangeDown`
  - whether it stores current positivity and next nonpositivity
  - existing right-edge interval-pulse sign-change theorem
  - whether the new falling-edge API reduces dependence on
    `SourcePressureBeamAddressedDepthTarget`
  - whether it duplicates too much existing API

Allowed outcomes:
  1. Add a small `SourcePressureBeamFallingEdgeTarget` API if it clarifies the
     right-edge route.
  2. Add only thin wrappers around `SourcePressureSignChangeDown`, if that is
     enough.
  3. Add no Lean code and report that existing right-edge APIs are sufficient.

Guardrails:
  Do not add:
    - arbitrary target transport;
    - global interval coverage;
    - aggregation over witness families;
    - canonical target selection;
    - overlap repair;
    - Collatz convergence.

Report requirements:
  - Explain what Codex inspected.
  - State whether falling-edge vocabulary was added or skipped.
  - If added, explain how it complements:
      DepthTarget
      CrossingEdgeTarget
  - If added, show whether it removes the need for addressed-target hypotheses
    in right-edge false/boundary mass-balance comparisons.
  - If skipped, explain why existing `SourcePressureSignChangeDown` /
    addressed-target APIs are enough.
  - Classify results as True Beam / Boundary / False Beam / Gap.
  - Make clear this is vocabulary/API design for exact falling edges, not
    propagation or coverage.

Verification if code changes:
  lake build DkMath.Collatz.PetalBridge.PressureBeam
  lake build DkMath.Collatz.PetalBridge
  no-sorry grep over inspected pressure files
  git diff --check
```

## 一歩先ゆく推論

cp221 で見えた構造はこうじゃ。

```text id="dk4tul"
CrossingEdgeTarget:
  nonpositive -> positive
  left edge の入口

DepthTarget:
  positive current depth
  island 内部 / center

FallingEdgeTarget:
  positive -> nonpositive
  right edge の出口
```

この三つが揃うと、local pressure island はかなり綺麗に読める。

```text id="gzioip"
入口:
  CrossingEdgeTarget

内部:
  DepthTarget

出口:
  FallingEdgeTarget
```

これはかなり良い構造じゃ。
次は右 edge を `FallingEdgeTarget` として分離できるかを見るのが自然じゃな。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
index 0d22b927..9e09a277 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
@@ -1432,4 +1432,157 @@ theorem not_sourcePressureBeamAddressedDepthTarget_localIslandWitness_intervalPu
   not_sourcePressureBeamAddressedDepthTarget_intervalPulse_left
     (sourcePressureIntervalPulseAddress_of_localIslandWitness W)
 
+/-
+Beam crossing-edge target.
+
+Checkpoint 221 separates two Beam-facing notions that cp220 showed should not
+be conflated:
+
+* `SourcePressureBeamDepthTarget n k r j` means the current depth `j` is already
+  positive;
+* `SourcePressureBeamCrossingEdgeTarget n k r j` means the edge `j -> j + 1`
+  crosses from nonpositive to positive.
+
+The crossing-edge target is intentionally a Beam-facing name for the existing
+`SourcePressureSignChangeUp` predicate.  The new name is useful because the
+left edge of an interval pulse is not a positive-depth target, but it is
+exactly a crossing-edge target.  No propagation, coverage, or target transport
+is introduced here.
+-/
+
+/--
+Beam-facing target for an upward pressure crossing edge.
+
+This is a vocabulary layer over `SourcePressureSignChangeUp`.  It is not a
+positive-depth target: it records a boundary edge whose current margin is
+nonpositive and whose next margin is positive.
+-/
+def SourcePressureBeamCrossingEdgeTarget
+    (n : OddNat) (k r j : ℕ) : Prop :=
+  SourcePressureSignChangeUp n k r j
+
+/-- Crossing-edge targets expose nonpositive current margin. -/
+theorem sourcePressureBeamCrossingEdgeTarget_current_nonpos
+    {n : OddNat} {k r j : ℕ}
+    (h : SourcePressureBeamCrossingEdgeTarget n k r j) :
+    SourcePressureMarginInt n k (r + j) ≤ 0 :=
+  h.1
+
+/-- Crossing-edge targets expose positive next margin. -/
+theorem sourcePressureBeamCrossingEdgeTarget_next_pos
+    {n : OddNat} {k r j : ℕ}
+    (h : SourcePressureBeamCrossingEdgeTarget n k r j) :
+    0 < SourcePressureMarginInt n k (r + j + 1) :=
+  h.2
+
+/--
+A crossing-edge target cannot be a positive Beam depth target at its current
+edge.
+
+This is the API-level version of the cp220 obstruction: the left edge of a
+crossing is a boundary before the positive run, not a positive selected depth.
+-/
+theorem not_sourcePressureBeamDepthTarget_of_crossingEdgeTarget
+    {n : OddNat} {k r j : ℕ}
+    (h : SourcePressureBeamCrossingEdgeTarget n k r j) :
+    ¬ SourcePressureBeamDepthTarget n k r j := by
+  intro htarget
+  have hpos := sourcePressureMargin_pos_of_beamDepthTarget n k r j htarget
+  have hnonpos := sourcePressureBeamCrossingEdgeTarget_current_nonpos h
+  omega
+
+/--
+The next-margin sign is algebraically equivalent to the named mass-balance
+comparison at any edge.
+
+Unlike the older addressed-target spelling, this theorem does not require a
+positive current depth.  That is what the crossing-edge API needs: left
+crossing edges are not Beam depth targets, but their next-margin positivity
+still determines the same mass-balance inequality.
+-/
+theorem sourcePressureMargin_next_pos_iff_massBalanceLeft_lt_right_edge
+    (n : OddNat) (k r j : ℕ) :
+    0 < SourcePressureMarginInt n k (r + j + 1) ↔
+      SourcePressureBeamMassBalanceLeftInt n k r j <
+        SourcePressureBeamMassBalanceRightInt n k r j := by
+  unfold SourcePressureBeamMassBalanceLeftInt
+  unfold SourcePressureBeamMassBalanceRightInt SourcePressureMarginInt
+  omega
+
+/--
+Edge-local false/boundary mass-balance classifier without a positive-depth
+target hypothesis.
+-/
+theorem sourcePressureMargin_next_nonpos_iff_massBalanceRight_le_left_edge
+    (n : OddNat) (k r j : ℕ) :
+    SourcePressureMarginInt n k (r + j + 1) ≤ 0 ↔
+      SourcePressureBeamMassBalanceRightInt n k r j ≤
+        SourcePressureBeamMassBalanceLeftInt n k r j := by
+  unfold SourcePressureBeamMassBalanceLeftInt
+  unfold SourcePressureBeamMassBalanceRightInt SourcePressureMarginInt
+  omega
+
+/--
+Crossing-edge targets feed the True Beam mass-balance comparison at the same
+edge without requiring `SourcePressureBeamAddressedDepthTarget`.
+-/
+theorem sourcePressureBeamMassBalanceLeft_lt_right_of_crossingEdgeTarget
+    {n : OddNat} {k r j : ℕ}
+    (h : SourcePressureBeamCrossingEdgeTarget n k r j) :
+    SourcePressureBeamMassBalanceLeftInt n k r j <
+      SourcePressureBeamMassBalanceRightInt n k r j :=
+  (sourcePressureMargin_next_pos_iff_massBalanceLeft_lt_right_edge n k r j).1
+    (sourcePressureBeamCrossingEdgeTarget_next_pos h)
+
+/--
+An interval-pulse address supplies a Beam crossing-edge target at its exact
+left edge.
+-/
+theorem sourcePressureBeamCrossingEdgeTarget_of_intervalPulse_left
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    SourcePressureBeamCrossingEdgeTarget n k r (A.start - 1) :=
+  sourcePressureIntervalPulseAddress_left_signChange A
+
+/--
+The left edge of an interval-pulse address supplies the True Beam
+mass-balance comparison through the crossing-edge target API.
+
+This is the corrected cp221 replacement for trying to make the left edge into
+`SourcePressureBeamAddressedDepthTarget`.
+-/
+theorem sourcePressureBeamMassBalanceLeft_lt_right_of_intervalPulse_left_crossing
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    SourcePressureBeamMassBalanceLeftInt n k r (A.start - 1) <
+      SourcePressureBeamMassBalanceRightInt n k r (A.start - 1) :=
+  sourcePressureBeamMassBalanceLeft_lt_right_of_crossingEdgeTarget
+    (sourcePressureBeamCrossingEdgeTarget_of_intervalPulse_left A)
+
+/--
+A local-island witness supplies a Beam crossing-edge target at the left edge
+of its generated singleton interval pulse.
+-/
+theorem sourcePressureBeamCrossingEdgeTarget_of_localIslandWitness_intervalPulse_left
+    {n : OddNat} {k r : ℕ}
+    (W : SourcePressureLocalIslandWitness n k r) :
+    SourcePressureBeamCrossingEdgeTarget n k r
+      ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start - 1) :=
+  sourcePressureBeamCrossingEdgeTarget_of_intervalPulse_left
+    (sourcePressureIntervalPulseAddress_of_localIslandWitness W)
+
+/--
+A local-island witness supplies the True Beam mass-balance comparison at the
+left edge of its generated singleton interval pulse.
+-/
+theorem sourcePressureBeamMassBalanceLeft_lt_right_of_localIslandWitness_intervalPulse_left
+    {n : OddNat} {k r : ℕ}
+    (W : SourcePressureLocalIslandWitness n k r) :
+    SourcePressureBeamMassBalanceLeftInt n k r
+        ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start - 1) <
+      SourcePressureBeamMassBalanceRightInt n k r
+        ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start - 1) :=
+  sourcePressureBeamMassBalanceLeft_lt_right_of_crossingEdgeTarget
+    (sourcePressureBeamCrossingEdgeTarget_of_localIslandWitness_intervalPulse_left W)
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-221.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-221.md
new file mode 100644
index 00000000..e3c2420f
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-221.md
@@ -0,0 +1,240 @@
+# report-petal-221
+
+## Checkpoint
+
+`petal-221`
+
+## Goal
+
+Investigate whether the Beam layer should introduce a separate crossing-edge
+target vocabulary for interval-pulse left edges.
+
+cp220 showed:
+
+```text
+right edge:
+  witness center
+  positive Beam depth target
+
+left edge:
+  nonpositive boundary before entering the positive run
+  not a Beam depth target
+```
+
+Therefore the question was whether `SourcePressureSignChangeUp` is enough, or
+whether the Beam layer needs a distinct Beam-facing crossing-edge vocabulary.
+
+## Decision
+
+Added a Beam-facing crossing-edge target API.
+
+The definition is intentionally thin:
+
+```lean
+def SourcePressureBeamCrossingEdgeTarget
+    (n : OddNat) (k r j : Nat) : Prop :=
+  SourcePressureSignChangeUp n k r j
+```
+
+This is not a new mathematical predicate.  It is a Beam-facing vocabulary
+split that prevents left crossing edges from being forced into
+`SourcePressureBeamDepthTarget`.
+
+## Why this is useful
+
+`SourcePressureBeamDepthTarget n k r j` means:
+
+```lean
+0 < SourcePressureMarginInt n k (r + j)
+```
+
+It is a positive current-depth target.
+
+`SourcePressureBeamCrossingEdgeTarget n k r j` means:
+
+```lean
+SourcePressureMarginInt n k (r + j) ≤ 0
+0 < SourcePressureMarginInt n k (r + j + 1)
+```
+
+It is an edge target from a nonpositive boundary into a positive next depth.
+
+This distinction matters because interval-pulse left edges are crossing edges,
+not positive depth targets.
+
+## Lean changes
+
+File changed:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
+```
+
+Added:
+
+```lean
+def SourcePressureBeamCrossingEdgeTarget
+
+theorem sourcePressureBeamCrossingEdgeTarget_current_nonpos
+theorem sourcePressureBeamCrossingEdgeTarget_next_pos
+theorem not_sourcePressureBeamDepthTarget_of_crossingEdgeTarget
+
+theorem sourcePressureMargin_next_pos_iff_massBalanceLeft_lt_right_edge
+theorem sourcePressureMargin_next_nonpos_iff_massBalanceRight_le_left_edge
+
+theorem sourcePressureBeamMassBalanceLeft_lt_right_of_crossingEdgeTarget
+theorem sourcePressureBeamCrossingEdgeTarget_of_intervalPulse_left
+theorem sourcePressureBeamMassBalanceLeft_lt_right_of_intervalPulse_left_crossing
+theorem sourcePressureBeamCrossingEdgeTarget_of_localIslandWitness_intervalPulse_left
+theorem sourcePressureBeamMassBalanceLeft_lt_right_of_localIslandWitness_intervalPulse_left
+```
+
+## Main result
+
+The left-edge True Beam route is now expressed without pretending that the left
+edge is a positive depth target:
+
+```text
+interval-pulse left edge
+  -> SourcePressureBeamCrossingEdgeTarget
+  -> next margin positive
+  -> left < right mass-balance comparison
+```
+
+The key theorem is:
+
+```lean
+sourcePressureBeamMassBalanceLeft_lt_right_of_intervalPulse_left_crossing
+```
+
+and the witness-derived version is:
+
+```lean
+sourcePressureBeamMassBalanceLeft_lt_right_of_localIslandWitness_intervalPulse_left
+```
+
+## Important correction
+
+The earlier addressed-target mass-balance classifiers are still valid, but
+their `SourcePressureBeamAddressedDepthTarget` hypothesis is not necessary for
+pure edge algebra.
+
+For crossing-edge work, this checkpoint added edge-local algebraic classifiers:
+
+```lean
+sourcePressureMargin_next_pos_iff_massBalanceLeft_lt_right_edge
+sourcePressureMargin_next_nonpos_iff_massBalanceRight_le_left_edge
+```
+
+These do not require positive current margin.
+
+This is the right API for crossing edges.
+
+## Classification
+
+### True Beam
+
+Crossing-edge target gives:
+
+```lean
+SourcePressureBeamMassBalanceLeftInt n k r j <
+  SourcePressureBeamMassBalanceRightInt n k r j
+```
+
+because it supplies positive next margin.
+
+### Boundary
+
+No equality-specific crossing-boundary theorem was added.  The boundary layer
+still belongs to the zero next-margin / mass-balance equality API.
+
+### False Beam
+
+The false/boundary edge-local classifier was added as:
+
+```lean
+sourcePressureMargin_next_nonpos_iff_massBalanceRight_le_left_edge
+```
+
+but no new downward-crossing target was introduced in this checkpoint.
+
+### Gap
+
+The current crossing-edge target only covers upward crossings:
+
+```lean
+SourcePressureSignChangeUp
+```
+
+A future symmetric API could introduce:
+
+```lean
+SourcePressureBeamFallingEdgeTarget
+```
+
+as a Beam-facing name for `SourcePressureSignChangeDown`, but this checkpoint
+did not need it because the right-edge route already works through positive
+depth targets and existing downward sign-change wrappers.
+
+## Guardrails
+
+The new API is vocabulary and exact-edge algebra only.
+
+It does not assert:
+
+- arbitrary target transport;
+- global interval coverage;
+- aggregation over witness families;
+- canonical target selection;
+- overlap repair;
+- Collatz convergence.
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
+  lean/dk_math/DkMath/Collatz/PetalBridge/PressureDecay.lean \
+  lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
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
+The natural next step is to decide whether a symmetric falling-edge vocabulary
+is worth adding:
+
+```lean
+def SourcePressureBeamFallingEdgeTarget
+    (n : OddNat) (k r j : Nat) : Prop :=
+  SourcePressureSignChangeDown n k r j
+```
+
+This would make the Beam edge vocabulary symmetric:
+
+```text
+CrossingEdgeTarget: nonpositive -> positive
+FallingEdgeTarget:  positive -> nonpositive
+DepthTarget:        positive current depth
+```
+
+If added, it should stay exact-edge and should not replace the existing
+right-edge positive-depth route.
````
`````
