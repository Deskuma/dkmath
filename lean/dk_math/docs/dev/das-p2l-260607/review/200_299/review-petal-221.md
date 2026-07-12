# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam

gch: aeaf23b9b5a5d4ad40cd71b3806b6ac0964c7601

## Report

cp220 実装完了です。

[PressureBeam.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean) に witness-to-edge address alignment を追加しました。結論は非対称です。

`SourcePressureLocalIslandWitness` は island center `W.val` を持ち、そこから作る singleton interval-pulse は:

```text
start = W.val
len   = 1
right edge = start + len - 1 = W.val
left edge  = start - 1
```

なので右 edge は Beam addressed target と整合します。一方、左 edge は interval-pulse crossing により margin nonpositive なので、`SourcePressureBeamAddressedDepthTarget` にはなれないことも Lean で固定しました。

追加定理の主なもの:

```lean
sourcePressureBeamAddressedDepthTarget_of_localIslandWitness_mem
sourcePressureIntervalPulseAddress_of_localIslandWitness_rightEdge_eq
sourcePressureBeamAddressedDepthTarget_of_localIslandWitness_intervalPulse_right
sourcePressureBeamMassBalanceRight_le_left_of_localIslandWitness_intervalPulse_right
not_sourcePressureBeamAddressedDepthTarget_intervalPulse_left
not_sourcePressureBeamAddressedDepthTarget_localIslandWitness_intervalPulse_left
```

結果整理は [report-petal-220.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-220.md) に書きました。

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
cp220 はかなり重要な checkpoint になった。

今回の核心は、address alignment が単なる未接続 Gap ではなく、**左右で非対称**だったことじゃ。

```text id="qt1sgc"
witness center = W.val
singleton pulse start = W.val
singleton pulse len = 1

right edge = W.val
left edge  = W.val - 1
```

つまり、witness が自然に持つ Beam addressed target は **右 edge** に整合する。
一方、左 edge は crossing の直前側で margin nonpositive なので、現在の `SourcePressureBeamAddressedDepthTarget` にはなれない。ここを Lean で obstruction として固定できたのが大きい。

## 実装レビュー

追加された主 theorem はこれ。

```lean id="xgvmq2"
sourcePressureBeamAddressedDepthTarget_of_localIslandWitness_mem
sourcePressureIntervalPulseAddress_of_localIslandWitness_rightEdge_eq
sourcePressureBeamAddressedDepthTarget_of_localIslandWitness_intervalPulse_right
sourcePressureBeamMassBalanceRight_le_left_of_localIslandWitness_intervalPulse_right
sourcePressureMargin_next_nonpos_of_localIslandWitness_intervalPulse_right
not_sourcePressureBeamAddressedDepthTarget_intervalPulse_left
not_sourcePressureBeamAddressedDepthTarget_localIslandWitness_intervalPulse_left
```

とても良い構成じゃ。

まず、witness membership から中心 depth の addressed target を作る。

```text id="kdbfda"
W ∈ L
  -> SourcePressureBeamAddressedDepthTarget L W.val
```

これは既存の exact containment と target projection を素直に使っている。

次に、witness-derived singleton pulse の右 edge が `W.val` と一致することを固定。

```text id="ptw0rz"
start + len - 1 = W.val
```

これで、右 edge については

```text id="k8k5j0"
witness membership
  -> addressed target at right edge
  -> interval pulse right theorem
  -> right <= left
  -> next margin nonpositive
```

まで通った。

## 左 edge の obstruction が重要

今回一番よいのは、左 edge を「まだ Gap」とせず、Lean で否定側まで固定したことじゃ。

```lean id="ld19x3"
not_sourcePressureBeamAddressedDepthTarget_intervalPulse_left
```

意味はこう。

```text id="pn5ggo"
interval-pulse left edge:
  margin <= 0

Beam addressed depth target:
  margin > 0

したがって両立しない
```

これは単なる「witness が left edge を持っていない」ではない。
左 edge は構造的に positive target ではない。
つまり、現在の `SourcePressureBeamDepthTarget` のまま True Beam 左端を扱おうとする道は閉じた。

これは立派な **False Beam / obstruction** じゃ。

## 数学的意味

これで構造がかなりはっきりした。

```text id="u8rfrn"
positive run / island の中心:
  BeamDepthTarget になる

right edge:
  witness center と一致するので addressed target と整合する

left edge:
  crossing 前の nonpositive side なので BeamDepthTarget ではない
```

つまり、同じ interval-pulse でも左右の役割が違う。

```text id="qa42w3"
left edge:
  crossing target

inside / center / right edge:
  positive-depth target

right edge transition:
  fall / nonpositive target
```

ここで `SourcePressureBeamDepthTarget` が「正の margin を持つ depth」を意味していることが、逆に明確になった。

## True Beam / Boundary / False Beam / Gap

## True Beam

今回の True Beam は、中心 depth の addressed target 構成じゃ。

```text id="usmohd"
W ∈ L
  -> SourcePressureBeamAddressedDepthTarget L W.val
```

これは witness list が持つ正の depth を Beam target として読める、という基礎事実。

## False / Boundary Beam

右 edge では、

```text id="wx1gav"
witness-derived singleton pulse right edge
  -> right <= left
  -> next margin nonpositive
```

が通った。これは False / Boundary 側。

## Obstruction

左 edge では、

```text id="rf1sv8"
¬ SourcePressureBeamAddressedDepthTarget L (A.start - 1)
```

が通った。
これはかなり価値が高い。左 edge を正の BeamDepthTarget として扱う道を明確に閉じた。

## Gap

残る Gap は report の通り、True Beam 左側を扱うには別語彙が必要ということじゃ。

```text id="rb8qt8"
left edge は positive depth target ではない

しかし left edge は crossing edge ではある
```

したがって次は、`BeamDepthTarget` とは別に、

```text id="n1rw3t"
BeamCrossingEdgeTarget
```

のような語彙を検討するのが自然じゃ。

## 評価

これはかなり良い現場判断じゃ。

Codex は、

```text id="iz9tka"
witness-derived structures can supply the addressed target?
```

という問いに対して、

```text id="jiui6u"
右 edge は yes
左 edge は no, しかも impossible
```

と答えた。

この「非対称」という発見は、こちらが事前に決め打ちできるものではなかった。
現場で Lean に聞いたから見えた事実じゃ。

## 次の checkpoint 方針

次は report の候補通り、**crossing edge target vocabulary** を検討するのがよい。

ただし、ここでも Codex に判断させる。
単純に

```lean id="t4wdf2"
def SourcePressureBeamCrossingEdgeTarget
    (n : OddNat) (k r j : ℕ) : Prop :=
  SourcePressureSignChangeUp n k r j
```

としてよいのか、それとも既存の `SourcePressureSignChangeUp` をそのまま使えば十分なのかを調査させる。

重要なのは、

```text id="rs5uli"
left edge を BeamDepthTarget に無理やり入れない
```

ことじゃ。

## 次の Codex 指示

```text id="qcxwpi"
Checkpoint: petal-221

Goal:
  Investigate whether the Beam layer should introduce a separate crossing-edge
  target vocabulary for interval-pulse left edges.

Context:
  cp220 showed an asymmetry:

    right edge of a witness-derived singleton pulse:
      aligns with W.val and can be a SourcePressureBeamAddressedDepthTarget

    left edge:
      is nonpositive before the crossing and cannot be a
      SourcePressureBeamAddressedDepthTarget

  Therefore, the left edge should not be forced into the positive-depth target
  vocabulary.

Main question:
  Is it useful to add a Beam-facing crossing-edge target, or is the existing
  `SourcePressureSignChangeUp` vocabulary already sufficient?

Candidate idea, only if useful:

  def SourcePressureBeamCrossingEdgeTarget
      (n : OddNat) (k r j : ℕ) : Prop :=
    SourcePressureSignChangeUp n k r j

Possible useful wrappers:
  - crossing edge exposes current nonpositivity
  - crossing edge exposes next positivity
  - interval-pulse left edge gives crossing-edge target
  - crossing-edge target feeds the existing True Beam mass-balance comparison
    at the same edge, without requiring `SourcePressureBeamAddressedDepthTarget`

But do not blindly add a synonym if it only duplicates existing
`SourcePressureSignChangeUp`.

Codex should inspect:
  - current usage of `SourcePressureSignChangeUp`
  - whether Beam-facing naming improves readability
  - whether the left-edge route needs a carrier distinct from
    `SourcePressureBeamAddressedDepthTarget`
  - whether existing cp218 / cp219 sign-change bridges are already enough

Allowed outcomes:
  1. Add a small `SourcePressureBeamCrossingEdgeTarget` API if it clarifies the
     left-edge route.
  2. Add only thin wrappers around `SourcePressureSignChangeUp`, if useful.
  3. Add no Lean code and report that the existing sign-change vocabulary is
     sufficient.

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
  - State whether crossing-edge vocabulary was added or skipped.
  - If added, explain how it differs from positive BeamDepthTarget.
  - If skipped, explain why existing sign-change vocabulary is enough.
  - Classify results as True Beam / Boundary / False Beam / Gap.
  - Make clear this is vocabulary/API design for crossing edges, not
    propagation.

Verification if code changes:
  lake build DkMath.Collatz.PetalBridge.PressureBeam
  lake build DkMath.Collatz.PetalBridge
  no-sorry grep over inspected pressure files
  git diff --check
```

## 一歩先ゆく推論

ここで大事な絵はこれじゃ。

```text id="im7oga"
left edge:
  crossing edge
  current margin <= 0
  next margin > 0

center/right edge:
  positive-depth target
  current margin > 0
  next margin <= 0 at fall side
```

つまり、Beam には少なくとも二種類の edge vocabulary が必要かもしれぬ。

```text id="2hze9y"
DepthTarget:
  positive current margin を持つ点

CrossingEdgeTarget:
  nonpositive から positive へ入る境界
```

これを分けると、今後の証明の読みやすさがかなり上がる可能性がある。

## 総合判断

cp220 は成功。
特に、

```text id="ah9uxr"
left edge is not a BeamDepthTarget
```

を Lean で固定できたのが大きい。

これは回り道ではなく、**行ってはいけない道を閉じた** checkpoint じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
index 0ac72101..0d22b927 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
@@ -1295,4 +1295,141 @@ theorem sourcePressureMargin_next_nonpos_of_intervalPulse_right
   sourcePressureMargin_next_nonpos_of_massBalanceRight_le_left haddr
     (sourcePressureBeamMassBalanceRight_le_left_of_intervalPulse_right A haddr)
 
+/-
+Witness-to-edge address alignment.
+
+Checkpoint 220 asks whether a witness-derived interval pulse can supply the
+Beam addressed target required by the exact-edge API above.  The answer is
+asymmetric for the existing witness carrier:
+
+* `SourcePressureLocalIslandWitness` stores the island center `W.val`;
+* `sourcePressureIntervalPulseAddress_of_localIslandWitness W` is a singleton
+  pulse with `start = W.val` and `len = 1`;
+* hence the right edge `start + len - 1` is exactly `W.val`;
+* the left edge `start - 1` is the depth before the island and is nonpositive
+  by the interval-pulse crossing data, so it cannot be a Beam depth target.
+
+Thus the current witness/list relation aligns with the interval-pulse right
+edge, not with the left edge.  This is an exact-edge fact, not transport.
+-/
+
+/--
+An explicit local-island witness contained in `L` supplies a Beam addressed
+target at its own center depth.
+
+This is the reusable center-depth alignment theorem.  It uses only membership
+of the supplied witness in the supplied list; it does not claim list coverage.
+-/
+theorem sourcePressureBeamAddressedDepthTarget_of_localIslandWitness_mem
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W : SourcePressureLocalIslandWitness n k r}
+    (hmem : W ∈ L) :
+    SourcePressureBeamAddressedDepthTarget L W.val := by
+  have hcontains : SourcePressureBeamSeedContainsDepth L W.val :=
+    ⟨W, hmem, rfl⟩
+  exact
+    sourcePressureBeamAddressedDepthTarget_mk hcontains
+      (sourcePressureBeamDepthTarget_of_seedContainsDepth hcontains)
+
+/--
+The singleton interval-pulse address generated by a local-island witness has
+right edge equal to the witness center.
+-/
+theorem sourcePressureIntervalPulseAddress_of_localIslandWitness_rightEdge_eq
+    {n : OddNat} {k r : ℕ}
+    (W : SourcePressureLocalIslandWitness n k r) :
+    (sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
+        (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1 =
+      W.val := by
+  simp [sourcePressureIntervalPulseAddress_of_localIslandWitness,
+    sourcePressureIntervalPulseAddress_of_localIsland]
+
+/--
+A local-island witness contained in `L` supplies the Beam addressed target at
+the right edge of its generated singleton interval pulse.
+
+This is the positive address-alignment result of cp220.
+-/
+theorem sourcePressureBeamAddressedDepthTarget_of_localIslandWitness_intervalPulse_right
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W : SourcePressureLocalIslandWitness n k r}
+    (hmem : W ∈ L) :
+    SourcePressureBeamAddressedDepthTarget L
+      ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
+        (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) := by
+  rw [sourcePressureIntervalPulseAddress_of_localIslandWitness_rightEdge_eq W]
+  exact sourcePressureBeamAddressedDepthTarget_of_localIslandWitness_mem hmem
+
+/--
+Witness-derived singleton pulses feed the False/Boundary Beam comparison at
+their aligned right edge.
+
+The edge alignment is not assumed externally: it is supplied by membership of
+the witness in the explicit list `L`.
+-/
+theorem sourcePressureBeamMassBalanceRight_le_left_of_localIslandWitness_intervalPulse_right
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W : SourcePressureLocalIslandWitness n k r}
+    (hmem : W ∈ L) :
+    SourcePressureBeamMassBalanceRightInt n k r
+        ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
+          (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) ≤
+      SourcePressureBeamMassBalanceLeftInt n k r
+        ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
+          (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) :=
+  sourcePressureBeamMassBalanceRight_le_left_of_intervalPulse_right
+    (sourcePressureIntervalPulseAddress_of_localIslandWitness W)
+    (sourcePressureBeamAddressedDepthTarget_of_localIslandWitness_intervalPulse_right hmem)
+
+/--
+Witness-derived singleton pulses supply next-margin nonpositivity at their
+aligned right edge.
+-/
+theorem sourcePressureMargin_next_nonpos_of_localIslandWitness_intervalPulse_right
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W : SourcePressureLocalIslandWitness n k r}
+    (hmem : W ∈ L) :
+    SourcePressureMarginInt n k
+        (r +
+          ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
+            (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) +
+          1) ≤ 0 :=
+  sourcePressureMargin_next_nonpos_of_intervalPulse_right
+    (sourcePressureIntervalPulseAddress_of_localIslandWitness W)
+    (sourcePressureBeamAddressedDepthTarget_of_localIslandWitness_intervalPulse_right hmem)
+
+/--
+The left edge of an interval-pulse address cannot be a Beam addressed target.
+
+This is the negative side of the address-alignment investigation.  A Beam
+addressed target implies positive margin at the addressed depth, while the
+interval-pulse left crossing records that the left edge is nonpositive.
+-/
+theorem not_sourcePressureBeamAddressedDepthTarget_intervalPulse_left
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    ¬ SourcePressureBeamAddressedDepthTarget L (A.start - 1) := by
+  intro haddr
+  have hpos := sourcePressureMargin_pos_of_addressedDepthTarget haddr
+  have hnonpos := sourcePressureIntervalPulseAddress_before_start_nonpos A
+  omega
+
+/--
+In particular, a witness-derived singleton interval pulse cannot supply a Beam
+addressed target at its left edge.
+-/
+theorem not_sourcePressureBeamAddressedDepthTarget_localIslandWitness_intervalPulse_left
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (W : SourcePressureLocalIslandWitness n k r) :
+    ¬ SourcePressureBeamAddressedDepthTarget L
+      ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start - 1) :=
+  not_sourcePressureBeamAddressedDepthTarget_intervalPulse_left
+    (sourcePressureIntervalPulseAddress_of_localIslandWitness W)
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-220.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-220.md
new file mode 100644
index 00000000..c50b57ce
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-220.md
@@ -0,0 +1,269 @@
+# report-petal-220
+
+## Checkpoint
+
+`petal-220`
+
+## Goal
+
+Investigate the remaining address-alignment gap between interval-pulse exact
+edges and Beam addressed targets.
+
+cp219 established:
+
+```text
+interval pulse
+  -> exact edge sign-change
+  -> Beam mass-balance comparison
+```
+
+provided that a Beam addressed target is supplied at the same edge.
+
+This checkpoint asks whether witness-derived structures can supply that
+addressed target.
+
+## Structures inspected
+
+### `SourcePressureLocalIslandWitness`
+
+Defined in `PressureAccounting` as:
+
+```lean
+abbrev SourcePressureLocalIslandWitness
+    (n : OddNat) (k r : Nat) :=
+  { j : Nat // SourcePressureLocalIsland n k r j }
+```
+
+The witness stores the local-island center depth:
+
+```text
+W.val
+```
+
+It does not store both pulse edges as separate addresses.
+
+### `sourcePressureIntervalPulseAddress_of_localIslandWitness`
+
+This converts a local-island witness into a singleton interval-pulse address:
+
+```lean
+sourcePressureIntervalPulseAddress_of_localIsland n k r W.val W.property
+```
+
+Therefore the generated pulse has:
+
+```text
+start = W.val
+len   = 1
+```
+
+Its exact edges are:
+
+```text
+left edge  = W.val - 1
+right edge = W.val + 1 - 1 = W.val
+```
+
+### `SourcePressureBeamAddressedDepthTarget`
+
+This requires both:
+
+```lean
+SourcePressureBeamSeedContainsDepth L j
+SourcePressureBeamDepthTarget n k r j
+```
+
+Containment is exact:
+
+```lean
+∃ W ∈ L, W.val = j
+```
+
+Thus a witness list naturally contains the center `W.val`, not the left edge
+`W.val - 1`.
+
+## Lean changes
+
+File changed:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
+```
+
+Added a witness-to-edge alignment comment block and seven theorems:
+
+```lean
+theorem sourcePressureBeamAddressedDepthTarget_of_localIslandWitness_mem
+theorem sourcePressureIntervalPulseAddress_of_localIslandWitness_rightEdge_eq
+theorem sourcePressureBeamAddressedDepthTarget_of_localIslandWitness_intervalPulse_right
+theorem sourcePressureBeamMassBalanceRight_le_left_of_localIslandWitness_intervalPulse_right
+theorem sourcePressureMargin_next_nonpos_of_localIslandWitness_intervalPulse_right
+theorem not_sourcePressureBeamAddressedDepthTarget_intervalPulse_left
+theorem not_sourcePressureBeamAddressedDepthTarget_localIslandWitness_intervalPulse_left
+```
+
+## Main finding
+
+The address alignment is asymmetric.
+
+### Right edge: aligned
+
+For a witness-derived singleton pulse:
+
+```text
+right edge = start + len - 1 = W.val
+```
+
+Since `W ∈ L` supplies exact containment at `W.val`, Lean can construct:
+
+```lean
+SourcePressureBeamAddressedDepthTarget L
+  ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
+    (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1)
+```
+
+This feeds the cp219 interval-pulse right-edge theorem and gives:
+
+```lean
+SourcePressureBeamMassBalanceRightInt n k r rightEdge ≤
+  SourcePressureBeamMassBalanceLeftInt n k r rightEdge
+```
+
+and next-margin nonpositivity at the same right edge.
+
+Classification: `False Beam / Boundary`, exact-edge bridge.
+
+### Left edge: not aligned, and actually impossible as a Beam target
+
+For an interval-pulse address:
+
+```text
+left edge = A.start - 1
+```
+
+The pulse left crossing records:
+
+```lean
+SourcePressureMarginInt n k (r + (A.start - 1)) ≤ 0
+```
+
+But a Beam addressed target implies:
+
+```lean
+0 < SourcePressureMarginInt n k (r + (A.start - 1))
+```
+
+So Lean proves:
+
+```lean
+¬ SourcePressureBeamAddressedDepthTarget L (A.start - 1)
+```
+
+This is stronger than a mere missing containment relation.  The left edge is
+the nonpositive side of the crossing, so it cannot be a Beam depth target under
+the current definition.
+
+Classification: `False / obstruction`, exact-edge negative theorem.
+
+## Boundary
+
+No equality-specific upstream source was added.  The right-edge theorem gives
+the non-strict false/boundary side because `SourcePressureSignChangeDown`
+stores next-margin nonpositivity.
+
+The equality boundary remains the existing mass-balance equality API.
+
+## Gap
+
+The previous “address alignment gap” is now sharpened:
+
+```text
+witness center aligns with singleton pulse right edge
+left edge is not a Beam target at all
+```
+
+Therefore, a future True Beam route cannot use the interval-pulse left edge as
+a Beam addressed target under the current target definition.  It must either:
+
+1. use a separate crossing-edge carrier that does not require positive current
+   margin, or
+2. read True Beam at the next positive depth rather than at the left edge
+   itself, or
+3. introduce a new boundary/crossing target vocabulary distinct from
+   `SourcePressureBeamDepthTarget`.
+
+This is not a failure.  It clarifies that Beam depth targets are positive
+depths, while left crossings live immediately before the positive run.
+
+## Guardrails
+
+The new theorems are exact-edge and witness-local.
+
+They do not assert:
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
+  lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean \
+  lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean \
+  lean/dk_math/DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
+  lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean \
+  lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
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
+The next useful step is to name the left-edge crossing target separately.
+
+Current target:
+
+```lean
+SourcePressureBeamDepthTarget n k r j
+```
+
+means positive current margin.
+
+But the left edge of a pulse is a crossing boundary:
+
+```lean
+SourcePressureMarginInt n k (r + j) ≤ 0
+0 < SourcePressureMarginInt n k (r + j + 1)
+```
+
+Candidate vocabulary:
+
+```lean
+def SourcePressureBeamCrossingEdgeTarget (n : OddNat) (k r j : Nat) : Prop :=
+  SourcePressureSignChangeUp n k r j
+```
+
+This would let the True Beam side talk about crossing edges without falsely
+requiring the left edge itself to be a positive depth target.
````
`````
