# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam

gch: 064c98042d827a0f12dcffe498ab906e94f1a4df

## Report

cp222 完了です。

`PressureBeam.lean` に `SourcePressureBeamFallingEdgeTarget` を追加し、右端の出口 edge を Beam 側の語彙として固定しました。これで構図は次の形になります。

```text
CrossingEdgeTarget : entry edge
DepthTarget        : positive current depth
FallingEdgeTarget  : exit edge
```

主な追加は、falling edge から `right <= left` の mass-balance 比較へ直接つなぐ補題と、interval pulse / local-island witness の右端から falling-edge target を得る補題です。これにより、右端 false/boundary 比較で `SourcePressureBeamAddressedDepthTarget` に寄せすぎない API になりました。

レポートも追加しました。

- [PressureBeam.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean)
- [report-petal-222.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-222.md)

検証済みです。

```text
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
rg no-sorry/admit over inspected pressure files
git diff --check
```

既知の unrelated warning として `ZsigmondyCyclotomicResearch.lean` の既存 `sorry` 警告は残っています。

## Review

## 結論

**採用** じゃ。
cp222 は、cp221 の `CrossingEdgeTarget` に対して、対称な出口語彙 `FallingEdgeTarget` を追加した checkpoint じゃな。

これで Beam 側の局所 target 語彙がかなり綺麗に揃った。

```text id="kyb3bq"
CrossingEdgeTarget:
  nonpositive -> positive
  entry edge

DepthTarget:
  positive current depth
  interior / active depth

FallingEdgeTarget:
  positive -> nonpositive
  exit edge
```

これは良い。右端 false/boundary 比較を `SourcePressureBeamAddressedDepthTarget` に寄せすぎず、edge 語彙として直接読めるようになった。

## 実装レビュー

追加された主な API はこれ。

```lean id="ctkain"
SourcePressureBeamFallingEdgeTarget
sourcePressureBeamFallingEdgeTarget_current_pos
sourcePressureBeamFallingEdgeTarget_next_nonpos
sourcePressureBeamDepthTarget_of_fallingEdgeTarget
not_crossingEdgeTarget_and_fallingEdgeTarget
sourcePressureBeamMassBalanceRight_le_left_of_fallingEdgeTarget
sourcePressureBeamFallingEdgeTarget_of_intervalPulse_right
sourcePressureBeamMassBalanceRight_le_left_of_intervalPulse_right_falling
sourcePressureBeamFallingEdgeTarget_of_localIslandWitness_intervalPulse_right
sourcePressureBeamMassBalanceRight_le_left_of_localIslandWitness_intervalPulse_right_falling
```

特に重要なのはこれ。

```lean id="xb5d75"
sourcePressureBeamMassBalanceRight_le_left_of_fallingEdgeTarget
```

意味は、

```text id="knvftr"
FallingEdgeTarget
  -> next margin nonpositive
  -> right <= left
```

じゃ。
これにより、右 edge の false/boundary 側も、positive-depth target を経由せずに edge-local classifier へ接続できる。

## 数学的意味

cp221 で入口が分離された。

```text id="7my65j"
CrossingEdgeTarget:
  left edge
  nonpositive -> positive
```

cp222 で出口も分離された。

```text id="hmh0cd"
FallingEdgeTarget:
  right edge
  positive -> nonpositive
```

これで positive island の局所構造はかなり自然に読める。

```text id="zr8a52"
入口:
  crossing edge

内部:
  positive depth target

出口:
  falling edge
```

この三語彙が分かれたことで、以前の混乱、

```text id="zsn1pj"
left edge を DepthTarget にしてよいのか？
```

が解消された。
左 edge は DepthTarget ではなく CrossingEdgeTarget。
右 edge は DepthTarget でもあり、FallingEdgeTarget でもある。ここが非対称じゃ。

## True Beam / Boundary / False Beam / Gap

## True Beam

入口側。

```text id="3skqob"
CrossingEdgeTarget
  -> left < right
```

これは cp221 から継続。
interval-pulse left edge / witness-derived left edge が True Beam mass-balance 比較へ入る。

## False / Boundary Beam

出口側。

```text id="pc95gs"
FallingEdgeTarget
  -> right <= left
```

これは cp222 の成果。
interval-pulse right edge / witness-derived right edge が false-or-boundary 比較へ入る。

## DepthTarget

今回、

```lean id="n0iey9"
sourcePressureBeamDepthTarget_of_fallingEdgeTarget
```

が入ったのも良い。

```text id="yvvemv"
falling edge は current margin positive なので、
その current edge は DepthTarget でもある
```

つまり、出口点は「positive run の最後の点」でもある。
ここが crossing edge との大きな違いじゃ。

## Gap

残る Gap は report の通り、strict false まではまだ言っていない。

```text id="do7s1a"
FallingEdgeTarget
  -> next margin <= 0
```

であり、

```text id="z10107"
next margin < 0
```

ではない。

したがって、

```text id="jrr8wm"
right <= left
```

までは出るが、

```text id="km6rr9"
right < left
```

にはならない。

これは正しい。境界落ち `nextMargin = 0` を含むからじゃ。

## 注意点

今回も安全境界は守れている。

```text id="ocd0np"
arbitrary target transport ではない
global interval coverage ではない
aggregation over witness families ではない
canonical target selection ではない
overlap repair ではない
Collatz convergence ではない
```

これは exact-edge vocabulary と algebra bridge。
過剰主張はない。

## 小さな注意

report の説明で、`not_crossingEdgeTarget_and_fallingEdgeTarget` について「next margin が positive と nonpositive を同時に要求する」と書いているが、実装上は current margin の符号でも矛盾している。

```text id="j2ghcl"
CrossingEdgeTarget:
  current <= 0, next > 0

FallingEdgeTarget:
  current > 0, next <= 0
```

同じ edge では current 側でも next 側でも矛盾する。
実装は current 側で `omega` しているので問題なし。説明だけ少し補足しておけば十分じゃ。

## 次の checkpoint 方針

次は report の候補通り、**local pulse packaging theorem** が自然じゃ。

ただし、ここでも global coverage に飛ばないこと。

狙いは、

```text id="vqfy3y"
interval pulse A
  -> crossing target at A.start - 1
  -> falling target at A.start + A.len - 1
```

あるいは witness 付きで、

```text id="xe4xrs"
W ∈ L
  -> crossing target at left edge
  -> DepthTarget / AddressedDepthTarget at W.val
  -> falling target at right edge
```

まで。

`interval pulse` 一般について「内部全部が addressed target」と言うのは危険。
まずは exact entry / exit package に留めるのが良い。

## 次の Codex 指示

```text id="s05r33"
Checkpoint: petal-223

Goal:
  Package the local pulse shape using the new Beam edge vocabulary, if doing so
  reduces caller proof noise.

Context:
  The Beam layer now has three local target vocabularies:

    CrossingEdgeTarget:
      nonpositive -> positive entry edge

    DepthTarget:
      positive current depth

    FallingEdgeTarget:
      positive -> nonpositive exit edge

  cp221 connected interval-pulse left edges to CrossingEdgeTarget.
  cp222 connected interval-pulse right edges to FallingEdgeTarget.

Main question:
  Should we add a compact local pulse-shape theorem or predicate that packages:

    interval pulse
      -> crossing target at the exact left edge
      -> falling target at the exact right edge

  and, for witness-derived singleton pulses with `W ∈ L`,

    witness membership
      -> addressed depth target at the center/right edge
      -> crossing target at the left edge
      -> falling target at the right edge

Codex should inspect:
  - existing theorem names around interval-pulse left/right edges;
  - current `SourcePressureBeamCrossingEdgeTarget` and
    `SourcePressureBeamFallingEdgeTarget` APIs;
  - whether a paired theorem would reduce future proof noise;
  - whether a new predicate would add too much API weight;
  - whether general interval-pulse interior facts are already available or
    should be avoided.

Possible useful theorem shapes, only if Lean supports them naturally:

  theorem sourcePressureBeamPulse_edges_of_intervalPulseAddress
      {n : OddNat} {k r : Nat}
      (A : SourcePressureIntervalPulseAddress n k r) :
      SourcePressureBeamCrossingEdgeTarget n k r (A.start - 1) ∧
        SourcePressureBeamFallingEdgeTarget n k r (A.start + A.len - 1)

  theorem sourcePressureBeamPulse_witness_singleton_shape
      {n : OddNat} {k r : Nat}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W : SourcePressureLocalIslandWitness n k r}
      (hmem : W ∈ L) :
      SourcePressureBeamCrossingEdgeTarget n k r
          ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start - 1) ∧
        SourcePressureBeamAddressedDepthTarget L
          ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
            (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) ∧
          SourcePressureBeamFallingEdgeTarget n k r
            ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
              (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1)

  Optionally, if useful, add paired mass-balance comparison packaging:

    left edge:
      left < right

    right edge:
      right <= left

But do not add a theorem claiming coverage of all interval interiors or all
witness families.

Allowed outcomes:
  1. Add a compact paired edge theorem for interval-pulse addresses.
  2. Add a witness-derived singleton pulse-shape theorem.
  3. Add no Lean code and report that existing individual edge APIs are already
     sufficient.
  4. Add only a report if the proposed theorem shapes create API noise.

Guardrails:
  Do not add:
    - arbitrary target transport;
    - global interval coverage;
    - aggregation over witness families;
    - canonical target selection;
    - overlap repair;
    - Collatz convergence;
    - theorem claiming every interior point is addressed unless existing Lean
      facts already prove exact membership/positivity and the statement remains
      local.

Report requirements:
  - Explain what Codex inspected.
  - State whether pulse-shape packaging was added or skipped.
  - If added, explain exact left/right edge indices.
  - If witness theorem is added, explain why the center/right addressed target
    requires `W ∈ L`.
  - Classify results as True Beam / DepthTarget / Falling or Boundary / Gap.
  - Make clear this is local pulse-shape packaging, not coverage or propagation.

Verification if code changes:
  lake build DkMath.Collatz.PetalBridge.PressureBeam
  lake build DkMath.Collatz.PetalBridge
  no-sorry grep over inspected pressure files
  git diff --check
```

## 一歩先ゆく推論

ここまでで、局所 island の「入口・内部・出口」はかなり見えた。

```text id="f9wf0l"
entry:
  CrossingEdgeTarget
  left < right

interior / active:
  DepthTarget
  current margin positive

exit:
  FallingEdgeTarget
  right <= left
```

次の packaging が通れば、`PressureBeam` は局所 pulse をこう扱える。

```text id="9vb1vf"
PulseShape:
  entry + active depth + exit
```

ただし、これはあくまで **一つの pulse / 一つの witness** の話。
複数 pulse の coverage や aggregation はまだ先じゃ。

## 総合判断

cp222 は成功。
これで Beam の edge vocabulary はかなり整った。

次は、個別 theorem をただ増やすのではなく、**入口・内部・出口をまとめて呼べる local pulse API** が必要かどうかを Codex に判断させる段階じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
index 9e09a277..5010fb52 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
@@ -1585,4 +1585,140 @@ theorem sourcePressureBeamMassBalanceLeft_lt_right_of_localIslandWitness_interva
   sourcePressureBeamMassBalanceLeft_lt_right_of_crossingEdgeTarget
     (sourcePressureBeamCrossingEdgeTarget_of_localIslandWitness_intervalPulse_left W)

+/-
+Beam falling-edge target.
+
+Checkpoint 222 completes the symmetric exact-edge vocabulary:
+
+* `SourcePressureBeamCrossingEdgeTarget` reads an entrance edge
+  `nonpositive -> positive`;
+* `SourcePressureBeamFallingEdgeTarget` reads an exit edge
+  `positive -> nonpositive`;
+* `SourcePressureBeamDepthTarget` reads a positive current depth.
+
+The falling-edge target is a Beam-facing name for the existing
+`SourcePressureSignChangeDown` predicate.  It is useful because right-edge
+false/boundary mass-balance comparisons can be read directly from the edge,
+without requiring an addressed positive-depth target carrier.  This is still
+only exact-edge vocabulary and algebra, not propagation or coverage.
+-/
+
+/--
+Beam-facing target for a downward pressure falling edge.
+
+This is a vocabulary layer over `SourcePressureSignChangeDown`: current margin
+is positive and the next margin is nonpositive.
+-/
+def SourcePressureBeamFallingEdgeTarget
+    (n : OddNat) (k r j : ℕ) : Prop :=
+  SourcePressureSignChangeDown n k r j
+
+/-- Falling-edge targets expose positive current margin. -/
+theorem sourcePressureBeamFallingEdgeTarget_current_pos
+    {n : OddNat} {k r j : ℕ}
+    (h : SourcePressureBeamFallingEdgeTarget n k r j) :
+    0 < SourcePressureMarginInt n k (r + j) :=
+  h.1
+
+/-- Falling-edge targets expose nonpositive next margin. -/
+theorem sourcePressureBeamFallingEdgeTarget_next_nonpos
+    {n : OddNat} {k r j : ℕ}
+    (h : SourcePressureBeamFallingEdgeTarget n k r j) :
+    SourcePressureMarginInt n k (r + j + 1) ≤ 0 :=
+  h.2
+
+/--
+A falling-edge target is a positive Beam depth target at its current edge.
+
+This is the main distinction from crossing edges: falling edges start inside a
+positive run, so the current depth is selected.
+-/
+theorem sourcePressureBeamDepthTarget_of_fallingEdgeTarget
+    {n : OddNat} {k r j : ℕ}
+    (h : SourcePressureBeamFallingEdgeTarget n k r j) :
+    SourcePressureBeamDepthTarget n k r j :=
+  sourcePressureBeamDepthTarget_of_margin_pos n k r j
+    (sourcePressureBeamFallingEdgeTarget_current_pos h)
+
+/--
+A crossing edge and a falling edge cannot occur at the same pressure edge.
+
+They demand incompatible signs for the current margin.
+-/
+theorem not_crossingEdgeTarget_and_fallingEdgeTarget
+    {n : OddNat} {k r j : ℕ}
+    (hcross : SourcePressureBeamCrossingEdgeTarget n k r j) :
+    ¬ SourcePressureBeamFallingEdgeTarget n k r j := by
+  intro hfall
+  have hnonpos := sourcePressureBeamCrossingEdgeTarget_current_nonpos hcross
+  have hpos := sourcePressureBeamFallingEdgeTarget_current_pos hfall
+  omega
+
+/--
+A falling-edge target feeds the False/Boundary Beam mass-balance comparison at
+the same edge without requiring `SourcePressureBeamAddressedDepthTarget`.
+-/
+theorem sourcePressureBeamMassBalanceRight_le_left_of_fallingEdgeTarget
+    {n : OddNat} {k r j : ℕ}
+    (h : SourcePressureBeamFallingEdgeTarget n k r j) :
+    SourcePressureBeamMassBalanceRightInt n k r j ≤
+      SourcePressureBeamMassBalanceLeftInt n k r j :=
+  (sourcePressureMargin_next_nonpos_iff_massBalanceRight_le_left_edge n k r j).1
+    (sourcePressureBeamFallingEdgeTarget_next_nonpos h)
+
+/--
+An interval-pulse address supplies a Beam falling-edge target at its exact
+right edge.
+-/
+theorem sourcePressureBeamFallingEdgeTarget_of_intervalPulse_right
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    SourcePressureBeamFallingEdgeTarget n k r (A.start + A.len - 1) :=
+  sourcePressureIntervalPulseAddress_right_signChange A
+
+/--
+The right edge of an interval-pulse address supplies the False/Boundary
+mass-balance comparison through the falling-edge target API.
+
+Unlike the older right-edge theorem, this version does not require an
+addressed-depth target hypothesis.
+-/
+theorem sourcePressureBeamMassBalanceRight_le_left_of_intervalPulse_right_falling
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    SourcePressureBeamMassBalanceRightInt n k r (A.start + A.len - 1) ≤
+      SourcePressureBeamMassBalanceLeftInt n k r (A.start + A.len - 1) :=
+  sourcePressureBeamMassBalanceRight_le_left_of_fallingEdgeTarget
+    (sourcePressureBeamFallingEdgeTarget_of_intervalPulse_right A)
+
+/--
+A local-island witness supplies a Beam falling-edge target at the right edge
+of its generated singleton interval pulse.
+-/
+theorem sourcePressureBeamFallingEdgeTarget_of_localIslandWitness_intervalPulse_right
+    {n : OddNat} {k r : ℕ}
+    (W : SourcePressureLocalIslandWitness n k r) :
+    SourcePressureBeamFallingEdgeTarget n k r
+      ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
+        (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) :=
+  sourcePressureBeamFallingEdgeTarget_of_intervalPulse_right
+    (sourcePressureIntervalPulseAddress_of_localIslandWitness W)
+
+/--
+A local-island witness supplies the False/Boundary Beam comparison at the
+right edge of its generated singleton interval pulse through the falling-edge
+target API.
+-/
+theorem sourcePressureBeamMassBalanceRight_le_left_of_localIslandWitness_intervalPulse_right_falling
+    {n : OddNat} {k r : ℕ}
+    (W : SourcePressureLocalIslandWitness n k r) :
+    SourcePressureBeamMassBalanceRightInt n k r
+        ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
+          (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) ≤
+      SourcePressureBeamMassBalanceLeftInt n k r
+        ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
+          (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) :=
+  sourcePressureBeamMassBalanceRight_le_left_of_fallingEdgeTarget
+    (sourcePressureBeamFallingEdgeTarget_of_localIslandWitness_intervalPulse_right W)
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-222.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-222.md
new file mode 100644
index 00000000..9788c0e2
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-222.md
@@ -0,0 +1,141 @@
+# Report: petal-222
+
+## Checkpoint
+
+`petal-222` asked whether the Beam layer should introduce a symmetric
+falling-edge vocabulary for the right edge of a local pressure island.
+
+The implemented answer is yes:
+
+```lean
+def SourcePressureBeamFallingEdgeTarget
+    (n : OddNat) (k r j : Nat) : Prop :=
+  SourcePressureSignChangeDown n k r j
+```
+
+This is intentionally a thin Beam-facing name.  It does not add propagation,
+coverage, canonical target selection, overlap repair, or any Collatz convergence
+claim.
+
+## What was inspected
+
+- `SourcePressureSignChangeDown` already stores the two facts needed for an exit
+  edge:
+  - the current margin is positive;
+  - the next margin is nonpositive.
+- cp221 had already supplied the edge-local classifier:
+  - positive next margin iff left mass balance is strictly larger;
+  - nonpositive next margin iff right mass balance is at most the left mass
+    balance.
+- The interval-pulse right edge already gives `SourcePressureSignChangeDown`.
+- The local-island singleton witness route already exposes the same interval
+  pulse.
+
+Therefore the new vocabulary can remove unnecessary dependence on
+`SourcePressureBeamAddressedDepthTarget` for the right-edge false/boundary
+mass-balance comparison.
+
+## Implemented theorem surface
+
+Added in `DkMath.Collatz.PetalBridge.PressureBeam`:
+
+```lean
+SourcePressureBeamFallingEdgeTarget
+sourcePressureBeamFallingEdgeTarget_current_pos
+sourcePressureBeamFallingEdgeTarget_next_nonpos
+sourcePressureBeamDepthTarget_of_fallingEdgeTarget
+not_crossingEdgeTarget_and_fallingEdgeTarget
+sourcePressureBeamMassBalanceRight_le_left_of_fallingEdgeTarget
+sourcePressureBeamFallingEdgeTarget_of_intervalPulse_right
+sourcePressureBeamMassBalanceRight_le_left_of_intervalPulse_right_falling
+sourcePressureBeamFallingEdgeTarget_of_localIslandWitness_intervalPulse_right
+sourcePressureBeamMassBalanceRight_le_left_of_localIslandWitness_intervalPulse_right_falling
+```
+
+The important operational bridge is:
+
+```lean
+SourcePressureBeamFallingEdgeTarget n k r j
+  -> SourcePressureBeamMassBalanceRightInt n k r j
+       <= SourcePressureBeamMassBalanceLeftInt n k r j
+```
+
+This now follows directly from the falling edge and the edge-local classifier.
+
+## Complementarity
+
+The three Beam target names now form a small local-island vocabulary:
+
+```text
+CrossingEdgeTarget:
+  nonpositive -> positive
+  entry edge
+
+DepthTarget:
+  positive current depth
+  interior / active depth
+
+FallingEdgeTarget:
+  positive -> nonpositive
+  exit edge
+```
+
+`not_crossingEdgeTarget_and_fallingEdgeTarget` records that the same edge cannot
+be both an entry edge and an exit edge, because the next margin cannot be both
+positive and nonpositive.
+
+## Classification
+
+- True Beam:
+  The entry-side route remains cp221's `CrossingEdgeTarget`, which gives the
+  strict left/right classifier.
+
+- Boundary / False Beam:
+  `FallingEdgeTarget` gives `right <= left` at the exact exit edge.  This covers
+  the false-or-boundary comparison without requiring an addressed-depth target.
+
+- Boundary:
+  Equality remains handled by the existing mass-balance equality vocabulary.
+  This checkpoint does not add a new equality-specific falling-edge theorem.
+
+- Gap:
+  No claim is made about all edges in an interval, propagation past an edge, or
+  global coverage of every source.  Strict false would require a strictly
+  negative next-margin hypothesis, not merely nonpositivity.
+
+## Verification
+
+Completed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureBeam
+lake build DkMath.Collatz.PetalBridge
+rg -n "\bsorry\b|admit" over PressureBeam / PressureDecay / PressureFrontier
+git diff --check
+```
+
+The inspected pressure files have no new `sorry` / `admit` matches.
+
+`PressureBeam.lean` is now 1724 lines, still below the 2000-line split criterion.
+
+Known unrelated project warning remains:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses 'sorry'
+```
+
+## Next inference
+
+The next natural small step is not global coverage.  A safer direction is a
+local pulse packaging theorem:
+
+```text
+interval pulse
+  -> crossing target at the left edge
+  -> positive depth inside the addressed island
+  -> falling target at the right edge
+```
+
+This would package the entry/interior/exit vocabulary without claiming that such
+pulses cover all pressure behavior.
````
`````
