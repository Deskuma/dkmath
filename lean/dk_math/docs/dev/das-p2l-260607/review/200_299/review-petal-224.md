# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam

gch: fa6ee04a7ac07dd9b6fca94f5c05c8aff6e6b915

## Report

cp223 完了です。

`PressureBeam.lean` に local pulse shape の薄い packaging theorem を追加しました。新しい predicate は増やさず、既存の `CrossingEdgeTarget / AddressedDepthTarget / FallingEdgeTarget` を `∧` でまとめるだけにしています。

追加した主な補題:

```lean
sourcePressureBeamPulse_edges_of_intervalPulseAddress
sourcePressureBeamPulse_massBalance_edges_of_intervalPulseAddress
sourcePressureBeamPulse_witness_singleton_shape
sourcePressureBeamPulse_witness_singleton_massBalance_edges
```

レポートも追加済みです。

- [PressureBeam.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean)
- [report-petal-223.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-223.md)

検証済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
rg no-sorry/admit over inspected pressure files
git diff --check
```

`PressureBeam.lean` は 1821 行で、まだ 2000 行の分割基準未満です。既知の unrelated warning として `ZsigmondyCyclotomicResearch.lean` の既存 `sorry` 警告だけ残っています。

## Review

## 結論

**採用** じゃ。
cp223 は、local pulse shape の整理としてちょうどよい粒度になっている。

今回追加されたのは、新しい predicate ではなく、既存の三語彙を `∧` でまとめる薄い theorem packaging。

```lean id="f5b41t"
sourcePressureBeamPulse_edges_of_intervalPulseAddress
sourcePressureBeamPulse_massBalance_edges_of_intervalPulseAddress
sourcePressureBeamPulse_witness_singleton_shape
sourcePressureBeamPulse_witness_singleton_massBalance_edges
```

これは良い判断じゃ。
`PulseShape` のような新 predicate を増やすほどではないが、caller 側で毎回 entry / exit を組み直すのは面倒。だから theorem packaging としてまとめたのは妥当じゃ。

## 実装レビュー

今回の中心構造はこれ。

```text id="2en8wc"
interval pulse A:
  left edge  = A.start - 1
  right edge = A.start + A.len - 1
```

そして、

```text id="21tg3b"
left edge:
  CrossingEdgeTarget

right edge:
  FallingEdgeTarget
```

をまとめる。

```lean id="zpq02p"
theorem sourcePressureBeamPulse_edges_of_intervalPulseAddress
```

さらに mass-balance 版では、

```text id="4ys2ol"
entry:
  left < right

exit:
  right <= left
```

をまとめる。

```lean id="sbty0c"
theorem sourcePressureBeamPulse_massBalance_edges_of_intervalPulseAddress
```

この二つは interval pulse 一個に対する exact-edge packaging であり、coverage でも aggregation でもない。安全じゃ。

## witness singleton 側

witness 版も良い。

```lean id="fwjp05"
sourcePressureBeamPulse_witness_singleton_shape
```

これは、

```text id="819r17"
left edge:
  CrossingEdgeTarget

right / center edge:
  SourcePressureBeamAddressedDepthTarget

right edge:
  FallingEdgeTarget
```

をまとめている。

ここで `SourcePressureBeamAddressedDepthTarget` だけ `W ∈ L` を要求するのも正しい。
crossing / falling は pulse 由来の intrinsic な sign-change だが、addressed depth target は witness list relative な carrier だからじゃ。report でもこの点が明確に整理されている。

## True Beam / DepthTarget / False Beam / Gap

## True Beam

entry 側。

```text id="99a0l6"
CrossingEdgeTarget
  -> left < right
```

これは positive run に入る入口。

## DepthTarget

witness singleton の center / right edge。

```text id="bdtms8"
W ∈ L
  -> AddressedDepthTarget at right/center edge
```

ここは positive current depth として読める。

## False / Boundary

exit 側。

```text id="1es7bg"
FallingEdgeTarget
  -> right <= left
```

これは non-strict なので false-or-boundary。
strict false ではない。

## Gap

今回も interior coverage は追加していない。

```text id="hfo7qh"
interval 内部の全点 coverage
family aggregation
canonical target selection
overlap repair
propagation
Collatz convergence
```

には踏み込んでいない。ここは正しい。

## 評価

これは「局所 pulse の API が一段落した」と見てよい。

ここまでの流れはこうじゃ。

```text id="kazpgg"
classifier:
  nextMargin = right - left

edge vocabulary:
  CrossingEdgeTarget / DepthTarget / FallingEdgeTarget

pulse packaging:
  entry / active-center / exit
```

かなり綺麗に閉じた。

そして `PressureBeam.lean` が 1821 行で、まだ 2000 行の分割基準未満という確認も良い。
ただ、そろそろ次の大きな追加をするなら、分割候補を意識し始めてもよい頃合いじゃ。

## 次の checkpoint 方針

次は、`PressureBeam` にさらに同種の包装を増やすより、**この pulse packaging を downstream diagnostic layer が消費できるか**を見るのが良い。

候補は二つ。

```text id="j5g6vq"
A:
  downstream diagnostic / obstruction layer から pulse packaging を使う

B:
  false/boundary observation を一つだけ named theorem として取り出す
```

ただし、まだ coverage に飛んではいけない。

## 次の Codex 指示

```text id="sd7ix4"
Checkpoint: petal-224

Goal:
  Consume the local pulse-shape packaging from a downstream diagnostic or
  obstruction-facing layer, or decide that the current API is sufficient.

Context:
  cp223 packaged local pulse shape without adding a new predicate:

    interval pulse:
      crossing target at left edge
      falling target at right edge

    witness singleton:
      crossing target at left edge
      addressed depth target at center/right edge, requiring W ∈ L
      falling target at right edge

  The local Beam vocabulary is now:

    CrossingEdgeTarget:
      entry edge, nonpositive -> positive

    DepthTarget:
      positive current depth

    FallingEdgeTarget:
      exit edge, positive -> nonpositive

Main question:
  Is there a downstream theorem in the diagnostic / obstruction / witness-list
  layer that can use the cp223 packaged shape to reduce proof noise?

Modules to inspect:
  - DkMath.Collatz.PetalBridge.PressureBeam
  - DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
  - DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
  - DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
  - DkMath.Collatz.PetalBridge.PressureAutomaton

Codex should use workspace judgment:
  - inspect whether any existing theorem repeatedly needs entry/exit edge facts;
  - inspect whether witness singleton shape helps existing obstruction reports;
  - use `#check`, `#print`, and small scratch lemmas;
  - decide whether to add a small caller-facing theorem or only a report.

Possible useful outcomes:

  Outcome 1:
    Add a theorem that consumes
      sourcePressureBeamPulse_witness_singleton_shape
    to produce a named local false/boundary observation at the witness exit.

  Outcome 2:
    Add a theorem that consumes
      sourcePressureBeamPulse_massBalance_edges_of_intervalPulseAddress
    to expose paired entry/exit mass-balance comparisons for a diagnostic caller.

  Outcome 3:
    Add no Lean code and report that cp223 already provides enough local API,
    and the next step should move to a different module or split PressureBeam.

Do not force a theorem.

Guardrails:
  Do not add:
    - interval interior coverage;
    - global family coverage;
    - aggregation over witness families;
    - canonical target selection;
    - overlap repair;
    - arbitrary target transport;
    - Collatz convergence.

Report requirements:
  - Explain what Codex inspected.
  - State whether a downstream consumer theorem was added or skipped.
  - If added, explain exactly which packaged theorem it consumes.
  - If skipped, explain why existing API is sufficient.
  - Mention PressureBeam file size and whether a split should be considered soon.
  - Classify results as True Beam / DepthTarget / Falling-or-Boundary / Gap.
  - Make clear this is local API consumption, not coverage or propagation.

Verification if code changes:
  lake build DkMath.Collatz.PetalBridge.PressureBeam
  lake build DkMath.Collatz.PetalBridge
  no-sorry grep over inspected pressure files
  git diff --check
```

## 一歩先ゆく推論

いま `PressureBeam` は、局所 pulse の説明能力をかなり持った。

```text id="uw5o8y"
entry:
  positive run に入る

center:
  selected addressed positive depth

exit:
  nonpositive 側へ落ちる
```

次に欲しいのは、これを **diagnostic / obstruction の言葉**へ渡す橋じゃ。

つまり、

```text id="74ja83"
pulse shape
  -> diagnostic observation
  -> obstruction / false-boundary classification
```

へ進めるかどうか。

ただし、ここで無理に theorem を増やす必要はない。
Codex が現場を見て「今は report-only が良い」と判断するなら、それも正解じゃ。

## 総合判断

cp223 は成功。
これで local pulse API はかなり整った。

次は、`PressureBeam` の中でさらに増やすより、**この API を誰が使うのか**を調べる段階じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
index 5010fb52..f6361c54 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
@@ -1721,4 +1721,101 @@ theorem sourcePressureBeamMassBalanceRight_le_left_of_localIslandWitness_interva
   sourcePressureBeamMassBalanceRight_le_left_of_fallingEdgeTarget
     (sourcePressureBeamFallingEdgeTarget_of_localIslandWitness_intervalPulse_right W)

+/-
+Local pulse-shape packaging.
+
+Checkpoint 223 keeps this as theorem packaging rather than a new predicate.
+The three target vocabularies are already precise enough:
+
+* entry edge: `SourcePressureBeamCrossingEdgeTarget`;
+* active selected depth: `SourcePressureBeamAddressedDepthTarget`;
+* exit edge: `SourcePressureBeamFallingEdgeTarget`.
+
+The paired interval theorem records only the exact two boundary edges of one
+given pulse address.  The witness theorem adds the addressed-depth target at
+the singleton pulse's right/center edge, and that part necessarily requires
+`W ∈ L`: addressed targets are list-relative carriers, while crossing/falling
+edge targets are intrinsic sign-change facts of the witness-generated pulse.
+
+This section deliberately does not claim interior coverage, family coverage,
+canonical target selection, overlap repair, or Collatz convergence.
+-/
+
+/--
+An interval-pulse address packages its two exact Beam boundary edges.
+
+The left edge is the entrance crossing at `A.start - 1`; the right edge is the
+falling exit at `A.start + A.len - 1`.
+-/
+theorem sourcePressureBeamPulse_edges_of_intervalPulseAddress
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    SourcePressureBeamCrossingEdgeTarget n k r (A.start - 1) ∧
+      SourcePressureBeamFallingEdgeTarget n k r (A.start + A.len - 1) :=
+  ⟨sourcePressureBeamCrossingEdgeTarget_of_intervalPulse_left A,
+    sourcePressureBeamFallingEdgeTarget_of_intervalPulse_right A⟩
+
+/--
+An interval-pulse address packages the entry and exit mass-balance comparisons.
+
+This is the finite local pulse shape:
+entry gives the True Beam comparison `left < right`, while exit gives the
+False/Boundary comparison `right <= left`.
+-/
+theorem sourcePressureBeamPulse_massBalance_edges_of_intervalPulseAddress
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    SourcePressureBeamMassBalanceLeftInt n k r (A.start - 1) <
+        SourcePressureBeamMassBalanceRightInt n k r (A.start - 1) ∧
+      SourcePressureBeamMassBalanceRightInt n k r (A.start + A.len - 1) ≤
+        SourcePressureBeamMassBalanceLeftInt n k r (A.start + A.len - 1) :=
+  ⟨sourcePressureBeamMassBalanceLeft_lt_right_of_intervalPulse_left_crossing A,
+    sourcePressureBeamMassBalanceRight_le_left_of_intervalPulse_right_falling A⟩
+
+/--
+A local-island witness packages the singleton pulse shape:
+
+* crossing target at the generated pulse's left edge;
+* addressed positive depth at the generated pulse's right/center edge;
+* falling target at the same generated pulse's right edge.
+
+The addressed-depth component is list-relative, hence the `W ∈ L` hypothesis.
+-/
+theorem sourcePressureBeamPulse_witness_singleton_shape
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W : SourcePressureLocalIslandWitness n k r}
+    (hmem : W ∈ L) :
+    SourcePressureBeamCrossingEdgeTarget n k r
+        ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start - 1) ∧
+      SourcePressureBeamAddressedDepthTarget L
+        ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
+          (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) ∧
+        SourcePressureBeamFallingEdgeTarget n k r
+          ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
+            (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) :=
+  ⟨sourcePressureBeamCrossingEdgeTarget_of_localIslandWitness_intervalPulse_left W,
+    sourcePressureBeamAddressedDepthTarget_of_localIslandWitness_intervalPulse_right hmem,
+    sourcePressureBeamFallingEdgeTarget_of_localIslandWitness_intervalPulse_right W⟩
+
+/--
+A local-island witness packages the singleton pulse's two edge comparisons:
+True Beam at entry and False/Boundary at exit.
+-/
+theorem sourcePressureBeamPulse_witness_singleton_massBalance_edges
+    {n : OddNat} {k r : ℕ}
+    (W : SourcePressureLocalIslandWitness n k r) :
+    SourcePressureBeamMassBalanceLeftInt n k r
+        ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start - 1) <
+        SourcePressureBeamMassBalanceRightInt n k r
+          ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start - 1) ∧
+      SourcePressureBeamMassBalanceRightInt n k r
+          ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
+            (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) ≤
+        SourcePressureBeamMassBalanceLeftInt n k r
+          ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
+            (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) :=
+  ⟨sourcePressureBeamMassBalanceLeft_lt_right_of_localIslandWitness_intervalPulse_left W,
+    sourcePressureBeamMassBalanceRight_le_left_of_localIslandWitness_intervalPulse_right_falling W⟩
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-223.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-223.md
new file mode 100644
index 00000000..69a609f4
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-223.md
@@ -0,0 +1,112 @@
+# Report: petal-223
+
+## Checkpoint
+
+`petal-223` asked whether the new Beam edge vocabulary should be packaged into
+a compact local pulse-shape API.
+
+The implemented answer is yes, but only as thin theorem packaging.  No new
+predicate was added.
+
+## What was inspected
+
+The relevant API already existed after cp221 and cp222:
+
+- `SourcePressureBeamCrossingEdgeTarget`
+  records an entry edge, `nonpositive -> positive`.
+- `SourcePressureBeamDepthTarget`
+  records a positive current depth.
+- `SourcePressureBeamFallingEdgeTarget`
+  records an exit edge, `positive -> nonpositive`.
+- `sourcePressureBeamCrossingEdgeTarget_of_intervalPulse_left`
+  gives the left edge of an interval pulse.
+- `sourcePressureBeamFallingEdgeTarget_of_intervalPulse_right`
+  gives the right edge of an interval pulse.
+- `sourcePressureBeamAddressedDepthTarget_of_localIslandWitness_intervalPulse_right`
+  gives the singleton witness depth target, but this one is list-relative and
+  therefore requires `W ∈ L`.
+
+This was enough to add compact local packaging without introducing a heavier
+`PulseShape` predicate.
+
+## Implemented theorem surface
+
+Added in `DkMath.Collatz.PetalBridge.PressureBeam`:
+
+```lean
+sourcePressureBeamPulse_edges_of_intervalPulseAddress
+sourcePressureBeamPulse_massBalance_edges_of_intervalPulseAddress
+sourcePressureBeamPulse_witness_singleton_shape
+sourcePressureBeamPulse_witness_singleton_massBalance_edges
+```
+
+The interval-pulse edge theorem packages the exact indices:
+
+```text
+left edge  = A.start - 1
+right edge = A.start + A.len - 1
+```
+
+The witness singleton theorem packages:
+
+```text
+left edge:
+  CrossingEdgeTarget
+
+right / center edge of the singleton pulse:
+  SourcePressureBeamAddressedDepthTarget L ...
+  FallingEdgeTarget
+```
+
+The addressed-depth component requires `W ∈ L` because it is a carrier relative
+to a witness list.  The crossing and falling edge targets do not require list
+membership, because they are intrinsic sign-change facts of the generated pulse.
+
+## Classification
+
+- True Beam:
+  The entry edge gives `left < right`.
+
+- DepthTarget:
+  The singleton local-island witness gives an addressed depth target at the
+  generated pulse's right/center edge, under `W ∈ L`.
+
+- Falling / Boundary:
+  The exit edge gives `right <= left`, i.e. the false-or-boundary comparison.
+
+- Gap:
+  No interior coverage theorem was added.  No family aggregation, canonical
+  target selection, overlap repair, propagation, or Collatz convergence is
+  claimed.
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
+`PressureBeam.lean` is now 1821 lines, still below the 2000-line split
+criterion.
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
+The entry/interior/exit vocabulary is now available as local pulse packaging.
+The next safe step is to consume these packaged theorems from a downstream
+diagnostic layer, or to add one more local theorem that destructs the packaged
+shape into a named false/boundary observation.  The unsafe step would be to
+upgrade this into coverage over all intervals or all witness families; that
+should remain out of scope until exact membership and non-overlap facts exist.
````
`````
