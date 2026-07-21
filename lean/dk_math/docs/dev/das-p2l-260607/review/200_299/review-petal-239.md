# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam.Pulse

gch: 13f6e7a695cc3e197f9954c8301a6707c174d468

## Report

cp238 完了です。

`PressureBeam/Pulse.lean` に local pulse box を追加しました。生の theorem に全部展開すると読みにくいので、Branch B として predicate + existence theorem にしています。

追加:

- `SourcePressureBeamCenteredLocalPulseBox`
- `exists_sourcePressureBeamPulse_witness_center_local_box_of_seed`

これは cp235 の sign transition、cp236 の margin height box、cp237 の net-drop jump box を、同じ witness `W` に対して束ねるものです。局所 witness の箱であり、propagation / coverage / convergence は主張していません。

レポート:
[report-petal-238.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-238.md)

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureDecay`
- `lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse`
- `lake build DkMath.Collatz.PetalBridge.PressureBeam`
- `lake build DkMath.Collatz.PetalBridge`
- no-sorry grep 対象範囲一致なし
- `git diff --check`

すべて通過しています。

## Review

## 結論

**採用。これは局所 Core の箱詰め完了じゃ。**

cp238 は、cp235 の sign transition、cp236 の height box、cp237 の jump box を、同じ witness `W` に対して束ねる **local pulse box** を作った。生 theorem を巨大化させず、Branch B として predicate + existence theorem にした判断も正しい。

追加はこの 2 つ。

```lean id="edyt9v"
SourcePressureBeamCenteredLocalPulseBox
```

```lean id="xlg8zk"
exists_sourcePressureBeamPulse_witness_center_local_box_of_seed
```

これで、

```text id="h2nnel"
SourcePressureBeamSeed L
  -> ∃ W,
       W is a centered local pulse
       with sign transition
       with finite height boxes
       with finite jump boxes
```

が一つの public surface になった。

## 実装レビュー

predicate 化は正解じゃ。

raw theorem に全部展開すると、

```text id="ylghs3"
W ∈ L
previous margin ≤ 0
center margin > 0
addressed target
next margin ≤ 0
height bounds at 3 depths
jump bounds at 2 edges
```

を全部抱えるため、statement が読みづらくなる。
そこで `SourcePressureBeamCenteredLocalPulseBox` として名前を与えたのは、今後の propagation / obstruction 解析の入口としてかなり使いやすい。

証明も薄い。

```lean id="nhfa4q"
exists_sourcePressureBeamPulse_witness_center_margin_signs_of_seed
sourcePressureMarginInt_bounds_window
sourcePressureNetDropInt_bounds_window
```

を合成しているだけ。
つまり、cp235 / cp236 / cp237 の成果を再証明せずに束ねた。これは良い API 化じゃ。

## 数学的意味

ここまでで、局所 pulse は次のように定式化された。

```text id="te2m1g"
sign:
  非正 -> 正 -> 非正

height:
  margin ∈ [-k, 2k]

jump:
  net drop ∈ [-3k, 3k]
```

これは DkMath 的には、**局所 Core の完成形に近い**。

つまり、

```text id="ptt6gy"
局所的に何が起きているか
どこで正圧になるか
高さはどの箱に収まるか
隣接ジャンプはどの箱に収まるか
```

が、ひとつの witness-local predicate で読める。

## True Beam / Boundary / False Beam / Gap

## True Beam

`SourcePressureBeamSeed L` から、有限箱に入った centered local pulse witness が存在する。

```text id="kwxxl8"
seed
  -> ∃ W, SourcePressureBeamCenteredLocalPulseBox n k r L W
```

これはかなり強い局所診断 surface じゃ。

## Boundary

あくまで one witness local。

```text id="c9hu9f"
W.val 周辺の 3 depth
W.val - 1 と W.val の 2 adjacent edge
```

に限られる。

## False Beam

この predicate だけからは、次は言えない。

```text id="eabf2u"
monotone trend
propagation
coverage
global descent
Collatz convergence
```

ここを report でも明確に切っている。正しい。

## Gap

次の Gap はこれ。

```text id="h9kpm9"
boxed local pulse は、隣へ運べるのか？
運べないなら、何が obstruction なのか？
```

つまり、次は **propagation そのもの** ではなく、まず **controlled propagation-obstruction split** が本命じゃ。

## 注意点

`SourcePressureBeamCenteredLocalPulseBox` は `def ... : Prop` なので、今後 caller が使うと `rcases hbox with ...` がやや長くなる可能性がある。

ただし今はこれでよい。
すぐに projection lemma を増やす必要はない。

もし次 checkpoint で何度も同じ分解をするなら、その時にだけ、

```lean id="fn21tc"
SourcePressureBeamCenteredLocalPulseBox.center_pos
SourcePressureBeamCenteredLocalPulseBox.prev_nonpos
SourcePressureBeamCenteredLocalPulseBox.next_nonpos
```

のような projection lemma を検討すればよい。

今は predicate の存在だけで十分じゃ。

## 次の checkpoint 方針

次は report の予測通り、**controlled propagation-obstruction split** を狙う。

いきなり、

```text id="vjlo7k"
local pulse box -> propagation
```

を主張してはいけない。

まずは、

```text id="hmat3o"
local pulse box
  -> either next-step continuation candidate
     or explicit obstruction/failure predicate
```

の形を探す。

この分岐なら、通れば前進。
通らなければ obstruction が残る。
どちらでも情報が増える。

## 次の Codex 指示

```text id="spmavp"
Checkpoint: petal-239

Primary Goal:
  Use the new `SourcePressureBeamCenteredLocalPulseBox` predicate to investigate
  the first controlled propagation-or-obstruction split.

Context:
  cp238 added:

    def SourcePressureBeamCenteredLocalPulseBox
    theorem exists_sourcePressureBeamPulse_witness_center_local_box_of_seed

  This packages:
    - local sign transition;
    - margin height boxes;
    - net-drop jump boxes;

  for one witness `W` exposed by `SourcePressureBeamSeed L`.

  The next goal is not to prove propagation globally.
  The next goal is to inspect whether a boxed local pulse can be related to a
  neighboring candidate, or whether the existing API exposes an obstruction.

Strategic Branch Goals:

  Branch A: existing neighboring candidate relation
    Search for existing definitions/theorems involving:
      - next local island;
      - adjacent local witness;
      - neighboring pressure pulse;
      - source pressure continuation;
      - pressure pulse transport;
      - interval pulse successor;
      - addressed depth successor.

    If there is an existing relation from a witness `W` to a neighboring
    witness/candidate `W'`, try to prove a thin theorem of the form:

      SourcePressureBeamCenteredLocalPulseBox n k r L W
        -> <neighbor candidate relation for W>

    Only add this if it is a direct wrapper over existing API.

  Branch B: obstruction predicate already exists
    If the code already has an obstruction/failure predicate for why a pulse
    cannot transport or chain, add a theorem connecting the local pulse box to
    that predicate only if the hypotheses are already present.

    Candidate shape:

      SourcePressureBeamCenteredLocalPulseBox n k r L W
        -> <transport obstruction or local failure predicate>
           ∨ <neighbor candidate>

    Do not invent a new obstruction unless the existing definitions clearly
    support it.

  Branch C: only sign/jump facts are usable
    If no transport relation exists, derive a small theorem exposing the useful
    components of the box for future callers.

    For example:
      - center margin positive;
      - previous/next nonpositive;
      - net-drop bound at entry/exit;
      - addressed target at W.val.

    Prefer projection lemmas only if repeated `rcases` becomes noisy.

  Branch D: no propagation theorem yet
    If no existing neighbor/transport/obstruction API exists, add no Lean code.

    Write a report explaining:
      - what was searched;
      - which theorem names currently form the local pulse box API;
      - the exact missing relation needed for propagation.

  Branch E: sharpened jump relation appears
    If existing API gives a relation between entry jump and exit jump, or a
    sharper bound than `[-3k, 3k]` under the local pulse box assumptions, report
    it as the next candidate.

    Do not replace cp237's coarse bound in this checkpoint.

Implementation rules:
  - Use #check, #print, and scratch lemmas.
  - Inspect actual definitions before naming any theorem.
  - Add no more than one theorem, unless adding tiny projection lemmas is
    clearly necessary.
  - Prefer no-code report over speculative propagation theorem.
  - Keep all claims local and witness-relative.

Files to inspect:
  DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
  DkMath/Collatz/PetalBridge/PressureBeam/Core.lean
  DkMath/Collatz/PetalBridge/PressureAutomaton.lean
  DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
  DkMath/Collatz/PetalBridge/PressureDecay.lean
  DkMath/Collatz/PetalBridge/PressureFrontier.lean
  DkMath/Collatz/PetalBridge/PressureAccounting.lean

Search terms:
  SourcePressureBeamCenteredLocalPulseBox
  SourcePressureBeamAddressedDepthTarget
  SourcePressureLocalIslandWitness
  SourcePressureLocalIsland
  SourcePressureFailureResolution
  SourcePressureLocalIslandWitnessAdjacentPairInList
  SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
  SourcePressureNetDropInt
  SourcePressureMarginInt
  successor
  next
  adjacent
  transport
  obstruction
  frontier
  propagation

Guardrails:
  Do not add:
    - propagation without explicit existing hypotheses;
    - list-wide coverage;
    - witness-family aggregation;
    - canonical witness selection;
    - arbitrary target transport;
    - overlap repair;
    - disjointness;
    - monotone trend;
    - global Big bounds;
    - Collatz convergence.

Verification if code changes:
  lake build DkMath.Collatz.PetalBridge.PressureDecay
  lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
  lake build DkMath.Collatz.PetalBridge.PressureBeam
  lake build DkMath.Collatz.PetalBridge
  no-sorry grep over inspected pressure files
  git diff --check

Report requirements:
  - State which Branch was taken.
  - If code was added, show the exact theorem statement and why it is local.
  - If no code was added, identify the exact missing propagation relation.
  - Explain how cp238 local pulse box is intended to be consumed.
  - Classify results as True Beam / Boundary / False Beam / Gap.
  - Predict whether the next branch should add projection lemmas, an obstruction
    bridge, or a true neighbor-candidate theorem.
```

## 待ち構え

次はたぶん、このどれかじゃ。

```text id="kprmy0"
Branch D:
  まだ transport API が無い
```

この場合でも収穫あり。missing relation が明確になる。

```text id="ixmnh6"
Branch C:
  projection lemmas が欲しくなる
```

これは実用改善。次の caller が楽になる。

```text id="avzrzw"
Branch A/B:
  neighbor candidate or obstruction に繋がる
```

これが本命。
ここが通れば、いよいよ Beam 伝播解析の入口に入る。

## 総合判断

cp238 は成功。
局所 Core は、かなり綺麗に箱詰めされた。

次は、焦って大域へ飛ばず、

```text id="w4zgcq"
boxed local pulse
  -> neighbor candidate
  or obstruction
```

を探す。
これが、Core から Beam へ渡る最初の橋じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
index 1a2b81f8..194ade98 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
@@ -355,6 +355,80 @@ theorem exists_sourcePressureBeamPulse_witness_center_margin_signs_of_seed
   exact
     ⟨W, hmem, hprev, hcenterFromEntry, haddr, hnextFromExit⟩

+/--
+Centered local pulse box for one Beam witness.
+
+This predicate is the cp238 local packaging of three already-established
+layers:
+
+* cp235 sign transition around the native witness depth `W.val`;
+* cp236 margin-height boxes at the previous, center, and next depths;
+* cp237 net-drop jump boxes at the entry and exit adjacent edges.
+
+The predicate is intentionally local and witness-relative.  It does not assert
+propagation, list-wide coverage, witness aggregation, overlap repair, canonical
+witness selection, monotone trend, global Big bounds, or Collatz convergence.
+-/
+def SourcePressureBeamCenteredLocalPulseBox
+    (n : OddNat) (k r : ℕ)
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (W : SourcePressureLocalIslandWitness n k r) : Prop :=
+  W ∈ L ∧
+    SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0 ∧
+      0 < SourcePressureMarginInt n k (r + W.val) ∧
+        SourcePressureBeamAddressedDepthTarget L W.val ∧
+          SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
+            (- (k : ℤ) ≤ SourcePressureMarginInt n k (r + (W.val - 1)) ∧
+              SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 2 * (k : ℤ)) ∧
+              (- (k : ℤ) ≤ SourcePressureMarginInt n k (r + W.val) ∧
+                SourcePressureMarginInt n k (r + W.val) ≤ 2 * (k : ℤ)) ∧
+                (- (k : ℤ) ≤ SourcePressureMarginInt n k (r + W.val + 1) ∧
+                  SourcePressureMarginInt n k (r + W.val + 1) ≤ 2 * (k : ℤ)) ∧
+                  (- (3 * (k : ℤ)) ≤
+                      SourcePressureNetDropInt n k r (W.val - 1) ∧
+                    SourcePressureNetDropInt n k r (W.val - 1) ≤
+                      3 * (k : ℤ)) ∧
+                    (- (3 * (k : ℤ)) ≤
+                        SourcePressureNetDropInt n k r W.val ∧
+                      SourcePressureNetDropInt n k r W.val ≤
+                        3 * (k : ℤ))
+
+/--
+A Beam seed exposes one witness whose centered pulse is inside the finite
+local pulse box.
+
+This is only a thin wrapper over:
+
+* `exists_sourcePressureBeamPulse_witness_center_margin_signs_of_seed`;
+* `sourcePressureMarginInt_bounds_window`;
+* `sourcePressureNetDropInt_bounds_window`.
+
+It packages the local sign transition, three pointwise height boxes, and two
+adjacent jump boxes for the same existential witness.  No propagation or
+global behavior is claimed.
+-/
+theorem exists_sourcePressureBeamPulse_witness_center_local_box_of_seed
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hseed : SourcePressureBeamSeed L) :
+    ∃ W : SourcePressureLocalIslandWitness n k r,
+      SourcePressureBeamCenteredLocalPulseBox n k r L W := by
+  rcases exists_sourcePressureBeamPulse_witness_center_margin_signs_of_seed
+      hseed with
+    ⟨W, hmem, hprev, hcenter, haddr, hnext⟩
+  exact
+    ⟨W,
+      hmem,
+      hprev,
+      hcenter,
+      haddr,
+      hnext,
+      sourcePressureMarginInt_bounds_window n k (r + (W.val - 1)),
+      sourcePressureMarginInt_bounds_window n k (r + W.val),
+      sourcePressureMarginInt_bounds_window n k (r + W.val + 1),
+      sourcePressureNetDropInt_bounds_window n k r (W.val - 1),
+      sourcePressureNetDropInt_bounds_window n k r W.val⟩
+
 /--
 Failure resolution also exposes one witness whose singleton pulse has the full
 local entry-depth-exit diagnostic.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-238.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-238.md
new file mode 100644
index 00000000..8b29cb74
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-238.md
@@ -0,0 +1,181 @@
+# report-petal-238
+
+## Checkpoint
+
+`petal-238`
+
+## Summary
+
+Implemented Branch B: one small Beam-facing predicate plus one seed-existence
+theorem.
+
+The raw theorem statement would have been too large because the local pulse box
+contains:
+
+```text
+membership
+sign transition at three depths
+addressed-depth target
+height boxes at three depths
+jump boxes at two adjacent edges
+```
+
+So the implementation introduces a named predicate and proves that every Beam
+seed exposes one witness satisfying it.
+
+## Added Predicate
+
+```lean
+def SourcePressureBeamCenteredLocalPulseBox
+    (n : OddNat) (k r : ℕ)
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (W : SourcePressureLocalIslandWitness n k r) : Prop
+```
+
+It contains:
+
+```text
+W ∈ L
+SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0
+0 < SourcePressureMarginInt n k (r + W.val)
+SourcePressureBeamAddressedDepthTarget L W.val
+SourcePressureMarginInt n k (r + W.val + 1) ≤ 0
+
+height box at r + (W.val - 1)
+height box at r + W.val
+height box at r + W.val + 1
+
+jump box at edge W.val - 1
+jump box at edge W.val
+```
+
+The predicate deliberately stays local and witness-relative.
+
+## Added Theorem
+
+```lean
+theorem exists_sourcePressureBeamPulse_witness_center_local_box_of_seed
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hseed : SourcePressureBeamSeed L) :
+    ∃ W : SourcePressureLocalIslandWitness n k r,
+      SourcePressureBeamCenteredLocalPulseBox n k r L W
+```
+
+This is the local pulse box wrapper expected by cp238:
+
+```text
+seed
+  -> ∃ W,
+       centered local pulse
+       inside finite height box
+       with finite jump box
+```
+
+## Consumed Theorems
+
+The new theorem is a thin composition of:
+
+```lean
+exists_sourcePressureBeamPulse_witness_center_margin_signs_of_seed
+sourcePressureMarginInt_bounds_window
+sourcePressureNetDropInt_bounds_window
+```
+
+Interpretation:
+
+- cp235 supplies the centered sign transition.
+- cp236 supplies finite local height boxes `[-k, 2k]`.
+- cp237 supplies finite adjacent jump boxes `[-3k, 3k]`.
+
+## Important Scope Boundary
+
+This is a finite local pulse box theorem.
+
+It does not claim:
+
+```text
+propagation
+list-wide coverage
+witness-family aggregation
+canonical witness selection
+overlap repair
+disjointness
+monotone trend
+global Big bounds
+Collatz convergence
+```
+
+The result only says that one seed exposes one witness whose native pulse has
+the local sign, height, and jump diagnostics simultaneously.
+
+## Big / Core / Beam / Gap Classification
+
+- Core:
+  the finite definitions and earlier boxed estimates are now reusable:
+  margin height `[-k, 2k]` and net jump `[-3k, 3k]`.
+
+- True Beam:
+  the seed-level local pulse now has a single public predicate expressing
+  sign transition plus finite boxes.
+
+- Boundary:
+  the theorem is existential over one witness `W ∈ L` and local to depths
+  around `W.val`.
+
+- False Beam:
+  no global trend or propagation is obtained merely from the local box.
+
+- Gap:
+  the next mathematical question is whether and how boxed local pulses can be
+  transported, chained, or blocked.  That is not part of this checkpoint.
+
+## Next Branch Prediction
+
+Two next branches are plausible:
+
+1. Sharpen jump bounds.
+   The current `[-3k, 3k]` net-drop box is coarse but robust.  A sharper theorem
+   may exist if retention and continuation drops are not independent in a
+   local pulse.
+
+2. Begin controlled propagation analysis.
+   Now that the local pulse box is packaged, the next propagation theorem can
+   consume a single clean predicate rather than separately carrying sign,
+   height, and jump facts.
+
+The safer next checkpoint is a controlled propagation-obstruction split:
+
+```text
+local pulse box
+  -> either a bounded next-step continuation candidate
+     or an explicit obstruction/failure predicate
+```
+
+That would preserve the current project discipline: prove local transport only
+when Lean supplies the hypotheses, and otherwise record the false branch as an
+obstruction.
+
+## Verification
+
+Commands run:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureDecay
+lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
+lake build DkMath.Collatz.PetalBridge.PressureBeam
+lake build DkMath.Collatz.PetalBridge
+rg -n "sorry|admit" <pressure-file-scope>
+git diff --check
+```
+
+Results:
+
+```text
+PressureDecay build: pass
+PressureBeam.Pulse build: pass
+PressureBeam build: pass
+PetalBridge build: pass
+no-sorry grep: no matches in inspected pressure scope
+git diff --check: pass
+```
````
`````
