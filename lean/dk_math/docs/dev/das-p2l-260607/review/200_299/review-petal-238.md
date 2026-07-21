# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureDecay

gch: 16e1ba252a842a05bc0dee3353beebc66607ea99

## Report

cp237 完了です。

`PressureDecay.lean` に有限局所ジャンプ境界を追加しました。実定義は `j` 付きなので、API も `Source...DropInt n k r j` の形で固定しています。

追加内容:

- `SourceRetentionDropInt ∈ [-k, k]`
- `SourceContinuationDropInt ∈ [-k, k]`
- `SourcePressureNetDropInt ∈ [-3k, 3k]`

レポートも追加済みです:
[report-petal-237.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-237.md)

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureDecay`
- `lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse`
- `lake build DkMath.Collatz.PetalBridge.PressureBeam`
- `lake build DkMath.Collatz.PetalBridge`
- no-sorry grep 対象範囲一致なし
- `git diff --check`

すべて通過しています。次はレポートにも書いた通り、cp235 の sign transition と、cp236/cp237 の height/jump box を束ねる薄い local pulse wrapper が自然です。

## Review

## 結論

**採用。これは三塁打じゃ。**
cp237 は、cp236 の「高さの箱」に続いて、**隣接ジャンプの箱**をきちんと theorem 化している。

追加されたのは、retention drop / continuation drop / net pressure drop の有限局所境界。

```lean id="srzyeg"
sourceRetentionDropInt_bounds_window
sourceContinuationDropInt_bounds_window
sourcePressureNetDropInt_bounds_window
```

中心結果はこれ。

```text id="ay8g10"
SourceRetentionDropInt n k r j ∈ [-k, k]
SourceContinuationDropInt n k r j ∈ [-k, k]
SourcePressureNetDropInt n k r j ∈ [-3k, 3k]
```

cp236 が **margin height box**、cp237 が **adjacent jump box**。
これで局所 Big の輪郭がかなり明確になった。

## 実装レビュー

実装は正しい方向。

定義が `j` 付きだったため、API も

```lean id="qjodxs"
SourceRetentionDropInt n k r j
SourceContinuationDropInt n k r j
SourcePressureNetDropInt n k r j
```

の形にしたのは正解じゃ。
`r` は base pressure depth、`j` は隣接遷移 `r + j -> r + j + 1` の edge selector。ここを無理に `r` だけの定理へ潰さなかったのが良い。

証明も薄い。

retention / continuation は、それぞれ両端の mass が有限 window `k` に入ることから差分が `[-k,k]` に入る。
net drop は定義

```lean id="tt2686"
SourcePressureNetDropInt
  = SourceRetentionDropInt - 2 * SourceContinuationDropInt
```

と component bounds から `[-3k,3k]`。
`omega` で閉じるのも自然じゃ。

## 数学的意味

ここまでの流れはこう。

```text id="wyz5eh"
cp235:
  seed -> 非正 -> 正 -> 非正 の local pulse sign pattern

cp236:
  margin height box:
    margin ∈ [-k, 2k]

cp237:
  adjacent jump box:
    net drop ∈ [-3k, 3k]
```

つまり、局所 pulse について、

```text id="s2lvps"
どこで正になるか
どの高さの箱に入るか
一歩でどれだけ跳べるか
```

がそろい始めた。

これは DkMath 語彙では、

```text id="mpbpba"
Core:
  finite-window mass bounds

True Beam:
  local positive pulse と finite jump bounds

Boundary:
  すべて finite observation window k に局所化

Gap:
  sign pattern + height box + jump box の bundle はまだない
```

という状態じゃ。

## 注意点

今回の theorem は、隣接 edge ごとの局所 bound。

まだ言っていないことは明確じゃ。

```text id="fo1hth"
net drop が長期的に負へ偏る
positive pulse が有限回しか続かない
window family を覆う
軌道方向へ伝播する
Collatz 収束する
```

これらは一切出ていない。
report の「jump analogue of pointwise margin-height box」という整理はかなり正しい。

## 次の本命

次は report の予測どおり、

```text id="ize8vf"
cp235 sign transition
+ cp236 height box
+ cp237 jump box
```

を束ねる薄い local pulse wrapper が自然じゃ。

ただし、欲張りすぎて巨大 theorem にしない。
まずは seed から出る witness `W` について、3 つの margin と 2 つの adjacent jump を有限箱に入れる程度が良い。

狙う形はこう。

```text id="ge815e"
SourcePressureBeamSeed L
  -> ∃ W ∈ L,
       sign pattern around W.val
       ∧ margin bounds at:
           r + (W.val - 1)
           r + W.val
           r + W.val + 1
       ∧ net-drop bounds at edges:
           W.val - 1
           W.val
```

これで、

```text id="olpwap"
局所 pulse は有限高さの箱に入り、
その入口・出口ジャンプも有限幅の箱に入る
```

と言える。

## 次の Codex 指示

```text id="vznxe5"
Checkpoint: petal-238

Primary Goal:
  Bundle the local pulse sign transition from cp235 with the finite height box
  from cp236 and the finite jump box from cp237.

Context:
  cp235 established the centered seed sign transition:

    SourcePressureBeamSeed L
      -> ∃ W ∈ L,
           margin at r + (W.val - 1) ≤ 0
           ∧ margin at r + W.val > 0
           ∧ SourcePressureBeamAddressedDepthTarget L W.val
           ∧ margin at r + W.val + 1 ≤ 0

  cp236 established generic margin height bounds:

    sourcePressureMarginInt_bounds_window
      -k ≤ SourcePressureMarginInt n k t ≤ 2k

  cp237 established generic adjacent jump bounds:

    sourcePressureNetDropInt_bounds_window
      -3k ≤ SourcePressureNetDropInt n k r j ≤ 3k

  The next theorem should be a local, witness-existential pulse box theorem.
  It must not claim propagation, coverage, aggregation, or convergence.

Strategic Branch Goals:

  Branch A: thin seed-level local pulse box wrapper
    Add one theorem in `PressureBeam/Pulse.lean` consuming:

      exists_sourcePressureBeamPulse_witness_center_margin_signs_of_seed
      sourcePressureMarginInt_bounds_window
      sourcePressureNetDropInt_bounds_window

    Candidate theorem name:

      exists_sourcePressureBeamPulse_witness_center_local_box_of_seed

    Candidate shape:

      theorem exists_sourcePressureBeamPulse_witness_center_local_box_of_seed
          {n : OddNat} {k r : ℕ}
          {L : List (SourcePressureLocalIslandWitness n k r)}
          (hseed : SourcePressureBeamSeed L) :
          ∃ W : SourcePressureLocalIslandWitness n k r,
            W ∈ L ∧
              SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0 ∧
              0 < SourcePressureMarginInt n k (r + W.val) ∧
              SourcePressureBeamAddressedDepthTarget L W.val ∧
              SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
              source-local height/jump bounds for the same three depths and
              two adjacent edges

    Keep the statement readable.  Prefer bundled bound conjuncts rather than
    expanding every one-sided inequality if the expanded theorem becomes too
    large.

  Branch B: define a local predicate to avoid a huge statement
    If the theorem statement becomes too large, introduce a small Beam-facing
    predicate in `PressureBeam/Pulse.lean`, for example:

      def SourcePressureBeamCenteredLocalPulseBox
          (n : OddNat) (k r : ℕ)
          (L : List (SourcePressureLocalIslandWitness n k r))
          (W : SourcePressureLocalIslandWitness n k r) : Prop := ...

    It should contain:
      - W ∈ L
      - previous margin nonpositive
      - center margin positive
      - addressed depth target
      - next margin nonpositive
      - margin bounds at the three involved depths
      - net-drop bounds at the two involved edges

    Then prove:

      SourcePressureBeamSeed L
        -> ∃ W, SourcePressureBeamCenteredLocalPulseBox n k r L W

    Use this branch only if the raw theorem statement is unwieldy.

  Branch C: height-only wrapper first
    If net-drop edge indexing causes friction, first add a smaller theorem
    bundling only:

      sign pattern + margin height bounds

    Report the exact index blocker for net-drop bounds.

  Branch D: no wrapper needed
    If adding the wrapper merely duplicates a clean theorem chain and no caller
    needs it yet, add no code.

    Report the exact chain:
      cp235 sign theorem
      cp236 margin bounds
      cp237 net-drop bounds

  Branch E: discover sharper edge-specific bound
    If existing API gives a sharper jump bound than `[-3k, 3k]`, do not replace
    cp237.

    Report the sharper candidate and leave it for a later checkpoint.

Implementation rules:
  - Use #check, #print, and scratch lemmas.
  - Do not add adjacent-pair or overlap wrappers.
  - Add at most one theorem, unless using one small predicate plus one theorem.
  - Prefer local witness-existential API.
  - Keep all claims pointwise/local.

Guardrails:
  Do not add:
    - propagation;
    - list-wide coverage;
    - witness-family aggregation;
    - canonical witness selection;
    - arbitrary target transport;
    - overlap repair;
    - disjointness;
    - monotone trend;
    - Collatz convergence;
    - global Big bounds.

Verification:
  lake build DkMath.Collatz.PetalBridge.PressureDecay
  lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
  lake build DkMath.Collatz.PetalBridge.PressureBeam
  lake build DkMath.Collatz.PetalBridge
  no-sorry grep over inspected pressure files
  git diff --check

Report requirements:
  - State which Branch was taken.
  - If a predicate was introduced, show why it was needed.
  - Show exactly which cp235/cp236/cp237 theorems are consumed.
  - Explain that this is a finite local pulse box, not propagation.
  - Classify results as True Beam / Boundary / False Beam / Gap.
  - Predict the next branch:
      either sharpen jump bounds,
      or begin controlled propagation analysis.
```

## 待ち構え

次の期待は、

```text id="jqreux"
seed
  -> ∃ W,
       centered local pulse
       inside finite height box
       with finite jump box
```

じゃ。

これが通れば、局所 Core はかなり綺麗に閉じる。

その次に初めて、

```text id="v9oz1e"
この bounded pulse が隣へどう伝播するか
```

を見る段階に入れる。

## 総合判断

cp237 は成功。
高さの箱 `[-k,2k]` に続いて、ジャンプの箱 `[-3k,3k]` が立った。

局所 Big は、もうかなり姿を持った。
次はそれを **local pulse box** として一つに束ねる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDecay.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDecay.lean
index 688be983..b35a3c6f 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDecay.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDecay.lean
@@ -101,6 +101,49 @@ noncomputable def SourceRetentionDropInt
   (orbitWindowRetentionMassPow2 n k (r + j) : ℤ) -
     (orbitWindowRetentionMassPow2 n k (r + j + 1) : ℤ)

+/--
+Finite local upper bound for one adjacent retention drop.
+
+Both endpoint retention masses are counts inside the same finite observation
+window of size `k`, so their integer difference cannot exceed `k`.
+-/
+theorem sourceRetentionDropInt_le_window
+    (n : OddNat) (k r j : ℕ) :
+    SourceRetentionDropInt n k r j ≤ (k : ℤ) := by
+  have hcur :
+      orbitWindowRetentionMassPow2 n k (r + j) ≤ k :=
+    orbitWindowRetentionMassPow2_le_window n k (r + j)
+  unfold SourceRetentionDropInt
+  omega
+
+/--
+Finite local lower bound for one adjacent retention drop.
+
+This is the opposite endpoint case of `sourceRetentionDropInt_le_window`:
+the next retention mass is also bounded by the same finite window `k`.
+-/
+theorem neg_window_le_sourceRetentionDropInt
+    (n : OddNat) (k r j : ℕ) :
+    - (k : ℤ) ≤ SourceRetentionDropInt n k r j := by
+  have hnext :
+      orbitWindowRetentionMassPow2 n k (r + j + 1) ≤ k :=
+    orbitWindowRetentionMassPow2_le_window n k (r + j + 1)
+  unfold SourceRetentionDropInt
+  omega
+
+/--
+The adjacent retention drop lies in the finite jump box `[-k, k]`.
+
+This is a pointwise adjacent-edge bound.  It does not assert monotonicity or
+propagation of retention mass across a window family.
+-/
+theorem sourceRetentionDropInt_bounds_window
+    (n : OddNat) (k r j : ℕ) :
+    - (k : ℤ) ≤ SourceRetentionDropInt n k r j ∧
+      SourceRetentionDropInt n k r j ≤ (k : ℤ) :=
+  ⟨neg_window_le_sourceRetentionDropInt n k r j,
+    sourceRetentionDropInt_le_window n k r j⟩
+
 /--
 Integer-valued continuation drop across adjacent pressure depths.

@@ -114,6 +157,46 @@ noncomputable def SourceContinuationDropInt
   (orbitWindowContinuationSiblingMassPow2 n k (r + j) : ℤ) -
     (orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) : ℤ)

+/--
+Finite local upper bound for one adjacent continuation drop.
+
+Both endpoint continuation masses are finite window counts, so their integer
+difference cannot exceed the window size `k`.
+-/
+theorem sourceContinuationDropInt_le_window
+    (n : OddNat) (k r j : ℕ) :
+    SourceContinuationDropInt n k r j ≤ (k : ℤ) := by
+  have hcur :
+      orbitWindowContinuationSiblingMassPow2 n k (r + j) ≤ k :=
+    orbitWindowContinuationSiblingMassPow2_le_window n k (r + j)
+  unfold SourceContinuationDropInt
+  omega
+
+/--
+Finite local lower bound for one adjacent continuation drop.
+-/
+theorem neg_window_le_sourceContinuationDropInt
+    (n : OddNat) (k r j : ℕ) :
+    - (k : ℤ) ≤ SourceContinuationDropInt n k r j := by
+  have hnext :
+      orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) ≤ k :=
+    orbitWindowContinuationSiblingMassPow2_le_window n k (r + j + 1)
+  unfold SourceContinuationDropInt
+  omega
+
+/--
+The adjacent continuation drop lies in the finite jump box `[-k, k]`.
+
+This is only a local adjacent-edge bound.  It does not imply any global
+continuation trend.
+-/
+theorem sourceContinuationDropInt_bounds_window
+    (n : OddNat) (k r j : ℕ) :
+    - (k : ℤ) ≤ SourceContinuationDropInt n k r j ∧
+      SourceContinuationDropInt n k r j ≤ (k : ℤ) :=
+  ⟨neg_window_le_sourceContinuationDropInt n k r j,
+    sourceContinuationDropInt_le_window n k r j⟩
+
 /--
 Integer-valued net pressure drop across adjacent pressure depths.

@@ -127,6 +210,45 @@ noncomputable def SourcePressureNetDropInt
   SourceRetentionDropInt n k r j -
     2 * SourceContinuationDropInt n k r j

+/--
+Finite local upper bound for one adjacent net pressure drop.
+
+The net drop is `retention_drop - 2 * continuation_drop`.  Combining the two
+`[-k, k]` jump boxes gives the coarse but uniform upper bound `3k`.
+-/
+theorem sourcePressureNetDropInt_le_three_mul_window
+    (n : OddNat) (k r j : ℕ) :
+    SourcePressureNetDropInt n k r j ≤ 3 * (k : ℤ) := by
+  have hret := sourceRetentionDropInt_le_window n k r j
+  have hcont := neg_window_le_sourceContinuationDropInt n k r j
+  unfold SourcePressureNetDropInt
+  omega
+
+/--
+Finite local lower bound for one adjacent net pressure drop.
+-/
+theorem neg_three_mul_window_le_sourcePressureNetDropInt
+    (n : OddNat) (k r j : ℕ) :
+    - (3 * (k : ℤ)) ≤ SourcePressureNetDropInt n k r j := by
+  have hret := neg_window_le_sourceRetentionDropInt n k r j
+  have hcont := sourceContinuationDropInt_le_window n k r j
+  unfold SourcePressureNetDropInt
+  omega
+
+/--
+The adjacent net pressure drop lies in the finite local jump box `[-3k, 3k]`.
+
+This is the jump analogue of the pointwise margin-height box.  It bounds one
+adjacent transition; it does not assert propagation, coverage, aggregation, or
+Collatz convergence.
+-/
+theorem sourcePressureNetDropInt_bounds_window
+    (n : OddNat) (k r j : ℕ) :
+    - (3 * (k : ℤ)) ≤ SourcePressureNetDropInt n k r j ∧
+      SourcePressureNetDropInt n k r j ≤ 3 * (k : ℤ) :=
+  ⟨neg_three_mul_window_le_sourcePressureNetDropInt n k r j,
+    sourcePressureNetDropInt_le_three_mul_window n k r j⟩
+
 /--
 Adjacent source-pressure margin accounting identity.

diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-237.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-237.md
new file mode 100644
index 00000000..075557fb
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-237.md
@@ -0,0 +1,203 @@
+# report-petal-237
+
+## Checkpoint
+
+`petal-237`
+
+## Summary
+
+Implemented Branch A and Branch B.
+
+The checkpoint requested finite local jump bounds for retention drop,
+continuation drop, and net pressure drop.  The actual definitions in
+`PressureDecay.lean` are edge-indexed by `j`, so the implemented public surface
+keeps the adjacent-edge parameter:
+
+```lean
+SourceRetentionDropInt n k r j
+SourceContinuationDropInt n k r j
+SourcePressureNetDropInt n k r j
+```
+
+This is the correct API shape for the current source code: `r` is the base
+pressure depth, while `j` selects the adjacent transition
+`r + j -> r + j + 1`.
+
+## Implemented Theorems
+
+### Retention drop
+
+```lean
+theorem sourceRetentionDropInt_le_window
+    (n : OddNat) (k r j : ℕ) :
+    SourceRetentionDropInt n k r j ≤ (k : ℤ)
+
+theorem neg_window_le_sourceRetentionDropInt
+    (n : OddNat) (k r j : ℕ) :
+    - (k : ℤ) ≤ SourceRetentionDropInt n k r j
+
+theorem sourceRetentionDropInt_bounds_window
+    (n : OddNat) (k r j : ℕ) :
+    - (k : ℤ) ≤ SourceRetentionDropInt n k r j ∧
+      SourceRetentionDropInt n k r j ≤ (k : ℤ)
+```
+
+Meaning:
+
+```text
+retention adjacent jump ∈ [-k, k]
+```
+
+The proof uses the existing finite-window bound
+`orbitWindowRetentionMassPow2_le_window`.
+
+### Continuation drop
+
+```lean
+theorem sourceContinuationDropInt_le_window
+    (n : OddNat) (k r j : ℕ) :
+    SourceContinuationDropInt n k r j ≤ (k : ℤ)
+
+theorem neg_window_le_sourceContinuationDropInt
+    (n : OddNat) (k r j : ℕ) :
+    - (k : ℤ) ≤ SourceContinuationDropInt n k r j
+
+theorem sourceContinuationDropInt_bounds_window
+    (n : OddNat) (k r j : ℕ) :
+    - (k : ℤ) ≤ SourceContinuationDropInt n k r j ∧
+      SourceContinuationDropInt n k r j ≤ (k : ℤ)
+```
+
+Meaning:
+
+```text
+continuation adjacent jump ∈ [-k, k]
+```
+
+The proof uses the existing finite-window bound
+`orbitWindowContinuationSiblingMassPow2_le_window`.
+
+### Net pressure drop
+
+```lean
+theorem sourcePressureNetDropInt_le_three_mul_window
+    (n : OddNat) (k r j : ℕ) :
+    SourcePressureNetDropInt n k r j ≤ 3 * (k : ℤ)
+
+theorem neg_three_mul_window_le_sourcePressureNetDropInt
+    (n : OddNat) (k r j : ℕ) :
+    - (3 * (k : ℤ)) ≤ SourcePressureNetDropInt n k r j
+
+theorem sourcePressureNetDropInt_bounds_window
+    (n : OddNat) (k r j : ℕ) :
+    - (3 * (k : ℤ)) ≤ SourcePressureNetDropInt n k r j ∧
+      SourcePressureNetDropInt n k r j ≤ 3 * (k : ℤ)
+```
+
+Meaning:
+
+```text
+net pressure adjacent jump ∈ [-3k, 3k]
+```
+
+This follows from:
+
+```lean
+SourcePressureNetDropInt
+  = SourceRetentionDropInt - 2 * SourceContinuationDropInt
+```
+
+and the two component jump boxes.
+
+## Height Bounds vs Jump Bounds
+
+cp236 established finite local height bounds:
+
+```text
+SourcePressureMarginInt n k r ∈ [-k, 2k]
+```
+
+Those theorems bound the pressure margin at a single depth.
+
+cp237 establishes finite local jump bounds:
+
+```text
+SourceRetentionDropInt n k r j      ∈ [-k, k]
+SourceContinuationDropInt n k r j   ∈ [-k, k]
+SourcePressureNetDropInt n k r j    ∈ [-3k, 3k]
+```
+
+These theorems bound one adjacent transition.  They do not claim propagation,
+coverage, global descent, or convergence.
+
+## Big / Core / Beam / Gap Classification
+
+- Core:
+  existing finite-window mass bounds:
+  `orbitWindowRetentionMassPow2_le_window` and
+  `orbitWindowContinuationSiblingMassPow2_le_window`.
+
+- True Beam:
+  the finite jump boxes are now theoremized.  They give a verified local
+  diagnostic for each adjacent pressure step.
+
+- Boundary:
+  the bound is local to `(r, j)` and to the finite observation window `k`.
+
+- False Beam:
+  no monotonicity, no global trend, and no coverage theorem follows from these
+  bounds alone.
+
+- Gap:
+  the interaction between cp235 sign transition, cp236 height box, and cp237
+  jump box is not yet bundled into a single pulse diagnostic theorem.
+
+## Next Branch Prediction
+
+The next natural branch is to combine:
+
+```text
+cp235 sign transition
++ cp236 height box
++ cp237 jump box
+```
+
+into a thin local pulse wrapper.
+
+That wrapper should stay local and witness-based.  A useful target would expose
+one seed/pulse witness together with:
+
+```text
+left margin sign
+center margin sign
+right margin sign
+margin height box
+net-drop jump box
+```
+
+The wrapper should not claim propagation, list coverage, overlap repair,
+canonical witness selection, or Collatz convergence.
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
