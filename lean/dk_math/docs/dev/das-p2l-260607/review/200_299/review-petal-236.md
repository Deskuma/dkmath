# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam.Pulse

gch: 56a9df5e69bd75f97dc85a25dc47ec97266a25ef

## Report

cp235 実装完了です。

`PressureBeam/Pulse.lean` に1本だけ追加しました。

```lean
exists_sourcePressureBeamPulse_witness_center_margin_signs_of_seed
```

cp234 の centered diagnostic を消費して、seed から witness `W` を取り出し、

- `r + (W.val - 1)` は非正
- `r + W.val` は正
- `W.val` は addressed depth target
- `r + W.val + 1` は非正

という centered margin-sign transition を出します。

添字規約はコードコメントにも明記しました。mass-balance at edge `j` は next margin `r + j + 1` を分類します。したがって entry edge `W.val - 1` は `r + W.val` の正値、exit edge `W.val` は `r + W.val + 1` の非正値に対応します。

検証済みです。

```text
lake build DkMath.Collatz.PetalBridge.PressureBeam.Core
lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
git diff --check
```

対象 pressure 範囲の `sorry/admit` grep も該当なしです。レポートは `lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-235.md` に追加しました。

## Review

## 結論

**採用。これは二塁打じゃ。**
cp235 は、cp234 の centered diagnostic をちゃんと次段へ進めて、**margin-sign transition** まで落としている。

追加 theorem は 1 本。

```lean
exists_sourcePressureBeamPulse_witness_center_margin_signs_of_seed
```

これで `SourcePressureBeamSeed L` から witness `W` を取り出し、

```text
r + (W.val - 1) は非正
r + W.val は正
W.val は addressed depth target
r + W.val + 1 は非正
```

という **native depth 上の local pulse sign pattern** が得られるようになった。添字規約も明記されており、mass-balance at edge `j` が next margin `r + j + 1` を分類する、と整理されている。

## 実装レビュー

証明の筋は良い。

まず cp234 の theorem を使う。

```lean
exists_sourcePressureBeamPulse_witness_center_full_diagnostic_of_seed
```

ここから、

```text
MassBalanceLeft (W.val - 1) < MassBalanceRight (W.val - 1)
SourcePressureBeamAddressedDepthTarget L W.val
MassBalanceRight W.val ≤ MassBalanceLeft W.val
```

を得る。

それを、

```lean
sourcePressureMargin_next_pos_iff_massBalanceLeft_lt_right_edge
```

で entry 側の positive margin へ変換し、

```lean
sourcePressureMargin_next_nonpos_of_massBalanceRight_le_left
```

で exit 側の nonpositive margin へ変換している。

さらに、前状態の非正性は local-island witness 自身から取っている。

```lean
(sourcePressureLocalIsland_iff_margin n k r W.val).1 W.property
```

ここも良い。
Pulse 診断を無理に再構築していないし、既存の local island / mass-balance / margin bridge を使っている。

## 添字規約の確定が大きい

今回の重要点は theorem そのものだけではない。
添字規約が明文化されたことが大きい。

```text
mass-balance at edge j
  -> next margin at r + j + 1
```

したがって、

```text
entry edge = W.val - 1
  -> r + W.val が正

exit edge = W.val
  -> r + W.val + 1 が非正
```

これで local pulse は、native depth 上で

```text
非正 -> 正 -> 非正
```

として読める。

つまり、やっと

```text
W.val が孤立正圧の中心
```

として Lean theorem surface に出た。

## 数学的意味

これは **局所 pulse の Core 化** じゃ。

cp234 では、

```text
mass-balance comparison
```

だった。

cp235 では、それが

```text
margin sign profile
```

に戻った。

つまり、

```text
entry comparison:
  圧力が正領域へ入る

center:
  addressed depth target

exit comparison:
  圧力が非正領域へ落ちる
```

が一つの theorem にまとまった。

DkMath 的にはこう読める。

```text
Core:
  W.val を中心とする局所 pulse が存在する

True Beam:
  r + W.val で pressure margin が正

Boundary / False Beam:
  直前 r + (W.val - 1) と直後 r + W.val + 1 は非正

Gap:
  これが他の witness や時間方向へ伝播するとはまだ言っていない
```

## 注意点

この theorem は強いが、まだ **local Big bound** ではない。

言えているのは、

```text
非正 -> 正 -> 非正
```

という符号形。

まだ言っていないのは、

```text
正の高さがどれだけか
net drop がどれだけか
pulse がどれだけ連鎖するか
window 全体を覆うか
大域的に下降するか
```

じゃ。

つまり、Collatz 収束はもちろん、局所 Big の数値上界すらまだ theorem としては出ていない。

## 次の球筋

ここで snapshot を見ると、次の狙いはかなり明確じゃ。

`SourcePressureMarginInt` は定義上、

```lean
(2 * continuation : ℤ) - (retention : ℤ)
```

であり、既存には mass 側の window bound がある。

```lean
orbitWindowRetentionMassPow2_le_window
orbitWindowContinuationSiblingMassPow2_le_window
```

つまり、任意の depth で粗いが強い有限上界が出る。

```text
retention ≤ k
continuation ≤ k
```

したがって margin は必ず、

```text
-k ≤ SourcePressureMarginInt n k r ≤ 2k
```

に入る。

これはまさに **局所 Big の最初の箱** じゃ。

符号 pulse は、

```text
非正 -> 正 -> 非正
```

だった。
次に欲しいのは、

```text
その正の高さも、負側の深さも、有限 window k によって包まれる
```

という theorem。

これを先に取るべきじゃ。
centered wrapper を増やすより、こっちが次の命中球。

## 次の checkpoint 方針

次は `PressureDecay` か、`SourcePressureMarginInt` を定義している低位 module に、margin の有限 window bound を置く。

候補 theorem はこの 3 本。

```lean
theorem sourcePressureMarginInt_le_two_mul_window
    (n : OddNat) (k r : ℕ) :
    SourcePressureMarginInt n k r ≤ 2 * (k : ℤ)
```

```lean
theorem neg_window_le_sourcePressureMarginInt
    (n : OddNat) (k r : ℕ) :
    - (k : ℤ) ≤ SourcePressureMarginInt n k r
```

```lean
theorem sourcePressureMarginInt_bounds_window
    (n : OddNat) (k r : ℕ) :
    - (k : ℤ) ≤ SourcePressureMarginInt n k r ∧
      SourcePressureMarginInt n k r ≤ 2 * (k : ℤ)
```

これは propagation でも coverage でもない。
完全に局所的な finite window bound。

これが通れば、次に cp235 の sign pattern と接続して、

```text
seed
  -> ∃ W,
       local pulse sign pattern
       and all three margins lie in [-k, 2k]
```

へ行ける。

## 次の Codex 指示

```text
Checkpoint: petal-236

Primary Goal:
  Establish the first finite local Big bound for source pressure margins.

Context:
  cp235 converted the centered seed diagnostic into a native-depth sign pattern:

    SourcePressureBeamSeed L
      -> ∃ W ∈ L,
           SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0
           ∧ 0 < SourcePressureMarginInt n k (r + W.val)
           ∧ SourcePressureBeamAddressedDepthTarget L W.val
           ∧ SourcePressureMarginInt n k (r + W.val + 1) ≤ 0

  This gives the local pulse shape, but not its finite height bound.

  The next target is the generic window-size bound for `SourcePressureMarginInt`.

Key observation:
  By definition,

    SourcePressureMarginInt n k r
      = (2 * continuation : ℤ) - (retention : ℤ)

  and existing mass bounds should give:

    retention ≤ k
    continuation ≤ k

  Therefore every source pressure margin should lie in the finite interval:

    -k ≤ SourcePressureMarginInt n k r ≤ 2k

Strategic Branch Goals:

  Branch A: direct generic margin bounds
    Inspect the definitions and existing mass bounds:

      SourcePressureMarginInt
      orbitWindowRetentionMassPow2_le_window
      orbitWindowContinuationSiblingMassPow2_le_window

    If direct, add the following low-level theorems near the definition of
    `SourcePressureMarginInt`, likely in `PressureDecay.lean`:

      theorem sourcePressureMarginInt_le_two_mul_window
          (n : OddNat) (k r : ℕ) :
          SourcePressureMarginInt n k r ≤ 2 * (k : ℤ)

      theorem neg_window_le_sourcePressureMarginInt
          (n : OddNat) (k r : ℕ) :
          - (k : ℤ) ≤ SourcePressureMarginInt n k r

      theorem sourcePressureMarginInt_bounds_window
          (n : OddNat) (k r : ℕ) :
          - (k : ℤ) ≤ SourcePressureMarginInt n k r ∧
            SourcePressureMarginInt n k r ≤ 2 * (k : ℤ)

    These are the first local Big bounds for pressure margin height.

  Branch B: cast / omega friction
    If the proof is blocked only by Nat-to-Int casts, add tiny private/local
    helper steps in the proof, but do not introduce broad new API.

    Prefer proof-local `have` statements using existing Nat bounds and `omega`.

  Branch C: bounds already exist
    If equivalent bounds already exist under another name, do not duplicate.
    Report the exact theorem names and add no code unless an alias is clearly
    useful.

  Branch D: centered seed pulse plus bounds
    If Branch A succeeds and a combined theorem is one-line, consider adding
    one caller-facing theorem in `PressureBeam/Pulse.lean`:

      SourcePressureBeamSeed L
        -> ∃ W ∈ L,
             centered margin-sign transition
             and the involved margins are bounded by [-k, 2k]

    Add this only if the statement remains readable.
    Otherwise, report the theorem chain and postpone the combined wrapper.

  Branch E: stronger local Big is visible
    If existing API already bounds net drop, retention drop, or continuation
    drop directly, do not add a large theorem in this checkpoint.
    Report the candidate next theorem shapes.

Implementation rules:
  - Use #check, #print, and scratch lemmas.
  - Inspect exact theorem names for window-size bounds.
  - Add no more than three small theorems.
  - Prefer generic margin bounds over seed-specific wrappers.
  - Do not add adjacent-pair / overlap centered wrappers in this checkpoint.

Guardrails:
  Do not add:
    - propagation;
    - list-wide coverage;
    - witness-family aggregation;
    - canonical witness selection;
    - arbitrary target transport;
    - overlap repair;
    - disjointness;
    - Collatz convergence;
    - global Big bounds.

Dependency guardrail:
  The generic margin bounds belong at or below the module defining
  `SourcePressureMarginInt`.
  Beam-facing wrappers, if any, belong only above that layer.

Verification:
  lake build DkMath.Collatz.PetalBridge.PressureDecay
  lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
  lake build DkMath.Collatz.PetalBridge.PressureBeam
  lake build DkMath.Collatz.PetalBridge
  no-sorry grep over inspected pressure files
  git diff --check

Report requirements:
  - State which Branch was taken.
  - Show the exact margin bound theorem statements.
  - Explain that this is a finite local Big bound, not propagation.
  - If no theorem was added, identify the existing theorem names.
  - Classify results as True Beam / Boundary / False Beam / Gap.
  - Predict whether the next branch should bound net drop or combine cp235 with
    the new margin bounds.
```

## 待ち構え

次の期待はこれ。

```text
A:
  -k ≤ margin ≤ 2k
```

これが通れば、局所 Big の箱ができる。

次の次は、

```text
cp235 sign pulse
+
margin bounds
```

を組み合わせて、

```text
seed から得られる local pulse は、
有限 window k の中で高さが制限される
```

まで行ける。

## 総合判断

cp235 は成功。
これは当たった。

次は、符号形から **有限高さの箱** へ進む。
つまり、

```text
非正 -> 正 -> 非正
```

を、

```text
[-k, 2k] の有限箱の中で起きる局所 pulse
```

として閉じる。

ここが局所 Big の最初の実体じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
index ed40e1d1..1a2b81f8 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
@@ -309,6 +309,52 @@ theorem exists_sourcePressureBeamPulse_witness_center_full_diagnostic_of_seed
     ⟨W, hmem,
       sourcePressureBeamPulse_witness_singleton_full_diagnostic_at_center hmem⟩

+/--
+A Beam seed exposes one witness whose centered diagnostic also gives the local
+margin-sign transition around the native depth `W.val`.
+
+The index convention is the Beam edge convention:
+
+* mass-balance at edge `j` classifies the next margin `r + j + 1`;
+* therefore the entry comparison at `W.val - 1` gives positivity at `r + W.val`;
+* the exit comparison at `W.val` gives nonpositivity at `r + W.val + 1`.
+
+The previous margin nonpositivity at `W.val - 1` is read from the local-island
+witness itself.  This theorem remains witness-local and seed-existential: it
+does not choose a canonical witness, aggregate a family, repair overlaps,
+propagate the transition, or claim Collatz convergence.
+-/
+theorem exists_sourcePressureBeamPulse_witness_center_margin_signs_of_seed
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hseed : SourcePressureBeamSeed L) :
+    ∃ W : SourcePressureLocalIslandWitness n k r,
+      W ∈ L ∧
+        SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0 ∧
+          0 < SourcePressureMarginInt n k (r + W.val) ∧
+            SourcePressureBeamAddressedDepthTarget L W.val ∧
+              SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 := by
+  rcases exists_sourcePressureBeamPulse_witness_center_full_diagnostic_of_seed
+      hseed with
+    ⟨W, hmem, hentry, haddr, hexit⟩
+  have hlocal :=
+    (sourcePressureLocalIsland_iff_margin n k r W.val).1 W.property
+  rcases hlocal with ⟨hWpos, _hcenterLocal, hprev, _hnextLocal⟩
+  have hcenterFromEntry :
+      0 < SourcePressureMarginInt n k (r + W.val) := by
+    have hentryNext :
+        0 < SourcePressureMarginInt n k (r + (W.val - 1) + 1) :=
+      (sourcePressureMargin_next_pos_iff_massBalanceLeft_lt_right_edge
+        n k r (W.val - 1)).2 hentry
+    have hidx : r + (W.val - 1) + 1 = r + W.val := by
+      omega
+    simpa [hidx] using hentryNext
+  have hnextFromExit :
+      SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 :=
+    sourcePressureMargin_next_nonpos_of_massBalanceRight_le_left haddr hexit
+  exact
+    ⟨W, hmem, hprev, hcenterFromEntry, haddr, hnextFromExit⟩
+
 /--
 Failure resolution also exposes one witness whose singleton pulse has the full
 local entry-depth-exit diagnostic.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-235.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-235.md
new file mode 100644
index 00000000..db9fd364
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-235.md
@@ -0,0 +1,128 @@
+# report-petal-235
+
+## Checkpoint
+
+`petal-235`
+
+## Result
+
+Implemented Branch A.
+
+The centered seed diagnostic from cp234 now feeds a centered local
+margin-sign transition theorem.
+
+## Added Theorem
+
+```lean
+theorem exists_sourcePressureBeamPulse_witness_center_margin_signs_of_seed
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hseed : SourcePressureBeamSeed L) :
+    ∃ W : SourcePressureLocalIslandWitness n k r,
+      W ∈ L ∧
+        SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0 ∧
+          0 < SourcePressureMarginInt n k (r + W.val) ∧
+            SourcePressureBeamAddressedDepthTarget L W.val ∧
+              SourcePressureMarginInt n k (r + W.val + 1) ≤ 0
+```
+
+## Margin Index Convention
+
+The discovered convention is:
+
+```text
+mass-balance at edge j
+  classifies the next margin at r + j + 1
+```
+
+Therefore:
+
+```text
+entry edge  = W.val - 1
+entry sign  = positivity at r + (W.val - 1) + 1 = r + W.val
+
+exit edge   = W.val
+exit sign   = nonpositivity at r + W.val + 1
+```
+
+The previous sign at `r + (W.val - 1)` is obtained from the local-island
+witness itself.
+
+## Proof Chain
+
+The theorem consumes:
+
+```lean
+exists_sourcePressureBeamPulse_witness_center_full_diagnostic_of_seed
+```
+
+which supplies:
+
+```text
+W ∈ L
+MassBalanceLeft (W.val - 1) < MassBalanceRight (W.val - 1)
+SourcePressureBeamAddressedDepthTarget L W.val
+MassBalanceRight W.val ≤ MassBalanceLeft W.val
+```
+
+Then:
+
+```lean
+sourcePressureMargin_next_pos_iff_massBalanceLeft_lt_right_edge
+```
+
+converts the entry comparison to positive margin at `r + W.val`, and:
+
+```lean
+sourcePressureMargin_next_nonpos_of_massBalanceRight_le_left
+```
+
+converts the exit comparison to nonpositive margin at `r + W.val + 1`.
+
+## Beam Classification
+
+- True Beam: `0 < SourcePressureMarginInt n k (r + W.val)`.
+- Boundary / False Beam:
+  `SourcePressureMarginInt n k (r + W.val + 1) ≤ 0`.
+- Core: `SourcePressureBeamAddressedDepthTarget L W.val` remains visible.
+- Gap: no propagation, coverage, local Big bound, or convergence is claimed.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureBeam.Core
+lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
+lake build DkMath.Collatz.PetalBridge.PressureBeam
+lake build DkMath.Collatz.PetalBridge
+git diff --check
+```
+
+No `sorry` or `admit` was found in the requested pressure-file grep scope.
+
+Known unrelated warning still appears during builds:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
+
+## Next Branch
+
+The next branch can attack local Big bounds, but only if an existing theorem
+already turns this sign pattern into a bounded local estimate without adding
+propagation or list coverage.
+
+Recommended next search:
+
+```text
+SourcePressureMarginInt
+SourcePressureNetDropInt
+retention mass
+continuation mass
+local Big / upper bound
+```
+
+If no direct bridge exists, add a report-only chain first and postpone the
+theorem.
````
`````
