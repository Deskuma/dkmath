# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: 2a143ae2cbe8e8514182db0d84701e494ab8e5e8

## Report

実装完了です。

[PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:403) に左 endpoint 用、[同ファイル](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:439) に右 endpoint 用の margin sign projection を追加しました。

追加 theorem:

```lean
sourcePressureOrientedNeighborDiagnosticState_left_center_margin_signs
sourcePressureOrientedNeighborDiagnosticState_right_center_margin_signs
```

どちらも `SourcePressureOrientedNeighborDiagnosticState L W W'` から、対応する `W` / `W'` について

```text
previous margin <= 0
center margin   >  0
addressed depth target
next margin     <= 0
```

を取り出します。

レポートは [report-petal-251.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-251.md:1) に追加しました。

確認済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

## Review

## 判定

採用。
`OrientedNeighborDiagnosticState` から、左右 endpoint の sign pattern が直接取れるようになった。

追加：

```lean id="f9fqx6"
sourcePressureOrientedNeighborDiagnosticState_left_center_margin_signs
sourcePressureOrientedNeighborDiagnosticState_right_center_margin_signs
```

これで状態 `D` は、

```text id="3neohx"
D(W,W') -> signs(W)
D(W,W') -> signs(W')
```

を持つ。

## 増えた事実

左右それぞれについて、これが出る。

```text id="x0zwh7"
previous margin <= 0
center margin   >  0
addressed depth target
next margin     <= 0
```

つまり `OrientedNeighborDiagnosticState L W W'` は、単に mass-balance diagnostic を持つだけではなく、**両 endpoint が centered pulse sign を持つ状態**として読める。

証明筋も良い。

```text id="6rc4co"
prev nonpos:
  local-island witness property

center positive:
  entry mass-balance at val - 1
  -> next margin positivity

next nonpos:
  exit mass-balance at val
  -> next margin nonpositivity
```

添字変換 `r + (val - 1) + 1 = r + val` は `omega`。

## 状態表の更新

現在：

```text id="gvjwdq"
SortedFailure
  -> D ∨ PO

FailureResolution
  -> D ∨ PO

BeamSeed
  -> D ∨ PO

D(W,W')
  -> signs(W)
  -> signs(W')
```

ここまで来たので、`D` は観測状態としてかなり使いやすい。

## 次に攻める定理

次は `D` から **height/jump box** を左右 endpoint へ出す。

cp236/cp237 の generic bounds はすでにあるので、薄く出せる。

まず height：

```lean id="eq5zo8"
sourcePressureOrientedNeighborDiagnosticState_left_margin_boxes
sourcePressureOrientedNeighborDiagnosticState_right_margin_boxes
```

または、左右まとめて：

```lean id="i3xd63"
sourcePressureOrientedNeighborDiagnosticState_pair_margin_boxes
```

中身：

```text id="0a2qyr"
bounds at:
  r + (W.val - 1)
  r + W.val
  r + W.val + 1

bounds at:
  r + (W'.val - 1)
  r + W'.val
  r + W'.val + 1
```

次に jump：

```lean id="sv9wi2"
sourcePressureOrientedNeighborDiagnosticState_pair_netDrop_boxes
```

中身：

```text id="g1eqer"
net drop bounds at:
  W.val - 1
  W.val
  W'.val - 1
  W'.val
```

ただし statement が大きくなる。
ここは predicate 化がよい。

## 次の設計

`D` の boxed 版を作る。

```lean id="h75wld"
def SourcePressureOrientedNeighborBoxState
    (L : List (SourcePressureLocalIslandWitness n k r))
    (W W' : SourcePressureLocalIslandWitness n k r) : Prop := ...
```

中身：

```text id="gv1f0o"
OrientedNeighborDiagnosticState L W W'
signs(W)
signs(W')
height boxes for W and W'
jump boxes for W and W'
```

そして theorem：

```lean id="ekcpx8"
sourcePressureOrientedNeighborDiagnosticState_to_boxState
```

これで `D` が、二点 box 状態へ昇格する。

## Codex 指示

```text id="mk8o1b"
Goal:
  Package OrientedNeighborDiagnosticState into a two-endpoint box state.

Add in PressureState.lean:

  def SourcePressureOrientedNeighborBoxState
      {n : OddNat} {k r : ℕ}
      (L : List (SourcePressureLocalIslandWitness n k r))
      (W W' : SourcePressureLocalIslandWitness n k r) : Prop := ...

Include:
  SourcePressureOrientedNeighborDiagnosticState L W W'
  signs for W
  signs for W'
  margin height bounds at:
    r + (W.val - 1), r + W.val, r + W.val + 1
    r + (W'.val - 1), r + W'.val, r + W'.val + 1
  net-drop bounds at:
    W.val - 1, W.val, W'.val - 1, W'.val

Add theorem:

  theorem sourcePressureOrientedNeighborDiagnosticState_to_boxState
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureOrientedNeighborDiagnosticState L W W') :
      SourcePressureOrientedNeighborBoxState L W W'

Use:
  sourcePressureOrientedNeighborDiagnosticState_left_center_margin_signs
  sourcePressureOrientedNeighborDiagnosticState_right_center_margin_signs
  sourcePressureMarginInt_bounds_window
  sourcePressureNetDropInt_bounds_window

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の狙い

`D` を二点 box にする。

```text id="zrqjv7"
OrientedNeighborDiagnostic
  -> two-endpoint signs
  -> two-endpoint height/jump boxes
```

これが通れば、次は pair-level の比較へ行ける。

```text id="1yybjv"
W と W' の pulse box が並ぶ
  -> pair relation を数値的に読む
```

ここから transport / obstruction の解析に入れる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index bf445899..876d46f4 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -383,6 +383,87 @@ theorem sourcePressureOrientedNeighborDiagnosticState_of_forward
   exact
     ⟨hin, hdiag', hWentry, hWaddr, hWexit, hW'entry, hW'addr, hW'exit⟩
 
+/--
+Project the left endpoint margin-sign pattern from an oriented neighbor
+diagnostic state.
+
+The oriented state stores mass-balance entry/exit comparisons for `W`.
+Together with the local-island witness property, these comparisons recover the
+three-margin pattern around the native depth `W.val`:
+
+```text
+r + (W.val - 1) <= 0
+r + W.val       >  0
+r + W.val + 1   <= 0
+```
+
+This is a pure projection from state `D`; it does not add transport,
+propagation, coverage, or canonical witness selection.
+-/
+theorem sourcePressureOrientedNeighborDiagnosticState_left_center_margin_signs
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureOrientedNeighborDiagnosticState L W W') :
+    SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0 ∧
+      0 < SourcePressureMarginInt n k (r + W.val) ∧
+        SourcePressureBeamAddressedDepthTarget L W.val ∧
+          SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 := by
+  rcases h with
+    ⟨_hin, _hdiag, hentry, haddr, hexit, _hentry', _haddr', _hexit'⟩
+  have hlocal :=
+    (sourcePressureLocalIsland_iff_margin n k r W.val).1 W.property
+  rcases hlocal with ⟨_hWpos, _hcenterLocal, hprev, _hnextLocal⟩
+  have hcenter :
+      0 < SourcePressureMarginInt n k (r + W.val) := by
+    have hentryNext :
+        0 < SourcePressureMarginInt n k (r + (W.val - 1) + 1) :=
+      (sourcePressureMargin_next_pos_iff_massBalanceLeft_lt_right_edge
+        n k r (W.val - 1)).2 hentry
+    have hidx : r + (W.val - 1) + 1 = r + W.val := by
+      omega
+    simpa [hidx] using hentryNext
+  have hnext :
+      SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 :=
+    sourcePressureMargin_next_nonpos_of_massBalanceRight_le_left haddr hexit
+  exact ⟨hprev, hcenter, haddr, hnext⟩
+
+/--
+Project the right endpoint margin-sign pattern from an oriented neighbor
+diagnostic state.
+
+This is the same projection as the left endpoint theorem, but applied to the
+oriented neighbor endpoint `W'`.  The proof deliberately reads only the local
+fields already stored in state `D`.
+-/
+theorem sourcePressureOrientedNeighborDiagnosticState_right_center_margin_signs
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureOrientedNeighborDiagnosticState L W W') :
+    SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
+      0 < SourcePressureMarginInt n k (r + W'.val) ∧
+        SourcePressureBeamAddressedDepthTarget L W'.val ∧
+          SourcePressureMarginInt n k (r + W'.val + 1) ≤ 0 := by
+  rcases h with
+    ⟨_hin, _hdiag, _hentry, _haddr, _hexit, hentry', haddr', hexit'⟩
+  have hlocal :=
+    (sourcePressureLocalIsland_iff_margin n k r W'.val).1 W'.property
+  rcases hlocal with ⟨_hW'pos, _hcenterLocal, hprev, _hnextLocal⟩
+  have hcenter :
+      0 < SourcePressureMarginInt n k (r + W'.val) := by
+    have hentryNext :
+        0 < SourcePressureMarginInt n k (r + (W'.val - 1) + 1) :=
+      (sourcePressureMargin_next_pos_iff_massBalanceLeft_lt_right_edge
+        n k r (W'.val - 1)).2 hentry'
+    have hidx : r + (W'.val - 1) + 1 = r + W'.val := by
+      omega
+    simpa [hidx] using hentryNext
+  have hnext :
+      SourcePressureMarginInt n k (r + W'.val + 1) ≤ 0 :=
+    sourcePressureMargin_next_nonpos_of_massBalanceRight_le_left haddr' hexit'
+  exact ⟨hprev, hcenter, haddr', hnext⟩
+
 /--
 Recovered adjacent state enters the oriented neighbor diagnostic state.
 
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-251.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-251.md
new file mode 100644
index 00000000..16b9bc26
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-251.md
@@ -0,0 +1,77 @@
+# Report: petal-251
+
+## Goal
+
+Project margin sign patterns from `SourcePressureOrientedNeighborDiagnosticState`.
+
+## Implemented
+
+Added in `DkMath.Collatz.PetalBridge.PressureState`:
+
+```lean
+theorem sourcePressureOrientedNeighborDiagnosticState_left_center_margin_signs
+theorem sourcePressureOrientedNeighborDiagnosticState_right_center_margin_signs
+```
+
+Both theorems expose the centered three-margin pattern from state `D`:
+
+```text
+previous margin <= 0
+center margin   >  0
+addressed depth target
+next margin     <= 0
+```
+
+The left theorem projects this pattern for `W`; the right theorem projects the
+same pattern for `W'`.
+
+## Proof Shape
+
+Each proof reads only already-stored local state evidence:
+
+- local-island witness property for the previous-margin nonpositivity,
+- entry mass-balance comparison at `val - 1` for center positivity,
+- addressed depth target from the oriented diagnostic state,
+- exit mass-balance comparison at `val` for next-margin nonpositivity.
+
+The index step
+
+```text
+r + (val - 1) + 1 = r + val
+```
+
+is discharged by `omega`.
+
+## Automaton Reading
+
+State `D` now has direct diagnostic projections:
+
+```text
+D(W,W') -> signs(W)
+D(W,W') -> signs(W')
+```
+
+This makes the oriented neighbor state usable without manually unpacking all
+mass-balance fields at call sites.
+
+## Guardrails
+
+These are projection theorems only.  They do not add:
+
+- transport or propagation,
+- list-wide coverage,
+- canonical witness selection,
+- overlap repair,
+- aggregation,
+- convergence or Collatz termination.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureState
+lake build DkMath.Collatz.PetalBridge
+git diff --check
+```
+
````
`````
