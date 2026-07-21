# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: 96c41146f50633005488d87fe7fd4adddf3dceac

## Report

実装完了です。

[PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:1093) に `SourcePressureForwardPairComparisonState.center_pair_surface` を追加しました。

これで `FPC` から一発で以下を取り出せます。

```text
left center > 0
right center > 0
left addressed target
right addressed target
W.val < W'.val
```

レポートは [report-petal-267.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-267.md:1) に追加済みです。

検証:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

すべて通過しました。

## Review

## 判定

採用。
`FPC` の中心比較 surface が一発で取れるようになった。

追加：

```lean id="gnsg73"
SourcePressureForwardPairComparisonState.center_pair_surface
```

これで `FPC` から、

```text id="rka2we"
left center > 0
right center > 0
left addressed target
right addressed target
W.val < W'.val
```

をまとめて取り出せる。`center_pos_pair` と `center_targets_pair` を束ねる、ちょうどよい caller-facing theorem じゃ。

## 増えた事実

`ForwardPairComparisonState` は、次のように読める。

```text id="1tc84i"
FPC
  -> two positive centers
  -> two addressed targets
  -> strict ordered centers
```

これで pair-comparison 層の中心部はかなり簡潔になる。

今後は毎回、

```lean id="44thuw"
h.center_pos_pair
h.center_targets_pair
```

を別々に unpack しなくてよい。

## 現在の状態表

```text id="a3dj5s"
SortedFailure + sorted(L)
  -> FPC ∨ PO

FailureResolution + sorted(L)
  -> FPC ∨ PO

BeamSeed + sorted(L)
  -> FPC ∨ PO

FPC
  -> center_pair_surface
```

ここまでで正向き branch は、

```text id="nehe7i"
正の中心が二つあり、
両方が addressed target で、
左 center が右 center より前にある
```

という比較状態になった。

## 次に攻める定理

次は予告通り、boundary sign を左右まとめて出す。

狙い：

```lean id="677zus"
theorem SourcePressureForwardPairComparisonState.boundary_sign_pair_surface
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0 ∧
      0 < SourcePressureMarginInt n k (r + W.val) ∧
        SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
          SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
            0 < SourcePressureMarginInt n k (r + W'.val) ∧
              SourcePressureMarginInt n k (r + W'.val + 1) ≤ 0 ∧
                W.val < W'.val
```

これで、

```text id="utspz6"
left:
  previous <= 0
  center > 0
  next <= 0

right:
  previous <= 0
  center > 0
  next <= 0

order:
  W.val < W'.val
```

が一つの theorem で読める。

## Codex 指示

```text id="7os23a"
Goal:
  Add the boundary-sign pair surface for SourcePressureForwardPairComparisonState.

Add in PressureState.lean:

  theorem SourcePressureForwardPairComparisonState.boundary_sign_pair_surface
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureForwardPairComparisonState L W W') :
      SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0 ∧
        0 < SourcePressureMarginInt n k (r + W.val) ∧
          SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
            SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
              0 < SourcePressureMarginInt n k (r + W'.val) ∧
                SourcePressureMarginInt n k (r + W'.val + 1) ≤ 0 ∧
                  W.val < W'.val

Use:
  h.left_signs
  h.right_signs
  h.val_lt

Proof:
  rcases h.left_signs with ⟨_, hprevL, hcenterL, _, hnextL⟩
  rcases h.right_signs with ⟨_, hprevR, hcenterR, _, hnextR⟩
  exact ⟨hprevL, hcenterL, hnextL, hprevR, hcenterR, hnextR, h.val_lt⟩

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の狙い

次で `FPC` は、二つの局所 pulse が順序付きで並ぶことをそのまま言える。

```text id="b1vw2t"
FPC
  -> left local pulse signs
  -> right local pulse signs
  -> left center before right center
```

ここまで整えば、次は左右 boundary の干渉・分離・隣接性を読む比較補題へ進める。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index 350af6d6..c8f1d7a4 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -1082,6 +1082,28 @@ theorem SourcePressureForwardPairComparisonState.center_targets_pair
     ⟨_hmemR, _hprevR, _hcenterR, htargetR, _hnextR⟩
   exact ⟨htargetL, htargetR, h.val_lt⟩

+/--
+Bundle the positive-center and addressed-target pair surfaces into one
+caller-facing theorem.
+
+This is the compact comparison surface for the forward pair branch:
+two positive centers, two addressed targets, and strict left-to-right value
+order.  It remains local to the explicit pair carried by `FPC`.
+-/
+theorem SourcePressureForwardPairComparisonState.center_pair_surface
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W') :
+    0 < SourcePressureMarginInt n k (r + W.val) ∧
+      0 < SourcePressureMarginInt n k (r + W'.val) ∧
+        SourcePressureBeamAddressedDepthTarget L W.val ∧
+          SourcePressureBeamAddressedDepthTarget L W'.val ∧
+            W.val < W'.val := by
+  rcases h.center_pos_pair with ⟨hposL, hposR, hlt⟩
+  rcases h.center_targets_pair with ⟨htargetL, htargetR, _hlt'⟩
+  exact ⟨hposL, hposR, htargetL, htargetR, hlt⟩
+
 /--
 Constructor from the forward box comparison state to the pair-comparison-facing
 state.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-267.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-267.md
new file mode 100644
index 00000000..6e197dab
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-267.md
@@ -0,0 +1,96 @@
+# Report: petal-267
+
+## Goal
+
+Bundle the two FPC center comparison facts into one caller-facing theorem.
+
+Target surface:
+
+```text
+FPC
+  -> two positive centers
+  -> two addressed targets
+  -> strict ordered centers
+```
+
+## Implemented
+
+Added the following theorem in
+`DkMath.Collatz.PetalBridge.PressureState`:
+
+```lean
+SourcePressureForwardPairComparisonState.center_pair_surface
+```
+
+The proof bundles the two existing pair-comparison facts:
+
+```lean
+h.center_pos_pair
+h.center_targets_pair
+```
+
+## Meaning
+
+The forward pair-comparison branch now has a compact caller-facing theorem:
+
+```text
+0 < margin(W.center)
+0 < margin(W'.center)
+Target(W.val)
+Target(W'.val)
+W.val < W'.val
+```
+
+This lets downstream comparison lemmas consume the positive-center and
+addressed-target payload without repeatedly unpacking the two smaller
+projection theorems.
+
+## Guardrails
+
+This checkpoint is still local to the explicit `FPC` pair.
+
+It does not assert:
+
+- uniqueness of center pulses;
+- absence of other positive centers;
+- propagation between endpoints;
+- overlap repair;
+- global coverage;
+- Collatz convergence.
+
+The pair-overlap obstruction branch remains separate.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureState
+```
+
+The final gate for this checkpoint also runs:
+
+```text
+lake build DkMath.Collatz.PetalBridge
+git diff --check
+```
+
+## Next Branch Prediction
+
+The next natural branch is to expose the boundary-sign comparison surface for
+both endpoints:
+
+```text
+previous <= 0
+center > 0
+next <= 0
+```
+
+Candidate theorem:
+
+```lean
+SourcePressureForwardPairComparisonState.boundary_sign_pair_surface
+```
+
+This would let the pair-comparison layer read both endpoints as ordered local
+pulses with nonpositive neighboring margins and positive centers.
````
`````
