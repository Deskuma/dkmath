# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking

gch: 59a94356b24e8f29f727b4124da061b1ff450f03

## Report

cp-295 を実装しました。

今回、pair-state の階層を整理し、unresolved pair の正体を明示できるようになりました。

追加した主な内容:

- `ForwardPairComparisonState ↔ ForwardBoxComparisonState`
- sorted adjacency 下での
  `ForwardBoxComparisonState ↔ OrientedNeighborBoxState`
- internal window bounds を含む
  `CanonicalFiniteWindowPackingState ↔ OrientedNeighborBoxState`
- `SourcePressureInternalPairBoxObstruction`
- oriented box の否定と obstruction の同値
- unresolved internal pair が obstruction を持つ定理
- unresolved family の obstruction 形 membership theorem

つまり、unresolved internal pair は単なる未計数項ではなく、

```text
diagnostic がない
または
left pulse box がない
または
right pulse box がない
```

という局所的な不足として分類されました。

現在の producer は、選択された existential pair についてはこの obstruction を解消できますが、任意の internal adjacent pair 全体について解消する per-pair producer はまだありません。

実装箇所は [FiniteWindowPacking.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean#L1034)、結果報告は [report-petal-295.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-295.md) です。

確認済み:

- `lake build DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking`
- `lake build DkMath.Collatz.PetalBridge.PressureState`
- `lake build DkMath.Collatz.PetalBridge`
- `git diff --check`
- 新規 `sorry` / `axiom` なし

残る本線は、任意の internal adjacent pair に対して

```text
OrientedNeighborBoxState
  ∨
InternalPairBoxObstruction
```

を直接構成する per-pair theorem です。

## Review

## 判定

**採用。cp-295 は、有限窓 local Big の未解決項を pair-state の内部まで還元した checkpoint じゃ。**

今回、

```lean
SourcePressureForwardPairComparisonState
  ↔ SourcePressureForwardBoxComparisonState
```

および、sortedness と窓境界のもとで、

```lean
SourcePressureCanonicalFiniteWindowPackingState
  ↔ SourcePressureOrientedNeighborBoxState
```

が固定された。

その結果、

```lean
P ∈ unresolvedInternalPairFamily
  ↔
P は窓内 adjacent pair
  ∧ ¬ OrientedNeighborBoxState P
```

まで読めるようになった。build、集約 import、`git diff --check` が通り、新規 `sorry` / `axiom` もない。

## 今回の本当の進展

cp-294 までの未解決項は、

```text
unresolved internal pair の個数
```

という数だけだった。

cp-295 では、その一組ごとの中身が、

```lean
SourcePressureInternalPairBoxObstruction
```

として露出した。

現行定義では、

```text
oriented diagnostic がない
または
left pulse box がない
または
right pulse box がない
```

じゃ。

したがって、local Big は概念的に、

$$
\#Positive \le \frac{hi-lo}{2}+2 + \#\{\text{内部 box 不足 pair}\}
$$

まで読めるようになった。

これは未解決項を単に別名へ置き換えたのではなく、**どの proof-state の不足を数えているか**を特定した進展じゃ。

## state 階層の整理

```lean
sourcePressureForwardPairComparisonState_iff_forwardBoxComparisonState
```

は、数学的には新事実というより重複 carrier の整理じゃ。

一方、

```lean
sourcePressureCanonicalFiniteWindowPackingState_iff_orientedNeighborBox_of_sorted
```

は有用性が高い。

窓境界、

```text
lo ≤ left center
right center ≤ hi
```

と sortedness があれば、canonical packing の数学的 payload は `OrientedNeighborBoxState` だけになる。

つまり、

```text
窓の幾何条件
+
pair の局所診断
=
canonical packing unit
```

という必要十分条件が得られた。

## ただし obstruction は、さらに一段縮む

ここが今回の重要なレビュー点じゃ。

既存 API には既に、

```lean
sourcePressureOrientedNeighborDiagnosticState_to_boxState
```

がある。

これは `OrientedNeighborDiagnosticState` から左右両方の pulse box を構成する theorem じゃ。

逆方向は今回以前から、

```lean
SourcePressureOrientedNeighborBoxState.diagnostic
```

という projection がある。

したがって実際には、無条件で、

```text
OrientedNeighborBoxState
  ↔ OrientedNeighborDiagnosticState
```

が成立する。

つまり現在の三分岐、

```text
¬ diagnostic
∨ ¬ left box
∨ ¬ right box
```

は、三つの独立した Gap ではない。

diagnostic があれば左右 box は必ず構成されるため、

```text
¬ left box -> ¬ diagnostic
¬ right box -> ¬ diagnostic
```

じゃ。

ゆえに obstruction は結局、

```text
¬ OrientedNeighborDiagnosticState
```

一つへ縮約できる。

現在の `SourcePressureInternalPairBoxObstruction` は正しいが、**冗長な De Morgan 展開**になっている。

## さらに `AdjacentDiagnosis` まで縮む

まだ一段ある。

`SourcePressureOrientedNeighborDiagnosticState` の内容は、

```text
ordered adjacency
AdjacentDiagnosis
左右 endpoint の Beam diagnostic
```

じゃ。

しかし ordered adjacency と `AdjacentDiagnosis` が与えられれば、既存 theorem が左右 endpoint の全 diagnostic を構成する。

```lean
sourcePressureOrientedNeighborDiagnosticState_of_forward
```

および、その下層の forward centered-diagnostics theorem が既にある。

unresolved family の pair は `L.zip L.tail` 由来なので、ordered adjacency は初めから持っている。

したがって internal adjacent pair 上では、

```text
OrientedNeighborDiagnosticState
  ↔ AdjacentDiagnosis
```

まで縮む。

最終的に、cp-295 の未解決 pair の正体は、

```text
box 不足
```

でも、

```text
endpoint pulse box 不足
```

でもない。

正確には、

> **`SourcePressureLocalIslandWitnessAdjacentDiagnosis` をまだ持たない internal adjacent pair**

じゃ。

## 現在の local Big の最小表現

したがって現在の成果は、最小化するとこうなる。

$$
\#Positive \le \frac{hi-lo}{2}+2 + \#\{\text{窓内 undiagnosed adjacent pairs}\}
$$

および、

$$
\#Positive \le \#Nonpos+1 + \#\{\text{窓内 undiagnosed adjacent pairs}\}
$$

これで残った Gap は、局所 pulse box ではなく、**pair diagnosis の生成問題**へ完全に集約される。

## 次目標にある罠

report では次の候補として、

```text
OrientedNeighborBoxState
  ∨ InternalPairBoxObstruction
```

が挙げられている。

しかしこれは進めてはいけない。

今回既に、

```lean
¬ Box ↔ Obstruction
```

を証明しているため、

```text
Box ∨ Obstruction
```

は実質的に、

```text
Box ∨ ¬ Box
```

でしかない。

`by_cases hbox : Box` で即座に通るが、数学的情報は一切増えない。

これは producer theorem ではなく、単なる排中律 surface じゃ。

次に必要なのは、

```text
AdjacentDiagnosis
```

を実データから作る theorem、または診断できない場合に **否定ではない具体的な正 obstruction** を返す theorem じゃ。

## 実装上の軽微な修正

```lean
sourcePressureForwardBoxComparisonState_iff_orientedNeighborBox_of_sorted
```

の引数、

```lean
(_hpair : SourcePressureLocalIslandWitnessAdjacentPairInList L W W')
```

は使用されていない。

`OrientedNeighborBoxState` 自体が ordered adjacency を含むため、この仮定は削除できる。

また、今回の committed report では module 単体 build のみ記載されているが、上部の実装報告では `PressureState` と `PetalBridge` の build も確認済みになっている。次回は report 側にも三本すべてを揃えるとよい。

## 次に攻める本命

次は obstruction を最小化したうえで、`AdjacentDiagnosis` の生成条件を調べる。

進行はこうじゃ。

```text
Box
  ↔ OrientedDiagnostic
  ↔ adjacency + AdjacentDiagnosis

internal pair は adjacency 済み

したがって

unresolved internal pair
  ↔ ¬ AdjacentDiagnosis
```

そこから初めて、

```text
AdjacentDiagnosis を作れる
または
具体的な overlap / recovered-budget obstruction がある
```

という正の pair classification を狙う。

次の Codex 指示は、この点を外さぬ形にする。

````text
Goal:
Sharpen cp-295.  Do not add the theorem

```
OrientedNeighborBoxState ∨ InternalPairBoxObstruction
```

as the main result: because cp-295 already proves
`InternalPairBoxObstruction ↔ ¬ OrientedNeighborBoxState`, that disjunction
is only excluded middle and does not reduce the unresolved correction.

Collapse the redundant box obstruction to the actual missing pair payload,
`SourcePressureLocalIslandWitnessAdjacentDiagnosis`, and then investigate a
genuine positive per-pair producer/classification theorem.

Phase A — Box and diagnostic are equivalent:
Prove the unconditional theorem:

```
theorem sourcePressureOrientedNeighborBoxState_iff_diagnostic
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r} :
  SourcePressureOrientedNeighborBoxState L W W' ↔
    SourcePressureOrientedNeighborDiagnosticState L W W'
```

Use:
SourcePressureOrientedNeighborBoxState.diagnostic
sourcePressureOrientedNeighborDiagnosticState_to_boxState

Phase B — diagnostic and adjacent diagnosis:
Under explicit ordered adjacency, prove:

```
theorem sourcePressureOrientedNeighborDiagnosticState_iff_adjacentDiagnosis
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (hpair :
      SourcePressureLocalIslandWitnessAdjacentPairInList L W W') :
  SourcePressureOrientedNeighborDiagnosticState L W W' ↔
    SourcePressureLocalIslandWitnessAdjacentDiagnosis L W W'
```

Forward:
project the adjacent diagnosis from the diagnostic state.  Add a projection
theorem if one does not already exist.

Reverse:
use `sourcePressureOrientedNeighborDiagnosticState_of_forward hpair`.

The endpoint Beam diagnostics are already produced from witness membership;
do not treat the two pulse boxes as independent missing assumptions.

Phase C — canonical state characterized by adjacent diagnosis:
Under sortedness, ordered adjacency, and internal window bounds, prove:

```
theorem sourcePressureCanonicalFiniteWindowPackingState_iff_adjacentDiagnosis
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
    (hpair :
      SourcePressureLocalIslandWitnessAdjacentPairInList L W W')
    (hlo : lo ≤ r + W.val)
    (hhi : r + W'.val ≤ hi) :
  SourcePressureCanonicalFiniteWindowPackingState L lo hi W W' ↔
    SourcePressureLocalIslandWitnessAdjacentDiagnosis L W W'
```

Compose:
canonical ↔ box
box ↔ diagnostic
diagnostic ↔ adjacent diagnosis.

Phase D — minimize the obstruction:
Add:

```
def SourcePressureInternalPairDiagnosisObstruction
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r))
    (W W' : SourcePressureLocalIslandWitness n k r) : Prop :=
  ¬ SourcePressureLocalIslandWitnessAdjacentDiagnosis L W W'
```

Prove, for an ordered adjacent pair:

```
SourcePressureInternalPairBoxObstruction L W W'
  ↔ SourcePressureInternalPairDiagnosisObstruction L W W'
```

Keep the old box-obstruction name for compatibility, but document that its
three apparent branches are not independent because an oriented diagnostic
constructs both endpoint pulse boxes.

Phase E — exact unresolved membership:
Strengthen the cp-295 membership theorem to:

```
P ∈ sourcePressureUnresolvedInternalPairFamily L lo hi
  ↔
P ∈ L.zip L.tail
  ∧ lo ≤ r + P.1.val
  ∧ r + P.2.val ≤ hi
  ∧ ¬ SourcePressureLocalIslandWitnessAdjacentDiagnosis L P.1 P.2
```

Require sortedness only where the canonical equivalence needs it.

Add a clearly named alias, if useful:

```
sourcePressureUndiagnosedInternalPairFamily
```

It may be definitionally equal to the existing unresolved family rather than
duplicating its data.

Phase F — state the sharpened local Big:
Re-export the cp-294 inequalities in diagnosis terminology:

```
positiveWitnesses.card
  ≤ (hi - lo) / 2 + 2
    + undiagnosedInternalPairFamily.card

positiveWitnesses.card
  ≤ nonposPositions.card + 1
    + undiagnosedInternalPairFamily.card
```

This should be a thin semantic alias, not a new counting proof.

Phase G — inspect the real per-pair producer:
Inspect the definitions and constructors of:

```
SourcePressureLocalIslandWitnessAdjacentDiagnosis
SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
SourcePressureLocalIslandWitnessPairOverlapObstruction
SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered
```

Determine the strongest nontrivial theorem available for an arbitrary
addressed adjacent pair.

Preferred target, only if it follows from actual lower hypotheses:

```
AdjacentPairInList L W W'
  -> AdjacentDiagnosis L W W'
     ∨ SourcePressureLocalIslandWitnessPairOverlapObstruction W W'
```

Do not prove this by `by_cases hdiag`.
The right branch must carry an existing positive obstruction structure, not
merely `¬ AdjacentDiagnosis`.

If that theorem is not derivable, identify the exact positive data missing
from `AdjacentDiagnosis.recovered`, for example:

- reversed-before evidence;
- recovered budget evidence;
- accounted-family evidence;
- overlap evidence.

Define the smallest positive pair-obstruction carrier containing those
missing witnesses.  Avoid a predicate that is only a negation of the target.

Phase H — finite-family classification:
If Phase G produces a genuine pair split, filter the internal pair family into
concrete positive branches, for example:

```
recoveredDiagnosedInternalPairs
overlapObstructedInternalPairs
budgetMissingInternalPairs
```

Prove a finite union coverage theorem for the undiagnosed family and update
the local-Big correction using those concrete families.

Phase I — cleanup:
Remove the unused `_hpair` argument from
sourcePressureForwardBoxComparisonState_iff_orientedNeighborBox_of_sorted
if no public compatibility concern requires it.

Fix the line-length warning.

Ensure the committed report records all verification commands:
lake build DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check

Report:

* Box ↔ diagnostic;
* diagnostic ↔ adjacent diagnosis under adjacency;
* unresolved internal pair ↔ missing adjacent diagnosis;
* the exact positive data still needed for a per-pair diagnosis producer;
* whether a genuine recovered/overlap pair split closed.

Build:
lake build DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
````

## 総合評価

cp-295 により、

```text
canonical packing
  ↔ oriented box
```

まで整理され、unresolved pair の proof-state が見えるようになった。

ただし既存資産まで重ねると、その不足はさらに鋭く、

```text
missing box
  -> missing diagnostic
  -> missing AdjacentDiagnosis
```

へ縮む。

したがって現在の local Big は、最終的に、

```text
canonical half-window capacity
+
undiagnosed internal adjacent pairs
+
one finite-window boundary
```

という形じゃ。

次の本丸は排中律による `Box ∨ ¬Box` ではない。
**各 adjacent pair に lower-level diagnosis を与える構造、または診断を阻む具体的な正 obstruction を取り出すこと**じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean
index c2c528c3..ff4acbfa 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean
@@ -1030,4 +1030,122 @@ theorem sourcePressurePositiveWitnesses_endpointCorrectedLocalBig_of_internalCov
       sourcePressurePositiveWitnesses_card_le_nonposPositions_add_one_add_unresolvedInternal
         (L := L) (lo := lo) (hi := hi) hsorted

+/-- The duplicated pair state has exactly the forward-box payload. -/
+theorem sourcePressureForwardPairComparisonState_iff_forwardBoxComparisonState
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r} :
+    SourcePressureForwardPairComparisonState L W W' ↔
+      SourcePressureForwardBoxComparisonState L W W' := by
+  constructor
+  · exact SourcePressureForwardPairComparisonState.forward
+  · intro h
+    exact h.to_pairComparisonState
+
+/-- Under sortedness, an oriented box is precisely a forward box comparison. -/
+theorem sourcePressureForwardBoxComparisonState_iff_orientedNeighborBox_of_sorted
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (_hpair : SourcePressureLocalIslandWitnessAdjacentPairInList L W W') :
+    SourcePressureForwardBoxComparisonState L W W' ↔
+      SourcePressureOrientedNeighborBoxState L W W' := by
+  constructor
+  · exact SourcePressureForwardBoxComparisonState.box
+  · intro hbox
+    exact hbox.to_forwardComparisonState_of_sorted hsorted
+
+/-- Canonical finite-window packing is the oriented box plus window bounds. -/
+theorem sourcePressureCanonicalFiniteWindowPackingState_iff_orientedNeighborBox_of_sorted
+    {n : OddNat} {k r lo hi : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (hlo : lo ≤ r + W.val) (hhi : r + W'.val ≤ hi) :
+    SourcePressureCanonicalFiniteWindowPackingState L lo hi W W' ↔
+      SourcePressureOrientedNeighborBoxState L W W' := by
+  constructor
+  · intro h
+    have hFPC : SourcePressureForwardPairComparisonState L W W' :=
+      h.finiteWindow.localPacking.forward
+    exact hFPC.forward.box
+  · intro hbox
+    exact (hbox.to_forwardComparisonState_of_sorted hsorted).to_pairComparisonState
+      |>.to_canonicalFiniteWindowPackingState hlo hhi
+
+/-- Exact obstruction for an internal pair missing its oriented box. -/
+def SourcePressureInternalPairBoxObstruction
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (W W' : SourcePressureLocalIslandWitness n k r) : Prop :=
+  ¬ SourcePressureOrientedNeighborDiagnosticState L W W' ∨
+    ¬ SourcePressureBeamCenteredLocalPulseBox n k r L W ∨
+      ¬ SourcePressureBeamCenteredLocalPulseBox n k r L W'
+
+theorem not_orientedNeighborBox_iff_internalPairBoxObstruction
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r} :
+    ¬ SourcePressureOrientedNeighborBoxState L W W' ↔
+      SourcePressureInternalPairBoxObstruction L W W' := by
+  constructor
+  · intro h
+    by_cases hD : SourcePressureOrientedNeighborDiagnosticState L W W'
+    · by_cases hL : SourcePressureBeamCenteredLocalPulseBox n k r L W
+      · by_cases hR : SourcePressureBeamCenteredLocalPulseBox n k r L W'
+        · exact False.elim (h ⟨hD, hL, hR⟩)
+        · exact Or.inr (Or.inr hR)
+      · exact Or.inr (Or.inl hL)
+    · exact Or.inl hD
+  · intro h hbox
+    rcases hbox with ⟨hD, hL, hR⟩
+    rcases h with hD' | hL' | hR'
+    · exact hD' hD
+    · exact hL' hL
+    · exact hR' hR
+
+theorem sourcePressureUnresolvedInternalPairFamily_mem_obstruction
+    {n : OddNat} {k r lo hi : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {P : SourcePressureLocalIslandWitness n k r ×
+      SourcePressureLocalIslandWitness n k r}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (hP : P ∈ sourcePressureUnresolvedInternalPairFamily L lo hi) :
+    SourcePressureInternalPairBoxObstruction L P.1 P.2 := by
+  apply not_orientedNeighborBox_iff_internalPairBoxObstruction.1
+  intro hbox
+  have hleft : lo ≤ r + P.1.val :=
+    (mem_sourcePressureUnresolvedInternalPairFamily.1 hP).2.1
+  have hright : r + P.2.val ≤ hi :=
+    (mem_sourcePressureUnresolvedInternalPairFamily.1 hP).2.2.1
+  exact (mem_sourcePressureUnresolvedInternalPairFamily.1 hP).2.2.2
+    ((sourcePressureCanonicalFiniteWindowPackingState_iff_orientedNeighborBox_of_sorted
+      hsorted hleft hright).2 hbox)
+
+/-- Sorted internal unresolved pairs are exactly the pairs missing the box. -/
+theorem mem_sourcePressureUnresolvedInternalPairFamily_iff_not_orientedNeighborBox
+    {n : OddNat} {k r lo hi : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {P : SourcePressureLocalIslandWitness n k r ×
+      SourcePressureLocalIslandWitness n k r}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
+    P ∈ sourcePressureUnresolvedInternalPairFamily L lo hi ↔
+      P ∈ L.zip L.tail ∧ lo ≤ r + P.1.val ∧ r + P.2.val ≤ hi ∧
+        ¬ SourcePressureOrientedNeighborBoxState L P.1 P.2 := by
+  constructor
+  · intro hP
+    rcases mem_sourcePressureUnresolvedInternalPairFamily.1 hP with
+      ⟨hzip, hlo, hhi, hnot⟩
+    refine ⟨hzip, hlo, hhi, ?_⟩
+    intro hbox
+    exact hnot ((sourcePressureCanonicalFiniteWindowPackingState_iff_orientedNeighborBox_of_sorted
+      hsorted hlo hhi).2 hbox)
+  · rintro ⟨hzip, hlo, hhi, hnotbox⟩
+    apply mem_sourcePressureUnresolvedInternalPairFamily.2
+    refine ⟨hzip, hlo, hhi, ?_⟩
+    intro hcanon
+    exact hnotbox ((sourcePressureCanonicalFiniteWindowPackingState_iff_orientedNeighborBox_of_sorted
+      hsorted hlo hhi).1 hcanon)
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-295.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-295.md
new file mode 100644
index 00000000..74092f7a
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-295.md
@@ -0,0 +1,77 @@
+# Petal implementation report cp-295
+
+## State simplification
+
+Added the equivalence between the duplicated
+`SourcePressureForwardPairComparisonState` and its underlying
+`SourcePressureForwardBoxComparisonState`.
+
+Under sorted adjacency, the forward box state is equivalent to the oriented
+neighbor box state.  With explicit internal window bounds, the canonical
+finite-window packing state is also equivalent to the oriented neighbor box.
+
+This makes the canonical construction readable as:
+
+```text
+internal bounds + sorted adjacency + oriented neighbor box
+  <-> canonical packing state
+```
+
+## Exact unresolved-pair obstruction
+
+Added `SourcePressureInternalPairBoxObstruction`:
+
+```text
+missing oriented diagnostic
+or missing left pulse box
+or missing right pulse box
+```
+
+Its negated-box equivalence is proved.  Every unresolved internal pair carries
+this obstruction, and the unresolved pair Finset has a direct membership
+equivalence in terms of `¬ SourcePressureOrientedNeighborBoxState`.
+
+Therefore the remaining unresolved count is not an opaque numerical gap. It is
+exactly the count of internal adjacent pairs for which at least one local box
+component has not been constructed.
+
+## Producer audit
+
+The existing BeamSeed / SortedFailure / FailureResolution hierarchy constructs
+an existential forward pair and can therefore eliminate the obstruction for
+that selected pair. It does not yet eliminate the obstruction for every
+internal adjacent pair in an arbitrary list. The missing producer theorem is a
+per-pair construction of `SourcePressureOrientedNeighborBoxState`.
+
+## Existing local-Big result
+
+The strongest current decomposition remains:
+
+```text
+positiveWitnesses.card
+  <= (hi - lo) / 2 + 2 + unresolvedInternalPairFamily.card
+
+positiveWitnesses.card
+  <= nonposPositions.card + 1 + unresolvedInternalPairFamily.card
+```
+
+Under internal coverage, the unresolved family is empty and the endpoint-
+corrected bounds follow.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking
+```
+
+The new code contains no `sorry` or `axiom`. One existing style warning notes
+a line longer than 100 characters; it does not affect the build.
+
+## Next target
+
+Add a per-pair producer theorem, preferably a disjunction of the oriented box
+state and the explicit `SourcePressureInternalPairBoxObstruction`. This is the
+next point at which the unresolved correction can be reduced rather than merely
+counted.
````
`````
