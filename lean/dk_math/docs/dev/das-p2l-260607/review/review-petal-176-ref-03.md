# Git diff / Report / Review

## Upd: refact: docs: Collatz-Overview.md, etc

gch: 87f2c37040d993ae4f5b4743b8354275174c622c

## Report

Docs 同期を完了しました。今回の `176-ref-02` は Markdown 更新のみです。

更新内容:

- [Collatz-Overview.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-Overview.md)
- [Collatz-Package-Structure.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-Package-Structure.md)
- [Collatz-PetalBridge-Guide.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md)
- [Collatz-PetalBridge-Status.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md)
- [report-petal-176-ref-02.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-176-ref-02.md)

反映した主な内容は、`DkMath.Collatz.PetalBridge` が現在は aggregator であり、`PressureAccounting` / `PressureLocalWitnessObstruction` / `PressureAdjacentDiagnosis` へ責務分割されたことです。あわせて、global coverage・arbitrary sorting・union accounting・Collatz convergence を主張していない点も明記しました。

検証:

```bash
git diff --check
```

pass です。Markdown のみなので Lean build は実行していません。

## Review

## 結論

うむ、リファクタ完了確認。次は **通常の定理開発に戻ってよい** 状態じゃ。

`PressureAccounting` は 2000 行未満に落ち、`PressureLocalWitnessObstruction` と `PressureAdjacentDiagnosis` に分割され、公開 `DkMath.Collatz.PetalBridge` aggregator も安定している。
さらに docs 側も split 後の package structure に同期済みで、非主張事項も package level に記録されている。

次の一手は、固定長 wrapper をさらに増やすより、ここまで整えた carrier を使って **明示 list の failure から adjacent diagnosis を得る弱い一般定理** に進むのが良い。

## 次の実装方針

狙う theorem はこれじゃ。

```lean id="wkagp5"
sourcePressureLocalIslandWitnessList_failure_hasAdjacentDiagnosis
```

意味は、

```text id="i2jonl"
explicit witness list に sorted-before failure がある
  -> その list のどこかの adjacent pair に diagnosis がある
```

これは global coverage ではない。
Collatz 収束でもない。
任意の local island を列挙する theorem でもない。

あくまで、**すでに与えられた明示 witness list の failure predicate を構文的に剥がして、隣接 pair diagnosis へ落とす** 定理じゃ。

ポイントは、既存の

```lean id="u4rddd"
sourcePressureLocalIslandWitnessList_failure_oneStepDiagnosis
SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_head
SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail
```

を使って、list induction するだけ、というところじゃな。

## 次の Codex 指示

```text id="vyzmz2"
Checkpoint 177: Main root only — explicit-list failure implies list-level adjacent diagnosis.

Scope:
Focus on the refactored Collatz/PetalBridge pressure modules.

Primary target file:
- DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean

Allowed supporting file, only if needed:
- DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean

Do not modify:
- OneCycle.lean
- ValuationFlowBridge.lean
- ABC files
- NumberTheory files

Do not change public theorem names from prior checkpoints.

Context:
The refactor split the pressure surface into:

- PressureAccounting
- PressureLocalWitnessObstruction
- PressureAdjacentDiagnosis

The public aggregator `DkMath.Collatz.PetalBridge` remains stable.

Relevant existing API includes:

- SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
- SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_head
- SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail
- SourcePressureLocalIslandWitnessAdjacentDiagnosis
- SourcePressureLocalIslandWitnessAdjacentPairInList
- sourcePressureLocalIslandWitnessList_failure_oneStepDiagnosis
- sourcePressureLocalIslandWitnessList_failure_three_hasAdjacentDiagnosis
- sourcePressureLocalIslandWitnessList_failure_four_hasAdjacentDiagnosis
- sourcePressureLocalIslandWitnessList_failure_five_hasAdjacentDiagnosis

Global guardrails:
- Do not claim global local-island coverage.
- Do not claim maximality.
- Do not claim uniqueness.
- Do not claim prefix behavior.
- Do not claim arbitrary list sorting.
- Do not claim union accounting.
- Do not claim overlap repair.
- Do not claim Collatz convergence.
- Keep all statements local to explicitly supplied witness lists.
- Recovered budgets remain pair-local.
- Overlap remains an adjacent obstruction on the enclosing list.

Main goal:
Prove a weak structural theorem:

  if an explicit witness list has sorted-before failure,
  then it has a list-level adjacent diagnosis.

This is a structural induction over the explicit list and the existing failure
predicate.  It is not a sorting algorithm, not coverage, and not union
accounting.

Part A: check whether witness-address length positivity is already available.

Search for an existing theorem proving:

  0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len

for any `W : SourcePressureLocalIslandWitness n k r`.

Suggested searches:

  rg "sourcePressureIntervalPulseAddress_of_localIslandWitness.*len"
  rg "LocalIslandWitness.*len.*pos"
  rg "localIslandWitness.*len"

If such theorem exists, use it.

If no such theorem exists, try to prove a small lemma, preferably near the
definition of the local witness address if that is in the current dependency
layer:

  theorem sourcePressureIntervalPulseAddress_of_localIslandWitness_len_pos
      {n : OddNat} {k r : Nat}
      (W : SourcePressureLocalIslandWitness n k r) :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len

Expected proof may be `simp` if the local witness address has length 1.

If this lemma becomes nontrivial, do not get stuck.  Use the explicit positivity
hypothesis version in Part B instead.

Part B: prove explicit positivity version first.

In `PressureAdjacentDiagnosis.lean`, prove:

  theorem sourcePressureLocalIslandWitnessList_failure_hasAdjacentDiagnosis_of_forall_len_pos
      {n : OddNat} {k r : Nat}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      (hpos :
        ∀ W ∈ L,
          0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len)
      (h :
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L) :
      SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis L

Suggested proof:
- induction on L.
- nil case:
  use `SourcePressureLocalIslandWitnessListHasSortedBeforeFailure_nil_false`.
- singleton case:
  use `SourcePressureLocalIslandWitnessListHasSortedBeforeFailure_singleton_false`.
- cons-cons case:
  list is `W1 :: W2 :: rest`.
  derive:
    h1pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len
    h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len
  from hpos.
- apply:
    sourcePressureLocalIslandWitnessList_failure_oneStepDiagnosis h1pos h2pos h
- head branch:
  it already has the adjacent diagnosis evidence for the head pair.
  use:
    SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_head
- tail branch:
  build tail positivity:
    ∀ W ∈ (W2 :: rest), 0 < ...
  apply the induction hypothesis to the tail failure.
  then lift using:
    SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail

Important:
The theorem only produces `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis L`.
It does not enumerate all adjacent diagnoses.
It does not choose a canonical first diagnosis.
It does not sort the list.

Part C: optional no-hpos public theorem.

Only if Part A found or proved automatic witness-address length positivity,
prove the cleaner theorem:

  theorem sourcePressureLocalIslandWitnessList_failure_hasAdjacentDiagnosis
      {n : OddNat} {k r : Nat}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      (h :
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L) :
      SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis L

Suggested proof:
- apply the Part B theorem.
- supply hpos by the automatic per-witness length positivity theorem.

If automatic positivity is not available or becomes expensive, skip Part C.
The explicit-hpos theorem is acceptable for this checkpoint.

Part D: optional bounded wrappers become corollaries.

Do not delete existing length-three/four/five wrappers.

If easy, add comments or small theorem notes that the existing bounded wrappers
are special cases of the new general explicit-list theorem once hpos is supplied.

Do not rewrite existing proofs in this checkpoint unless it is trivial and keeps
the diff small.

Part E: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-177.md

Include:
- whether automatic witness-address length positivity existed or was added;
- the explicit-hpos theorem;
- the clean no-hpos theorem if added;
- proof strategy summary by list induction;
- explicit note that this is only about explicitly supplied witness lists;
- explicit note that the theorem does not assert coverage, maximality,
  uniqueness, sorting, union accounting, overlap repair, or Collatz convergence;
- verification results.

Verification:

  lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
  lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
  lake build DkMath.Collatz.PetalBridge.PressureAccounting
  lake build DkMath.Collatz.PetalBridge.PressureFrontier
  lake build DkMath.Collatz.PetalBridge

Run no-sorry checks:

  rg -n "\\bsorry\\b" \
    DkMath/Collatz/PetalBridge/PressureAccounting.lean \
    DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
    DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean

Also run:

  git diff --check
```

## 補足

もし `sourcePressureIntervalPulseAddress_of_localIslandWitness_len_pos` がすぐ通るなら、今回でかなり綺麗な theorem まで行ける。

```lean id="uwbv9h"
sourcePressureLocalIslandWitnessList_failure_hasAdjacentDiagnosis
```

これが通ると、今までの length-three / four / five wrapper は「観測用の固定長 theorem」から、「一般 theorem に向かう前の確認済みパターン」へ役割が移る。

ただし、これはまだ **Collatz 大域の証明** ではない。
あくまで、明示 list の sorted-before failure を、その list 内の adjacent diagnosis へ局所化する定理じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-Overview.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-Overview.md
index 5118810e..a1b2d041 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-Overview.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-Overview.md
@@ -105,7 +105,9 @@ height information without immediately leaving finite arithmetic.
 
 ## Observation Windows
 
-`DkMath.Collatz.PetalBridge` defines a finite observation window:
+`DkMath.Collatz.PetalBridge` is now a public aggregator over a split
+`PetalBridge/` subpackage.  The basic layer defines a finite observation
+window:
 
 ```lean
 OrbitWindow n k = Finset.range k
@@ -132,6 +134,26 @@ with:
 
 This connects the local finite profile to the existing accumulated-height API.
 
+The current implementation keeps the window language modular:
+
+```text
+Basic / Residues / Profiles / Counts
+  finite orbit labels, residues, height profiles, and occupation counts
+
+Mass / PressureCore / PressureCounts
+  retention, recovery, continuation, and pressure predicates
+
+TailSplits / TailGrammar / DriftBudget / PressureDecay
+  tail grammar and delayed budget observations
+
+PressureFrontier / PressureAccounting / PressureLocalWitnessObstruction /
+PressureAdjacentDiagnosis
+  explicit local-island witness accounting and bounded obstruction diagnosis
+```
+
+This split is refactor-only.  It does not change the theorem meanings; it
+only keeps the base accounting layer readable.
+
 ## From Counts To Distributions
 
 The file then counts how often a finite window enters a chosen residue cell:
@@ -189,6 +211,29 @@ tail occupation count.
 
 This turns pointwise residue arithmetic into count-level channel flow.
 
+## Pressure Accounting And Local Obstructions
+
+The pressure route now has a separate explicit-witness accounting surface.
+The base file:
+
+```lean
+DkMath.Collatz.PetalBridge.PressureAccounting
+```
+
+contains interval-pulse addresses, accounted intervals, sorted-before finite
+families, and singleton local-island witness wrappers.
+
+The later local obstruction files are separated:
+
+```lean
+DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
+DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
+```
+
+These layers discuss only explicitly supplied witnesses and adjacent pairs.
+They do not assert global coverage, maximality, arbitrary sorting, interval
+union accounting, or Collatz convergence.
+
 ## What This Does Not Yet Do
 
 This layer does not prove global convergence.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-Package-Structure.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-Package-Structure.md
index f3832a35..fba664e2 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-Package-Structure.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-Package-Structure.md
@@ -9,7 +9,28 @@ DkMath.Collatz.Basic
 DkMath.Collatz.V2
 DkMath.Collatz.Accelerated
 DkMath.Collatz.Shift
+DkMath.Collatz.GnomonEvaluation
 DkMath.Collatz.PetalBridge
+DkMath.Collatz.PetalBridge.Basic
+DkMath.Collatz.PetalBridge.Residues
+DkMath.Collatz.PetalBridge.Profiles
+DkMath.Collatz.PetalBridge.Counts
+DkMath.Collatz.PetalBridge.Ratios
+DkMath.Collatz.PetalBridge.Mass
+DkMath.Collatz.PetalBridge.PressureCore
+DkMath.Collatz.PetalBridge.PressureCounts
+DkMath.Collatz.PetalBridge.HeightBudget
+DkMath.Collatz.PetalBridge.TailSplits
+DkMath.Collatz.PetalBridge.TailGrammar
+DkMath.Collatz.PetalBridge.DriftBudget
+DkMath.Collatz.PetalBridge.PressureDecay
+DkMath.Collatz.PetalBridge.PressureFrontier
+DkMath.Collatz.PetalBridge.PressureAccounting
+DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
+DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
+DkMath.Collatz.PetalBridge.OneCycle
+DkMath.Collatz.PetalBridge.ValuationFlowBridge
+DkMath.Collatz.PetalBridge.Collision
 DkMath.Collatz.Collatz2K26
 ```
 
@@ -89,11 +110,43 @@ theme that later appears in `PetalBridge`:
 differences concentrate around 2-adic boundaries and singular residue ridges
 ```
 
+## `GnomonEvaluation.lean`
+
+This file contains the low-level odd gnomon reading of one accelerated Collatz
+step.
+
+Important names:
+
+```lean
+OddGnomonLayer
+RawGnomonStep
+RawGnomonHeight
+RawGnomonResidualShape
+RawGnomonRemainderAtDepth
+```
+
+Its role is to keep the arithmetic shape:
+
+```text
+n + (2n + 1) = 3n + 1
+```
+
+out of the finite observation-window package.
+
 ## `PetalBridge.lean`
 
-This is the current active bridge layer.
+This is now the public aggregator for the split PetalBridge package.
+
+It imports the finite observation, residue, pressure, accounting, obstruction,
+one-cycle, valuation-flow, and collision modules.  Users that want the full
+surface can continue importing:
 
-It packages the accelerated orbit as a Petal-style finite observation window:
+```lean
+import DkMath.Collatz.PetalBridge
+```
+
+The split package packages the accelerated orbit as a Petal-style finite
+observation window:
 
 ```lean
 OrbitWindow
@@ -121,6 +174,57 @@ pow2ChannelFlow_of_pointwise
 
 This file is where Collatz dynamics are read as finite channel movement.
 
+## `PetalBridge/` Subpackage
+
+The subpackage is organized as follows:
+
+```text
+Basic
+  orbit windows, odd labels, gnomon residual-shape bridge
+
+Residues
+  residue-class and height-detection lemmas
+
+Profiles
+  ordered finite profiles: heights, residual shapes, first-failed depths
+
+Counts / Ratios
+  finite occupation counts and ratio predicates
+
+Mass
+  retention, recovery, continuation, and shifted-tail mass definitions
+
+PressureCore / PressureCounts
+  pressure predicates and depth-mode counting surfaces
+
+HeightBudget
+  finite height-count lower bounds feeding `sumS`
+
+TailSplits / TailGrammar / DriftBudget / PressureDecay
+  delayed tail grammar and budget observations
+
+PressureFrontier
+  prefix-failure, frontier, sign-change, local-island predicates
+
+PressureAccounting
+  interval-pulse addresses, accounted intervals, sorted-before families,
+  singleton local-island witness accounting
+
+PressureLocalWitnessObstruction
+  witness-level before/overlap, pair obstruction, bounded list diagnosis
+
+PressureAdjacentDiagnosis
+  adjacent-pair diagnosis carriers and small fixed-list wrappers
+
+OneCycle / ValuationFlowBridge / Collision
+  one-cycle obstruction, valuation-flow bridge, and collision interface
+```
+
+The `PressureAccounting` split at checkpoint `176-ref-01` is refactor-only.
+It moved theorem groups into downstream modules without changing theorem
+statements.  The base file is now below 2000 lines, which keeps the core
+accounting layer maintainable.
+
 ## `Collatz2K26.lean`
 
 This is the integration file for the 2026 Collatz cartography route.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
index 043bda6f..0b6f7cb3 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
@@ -43,6 +43,39 @@ residual shape
 `PetalBridge` should not absorb that low-level vocabulary.  Its job is to
 observe finite windows of those shapes and compare finite channel masses.
 
+Checkpoint `176-ref-01` clarifies the implementation boundary further:
+`DkMath.Collatz.PetalBridge` is a public aggregator over a split subpackage.
+The split is refactor-only, but it is important for finding the right theorem
+surface.
+
+```text
+Basic / Residues / Profiles / Counts
+  finite observation windows and count surfaces
+
+Mass / PressureCore / PressureCounts
+  retention/recovery/continuation and pressure predicates
+
+TailSplits / TailGrammar / DriftBudget / PressureDecay
+  tail grammar and delayed budget surfaces
+
+PressureFrontier
+  prefix failure, frontier, sign-change, positive-block, local-island handles
+
+PressureAccounting
+  interval-pulse addresses, accounted intervals, sorted-before families,
+  singleton local-island witness wrappers
+
+PressureLocalWitnessObstruction
+  witness-level before/overlap, pair obstruction, bounded diagnosis
+
+PressureAdjacentDiagnosis
+  adjacent-pair diagnosis carriers and fixed small-list wrappers
+```
+
+When adding new pressure theorems, choose the lowest module that already owns
+the vocabulary.  In particular, do not put local-witness obstruction or
+adjacent-diagnosis facts back into `PressureAccounting`.
+
 ## Basic Objects
 
 ### `OrbitWindow`
@@ -316,6 +349,21 @@ sourcePressureSignChangeUp_of_localIsland
 These names are for reading scan output.  They do not assert maximality,
 uniqueness, unconditional prefix behavior, or a global pressure shape theorem.
 
+The later accounting modules preserve the same discipline.  Explicit local
+island witnesses can be converted to interval-pulse addresses, sorted when an
+ordered non-overlap proof is supplied, or diagnosed when adjacent sortedness
+fails.  The failure branch is deliberately local:
+
+```text
+reversed adjacent pair
+or
+adjacent overlap obstruction
+```
+
+Recovered budget remains attached to the recovered adjacent pair.  An overlap
+obstruction is not repaired by swapping and is not converted into a union
+accounting theorem without additional hypotheses.
+
 Checkpoint 131 refines the Python wording:
 
 ```text
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 4b5e6fd5..03afb89a 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -82,6 +82,35 @@ The bridge file is:
 DkMath.Collatz.PetalBridge
 ```
 
+As of checkpoint `176-ref-01`, this is a public aggregator over a split
+subpackage rather than one large implementation file.  The active modules are:
+
+```text
+DkMath.Collatz.PetalBridge.Basic
+DkMath.Collatz.PetalBridge.Residues
+DkMath.Collatz.PetalBridge.Profiles
+DkMath.Collatz.PetalBridge.Counts
+DkMath.Collatz.PetalBridge.Ratios
+DkMath.Collatz.PetalBridge.Mass
+DkMath.Collatz.PetalBridge.PressureCore
+DkMath.Collatz.PetalBridge.PressureCounts
+DkMath.Collatz.PetalBridge.HeightBudget
+DkMath.Collatz.PetalBridge.TailSplits
+DkMath.Collatz.PetalBridge.TailGrammar
+DkMath.Collatz.PetalBridge.DriftBudget
+DkMath.Collatz.PetalBridge.PressureDecay
+DkMath.Collatz.PetalBridge.PressureFrontier
+DkMath.Collatz.PetalBridge.PressureAccounting
+DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
+DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
+DkMath.Collatz.PetalBridge.OneCycle
+DkMath.Collatz.PetalBridge.ValuationFlowBridge
+DkMath.Collatz.PetalBridge.Collision
+```
+
+The refactor moved theorem groups only.  It did not change the mathematical
+meaning of the pressure accounting API.
+
 Checkpoint 125 clarifies the module boundary:
 
 ```text
@@ -305,6 +334,45 @@ ResidualAllOnesProfile
 PressureDecayProfile
 ```
 
+Checkpoint `176-ref-01` closes the first pressure-accounting refactor target.
+The formerly oversized accounting file was split into:
+
+```text
+PressureAccounting
+  interval-pulse address accounting, accounted interval families,
+  sorted-before families, singleton local-island witness budget wrappers
+
+PressureLocalWitnessObstruction
+  witness-level before/overlap, pair failure, overlap obstruction,
+  recovered-pair budget, bounded list diagnosis
+
+PressureAdjacentDiagnosis
+  adjacent-diagnosis carriers, adjacent-pair-in-list predicates,
+  bounded three/four/five witness diagnostic wrappers
+```
+
+Current line counts after the split:
+
+```text
+1896 PressureAccounting.lean
+1376 PressureLocalWitnessObstruction.lean
+ 545 PressureAdjacentDiagnosis.lean
+```
+
+The important semantic non-claims remain explicit:
+
+```text
+no global local-island coverage
+no maximality or uniqueness
+no arbitrary list sorting theorem
+no interval union accounting
+no overlap repair without extra hypotheses
+no Collatz convergence theorem
+```
+
+Recovered budgets remain pair-local.  Overlap remains an obstruction branch
+for the explicit adjacent witness list.
+
 The first theorem set is deliberately thin:
 
 ```lean
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-176-ref-02.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-176-ref-02.md
new file mode 100644
index 00000000..ce5b5ebe
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-176-ref-02.md
@@ -0,0 +1,84 @@
+# Report Petal 176-ref-02
+
+## Scope
+
+This checkpoint updated the Collatz documentation to match the refactored
+`DkMath.Collatz.PetalBridge` package structure.
+
+No Lean theorem statements were changed in this checkpoint.
+
+## Updated Documents
+
+Updated:
+
+```text
+DkMath/Collatz/docs/Collatz-Overview.md
+DkMath/Collatz/docs/Collatz-Package-Structure.md
+DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+```
+
+The updates record that `DkMath.Collatz.PetalBridge` is now a public aggregator
+over a split subpackage.
+
+## Main Synchronization Points
+
+The docs now mention the current module layout:
+
+```text
+Basic / Residues / Profiles / Counts / Ratios
+Mass / PressureCore / PressureCounts
+HeightBudget / TailSplits / TailGrammar / DriftBudget / PressureDecay
+PressureFrontier
+PressureAccounting
+PressureLocalWitnessObstruction
+PressureAdjacentDiagnosis
+OneCycle / ValuationFlowBridge / Collision
+```
+
+The docs also record the checkpoint `176-ref-01` split:
+
+```text
+PressureAccounting
+  base interval-pulse and accounted-family layer
+
+PressureLocalWitnessObstruction
+  witness-level before/overlap and bounded obstruction diagnosis
+
+PressureAdjacentDiagnosis
+  adjacent-pair diagnosis carriers and small fixed-list wrappers
+```
+
+## Guardrails Preserved In Docs
+
+The documentation now repeats the important non-claims at the package level:
+
+```text
+no global local-island coverage
+no maximality or uniqueness
+no arbitrary list sorting theorem
+no interval union accounting
+no overlap repair without extra hypotheses
+no Collatz convergence theorem
+```
+
+Recovered budgets are described as pair-local, and overlap remains an explicit
+obstruction branch for the supplied adjacent witness list.
+
+## Verification
+
+Documentation-only checkpoint.
+
+Passed:
+
+```bash
+git diff --check
+```
+
+No Lean build was required because this checkpoint changed only Markdown files.
+
+## Next Candidate
+
+Return to normal theorem development on top of the refactored package surface.
+If additional refactoring becomes necessary, split one module at a time and keep
+the public `DkMath.Collatz.PetalBridge` aggregator stable.
````
`````
