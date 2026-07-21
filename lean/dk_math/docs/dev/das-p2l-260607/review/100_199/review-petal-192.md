# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition

gch: d9d45b8d379bac53a7e5df23ae8b5e7db89a2058

## Report

cp191 完了です。

`PressureDiagnosticDecomposition.lean` に、五要素限定の fully bounded pair-normalization を追加しました。

- `three_pairDiagnostic_cases`
- `four_pairDiagnostic_cases`
- `five_pairDiagnostic_cases`
- `five_iff_pairDiagnostic_cases`
- `sourcePressureLocalIslandWitnessList_failure_five_pairDiagnostic_cases_of_noAdjacentOverlap`

`five_iff_pairDiagnostic_cases` まで no-sorry で閉じています。逆向きは tail lift の合成ではなく、各 adjacent pair の bounded address を直接組む形にして、固定五要素の主張であることを明確にしました。

レポートも作成済みです。

- `lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-191.md`

検証はすべて通過しました。

- 指定された 6 build: pass
- 対象4ファイルの `sorry` 検索: ヒットなし
- `git diff --check`: pass

今回も任意長分解、aggregation、union accounting、coverage、canonical first diagnosis、Collatz convergence は追加していません。既知の unrelated warning として `ZsigmondyCyclotomicResearch.lean` の既存 `sorry` 警告だけ出ています。

## Review

## 結論

うむ、Checkpoint 191 は **採用** じゃ 👍️
五要素 list に対する fully bounded pair-normalization が入り、固定長の範囲ではかなり使いやすくなった。

追加された中心は、

```lean id="8oykgy"
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_pairDiagnostic_cases
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_pairDiagnostic_cases
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.five_pairDiagnostic_cases
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.five_iff_pairDiagnostic_cases
sourcePressureLocalIslandWitnessList_failure_five_pairDiagnostic_cases_of_noAdjacentOverlap
```

じゃな。五要素限定で、

```text id="oc5exq"
Diagnostic [W1,W2,W3,W4,W5]
  -> PairDiagnostic W1 W2
     or PairDiagnostic W2 W3
     or PairDiagnostic W3 W4
     or PairDiagnostic W4 W5
```

まで開けるようになった。任意長分解、aggregation、union accounting、coverage、canonical first diagnosis、Collatz convergence は追加していない。境界管理は良い。

## 実装レビュー

## 1. three / four helper を先に作ったのが良い

```lean id="j07kwa"
three_pairDiagnostic_cases
four_pairDiagnostic_cases
```

を作ってから `five_pairDiagnostic_cases` に進んでいるので、証明の流れが素直じゃ。

これは今後、別の固定長 theorem を作るときにも使える。

```text id="hd7bkw"
five -> four -> three -> two
```

という bounded decomposition chain が明確になった。

## 2. five-to-pairs theorem は実用性が高い

`five_head_or_tail` は一段分解だった。

```text id="ai4mq8"
head pair
or
tail diagnostic
```

今回の `five_pairDiagnostic_cases` は tail を最後まで開いて、

```text id="ad5eu7"
どの隣接 pair が recovered pair diagnostic か
```

まで返す。

これは downstream consumer にかなり使いやすい。
特に、固定サイズの局所窓で「回収可能な adjacent pair が必ずある」と言いたい場合にそのまま使える。

## 3. `five_iff_pairDiagnostic_cases` まで閉じたのは良い

forward だけでなく iff まであるのは強い。

reverse direction で tail lift 合成に頼らず、各 adjacent pair の bounded address を直接組んだのも良い判断じゃ。

```lean id="7122xp"
head
tail head
tail tail head
tail tail tail head
```

という固定五要素の住所が明示されているので、「これは arbitrary list の探索ではない」という境界が Lean コード上でも見える。

## 4. consumer theorem も自然

```lean id="um36v8"
sourcePressureLocalIslandWitnessList_failure_five_pairDiagnostic_cases_of_noAdjacentOverlap
```

により、

```text id="yq4iaj"
failure [W1,W2,W3,W4,W5]
noAdjacentOverlap [W1,W2,W3,W4,W5]
  -> four adjacent pair diagnostics のどれか
```

が得られた。

これはここまでの構築の一つの使いやすい到達点じゃ。

## 数学的意味

今回で、固定五要素窓においては、

```text id="au0f6i"
failure + noAdjacentOverlap
  -> diagnostic
  -> adjacent pair diagnostic cases
```

まで閉じた。

DkMath 的には、

```text id="v37qx9"
五要素の局所窓に sorted-before failure があり、
overlap obstruction がないなら、
その窓内のどこかの隣接二項が
pair-local recovered budget を持つ。
```

と読める。

これは収束方向の構築としてかなり良い。
まだ大域収束ではないが、「局所 failure を二項の負会計へ落とす」という機構が、固定窓ではかなり明示的になってきた。

## 注意点

## 1. まだ任意長 theorem ではない

今回の theorem は五要素限定じゃ。

まだ次は言っていない。

```text id="d9xebc"
任意 list に diagnostic があれば pairDiagnostic のどれか
任意 list で最初の pairDiagnostic を選ぶ
全 pairDiagnostic を列挙する
```

ここは別設計が必要じゃ。

## 2. “finite disjunction” は固定五要素限定

report にもある通り、これは「この固定窓の有限分岐」であって、一般的な diagnostic enumeration ではない。

この区別は引き続き大事じゃ。

## 3. 次は対称性を揃えると良い

今は五要素の iff と consumer theorem が強い。
一方で、three / four については forward の pair cases はあるが、完全な iff / failure consumer pair-cases を揃える余地がある。

この API の穴を埋めると、bounded layer がきれいに整う。

## 次の checkpoint 方針

次は **three / four の pair-cases API を five と同じ粒度に揃える** のが良い。

つまり、

```lean id="0is7jh"
three_iff_pairDiagnostic_cases
four_iff_pairDiagnostic_cases
sourcePressureLocalIslandWitnessList_failure_three_pairDiagnostic_cases_of_noAdjacentOverlap
sourcePressureLocalIslandWitnessList_failure_four_pairDiagnostic_cases_of_noAdjacentOverlap
```

を追加する。

これは新しい数学的主張というより、cp191 で作った five API の対称補完じゃ。
任意長にはまだ行かない。

## 次の Codex 指示

```text id="7dd1bf"
Checkpoint 192: API completion only — three/four pair-cases iff and consumer wrappers.

Scope:
Work in the refactored bounded diagnostic decomposition module.

Primary target file:
- DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean

Do not modify unless absolutely necessary:
- DkMath/Collatz/PetalBridge.lean
- DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean

Do not modify:
- PressureAccounting.lean
- PressureLocalWitnessObstruction.lean
- PressureFrontier.lean
- OneCycle.lean
- ValuationFlowBridge.lean
- ABC files
- NumberTheory files

Context:
Checkpoint 191 added:
- three_pairDiagnostic_cases
- four_pairDiagnostic_cases
- five_pairDiagnostic_cases
- five_iff_pairDiagnostic_cases
- sourcePressureLocalIslandWitnessList_failure_five_pairDiagnostic_cases_of_noAdjacentOverlap

The five-element API now has an iff and a failure/noAdjacentOverlap consumer
wrapper for the fully opened finite pair cases.  The three/four APIs have
forward pair-cases helpers, but not yet matching iff and fully opened consumer
wrappers.

Main goal:
Complete the bounded pair-cases API for length three and length four so it
matches the length-five surface.

Part A: three-element iff pair-cases theorem.

Prove:

  theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_iff_pairDiagnostic_cases
      {n : OddNat} {k r : Nat}
      {W1 W2 W3 : SourcePressureLocalIslandWitness n k r} :
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
        [W1, W2, W3] ↔
      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W1 W2 ∨
        SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W2 W3

Suggested proof:
- forward:
  use `three_pairDiagnostic_cases`.
- reverse:
  case `W1 W2`: build with
    `SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair`
    and `SourcePressureLocalIslandWitnessAdjacentPairInList.head`.
  case `W2 W3`: build with
    `SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair`
    and
    `SourcePressureLocalIslandWitnessAdjacentPairInList.tail
      SourcePressureLocalIslandWitnessAdjacentPairInList.head`.

Alternatively use `of_pairDiagnostic_two` and `of_tail`, but direct bounded
addresses are also acceptable.

Part B: four-element iff pair-cases theorem.

Prove:

  theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_iff_pairDiagnostic_cases
      {n : OddNat} {k r : Nat}
      {W1 W2 W3 W4 : SourcePressureLocalIslandWitness n k r} :
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
        [W1, W2, W3, W4] ↔
      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W1 W2 ∨
      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W2 W3 ∨
      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W3 W4

Suggested proof:
- forward:
  use `four_pairDiagnostic_cases`.
- reverse:
  build directly from the selected bounded address:
  - `W1,W2`: head
  - `W2,W3`: tail head
  - `W3,W4`: tail tail head
- Keep disjunction right-associated as written.

Part C: failure + noAdjacentOverlap consumer wrapper for length three.

Prove:

  theorem sourcePressureLocalIslandWitnessList_failure_three_pairDiagnostic_cases_of_noAdjacentOverlap
      {n : OddNat} {k r : Nat}
      {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
      (h :
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2, W3])
      (hno :
        SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction [W1, W2, W3]) :
      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W1 W2 ∨
        SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W2 W3

Suggested proof:
- obtain diagnostic via
  sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
- apply `.three_pairDiagnostic_cases`.

Part D: failure + noAdjacentOverlap consumer wrapper for length four.

Prove:

  theorem sourcePressureLocalIslandWitnessList_failure_four_pairDiagnostic_cases_of_noAdjacentOverlap
      {n : OddNat} {k r : Nat}
      {W1 W2 W3 W4 : SourcePressureLocalIslandWitness n k r}
      (h :
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2, W3, W4])
      (hno :
        SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction [W1, W2, W3, W4]) :
      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W1 W2 ∨
      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W2 W3 ∨
      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W3 W4

Suggested proof:
- obtain diagnostic via
  sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
- apply `.four_pairDiagnostic_cases`.

Part E: optional two-element consumer alias.

If useful, add an alias matching naming style:

  theorem sourcePressureLocalIslandWitnessList_failure_two_pairDiagnostic_cases_of_noAdjacentOverlap
      ...
      : SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W1 W2

This can simply call the existing:
  sourcePressureLocalIslandWitnessList_failure_two_pairDiagnostic_of_noAdjacentOverlap

Do not force if it feels redundant.

Part F: do not introduce new mathematical strength.

Do not add:
- length-six decomposition;
- arbitrary-list decomposition;
- arbitrary-list recursion;
- aggregation over multiple recovered diagnostics;
- list-wide interval union accounting;
- coverage;
- maximality;
- uniqueness for arbitrary lists;
- sorting theorems;
- canonical first diagnosis for arbitrary lists;
- diagnostic enumeration beyond fixed finite disjunctions;
- overlap repair;
- disjointness between multiple recovered families;
- Collatz convergence.

This checkpoint is only API completion for fixed length three/four pair cases.

Part G: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-192.md

Include:
- three_iff_pairDiagnostic_cases;
- four_iff_pairDiagnostic_cases;
- failure + noAdjacentOverlap three/four consumer wrappers;
- optional two alias if added;
- explicit note that this only completes the bounded fixed-length API;
- explicit note that no length-six, arbitrary-list decomposition, aggregation,
  union accounting, coverage, maximality, uniqueness for arbitrary lists,
  sorting, canonical first diagnosis for arbitrary lists, enumeration beyond
  fixed finite disjunctions, overlap repair, or Collatz convergence was
  introduced;
- verification results.

Verification:

  lake build DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
  lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
  lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
  lake build DkMath.Collatz.PetalBridge.PressureAccounting
  lake build DkMath.Collatz.PetalBridge.PressureFrontier
  lake build DkMath.Collatz.PetalBridge

Run no-sorry checks:

  rg -n "\\bsorry\\b" \
    DkMath/Collatz/PetalBridge/PressureAccounting.lean \
    DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
    DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean \
    DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean

Also run:

  git diff --check
```

## 総評

cp191 は良い到達点じゃ。

五要素固定窓では、

```text id="sd6big"
failure + noAdjacentOverlap
  -> どれかの隣接 pair が pairDiagnostic
```

まで直接読めるようになった。

次は three / four の API 粒度を揃える。
そのあとで初めて、任意長へ進むべきか、あるいは固定窓 consumer を作るべきかを選べばよい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
index f232f711..886d6195 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
@@ -352,6 +352,32 @@ theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyD
   exact
     SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_iff_head_or_tail

+set_option linter.style.longLine false in
+/--
+Fully bounded pair-case normalization for a three-element diagnostic.
+
+This expands the one-step head-or-tail form into the fixed finite disjunction
+of adjacent pair diagnostics for `[W1, W2, W3]`.  It is not an arbitrary-list
+classifier.
+-/
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_pairDiagnostic_cases
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
+    (h :
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+        [W1, W2, W3]) :
+    SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+      W1 W2 ∨
+      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+        W2 W3 := by
+  rcases
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_iff_pairDiagnostic_or_tail.mp
+        h with hhead | htail
+  · exact Or.inl hhead
+  · exact Or.inr
+      (SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.two_iff_pairDiagnostic.mp
+        htail)
+
 set_option linter.style.longLine false in
 /--
 Four-element bounded decomposition for the bundled diagnostic carrier.
@@ -452,6 +478,36 @@ theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyD
   exact
     SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_iff_head_or_tail

+set_option linter.style.longLine false in
+/--
+Fully bounded pair-case normalization for a four-element diagnostic.
+
+This expands the one-step head-or-tail form into the fixed finite disjunction
+of adjacent pair diagnostics for `[W1, W2, W3, W4]`.  It is not an
+arbitrary-list classifier.
+-/
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_pairDiagnostic_cases
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 W4 : SourcePressureLocalIslandWitness n k r}
+    (h :
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+        [W1, W2, W3, W4]) :
+    SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+      W1 W2 ∨
+      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+        W2 W3 ∨
+      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+        W3 W4 := by
+  rcases
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_iff_pairDiagnostic_or_tail.mp
+        h with hhead | htail
+  · exact Or.inl hhead
+  · rcases
+        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_pairDiagnostic_cases
+          htail with h23 | h34
+    · exact Or.inr (Or.inl h23)
+    · exact Or.inr (Or.inr h34)
+
 set_option linter.style.longLine false in
 /--
 Five-element bounded decomposition for the bundled diagnostic carrier.
@@ -514,6 +570,97 @@ theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyD
         SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail
           htail

+set_option linter.style.longLine false in
+/--
+Fully bounded pair-case normalization for a five-element diagnostic.
+
+This expands the one-step head-or-tail form into the fixed finite disjunction
+of adjacent pair diagnostics for `[W1, W2, W3, W4, W5]`.  It is only a
+five-element theorem and does not introduce arbitrary-list decomposition or a
+canonical first diagnostic.
+-/
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.five_pairDiagnostic_cases
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 W4 W5 : SourcePressureLocalIslandWitness n k r}
+    (h :
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+        [W1, W2, W3, W4, W5]) :
+    SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+      W1 W2 ∨
+      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+        W2 W3 ∨
+      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+        W3 W4 ∨
+      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+        W4 W5 := by
+  rcases
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.five_iff_pairDiagnostic_or_tail.mp
+        h with hhead | htail
+  · exact Or.inl hhead
+  · rcases
+        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_pairDiagnostic_cases
+          htail with h23 | htailCases
+    · exact Or.inr (Or.inl h23)
+    · rcases htailCases with h34 | h45
+      · exact Or.inr (Or.inr (Or.inl h34))
+      · exact Or.inr (Or.inr (Or.inr h45))
+
+set_option linter.style.longLine false in
+/--
+Iff form of the fully bounded five-to-pairs normalization.
+
+The reverse direction builds a diagnostic from exactly one adjacent-pair
+branch by giving the corresponding bounded adjacent-pair address.  This is a
+fixed finite disjunction only; it does not choose or enumerate diagnostics in
+arbitrary lists.
+-/
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.five_iff_pairDiagnostic_cases
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 W4 W5 : SourcePressureLocalIslandWitness n k r} :
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+      [W1, W2, W3, W4, W5] ↔
+    SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+      W1 W2 ∨
+      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+        W2 W3 ∨
+      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+        W3 W4 ∨
+      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+        W4 W5 := by
+  constructor
+  · exact
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.five_pairDiagnostic_cases
+  · intro h
+    rcases h with h12 | htail
+    · rcases h12 with ⟨hrev, hbudget, hneg, hlen⟩
+      exact
+        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
+          SourcePressureLocalIslandWitnessAdjacentPairInList.head
+          hrev hbudget hneg hlen
+    · rcases htail with h23 | htail
+      · rcases h23 with ⟨hrev, hbudget, hneg, hlen⟩
+        exact
+          SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
+            (SourcePressureLocalIslandWitnessAdjacentPairInList.tail
+              SourcePressureLocalIslandWitnessAdjacentPairInList.head)
+            hrev hbudget hneg hlen
+      · rcases htail with h34 | h45
+        · rcases h34 with ⟨hrev, hbudget, hneg, hlen⟩
+          exact
+            SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
+              (SourcePressureLocalIslandWitnessAdjacentPairInList.tail
+                (SourcePressureLocalIslandWitnessAdjacentPairInList.tail
+                  SourcePressureLocalIslandWitnessAdjacentPairInList.head))
+              hrev hbudget hneg hlen
+        · rcases h45 with ⟨hrev, hbudget, hneg, hlen⟩
+          exact
+            SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
+              (SourcePressureLocalIslandWitnessAdjacentPairInList.tail
+                (SourcePressureLocalIslandWitnessAdjacentPairInList.tail
+                  (SourcePressureLocalIslandWitnessAdjacentPairInList.tail
+                    SourcePressureLocalIslandWitnessAdjacentPairInList.head)))
+              hrev hbudget hneg hlen
+
 set_option linter.style.longLine false in
 /--
 Two-element consumer form: failure plus named no-adjacent-overlap yields the
@@ -699,4 +846,34 @@ theorem
   (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
     h hno).five_head_or_tail

+set_option linter.style.longLine false in
+/--
+Five-element consumer form normalized all the way to the fixed finite
+disjunction of adjacent pair diagnostics.
+
+The theorem is bounded to `[W1, W2, W3, W4, W5]`.  It does not aggregate the
+branches, compute a list of all diagnostics, or choose a canonical diagnosis in
+an arbitrary list.
+-/
+theorem
+    sourcePressureLocalIslandWitnessList_failure_five_pairDiagnostic_cases_of_noAdjacentOverlap
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 W4 W5 : SourcePressureLocalIslandWitness n k r}
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+        [W1, W2, W3, W4, W5])
+    (hno :
+      SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
+        [W1, W2, W3, W4, W5]) :
+    SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+      W1 W2 ∨
+      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+        W2 W3 ∨
+      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+        W3 W4 ∨
+      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+        W4 W5 :=
+  (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
+    h hno).five_pairDiagnostic_cases
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-191.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-191.md
new file mode 100644
index 00000000..5cc22129
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-191.md
@@ -0,0 +1,182 @@
+# Report Petal 191
+
+## Checkpoint
+
+Checkpoint 191 normalized the explicit five-witness diagnostic into a fixed
+finite disjunction of adjacent pair diagnostics.
+
+Primary file:
+
+- `DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean`
+
+No other Lean source file was changed.
+
+## Implemented
+
+### Optional three/four pair-cases wrappers
+
+Added:
+
+```lean
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_pairDiagnostic_cases
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_pairDiagnostic_cases
+```
+
+These are bounded helper normalizations:
+
+```text
+Diagnostic [W1, W2, W3]
+  -> PairDiagnostic W1 W2 or PairDiagnostic W2 W3
+
+Diagnostic [W1, W2, W3, W4]
+  -> PairDiagnostic W1 W2 or PairDiagnostic W2 W3 or PairDiagnostic W3 W4
+```
+
+They are fixed-list wrappers only.  They do not classify arbitrary lists.
+
+### Five-to-pairs theorem
+
+Added:
+
+```lean
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.five_pairDiagnostic_cases
+```
+
+This expands:
+
+```text
+Diagnostic [W1, W2, W3, W4, W5]
+```
+
+into the right-associated finite disjunction:
+
+```text
+PairDiagnostic W1 W2
+or PairDiagnostic W2 W3
+or PairDiagnostic W3 W4
+or PairDiagnostic W4 W5
+```
+
+The proof uses the one-step five head-or-tail theorem from checkpoint 190, then
+the four/three/two bounded normalizations.
+
+### Five iff theorem
+
+Added:
+
+```lean
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.five_iff_pairDiagnostic_cases
+```
+
+This gives the iff form for the fixed five-element list.
+
+The reverse direction builds the diagnostic directly from the selected bounded
+adjacent-pair address:
+
+- `W1,W2`: head address;
+- `W2,W3`: one tail step then head;
+- `W3,W4`: two tail steps then head;
+- `W4,W5`: three tail steps then head.
+
+This avoided noisy tail-lift bookkeeping and kept the construction explicitly
+bounded.
+
+### Failure + noAdjacentOverlap consumer theorem
+
+Added:
+
+```lean
+theorem sourcePressureLocalIslandWitnessList_failure_five_pairDiagnostic_cases_of_noAdjacentOverlap
+```
+
+This composes the existing failure plus no-adjacent-overlap diagnostic theorem
+with `five_pairDiagnostic_cases`.
+
+## Guardrails
+
+This checkpoint is only a fixed five-element finite disjunction.
+
+It did not introduce:
+
+- arbitrary-list decomposition;
+- arbitrary-list recursion;
+- aggregation over multiple recovered diagnostics;
+- list-wide interval union accounting;
+- coverage;
+- maximality;
+- uniqueness for arbitrary lists;
+- sorting theorems;
+- canonical first diagnosis for arbitrary lists;
+- diagnostic enumeration beyond this fixed finite disjunction;
+- overlap repair;
+- disjointness between multiple recovered families;
+- Collatz convergence.
+
+Recovered budgets remain pair-local.  The theorem only says that, if the
+five-element list has a recovered adjacent accounted-family diagnostic, then
+one of the four explicit adjacent pairs carries the named pair-local diagnostic.
+
+## File Size Watch
+
+Current line counts:
+
+```text
+   879 lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
+  1356 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+  1391 lean/dk_math/DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
+  1896 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+  5522 total
+```
+
+`PressureDiagnosticDecomposition.lean` remains below the 2,000-line split
+threshold.  No refactor was needed in this checkpoint.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
+lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
+lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
+lake build DkMath.Collatz.PetalBridge.PressureAccounting
+lake build DkMath.Collatz.PetalBridge.PressureFrontier
+lake build DkMath.Collatz.PetalBridge
+git diff --check
+```
+
+No-sorry check over the requested pressure files produced no matches:
+
+```text
+rg -n "\bsorry\b" \
+  DkMath/Collatz/PetalBridge/PressureAccounting.lean \
+  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
+  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean \
+  DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
+```
+
+Known unrelated warning still appears during builds:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
+
+That warning is outside this checkpoint and was not modified.
+
+## Next Inference
+
+The bounded diagnostic layer now has two views for five elements:
+
+```text
+one-step view:
+  head pair or tail diagnostic
+
+fully opened view:
+  one of the four adjacent pair diagnostics
+```
+
+This is enough for fixed-size consumers that need a concrete adjacent pair
+without introducing arbitrary-list machinery.  A future general theorem should
+remain a separate design checkpoint because it would need a precise policy for
+list recursion, canonical choice, and non-overclaiming.
````
`````
