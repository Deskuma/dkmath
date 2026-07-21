# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureAccounting

gch: 9c01946ae854725e2cb387793220afa0b2416431

## Report

実装完了です。

[PressureAccounting.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean) に cp167 の 4 補題を追加しました。

- `head_or_tail`
- `cons_iff_head_or_tail`
- `sourcePressureLocalIslandWitnessList_headNotBefore_recovered_or_adjacentOverlapObstruction`
- `sourcePressureLocalIslandWitnessList_failure_oneStepDiagnosis`

レポートも追加しました: [report-petal-167.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-167.md)

検証結果:

- `lake build DkMath.Collatz.PetalBridge.PressureAccounting` PASS
- `lake build DkMath.Collatz.PetalBridge.PressureFrontier` PASS
- `lake build DkMath.Collatz.PetalBridge` PASS
- 対象 2 ファイルの `sorry` 検索: ヒットなし
- `git diff --check` PASS

既存の `DkMath.NumberTheory.ZsigmondyCyclotomicResearch` の `sorry` 警告は引き続き出ますが、今回の変更対象ではありません。

## Review

## 結論

うむ、Checkpoint 167 は **採用** じゃ 👍️
今回で、list sorted-before failure を **一段だけ head / tail に分解する API** が入った。

中心はこの 4 つじゃ。

```lean
SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.head_or_tail
SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_iff_head_or_tail
sourcePressureLocalIslandWitnessList_headNotBefore_recovered_or_adjacentOverlapObstruction
sourcePressureLocalIslandWitnessList_failure_oneStepDiagnosis
```

これで、list failure を受け取ったときに、

```text
head pair の failure
または
tail 側の failure
```

へ一段剥がせるようになった。さらに head failure なら、既存の pair-level 診断に接続して、recovered budget か adjacent overlap obstruction へ分岐できる。

## 状況分析

## 1. constructor と destructor が揃った

Checkpoint 166 では、

```text
head not-before or tail failure
  -> full list failure
```

という constructor 側が整った。

今回の Checkpoint 167 で、その逆向きが入った。

```text
full list failure
  -> head not-before or tail failure
```

つまり、failure predicate の再帰構造について、作る方向と剥がす方向が揃った。

これは大きい。
list-level diagnosis の基礎が閉じたと言える。

## 2. one-step diagnosis が入った

今回の一番の主成果は、

```lean
sourcePressureLocalIslandWitnessList_failure_oneStepDiagnosis
```

じゃ。

意味は、

```text
failure (W1 :: W2 :: rest)
  -> head branch:
       recovered reversed-pair budget
       or adjacent overlap obstruction
  -> tail branch:
       failure (W2 :: rest)
```

である。

これはまだ再帰 algorithm ではない。
しかし、再帰 algorithm の一段分の構文は完全に見えた。

## 3. tail branch はまだ保持するだけ

今回、tail failure は分類せず、そのまま返している。

これは正しい。
head branch だけを診断し、tail branch は後続に送る。

```text
head を見る
駄目なら tail に送る
```

という最小骨格ができた。

## レビュー

## 採用理由

第一に、`head_or_tail` が非常に重要じゃ。

```lean
SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.head_or_tail
```

これで full list failure を一段剥がせる。

第二に、`cons_iff_head_or_tail` が入ったことで、以後の rewrite / simp がやりやすくなる。

```lean
SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_iff_head_or_tail
```

これは保守面でも助かる。

第三に、head not-before を直接 recovered-or-adjacent obstruction へ送る theorem が入った。

```lean
sourcePressureLocalIslandWitnessList_headNotBefore_recovered_or_adjacentOverlapObstruction
```

これにより、`head_or_tail` の head branch をすぐ処理できる。

第四に、`failure_oneStepDiagnosis` が最初の list 診断面になっている。

```lean
sourcePressureLocalIslandWitnessList_failure_oneStepDiagnosis
```

これは今後の再帰処理の基礎定理じゃ。

## 注意点

## 1. まだ recursive classifier ではない

今回の theorem は一段だけ剥がす。

まだ次は言っていない。

```text
list 全体の全 failure を分類する
list を sorting する
全 recovered budget を合算する
```

ここはまだ先。

## 2. recovered budget は head pair に限る

`oneStepDiagnosis` の recovered branch は、head pair `W1, W2` の budget じゃ。

tail branch の内部で recovered budget が出ても、それは tail 内の pair に対する budget であり、full list 全体の budget ではない。

ここは次 checkpoint でも特に注意するべきじゃ。

## 3. overlap はまだ obstruction

今回も overlap branch は adjacent obstruction として記録するだけ。

まだ merge / split / union accounting へは進まない。
この境界を守れているのは良い。

## 解説

今回の到達点は、直感的にはこうじゃ。

```text
list に failure がある。
まず先頭を見る。

先頭 pair が壊れているなら、
  逆順なら recovered budget
  overlap なら adjacent obstruction

先頭が原因でないなら、
  tail に failure がある
```

これにより、failure を一段ずつ左から調べる道ができた。

いまの構造は、

```text
pair diagnosis
  -> head-pair diagnosis
  -> list one-step diagnosis
```

まで進んでいる。

PressureAccounting が、かなり「局所 failure 診断器」らしくなってきた。

## 一歩先ゆく推論

次は report の通り、**tail-cons propagation for the diagnostic surface** が安全じゃ。

ただし強くしすぎてはいけない。

危険なのは、

```text
tail 内で recovered budget がある
  -> full list の recovered budget である
```

のように読んでしまうことじゃ。

これはまだ言えない。
tail 内の recovered budget は、あくまで tail 内の隣接 pair に対するもの。

したがって次は、弱い形でよい。

```text
tail の one-step diagnosis を、
new head を付けた list の tail branch として持ち上げる
```

つまり、

```text
failure (W2 :: W3 :: rest)
  を診断する

その結果を
  W1 :: W2 :: W3 :: rest
  の tail-side diagnosis として保持する
```

という方向じゃ。

## 賢狼が試して欲しい実験補題

## 実験補題 A: tail one-step diagnosis alias

まず tail 側に対する one-step diagnosis を名前で呼びやすくする。

```lean
theorem sourcePressureLocalIslandWitnessList_tail_failure_oneStepDiagnosis
    {n : OddNat} {k r : ℕ}
    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (h3pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
    (htail :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W2 :: W3 :: rest)) :
    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W3 W2,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W2 W3 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
      ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
          (W2 :: W3 :: rest))
    ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W3 :: rest)
```

これは既存の `sourcePressureLocalIslandWitnessList_failure_oneStepDiagnosis` を `W2 W3 rest` に適用するだけじゃ。

## 実験補題 B: tail adjacent obstruction lifts to full adjacent obstruction

これは既に `SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_tail` があるので、再確認用。

```lean
theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_tailDiagnosisOverlap
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (hobs :
      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
        (W2 :: rest)) :
    SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
      (W1 :: W2 :: rest) :=
  SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_tail hobs
```

既存名で十分なら不要じゃ。

## 実験補題 C: tail one-step diagnosis lifts obstruction branch

tail one-step diagnosis の overlap branch を full list の adjacent obstruction へ持ち上げる。

```lean
theorem sourcePressureLocalIslandWitnessList_tailDiagnosis_overlap_lift
    {n : OddNat} {k r : ℕ}
    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (hobs :
      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
        (W2 :: W3 :: rest)) :
    SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
      (W1 :: W2 :: W3 :: rest) :=
  SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_tail hobs
```

これは簡単だが、読みやすい。

## 実験補題 D: tail one-step diagnosis lifts tail failure branch

tail の tail failure を、さらに full list の deeper tail failure として扱う準備。

```lean
theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.of_deeperTailFailure
    {n : OddNat} {k r : ℕ}
    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (hdeep :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W3 :: rest)) :
    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
      (W1 :: W2 :: W3 :: rest) :=
  SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_tail
    (SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_tail hdeep)
```

これは「二段 tail propagation」じゃ。
必要なら入れる程度でよい。

## 実験補題 E: weak tail diagnosis under cons

これが次 checkpoint の本命候補じゃ。

```lean
theorem sourcePressureLocalIslandWitnessList_tailFailure_oneStepDiagnosis_under_cons
    {n : OddNat} {k r : ℕ}
    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (h3pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
    (htail :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W2 :: W3 :: rest)) :
    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W3 W2,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W2 W3 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
      ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
          (W1 :: W2 :: W3 :: rest))
    ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W3 :: rest)
```

証明は tail の `oneStepDiagnosis` を使い、

```text
tail recovered:
  left-left

tail overlap:
  left-right, but obstruction を of_tail で持ち上げる

tail deeper failure:
  right
```

とすればよい。

注意点として、recovered branch は tail pair `W2, W3` の budget のままにする。
full list budget とは言わない。

## 次の Codex 指示

```text
Checkpoint 168: Main root only — weak tail-cons propagation for one-step diagnosis.

Scope:
Focus only on the main Collatz/PetalBridge root.

Allowed files:
- DkMath/Collatz/PetalBridge/PressureAccounting.lean
- DkMath/Collatz/PetalBridge/PressureFrontier.lean only if needed for imports or names

Do not modify:
- OneCycle.lean
- ValuationFlowBridge.lean
- ABC files
- NumberTheory files

unless a build/import issue forces a tiny fix.

Context:
Checkpoint 167 added one-layer list failure diagnosis:

- SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.head_or_tail
- SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_iff_head_or_tail
- sourcePressureLocalIslandWitnessList_headNotBefore_recovered_or_adjacentOverlapObstruction
- sourcePressureLocalIslandWitnessList_failure_oneStepDiagnosis

Global rules:
- Do not claim maximality.
- Do not claim uniqueness of pressure families.
- Do not claim coverage.
- Do not claim prefix behavior.
- Do not claim union accounting.
- Do not claim Collatz convergence.
- Keep all statements local to explicitly supplied witness lists.
- Reverse branch is recovered at pair level only.
- Overlap branch remains an adjacent obstruction.
- Do not merge intervals or prove union accounting in this checkpoint.
- Do not implement a full list sorting algorithm.
- Do not promote a recovered tail-pair budget into a full-list budget.

Main goal:
Add weak tail-cons propagation for the existing one-step diagnostic surface.
A diagnosis of the tail list `W2 :: W3 :: rest` can be viewed under a new head
`W1`, but recovered budgets remain budgets for the tail head pair only.

Part A: tail one-step diagnosis alias.

Prove:

  theorem sourcePressureLocalIslandWitnessList_tail_failure_oneStepDiagnosis
      {n : OddNat} {k r : Nat}
      {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
      {rest : List (SourcePressureLocalIslandWitness n k r)}
      (h2pos :
        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
      (h3pos :
        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
      (htail :
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
          (W2 :: W3 :: rest)) :
      ((∃ hrev : SourcePressureLocalIslandWitnessBefore W3 W2,
        (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
          W2 W3 hrev).items).map
          (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
        ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
            (W2 :: W3 :: rest))
      ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
          (W3 :: rest)

Suggested proof:
- exact sourcePressureLocalIslandWitnessList_failure_oneStepDiagnosis
    h2pos h3pos htail

Part B: tail overlap branch lifts through a new head.

Prove:

  theorem sourcePressureLocalIslandWitnessList_tailDiagnosis_overlap_lift
      {n : OddNat} {k r : Nat}
      {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
      {rest : List (SourcePressureLocalIslandWitness n k r)}
      (hobs :
        SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
          (W2 :: W3 :: rest)) :
      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
        (W1 :: W2 :: W3 :: rest)

Suggested proof:
- exact SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_tail hobs

Part C: weak tail diagnosis under cons.

Prove:

  theorem sourcePressureLocalIslandWitnessList_tailFailure_oneStepDiagnosis_under_cons
      {n : OddNat} {k r : Nat}
      {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
      {rest : List (SourcePressureLocalIslandWitness n k r)}
      (h2pos :
        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
      (h3pos :
        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
      (htail :
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
          (W2 :: W3 :: rest)) :
      ((∃ hrev : SourcePressureLocalIslandWitnessBefore W3 W2,
        (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
          W2 W3 hrev).items).map
          (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
        ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
            (W1 :: W2 :: W3 :: rest))
      ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
          (W3 :: rest)

Suggested proof:
- rcases sourcePressureLocalIslandWitnessList_failure_oneStepDiagnosis
    h2pos h3pos htail with htailDiag | hdeep
- rcases htailDiag with hrecovered | hobs
- recovered branch:
    exact Or.inl (Or.inl hrecovered)
- overlap branch:
    exact Or.inl (Or.inr
      (sourcePressureLocalIslandWitnessList_tailDiagnosis_overlap_lift hobs))
- deeper failure branch:
    exact Or.inr hdeep

Part D: optional full-list failure wrapper from weak tail diagnosis.

Only if useful, prove a weakened branch theorem where the tail overlap branch is
converted to ordinary full-list failure using
`SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.hasSortedBeforeFailure`.

Do not force this if it becomes verbose.

Part E: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-168.md

Include:
- tail one-step diagnosis alias,
- tail overlap lift theorem,
- weak tail diagnosis under cons theorem,
- explicit note that recovered budget remains a tail-pair budget,
- explicit note that this is not a full list classifier,
- explicit note that overlap remains unmerged/unhandled,
- explicit note that this checkpoint does not introduce maximality, uniqueness,
  coverage, prefix behavior, union accounting, or Collatz convergence.

Verification:

  lake build DkMath.Collatz.PetalBridge.PressureAccounting
  lake build DkMath.Collatz.PetalBridge.PressureFrontier
  lake build DkMath.Collatz.PetalBridge

Run:

  rg -n "\\bsorry\\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
  rg -n "\\bsorry\\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean

Also run:

  git diff --check
```

## さらに一歩先の提案

Checkpoint 168 が通ったら、次は **bounded recursive diagnosis skeleton** じゃ。

ただし、いきなり任意 list を完全分類しない。
まずは「燃料付き」で一段ずつ診断する構造を作るのが安全じゃ。

例えば、

```lean
def SourcePressureLocalIslandWitnessListDiagnosisFuel
```

のような大きな構造体に行く前に、まず theorem として、

```text
2 段まで診断する
3 段まで診断する
```

を試す。

具体的には、長さ 3 の list について、

```text
failure [W1, W2, W3]
  -> head recovered
  or head overlap obstruction
  or tail recovered
  or tail overlap obstruction
```

のような theorem がよい。

これは完全再帰ではないが、pattern が見える。
pattern が見えてから、fuel 付き一般化へ進むとよい。

## 総評

Checkpoint 167 は、list failure を一段剥がす重要 checkpoint じゃ。

これで、

```text
failure
  -> head を見る
  -> tail に送る
```

が Lean で固定された。

次は tail 側の one-step diagnosis を、新しい head の下でも安全に扱う。
ここで recovered budget を full-list budget に誤拡張しなければ、かなり堅い。
PressureAccounting は、再帰的 failure 診断の直前まで来ておるぞ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
index c9504ee8..07d8b573 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
@@ -2131,6 +2131,43 @@ theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_head_
   · exact SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_tail
       htail

+/--
+Decompose an adjacent sorted-before failure at a nontrivial witness list into
+the head pair or the tail.
+
+This is the inverse of the head/tail constructors.  It peels exactly one
+recursive layer and does not classify or repair the resulting branch.
+-/
+theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.head_or_tail
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+        (W1 :: W2 :: rest)) :
+    (¬ SourcePressureLocalIslandWitnessBefore W1 W2) ∨
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+        (W2 :: rest) := by
+  simpa [SourcePressureLocalIslandWitnessListHasSortedBeforeFailure,
+    sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList,
+    SourcePressureIntervalPulseAddressFamilyHasSortedBeforeFailure,
+    SourcePressureIntervalPulseAddressListHasSortedBeforeFailure,
+    sourcePressureAccountedIntervalList_of_intervalPulseAddressList,
+    SourcePressureAccountedIntervalListHasSortedBeforeFailure] using h
+
+/-- Iff form of one-layer sorted-before failure decomposition. -/
+theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_iff_head_or_tail
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)} :
+    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+        (W1 :: W2 :: rest) ↔
+      (¬ SourcePressureLocalIslandWitnessBefore W1 W2) ∨
+        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+          (W2 :: rest) :=
+  ⟨SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.head_or_tail,
+    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_head_or_tail⟩
+
 /--
 Every explicit local-island witness pair is either sorted or carries a
 sorted-before failure.
@@ -2808,6 +2845,66 @@ theorem
       (SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_headPairObstruction
         hobs)

+/--
+Head not-before diagnosis for an explicit witness list.
+
+The head order failure is first packaged as the two-witness sorted-before
+failure, then passed to the head-pair recovered-or-obstruction split.
+-/
+theorem
+    sourcePressureLocalIslandWitnessList_headNotBefore_recovered_or_adjacentOverlapObstruction
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    (h1pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
+    (h2pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
+    (hnot : ¬ SourcePressureLocalIslandWitnessBefore W1 W2) :
+    (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
+      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+        W1 W2 hrev).items).map
+        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
+    ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+        (W1 :: W2 :: rest) :=
+  sourcePressureLocalIslandWitnessList_headPair_failure_recovered_or_adjacentOverlapObstruction
+    h1pos h2pos
+    (sourcePressureLocalIslandWitnessListHasSortedBeforeFailure_pair_iff.2
+      hnot)
+
+/--
+One-step diagnosis for a nontrivial witness-list sorted-before failure.
+
+The theorem peels one recursive layer.  A head failure is diagnosed by the
+pair-level recovered-or-adjacent-obstruction split; a tail failure is returned
+as a tail branch.  It is not a recursive algorithm.
+-/
+theorem sourcePressureLocalIslandWitnessList_failure_oneStepDiagnosis
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    (h1pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
+    (h2pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+        (W1 :: W2 :: rest)) :
+    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
+      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+        W1 W2 hrev).items).map
+        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
+      ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+          (W1 :: W2 :: rest))
+    ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+        (W2 :: rest) := by
+  rcases SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.head_or_tail h
+      with hhead | htail
+  · exact Or.inl
+      (sourcePressureLocalIslandWitnessList_headNotBefore_recovered_or_adjacentOverlapObstruction
+        h1pos h2pos hhead)
+  · exact Or.inr htail
+
 /--
 Head-pair split with the obstruction branch weakened to ordinary list
 sorted-before failure.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-167.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-167.md
new file mode 100644
index 00000000..08f47aef
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-167.md
@@ -0,0 +1,159 @@
+# Report Petal 167
+
+## Checkpoint
+
+Checkpoint 167 closes the one-layer decomposition of explicit witness-list
+sorted-before failure.
+
+The goal was intentionally narrow:
+
+- peel one recursive head/tail layer,
+- diagnose a head failure by the existing pair-level recovered-or-obstruction
+  split,
+- return a tail failure as a tail branch,
+- avoid any global sorting algorithm or union accounting.
+
+## Implemented Lean Surface
+
+File:
+
+- `DkMath.Collatz.PetalBridge.PressureAccounting`
+
+### 1. Head-or-tail decomposition
+
+```lean
+theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.head_or_tail
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+        (W1 :: W2 :: rest)) :
+    (¬ SourcePressureLocalIslandWitnessBefore W1 W2) ∨
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+        (W2 :: rest)
+```
+
+This is the inverse direction to the cp166 constructors.  It says that an
+adjacent sorted-before failure in a nontrivial explicit witness list is either
+already visible at the head pair, or it lives in the tail list.
+
+### 2. Iff form
+
+```lean
+theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_iff_head_or_tail
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)} :
+    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+        (W1 :: W2 :: rest) ↔
+      (¬ SourcePressureLocalIslandWitnessBefore W1 W2) ∨
+        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+          (W2 :: rest)
+```
+
+This packages the constructor direction from cp166 and the new decomposition
+direction from this checkpoint.
+
+### 3. Head not-before diagnosis
+
+```lean
+theorem
+    sourcePressureLocalIslandWitnessList_headNotBefore_recovered_or_adjacentOverlapObstruction
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    (h1pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
+    (h2pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
+    (hnot : ¬ SourcePressureLocalIslandWitnessBefore W1 W2) :
+    (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
+      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+        W1 W2 hrev).items).map
+        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
+    ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+        (W1 :: W2 :: rest)
+```
+
+This converts a raw head not-before proof into the existing pair-level
+diagnosis.  If the pair can be reversed, the recovered budget appears at the
+pair level.  Otherwise the result is recorded as an adjacent overlap
+obstruction on the surrounding list.
+
+### 4. One-step diagnosis
+
+```lean
+theorem sourcePressureLocalIslandWitnessList_failure_oneStepDiagnosis
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    (h1pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
+    (h2pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+        (W1 :: W2 :: rest)) :
+    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
+      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+        W1 W2 hrev).items).map
+        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
+      ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+          (W1 :: W2 :: rest))
+    ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+        (W2 :: rest)
+```
+
+This is a one-step diagnostic surface:
+
+- head failure: pair-level recovered branch or adjacent overlap obstruction,
+- tail failure: returned unchanged as a tail sorted-before failure.
+
+It is not a recursive list classifier.
+
+## Boundary Notes
+
+This checkpoint intentionally does not introduce:
+
+- maximality,
+- uniqueness of pressure families,
+- coverage,
+- prefix behavior,
+- union accounting,
+- interval merging,
+- arbitrary list sorting,
+- arbitrary list failure classification,
+- Collatz convergence.
+
+The overlap branch remains unmerged and unhandled.  It is only named as an
+adjacent obstruction.
+
+## Next Inference
+
+The next safe theorem direction is tail-cons propagation for the diagnostic
+surface, but only in the weak form:
+
+```text
+tail failure diagnosis can be lifted as a tail branch under a new head
+```
+
+The recovered-budget branch should not be promoted to a full-list recovered
+budget without additional accounting hypotheses, because the recovered pair may
+live strictly inside the tail.
+
+## Verification
+
+- PASS: `lake build DkMath.Collatz.PetalBridge.PressureAccounting`
+- PASS: `lake build DkMath.Collatz.PetalBridge.PressureFrontier`
+- PASS: `lake build DkMath.Collatz.PetalBridge`
+- PASS: `rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean`
+  produced no hits.
+- PASS: `rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean`
+  produced no hits.
+- PASS: `git diff --check`
+
+Build note: the existing unrelated warning from
+`DkMath.NumberTheory.ZsigmondyCyclotomicResearch` still reports a declaration
+using `sorry`.  This checkpoint did not edit that file, and the two target
+Collatz/PetalBridge files checked above have no `sorry` hits.
````
`````
