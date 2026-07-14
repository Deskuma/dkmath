# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureAccounting

gch: 6a878beb0becf71bac890a0e7b6c385f6d0abd77

## Report

cp174 実装完了です。

[PressureAccounting.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean:3551) に sharp projection を追加しました。

追加:

- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_overlap`
- `sourcePressureLocalIslandWitnessList_failure_five_hasAdjacentDiagnosis`

sharp projection は overlap を通常 failure に弱めず、`SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L` のまま保持します。length-five wrapper は head を一段剥がし、tail 側は既存の length-four wrapper を `of_tail` で持ち上げる bounded API です。一般再帰 classifier には踏み込んでいません。

[report-petal-174.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-174.md:1) も作成済みです。`PressureAccounting.lean` が 3773 行になっているため、次は一括リファクタではなく adjacent-diagnosis 周辺の段階的分割が妥当、という観測も記録しました。

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureAccounting` PASS
- `lake build DkMath.Collatz.PetalBridge.PressureFrontier` PASS
- `lake build DkMath.Collatz.PetalBridge` PASS
- 対象2ファイルの `sorry` 検索ヒットなし
- `git diff --check` PASS

既存の無関係 warning として `DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6 declaration uses sorry` は引き続き表示されています。

## Review

## 結論

うむ、Checkpoint 174 は **採用** じゃ 👍️
今回で、list-level adjacent diagnosis に対する **sharp projection** と、bounded な **length-five wrapper** が入った。

追加された中心は、

```lean
SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_overlap
sourcePressureLocalIslandWitnessList_failure_five_hasAdjacentDiagnosis
```

じゃな。

`exists_recovered_or_overlap` は overlap branch を ordinary failure に弱めず、`SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L` のまま保持している。さらに length-five wrapper は、head を一段剥がし、tail 側は既存の length-four wrapper を `of_tail` で持ち上げる bounded API になっている。一般再帰 classifier には踏み込んでいない。

## 実装レビュー

## 1. sharp projection は良い

今回の

```lean
SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_overlap
```

は、かなり重要じゃ。

これまでは、

```lean
SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_listFailure
```

で overlap branch を ordinary sorted-before failure に弱めていた。

今回の sharp 版では、

```text
some addressed adjacent pair has pair-local recovered budget
or
the enclosing list has adjacent overlap obstruction
```

として、overlap obstruction の情報を落とさない。

これは後で overlap branch を解析する可能性を残すので、とても良い。

## 2. length-five wrapper で bounded pattern が確認できた

```lean
sourcePressureLocalIslandWitnessList_failure_five_hasAdjacentDiagnosis
```

は、ここまで積んできた API が自然に働いている。

構造は、

```text
failure [W1,W2,W3,W4,W5]
  -> one-step diagnosis
  -> head branch:
       of_head
  -> tail branch:
       length-four wrapper
       then of_tail
```

じゃ。

この形が素直に通ったということは、`ListHasAdjacentDiagnosis` と `of_tail` の設計がうまく噛み合っている証拠じゃ。

## 3. recovered budget の局所性が保たれている

今回も recovered budget は、診断を生んだ adjacent pair に留まっている。

```text
W1,W2
W2,W3
W3,W4
W4,W5
```

のどれかに属する pair-local budget であって、list 全体の union accounting ではない。

ここを守れているのがよい。

## 注意点

## 1. ここで固定長 wrapper を増やし続けると危ない

length-five まで通ったので、pattern は十分観測できた。

次に length-six, length-seven と増やすことはできるが、`PressureAccounting.lean` はすでに約 3773 行という報告がある。
このまま theorem を足し続けると、意味のまとまりよりファイル肥大が先に来る。

## 2. まだ任意長 classifier ではない

今回も、

```text
arbitrary-length failure -> has adjacent diagnosis
```

は言っていない。

まだ fuel-indexed classifier でもない。
sorting でもない。
coverage でもない。

ここは明確に維持すべきじゃ。

## 3. 次は「証明追加」より「境界設計」がよい

ここまでで、

```text
length-three
length-four
length-five
```

の bounded wrapper が揃った。

次に必要なのは、さらに固定長を増やすことではなく、

```text
adjacent-diagnosis 周辺をどのファイルへ切り出すか
どの依存を前段に置くべきか
どの theorem を public API とするか
```

を整理することじゃ。

## 数学的・構造的意味

今回の到達点はこう読める。

```text
明示 list に sorted-before failure があるなら、
少なくとも一つの隣接 pair に、
局所診断が存在する。
```

ただし、これは bounded な list 長に対して確認された形じゃ。

診断の中身は二つ。

```text
recovered:
  逆順 pair として budget ≤ -2 が得られる

overlap:
  enclosing list に adjacent overlap obstruction がある
```

つまり、PressureAccounting はいま、

```text
failure を検出する
  -> 隣接 pair に局所化する
  -> pair-local recovery か overlap obstruction に分ける
```

という形まで育っている。

これはかなり良い。
「大域の failure を、局所 pair の診断へ落とす」道が見えてきた。

## 次の checkpoint 方針

次は **一括リファクタではなく、adjacent-diagnosis 周辺の分割設計 checkpoint** がよい。

まだ Lean 宣言を動かさず、まず依存関係を整理する。
理由は、`PressureAccounting.lean` 内の既存宣言に依存している可能性が高く、無計画にファイル移動すると import cycle や downstream breakage が起きやすいからじゃ。

まずは docs に、

```text
どの宣言を adjacent-diagnosis cluster と見るか
どの宣言が upstream dependency か
どの宣言を将来の新ファイルへ移せるか
移すなら段階はどうするか
```

をまとめるのが安全じゃ。

## 次の Codex 指示

```text
Checkpoint 175: Main root only — adjacent-diagnosis split preflight report.

Scope:
Focus only on the main Collatz/PetalBridge root.

Primary goal:
Do not move Lean declarations yet.  Create a refactor preflight report for the
adjacent-diagnosis surface around PressureAccounting.

Allowed implementation files:
- Prefer no Lean code changes in this checkpoint.
- Only touch Lean files if a tiny comment/section marker is clearly useful and
  does not affect declarations.

Allowed documentation files:
- docs/dev/das-p2l-260607/review/report-petal-175.md
- docs/dev/das-p2l-260607/refactor/pressure-adjacent-diagnosis-split-plan.md

Do not modify:
- OneCycle.lean
- ValuationFlowBridge.lean
- ABC files
- NumberTheory files

Do not move declarations yet.

Context:
Checkpoint 174 added:

- SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_overlap
- sourcePressureLocalIslandWitnessList_failure_five_hasAdjacentDiagnosis

The adjacent-diagnosis surface now includes at least:

- SourcePressureLocalIslandWitnessAdjacentDiagnosis
- SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered
- SourcePressureLocalIslandWitnessAdjacentDiagnosis.overlap
- SourcePressureLocalIslandWitnessAdjacentDiagnosis.elim
- SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered_or_listFailure
- SourcePressureLocalIslandWitnessAdjacentDiagnosis.lift_tail
- SourcePressureLocalIslandWitnessAdjacentPairInList
- SourcePressureLocalIslandWitnessAdjacentPairInList.head
- SourcePressureLocalIslandWitnessAdjacentPairInList.tail
- SourcePressureLocalIslandWitnessAdjacentPairInList.head_or_tail
- SourcePressureLocalIslandWitnessAdjacentPairInList.cons_iff_head_or_tail
- SourcePressureLocalIslandWitnessAdjacentPairInList.nil_false
- SourcePressureLocalIslandWitnessAdjacentPairInList.singleton_false
- SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
- SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_adjacent
- SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.elim
- SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_head
- SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail
- SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail_tail
- SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail_tail_tail
- SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_listFailure
- SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_overlap
- sourcePressureLocalIslandWitnessList_failure_threeDiagnosis_carrier
- sourcePressureLocalIslandWitnessList_failure_fourDiagnosis_carrier
- sourcePressureLocalIslandWitnessList_failure_three_hasAdjacentDiagnosis
- sourcePressureLocalIslandWitnessList_failure_four_hasAdjacentDiagnosis
- sourcePressureLocalIslandWitnessList_failure_five_hasAdjacentDiagnosis

Global rules:
- Do not claim maximality.
- Do not claim uniqueness of pressure families.
- Do not claim coverage.
- Do not claim prefix behavior.
- Do not claim union accounting.
- Do not claim Collatz convergence.
- Do not introduce sorting.
- Do not introduce a general recursive classifier.
- Do not move declarations yet.
- Keep recovered budgets pair-local.
- Keep overlap as an adjacent obstruction on the enclosing list.

Part A: create split plan document.

Create:

  docs/dev/das-p2l-260607/refactor/pressure-adjacent-diagnosis-split-plan.md

Include sections:

1. Current state
   - note current PressureAccounting.lean approximate line count;
   - explain why adjacent-diagnosis declarations are now a coherent cluster.

2. Candidate cluster
   - list declarations belonging to:
     - adjacent diagnosis carrier;
     - adjacent pair address predicate;
     - list-level adjacent diagnosis carrier;
     - bounded diagnosis wrappers;
     - projection / propagation helpers.

3. Upstream dependencies
   For each cluster group, identify the major upstream declarations it depends on.
   Examples likely include:
   - SourcePressureLocalIslandWitness
   - SourcePressureLocalIslandWitnessBefore
   - SourcePressureIntervalNetDrop
   - sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
   - SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
   - SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
   - sourcePressureLocalIslandWitnessList_failure_oneStepDiagnosis
   - sourcePressureLocalIslandWitnessList_failure_threeDiagnosis
   - sourcePressureLocalIslandWitnessList_failure_fourDiagnosis_carrier

4. Candidate module layout
   Propose a staged layout, but do not implement it yet.
   For example:
   - PressureAccounting.lean remains the compatibility surface for now.
   - A future PressureAdjacentDiagnosis.lean may host carrier/address/bounded wrapper declarations.
   - If dependencies make direct extraction impossible, identify which earlier declarations must be split first.

5. Migration plan
   Stage 1:
   - add no new theorem movement;
   - document dependency boundaries.

   Stage 2:
   - extract only declarations that depend on stable upstream declarations;
   - keep names unchanged;
   - update imports;
   - ensure DkMath.Collatz.PetalBridge still builds.

   Stage 3:
   - move bounded wrappers only after carrier/address predicates are stable.

6. Risks
   - import cycles;
   - downstream files importing PressureAccounting expecting these names;
   - theorem order dependencies;
   - namespace/name stability;
   - line-number churn in review diffs.

7. Non-goals
   Explicitly say this refactor plan does not introduce:
   - arbitrary-length classifier;
   - fuel-indexed diagnosis;
   - sorting;
   - coverage;
   - union accounting;
   - Collatz convergence.

Part B: create checkpoint report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-175.md

Include:
- that this checkpoint is a refactor preflight only;
- no Lean declaration movement;
- summary of the split plan;
- recommended next implementation checkpoint;
- verification commands run.

Part C: optional lightweight verification.

Run:

  lake build DkMath.Collatz.PetalBridge.PressureAccounting
  lake build DkMath.Collatz.PetalBridge.PressureFrontier
  lake build DkMath.Collatz.PetalBridge

Run:

  rg -n "\\bsorry\\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
  rg -n "\\bsorry\\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean

Also run:

  git diff --check

Part D: do not implement the split yet.

Do not create a new Lean module in this checkpoint unless the report discovers
a very low-risk documentation-only stub is useful.  The main output should be
the split plan.
```

## さらに一歩先の提案

Checkpoint 175 で分割計画ができたら、次は二択じゃ。

一つ目は、実際に `AdjacentDiagnosis` 周辺だけを小さく切り出す。
ただし、この場合は import cycle を避けるため、どの upstream 定義を先に分けるかが重要になる。

二つ目は、まだファイル分割せずに、`ListHasAdjacentDiagnosis` の bounded recursion helper の型だけを設計する。

わっちとしては、まず **split preflight report** を挟むのが一番安全じゃ。
ここまでかなり積み上がってきたので、焦って一般化するより、足場を一度締め直すのがよい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
index 9b906d8d..70337d10 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
@@ -3540,6 +3540,30 @@ theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovere
   exact ⟨A, B, hin,
     SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered_or_listFailure hdiag⟩
 
+/--
+Project a list-level adjacent diagnosis without weakening the overlap branch.
+
+The recovered alternative remains explicitly tied to the addressed adjacent
+pair `A, B`.  The other alternative is still the sharp adjacent-overlap
+obstruction on the enclosing list `L`; it is not merged into ordinary failure
+and no interval union accounting is introduced.
+-/
+theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_overlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h : SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis L) :
+    (∃ A B,
+      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+        ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
+          (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+            A B hrev).items).map
+            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2)
+    ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L := by
+  rcases h with ⟨A, B, hin, hdiag⟩
+  rcases hdiag with hrecovered | hobs
+  · exact Or.inl ⟨A, B, hin, hrecovered⟩
+  · exact Or.inr hobs
+
 /-- The empty witness list cannot carry a list-level adjacent diagnosis. -/
 theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.nil_false
     {n : OddNat} {k r : ℕ} :
@@ -3618,6 +3642,38 @@ theorem sourcePressureLocalIslandWitnessList_failure_four_hasAdjacentDiagnosis
           (SourcePressureLocalIslandWitnessAdjacentPairInList.tail
             SourcePressureLocalIslandWitnessAdjacentPairInList.head)) h34
 
+/--
+Length-five sorted-before failure yields a list-level adjacent diagnosis.
+
+This is a bounded wrapper: it peels the head pair once, then delegates the tail
+case to the existing four-witness wrapper and lifts that diagnosis back to the
+full list.  It is not a general recursive classifier.
+-/
+theorem sourcePressureLocalIslandWitnessList_failure_five_hasAdjacentDiagnosis
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 W4 W5 : SourcePressureLocalIslandWitness n k r}
+    (h1pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
+    (h2pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
+    (h3pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
+    (h4pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W4).len)
+    (h5pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W5).len)
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+        [W1, W2, W3, W4, W5]) :
+    SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
+      [W1, W2, W3, W4, W5] := by
+  rcases sourcePressureLocalIslandWitnessList_failure_oneStepDiagnosis
+      h1pos h2pos h with hhead | htail
+  · exact SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_head hhead
+  · exact SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail
+      (sourcePressureLocalIslandWitnessList_failure_four_hasAdjacentDiagnosis
+        h2pos h3pos h4pos h5pos htail)
+
 /--
 Head-pair split with the obstruction branch weakened to ordinary list
 sorted-before failure.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-174.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-174.md
new file mode 100644
index 00000000..4ac17c79
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-174.md
@@ -0,0 +1,120 @@
+# Report Petal 174
+
+## Checkpoint
+
+`cp: 174`
+
+Main root only: sharp projection for list-level adjacent diagnosis, then
+bounded length-five wrapper.
+
+## Implemented
+
+### Sharp recovered-or-overlap projection
+
+Added:
+
+```lean
+theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_overlap
+```
+
+This projects a list-level adjacent diagnosis into exactly one of:
+
+```text
+some addressed adjacent pair with pair-local recovered budget
+or
+the sharp adjacent-overlap obstruction on the enclosing list
+```
+
+Unlike `exists_recovered_or_listFailure`, this theorem does not weaken the
+overlap branch into ordinary sorted-before failure.  The overlap obstruction
+remains unmerged and unhandled.
+
+### Bounded length-five wrapper
+
+Added:
+
+```lean
+theorem sourcePressureLocalIslandWitnessList_failure_five_hasAdjacentDiagnosis
+```
+
+The proof is bounded and follows the existing pattern:
+
+```text
+one-step head/tail diagnosis
+  head: package the head-pair diagnosis
+  tail: use the length-four wrapper and lift by of_tail
+```
+
+This extends the explicit witness-list surface to five witnesses without
+introducing a general recursive classifier.
+
+## Boundary
+
+Recovered budgets remain attached to the adjacent pair that produced them.
+
+Overlap remains an adjacent obstruction on the enclosing list.  No interval
+merge, repair step, or union accounting was added.
+
+This checkpoint did not introduce:
+
+- arbitrary-length failure to adjacent diagnosis;
+- a fuel-indexed classifier;
+- sorting;
+- coverage;
+- maximality;
+- uniqueness;
+- prefix behavior;
+- union accounting;
+- Collatz convergence.
+
+## Refactor Observation
+
+`PressureAccounting.lean` is now about 3773 lines.  The next structural task
+should not be a broad rewrite.  A gradual split should start with the bounded
+adjacent-diagnosis surface around:
+
+```text
+SourcePressureLocalIslandWitnessAdjacentDiagnosis
+SourcePressureLocalIslandWitnessAdjacentPairInList
+SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
+```
+
+The current checkpoint intentionally avoided moving declarations, so the
+review diff stays small and theorem names remain stable.
+
+## Verification
+
+Builds completed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureAccounting
+lake build DkMath.Collatz.PetalBridge.PressureFrontier
+lake build DkMath.Collatz.PetalBridge
+```
+
+No-sorry checks completed for:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+```
+
+Whitespace check completed:
+
+```text
+git diff --check
+```
+
+The build still reports the existing unrelated warning:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
+
+## Next Inference
+
+Length five confirms the bounded pattern.  The next checkpoint should either
+design the type shape for a bounded-recursion helper, or begin a gradual file
+split for the adjacent-diagnosis API.  It should still avoid arbitrary list
+classification until the type boundary is reviewed.
````
`````
