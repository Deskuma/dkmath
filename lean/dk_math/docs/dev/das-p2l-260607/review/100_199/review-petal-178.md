# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.*

gch: b3dac05c17c9aa766c3b64dd6f68752ebc15e95c

## Report

実装完了しました。`cp: 177` の main goal まで到達しています。

追加したもの:

- [PressureLocalWitnessObstruction.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean)
  - `sourcePressureIntervalPulseAddress_of_localIslandWitness_len_pos`
- [PressureAdjacentDiagnosis.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean)
  - `sourcePressureLocalIslandWitnessList_failure_hasAdjacentDiagnosis_of_forall_len_pos`
  - `sourcePressureLocalIslandWitnessList_failure_hasAdjacentDiagnosis`
- [report-petal-177.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-177.md)

意味としては、明示的に与えられた witness list に sorted-before failure があるなら、その同じ list 内に list-level adjacent diagnosis が存在する、という一般定理です。自動の witness-address length positivity も通ったので、hpos なしの clean theorem まで入れました。

検証:

```bash
lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
git diff --check
```

対象3ファイルの `sorry` 検索も no hits です。既存の無関係 warning として `ZsigmondyCyclotomicResearch.lean:152` の `sorry` は引き続き表示されています。

## Review

## 結論

うむ、Checkpoint 177 は **採用** じゃ 👍️
これはかなり大きい。固定長 3 / 4 / 5 の bounded wrapper から一段進んで、**任意の明示 witness list** に対する一般構文定理まで到達しておる。

追加された中心はこの 3 つじゃ。

```lean id="v0zd6m"
sourcePressureIntervalPulseAddress_of_localIslandWitness_len_pos
sourcePressureLocalIslandWitnessList_failure_hasAdjacentDiagnosis_of_forall_len_pos
sourcePressureLocalIslandWitnessList_failure_hasAdjacentDiagnosis
```

意味としては、

```text id="s48kyx"
明示的に与えられた local-island witness list に sorted-before failure があるなら、
その同じ list 内のどこかの adjacent pair に list-level adjacent diagnosis が存在する。
```

じゃな。自動の witness-address length positivity まで通っているので、`hpos` なしの clean theorem が入ったのも大きい。

## 実装レビュー

## 1. `len_pos` wrapper は正しい位置にある

```lean id="x79bt4"
sourcePressureIntervalPulseAddress_of_localIslandWitness_len_pos
```

は、`PressureLocalWitnessObstruction.lean` に置かれている。これは正しい。

これは `SourcePressureIntervalPulseAddress.len_pos` を witness-facing にしただけの薄い wrapper で、完全性や canonical list を主張していない。レポートでも「supplied explicit witness に局所的」と明記されている。

この補題のおかげで、後続の theorem から `hpos` 仮定を外せた。

## 2. 明示 list の induction が綺麗

```lean id="i0x4j3"
sourcePressureLocalIslandWitnessList_failure_hasAdjacentDiagnosis_of_forall_len_pos
```

の証明構造はかなり良い。

流れは、

```text id="orr0t0"
nil:
  failure は不可能

singleton:
  failure は不可能

W1 :: W2 :: rest:
  one-step diagnosis で head / tail に分ける

head:
  of_head で list-level adjacent diagnosis

tail:
  induction hypothesis で tail diagnosis
  of_tail で元 list へ持ち上げる
```

じゃ。

これは、ここまで積んできた API が自然に噛み合っている証拠じゃな。とくに `of_tail` の設計が効いている。

## 3. clean public theorem まで閉じたのが重要

```lean id="z6xwhj"
sourcePressureLocalIslandWitnessList_failure_hasAdjacentDiagnosis
```

は、今回の checkpoint の本体じゃ。

これは、

```lean id="kf0vwk"
sourcePressureLocalIslandWitnessList_failure_hasAdjacentDiagnosis_of_forall_len_pos
```

に対して、

```lean id="qmx2re"
sourcePressureIntervalPulseAddress_of_localIslandWitness_len_pos
```

を供給しているだけの clean wrapper じゃが、外部 API としての意味は大きい。

今後の consumer は、長さ 3 / 4 / 5 を気にせず、

```text id="a6clhx"
failure L
  -> has adjacent diagnosis L
```

を直接使える。

## 数学的意味

今回の theorem は、DkMath 的にはこう読める。

```text id="v92cdr"
list の sorted-before failure は、
どこかの隣接 pair の局所診断へ必ず落ちる。
```

ここで「局所診断」は二種類じゃ。

```text id="t1ypqz"
recovered:
  逆順 pair として pair-local budget ≤ -2 を持つ

overlap:
  enclosing explicit list に adjacent overlap obstruction がある
```

つまり、list-level の failure は、少なくとも一つの adjacent pair に局所化される。

これは良い。
ただし、これは **coverage theorem ではない**。
全 local island を列挙しているわけではない。
最初の failure を canonical に選んでいるわけでもない。
全 diagnosis を enumerate しているわけでもない。

レポートでも、global local-island coverage、maximality、uniqueness、prefix behavior、arbitrary sorting、canonical first diagnosis、enumeration、union accounting、overlap repair、Collatz convergence は主張しないと明記されている。

## 到達点の評価

これは、PressureAdjacentDiagnosis の一つの節目じゃ。

これまでの段階は、

```text id="ebirtt"
length-three failure
  -> adjacent diagnosis

length-four failure
  -> adjacent diagnosis

length-five failure
  -> adjacent diagnosis
```

だった。

今回からは、

```text id="kkmhmg"
任意の明示 witness list failure
  -> adjacent diagnosis
```

になった。

ここで「任意」と言ってよいのは、**明示的に与えられた list に対して** という意味じゃ。
大域的な全 local island の covering family ではない。

この境界を守れば、今回の theorem はかなり強い。

## 注意点

## 1. `ListHasAdjacentDiagnosis` は存在主張

```lean id="q4mrna"
SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis L
```

は、「少なくとも一つある」じゃ。

まだ次は言っていない。

```text id="sr8cou"
全 failure を列挙する
canonical first diagnosis を返す
隣接診断の全リストを作る
```

ここは次の段階でも慎重に扱うべきじゃ。

## 2. tail induction は list 構文の theorem

今回の proof は、list の構文構造に沿って剥がしている。
したがって theorem の性質は、

```text id="3nrazn"
与えられた list の sorted-before failure predicate を構文的に分解する
```

であって、軌道上・深さ方向の大域的 completeness ではない。

この違いは大事じゃ。

## 3. 次は projection theorem が自然

今回の theorem は `has adjacent diagnosis` で止まる。
次は、それを既存の sharp projection に通して、

```text id="s5cxf9"
failure L
  -> exists pair-local recovered budget
  or adjacent overlap obstruction L
```

へ落とすのが自然じゃ。

既に `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_overlap` があるので、これは薄い corollary で通るはずじゃ。レポートの Next Candidate もその方向を示している。

## 次の checkpoint 方針

次は **consumer-facing corollaries** を作るのがよい。

主 theorem はすでに閉じた。
次は外部から使いやすい表面 API にする。

欲しいのは、

```lean id="w0cb97"
sourcePressureLocalIslandWitnessList_failure_exists_recovered_or_overlap
```

と、

```lean id="vvncuh"
sourcePressureLocalIslandWitnessList_failure_of_no_overlap_exists_recovered
```

じゃ。

後者は特に重要で、

```text id="l9wg3n"
overlap obstruction がないなら、
failure は pair-local recovered budget を持つ adjacent pair を生む
```

と言える。

これは overlap branch を明示的な obstruction として隔離する、かなり使いやすい形じゃ。

## 次の Codex 指示

```text id="gg8oot"
Checkpoint 178: Main root only — consumer-facing corollaries from explicit-list failure diagnosis.

Scope:
Focus on the refactored Collatz/PetalBridge pressure modules.

Primary target file:
- DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean

Allowed supporting file, only if needed:
- DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean

Do not modify:
- PressureAccounting.lean unless import/order forces a tiny fix
- OneCycle.lean
- ValuationFlowBridge.lean
- ABC files
- NumberTheory files

Do not rename or rewrite previous theorem statements.

Context:
Checkpoint 177 added:

- sourcePressureIntervalPulseAddress_of_localIslandWitness_len_pos
- sourcePressureLocalIslandWitnessList_failure_hasAdjacentDiagnosis_of_forall_len_pos
- sourcePressureLocalIslandWitnessList_failure_hasAdjacentDiagnosis

Relevant existing projection theorem:

- SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_overlap

It projects a list-level adjacent diagnosis into:

- some addressed adjacent pair with pair-local recovered budget,
  or
- SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L.

Global guardrails:
- Do not claim global local-island coverage.
- Do not claim maximality.
- Do not claim uniqueness.
- Do not claim prefix behavior.
- Do not claim arbitrary list sorting.
- Do not claim canonical first diagnosis.
- Do not enumerate all diagnoses.
- Do not claim union accounting.
- Do not claim overlap repair.
- Do not claim Collatz convergence.
- Keep all statements local to explicitly supplied witness lists.
- Recovered budgets remain pair-local.
- Overlap remains an adjacent obstruction on the enclosing explicit list.

Main goal:
Add small consumer-facing corollaries that combine the new general explicit-list
failure theorem with the existing sharp projection.

Part A: failure implies recovered-or-overlap.

Prove:

  theorem sourcePressureLocalIslandWitnessList_failure_exists_recovered_or_overlap
      {n : OddNat} {k r : Nat}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      (h :
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L) :
      (∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
            (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
              A B hrev).items).map
              (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2)
      ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L

Suggested proof:
- exact
    SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_overlap
      (sourcePressureLocalIslandWitnessList_failure_hasAdjacentDiagnosis h)

Part B: no-overlap corollary gives recovered pair.

Prove:

  theorem sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_no_overlap
      {n : OddNat} {k r : Nat}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      (h :
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
      (hno :
        ¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
      ∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
            (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
              A B hrev).items).map
              (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2

Suggested proof:
- rcases sourcePressureLocalIslandWitnessList_failure_exists_recovered_or_overlap h
  with hrec | hobs
- recovered branch: exact hrec
- overlap branch: exact False.elim (hno hobs)

Part C: optional ordinary list-failure projection.

Only if useful and not redundant, prove a consumer-facing corollary using
`exists_recovered_or_listFailure`.

Be careful: since the input already assumes sorted-before failure of L, a theorem
whose right branch is merely `SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L`
may be tautological and less useful. Prefer Part A and Part B.

Part D: optional aliases for names.

If theorem names become too long, keep the long precise names.  Do not abbreviate
in a way that hides `explicit-list`, `recovered`, or `overlap`.

Part E: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-178.md

Include:
- the recovered-or-overlap corollary;
- the no-overlap recovered corollary;
- proof strategy summary;
- explicit note that this is consumer-facing API over the cp177 theorem;
- explicit note that no general coverage, maximality, uniqueness, sorting,
  canonical first diagnosis, enumeration, union accounting, overlap repair, or
  Collatz convergence was introduced;
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

## さらに一歩先の提案

Checkpoint 178 が通ったら、次は **overlap-free sorted list family** へ進める。

ただし、まだ sorting algorithm ではない。
次に作るなら、

```text id="fihyjs"
明示 list に failure がある
かつ
adjacent overlap obstruction がない
なら
pair-local recovered budget を持つ adjacent pair がある
```

を使って、overlap-free な failure list が必ず recovered branch を持つ、という形じゃ。

これは「overlap が唯一の obstruction」として綺麗に分離される。
その先で初めて、overlap をどう扱うか、あるいは overlap-free family をどこまで作れるかを見るとよい。

## 総評

Checkpoint 177 は、かなり良い節目じゃ。

これまでの bounded wrapper 群が、ついに一般の明示 list 定理へ統合された。

```text id="3p8nly"
sorted-before failure L
  -> adjacent diagnosis L
```

これが通ったことで、PressureAdjacentDiagnosis は実用 API になった。

次は、その diagnosis を consumer が直接使いやすいように、

```text id="f6h3q5"
recovered branch
or
overlap obstruction branch
```

へ射影する corollary を足す。
ここまで通れば、次の大きな問いは「overlap-free なら何が言えるか」に移れるぞ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
index 84ecec13..9f78672c 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
@@ -448,6 +448,78 @@ theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.singleton_false
   rintro ⟨A, B, hin, _⟩
   exact SourcePressureLocalIslandWitnessAdjacentPairInList.singleton_false hin

+/--
+Any sorted-before failure in an explicitly supplied witness list has a
+list-level adjacent diagnosis, assuming the converted witness addresses have
+positive length.
+
+The proof only peels the explicit list until the existing one-step diagnosis
+finds either the head pair or a tail failure.  It does not sort the list, choose
+a canonical first diagnosis, enumerate all diagnoses, merge intervals, or claim
+that the list covers all local islands.
+-/
+theorem
+    sourcePressureLocalIslandWitnessList_failure_hasAdjacentDiagnosis_of_forall_len_pos
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hpos :
+      ∀ W ∈ L,
+        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len)
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L) :
+    SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis L := by
+  induction L with
+  | nil =>
+      exact False.elim
+        (SourcePressureLocalIslandWitnessListHasSortedBeforeFailure_nil_false h)
+  | cons W1 tail ih =>
+      cases tail with
+      | nil =>
+          exact False.elim
+            (SourcePressureLocalIslandWitnessListHasSortedBeforeFailure_singleton_false
+              h)
+      | cons W2 rest =>
+          have h1pos :
+              0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len :=
+            hpos W1 (by simp)
+          have h2pos :
+              0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len :=
+            hpos W2 (by simp)
+          rcases sourcePressureLocalIslandWitnessList_failure_oneStepDiagnosis
+              h1pos h2pos h with hhead | htail
+          · exact SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_head
+              hhead
+          · have htailpos :
+                ∀ W ∈ W2 :: rest,
+                  0 <
+                    (sourcePressureIntervalPulseAddress_of_localIslandWitness
+                      W).len := by
+              intro W hW
+              exact hpos W (List.mem_cons_of_mem W1 hW)
+            exact SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail
+              (ih htailpos htail)
+
+/--
+Any sorted-before failure in an explicitly supplied witness list has a
+list-level adjacent diagnosis.
+
+This is the clean public form of the previous theorem.  The positivity
+hypothesis is discharged by the local witness-address length lemma.  The result
+is still only local to the supplied explicit list: it is not a sorting
+algorithm, not a coverage theorem, and not a union-accounting statement.
+-/
+theorem sourcePressureLocalIslandWitnessList_failure_hasAdjacentDiagnosis
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L) :
+    SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis L :=
+  sourcePressureLocalIslandWitnessList_failure_hasAdjacentDiagnosis_of_forall_len_pos
+    (by
+      intro W _hW
+      exact sourcePressureIntervalPulseAddress_of_localIslandWitness_len_pos W)
+    h
+
 /--
 Length-three sorted-before failure yields a list-level adjacent diagnosis.

diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
index d21e9661..b68e258f 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
@@ -17,6 +17,21 @@ islands, do not sort arbitrary lists, do not merge overlapping intervals, and do
 not prove Collatz convergence.
 -/

+/--
+The interval-pulse address obtained from one explicit local-island witness has
+positive length.
+
+This is the witness-facing wrapper around
+`SourcePressureIntervalPulseAddress.len_pos`.  It is intentionally local to the
+supplied witness and does not say anything about a complete list of islands.
+-/
+theorem sourcePressureIntervalPulseAddress_of_localIslandWitness_len_pos
+    {n : OddNat} {k r : ℕ}
+    (W : SourcePressureLocalIslandWitness n k r) :
+    0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len :=
+  SourcePressureIntervalPulseAddress.len_pos
+    (sourcePressureIntervalPulseAddress_of_localIslandWitness W)
+
 /--
 Ordered non-overlap for two explicit local-island witnesses.

diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-177.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-177.md
new file mode 100644
index 00000000..d98a6df3
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-177.md
@@ -0,0 +1,167 @@
+# Report Petal 177
+
+## Scope
+
+Checkpoint 177 focused on the refactored Collatz/PetalBridge pressure modules.
+
+Primary file:
+
+```text
+DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+```
+
+Supporting file:
+
+```text
+DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
+```
+
+No `OneCycle`, `ValuationFlowBridge`, `ABC`, or `NumberTheory` files were
+modified.
+
+## Implemented Theorems
+
+### Witness-address length positivity
+
+Added:
+
+```lean
+theorem sourcePressureIntervalPulseAddress_of_localIslandWitness_len_pos
+    {n : OddNat} {k r : ℕ}
+    (W : SourcePressureLocalIslandWitness n k r) :
+    0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len
+```
+
+This is a witness-facing wrapper around:
+
+```lean
+SourcePressureIntervalPulseAddress.len_pos
+```
+
+The theorem is local to the supplied explicit witness.  It does not assert that
+the witness belongs to a complete or canonical list of local islands.
+
+### Explicit positivity theorem
+
+Added:
+
+```lean
+theorem
+    sourcePressureLocalIslandWitnessList_failure_hasAdjacentDiagnosis_of_forall_len_pos
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hpos :
+      ∀ W ∈ L,
+        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len)
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L) :
+    SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis L
+```
+
+Proof strategy:
+
+```text
+structural induction on the explicit list L
+nil: impossible by nil-failure false theorem
+singleton: impossible by singleton-failure false theorem
+cons-cons:
+  use the existing one-step diagnosis
+  head branch -> list-level diagnosis by `of_head`
+  tail branch -> induction hypothesis, then lift by `of_tail`
+```
+
+### Clean public theorem
+
+Added:
+
+```lean
+theorem sourcePressureLocalIslandWitnessList_failure_hasAdjacentDiagnosis
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L) :
+    SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis L
+```
+
+This discharges the positivity hypothesis using
+`sourcePressureIntervalPulseAddress_of_localIslandWitness_len_pos`.
+
+## Meaning
+
+The new theorem says:
+
+```text
+If an explicitly supplied local-island witness list has sorted-before failure,
+then some adjacent pair in that same explicit list carries an adjacent
+diagnosis.
+```
+
+This moves the fixed length-three/four/five wrappers into the role of bounded
+observational examples of the now-general explicit-list theorem.
+
+## Non-Claims
+
+The theorem does not assert:
+
+```text
+global local-island coverage
+maximality
+uniqueness
+prefix behavior
+arbitrary list sorting
+canonical first diagnosis
+enumeration of all diagnoses
+union accounting
+overlap repair
+Collatz convergence
+```
+
+Recovered budgets remain pair-local.
+Overlap remains an adjacent obstruction on the enclosing explicit list.
+
+## Verification
+
+Passed:
+
+```bash
+lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
+lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
+lake build DkMath.Collatz.PetalBridge.PressureAccounting
+lake build DkMath.Collatz.PetalBridge.PressureFrontier
+lake build DkMath.Collatz.PetalBridge
+git diff --check
+```
+
+No-sorry check:
+
+```bash
+rg -n "\bsorry\b" \
+  DkMath/Collatz/PetalBridge/PressureAccounting.lean \
+  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
+  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+```
+
+Result: no hits.
+
+Known unrelated build warning still appears:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
+
+## Next Candidate
+
+The next natural step is to add small consumer-facing corollaries that project
+the general adjacent diagnosis into either:
+
+```text
+some pair-local recovered budget
+or
+the enclosing list has an adjacent overlap obstruction
+```
+
+The existing projection theorem
+`SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_overlap`
+already provides this once the new general theorem has produced the list-level
+diagnosis.
````
`````
