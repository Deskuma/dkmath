# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam

gch: 15ce9e8d12cd2391431f488f738fdbfc9e524df2

## Report

cp224 完了です。

下流の `PressureLocalWitnessObstruction / PressureAdjacentDiagnosis / PressureDiagnosticDecomposition / PressureAutomaton` を確認したうえで、直接それらを編集せず、上位の [PressureBeam.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean) に diagnostic-facing consumer theorem を 2 本追加しました。

```lean
sourcePressureBeamPulse_diagnostic_massBalance_of_intervalPulseAddress
sourcePressureBeamPulse_witness_singleton_depth_and_exit_massBalance
```

どちらも cp223 の packaged shape を実際に消費して、caller が欲しそうな `entry: left < right` と `exit: right <= left`、および witness singleton の addressed depth を取り出します。下流診断モジュールは witness-list order failure / overlap obstruction が主語なので、Beam 語彙を下へ import しない判断にしました。

レポートも追加済みです。

- [report-petal-224.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-224.md)

検証済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
rg no-sorry/admit over inspected pressure files
git diff --check
```

`PressureBeam.lean` は 1885 行で、2000 行の分割基準に近づいています。次に大きめの section を足すなら、`PressureBeam.Edge` / `PressureBeam.Pulse` あたりの段階的分割を検討するのがよさそうです。

## Review

## 結論

**採用** じゃ。
cp224 は、`PressureBeam` の local pulse API を「下流に押し込まず、上位で消費用 projection として置く」という判断がよい。

追加された theorem はこの 2 本。

```lean id="mutja7"
sourcePressureBeamPulse_diagnostic_massBalance_of_intervalPulseAddress
sourcePressureBeamPulse_witness_singleton_depth_and_exit_massBalance
```

下流の `PressureLocalWitnessObstruction / PressureAdjacentDiagnosis / PressureDiagnosticDecomposition / PressureAutomaton` を直接編集しなかった判断も正しい。これらは witness-list order failure / overlap obstruction が主語なので、Beam 語彙を下へ import すると依存方向が濁る。今回は `PressureBeam` 側に diagnostic-facing consumer theorem を置いた、という整理で安全じゃ。

## 実装レビュー

今回の 1 本目。

```lean id="ztsm45"
sourcePressureBeamPulse_diagnostic_massBalance_of_intervalPulseAddress
```

これは cp223 の

```lean id="h5hqro"
sourcePressureBeamPulse_edges_of_intervalPulseAddress A
```

を消費して、

```text id="96xz6f"
entry:
  left < right

exit:
  right <= left
```

を取り出している。

つまり、caller は entry / exit edge target を毎回分解しなくてよい。これは diagnostic-facing projection として意味がある。

2 本目。

```lean id="sm6gkc"
sourcePressureBeamPulse_witness_singleton_depth_and_exit_massBalance
```

こちらは witness singleton shape から、

```text id="66n7ot"
addressed depth target at singleton center/right edge
```

と、

```text id="8umjx6"
right <= left at the same exit edge
```

を取り出す。

ここで `W ∈ L` を要求するのも正しい。
crossing / falling edge は pulse 由来の intrinsic sign-change だが、`AddressedDepthTarget` は list-relative carrier なので、membership が必要じゃ。

## 数学的意味

これで、local pulse API は「作る」だけでなく、「使う」形まで整った。

```text id="s1b0id"
pulse shape:
  entry + center/depth + exit
```

から、

```text id="u4g33i"
diagnostic-facing facts:
  entry mass-balance true side
  selected depth target
  exit false/boundary side
```

へ落とせるようになった。

これは小さいが重要な段階じゃ。
「分類器」や「語彙」だけで終わらず、実際に downstream caller が使いやすい projection を用意したことになる。

## True Beam / DepthTarget / Falling-or-Boundary / Gap

## True Beam

interval pulse の entry 側。

```text id="phd438"
entry edge
  -> left < right
```

これは True Beam 側の mass-balance 比較として消費される。

## DepthTarget

witness singleton 側。

```text id="qjefmf"
W ∈ L
  -> addressed depth target at singleton right/center edge
```

これは list-relative な選択 carrier として保持される。

## Falling-or-Boundary

exit 側。

```text id="ehs5pi"
exit edge
  -> right <= left
```

これは false-or-boundary。
strict false ではない点も維持されている。

## Gap

今回も踏み込んでいないものは明確じゃ。

```text id="pz42vh"
coverage
propagation
family aggregation
canonical target selection
overlap repair
arbitrary target transport
Collatz convergence
```

ここはまだ Gap のまま。
今は一つの pulse / 一つの witness に対する local consumer API じゃ。

## 評価

今回の最大の良さは、**下流モジュールを汚さなかったこと**じゃ。

現時点では、

```text id="2t6a59"
PressureAutomaton
  <- PressureBeam
```

という向きで、Beam が下流 diagnostic の結果を読む上位層になっている。
ここで下流側へ Beam 語彙を import させると、依存関係が逆流する。

Codex はそこを避け、`PressureBeam` 内に consumer theorem を置いた。
これはかなり良い設計判断じゃ。

## 注意点

`PressureBeam.lean` が 1885 行。
2000 行の分割基準が近い。

次に大きな theorem section を足すなら、先に分割を考えたほうがよい。
ここからさらに 100 行以上増えると、また Codex 消費とレビュー負荷が上がる。

分割候補は report 通り、

```text id="xpuh2r"
PressureBeam.Edge
PressureBeam.Pulse
```

あたりが自然じゃ。

ただし、分割は新 theorem 追加と混ぜないほうがよい。
やるなら mechanical refactor checkpoint として切る。

## 次の checkpoint 方針

次は二択じゃ。

```text id="kf0e2e"
A:
  具体的な downstream theorem が今すぐ必要なら、
  今回の consumer projection を使う小さな theorem を追加する

B:
  これ以上 `PressureBeam.lean` を太らせる前に、
  mechanical split を行う
```

私は **B を推す**。
ここまでで `PressureBeam` は局所 classifier、edge vocabulary、pulse packaging、diagnostic-facing consumer まで揃った。
つまり一区切りとして、分割しやすい。

## 次の Codex 指示

```text id="fz5m6n"
Checkpoint: petal-225

Goal:
  Perform a mechanical refactor split of `PressureBeam.lean` if the workspace
  structure supports it.  Do not add new mathematical theorem content in this
  checkpoint unless required only to preserve imports.

Context:
  `PressureBeam.lean` is now around 1885 lines and close to the 2000-line split
  criterion.

  The recent sections have formed relatively coherent blocks:

    local classifier / mass-balance API
    edge vocabulary:
      CrossingEdgeTarget
      FallingEdgeTarget
    pulse packaging:
      interval pulse entry/exit
      witness singleton shape
    diagnostic-facing consumer projections

Main question:
  Can the edge/pulse vocabulary be split into smaller modules without changing
  theorem statements or proof content?

Candidate module layout, only if imports remain clean:

  DkMath.Collatz.PetalBridge.PressureBeam
    public aggregator / import file

  DkMath.Collatz.PetalBridge.PressureBeam.Core
    existing seed / addressed target / mass-balance definitions and classifiers

  DkMath.Collatz.PetalBridge.PressureBeam.Edge
    CrossingEdgeTarget
    FallingEdgeTarget
    edge-local mass-balance classifiers
    interval-pulse left/right edge bridges

  DkMath.Collatz.PetalBridge.PressureBeam.Pulse
    local pulse-shape packaging
    diagnostic-facing consumer projections

Do not force this exact layout.
Codex should inspect import dependencies and choose the smallest safe split.

Allowed outcomes:
  1. Split into `PressureBeam/Core.lean`, `PressureBeam/Edge.lean`,
     `PressureBeam/Pulse.lean`, and make `PressureBeam.lean` an aggregator.
  2. Split only one section, such as `PressureBeam/Edge.lean`, if that is safer.
  3. Add no split and write a report explaining why the current dependency shape
     makes a split premature.

Strict guardrails:
  - Do not introduce new mathematical claims.
  - Do not rename public theorem names unless unavoidable.
  - Do not change theorem statements.
  - Do not move lower modules to import higher modules.
  - Do not create circular imports.
  - Do not add coverage, propagation, aggregation, overlap repair, canonical
    target selection, or convergence claims.

Mechanical verification:
  lake build DkMath.Collatz.PetalBridge.PressureBeam
  lake build DkMath.Collatz.PetalBridge
  no-sorry grep over pressure files
  git diff --check

Report requirements:
  - Explain what was moved where.
  - Confirm public theorem names are unchanged.
  - Confirm dependency direction remains clean.
  - State final line counts of split files.
  - If no split was done, explain the exact dependency blocker.
  - Make clear this is a mechanical refactor checkpoint, not new proof work.
```

## 一歩先ゆく推論

このタイミングで分割すると、次の研究段階に入りやすい。

今の `PressureBeam` は、

```text id="xorzbq"
local classifier を作る
edge vocabulary を作る
pulse shape を作る
consumer projection を作る
```

まで終わった。

次はたぶん、

```text id="d9im4c"
diagnostic / automaton との接続を本格化する
```

段階じゃ。
その前にファイルを整理しておくと、今後 Codex の消費も減るし、レビューもしやすくなる。

## 総合判断

cp224 は成功。
そして、ここで `PressureBeam` は一度 refactor checkpoint に入るのがよい。

数学を進める前に、道具箱を整理する段階じゃな。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
index f6361c54..d2a1d73a 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
@@ -1818,4 +1818,68 @@ theorem sourcePressureBeamPulse_witness_singleton_massBalance_edges
   ⟨sourcePressureBeamMassBalanceLeft_lt_right_of_localIslandWitness_intervalPulse_left W,
     sourcePressureBeamMassBalanceRight_le_left_of_localIslandWitness_intervalPulse_right_falling W⟩
 
+/-
+Diagnostic-facing consumers of the local pulse-shape package.
+
+Checkpoint 224 inspected the downstream obstruction/diagnostic files.  Those
+files classify explicit witness-list order failure and overlap; importing Beam
+entry/exit vocabulary into them would blur the current module split.  The
+lightweight consumer layer therefore stays here, above the diagnostic modules:
+it projects the cp223 package into the exact facts a diagnostic caller is most
+likely to need.
+
+These theorems deliberately consume the packaged shape instead of rebuilding
+the left/right facts directly.  This keeps the future call site small while
+preserving the local-only contract: one supplied pulse, or one supplied witness
+with membership in one supplied list.
+-/
+
+/--
+Diagnostic-facing projection for one interval pulse.
+
+From the packaged entry/exit edge shape, recover the paired mass-balance
+classification: True Beam at the entry edge and False/Boundary at the exit
+edge.
+-/
+theorem sourcePressureBeamPulse_diagnostic_massBalance_of_intervalPulseAddress
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    SourcePressureBeamMassBalanceLeftInt n k r (A.start - 1) <
+        SourcePressureBeamMassBalanceRightInt n k r (A.start - 1) ∧
+      SourcePressureBeamMassBalanceRightInt n k r (A.start + A.len - 1) ≤
+        SourcePressureBeamMassBalanceLeftInt n k r (A.start + A.len - 1) := by
+  rcases sourcePressureBeamPulse_edges_of_intervalPulseAddress A with
+    ⟨hentry, hexit⟩
+  exact
+    ⟨sourcePressureBeamMassBalanceLeft_lt_right_of_crossingEdgeTarget hentry,
+      sourcePressureBeamMassBalanceRight_le_left_of_fallingEdgeTarget hexit⟩
+
+/--
+Diagnostic-facing projection for one witness-generated singleton pulse.
+
+The result keeps exactly the two facts that an obstruction consumer can use
+without claiming coverage: the selected addressed depth at the singleton
+center/right edge, and the False/Boundary mass-balance comparison at that same
+exit edge.
+-/
+theorem sourcePressureBeamPulse_witness_singleton_depth_and_exit_massBalance
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W : SourcePressureLocalIslandWitness n k r}
+    (hmem : W ∈ L) :
+    SourcePressureBeamAddressedDepthTarget L
+        ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
+          (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) ∧
+      SourcePressureBeamMassBalanceRightInt n k r
+          ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
+            (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) ≤
+        SourcePressureBeamMassBalanceLeftInt n k r
+          ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
+            (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) := by
+  rcases sourcePressureBeamPulse_witness_singleton_shape hmem with
+    ⟨_, hdepth, hexit⟩
+  exact
+    ⟨hdepth,
+      sourcePressureBeamMassBalanceRight_le_left_of_fallingEdgeTarget hexit⟩
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-224.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-224.md
new file mode 100644
index 00000000..67afa9b3
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-224.md
@@ -0,0 +1,157 @@
+# Report: petal-224
+
+## Checkpoint
+
+`petal-224` asked whether the local pulse-shape package from cp223 should be
+consumed by a downstream diagnostic or obstruction-facing layer.
+
+The implemented answer is a small consumer layer in `PressureBeam.lean`.
+No downstream diagnostic module was modified.
+
+## What was inspected
+
+The inspected modules were:
+
+- `DkMath.Collatz.PetalBridge.PressureBeam`
+- `DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction`
+- `DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis`
+- `DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition`
+- `DkMath.Collatz.PetalBridge.PressureAutomaton`
+
+The downstream diagnostic files are focused on explicit witness-list order
+failure, adjacent pair recovery, and overlap obstruction.  They do not yet need
+to own Beam entry/exit vocabulary directly.  Importing Beam facts back into
+those lower layers would blur the current module split:
+
+```text
+PressureAutomaton
+  <- PressureBeam
+```
+
+So the consumer theorem surface was added in `PressureBeam`, above the
+diagnostic modules.
+
+## Implemented theorem surface
+
+Added:
+
+```lean
+sourcePressureBeamPulse_diagnostic_massBalance_of_intervalPulseAddress
+sourcePressureBeamPulse_witness_singleton_depth_and_exit_massBalance
+```
+
+Both theorems deliberately consume the cp223 packaged shape.
+
+For an interval pulse:
+
+```lean
+sourcePressureBeamPulse_edges_of_intervalPulseAddress A
+```
+
+is destructed into entry and exit edge targets, then projected to the paired
+mass-balance comparison:
+
+```text
+entry:
+  left < right
+
+exit:
+  right <= left
+```
+
+For a witness singleton:
+
+```lean
+sourcePressureBeamPulse_witness_singleton_shape hmem
+```
+
+is destructed into:
+
+```text
+entry crossing target
+addressed depth target
+exit falling target
+```
+
+and projected to the two diagnostic-facing facts:
+
+```text
+addressed depth at the singleton right/center edge
+right <= left at the same exit edge
+```
+
+The membership hypothesis `W ∈ L` is still required for the addressed-depth
+component because addressed targets are list-relative carriers.
+
+## Why not edit the lower diagnostic files?
+
+The obstruction and adjacent-diagnosis modules classify list order failure and
+overlap.  They do not currently repeat entry/exit Beam reasoning.  Adding Beam
+imports or Beam-specific predicates there would increase coupling without
+reducing existing proof noise.
+
+The new consumer layer gives future diagnostic callers a ready projection while
+preserving the current dependency direction.
+
+## Classification
+
+- True Beam:
+  The interval entry edge is consumed as `left < right`.
+
+- DepthTarget:
+  The witness singleton projection keeps the addressed depth target at the
+  generated singleton right/center edge.
+
+- Falling-or-Boundary:
+  The exit edge is consumed as `right <= left`.
+
+- Gap:
+  No coverage, propagation, family aggregation, canonical target selection,
+  overlap repair, arbitrary target transport, or Collatz convergence is claimed.
+
+## File size / refactor note
+
+`PressureBeam.lean` is now 1885 lines.  This is still below the 2000-line split
+criterion, but close enough that the next few checkpoints should be careful.
+
+If the next work adds another large section, the likely split point is the
+edge/pulse vocabulary:
+
+```text
+PressureBeam.Edge
+PressureBeam.Pulse
+```
+
+That split should be gradual and mechanical, not mixed with new theorem work.
+
+## Verification
+
+Completed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureBeam
+lake build DkMath.Collatz.PetalBridge
+rg -n "\bsorry\b|admit" over inspected pressure files
+git diff --check
+```
+
+The inspected pressure files have no new `sorry` / `admit` matches.
+
+Known unrelated project warning remains:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses 'sorry'
+```
+
+## Next inference
+
+The diagnostic consumer surface is now available without changing the lower
+diagnostic modules.  The next natural step is either:
+
+1. use these projections from a concrete downstream theorem, if a caller now
+   needs the exact facts; or
+2. start the gradual `PressureBeam` split before adding more large sections.
+
+Given the file size, a split should be considered soon, but it does not need to
+happen until a new checkpoint would push the file past the stated threshold.
````
`````
