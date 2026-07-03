# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureFrontier

gch: 77f6b895eb996cdc4924696d04dfeacf4006d7c7

## Report

Checkpoint 144 完了です。

[PressureFrontier.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean) に address vocabulary を追加しました。

追加内容:

- `SourcePressureRunAddress`
- `SourcePressureIntervalPulseAddress`
- `SourcePressureRunAddress.depthStart`
- `SourcePressureRunAddress.depthEnd`
- `SourcePressureIntervalPulseAddress.toRunAddress`
- `sourcePressureIntervalPulseAddress_left_signChange`
- `sourcePressureIntervalPulseAddress_right_signChange`
- `sourcePressureIntervalPulseAddress_of_localIsland`

住所は `start / len / witness` を包むだけで、maximality・uniqueness・coverage・prefix claim は入れていません。

report は [report-petal-144.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-144.md) に作成しました。

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureDecay` pass
- `lake build DkMath.Collatz.PetalBridge.PressureFrontier` pass
- `lake build DkMath.Collatz.PetalBridge` pass
- `rg -n "\bsorry\b" .../PressureDecay.lean` no hits
- `rg -n "\bsorry\b" .../PressureFrontier.lean` no hits
- `git diff --check` pass

既存の `ZsigmondyCyclotomicResearch` の `sorry` warning は今回範囲外です。

## Review

## 結論

うむ、全体ロードマップは見えておる。
今回の実装は **大域 Big へ直接登る実装** ではなく、その手前で必要になる **Pressure pulse の住所化** じゃ。

レビュー判定は **採用でよい** 。
かなり良い足場になっておる。特に、`start / len / witness` だけを包み、maximality・uniqueness・coverage・prefix claim を一切入れていない点が安全じゃ。今回追加されたものも、`SourcePressureRunAddress`、`SourcePressureIntervalPulseAddress`、`depthStart` / `depthEnd`、pulse から run への forget、左右 sign change 抽出、local island から interval-pulse address を作る constructor で、狙いは明確じゃ。

なお、ファイル名は `review-petal-145.md` じゃが、本文の報告は **Checkpoint 144** 完了になっておる。次に Codex へ投げるものは、こちらでは **Checkpoint 145** として扱えばよい。

## 実装内容の解説

今回の中心は、`PressureFrontier.lean` に **address vocabulary** を追加したことじゃ。

これまでの `SourcePressureRun n k r start len` や `SourcePressureIntervalPulse n k r start len` は、`start` と `len` を外側から毎回持ち回る必要があった。つまり、pulse を扱うたびに、

```lean
start
len
hpulse
```

を個別に引き回す形になりやすい。

今回の `SourcePressureIntervalPulseAddress` は、それを一つのオブジェクトとして束ねる。

```lean
structure SourcePressureIntervalPulseAddress (n : OddNat) (k r : ℕ) where
  start : ℕ
  len : ℕ
  hpulse : SourcePressureIntervalPulse n k r start len
```

これにより、以後は **「この pulse」** を `A` として渡せる。
この効果は地味じゃが大きい。局所 island、interval pulse、positive run、sign change、net-drop crossing / falling を、すべて同じ住所 `A` から取り出せるようになるからじゃ。

数学的には、これは

$$
\text{局所現象}
\to
\text{名前付き区間}
\to
\text{会計対象}
$$

への第一歩じゃな。

## 今回よい点

第一に、主張が薄い。
ここがよい。

今回の住所は、あくまで **観測された run / pulse の witness package** であって、最大区間である、唯一である、全 positive depth を覆う、prefix である、とは言っていない。これは以前から警戒していた「prefix claim の罠」を避けている。報告にも、住所層は relative start・length・run / pulse proof だけを包むと明記されておる。

第二に、local island から interval-pulse address への導線ができた。

$$
\text{SourcePressureLocalIsland}
\to
\text{SourcePressureIntervalPulse}
\to
\text{SourcePressureIntervalPulseAddress}
\to
\text{SourcePressureRunAddress}
$$

という道ができた。報告でもこの inference shape が次段の安定オブジェクトになると整理されておる。

第三に、ビルド・sorry 状況がよい。
`PressureDecay`、`PressureFrontier`、`PetalBridge` の build が通り、今回対象の `PressureDecay.lean` と `PressureFrontier.lean` には `sorry` がない。既存の `ZsigmondyCyclotomicResearch` warning は範囲外という扱いで問題ない。

## 注意点

ひとつだけ注意するなら、`depthEnd` の形じゃ。

$$
r+(start+len-1)
$$

なので、`len = 0` なら Nat 減算の丸めが絡む。しかし、snapshot 上では `SourcePressurePositiveBlock` 側が `0 < len` を含むので、`SourcePressureRunAddress` の `hrun` から `0 < A.len` は取り出せるはずじゃ。したがって次 checkpoint では、明示的に

```lean
SourcePressureRunAddress.len_pos
SourcePressureIntervalPulseAddress.len_pos
```

を出しておくとよい。

これで `depthEnd` 周りの後続証明がかなり楽になる。

## 全体ロードマップ上の位置

今の山道はこうじゃ。

## 1. 局所観測層

`PressureDecay` / `PressureFrontier` で、margin、net drop、sign change、local island、positive run、interval pulse を観測する。

これはすでにかなり進んでいる。

## 2. 住所層

今回ここに入った。

$$
\text{pulse as predicate}
\to
\text{pulse as address object}
$$

じゃ。

この層の目的は、大域 Big ではなく、後段で interval accounting をするために、局所 pulse を持ち運べる形にすること。

## 3. 射影層

次にやるべきはここ。

`A : SourcePressureIntervalPulseAddress n k r` から、

- run address
- absolute start / end
- left sign change
- right sign change
- left net-drop crossing
- right net-drop falling
- start positive
- length positive

を取り出す。

今回の報告でも、次 checkpoint として address projection helpers が提案されておる。

## 4. 会計層

ここからようやく、

$$
M(j+1)=M(j)+\Delta(j)
$$

を interval 上で足し上げる。

$$
M(b)=M(a)+\sum_{j=a}^{b-1}\Delta(j)
$$

の方向じゃ。

## 5. 局所 Big 層

positive run / interval pulse ごとに、局所的な上界を作る。

$$
x\le X_{\max},\qquad u\le U_{\max},\qquad x+u\le X_{\max}+U_{\max}
$$

ここで初めて、局所 Big が見える。

## 6. Beam / 伝播層

局所 Big が、隣の depth window、次の orbit window、次の pulse へどう伝播するかを見る。

## 7. 大域 Big 層

最終的に、

$$
Big=Core+Beam+Gap
$$

として、全軌道を包む器を探す。
ここはまだ先じゃ。今は Core を住所付きで持てるようにしている段階じゃな。

## 次の Codex 依頼

```text
Checkpoint 145: Add address projection helpers for Collatz/PetalBridge PressureFrontier.

Context:
Checkpoint 144 added thin address objects in
DkMath.Collatz.PetalBridge.PressureFrontier:

- SourcePressureRunAddress
- SourcePressureIntervalPulseAddress
- SourcePressureRunAddress.depthStart
- SourcePressureRunAddress.depthEnd
- SourcePressureIntervalPulseAddress.toRunAddress
- sourcePressureIntervalPulseAddress_left_signChange
- sourcePressureIntervalPulseAddress_right_signChange
- sourcePressureIntervalPulseAddress_of_localIsland

The design rule remains:
address helpers only.
Do not add maximality, uniqueness, coverage, prefix, or global convergence claims.

Tasks:

1. Add positivity projections.

Implement:

- SourcePressureRunAddress.len_pos
- SourcePressureIntervalPulseAddress.len_pos
- sourcePressureIntervalPulseAddress_start_pos

Expected meanings:

- len_pos should be extracted from the underlying SourcePressureRun / SourcePressureIntervalPulse witness.
- start_pos should be extracted from the left boundary condition of SourcePressureIntervalPulse, because SourcePressureRunHasLeftCrossing includes 0 < start.

2. Add depth helpers for interval-pulse addresses.

Implement:

- SourcePressureIntervalPulseAddress.depthStart
- SourcePressureIntervalPulseAddress.depthEnd

Use the same convention as SourcePressureRunAddress:

- depthStart := r + A.start
- depthEnd   := r + (A.start + A.len - 1)

Also add simp/projection lemmas connecting these to A.toRunAddress:

- sourcePressureIntervalPulseAddress_toRun_depthStart
- sourcePressureIntervalPulseAddress_toRun_depthEnd

3. Add address-level projections to boundary predicates.

Implement:

- sourcePressureIntervalPulseAddress_toRun
  if this name is useful as theorem/alias around A.toRunAddress.

- sourcePressureIntervalPulseAddress_left
  returning SourcePressureRunHasLeftCrossing n k r A.start A.len

- sourcePressureIntervalPulseAddress_right
  returning SourcePressureRunHasRightFall n k r A.start A.len

The already-existing sign-change helpers can remain.

4. Add address-level net-drop forms.

Using existing theorems:

- sourcePressureIntervalPulse_left_crossing
- sourcePressureIntervalPulse_right_falling

implement:

- sourcePressureIntervalPulseAddress_left_crossing
- sourcePressureIntervalPulseAddress_right_falling

Expected shapes:

sourcePressureIntervalPulseAddress_left_crossing:
  SourcePressureMarginInt n k (r + (A.start - 1)) ≤ 0 ∧
  0 <
    SourcePressureMarginInt n k (r + (A.start - 1)) +
      SourcePressureNetDropInt n k r (A.start - 1)

sourcePressureIntervalPulseAddress_right_falling:
  0 < SourcePressureMarginInt n k (r + (A.start + A.len - 1)) ∧
  SourcePressureMarginInt n k (r + (A.start + A.len - 1)) +
    SourcePressureNetDropInt n k r (A.start + A.len - 1) ≤ 0

5. Keep implementation thin.

Do not introduce new definitions about maximal pulses.
Do not prove coverage of all positive depths.
Do not claim prefix behavior.
Do not claim Collatz convergence.
Do not create a new module unless PressureFrontier becomes too large; if a split is necessary, create only a small
DkMath.Collatz.PetalBridge.PressureAddress
and re-export it from PetalBridge.

6. Verification commands:

lake build DkMath.Collatz.PetalBridge.PressureDecay
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge

rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureDecay.lean
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean

git diff --check

7. Report:

Create a short report file under docs/dev/das-p2l-260607/review/
named report-petal-145.md.

Explain:
- what address projections were added,
- that no maximality / uniqueness / coverage / prefix claims were introduced,
- how the new address-level crossing/falling lemmas prepare the next interval accounting checkpoint.
```

わっちの見立てでは、次はこの薄い projection 層で正解じゃ。
ここを急がず閉じれば、その次にようやく **interval accounting**、つまり pulse 一本ごとの取引明細を合計する段へ入れる。大域 Big は、その先じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
index fe336a2f..102931fb 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
@@ -885,6 +885,78 @@ theorem sourcePressureIntervalPulse_right_falling
       n k r (a + len - 1)).1
     (sourcePressureIntervalPulse_right_signChange h)
 
+/--
+Address of a positive pressure run.
+
+This packages only the observed start/length witness and the run proof.  It
+does not assert that the run is maximal, unique, covering, or prefix-shaped.
+-/
+structure SourcePressureRunAddress (n : OddNat) (k r : ℕ) where
+  /-- Start depth index, relative to base pressure depth `r`. -/
+  start : ℕ
+  /-- Run length in pressure-depth indices. -/
+  len : ℕ
+  /-- The addressed positive pressure run. -/
+  hrun : SourcePressureRun n k r start len
+
+/--
+Address of an interval pressure pulse.
+
+This is the interval-pulse analogue of `SourcePressureRunAddress`: it records
+the relative start, the length, and the pulse witness, without any maximality
+or uniqueness claim.
+-/
+structure SourcePressureIntervalPulseAddress (n : OddNat) (k r : ℕ) where
+  /-- Start depth index, relative to base pressure depth `r`. -/
+  start : ℕ
+  /-- Pulse length in pressure-depth indices. -/
+  len : ℕ
+  /-- The addressed interval pressure pulse. -/
+  hpulse : SourcePressureIntervalPulse n k r start len
+
+namespace SourcePressureRunAddress
+
+/-- Absolute pressure-depth start of a run address. -/
+def depthStart
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureRunAddress n k r) : ℕ :=
+  r + A.start
+
+/-- Absolute pressure-depth end of a run address. -/
+def depthEnd
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureRunAddress n k r) : ℕ :=
+  r + (A.start + A.len - 1)
+
+end SourcePressureRunAddress
+
+namespace SourcePressureIntervalPulseAddress
+
+/-- Forget an interval-pulse address down to its positive-run address. -/
+def toRunAddress
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    SourcePressureRunAddress n k r :=
+  { start := A.start
+    len := A.len
+    hrun := sourcePressureIntervalPulse_run A.hpulse }
+
+end SourcePressureIntervalPulseAddress
+
+/-- Extract the left sign change from an interval-pulse address. -/
+theorem sourcePressureIntervalPulseAddress_left_signChange
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    SourcePressureSignChangeUp n k r (A.start - 1) :=
+  sourcePressureIntervalPulse_left_signChange A.hpulse
+
+/-- Extract the right sign change from an interval-pulse address. -/
+theorem sourcePressureIntervalPulseAddress_right_signChange
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    SourcePressureSignChangeDown n k r (A.start + A.len - 1) :=
+  sourcePressureIntervalPulse_right_signChange A.hpulse
+
 /--
 A local pressure island is an interval pulse of length one.
 
@@ -909,6 +981,17 @@ theorem sourcePressureIntervalPulse_singleton_of_localIsland
       sourcePressureSignChangeDown_of_localIsland n k r j
         ⟨hjpos, hsel, hprev_not, hnext_not⟩
 
+/--
+Build an interval-pulse address from a local pressure island.
+-/
+def sourcePressureIntervalPulseAddress_of_localIsland
+    (n : OddNat) (k r j : ℕ)
+    (hisland : SourcePressureLocalIsland n k r j) :
+    SourcePressureIntervalPulseAddress n k r :=
+  { start := j
+    len := 1
+    hpulse := sourcePressureIntervalPulse_singleton_of_localIsland n k r j hisland }
+
 /--
 Package a named margin jump and a strict retention drop.
 
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-144.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-144.md
new file mode 100644
index 00000000..831b68fb
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-144.md
@@ -0,0 +1,158 @@
+# Report Petal 144
+
+## Scope
+
+Checkpoint 144 returned to the mathematical API after the `PressureDecay`
+split.  It added a thin address layer for positive pressure runs and interval
+pulses.
+
+Updated:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+```
+
+No Python changes were needed.
+
+## Lean additions
+
+Added run address:
+
+```lean
+structure SourcePressureRunAddress (n : OddNat) (k r : Nat)
+```
+
+Fields:
+
+```lean
+start : Nat
+len   : Nat
+hrun  : SourcePressureRun n k r start len
+```
+
+Added interval-pulse address:
+
+```lean
+structure SourcePressureIntervalPulseAddress (n : OddNat) (k r : Nat)
+```
+
+Fields:
+
+```lean
+start  : Nat
+len    : Nat
+hpulse : SourcePressureIntervalPulse n k r start len
+```
+
+Added address helpers:
+
+```lean
+SourcePressureRunAddress.depthStart
+SourcePressureRunAddress.depthEnd
+SourcePressureIntervalPulseAddress.toRunAddress
+```
+
+Added interval-pulse address projections:
+
+```lean
+sourcePressureIntervalPulseAddress_left_signChange
+sourcePressureIntervalPulseAddress_right_signChange
+```
+
+Added local-island address constructor:
+
+```lean
+def sourcePressureIntervalPulseAddress_of_localIsland
+```
+
+## Design note
+
+The address layer is intentionally only a witness package:
+
+```text
+relative start
+length
+run / pulse proof
+```
+
+It does not assert maximality, uniqueness, coverage, or prefix behavior.
+
+The absolute depth helpers are:
+
+```lean
+depthStart := r + A.start
+depthEnd   := r + (A.start + A.len - 1)
+```
+
+This keeps the pressure-depth index convention visible:
+
+```text
+r = base pressure depth
+start = relative depth offset
+len = run length
+```
+
+## Inference
+
+The useful shape now is:
+
+```text
+SourcePressureLocalIsland
+  -> SourcePressureIntervalPulse n k r j 1
+  -> SourcePressureIntervalPulseAddress n k r
+  -> SourcePressureRunAddress n k r
+```
+
+This gives later checkpoints a stable object to pass around without repeatedly
+threading explicit `start`, `len`, and proof fields.
+
+The next mathematical layer can add projections from addresses to:
+
+```text
+absolute start/end depths
+left/right sign changes
+left/right net-drop crossing/falling
+```
+
+or split address vocabulary into a small `PressureAddress` module if
+`PressureFrontier` continues growing.
+
+## Verification
+
+Commands run:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureDecay
+lake build DkMath.Collatz.PetalBridge.PressureFrontier
+lake build DkMath.Collatz.PetalBridge
+rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureDecay.lean
+rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+```
+
+Result:
+
+```text
+pass
+```
+
+The `rg` checks returned no matches in either file.
+
+The build still reports the pre-existing unrelated warning:
+
+```text
+DkMath.NumberTheory.ZsigmondyCyclotomicResearch: declaration uses `sorry`
+```
+
+## Suggested next checkpoint
+
+Add address projection helpers:
+
+```lean
+sourcePressureIntervalPulseAddress_toRun
+sourcePressureIntervalPulseAddress_left_crossing
+sourcePressureIntervalPulseAddress_right_falling
+SourcePressureIntervalPulseAddress.depthStart
+SourcePressureIntervalPulseAddress.depthEnd
+```
+
+Keep the same rule: address helpers only, no maximality or uniqueness.
````
`````
