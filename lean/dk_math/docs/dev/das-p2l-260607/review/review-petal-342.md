# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointReserve

gch: ecb45e2a713f134591bb4c233c252eaf62955481

## Report

(13m20s)

cp-342 を完了しました。

主な確定事項:

- zero-reserve credit は正の初期 drift により第1遷移で負になります。一般 certificate 候補ではないことを Lean で証明しました。
- all-ones family から任意に大きな負 credit と、`SignedCounterCertificate` の不存在を導出しました。
- root-dependent reserve を導入し、cumulative width bound の仮定下で conditional certificate を構成しました。
- 全 root に共通する有限 reserve は存在しません。
- fixed-root cumulative width bound は reflected queue の一様有界性と同値です。ただし独立な評価ではなく、同じ未解決対象の別表現です。
- cumulative width bound から pointwise endpoint-drift bound は従いますが、逆向きは未証明です。
- finite high-drift carrier の successor、membership decomposition、event-count 更新則を証明しました。

実装は [CanonicalEndpointConservation.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointConservation.lean:257)、[CanonicalEndpointReserve.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointReserve.lean:19)、[CanonicalHighDrift.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalHighDrift.lean:57) にあります。総括は [report-petal-342.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-342.md) に記録しました。

`FloatWindow`、`PetalBridge`、全 `DkMath` のビルド成功、変更ファイルの no-sorry、`git diff --check` を確認済みです。

## Review

(4m49s)

## cp-342 実装レビュー

## 総合判定

**実装本体は全面採用。**

cp-342 は、cp-341 で発見した zero-reserve counter の失敗を曖昧な「未証明」状態から引き上げ、

> 正の初期 drift を持つ root では、その counter certificate は存在しない

という明示的な否定定理へ固定した。

同時に、

```text
zero reserve
  → 一般 certificate として反例済み

root-dependent reserve
  → width bound を仮定すれば conditional certificate

global reserve
  → all-ones 族により反証済み

fixed-root cumulative width reserve
  → queue uniform bound と同値、未解決

fixed-root pointwise drift bound
  → cumulative width boundより弱い別問題、未解決
```

という階層が成立した。

循環証明や量化の誤投影はない。

ただし、ドキュメント上に二点だけ補正すべき表現が残っている。

---

## zero-reserve の否定

新しい一段目の式、

$$C_n(1)=-\Delta_n(0)$$

は正確じゃ。

したがって、

$$0<\Delta_n(0)\Longrightarrow C_n(1)<0$$

が直ちに閉じる。zero-reserve credit は「独立 guard が見つからない候補」ではなく、正の初期 drift を持つ root に対して実際に破綻する候補へ格下げされた。

all-ones 族についても、

$$C_{2^{2r+1}-1}(1)\le-r$$

が証明され、$r+1$ 版で strict negativity を得ている。

この使い分けも正しい。

- $r=0$ を含む一般形では $\le0$
- 正パラメータへずらした族では $<0$

となっており、境界を誤魔化していない。

---

## no-certificate theorem

```lean
not_exists_signedCounterCertificate_zeroReserve_of_initialDrift_pos
```

は正しい。

`SignedCounterCertificate.credit_nonneg 1` と、zero-reserve credit の strict negativity が直接衝突するため、certificate の不存在が得られている。all-ones 族への symbolic instanceも正しい。

### さらに強くできる点

現在の theorem は、

```lean
C.weight = endpointAccountingTerm n
C.credit = canonicalEndpointCounterCredit n
```

の両方を仮定しているが、証明では `C.weight` の等式を使っていない。

実際には、

```lean
¬ ∃ C : SignedCounterCertificate,
    C.credit = canonicalEndpointCounterCredit n
```

まで言える。

`SignedCounterCertificate` である以上、credit は全時刻で非負だからじゃ。

さらに exact recurrence同士を比較すれば、credit が一致するなら weight は自動的に endpoint driftへ一致することも導ける。

したがって現在の theorem は正しいが、**本質的 obstruction は weightではなく credit自身の負値**にある。

---

## reserved credit

修正版、

$$C_{n,B}(M)=B+\operatorname{width}(n)-\operatorname{width}(\operatorname{Start}_n(M))$$

は正確に設計されている。

Lean は、

$$C_{n,B}(0)=B$$

$$C_{n,B}(M+1)=C_{n,B}(M)-\Delta_n(M)$$

$$0\le C_{n,B}(M)\iff\operatorname{width}(\operatorname{Start}_n(M))\le\operatorname{width}(n)+B$$

を証明している。全時刻非負性と `CanonicalWidthWithinReserve` の同値も正しい。

これで root-dependent reserve の意味は完全に固定された。

---

## conditional counter certificate

```lean
canonicalEndpointReservedCounterCertificate
```

も論理的に正しい。

`CanonicalWidthWithinReserve n B` を明示的な前提として受け取り、その前提から次時刻の credit 非負性を出し、counter field の guardを埋めている。prefix sumの上界、

$$\sum_{m<M}\Delta_n(m)\le B$$

も正しく得られる。

ただし、この certificate の性格は明確にしておく必要がある。

これは、

```text
local arithmetic guard
→ all-time width bound
```

という証明器ではない。

実装では `hB (m+1)`、すなわち**既に与えられた全時刻 width bound**から guardを構成している。

したがって、

```text
width bound
→ certificate packaging
→ width/prefix consequence
```

という conditional API であり、width bound を証明するための独立な手段ではない。

レポートもそのように記述しているため問題なし。今後この定義を「canonical local guard が得られた」と引用してはならない。

---

## cumulative width bound から pointwise drift bound

新しい二 predicate、

```lean
CanonicalWidthWithinReserve n B
RootwiseCanonicalWidthBound n
```

は必要な分離じゃ。

Lean が証明した方向は、

$$\operatorname{RootwiseCanonicalWidthBound}(n)\Longrightarrow\operatorname{RootwiseEndpointDriftBound}(n)$$

のみ。

これは正しい。

全 width levelが root幅+$B$ 以下なら、次 width もその上限以下であり、現在 widthは非負なので一段 driftにも上限が生じる。

### 表現上の補正

report には、

> the second is strictly the stronger target

という趣旨の表現がある。

ここで **strictly** はまだ Lean 上で確定していない。

一般の整数列では、

```text
bounded increments
↛
bounded cumulative level
```

だが、canonical Collatz 軌道に固有の構造によって逆向きが導けないことまでは証明していない。

したがって正確には、

> cumulative width bound is a formally stronger target in the current API; it implies the pointwise bound, while no converse is currently available.

とするのがよい。

つまり、

$$\text{CumulativeWidthBound}\Longrightarrow\text{PointwiseDriftBound}$$

は theorem。

$$\text{PointwiseDriftBound}\not\Longrightarrow\text{CumulativeWidthBound}$$

は canonical 系については未証明じゃ。

---

## reflected queue との同値

```lean
rootwiseCanonicalWidthBound_iff_exists_queueUniformUpperBound
```

は正しい。

既存 scalar queue は positive suffix driftの反射最大値であり、queue ceiling と endpoint width ceiling の existential equivalenceが既にある。

今回の bridge は block座標へ移し、

$$\exists B,\ \forall M,\ w(M)\le w(0)+B$$

と、

$$\exists C,\ \forall m,\ Q(m)\le C$$

を同値にした。

ここで重要なのは、**存在量化としての同値**であって、同じ定数がそのまま往復するわけではないことじゃ。

実装上の変換は、

```text
width reserve B
  → absolute endpoint-width bound rootWidth + B
  → queue bound rootWidth + B

queue bound C
  → endpoint-width bound rootWidth + C
  → width reserve C
```

となっている。

したがって、

$$B_{\mathrm{reserve}}=C_{\mathrm{queue}}$$

という parameterwise equivalenceではない。

report の「同じ未解決対象の別表現」という評価は正しいが、今後 quantitative theorem を使う際には、この定数変換を明示した方が安全じゃ。

---

## global reserve obstruction

```lean
not_globalCanonicalWidthReserveBound
```

も正確。

任意の共通 reserve $B$ を仮定し、all-ones 族による初期 drift $>B$ の rootを選ぶ。幅制約を $M=1$ へ適用し、exact drift ledgerと衝突させている。

量化は、

$$\neg\exists B,\ \forall n,\ \operatorname{WidthWithinReserve}(n,B)$$

であり、

$$\forall n,\ \neg\exists B,\ \operatorname{WidthWithinReserve}(n,B)$$

ではない。

固定 root への誤投影はない。

---

## high-drift finite carrier の更新則

successor decompositionも完成している。

$$E_{K,M+1}=\begin{cases}E_{K,M}\cup{M}&K\le\Delta(M), \\ E_{K,M}&K>\Delta(M).\end{cases}$$

membershipも、

$$m\in E_{K,M+1}\iff m\in E_{K,M}\lor(m=M\land K\le\Delta(M))$$

と exact。

event countも、

$$N_K(M+1)=N_K(M)+\mathbf 1_{K\le\Delta(M)}$$

まで閉じている。

有限 horizonの外へ結論を伸ばしていない点もよい。

---

## 残っている古いコメント

`CanonicalEndpointConservation.lean` の section header は、

```text
Zero-reserve diagnostic counter
```

へ正しく変更された。

しかし次の theorem の doc comment はまだ、

> The desired local guard ... identifies the remaining arithmetic obligation

となっている。

zero-reserve guard は今や positive-initial-drift rootで**偽と確定済み**なので、この説明は古い。

例えば、

```text
The zero-reserve guard is algebraically equivalent to next-credit
nonnegativity. For roots with positive initial drift it already fails at
M = 0, so this theorem is diagnostic rather than an open certificate
obligation.
```

へ直すべきじゃ。

---

## 戦略上の重要な分岐

cp-342 により、二つの目標の役割が変わった。

## pointwise drift bound

$$\exists B,\ \forall m,\ \Delta_n(m)\le B$$

これは有限 upper-weight tableや一段 transition の制御に必要な条件。

しかし、これだけでは width level の累積成長を止められない。

## cumulative width bound

$$\exists B,\ \forall M,\ w_n(M)\le w_n(0)+B$$

こちらが canonical stateを有限 bit-width領域へ閉じ込める条件。

有限状態化から eventual periodicityへ進むには、実際にはこちらが必要じゃ。

そして cp-342 は、

$$\text{CumulativeWidthBound}\iff\text{UniformQueueBound}$$

を示した。

つまり scalar queue の一様有界性は単なる補助目標ではなく、**固定 root 軌道の有限領域化そのもの**じゃ。

詰将棋の最後の駒ではなく、囲碁盤全体の外周線だったということじゃな。

---

## cp-342 判定一覧

### zero-reserve first-step identity

**完成。**

### positive driftによる zero-reserve negativity

**完成。**

### zero-reserve certificate 不存在

**完成。weight条件を除いてさらに強化可能。**

### root-dependent reserved credit

**完成。**

### conditional reserved certificate

**完成。正しいが、global premiseの再包装。**

### cumulative width ⇒ pointwise drift

**完成。逆向きは未証明。**

### queue boundednessとの existential equivalence

**完成。定数変換は非対称。**

### global common reserve

**反証完成。**

### high-drift successor/count update

**完成。**

### fixed-root cumulative width bound

**未解決。**

### fixed-root pointwise drift bound

**未解決。**

### 循環性

**なし。**

### ドキュメント

**古い zero-reserve guard comment と “strictly stronger” の表現を修正推奨。**

## 総合

**全面採用。軽微なドキュメント修正あり。**

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge FloatWindow branch after
report-petal-342.

Checkpoint 342 is accepted.

It correctly refutes the zero-reserve counter, introduces a conditional
root-dependent reserve, separates cumulative width boundedness from pointwise
drift boundedness, identifies cumulative width boundedness with existential
queue boundedness, and refutes a global reserve.

Stage A — correct the remaining documentation

In `CanonicalEndpointConservation.lean`, revise the comment on:

    endpointAccountingTerm_le_counterCredit_iff_next_nonneg

The zero-reserve guard is not an open arithmetic obligation in general.
It is false at `M = 0` whenever the initial endpoint drift is positive.

In the next report, replace any claim that cumulative width boundedness is
"strictly stronger" for canonical roots with:

    cumulative width boundedness implies pointwise drift boundedness;
    no converse is currently available.

Do not claim a canonical separation theorem unless one is proved.

Stage B — strengthen the zero-reserve obstruction

Prove the stronger theorem:

    0 < endpointAccountingTerm n 0
      ->
    ¬ ∃ C : SignedCounterCertificate,
        C.credit = canonicalEndpointCounterCredit n

The weight equality is unnecessary because every signed-counter certificate
already forces all credit values to be nonnegative.

Optionally prove that if a certificate credit equals the canonical zero-reserve
credit, its exact recurrence forces its weight to equal
`endpointAccountingTerm n`.

Keep the existing caller-facing theorem as a corollary if compatibility is
useful.

Stage C — expose direct prefix-sum / reserve equivalence

Prove the direct theorem:

    CanonicalWidthWithinReserve n B
      ↔
    ∀ M,
      (∑ m in Finset.range M, endpointAccountingTerm n m) ≤ B

using the exact canonical width telescope.

Then prove:

    RootwiseCanonicalWidthBound n
      ↔
    ∃ B : Nat, ∀ M,
      prefixEndpointDrift n M ≤ B.

This should be a direct public bridge, not only an indirect counter-certificate
consequence.

Stage D — expose quantitative queue translations

Add explicit directional theorems showing the constants used by the existing
existential equivalence:

    CanonicalWidthWithinReserve n B
      ->
    CanonicalOutstandingClaimQueueUniformUpperBound
      n (bitWidth n.1 + B)

and:

    CanonicalOutstandingClaimQueueUniformUpperBound n C
      ->
    CanonicalWidthWithinReserve n C.

Retain the existential iff as a corollary.

Do not state a same-constant parameterwise iff.

Stage E — absorption-deficit window bridge

Define or expose a half-open-window absorption deficit:

    lengthWindow
      - claimHolesWindow
      - terminalValuationWindow.

Prove exactly:

    absorptionDeficitWindow n q M
      =
    canonicalEndpointDriftWindowSum n q M
      =
    width(start(q + M)) - width(start(q)).

Bridge this half-open convention to the existing inclusive
`canonicalWindowDriftInt n q m`.

Check empty, singleton, and `M = m - q + 1` endpoint conversions explicitly.

Stage F — reflected queue as maximum absorption deficit

Using the existing theorem that the scalar queue is the maximum positive suffix
drift, prove a conservation-facing form:

    canonicalOutstandingClaimQueue n m
      =
    maximum positive suffix absorption deficit through block m.

At minimum, prove:

    0 < canonicalOutstandingClaimQueue n m
      ->
    ∃ q ≤ m,
      (canonicalOutstandingClaimQueue n m : Int)
        =
      blockLengthWindow(q, m-q+1)
        - claimHolesWindow(q, m-q+1)
        - terminalValuationWindow(q, m-q+1).

This theorem must use the exact queue witness and the block conservation law.
It must not assume a queue bound.

Stage G — exact all-window boundedness target

Define a predicate such as:

    CanonicalAbsorptionDeficitWindowUniformUpperBound n C

meaning that every finite block window has absorption deficit at most `C`.

Prove the existential equivalence:

    RootwiseCanonicalWidthBound n
      ↔
    ∃ C, CanonicalAbsorptionDeficitWindowUniformUpperBound n C.

Make the quantitative constant translations explicit where they differ.

This is a reformulation of the open target, not a proof that the bound exists.

Stage H — distinguish the two remaining arithmetic targets

Keep both public surfaces:

Pointwise target:

    blockLength m
      <= claimHoles m + terminalValuation m + B.

Cumulative target:

    every finite window satisfies
      blockLengthWindow
        <= claimHolesWindow + terminalValuationWindow + C.

Record clearly that the cumulative target is the one needed for bounded
canonical width and finite-state reduction.

The pointwise target alone does not currently imply the cumulative target.

Stage I — search for an independent discharge theorem

Search the existing modules and source database for theorems involving:

    bounded repayment lag;
    source-age horizon;
    reflected queue zeros;
    terminal valuation accumulation;
    claim-hole incidence;
    PressureObstruction;
    Petal sorted-before constraints;
    finite transition-cycle exclusion.

The desired new arithmetic input must imply a cumulative absorption estimate
or force regular queue discharge.

Do not define another credit as the negation of the desired cumulative theorem.

Branch outcomes:

1. If an independent bounded-lag or discharge theorem exists, connect it to the
   absorption-deficit window target.

2. If a finite transition grammar excludes every positive-deficit cycle,
   formalize the exact graph theorem and its canonical bridge.

3. If neither exists, stop at the exact maximum-absorption-deficit
   characterization and report the missing arithmetic statement.

Stage J — finite diagnostics

Extend the finite audit to record the windows attaining the reflected queue
maximum:

    root;
    terminal block;
    witness start block;
    window length;
    cumulative block length;
    cumulative claim holes;
    cumulative terminal valuation;
    resulting absorption deficit / queue.

Keep all audit values explicitly observational.

Stopping rule

Stop at the first genuine obstruction among:

    inclusive and half-open window conventions do not align cleanly;

    the queue witness cannot be transported to the conservation ledgers;

    the same queue/width constant is accidentally claimed in both directions;

    pointwise drift boundedness is used as though it bounded cumulative width;

    a proposed discharge theorem assumes the queue or width bound it is meant
    to prove;

    finite audit data is promoted to an all-time theorem.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-343.md
```

cp-342 で、残る Gap はさらに明確になった。

$$\boxed{\text{Queue}=\text{最大の正の有限窓吸収不足}}$$

次はこの式を claim holes と terminal valuation の保存則へ直接接続し、**どの有限窓が土地不足を起こして queue を膨らませているか**を exact に取り出す段階じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
index ea835388..91fabcb9 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
@@ -42,6 +42,7 @@ import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointDrift
 import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointConservation
 import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalHighDrift
 import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalAllOnesDrift
+import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointReserve
 import DkMath.Collatz.PetalBridge.FloatWindow.RawLowSignatureObstruction

 #print "file: DkMath.Collatz.PetalBridge.FloatWindow"
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalAllOnesDrift.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalAllOnesDrift.lean
index 548e633c..0df2c0a0 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalAllOnesDrift.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalAllOnesDrift.lean
@@ -32,18 +32,11 @@ noncomputable def allOnesOdd (L : ℕ) (hL : 0 < L) : OddNat := by
 @[simp] theorem allOnesOdd_val (L : ℕ) (hL : 0 < L) :
     (allOnesOdd L hL).1 = 2 ^ L - 1 := rfl

-/-- Every first canonical block starts at the root itself. -/
-theorem canonicalBlockStartState_zero (n : OddNat) :
-    canonicalBlockStartState n 0 = n.1 := by
-  unfold canonicalBlockStartState canonicalBlockStartTime
-    canonicalEndpointBlockStart
-  rfl
-
 /-- The all-ones first block starts at the expected binary word. -/
 @[simp] theorem canonicalBlockStartState_allOnesOdd_zero
     (L : ℕ) (hL : 0 < L) :
     canonicalBlockStartState (allOnesOdd L hL) 0 = 2 ^ L - 1 := by
-  rw [canonicalBlockStartState_zero]
+  rw [canonicalBlockStartState_zero_eq_root]
   rfl

 /-- The first canonical block of `2^L - 1` has exact length `L`. -/
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointConservation.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointConservation.lean
index c8eec04b..55bae3bd 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointConservation.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointConservation.lean
@@ -245,9 +245,41 @@ theorem rootwiseEndpointDriftBound_iff_length_le_absorption_add
     have habsorb := hB m
     omega

+/-! ## Cumulative width boundedness
+
+This is deliberately stronger than pointwise endpoint-drift boundedness.  It
+controls every canonical width relative to the initial root width, rather than
+only controlling each one-step increment.  No converse implication is claimed.
+-/
+
+/-- A specified reserve bounds every canonical block-start width above the
+initial root width. -/
+def CanonicalWidthWithinReserve (n : OddNat) (B : ℕ) : Prop :=
+  ∀ M, bitWidth (canonicalBlockStartState n M) ≤ bitWidth n.1 + B
+
+/-- One fixed root admits some finite cumulative width reserve. -/
+def RootwiseCanonicalWidthBound (n : OddNat) : Prop :=
+  ∃ B : ℕ, CanonicalWidthWithinReserve n B
+
+/-- A cumulative width reserve gives a pointwise endpoint-drift ceiling.  The
+reverse implication is not available: bounded increments need not bound their
+cumulative level. -/
+theorem RootwiseCanonicalWidthBound.to_endpointDriftBound
+    {n : OddNat} (h : RootwiseCanonicalWidthBound n) :
+    RootwiseEndpointDriftBound n := by
+  rcases h with ⟨B, hB⟩
+  refine ⟨(bitWidth n.1 + B : ℕ), ?_⟩
+  intro m
+  rw [endpointAccountingTerm_eq_canonicalBlock_bitWidth_sub]
+  have hnext := hB (m + 1)
+  rw [canonicalBlockStartState_succ_eq_nextStartState] at hnext
+  omega
+
 /-! ## Scaled cumulative absorption -/

-/-- Scaling preserves the exact window budget over `Int`. -/
+/-- Scaling preserves the exact window budget over `Int`.  This is algebraic
+transport of the conservation identity, not a spiral-growth coefficient
+estimate. -/
 theorem canonicalEndpointWidthBudgetWindow_conservation_mul
     (n : OddNat) (q M : ℕ) (A : ℤ) :
     A * ((bitWidth (canonicalBlockStartState n (q + M)) : ℤ) -
@@ -311,12 +343,12 @@ theorem widthGrowth_nonpos_of_length_le_absorption
   apply widthGrowth_le_of_length_le_absorption_add (C := 0)
   simpa using habsorb

-/-! ## Canonical counter candidate
+/-! ## Zero-reserve diagnostic counter

-The following counter has the exact recurrence required by the generic
-counter API.  Its nonnegativity is exactly the missing width-prefix control,
-so no certificate is constructed here: proving the local guard from the
-counter invariant itself would be circular.
+The following expression has the exact counter recurrence, but it is not a
+general certificate candidate.  Positive initial endpoint drift makes its
+credit negative immediately.  It remains useful as the exact negative of
+cumulative width growth.
 -/

 /-- Cumulative absorbed budget minus cumulative block length. -/
@@ -359,6 +391,21 @@ theorem canonicalEndpointCounterCredit_succ
   rw [canonicalBlockStartState_succ_eq_nextStartState]
   ring

+/-- After one block, zero-reserve credit is exactly negative initial drift. -/
+theorem canonicalEndpointCounterCredit_one
+    (n : OddNat) :
+    canonicalEndpointCounterCredit n 1 = -endpointAccountingTerm n 0 := by
+  rw [show 1 = 0 + 1 by omega, canonicalEndpointCounterCredit_succ]
+  simp
+
+/-- Positive initial drift refutes nonnegativity of zero-reserve credit at the
+first transition. -/
+theorem canonicalEndpointCounterCredit_one_neg_of_initialDrift_pos
+    {n : OddNat} (hpos : 0 < endpointAccountingTerm n 0) :
+    canonicalEndpointCounterCredit n 1 < 0 := by
+  rw [canonicalEndpointCounterCredit_one]
+  omega
+
 /-- The desired local guard is equivalent to nonnegativity of the next
 candidate credit.  This identifies the remaining arithmetic obligation but
 does not discharge it. -/
@@ -369,4 +416,59 @@ theorem endpointAccountingTerm_le_counterCredit_iff_next_nonneg
   rw [canonicalEndpointCounterCredit_succ]
   omega

+/-! ## Reserved endpoint credit -/
+
+/-- Root-dependent reserve plus negative cumulative canonical width growth. -/
+noncomputable def canonicalEndpointReservedCredit
+    (n : OddNat) (B M : ℕ) : ℤ :=
+  (B : ℤ) + bitWidth n.1 - bitWidth (canonicalBlockStartState n M)
+
+/-- Reserved credit starts at the supplied reserve. -/
+@[simp] theorem canonicalEndpointReservedCredit_zero
+    (n : OddNat) (B : ℕ) :
+    canonicalEndpointReservedCredit n B 0 = B := by
+  simp [canonicalEndpointReservedCredit]
+
+/-- Reserved credit has the same exact endpoint-drift recurrence as the
+zero-reserve diagnostic. -/
+theorem canonicalEndpointReservedCredit_succ
+    (n : OddNat) (B M : ℕ) :
+    canonicalEndpointReservedCredit n B (M + 1) =
+      canonicalEndpointReservedCredit n B M - endpointAccountingTerm n M := by
+  rw [canonicalEndpointReservedCredit, canonicalEndpointReservedCredit,
+    endpointAccountingTerm_eq_canonicalBlock_bitWidth_sub,
+    canonicalBlockStartState_succ_eq_nextStartState]
+  ring
+
+/-- Reserved credit is nonnegative exactly while the current canonical width
+stays inside the supplied reserve. -/
+theorem canonicalEndpointReservedCredit_nonneg_iff
+    (n : OddNat) (B M : ℕ) :
+    0 ≤ canonicalEndpointReservedCredit n B M ↔
+      bitWidth (canonicalBlockStartState n M) ≤ bitWidth n.1 + B := by
+  rw [canonicalEndpointReservedCredit]
+  omega
+
+/-- All-time nonnegativity of reserved credit is exactly the corresponding
+cumulative width bound. -/
+theorem canonicalEndpointReservedCredit_all_nonneg_iff
+    (n : OddNat) (B : ℕ) :
+    (∀ M, 0 ≤ canonicalEndpointReservedCredit n B M) ↔
+      CanonicalWidthWithinReserve n B := by
+  constructor <;> intro h M
+  · exact (canonicalEndpointReservedCredit_nonneg_iff n B M).mp (h M)
+  · exact (canonicalEndpointReservedCredit_nonneg_iff n B M).mpr (h M)
+
+/-- Existence of a finite cumulative width reserve is equivalent to existence
+of a reserve whose endpoint credit stays nonnegative for all canonical time. -/
+theorem rootwiseCanonicalWidthBound_iff_exists_reservedCredit_nonneg
+    (n : OddNat) :
+    RootwiseCanonicalWidthBound n ↔
+      ∃ B : ℕ, ∀ M, 0 ≤ canonicalEndpointReservedCredit n B M := by
+  constructor
+  · rintro ⟨B, hB⟩
+    exact ⟨B, (canonicalEndpointReservedCredit_all_nonneg_iff n B).mpr hB⟩
+  · rintro ⟨B, hB⟩
+    exact ⟨B, (canonicalEndpointReservedCredit_all_nonneg_iff n B).mp hB⟩
+
 end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointReserve.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointReserve.lean
new file mode 100644
index 00000000..ab202e6c
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointReserve.lean
@@ -0,0 +1,176 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointConservation
+import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalAllOnesDrift
+import DkMath.Collatz.PetalBridge.FloatWindow.FiniteControlCounter
+import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentScalarQueue
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointReserve"
+
+namespace DkMath.Collatz
+
+/-!
+# Canonical endpoint reserves
+
+Zero-reserve endpoint credit is an exact diagnostic, but positive initial
+drift makes it negative after one block.  A valid signed-counter certificate
+therefore needs an explicit root-dependent reserve together with an
+independently supplied cumulative width bound.
+
+This module keeps three statements separate:
+
+* no finite reserve works uniformly across every root;
+* a fixed root may or may not admit a cumulative width reserve;
+* a fixed root may or may not have bounded pointwise endpoint drift.
+
+Only the first statement is refuted here.  The second conditionally supplies a
+counter certificate and implies the third.
+-/
+
+/-! ## Zero-reserve obstruction -/
+
+/-- Odd all-ones roots make zero-reserve credit at most the negative of the
+family parameter. -/
+theorem canonicalEndpointCounterCredit_allOnesOdd_odd_one_le_neg
+    (r : ℕ) :
+    canonicalEndpointCounterCredit
+        (allOnesOdd (2 * r + 1) (by omega)) 1 ≤ -(r : ℤ) := by
+  rw [canonicalEndpointCounterCredit_one]
+  have hdrift := le_endpointAccountingTerm_allOnesOdd_odd_zero r
+  omega
+
+/-- Choosing the positive parameter `r + 1` makes zero-reserve credit strictly
+negative after the first all-ones block. -/
+theorem canonicalEndpointCounterCredit_allOnesOdd_odd_succ_one_neg
+    (r : ℕ) :
+    canonicalEndpointCounterCredit
+        (allOnesOdd (2 * (r + 1) + 1) (by omega)) 1 < 0 := by
+  apply canonicalEndpointCounterCredit_one_neg_of_initialDrift_pos
+  have hdrift := le_endpointAccountingTerm_allOnesOdd_odd_zero (r + 1)
+  omega
+
+/-- Positive initial drift excludes every core counter certificate whose
+weight and credit are definitionally the zero-reserve endpoint functions. -/
+theorem not_exists_signedCounterCertificate_zeroReserve_of_initialDrift_pos
+    {n : OddNat} (hpos : 0 < endpointAccountingTerm n 0) :
+    ¬ ∃ C : SignedCounterCertificate,
+      C.weight = (fun m => endpointAccountingTerm n m) ∧
+        C.credit = canonicalEndpointCounterCredit n := by
+  rintro ⟨C, _, hcredit⟩
+  have hnonneg := C.credit_nonneg 1
+  rw [hcredit] at hnonneg
+  have hneg := canonicalEndpointCounterCredit_one_neg_of_initialDrift_pos hpos
+  omega
+
+/-- The positive all-ones subfamily gives an explicit symbolic obstruction to
+the zero-reserve certificate. -/
+theorem not_exists_signedCounterCertificate_zeroReserve_allOnesOdd
+    (r : ℕ) :
+    ¬ ∃ C : SignedCounterCertificate,
+      C.weight = (fun m => endpointAccountingTerm
+        (allOnesOdd (2 * (r + 1) + 1) (by omega)) m) ∧
+      C.credit = canonicalEndpointCounterCredit
+        (allOnesOdd (2 * (r + 1) + 1) (by omega)) := by
+  apply not_exists_signedCounterCertificate_zeroReserve_of_initialDrift_pos
+  have hdrift := le_endpointAccountingTerm_allOnesOdd_odd_zero (r + 1)
+  omega
+
+/-! ## Conditional reserved certificate -/
+
+/-- An independently supplied cumulative width reserve instantiates the core
+signed-counter API.  This definition does not prove that such a reserve exists
+for any particular root. -/
+noncomputable def canonicalEndpointReservedCounterCertificate
+    (n : OddNat) (B : ℕ) (hB : CanonicalWidthWithinReserve n B) :
+    SignedCounterCertificate where
+  weight := endpointAccountingTerm n
+  credit := canonicalEndpointReservedCredit n B
+  initial_credit_nonneg := by simp
+  credit_succ := canonicalEndpointReservedCredit_succ n B
+  preserves_nonneg := by
+    intro m _
+    have hnext : 0 ≤ canonicalEndpointReservedCredit n B (m + 1) :=
+      (canonicalEndpointReservedCredit_nonneg_iff n B (m + 1)).mpr (hB (m + 1))
+    rw [canonicalEndpointReservedCredit_succ] at hnext
+    omega
+
+/-- Conditional counter soundness: a supplied width reserve bounds every
+prefix sum of endpoint drift by the initial reserve. -/
+theorem sum_endpointAccountingTerm_le_reserve
+    {n : OddNat} {B : ℕ} (hB : CanonicalWidthWithinReserve n B) (M : ℕ) :
+    (∑ m ∈ Finset.range M, endpointAccountingTerm n m) ≤ B := by
+  have h :=
+    (canonicalEndpointReservedCounterCertificate n B hB).sum_weight_range_le_initial_credit M
+  change (∑ m ∈ Finset.range M, endpointAccountingTerm n m) ≤
+    canonicalEndpointReservedCredit n B 0 at h
+  simpa using h
+
+/-! ## Reflected-queue audit
+
+The existing scalar queue is the maximum positive suffix drift.  Its uniform
+boundedness is therefore not an independent absorption theorem: it is another
+exact presentation of the cumulative width question.  The bridges below make
+that equivalence explicit and prevent a queue bound from being cited as though
+it had already supplied the missing arithmetic estimate.
+-/
+
+/-- Completed endpoint width of block `m` is the width at the next canonical
+block start. -/
+theorem canonicalEndpointWidth_eq_blockStartState_succ
+    (n : OddNat) (m : ℕ) :
+    canonicalEndpointWidth n m =
+      bitWidth (canonicalBlockStartState n (m + 1)) := by
+  rw [canonicalBlockStartState_succ_eq_nextStartState]
+  rfl
+
+/-- A fixed-root cumulative width reserve exists exactly when the existing
+reflected scalar queue has some uniform ceiling.  This is an equivalence of
+targets, not an independent proof that either target holds. -/
+theorem rootwiseCanonicalWidthBound_iff_exists_queueUniformUpperBound
+    (n : OddNat) :
+    RootwiseCanonicalWidthBound n ↔
+      ∃ C : ℕ, CanonicalOutstandingClaimQueueUniformUpperBound n C := by
+  constructor
+  · rintro ⟨B, hB⟩
+    have hendpoint :
+        CanonicalEndpointWidthUniformUpperBound n (bitWidth n.1 + B) := by
+      intro m
+      rw [canonicalEndpointWidth_eq_blockStartState_succ]
+      exact hB (m + 1)
+    exact ⟨bitWidth n.1 + B,
+      hendpoint.to_outstandingClaimQueueUniformUpperBound⟩
+  · rintro ⟨C, hC⟩
+    refine ⟨C, ?_⟩
+    intro M
+    cases M with
+    | zero => simp
+    | succ m =>
+        rw [← canonicalEndpointWidth_eq_blockStartState_succ]
+        exact hC.to_endpointWidthUniformUpperBound m
+
+/-! ## Global reserve obstruction -/
+
+/-- One natural reserve bounds every canonical width of every odd root. -/
+def GlobalCanonicalWidthReserveBound : Prop :=
+  ∃ B : ℕ, ∀ n : OddNat, CanonicalWidthWithinReserve n B
+
+/-- The odd all-ones initial-drift family excludes a finite reserve shared by
+all roots.  This does not address existence of a reserve for one fixed root. -/
+theorem not_globalCanonicalWidthReserveBound :
+    ¬ GlobalCanonicalWidthReserveBound := by
+  rintro ⟨B, hB⟩
+  obtain ⟨n, hdrift⟩ := exists_endpointAccountingTerm_gt (B : ℤ)
+  have hwidth := hB n 1
+  have hstart : canonicalBlockStartState n 1 =
+      canonicalBlockNextStartState n 0 := by
+    simpa using canonicalBlockStartState_succ_eq_nextStartState n 0
+  rw [hstart] at hwidth
+  have hledger := endpointAccountingTerm_eq_canonicalBlock_bitWidth_sub n 0
+  rw [canonicalBlockStartState_zero_eq_root] at hledger
+  omega
+
+end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalHighDrift.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalHighDrift.lean
index 448f5a43..6db18cbd 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalHighDrift.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalHighDrift.lean
@@ -53,6 +53,34 @@ theorem mem_canonicalHighDriftBlocksUpTo_iff_budget
   ext m
   simp

+/-- Extending the horizon by one either inserts exactly the new terminal
+index or leaves the finite carrier unchanged. -/
+theorem canonicalHighDriftBlocksUpTo_succ
+    (n : OddNat) (K M : ℕ) :
+    canonicalHighDriftBlocksUpTo n K (M + 1) =
+      if (K : ℤ) ≤ endpointAccountingTerm n M then
+        insert M (canonicalHighDriftBlocksUpTo n K M)
+      else canonicalHighDriftBlocksUpTo n K M := by
+  unfold canonicalHighDriftBlocksUpTo
+  rw [Finset.range_add_one, Finset.filter_insert]
+
+/-- Membership at horizon `M + 1` decomposes into old membership or the new
+terminal event. -/
+theorem mem_canonicalHighDriftBlocksUpTo_succ_iff
+    {n : OddNat} {K M m : ℕ} :
+    m ∈ canonicalHighDriftBlocksUpTo n K (M + 1) ↔
+      m ∈ canonicalHighDriftBlocksUpTo n K M ∨
+        (m = M ∧ (K : ℤ) ≤ endpointAccountingTerm n M) := by
+  rw [mem_canonicalHighDriftBlocksUpTo,
+    mem_canonicalHighDriftBlocksUpTo]
+  constructor <;> intro h
+  · by_cases hm : m < M
+    · exact Or.inl ⟨hm, h.2⟩
+    · exact Or.inr ⟨by omega, by simpa [show m = M by omega] using h.2⟩
+  · rcases h with h | ⟨rfl, hK⟩
+    · exact ⟨by omega, h.2⟩
+    · exact ⟨by omega, hK⟩
+
 /-- Enlarging the observed prefix only adds possible events. -/
 theorem canonicalHighDriftBlocksUpTo_mono_prefix
     (n : OddNat) (K : ℕ) {M N : ℕ} (hMN : M ≤ N) :
@@ -77,6 +105,18 @@ noncomputable def canonicalHighDriftEventCount
     (n : OddNat) (K M : ℕ) : ℕ :=
   (canonicalHighDriftBlocksUpTo n K M).card

+/-- Exact one-step event-count update for the finite observation horizon. -/
+theorem canonicalHighDriftEventCount_succ
+    (n : OddNat) (K M : ℕ) :
+    canonicalHighDriftEventCount n K (M + 1) =
+      canonicalHighDriftEventCount n K M +
+        if (K : ℤ) ≤ endpointAccountingTerm n M then 1 else 0 := by
+  unfold canonicalHighDriftEventCount
+  rw [canonicalHighDriftBlocksUpTo_succ]
+  by_cases hnew : (K : ℤ) ≤ endpointAccountingTerm n M
+  · simp [hnew, canonicalHighDriftBlocksUpTo]
+  · simp [hnew]
+
 /-- Event count is monotone in the finite observation horizon. -/
 theorem canonicalHighDriftEventCount_mono_prefix
     (n : OddNat) (K : ℕ) {M N : ℕ} (hMN : M ≤ N) :
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-342.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-342.md
new file mode 100644
index 00000000..b7b7aada
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-342.md
@@ -0,0 +1,274 @@
+# Petal / FloatWindow implementation report: checkpoint 342
+
+## Status
+
+Checkpoint 342 is implemented without adding `sorry`.
+
+This checkpoint corrects the interpretation of the endpoint counter introduced
+at checkpoint 341.  The zero-reserve credit is not merely awaiting a local
+preservation lemma.  It is refuted as a general signed-counter certificate by
+every root whose first canonical endpoint drift is positive.
+
+The corrected API separates three different questions:
+
+1. whether one reserve works uniformly for every root;
+2. whether one fixed root has bounded cumulative canonical width;
+3. whether one fixed root has bounded pointwise endpoint drift.
+
+The first statement is false.  The second and third remain open for a general
+fixed root, and the second is strictly the stronger target in the current API.
+
+## Corrected zero-reserve diagnosis
+
+The duplicate initial block-state theorem was removed from
+`CanonicalAllOnesDrift.lean`.  The all-ones proofs now use the generic theorem
+
+```text
+canonicalBlockStartState_zero_eq_root.
+```
+
+For the zero-reserve endpoint credit, Lean now proves the exact first-step
+identity
+
+```text
+canonicalEndpointCounterCredit n 1
+  = - endpointAccountingTerm n 0.
+```
+
+Therefore positive initial drift gives strictly negative credit after one
+transition.  This is a counterexample to the required nonnegativity invariant,
+not an unproved guard.
+
+The odd all-ones family makes the failure symbolic:
+
+```text
+credit(allOnesOdd(2*r+1), 1) <= -r.
+```
+
+Using the positive parameter `r + 1` gives strict negativity.  The new reserve
+module consequently proves that no `SignedCounterCertificate` can have both
+
+```text
+weight := endpointAccountingTerm n
+credit := canonicalEndpointCounterCredit n
+```
+
+when the initial endpoint drift is positive.  An explicit no-certificate
+theorem is also provided for the positive all-ones subfamily.
+
+## Cumulative width reserve
+
+The new predicate
+
+```text
+CanonicalWidthWithinReserve n B
+```
+
+states that every canonical block-start width is at most the root width plus
+`B`.  Its existential fixed-root form is
+
+```text
+RootwiseCanonicalWidthBound n.
+```
+
+Lean proves the one-way implication
+
+```text
+RootwiseCanonicalWidthBound n
+  -> RootwiseEndpointDriftBound n.
+```
+
+The reason is structural: each endpoint drift is one difference between two
+successive widths, while the cumulative predicate bounds every absolute width
+level.  A bound on all cumulative levels bounds every positive increment.
+
+No reverse implication is proved or claimed.  Uniformly bounded one-step
+increments do not, by themselves, bound the cumulative level.
+
+## Reserved credit and conditional certificate
+
+The corrected endpoint credit is
+
+```text
+reservedCredit(n, B, M)
+  = B + rootWidth - blockStartWidth(M).
+```
+
+Lean proves:
+
+- initial reserved credit is exactly `B`;
+- its successor recurrence subtracts the exact endpoint drift;
+- its nonnegativity is equivalent to the current width being inside reserve;
+- all-time nonnegativity is equivalent to `CanonicalWidthWithinReserve n B`;
+- existence of such a reserve is equivalent to
+  `RootwiseCanonicalWidthBound n`.
+
+An explicit width-bound hypothesis now constructs
+
+```text
+canonicalEndpointReservedCounterCertificate.
+```
+
+This is a conditional certificate.  It does not prove that a reserve exists
+for any particular root.  Under that hypothesis, the generic counter theorem
+does prove the finite prefix estimate
+
+```text
+sum(endpointAccountingTerm, [0, M)) <= B.
+```
+
+## Global reserve obstruction
+
+The predicate
+
+```text
+GlobalCanonicalWidthReserveBound
+```
+
+asks for one natural reserve that works for every odd root.  Lean proves its
+negation.  The existing all-ones family supplies roots with initial endpoint
+drift larger than any proposed reserve, so the width bound already fails at
+the first completed block.
+
+This theorem does not refute a root-dependent reserve.  The quantifier order is
+essential:
+
+```text
+not (exists B, forall n, widthBound n B)
+```
+
+does not imply
+
+```text
+forall n, not (exists B, widthBound n B).
+```
+
+## Reflected-queue audit
+
+The existing scalar queue is exactly the maximum positive signed suffix drift.
+Checkpoint 342 adds the direct block-coordinate bridge
+
+```text
+canonicalEndpointWidth n m
+  = bitWidth (canonicalBlockStartState n (m + 1)).
+```
+
+It then proves
+
+```text
+RootwiseCanonicalWidthBound n
+  iff
+exists C, CanonicalOutstandingClaimQueueUniformUpperBound n C.
+```
+
+This is useful, but it does not close the width problem.  The queue theorem is
+an exact reformulation of the same cumulative boundedness target.  Existing
+queue, source-age, claim-hole, and terminal-valuation bridges do not currently
+supply an independent lower bound preventing arbitrarily long positive suffix
+drift.
+
+The required next input remains genuinely arithmetic or dynamical, such as:
+
+- an absorption lower bound for claim holes plus terminal valuation relative
+  to block length;
+- a uniform repayment-lag theorem;
+- exclusion of a pumpable positive-drift transition cycle; or
+- a finite-state discharge theorem independent of the desired width bound.
+
+Defining another credit as the negative of the target invariant would only
+rename this obstruction.
+
+## Pointwise endpoint branch remains open
+
+The exact fixed-root pointwise question is still
+
+```text
+exists B, forall m,
+  blockLength n m
+    <= claimHoles n m + terminalValuation n m + B.
+```
+
+This is equivalent to `RootwiseEndpointDriftBound n`.  It is weaker than the
+cumulative width-reserve question and must not be replaced by it.
+
+No independent uniform lower bound on
+
+```text
+claimHoles + terminalValuation
+```
+
+relative to block length was found in the queue audit.  The exact conservation
+identity remains the correct local surface for that search.
+
+## Finite high-drift increments
+
+`CanonicalHighDrift.lean` now gives an exact successor description of the
+finite event carrier.  Extending the horizon from `M` to `M + 1` either inserts
+the new index `M` or leaves the carrier unchanged, according to whether the new
+drift reaches threshold `K`.
+
+The corresponding membership theorem is
+
+```text
+m in events(M + 1)
+  iff m in events(M) or (m = M and K <= drift(M)).
+```
+
+The event count therefore satisfies the exact finite update
+
+```text
+eventCount(M + 1)
+  = eventCount(M) + if K <= drift(M) then 1 else 0.
+```
+
+These are finite prefix statements only.  They do not imply infinitely many
+events, eventual stabilization, or a finite all-time event count.
+
+## Scaled conservation clarification
+
+The existing `A`-scaled conservation theorem is now documented as algebraic
+transport of the exact integer identity.  The parameter `A` is not yet a
+spiral-growth coefficient, and no logarithmic or asymptotic interpretation is
+introduced in this module.
+
+## Facts fixed by Lean
+
+1. Zero-reserve credit equals negative initial drift after one block.
+2. Positive initial drift makes the zero-reserve certificate impossible.
+3. The all-ones family gives symbolic, arbitrarily large first-step failure.
+4. No finite reserve works uniformly over every odd root.
+5. A supplied fixed-root cumulative width reserve gives a valid signed counter.
+6. Cumulative width boundedness implies pointwise endpoint-drift boundedness.
+7. No converse implication has been established.
+8. Fixed-root width boundedness is equivalent to uniform reflected-queue
+   boundedness, so the queue does not independently solve the target.
+9. Finite high-drift carriers and their counts have exact one-step updates.
+10. The fixed-root pointwise endpoint bound remains a separate open branch.
+
+## Branch decision
+
+The zero-reserve branch is closed negatively.  It must not be retried as a
+certificate without changing its initial reserve.
+
+The reserved-credit branch is complete as a conditional API.  Its remaining
+premise is exactly fixed-root cumulative width boundedness, now also identified
+with reflected-queue boundedness.
+
+The next productive branch should seek an independent absorption or discharge
+theorem.  Until that input is proved, neither the cumulative width reserve nor
+the weaker pointwise endpoint bound should be promoted to an unconditional
+theorem.
+
+## Verification
+
+The checkpoint was checked with targeted and aggregate builds:
+
+```text
+lake build DkMath.Collatz.PetalBridge.FloatWindow.CanonicalHighDrift
+lake build DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointReserve
+lake build DkMath.Collatz.PetalBridge.FloatWindow
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath
+git diff --check
+```
+
````
`````
