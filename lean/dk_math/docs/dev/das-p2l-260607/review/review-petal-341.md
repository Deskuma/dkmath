# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointConservation, CanonicalHighDrift

gch: d8efe29aaa2495112ad3262721650bd119c1737f

## Report

(13m1s)

cp-341 を完了しました。

- ブロック保存則 `drift + holes + valuation = length` を直接定理化しました。[CanonicalEndpointDrift.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointDrift.lean:121)
- 有限窓保存則、幅テレスコープ、閾値同値、rootwise boundedness の構造的同値を証明しました。[CanonicalEndpointConservation.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointConservation.lean:93)
- 有限 high-drift carrier と単調性・反単調性を追加しました。[CanonicalHighDrift.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalHighDrift.lean:23)
- counter 証明を一般的な `SignedCounterCertificate` へ分離しました。[FiniteControlCounter.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteControlCounter.lean:30)
- 有限数値監査と正確な停止理由を [report-petal-341.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-341.md:3) に記録しました。

確定した核心事実は、endpoint drift がブロック長から claim holes と terminal valuation を除いた**正確な残余**であり、この保存則が任意の有限シフト窓でも成立することです。

一方、canonical credit の非負性は「現在幅が初期幅以下」と同値でした。
したがって、これを local guard に使うと目的命題の言い換えになり循環します。
canonical certificate の構築と rootwise boundedness の結論は、ここでは正しく保留しています。

検証済み:

- 対象3モジュール
- `DkMath.Collatz.PetalBridge.FloatWindow`
- `DkMath.Collatz.PetalBridge`
- `DkMath`
- `git diff --check`
- 変更対象に新規 `sorry` なし

## Review

(4m55s)

# cp-341 実装レビュー

## 総合判定

**実装本体は採用。**

cp-341 は、cp-340 の一ブロック保存式を任意の有限窓へ持ち上げ、

$$\text{WidthGrowth}+\text{ClaimHoles}+\text{TerminalValuation}=\text{BlockLength}$$

を exact cumulative law として確立した。

さらに、

- high-drift の exact finite carrier
- rootwise boundedness の吸収構造による同値変形
- finite control と counter soundness の分離
- canonical counter candidate の exact recurrence

まで、すべて筋が通っている。

ただし、**canonical zero-credit candidate の解釈に一か所、重要な補正が必要**じゃ。

> local guard がまだ見つからない

だけではない。

この候補は、正 driftを持つ root に対して **実際に非負性が破れる**。したがって一般 canonical certificate 候補としては、未証明ではなく反例によって退けられている。

これはコードの誤りではない。停止判断は正しい。だが report の次分岐を一段強く書き換える必要がある。

---

## 一ブロック保存則

中心定理、

```lean
endpointAccountingTerm_add_claimHoles_add_terminalValuation_eq_blockLength
```

は望んだ形そのものじゃ。

$$\Delta_n(m)+H_n(m)+V_n(m)=L_n(m)$$

全項を `Int` に置いているため、負 driftも情報を失わず保存されている。既存の rearranged theoremも新しい主定理から導く向きへ変更され、API の中心が正しく入れ替わった。

意味としては、

```text
BlockLength
  = realized signed drift
  + unrealized claim depths
  + terminal 2-adic absorption
```

じゃ。

これは cp-341 の最重要成果として全面採用。

---

## 有限窓保存則

四種類の window sum を `[q,q+M)` で統一した設計は良い。

- drift
- claim holes
- terminal valuation
- block length

空窓と singleton が明示され、一般保存則が一ブロック保存則の `Finset.sum` として素直に証明されている。

特に shifted telescope、

$$\sum_{i<M}\Delta_n(q+i)=w_n(q+M)-w_n(q)$$

が exact に閉じたことが大きい。

これと budget conservation の合流により、

$$w_n(q+M)-w_n(q)+\sum_{i<M}H_n(q+i)+\sum_{i<M}V_n(q+i)=\sum_{i<M}L_n(q+i)$$

が任意の有限 shifted windowで成立した。

これは「螺旋の各回転で、伸びた半径と吸収された余剰を合計すると、投入された全 block lengthへ戻る」という exact ledger じゃ。

---

## High-drift threshold

自然数閾値 $K$ に対する、

$$K\le\Delta_n(m)\iff K+H_n(m)+V_n(m)\le L_n(m)$$

は exact equivalence になっている。

そこから、

- high driftなら block lengthも長い
- high driftなら combined absorption は $L-K$ 以下
- fixed root で driftが非有界なら block lengthも非有界

が正しく導かれている。逆は主張されていない。

この結果により、高 drift の正体は、

> 長い block のうち、holesにも valuationにも吸収されなかった残余

として完全に固定された。

---

## Rootwise boundedness の構造的同値

次の theorem も正確じゃ。

```lean
rootwiseEndpointDriftBound_iff_length_le_absorption_add
```

$$\operatorname{RootwiseBound}(n)\iff\exists B,\ \forall m,\ L_n(m)\le H_n(m)+V_n(m)+B$$

これは fixed-root 問題を解いたわけではないが、問題を exact に整地した。

つまり今後探すべきものは、block length 単独の上界とは限らない。

$$L_n(m)-\bigl(H_n(m)+V_n(m)\bigr)$$

が固定 root 上で一様有界であればよい。

これは以前よりかなり狭く、正確な Gap じゃ。

---

## Scaled absorption theorem

`canonicalEndpointWidthBudgetWindow_conservation_mul` と、その inequality 版は代数的に正しい。係数 $A$ に符号仮定がなくても、仮定そのものがすでに $A$ 倍された不等式なので theorem は成立する。

ただし、これは現段階では**成長係数の発見ではない**。

同じ $A$ を length、holes、valuationの全項へ掛けているため、保存式のスケール移送であり、$A$ は本質的には消去可能じゃ。

したがって report 上では、

```text
scaled exact transport law
```

と読むのが正確で、

```text
spiral growth coefficient estimate
```

とまでは呼ばない方がよい。

本物の係数 theorem には、異なる重みを持つ算術評価か、block構造からの外部不等式が必要になる。

---

## High-drift finite carrier

```lean
canonicalHighDriftBlocksUpTo n K M
```

は、有限診断器として正しく作られている。

membership theorem、budget形への同値、観測 horizon に対する単調性、threshold に対する反単調性、event count版まで揃っている。

末尾で、

- 全時間 union
- eventual stabilization
- event総数の有限性
- fixed-root repeated high drift

を推論していないことも明記されている。

ここは完全採用。

---

## Counter API の分離

`SignedCounterCertificate` を arithmetic core として分離した判断も正しい。

```lean
weight
credit
initial_credit_nonneg
credit_succ
preserves_nonneg
```

だけで、

$$\sum_{m<M}w(m)=C(0)-C(M)$$

$$\sum_{m<M}w(m)\le C(0)$$

を得ている。

finite signatureは soundnessには不要であり、観測層として wrapper側へ残された。既存 API は core certificateへ射影して再利用されている。

cp-340 で露出した、

```text
finite control は証明力の核ではない
```

という事実を、そのまま API 構造へ反映できている。

---

## 重要補正：canonical zero-credit candidate は反例済み

定義された credit は、

$$C_n(M)=\sum_{i<M}H_n(i)+\sum_{i<M}V_n(i)-\sum_{i<M}L_n(i)$$

であり、Lean は、

$$C_n(M)=w_n(0)-w_n(M)$$

を証明している。

また、

$$C_n(M+1)=C_n(M)-\Delta_n(M)$$

も exact。

ここまでは非常に良い。

しかし $C_n(0)=0$ なので、

$$C_n(1)=-\Delta_n(0)$$

となる。

したがって初期 drift が正である rootでは、

$$\Delta_n(0)>0\Longrightarrow C_n(1)<0$$

じゃ。

all-ones 族だけでも、任意に大きな正の初期 driftを持つ root が既に theorem で存在する。有限監査にも `511` の drift $5$、`2047` の drift $6$ などが記録されている。

ゆえに、

```lean
preserves_nonneg :
  0 ≤ credit M → endpointAccountingTerm n M ≤ credit M
```

は、一般 rootについて単に「まだ証明されていない」のではない。

$M=0$ で、

```text
positive initial drift ≤ 0
```

を要求するため、**偽であることが既に分かっている**。

`endpointAccountingTerm_le_counterCredit_iff_next_nonneg` 自体は正確で、この失敗を露出する良い診断 theorem になっている。

### 正しい評価

```text
誤：
独立 arithmetic guard がまだ得られていない

正：
zero-reserve canonical credit の guard は一般 root では成立しない
したがって、この候補による一般 certificate は反例済み
```

循環を避けて certificate を作らなかった判断は正しい。
さらに一歩進めて、**候補そのものが一般解ではない**と theorem 化できる。

---

## reserve を加えた場合

一般初期 creditを許す API を作ったので、自然な修正版は、

$$C_{n,B}(M)=B+w_n(0)-w_n(M)$$

じゃ。

このとき、

$$C_{n,B}(0)=B$$

$$C_{n,B}(M+1)=C_{n,B}(M)-\Delta_n(M)$$

となる。

非負性は、

$$w_n(M)\le w_n(0)+B$$

と同値になる。

ただし、これは `RootwiseEndpointDriftBound` そのものではない。

```text
RootwiseEndpointDriftBound：
各一手の width increment が bounded

RootwiseCumulativeWidthBound：
軌道の width 全体が初期 width + B 以下
```

後者の方が強い。

軌道 width が一様有界なら、各 incrementも当然有界になる。だが各 incrementが有界でも、正 incrementが累積すれば width全体は伸び得るため、逆は現在の theoremからは出ない。

ここは次 checkpoint で別 predicate として分離する価値が高い。

---

## 初期 state lemma の重複

新しい、

```lean
@[simp] theorem canonicalBlockStartState_zero_eq_root
```

は命名・配置とも良い。

ただし `CanonicalAllOnesDrift.lean` には、旧 theorem、

```lean
canonicalBlockStartState_zero
```

が同じ証明内容で残っており、all-ones 側もまだ旧名を使っている。

これは意味上のバグではないが、今回の昇格を完了させるには、

- 旧 theorem を削除
- all-ones theorem を `canonicalBlockStartState_zero_eq_root` または `simp` で証明

へ整理するべきじゃ。

---

## 有限監査の読み方

report の監査は正直に書かれている。

特に、

```text
root 2047:
  block 19 drift 4, credit before 4
  block 21 drift 2, credit before -5

root 4095:
  block 18 drift 4, credit before 5
  block 19 drift 2, credit before -4
```

という観測は重要じゃ。

これは、

> 正 drift が現れる前に、常に現在の zero-reserve credit が十分ある

という素朴な guard が、有限観測上も成り立たないことを示す。

したがって、次に探すべき credit は単純な負 cumulative widthではない。

候補は少なくとも、

- root依存の初期 reserveを持つ width credit
- reflected queue や source-age deficitを含む別資源
- running baselineを更新する counter
- block内部の payment ownershipを保持する複合 counter

のいずれかになる。

---

## cp-341 判定一覧

### Block conservation

**完成。**

### Shifted finite-window conservation

**完成。**

### Width telescope

**完成。**

### High-drift threshold equivalence

**完成。**

### Rootwise structural restatement

**完成。**

### Finite high-drift carrier

**完成。**

### Counter API factoring

**完成。**

### Canonical zero-credit recurrence

**完成。診断式として有効。**

### Canonical zero-credit certificate

**一般 rootでは反例済み。保留ではなく棄却。**

### Rootwise endpoint bound

**未解決。**

### Fixed-root cumulative width bound

**未定義・未解決。次に分離すべき命題。**

### 循環性

**なし。**

### コード整理

**旧 `canonicalBlockStartState_zero` の重複除去が必要。**

## 総合

**採用。ただし report の branch interpretation は修正必須。**

cp-341 の保存則層は強い。
canonical credit の失敗も、失敗ではなく盤面を一つ狭めた exact negative result じゃ。

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge FloatWindow branch after
report-petal-341.

Checkpoint 341 is accepted, with one substantive interpretation correction:

The zero-reserve canonical endpoint credit is not merely waiting for an
independent preservation guard.  Its preservation guard is false for roots
with positive initial endpoint drift.  Treat this candidate as a diagnostic
counterexample, not as an open certificate candidate.

Stage A — remove the duplicate initial-state theorem

`CanonicalEndpointDrift.lean` now exports:

    @[simp] canonicalBlockStartState_zero_eq_root

Remove the older duplicate:

    canonicalBlockStartState_zero

from `CanonicalAllOnesDrift.lean`.

Update the all-ones initial-state proof to use the generic theorem or `simp`.

Stage B — formalize failure of the zero-reserve candidate

Prove:

    canonicalEndpointCounterCredit n 1
      = - endpointAccountingTerm n 0

and:

    0 < endpointAccountingTerm n 0
      -> canonicalEndpointCounterCredit n 1 < 0.

For the odd all-ones family, derive a symbolic negative-credit theorem, for
example:

    canonicalEndpointCounterCredit
      (allOnesOdd (2*r+1) ...) 1 <= -(r : Int).

For a positive parameter such as `r+1`, derive strict negativity.

State explicitly that no `SignedCounterCertificate` using:

    weight := endpointAccountingTerm n
    credit := canonicalEndpointCounterCredit n

can exist for those roots.

Do not phrase this as a missing guard.  The guard is false.

Stage C — separate pointwise drift boundedness from cumulative width boundedness

Define a new predicate with a clear name, for example:

    RootwiseCanonicalWidthBound n :=
      exists B : Nat, forall M,
        bitWidth (canonicalBlockStartState n M)
          <= bitWidth n.1 + B

or an equivalent stable `Int` formulation.

Prove:

    RootwiseCanonicalWidthBound n
      -> RootwiseEndpointDriftBound n.

Do not prove or claim the converse.

Document the logical hierarchy:

    cumulative width bound
      -> pointwise endpoint-drift bound

with no reverse implication currently available.

Stage D — reserved endpoint credit

Define:

    canonicalEndpointReservedCredit n B M
      := B + bitWidth n.1
           - bitWidth (canonicalBlockStartState n M)

over `Int`, with an appropriate nonnegative reserve hypothesis.

Prove:

    initial credit = B;
    exact successor recurrence;
    nonnegative credit iff the current width is within the reserve;
    all-time nonnegative reserved credit iff the corresponding cumulative
      width bound.

Instantiate `SignedCounterCertificate` only under an explicit independently
supplied width-bound hypothesis.

This is a conditional API, not a proof that any fixed root has such a reserve.

Stage E — global reserve obstruction

Use the existing all-ones initial-drift family to show that no one finite
reserve works uniformly for every root.

Keep this distinct from the fixed-root reserve question.

Stage F — preserve the exact rootwise endpoint branch

The exact fixed-root endpoint question remains:

    exists B, forall m,
      blockLength n m
        <= claimHoles n m + terminalValuation n m + B.

Search for independent arithmetic lower bounds on:

    claimHoles + terminalValuation

relative to block length.

Do not replace this pointwise question by the stronger cumulative width-bound
question.

Stage G — high-drift event increments

For `canonicalHighDriftBlocksUpTo`, add an exact successor/event-count theorem:

    eventCount n K (M+1)
      =
    eventCount n K M
      + indicator (K <= drift M).

Add the corresponding membership decomposition for horizon `M+1`.

Keep all statements finite.

Stage H — audit possible queue bridges

Investigate exact existing relations among:

    endpointAccountingTerm;
    canonical scalar/reflected queue change;
    claim holes;
    terminal valuation;
    source-age deficit.

The target is an independently proved resource recurrence or absorption lower
bound.

Do not define a new credit merely as the negation of the desired theorem.

Stage I — clarify scaled conservation

Document that the current `A`-scaled theorem is an algebraic transport of the
exact conservation identity, not yet a spiral-growth coefficient theorem.

Add a nonnegative-`A` caller-facing corollary only if it improves later use.
Do not introduce logarithmic language into this module.

Stage J — report correction

In `report-petal-342.md`, state:

    the zero-reserve endpoint credit is refuted as a general certificate by
    positive initial drift;

not merely:

    no independent guard was found.

Keep these three questions visibly separate:

    global reserve;
    fixed-root cumulative width reserve;
    fixed-root pointwise endpoint-drift bound.

Stopping rule

Stop at the first genuine obstruction among:

    the all-ones negative-credit theorem does not follow from the current
    drift lower bound;

    the reserved-credit recurrence changes the intended weight;

    cumulative width boundedness fails to imply pointwise drift boundedness;

    a queue bridge requires the target invariant as an assumption;

    finite high-drift observations are promoted to an all-time theorem.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-342.md
```

cp-341 で盤面はさらに明瞭になった。

$$\boxed{\text{BlockLength}=\text{Drift}+\text{Holes}+\text{Valuation}}$$

そして zero-credit の石は置けないことも分かった。
次は、**局所宇宙ごとの reserve と、一手ごとの drift ceiling を別の地として囲う段階**じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
index da4b2d9c..ea835388 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
@@ -39,6 +39,8 @@ import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeFlow
 import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeHorizon
 import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeFiniteCertificate
 import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointDrift
+import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointConservation
+import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalHighDrift
 import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalAllOnesDrift
 import DkMath.Collatz.PetalBridge.FloatWindow.RawLowSignatureObstruction
 
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointConservation.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointConservation.lean
new file mode 100644
index 00000000..c8eec04b
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointConservation.lean
@@ -0,0 +1,372 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointDrift
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointConservation"
+
+namespace DkMath.Collatz
+
+/-!
+# Cumulative canonical endpoint conservation
+
+The block identity
+
+`drift + claim holes + terminal valuation = block length`
+
+is summed here over half-open block windows `[q, q + M)`.  The half-open
+convention makes the empty and singleton windows definitional and aligns the
+drift sum with the width difference between block starts `q` and `q + M`.
+-/
+
+/-! ## Window ledgers -/
+
+/-- Total signed endpoint drift over blocks `[q, q + M)`. -/
+noncomputable def canonicalEndpointDriftWindowSum
+    (n : OddNat) (q M : ℕ) : ℤ :=
+  ∑ i ∈ Finset.range M, endpointAccountingTerm n (q + i)
+
+/-- Total claim-hole absorption over blocks `[q, q + M)`. -/
+noncomputable def canonicalClaimHolesWindowSum
+    (n : OddNat) (q M : ℕ) : ℤ :=
+  ∑ i ∈ Finset.range M, ((canonicalBlockClaimHoles n (q + i)).card : ℤ)
+
+/-- Total terminal-valuation absorption over blocks `[q, q + M)`. -/
+noncomputable def canonicalTerminalValuationWindowSum
+    (n : OddNat) (q M : ℕ) : ℤ :=
+  ∑ i ∈ Finset.range M, (canonicalBlockTerminalValuation n (q + i) : ℤ)
+
+/-- Total block-length budget over blocks `[q, q + M)`. -/
+noncomputable def canonicalBlockLengthWindowSum
+    (n : OddNat) (q M : ℕ) : ℤ :=
+  ∑ i ∈ Finset.range M, (canonicalBlockLength n (q + i) : ℤ)
+
+@[simp] theorem canonicalEndpointDriftWindowSum_zero
+    (n : OddNat) (q : ℕ) :
+    canonicalEndpointDriftWindowSum n q 0 = 0 := by
+  simp [canonicalEndpointDriftWindowSum]
+
+@[simp] theorem canonicalClaimHolesWindowSum_zero
+    (n : OddNat) (q : ℕ) :
+    canonicalClaimHolesWindowSum n q 0 = 0 := by
+  simp [canonicalClaimHolesWindowSum]
+
+@[simp] theorem canonicalTerminalValuationWindowSum_zero
+    (n : OddNat) (q : ℕ) :
+    canonicalTerminalValuationWindowSum n q 0 = 0 := by
+  simp [canonicalTerminalValuationWindowSum]
+
+@[simp] theorem canonicalBlockLengthWindowSum_zero
+    (n : OddNat) (q : ℕ) :
+    canonicalBlockLengthWindowSum n q 0 = 0 := by
+  simp [canonicalBlockLengthWindowSum]
+
+@[simp] theorem canonicalEndpointDriftWindowSum_one
+    (n : OddNat) (q : ℕ) :
+    canonicalEndpointDriftWindowSum n q 1 = endpointAccountingTerm n q := by
+  simp [canonicalEndpointDriftWindowSum]
+
+@[simp] theorem canonicalClaimHolesWindowSum_one
+    (n : OddNat) (q : ℕ) :
+    canonicalClaimHolesWindowSum n q 1 =
+      ((canonicalBlockClaimHoles n q).card : ℤ) := by
+  simp [canonicalClaimHolesWindowSum]
+
+@[simp] theorem canonicalTerminalValuationWindowSum_one
+    (n : OddNat) (q : ℕ) :
+    canonicalTerminalValuationWindowSum n q 1 =
+      (canonicalBlockTerminalValuation n q : ℤ) := by
+  simp [canonicalTerminalValuationWindowSum]
+
+@[simp] theorem canonicalBlockLengthWindowSum_one
+    (n : OddNat) (q : ℕ) :
+    canonicalBlockLengthWindowSum n q 1 =
+      (canonicalBlockLength n q : ℤ) := by
+  simp [canonicalBlockLengthWindowSum]
+
+/-! ## Exact window conservation -/
+
+/-- Every finite block window conserves its complete length budget. -/
+theorem canonicalEndpointBudgetWindow_conservation
+    (n : OddNat) (q M : ℕ) :
+    canonicalEndpointDriftWindowSum n q M +
+          canonicalClaimHolesWindowSum n q M +
+        canonicalTerminalValuationWindowSum n q M =
+      canonicalBlockLengthWindowSum n q M := by
+  unfold canonicalEndpointDriftWindowSum canonicalClaimHolesWindowSum
+    canonicalTerminalValuationWindowSum canonicalBlockLengthWindowSum
+  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
+  apply Finset.sum_congr rfl
+  intro i hi
+  exact
+    endpointAccountingTerm_add_claimHoles_add_terminalValuation_eq_blockLength
+      n (q + i)
+
+/-- The empty window is the zero instance of the conservation law. -/
+theorem canonicalEndpointBudgetWindow_conservation_empty
+    (n : OddNat) (q : ℕ) :
+    canonicalEndpointDriftWindowSum n q 0 +
+          canonicalClaimHolesWindowSum n q 0 +
+        canonicalTerminalValuationWindowSum n q 0 =
+      canonicalBlockLengthWindowSum n q 0 := by
+  simp
+
+/-- The singleton window recovers the primary block conservation law. -/
+theorem canonicalEndpointBudgetWindow_conservation_singleton
+    (n : OddNat) (q : ℕ) :
+    canonicalEndpointDriftWindowSum n q 1 +
+          canonicalClaimHolesWindowSum n q 1 +
+        canonicalTerminalValuationWindowSum n q 1 =
+      canonicalBlockLengthWindowSum n q 1 := by
+  simpa using
+    endpointAccountingTerm_add_claimHoles_add_terminalValuation_eq_blockLength
+      n q
+
+/-- Shifted endpoint telescope: drift on `[q, q + M)` is exactly the width
+change between the two canonical block starts. -/
+theorem canonicalEndpointDriftWindowSum_eq_startState_bitWidth_sub
+    (n : OddNat) (q M : ℕ) :
+    canonicalEndpointDriftWindowSum n q M =
+      (bitWidth (canonicalBlockStartState n (q + M)) : ℤ) -
+        bitWidth (canonicalBlockStartState n q) := by
+  unfold canonicalEndpointDriftWindowSum
+  induction M with
+  | zero => simp
+  | succ M ih =>
+      rw [Finset.sum_range_succ, ih,
+        endpointAccountingTerm_eq_canonicalBlock_bitWidth_sub]
+      rw [show q + (M + 1) = (q + M) + 1 by omega,
+        canonicalBlockStartState_succ_eq_nextStartState]
+      ring
+
+/-- Prefix telescope ending at the start of block `M`. -/
+theorem canonicalEndpointDriftPrefixSum_eq_startState_bitWidth_sub
+    (n : OddNat) (M : ℕ) :
+    canonicalEndpointDriftWindowSum n 0 M =
+      (bitWidth (canonicalBlockStartState n M) : ℤ) - bitWidth n.1 := by
+  simpa using
+    canonicalEndpointDriftWindowSum_eq_startState_bitWidth_sub n 0 M
+
+/-- Width growth plus the two cumulative absorption channels equals the
+cumulative block-length budget on every shifted window. -/
+theorem canonicalEndpointWidthBudgetWindow_conservation
+    (n : OddNat) (q M : ℕ) :
+    ((bitWidth (canonicalBlockStartState n (q + M)) : ℤ) -
+          bitWidth (canonicalBlockStartState n q)) +
+          canonicalClaimHolesWindowSum n q M +
+        canonicalTerminalValuationWindowSum n q M =
+      canonicalBlockLengthWindowSum n q M := by
+  rw [← canonicalEndpointDriftWindowSum_eq_startState_bitWidth_sub]
+  exact canonicalEndpointBudgetWindow_conservation n q M
+
+/-- Prefix form of cumulative endpoint conservation. -/
+theorem canonicalEndpointWidthBudgetPrefix_conservation
+    (n : OddNat) (M : ℕ) :
+    ((bitWidth (canonicalBlockStartState n M) : ℤ) - bitWidth n.1) +
+          canonicalClaimHolesWindowSum n 0 M +
+        canonicalTerminalValuationWindowSum n 0 M =
+      canonicalBlockLengthWindowSum n 0 M := by
+  simpa using canonicalEndpointWidthBudgetWindow_conservation n 0 M
+
+/-! ## Exact high-drift thresholds -/
+
+/-- A natural drift threshold is met exactly when block length covers that
+threshold together with both absorption channels. -/
+theorem natCast_le_endpointAccountingTerm_iff
+    (n : OddNat) (m K : ℕ) :
+    (K : ℤ) ≤ endpointAccountingTerm n m ↔
+      (K : ℤ) + ((canonicalBlockClaimHoles n m).card : ℤ) +
+          (canonicalBlockTerminalValuation n m : ℤ) ≤
+        (canonicalBlockLength n m : ℤ) := by
+  have hbudget :=
+    endpointAccountingTerm_add_claimHoles_add_terminalValuation_eq_blockLength
+      n m
+  constructor <;> intro h <;> omega
+
+/-- High realized drift requires a block at least as long as the threshold. -/
+theorem blockLength_ge_of_endpointAccountingTerm_ge
+    {n : OddNat} {m K : ℕ}
+    (h : (K : ℤ) ≤ endpointAccountingTerm n m) :
+    K ≤ canonicalBlockLength n m := by
+  have hthreshold := (natCast_le_endpointAccountingTerm_iff n m K).mp h
+  omega
+
+/-- High realized drift leaves at most `length - K` for the combined exact
+absorption.  The conclusion remains in `Int` to avoid truncated subtraction. -/
+theorem combinedAbsorption_le_length_sub_of_endpointAccountingTerm_ge
+    {n : OddNat} {m K : ℕ}
+    (h : (K : ℤ) ≤ endpointAccountingTerm n m) :
+    ((canonicalBlockClaimHoles n m).card : ℤ) +
+        (canonicalBlockTerminalValuation n m : ℤ) ≤
+      (canonicalBlockLength n m : ℤ) - K := by
+  have hthreshold := (natCast_le_endpointAccountingTerm_iff n m K).mp h
+  omega
+
+/-- If one fixed root has arbitrarily high endpoint drift, its canonical
+block lengths are necessarily unbounded.  No converse is asserted. -/
+theorem blockLength_unbounded_of_endpointAccountingTerm_unbounded
+    {n : OddNat}
+    (h : ∀ K : ℕ, ∃ m, (K : ℤ) ≤ endpointAccountingTerm n m) :
+    ∀ K : ℕ, ∃ m, K ≤ canonicalBlockLength n m := by
+  intro K
+  obtain ⟨m, hm⟩ := h K
+  exact ⟨m, blockLength_ge_of_endpointAccountingTerm_ge hm⟩
+
+/-! ## Rootwise structural restatement -/
+
+/-- Rootwise drift boundedness is exactly a uniform additive absorption
+estimate.  This theorem only reforms the fixed-root question; it does not
+provide the bound. -/
+theorem rootwiseEndpointDriftBound_iff_length_le_absorption_add
+    (n : OddNat) :
+    RootwiseEndpointDriftBound n ↔
+      ∃ B : ℤ, ∀ m,
+        (canonicalBlockLength n m : ℤ) ≤
+          ((canonicalBlockClaimHoles n m).card : ℤ) +
+            (canonicalBlockTerminalValuation n m : ℤ) + B := by
+  constructor
+  · rintro ⟨B, hB⟩
+    refine ⟨B, ?_⟩
+    intro m
+    have hbudget :=
+      endpointAccountingTerm_add_claimHoles_add_terminalValuation_eq_blockLength
+        n m
+    have hdrift := hB m
+    omega
+  · rintro ⟨B, hB⟩
+    refine ⟨B, ?_⟩
+    intro m
+    have hbudget :=
+      endpointAccountingTerm_add_claimHoles_add_terminalValuation_eq_blockLength
+        n m
+    have habsorb := hB m
+    omega
+
+/-! ## Scaled cumulative absorption -/
+
+/-- Scaling preserves the exact window budget over `Int`. -/
+theorem canonicalEndpointWidthBudgetWindow_conservation_mul
+    (n : OddNat) (q M : ℕ) (A : ℤ) :
+    A * ((bitWidth (canonicalBlockStartState n (q + M)) : ℤ) -
+          bitWidth (canonicalBlockStartState n q)) +
+          A * canonicalClaimHolesWindowSum n q M +
+        A * canonicalTerminalValuationWindowSum n q M =
+      A * canonicalBlockLengthWindowSum n q M := by
+  have h := canonicalEndpointWidthBudgetWindow_conservation n q M
+  calc
+    A * ((bitWidth (canonicalBlockStartState n (q + M)) : ℤ) -
+          bitWidth (canonicalBlockStartState n q)) +
+          A * canonicalClaimHolesWindowSum n q M +
+        A * canonicalTerminalValuationWindowSum n q M =
+        A * (((bitWidth (canonicalBlockStartState n (q + M)) : ℤ) -
+            bitWidth (canonicalBlockStartState n q)) +
+          canonicalClaimHolesWindowSum n q M +
+          canonicalTerminalValuationWindowSum n q M) := by ring
+    _ = A * canonicalBlockLengthWindowSum n q M := congrArg (fun z => A * z) h
+
+/-- If scaled absorption covers scaled length up to allowance `C`, then the
+same allowance bounds scaled width growth.  No logarithmic interpretation is
+needed. -/
+theorem mul_widthGrowth_le_of_mul_length_le_absorption_add
+    {n : OddNat} {q M : ℕ} {A C : ℤ}
+    (habsorb :
+      A * canonicalBlockLengthWindowSum n q M ≤
+        A * canonicalClaimHolesWindowSum n q M +
+          A * canonicalTerminalValuationWindowSum n q M + C) :
+    A * ((bitWidth (canonicalBlockStartState n (q + M)) : ℤ) -
+      bitWidth (canonicalBlockStartState n q)) ≤ C := by
+  have hbudget :=
+    canonicalEndpointWidthBudgetWindow_conservation_mul n q M A
+  linarith
+
+/-- Unscaled caller-facing absorption bound for cumulative width growth. -/
+theorem widthGrowth_le_of_length_le_absorption_add
+    {n : OddNat} {q M : ℕ} {C : ℤ}
+    (habsorb :
+      canonicalBlockLengthWindowSum n q M ≤
+        canonicalClaimHolesWindowSum n q M +
+          canonicalTerminalValuationWindowSum n q M + C) :
+    (bitWidth (canonicalBlockStartState n (q + M)) : ℤ) -
+        bitWidth (canonicalBlockStartState n q) ≤ C := by
+  have hscaled :
+      (1 : ℤ) * canonicalBlockLengthWindowSum n q M ≤
+        1 * canonicalClaimHolesWindowSum n q M +
+          1 * canonicalTerminalValuationWindowSum n q M + C := by
+    simpa using habsorb
+  simpa using (mul_widthGrowth_le_of_mul_length_le_absorption_add hscaled)
+
+/-- Complete absorption of cumulative length forces nonpositive width growth
+over the selected finite window. -/
+theorem widthGrowth_nonpos_of_length_le_absorption
+    {n : OddNat} {q M : ℕ}
+    (habsorb :
+      canonicalBlockLengthWindowSum n q M ≤
+        canonicalClaimHolesWindowSum n q M +
+          canonicalTerminalValuationWindowSum n q M) :
+    (bitWidth (canonicalBlockStartState n (q + M)) : ℤ) -
+        bitWidth (canonicalBlockStartState n q) ≤ 0 := by
+  apply widthGrowth_le_of_length_le_absorption_add (C := 0)
+  simpa using habsorb
+
+/-! ## Canonical counter candidate
+
+The following counter has the exact recurrence required by the generic
+counter API.  Its nonnegativity is exactly the missing width-prefix control,
+so no certificate is constructed here: proving the local guard from the
+counter invariant itself would be circular.
+-/
+
+/-- Cumulative absorbed budget minus cumulative block length. -/
+noncomputable def canonicalEndpointCounterCredit (n : OddNat) (M : ℕ) : ℤ :=
+  canonicalClaimHolesWindowSum n 0 M +
+    canonicalTerminalValuationWindowSum n 0 M -
+      canonicalBlockLengthWindowSum n 0 M
+
+@[simp] theorem canonicalEndpointCounterCredit_zero (n : OddNat) :
+    canonicalEndpointCounterCredit n 0 = 0 := by
+  simp [canonicalEndpointCounterCredit]
+
+/-- The candidate credit is exactly the negative cumulative width growth. -/
+theorem canonicalEndpointCounterCredit_eq_rootWidth_sub_startWidth
+    (n : OddNat) (M : ℕ) :
+    canonicalEndpointCounterCredit n M =
+      (bitWidth n.1 : ℤ) - bitWidth (canonicalBlockStartState n M) := by
+  have hbudget := canonicalEndpointWidthBudgetPrefix_conservation n M
+  unfold canonicalEndpointCounterCredit
+  linarith
+
+/-- Candidate credit is nonnegative exactly when the current canonical width
+does not exceed the initial root width.  This is diagnostic, not an
+independent proof of the condition. -/
+theorem canonicalEndpointCounterCredit_nonneg_iff
+    (n : OddNat) (M : ℕ) :
+    0 ≤ canonicalEndpointCounterCredit n M ↔
+      bitWidth (canonicalBlockStartState n M) ≤ bitWidth n.1 := by
+  rw [canonicalEndpointCounterCredit_eq_rootWidth_sub_startWidth]
+  omega
+
+/-- Exact one-block recurrence of the canonical counter candidate. -/
+theorem canonicalEndpointCounterCredit_succ
+    (n : OddNat) (M : ℕ) :
+    canonicalEndpointCounterCredit n (M + 1) =
+      canonicalEndpointCounterCredit n M - endpointAccountingTerm n M := by
+  rw [canonicalEndpointCounterCredit_eq_rootWidth_sub_startWidth,
+    canonicalEndpointCounterCredit_eq_rootWidth_sub_startWidth,
+    endpointAccountingTerm_eq_canonicalBlock_bitWidth_sub]
+  rw [canonicalBlockStartState_succ_eq_nextStartState]
+  ring
+
+/-- The desired local guard is equivalent to nonnegativity of the next
+candidate credit.  This identifies the remaining arithmetic obligation but
+does not discharge it. -/
+theorem endpointAccountingTerm_le_counterCredit_iff_next_nonneg
+    (n : OddNat) (M : ℕ) :
+    endpointAccountingTerm n M ≤ canonicalEndpointCounterCredit n M ↔
+      0 ≤ canonicalEndpointCounterCredit n (M + 1) := by
+  rw [canonicalEndpointCounterCredit_succ]
+  omega
+
+end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointDrift.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointDrift.lean
index 90def769..8ffaebc5 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointDrift.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointDrift.lean
@@ -88,6 +88,13 @@ theorem GlobalEndpointDriftBound.rootwise
 
 /-! ## Exact positive-drift normal forms -/
 
+/-- The initial canonical block starts at the odd root itself. -/
+@[simp] theorem canonicalBlockStartState_zero_eq_root (n : OddNat) :
+    canonicalBlockStartState n 0 = n.1 := by
+  unfold canonicalBlockStartState canonicalBlockStartTime
+    canonicalEndpointBlockStart
+  rfl
+
 /-- Exact claim/capacity form with terminal capacity expressed by its 2-adic
 valuation.  Positivity is not needed for the identity. -/
 theorem endpointAccountingTerm_eq_claimCount_sub_terminalValuation
@@ -107,7 +114,20 @@ theorem endpointAccountingTerm_le_length_sub_terminalValuation
   simpa [canonicalBlockCapacityCount_eq_terminalValuation] using
     endpointAccountingTerm_le_length_sub_capacity n m
 
-/-- Exact carry-word refinement: the gap between the coarse
+/-- Primary block conservation law.  Block length is partitioned exactly into
+realized endpoint drift, unrealized claim depths, and terminal 2-adic
+absorption.  All terms live in `Int`, so no natural subtraction loses
+information. -/
+theorem endpointAccountingTerm_add_claimHoles_add_terminalValuation_eq_blockLength
+    (n : OddNat) (m : ℕ) :
+    endpointAccountingTerm n m +
+          ((canonicalBlockClaimHoles n m).card : ℤ) +
+        (canonicalBlockTerminalValuation n m : ℤ) =
+      (canonicalBlockLength n m : ℤ) := by
+  rw [endpointAccountingTerm_eq_length_sub_terminalValuation_sub_claimHoles]
+  ring
+
+/-- Rearranged carry-word refinement: the gap between the coarse
 `length - valuation` ceiling and actual drift is precisely the number of
 missing claim depths. -/
 theorem endpointAccountingTerm_add_claimHoles_eq_length_sub_terminalValuation
@@ -115,8 +135,10 @@ theorem endpointAccountingTerm_add_claimHoles_eq_length_sub_terminalValuation
     endpointAccountingTerm n m + (canonicalBlockClaimHoles n m).card =
       (canonicalBlockLength n m : ℤ) -
         canonicalBlockTerminalValuation n m := by
-  rw [endpointAccountingTerm_eq_length_sub_terminalValuation_sub_claimHoles]
-  ring
+  have h :=
+    endpointAccountingTerm_add_claimHoles_add_terminalValuation_eq_blockLength
+      n m
+  omega
 
 /-! ## Sufficient rootwise hypotheses
 
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalHighDrift.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalHighDrift.lean
new file mode 100644
index 00000000..448f5a43
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalHighDrift.lean
@@ -0,0 +1,110 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointConservation
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalHighDrift"
+
+namespace DkMath.Collatz
+
+/-!
+# Finite high-drift event carrier
+
+These sets are finite diagnostics over the observed prefix `[0, M)`.  Their
+finiteness is inherited from `Finset.range M` and makes no statement about the
+number of high-drift blocks over all canonical time.
+-/
+
+/-- Blocks below `M` whose realized endpoint drift reaches natural threshold
+`K`. -/
+noncomputable def canonicalHighDriftBlocksUpTo
+    (n : OddNat) (K M : ℕ) : Finset ℕ :=
+  (Finset.range M).filter fun m =>
+    (K : ℤ) ≤ endpointAccountingTerm n m
+
+/-- Exact membership in the finite high-drift carrier. -/
+@[simp] theorem mem_canonicalHighDriftBlocksUpTo
+    {n : OddNat} {K M m : ℕ} :
+    m ∈ canonicalHighDriftBlocksUpTo n K M ↔
+      m < M ∧ (K : ℤ) ≤ endpointAccountingTerm n m := by
+  simp [canonicalHighDriftBlocksUpTo]
+
+/-- Structural membership form obtained from exact block conservation. -/
+theorem mem_canonicalHighDriftBlocksUpTo_iff_budget
+    {n : OddNat} {K M m : ℕ} :
+    m ∈ canonicalHighDriftBlocksUpTo n K M ↔
+      m < M ∧
+        (K : ℤ) + ((canonicalBlockClaimHoles n m).card : ℤ) +
+            (canonicalBlockTerminalValuation n m : ℤ) ≤
+          (canonicalBlockLength n m : ℤ) := by
+  rw [mem_canonicalHighDriftBlocksUpTo]
+  constructor
+  · rintro ⟨hm, hK⟩
+    exact ⟨hm, (natCast_le_endpointAccountingTerm_iff n m K).mp hK⟩
+  · rintro ⟨hm, hbudget⟩
+    exact ⟨hm, (natCast_le_endpointAccountingTerm_iff n m K).mpr hbudget⟩
+
+@[simp] theorem canonicalHighDriftBlocksUpTo_zero
+    (n : OddNat) (K : ℕ) :
+    canonicalHighDriftBlocksUpTo n K 0 = ∅ := by
+  ext m
+  simp
+
+/-- Enlarging the observed prefix only adds possible events. -/
+theorem canonicalHighDriftBlocksUpTo_mono_prefix
+    (n : OddNat) (K : ℕ) {M N : ℕ} (hMN : M ≤ N) :
+    canonicalHighDriftBlocksUpTo n K M ⊆
+      canonicalHighDriftBlocksUpTo n K N := by
+  intro m hm
+  rw [mem_canonicalHighDriftBlocksUpTo] at hm ⊢
+  exact ⟨hm.1.trans_le hMN, hm.2⟩
+
+/-- Raising the threshold can only remove events. -/
+theorem canonicalHighDriftBlocksUpTo_antitone_threshold
+    (n : OddNat) (M : ℕ) {K J : ℕ} (hKJ : K ≤ J) :
+    canonicalHighDriftBlocksUpTo n J M ⊆
+      canonicalHighDriftBlocksUpTo n K M := by
+  intro m hm
+  rw [mem_canonicalHighDriftBlocksUpTo] at hm ⊢
+  refine ⟨hm.1, ?_⟩
+  exact (Int.ofNat_le.mpr hKJ).trans hm.2
+
+/-- Number of observed high-drift blocks below `M`. -/
+noncomputable def canonicalHighDriftEventCount
+    (n : OddNat) (K M : ℕ) : ℕ :=
+  (canonicalHighDriftBlocksUpTo n K M).card
+
+/-- Event count is monotone in the finite observation horizon. -/
+theorem canonicalHighDriftEventCount_mono_prefix
+    (n : OddNat) (K : ℕ) {M N : ℕ} (hMN : M ≤ N) :
+    canonicalHighDriftEventCount n K M ≤
+      canonicalHighDriftEventCount n K N := by
+  exact Finset.card_le_card
+    (canonicalHighDriftBlocksUpTo_mono_prefix n K hMN)
+
+/-- Event count is antitone in the drift threshold. -/
+theorem canonicalHighDriftEventCount_antitone_threshold
+    (n : OddNat) (M : ℕ) {K J : ℕ} (hKJ : K ≤ J) :
+    canonicalHighDriftEventCount n J M ≤
+      canonicalHighDriftEventCount n K M := by
+  exact Finset.card_le_card
+    (canonicalHighDriftBlocksUpTo_antitone_threshold n M hKJ)
+
+/-- Every high-drift event in the finite carrier has a long enough block. -/
+theorem blockLength_ge_of_mem_canonicalHighDriftBlocksUpTo
+    {n : OddNat} {K M m : ℕ}
+    (hm : m ∈ canonicalHighDriftBlocksUpTo n K M) :
+    K ≤ canonicalBlockLength n m := by
+  exact blockLength_ge_of_endpointAccountingTerm_ge
+    (mem_canonicalHighDriftBlocksUpTo.mp hm).2
+
+/-!
+No union over all `M` is introduced here.  In particular, monotonicity of the
+finite carriers does not establish eventual stabilization, finite total event
+count, or repeated high drift for a fixed root.
+-/
+
+end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteControlCounter.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteControlCounter.lean
index caa4f6a1..532b7c09 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteControlCounter.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteControlCounter.lean
@@ -25,8 +25,54 @@ guard has been proved independently from canonical block arithmetic; using
 the desired prefix invariant itself as that guard would be circular.
 -/
 
+/-- Core signed-counter certificate.  No finite control state is needed for
+the recurrence or invariant induction. -/
+structure SignedCounterCertificate where
+  weight : ℕ → ℤ
+  credit : ℕ → ℤ
+  initial_credit_nonneg : 0 ≤ credit 0
+  credit_succ : ∀ m, credit (m + 1) = credit m - weight m
+  preserves_nonneg : ∀ m, 0 ≤ credit m → weight m ≤ credit m
+
+namespace SignedCounterCertificate
+
+/-- Exact recurrence and the local guard preserve credit nonnegativity. -/
+theorem credit_nonneg (C : SignedCounterCertificate) (M : ℕ) :
+    0 ≤ C.credit M := by
+  induction M with
+  | zero => exact C.initial_credit_nonneg
+  | succ M ih =>
+      rw [C.credit_succ]
+      exact sub_nonneg.mpr (C.preserves_nonneg M ih)
+
+/-- The unrestricted counter recurrence telescopes exactly. -/
+theorem sum_weight_range_eq_credit_zero_sub
+    (C : SignedCounterCertificate) (M : ℕ) :
+    (∑ m ∈ Finset.range M, C.weight m) = C.credit 0 - C.credit M := by
+  induction M with
+  | zero => simp
+  | succ M ih =>
+      rw [Finset.sum_range_succ, ih, C.credit_succ]
+      ring
+
+/-- General soundness with arbitrary nonnegative initial credit. -/
+theorem sum_weight_range_le_initial_credit
+    (C : SignedCounterCertificate) (M : ℕ) :
+    (∑ m ∈ Finset.range M, C.weight m) ≤ C.credit 0 := by
+  rw [C.sum_weight_range_eq_credit_zero_sub]
+  exact sub_le_self _ (C.credit_nonneg M)
+
+/-- Zero initial credit recovers nonpositive prefixes. -/
+theorem sum_weight_range_nonpos_of_initial_credit_eq_zero
+    (C : SignedCounterCertificate) (hzero : C.credit 0 = 0) (M : ℕ) :
+    (∑ m ∈ Finset.range M, C.weight m) ≤ 0 := by
+  simpa [hzero] using C.sum_weight_range_le_initial_credit M
+
+end SignedCounterCertificate
+
 /-- A finite control sequence accompanied by an unrestricted integer counter.
-The recurrence and local guard are the arithmetic proof obligations. -/
+The finite signature is observational; soundness is delegated to the core
+signed-counter certificate. -/
 structure FiniteControlSignedCounterCertificate
     (Signature : Type*) [Finite Signature] where
   signature : ℕ → Signature
@@ -40,34 +86,43 @@ namespace FiniteControlSignedCounterCertificate
 
 variable {Signature : Type*} [Finite Signature]
 
+/-- Forget the finite diagnostic control and retain the arithmetic counter
+certificate used by the soundness proof. -/
+def toSignedCounterCertificate
+    (C : FiniteControlSignedCounterCertificate Signature) :
+    SignedCounterCertificate where
+  weight := C.weight
+  credit := C.credit
+  initial_credit_nonneg := by rw [C.initial_credit_eq_zero]
+  credit_succ := C.credit_succ
+  preserves_nonneg := C.preserves_nonneg
+
 /-- Exact counter recurrence and the local guard preserve nonnegative credit
 at every realized transition. -/
 theorem credit_nonneg
     (C : FiniteControlSignedCounterCertificate Signature) (M : ℕ) :
-    0 ≤ C.credit M := by
-  induction M with
-  | zero => rw [C.initial_credit_eq_zero]
-  | succ M ih =>
-      rw [C.credit_succ]
-      exact sub_nonneg.mpr (C.preserves_nonneg M ih)
+    0 ≤ C.credit M :=
+  C.toSignedCounterCertificate.credit_nonneg M
 
 /-- Counter recurrence telescopes exactly: accumulated weight is initial
 credit minus final credit. -/
 theorem sum_weight_range_eq_credit_zero_sub
     (C : FiniteControlSignedCounterCertificate Signature) (M : ℕ) :
-    (∑ m ∈ Finset.range M, C.weight m) = C.credit 0 - C.credit M := by
-  induction M with
-  | zero => simp
-  | succ M ih =>
-      rw [Finset.sum_range_succ, ih, C.credit_succ]
-      ring
+    (∑ m ∈ Finset.range M, C.weight m) = C.credit 0 - C.credit M :=
+  C.toSignedCounterCertificate.sum_weight_range_eq_credit_zero_sub M
+
+/-- Finite-control wrapper of the general initial-credit bound. -/
+theorem sum_weight_range_le_initial_credit
+    (C : FiniteControlSignedCounterCertificate Signature) (M : ℕ) :
+    (∑ m ∈ Finset.range M, C.weight m) ≤ C.credit 0 :=
+  C.toSignedCounterCertificate.sum_weight_range_le_initial_credit M
 
 /-- Soundness: every prefix weight is nonpositive. -/
 theorem sum_weight_range_nonpos
     (C : FiniteControlSignedCounterCertificate Signature) (M : ℕ) :
     (∑ m ∈ Finset.range M, C.weight m) ≤ 0 := by
-  rw [C.sum_weight_range_eq_credit_zero_sub, C.initial_credit_eq_zero]
-  simpa only [zero_sub] using neg_nonpos.mpr (C.credit_nonneg M)
+  exact C.toSignedCounterCertificate.sum_weight_range_nonpos_of_initial_credit_eq_zero
+    C.initial_credit_eq_zero M
 
 end FiniteControlSignedCounterCertificate
 
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-341.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-341.md
new file mode 100644
index 00000000..71cc9774
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-341.md
@@ -0,0 +1,265 @@
+# Petal / FloatWindow implementation report: checkpoint 341
+
+## Status
+
+Checkpoint 341 is implemented without adding `sorry`.
+
+This checkpoint turns the canonical endpoint identity into an exact cumulative
+conservation layer.  It also isolates high-drift events as finite diagnostic
+objects and separates the reusable signed-counter argument from the finite
+control signature.
+
+The branch stops at an honest obstruction: the canonical counter candidate has
+the required exact recurrence, but its preservation guard is equivalent to the
+width-prefix bound that the certificate would be intended to prove.  Therefore
+no canonical certificate instance is constructed.
+
+## Implemented modules
+
+### `CanonicalEndpointDrift.lean`
+
+The primary one-block conservation theorem is now the direct identity
+
+```text
+endpoint drift + claim holes + terminal valuation = block length.
+```
+
+Lean theorem:
+
+```lean
+endpointAccountingTerm_add_claimHoles_add_terminalValuation_eq_blockLength
+```
+
+All four quantities are compared in `Int`, so negative realized drift is not
+lost through natural-number subtraction.  The previous rearranged theorem is
+retained as a corollary.
+
+The correct interpretation is now fixed:
+
+- block length is the total potential drift budget;
+- endpoint accounting is the realized signed drift;
+- claim holes and terminal valuation are the two exact absorption channels.
+
+A long block alone does not imply large realized drift.
+
+### `CanonicalEndpointConservation.lean`
+
+Four half-open window ledgers over `[q, q + M)` were added:
+
+- `canonicalEndpointDriftWindowSum`;
+- `canonicalClaimHolesWindowSum`;
+- `canonicalTerminalValuationWindowSum`;
+- `canonicalBlockLengthWindowSum`.
+
+Their zero and singleton forms are explicit.  The main finite conservation law
+is
+
+```lean
+canonicalEndpointBudgetWindow_conservation
+```
+
+and the drift telescope is
+
+```lean
+canonicalEndpointDriftWindowSum_eq_startState_bitWidth_sub
+```
+
+Combining them gives shifted and prefix width-budget laws:
+
+```text
+width growth + cumulative holes + cumulative terminal valuation
+  = cumulative block length.
+```
+
+This is an exact integer identity, not an asymptotic estimate.
+
+The exact high-drift threshold is also fixed:
+
+```text
+K <= drift
+  iff
+K + holes + terminal valuation <= block length.
+```
+
+Consequences proved in Lean:
+
+- high drift forces block length at least `K`;
+- high drift leaves at most `block length - K` for combined absorption;
+- unbounded drift for one fixed root implies unbounded block lengths for that
+  same root.
+
+No converse is claimed.
+
+Rootwise boundedness now has an exact structural restatement:
+
+```text
+RootwiseEndpointDriftBound n
+  iff
+there is a uniform additive B such that
+  block length <= holes + terminal valuation + B.
+```
+
+This reformulates the fixed-root problem but does not produce `B`.
+
+Scaled and unscaled cumulative absorption bounds were added.  In particular,
+if cumulative holes and terminal valuation absorb cumulative length up to `C`,
+then cumulative width growth is at most `C`.  Complete absorption forces
+nonpositive width growth on the selected finite window.
+
+### Canonical counter candidate
+
+The candidate
+
+```text
+credit(M) = cumulative holes + cumulative valuation - cumulative length
+```
+
+has been defined.  Lean proves
+
+```text
+credit(M) = root bit width - current canonical bit width
+```
+
+and the exact recurrence
+
+```text
+credit(M + 1) = credit(M) - endpoint drift(M).
+```
+
+The decisive diagnostic equivalences are:
+
+```text
+0 <= credit(M)
+  iff current width <= root width
+
+drift(M) <= credit(M)
+  iff 0 <= credit(M + 1).
+```
+
+Thus the candidate is algebraically correct, but the guard is not yet an
+independent arithmetic theorem.  Instantiating the counter certificate here
+would be circular.
+
+### `CanonicalHighDrift.lean`
+
+The finite event carrier
+
+```lean
+canonicalHighDriftBlocksUpTo n K M
+```
+
+contains exactly the block indices below `M` whose drift is at least `K`.
+Membership also has the equivalent block-budget form.  Prefix monotonicity,
+threshold antitonicity, event-count monotonicity, and the block-length lower
+bound are proved.
+
+This carrier is deliberately finite.  No union over all horizons, eventual
+stabilization, finite total event count, or repeated high-drift theorem is
+inferred from it.
+
+### `FiniteControlCounter.lean`
+
+The arithmetic soundness argument was factored into
+
+```lean
+SignedCounterCertificate
+```
+
+with weight, credit, nonnegative initial credit, exact recurrence, and local
+preservation guard.  It proves
+
+```text
+sum of prefix weights = initial credit - final credit
+sum of prefix weights <= initial credit.
+```
+
+`FiniteControlSignedCounterCertificate` is retained as an observational
+wrapper carrying the finite signature, and projects to the core certificate.
+The old zero-initial theorem remains as a corollary.  Existing users and the
+alternating witness are unchanged at their public surface.
+
+## Finite audit
+
+The canonical recurrence was sampled for roots
+
+```text
+27, 31, 47, 59, 123, 255, 511, 1023, 2047, 4095
+```
+
+until a repeated state or 1000 blocks.  For each block the audit recorded:
+
+```text
+index, drift, block length, claim holes, terminal valuation,
+scalar queue before/after, candidate credit before,
+spacing from the previous event with drift >= 2.
+```
+
+Selected high-drift observations are:
+
+| root | block | drift | length | holes | valuation | queue before/after | credit before | prior spacing |
+| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
+| 27 | 1 | 2 | 5 | 2 | 1 | 0 / 2 | 0 | - |
+| 31 | 0 | 2 | 5 | 2 | 1 | 0 / 2 | 0 | - |
+| 511 | 0 | 5 | 9 | 3 | 1 | 0 / 5 | 0 | - |
+| 1023 | 0 | 3 | 10 | 4 | 3 | 0 / 3 | 0 | - |
+| 2047 | 0 | 6 | 11 | 4 | 1 | 0 / 6 | 0 | - |
+| 2047 | 19 | 4 | 7 | 2 | 1 | 0 / 4 | 4 | 17 |
+| 2047 | 21 | 2 | 6 | 3 | 1 | 5 / 7 | -5 | 2 |
+| 4095 | 0 | 4 | 12 | 4 | 4 | 0 / 4 | 0 | - |
+| 4095 | 18 | 4 | 7 | 2 | 1 | 0 / 4 | 5 | 17 |
+| 4095 | 19 | 2 | 6 | 3 | 1 | 4 / 6 | -4 | 1 |
+
+These are finite observations only.  They show that repeated threshold events
+occur in the tested finite traces and that candidate credit may already be
+negative before a later event.  They do not prove repeated high drift for all
+time, unbounded drift, or failure of a rootwise bound.
+
+## Facts now fixed
+
+1. Canonical endpoint drift is exactly the residual block budget after two
+   absorption channels.
+2. This identity conserves exactly on every finite shifted window.
+3. Cumulative drift is exactly canonical width change.
+4. High-drift membership is equivalent to a local residual-budget inequality.
+5. Rootwise boundedness is exactly a uniform additive absorption estimate.
+6. A finite high-drift carrier supports honest finite counting and monotonicity.
+7. Counter soundness does not logically depend on finite control state.
+8. The canonical arithmetic credit has the correct recurrence, but its local
+   guard remains the missing theorem.
+
+## Branch decision
+
+No independent canonical preservation guard was found.  No theorem establishes
+repeated unbounded drift for a fixed root.  The finite audit does not justify an
+all-time statement.  Therefore:
+
+- do not instantiate a canonical `SignedCounterCertificate` yet;
+- do not refute `RootwiseEndpointDriftBound`;
+- keep the fixed-root question open.
+
+The next mathematically meaningful branch is to search for an arithmetic guard
+that does not mention candidate-credit nonnegativity or the desired prefix
+width bound.  Promising inputs are the already formalized reflected queue,
+source-age deficit, terminal valuation, and claim-hole incidence.  A valid next
+bridge must imply
+
+```text
+endpoint drift(M) <= credit(M)
+```
+
+from independently proved local data.  If this cannot be done, the exact
+conservation and finite event carrier are the correct stopping surface.
+
+## Verification
+
+The checkpoint passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointConservation
+lake build DkMath.Collatz.PetalBridge.FloatWindow.CanonicalHighDrift
+lake build DkMath.Collatz.PetalBridge.FloatWindow.FiniteControlCounter
+lake build DkMath.Collatz.PetalBridge.FloatWindow
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath
+git diff --check
+```
````
`````
