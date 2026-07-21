# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.FloatWindow.*

gch: eb7f045b5e285d20baff61228eb06488208f4590

## Report

(19m11s)

cp-340 を実装しました。

**確定した事実**

- `endpointAccountingTerm` は canonical block 間の正確な bit width 差。
- prefix sum は初期 root から現在 block までの width 差へ telescope する。
- 奇数長 all-ones root `2^(2r+1)-1` では初期 drift が `r` 以上。
- 任意の整数上限を超える root が存在するため、`¬ GlobalEndpointDriftBound`。
- ただし root が上限ごとに変わるため、固定 root の `RootwiseEndpointDriftBound` は未解決。
- `length - terminalValuation` と実 drift の差は、正確に claim holes 数。
- 非正 prefix と非有界な正 increment が両立し、有限 upper-weight table が存在しない明示例を形式化。
- 有限 control と非有界 counter による代替 certificate と soundness を実装。

詳細と有限数値監査表は [report-petal-340.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-340.md) に記録しました。

検証済みです。

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
lake build DkMath
git diff --check
```

新規4ファイルには `sorry` / `admit` はありません。
次の正直な境界は、単一の固定 root における endpoint drift の一様有界性、または反復的非有界性の証明です。

## Review

(2m46s)

## cp-340 実装レビュー

## 総合判定

**全面採用。**

cp-340 は単なる補題追加ではない。

cp-339 で残った、

```text
有限 potential を作るには endpoint drift の pointwise ceiling が必要
```

という境界に対して、

1. endpoint drift の正体を exact width difference として確定
2. global ceiling を all-ones 族で反証
3. rootwise ceiling との量化差を API 化
4. finite potential が prefix theorem に対して不完全である明示例を構築
5. unbounded counter による、より広い証明器を実装

まで完了している。

これにより、現在の分岐は完全に明瞭になった。

```text
GlobalEndpointDriftBound
  → 反証済み

RootwiseEndpointDriftBound n
  → 未解決

finite upper-weight / bounded potential
  → 一般の prefix 制御には不完全

finite control + unbounded counter
  → 一般形式として sound
  → canonical 適用は arithmetic guard 待ち
```

循環証明、量化の誤投影、観測値の theorem 化は見当たらない。

---

## Exact endpoint ledger

中心定理、

```lean
endpointAccountingTerm_eq_canonicalBlock_bitWidth_sub
```

は非常に良い。

$$\Delta_n(m)=\operatorname{bitWidth}(\operatorname{NextStart}_n(m))-\operatorname{bitWidth}(\operatorname{Start}_n(m))$$

が exact theorem になった。さらに prefix sum も、

$$\sum_{k\le m}\Delta_n(k)=\operatorname{bitWidth}(\operatorname{NextStart}_n(m))-\operatorname{bitWidth}(n)$$

へ telescope する。

これにより `endpointAccountingTerm` は、補助的な debt accounting ではなく、**canonical block 宇宙の正確な半径変化**として読めるようになった。

先ほど話していた「螺旋」の半径差が、ここで初めて exact ledger になっておる。

---

## Rootwise と global の量化分離

次の二つを別 predicate にした判断は正しい。

```lean
RootwiseEndpointDriftBound n
GlobalEndpointDriftBound
```

それぞれ、

$$\exists B_n,\ \forall m,\ \Delta_n(m)\le B_n$$

$$\exists B,\ \forall n,m,\ \Delta_n(m)\le B$$

である。

さらに cp-339 の固定 horizon theorem が、前者と一致することも公開 API として固定された。global から rootwise への片方向だけを theorem にし、逆を主張していない点も正確じゃ。

ここは今後の誤推論防止壁として強い。

---

## all-ones 族

all-ones root、

$$n_L=2^L-1$$

について、初期 canonical block が、

$$\operatorname{length}=L,\qquad\operatorname{core}=1,\qquad\operatorname{terminalCarrier}=3^L-1$$

を持つことが閉じた。

さらに奇数長 $L=2r+1$ では、

$$\nu_2(3^{2r+1}-1)=1$$

$$\operatorname{NextStart}=\frac{3^{2r+1}-1}{2}$$

まで exact に閉じている。mod $4$ から valuation one を出す流れにも問題はない。

### 線形成長下界

実数対数や漸近評価に逃げず、

$$2^{3r+1}\le3^{2r+1}-1$$

から next width を下から押さえ、

$$r\le\Delta_{n_{2r+1}}(0)$$

を得ている。

この証明は堅い。

実際の漸近係数 $\log_2(3/2)$ より弱い $1/2$ の線形下界だが、global ceiling を倒すには十分であり、Lean 実装として扱いやすい。

### global ceiling の否定

任意の整数 $B$ に対して root を選び直し、

$$B<\Delta_n(0)$$

を証明した上で、

```lean
not_globalEndpointDriftBound
```

を閉じている。

コメントにも theorem にも、root が $B$ に依存することが明記されている。固定 root の反復的非有界性へ誤投影されていない。

**この部分は完全採用。**

---

## Claim holes の exact 保存式

今回の中で、all-ones 族と並んで重要なのが、

```lean
endpointAccountingTerm_add_claimHoles_eq_length_sub_terminalValuation
```

じゃ。

現在の形は、

$$\Delta+h=L-v$$

だが、移項すれば、

$$\Delta+h+v=L$$

となる。

ここで、

- $\Delta$：実現した width drift
- $h$：claim holes
- $v$：terminal valuation payment
- $L$：block length

である。

これは単なる上界補題ではなく、**block length の三分解保存式**じゃ。

```text
全 block budget
=
実現 drift
+ claim にならなかった穴
+ terminal payment
```

まさに Big / Core / Gap の exact 分解になっている。

この theorem は次 checkpoint で、より直接的な名前の保存則として昇格させる価値がある。

```lean
endpointDrift_add_claimHoles_add_terminalValuation_eq_blockLength
```

さらに window sumへ持ち上げれば、

$$\sum\Delta+\sum h+\sum v=\sum L$$

となり、endpoint drift telescope と合わせて、

$$\operatorname{width}_{M+1}-\operatorname{width}_0+\sum h+\sum v=\sum L$$

が得られる。

これは先ほど話していた**螺旋の成長係数を exact に読む入口**じゃ。

---

## Sufficient rootwise hypotheses

次の三条件から rootwise bound を得る補題も正しく、主張範囲も適切じゃ。

- block length の一様上界
- $L-v$ の一様上界
- next width の additive increment 上界

いずれも「その仮定が成立する」とは述べず、依存関係だけを固定している。

これで fixed-root 攻略の候補が theorem shape として明示された。

---

## Finite-potential incompleteness witness

明示列、

$$w(2k)=-(k+1),\qquad w(2k+1)=k+1$$

について、

$$\sum_{m<2k}w(m)=0$$

$$\sum_{m<2k+1}w(m)=-(k+1)$$

$$\forall M,\ \sum_{m<M}w(m)\le0$$

が証明されている。

一方で正 increment は任意の整数上限を超え、したがって finite signature に対する sound successor upper-weight table は存在しない。

これにより、

$$\text{all prefixes nonpositive}\not\Rightarrow\text{pointwise increment bounded}$$

が Lean 上で確定した。

したがって、

```text
finite upper table の失敗
```

は、

```text
prefix theorem の失敗
```

を意味しない。

この論理的分離は完全に成功している。

---

## Finite control + unbounded counter

一般 certificate は、

```lean
credit 0 = 0
credit (m + 1) = credit m - weight m
0 ≤ credit m → weight m ≤ credit m
```

を持つ。

そこから帰納的に、

$$0\le\operatorname{credit}(M)$$

を得て、telescope により、

$$\sum_{m<M}w(m)=-\operatorname{credit}(M)\le0$$

を導く。

alternating witness では credit を、

$$C(2k)=0,\qquad C(2k+1)=k+1$$

として exact recurrence と local guard を独立に証明し、`Unit` 一状態の control へ instantiate している。

canonical deficit を instantiate していない判断も正しい。

## 小さな設計上の余白

ここだけ、今後整理できる余地がある。

`FiniteControlSignedCounterCertificate` の `signature` と `[Finite Signature]` は、現在の soundness theoremでは一度も使われていない。

つまり実質的な核は、

```lean
SignedCounterCertificate
```

であり、有限 control はその上に付随する観測層じゃ。

これは欠陥ではない。むしろ `Unit` で通ったことが、

> prefix soundness の本体は有限 control ではなく、unbounded credit と local guardである

と示している。

ただ API としては次の二層に分けるとさらに明瞭になる。

```lean
SignedCounterCertificate
FiniteControlSignedCounterCertificate
```

後者が前者を含む、または前者へ射影する形じゃ。

また一般資源証明器としては、

```lean
0 ≤ credit 0
```

を許し、

$$\sum_{m<M}w(m)\le\operatorname{credit}(0)$$

を結論とする版もあると応用範囲が広がる。

現在の zero-initial 版は prefix $\le0$ に特化した正しい特殊形なので、変更必須ではない。

---

## 循環性監査

今回、最も警戒すべきだったのは、

```text
次の credit が非負
```

を local guard の証明に使い、帰納法を偽装することだった。

しかし concrete witness の guard は parity 分岐から直接証明されており、prefix theoremや `credit_nonneg` を使っていない。

canonical への適用も保留されている。

したがって **循環性なし**。

ただし今後 canonical instance を作る際、

```lean
preserves_nonneg := desired_source_age_theorem
```

のような形にしてはならない。

必要なのは、

```text
carry carrier
claim holes
terminal valuation
FIFO consumption
block grammar
```

から導く独立 arithmetic guardじゃ。

---

## 数値監査

有限監査表も report の書き方が適切じゃ。

特に root `255` の、

```text
length = 8
terminal v2 = 5
claims = 5
drift = 0
```

は、長い block がそのまま高 driftを意味しないことを示す良い対照例になっている。

一方、odd all-ones で terminal valuation one の blockは高 driftになりやすい。

ただし report は明確に、

```text
finite observation
≠ rootwise boundedness theorem
≠ fixed-root unboundedness theorem
```

と分離している。

### 文言上の微修正候補

report 中の、

> A large block with low terminal valuation creates only capacity

は少し意味が取りにくい。

正確には、

> A large block with low terminal valuation creates a large potential drift budget; claim holes measure the exact loss before that budget becomes realized drift.

あたりが theorem の内容に合う。

つまり「capacity だけを作る」ではなく、**potential drift budget を作る**じゃな。

---

## cp-340 の到達点

cp-340 は、詰将棋を終わらせたのではない。

盤面を次の exact 保存式へ変えた。

$$L=\Delta+h+v$$

これにより fixed-root の高 drift は、

```text
長い block
かつ
少ない claim holes
かつ
小さい terminal valuation
```

が同時に起きる事象だと分かった。

高 drift は単なる「長い all-ones run」ではない。

> block length のうち、holesにも terminal paymentにも吸収されなかった残余

じゃ。

これが次の囲碁の整地線になる。

---

## 判定一覧

### Exact width ledger

**完成。**

### Prefix telescope

**完成。**

### Rootwise/global API 分離

**完成。**

### Odd all-ones normal form

**完成。**

### Cross-root drift unboundedness

**完成。**

### Global ceiling の否定

**完成。**

### Fixed-root ceiling

**未解決。影響なし。**

### Claim holes exact refinement

**完成。次の中心保存式。**

### Finite-potential incompleteness witness

**完成。**

### Unbounded-counter certificate

**完成。一般 soundness 正常。**

### Canonical counter instance

**未実装。正しく保留。**

### 循環性

**なし。**

### cp-340 総合

**全面採用。**

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge FloatWindow branch after
report-petal-340.

Checkpoint 340 is accepted.

It proved exact canonical width drift, cross-root failure of a global ceiling,
finite-potential incompleteness, and sound finite-control counter certificates.

The next checkpoint must turn the exact claim-hole identity into a cumulative
fixed-root conservation law and isolate the precise structure of repeated high
drift.

Stage A — expose the exact block conservation law

Add a theorem in the direct form:

    endpointAccountingTerm n m
      + card (canonicalBlockClaimHoles n m)
      + canonicalBlockTerminalValuation n m
      =
    canonicalBlockLength n m

with all casts explicit and stable.

Treat this as the primary block budget theorem.  Keep the existing rearranged
form as an alias or corollary.

Stage B — finite-window budget telescope

Define finite-window sums for:

    canonicalBlockLength;
    canonicalBlockClaimHoles.card;
    canonicalBlockTerminalValuation;
    endpointAccountingTerm.

Prove for every finite block window:

    sum drift + sum holes + sum terminal valuation = sum block length.

Then combine it with the existing canonical endpoint telescope to prove:

    next width - initial width
      + cumulative holes
      + cumulative terminal valuation
      =
    cumulative block length.

Provide both prefix and shifted-window forms where useful.

Check empty windows and singleton windows explicitly.

Stage C — exact high-drift threshold API

For natural threshold `K`, prove an exact equivalence of the form:

    K <= endpointAccountingTerm n m
      iff
    K + card holes + terminal valuation <= block length

with the required Int/Nat casts handled carefully.

Derive consequences:

    high drift forces long block length;
    high drift forces low combined absorption
      (claim holes + terminal valuation);
    unbounded fixed-root drift implies unbounded fixed-root block lengths.

Do not claim the converses.

Stage D — rootwise boundedness restatement

Derive an exact structural restatement:

    RootwiseEndpointDriftBound n
      iff
    exists B, forall m,
      blockLength m <= claimHoles m + terminalValuation m + B

using an integer or natural formulation that remains mathematically honest.

This is a reformulation, not a proof that the bound exists.

Stage E — repeated high-drift event carrier

Define a finite event set over a finite prefix:

    canonicalHighDriftBlocksUpTo n K M

and prove the exact membership theorem.

Add monotonicity in `M` and antitonicity in `K`.

Use this only as a finite diagnostic carrier.  Do not infer finiteness over all
time from finite prefixes.

Stage F — cumulative absorption ratio without real logarithms

Use the exact budget identity rather than asymptotic logarithms.

Expose integer inequalities showing that width growth over a window is bounded
when cumulative holes plus terminal valuation absorb enough of cumulative
block length.

A target shape is:

    A * cumulativeBlockLength
      <=
    A * cumulativeHoles
      + A * cumulativeValuation
      + C

implies a corresponding bound on cumulative width growth.

Do not introduce Real.log unless it is needed by a separate analytic module.

Stage G — counter-certificate API factoring

Audit whether the finite signature is logically used by the counter soundness
proof.

Prefer the following split if it improves the API without breaking existing
users:

    SignedCounterCertificate
    FiniteControlSignedCounterCertificate

The core certificate should contain:

    weight;
    credit;
    exact recurrence;
    initial condition;
    local preservation guard.

The finite-control wrapper should contain the finite signature and project to
the core certificate.

Also consider a general initial-credit version proving:

    sum weights <= initial credit.

Keep the current zero-initial theorem as a corollary.

Stage H — canonical counter candidate, but no instance

Define candidate arithmetic credit expressions only if they are assembled from
already proved quantities such as:

    cumulative terminal valuation;
    cumulative claim holes;
    cumulative block length;
    source-age deficit.

Prove their exact recurrence.

Do not construct a canonical counter certificate unless the local guard is
proved independently from canonical arithmetic.

A guard equivalent by definition to the desired prefix theorem is not
acceptable.

Stage I — fixed-root finite audit

Extend the finite audit to record, for each tested fixed root:

    the top several drift events, not only the maximum;
    spacing between high-drift events;
    block length;
    claim holes;
    terminal valuation;
    queue before and after;
    cumulative credit before the event.

Label every result as finite observation.

The audit may suggest a local guard, but it is not a proof of rootwise
boundedness or unboundedness.

Stage J — report wording

Replace the ambiguous phrase:

    a large block with low terminal valuation creates only capacity

with wording that distinguishes:

    potential drift budget;
    realized drift;
    exact absorption by claim holes and terminal valuation.

Stage K — branch decision

If an independently proved canonical local guard is found, instantiate the
counter certificate.

If repeated high drift is proved for one fixed root, record the exact
fixed-root obstruction and refute its rootwise bound.

If only cross-root families are found, keep the rootwise question open.

Stopping rule

Stop at the first genuine obstruction among:

    the direct conservation identity cannot be typed without changing an
    existing theorem;

    shifted-window telescoping fails at an endpoint convention;

    the high-drift threshold equivalence loses information through Int/Nat
    conversion;

    the proposed rootwise reformulation is only one-way;

    a canonical counter guard merely restates the desired invariant;

    finite audit data is being promoted to an all-time statement.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-341.md
```

今回の本当の新核は、これじゃ。

$$\boxed{L=\Delta+\text{ClaimHoles}+\text{TerminalPayment}}$$

詰将棋の駒を一個ずつ追う段階から、**各 block の土地がどこへ配分されたかを exact に整地する段階**へ入った。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
index f6a96346..da4b2d9c 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
@@ -30,12 +30,16 @@ import DkMath.Collatz.PetalBridge.FloatWindow.FiniteAmortizedResource
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmortizedResource
 import DkMath.Collatz.PetalBridge.FloatWindow.BoundedRepaymentLag
 import DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition
+import DkMath.Collatz.PetalBridge.FloatWindow.FinitePotentialIncompleteness
+import DkMath.Collatz.PetalBridge.FloatWindow.FiniteControlCounter
 import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceTimeLag
 import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalOwnedQueue
 import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalOwnedQueueGlobal
 import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeFlow
 import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeHorizon
 import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeFiniteCertificate
+import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointDrift
+import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalAllOnesDrift
 import DkMath.Collatz.PetalBridge.FloatWindow.RawLowSignatureObstruction

 #print "file: DkMath.Collatz.PetalBridge.FloatWindow"
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalAllOnesDrift.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalAllOnesDrift.lean
new file mode 100644
index 00000000..548e633c
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalAllOnesDrift.lean
@@ -0,0 +1,268 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointDrift
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalAllOnesDrift"
+
+namespace DkMath.Collatz
+
+/-!
+# Cross-root all-ones endpoint drift
+
+The root `2^L - 1` begins with one canonical block of length `L`.  For odd
+`L`, its terminal carrier has valuation one.  Varying `L` therefore gives a
+cross-root family with growing initial endpoint drift.  This refutes only the
+single global ceiling shared by every root; it is not a fixed-root
+unboundedness result.
+-/
+
+/-- The positive all-ones word of binary length `L`, packaged as an odd root.
+The positivity hypothesis excludes the zero word at `L = 0`. -/
+noncomputable def allOnesOdd (L : ℕ) (hL : 0 < L) : OddNat := by
+  refine ⟨2 ^ L - 1, ?_⟩
+  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : L ≠ 0)
+  rw [pow_succ]
+  have hp : 0 < 2 ^ q := pow_pos (by norm_num) _
+  omega
+
+@[simp] theorem allOnesOdd_val (L : ℕ) (hL : 0 < L) :
+    (allOnesOdd L hL).1 = 2 ^ L - 1 := rfl
+
+/-- Every first canonical block starts at the root itself. -/
+theorem canonicalBlockStartState_zero (n : OddNat) :
+    canonicalBlockStartState n 0 = n.1 := by
+  unfold canonicalBlockStartState canonicalBlockStartTime
+    canonicalEndpointBlockStart
+  rfl
+
+/-- The all-ones first block starts at the expected binary word. -/
+@[simp] theorem canonicalBlockStartState_allOnesOdd_zero
+    (L : ℕ) (hL : 0 < L) :
+    canonicalBlockStartState (allOnesOdd L hL) 0 = 2 ^ L - 1 := by
+  rw [canonicalBlockStartState_zero]
+  rfl
+
+/-- The first canonical block of `2^L - 1` has exact length `L`. -/
+@[simp] theorem canonicalBlockLength_allOnesOdd_zero
+    (L : ℕ) (hL : 0 < L) :
+    canonicalBlockLength (allOnesOdd L hL) 0 = L := by
+  rw [canonicalBlockLength_eq_v2_startState_add_one,
+    canonicalBlockStartState_allOnesOdd_zero]
+  have hp : 0 < 2 ^ L := pow_pos (by norm_num) _
+  have hadd : 2 ^ L - 1 + 1 = 2 ^ L := by omega
+  rw [hadd]
+  change v2 (pow2 L) = L
+  exact v2_pow2 L
+
+/-- Removing the initial exact power of two leaves odd core one. -/
+@[simp] theorem canonicalBlockOddCore_allOnesOdd_zero
+    (L : ℕ) (hL : 0 < L) :
+    canonicalBlockOddCore (allOnesOdd L hL) 0 = 1 := by
+  unfold canonicalBlockOddCore
+  rw [canonicalBlockStartState_allOnesOdd_zero,
+    canonicalBlockLength_allOnesOdd_zero]
+  have hp : 0 < 2 ^ L := pow_pos (by norm_num) _
+  have hadd : 2 ^ L - 1 + 1 = 2 ^ L := by omega
+  rw [hadd]
+  simp
+
+/-- The first all-ones terminal carrier is `3^L - 1`. -/
+@[simp] theorem canonicalBlockTerminalCarrier_allOnesOdd_zero
+    (L : ℕ) (hL : 0 < L) :
+    canonicalBlockTerminalCarrier (allOnesOdd L hL) 0 = 3 ^ L - 1 := by
+  unfold canonicalBlockTerminalCarrier
+  rw [canonicalBlockLength_allOnesOdd_zero,
+    canonicalBlockOddCore_allOnesOdd_zero]
+  simp
+
+/-- Powers of nine are one modulo four. -/
+private theorem nine_pow_mod_four (r : ℕ) :
+    9 ^ r % 4 = 1 := by
+  induction r with
+  | zero => norm_num
+  | succ r ih =>
+      rw [pow_succ, Nat.mul_mod, ih]
+
+/-- An odd power of three is three modulo four. -/
+private theorem three_pow_odd_mod_four (r : ℕ) :
+    3 ^ (2 * r + 1) % 4 = 3 := by
+  have hpow : 3 ^ (2 * r + 1) = 3 * 9 ^ r := by
+    rw [show 2 * r + 1 = 2 * r + 1 by rfl, pow_add, pow_mul]
+    norm_num
+    ring
+  rw [hpow, Nat.mul_mod, nine_pow_mod_four]
+
+/-- The carrier following an odd-length all-ones block is two modulo four. -/
+private theorem three_pow_odd_sub_one_mod_four (r : ℕ) :
+    (3 ^ (2 * r + 1) - 1) % 4 = 2 := by
+  have hmod := three_pow_odd_mod_four r
+  have hsplit := Nat.mod_add_div (3 ^ (2 * r + 1)) 4
+  have heq : 3 ^ (2 * r + 1) =
+      4 * (3 ^ (2 * r + 1) / 4) + 3 := by
+    omega
+  rw [heq]
+  simp
+
+/-- The exact terminal valuation of every odd-length all-ones initial block is
+one. -/
+theorem v2_three_pow_odd_sub_one (r : ℕ) :
+    v2 (3 ^ (2 * r + 1) - 1) = 1 := by
+  let c := 3 ^ (2 * r + 1) - 1
+  have hc4 : c % 4 = 2 := by
+    simpa [c] using three_pow_odd_sub_one_mod_four r
+  have hcpos : 0 < c := by
+    dsimp [c]
+    have hp : 1 < 3 ^ (2 * r + 1) := by
+      exact one_lt_pow₀ (by omega) (by omega)
+    omega
+  have hceven : c % 2 = 0 := by omega
+  have hhalfodd : (c / 2) % 2 = 1 := by omega
+  rw [v2_step_of_even c hceven hcpos, v2_odd _ hhalfodd]
+
+/-- Canonical terminal valuation of the odd-length all-ones first block. -/
+@[simp] theorem canonicalBlockTerminalValuation_allOnesOdd_odd_zero
+    (r : ℕ) :
+    canonicalBlockTerminalValuation
+      (allOnesOdd (2 * r + 1) (by omega)) 0 = 1 := by
+  unfold canonicalBlockTerminalValuation
+  rw [canonicalBlockTerminalCarrier_allOnesOdd_zero]
+  exact v2_three_pow_odd_sub_one r
+
+/-- Exact next-start state after an odd-length all-ones initial block. -/
+theorem canonicalBlockNextStartState_allOnesOdd_odd_zero
+    (r : ℕ) :
+    canonicalBlockNextStartState
+        (allOnesOdd (2 * r + 1) (by omega)) 0 =
+      (3 ^ (2 * r + 1) - 1) / 2 := by
+  rw [canonicalBlockNextStartState_eq_terminalCarrier_div_pow_valuation,
+    canonicalBlockTerminalCarrier_allOnesOdd_zero,
+    canonicalBlockTerminalValuation_allOnesOdd_odd_zero]
+  norm_num
+
+/-! ## Growing cross-root drift -/
+
+/-- Binary width of a positive finite all-ones word is its exponent. -/
+theorem bitWidth_two_pow_sub_one
+    (L : ℕ) (hL : 0 < L) :
+    bitWidth (2 ^ L - 1) = L := by
+  have hpow : 2 ^ L = 2 ^ (L - 1) * 2 := by
+    have hsplit : L = (L - 1) + 1 := by omega
+    calc
+      2 ^ L = 2 ^ ((L - 1) + 1) := congrArg (fun e => 2 ^ e) hsplit
+      _ = 2 ^ (L - 1) * 2 := by rw [pow_succ]
+  have hp : 0 < 2 ^ (L - 1) := pow_pos (by norm_num) _
+  have hlo : 2 ^ (L - 1) ≤ 2 ^ L - 1 := by omega
+  have hhi : 2 ^ L - 1 < 2 ^ ((L - 1) + 1) := by
+    have hsplit : L = (L - 1) + 1 := by omega
+    rw [← hsplit]
+    omega
+  have hwidth := bitWidth_eq_add_one_of_pow_le_lt hlo hhi
+  omega
+
+/-- Elementary exponential estimate used by the all-ones width lower bound. -/
+private theorem two_mul_eight_pow_add_one_le_three_mul_nine_pow
+    (r : ℕ) :
+    2 * 8 ^ r + 1 ≤ 3 * 9 ^ r := by
+  induction r with
+  | zero => norm_num
+  | succ r ih =>
+      rw [pow_succ, pow_succ]
+      have hpos : 0 < 9 ^ r := pow_pos (by norm_num) _
+      nlinarith
+
+/-- The odd-power carrier dominates the binary scale needed for a linear
+width gain. -/
+private theorem two_pow_three_mul_add_one_le_three_pow_odd_sub_one
+    (r : ℕ) :
+    2 ^ (3 * r + 1) ≤ 3 ^ (2 * r + 1) - 1 := by
+  have hbase := two_mul_eight_pow_add_one_le_three_mul_nine_pow r
+  have htwo : 2 ^ (3 * r + 1) = 2 * 8 ^ r := by
+    calc
+      2 ^ (3 * r + 1) = 2 ^ (3 * r) * 2 := by rw [pow_succ]
+      _ = (2 ^ 3) ^ r * 2 := by rw [pow_mul]
+      _ = 2 * 8 ^ r := by norm_num; ring
+  have hthree : 3 ^ (2 * r + 1) = 3 * 9 ^ r := by
+    calc
+      3 ^ (2 * r + 1) = 3 ^ (2 * r) * 3 := by rw [pow_succ]
+      _ = (3 ^ 2) ^ r * 3 := by rw [pow_mul]
+      _ = 3 * 9 ^ r := by norm_num; ring
+  rw [htwo, hthree]
+  omega
+
+/-- The next start after the odd all-ones block contains the `2^(3r)` binary
+scale. -/
+theorem two_pow_three_mul_le_allOnesOdd_nextStart (r : ℕ) :
+    2 ^ (3 * r) ≤
+      canonicalBlockNextStartState
+        (allOnesOdd (2 * r + 1) (by omega)) 0 := by
+  rw [canonicalBlockNextStartState_allOnesOdd_odd_zero]
+  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < (2 : ℕ))).2
+  calc
+    2 ^ (3 * r) * 2 = 2 ^ (3 * r + 1) := by rw [pow_succ]
+    _ ≤ 3 ^ (2 * r + 1) - 1 :=
+      two_pow_three_mul_add_one_le_three_pow_odd_sub_one r
+
+/-- The next-start binary width is at least `3r+1`. -/
+theorem three_mul_add_one_le_bitWidth_allOnesOdd_nextStart (r : ℕ) :
+    3 * r + 1 ≤ bitWidth
+      (canonicalBlockNextStartState
+        (allOnesOdd (2 * r + 1) (by omega)) 0) := by
+  let x := canonicalBlockNextStartState
+    (allOnesOdd (2 * r + 1) (by omega)) 0
+  have hlower : 2 ^ (3 * r) ≤ x := by
+    simpa [x] using two_pow_three_mul_le_allOnesOdd_nextStart r
+  have hxpos : 0 < x := (pow_pos (by norm_num) _).trans_le hlower
+  have hlt : 2 ^ (3 * r) < 2 ^ bitWidth x :=
+    hlower.trans_lt (lt_pow_bitWidth hxpos)
+  have hexp : 3 * r < bitWidth x :=
+    (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp hlt
+  change 3 * r + 1 ≤ bitWidth x
+  omega
+
+/-- Initial endpoint drift in the odd all-ones family grows at least linearly
+with the root parameter. -/
+theorem le_endpointAccountingTerm_allOnesOdd_odd_zero (r : ℕ) :
+    (r : ℤ) ≤ endpointAccountingTerm
+      (allOnesOdd (2 * r + 1) (by omega)) 0 := by
+  rw [endpointAccountingTerm_eq_canonicalBlock_bitWidth_sub,
+    canonicalBlockNextStartState_allOnesOdd_odd_zero,
+    canonicalBlockStartState_allOnesOdd_zero]
+  rw [bitWidth_two_pow_sub_one (2 * r + 1) (by omega)]
+  have hwidth := three_mul_add_one_le_bitWidth_allOnesOdd_nextStart r
+  rw [canonicalBlockNextStartState_allOnesOdd_odd_zero] at hwidth
+  omega
+
+/-- Across the family of odd roots, initial endpoint drift exceeds every
+integer threshold.  The quantified root depends on `B`; this theorem therefore
+does not make a fixed-root assertion. -/
+theorem exists_endpointAccountingTerm_gt (B : ℤ) :
+    ∃ n : OddNat, B < endpointAccountingTerm n 0 := by
+  let r := B.natAbs + 1
+  refine ⟨allOnesOdd (2 * r + 1) (by omega), ?_⟩
+  have hr : B < (r : ℤ) := by
+    have habs : B ≤ |B| := le_abs_self B
+    have hcast : (B.natAbs : ℤ) = |B| := by simp
+    rw [← hcast] at habs
+    simp [r]
+    omega
+  exact hr.trans_le (le_endpointAccountingTerm_allOnesOdd_odd_zero r)
+
+/-- There is no one endpoint-drift ceiling uniform across every odd root. -/
+theorem not_globalEndpointDriftBound :
+    ¬ GlobalEndpointDriftBound := by
+  rintro ⟨B, hB⟩
+  obtain ⟨n, hn⟩ := exists_endpointAccountingTerm_gt B
+  have hupper := hB n 0
+  omega
+
+/-!
+`not_globalEndpointDriftBound` varies the root with `r`.  It does not imply
+`¬ RootwiseEndpointDriftBound n` for any fixed `n`; that arithmetic question
+remains the exact fixed-root boundary isolated by cp-339.
+-/
+
+end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointDrift.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointDrift.lean
new file mode 100644
index 00000000..90def769
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointDrift.lean
@@ -0,0 +1,169 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeFiniteCertificate
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointDrift"
+
+namespace DkMath.Collatz
+
+/-!
+# Canonical endpoint drift
+
+This module isolates the arithmetic boundary left by the finite source-age
+certificate audit.  The endpoint term is exactly a binary-width difference.
+Two boundedness questions must therefore remain distinct:
+
+* `RootwiseEndpointDriftBound n` fixes one odd root and ranges over its blocks;
+* `GlobalEndpointDriftBound` asks for one ceiling shared by every odd root.
+
+A family of different roots may refute the second statement without saying
+anything about the first.  The distinction is part of the public API and must
+not be erased by later finite-signature work.
+-/
+
+/-! ## Exact canonical width ledger -/
+
+/-- The endpoint accounting term is exactly the signed width change from the
+canonical block start to the next canonical block start. -/
+theorem endpointAccountingTerm_eq_canonicalBlock_bitWidth_sub
+    (n : OddNat) (m : ℕ) :
+    endpointAccountingTerm n m =
+      (bitWidth (canonicalBlockNextStartState n m) : ℤ) -
+        bitWidth (canonicalBlockStartState n m) := by
+  rw [endpointAccountingTerm_eq_universalPaymentBlockSignedDriftAt,
+    universalPaymentBlockSignedDriftAt_eq_bitWidth_sub n
+      (paymentEndpointSeq n m)
+      (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n m)]
+  rw [← canonicalBlockStartTime_eq_universalPaymentBlockStart]
+  rfl
+
+/-- Canonical prefix telescope: the sum through block `m` is the width change
+from the initial root to the next start after block `m`. -/
+theorem sum_endpointAccountingTerm_eq_canonicalBlockNextStart_bitWidth_sub
+    (n : OddNat) (m : ℕ) :
+    (∑ k ∈ Finset.range (m + 1), endpointAccountingTerm n k) =
+      (bitWidth (canonicalBlockNextStartState n m) : ℤ) - bitWidth n.1 := by
+  simpa [canonicalBlockNextStartState] using
+    sum_endpointAccountingTerm_paymentEndpointSeq n m
+
+/-! ## Rootwise versus global boundedness -/
+
+/-- One fixed odd root has a uniform upper bound on all of its endpoint
+drifts. -/
+def RootwiseEndpointDriftBound (n : OddNat) : Prop :=
+  ∃ B : ℤ, ∀ m, endpointAccountingTerm n m ≤ B
+
+/-- One integer bounds endpoint drift simultaneously for every odd root and
+every canonical block.  This is strictly a cross-root statement. -/
+def GlobalEndpointDriftBound : Prop :=
+  ∃ B : ℤ, ∀ (n : OddNat) (m : ℕ), endpointAccountingTerm n m ≤ B
+
+/-- The cp-339 endpoint condition is exactly the rootwise condition. -/
+theorem rootwiseEndpointDriftBound_iff_canonicalEndpointUniformUpperBound
+    (n : OddNat) :
+    RootwiseEndpointDriftBound n ↔
+      CanonicalEndpointAccountingTermUniformUpperBound n :=
+  Iff.rfl
+
+/-- The fixed-horizon cp-339 frontier theorem concerns one fixed root only. -/
+theorem canonicalSourceAgeFrontierIncrementUniformUpperBound_iff_rootwiseEndpoint
+    (n : OddNat) (H : ℕ) :
+    CanonicalSourceAgeFrontierIncrementUniformUpperBound n H ↔
+      RootwiseEndpointDriftBound n := by
+  rw [rootwiseEndpointDriftBound_iff_canonicalEndpointUniformUpperBound]
+  exact canonicalSourceAgeFrontierIncrementUniformUpperBound_iff_endpoint n H
+
+/-- A global drift ceiling implies every rootwise ceiling.  The converse is
+not asserted: choosing a bound separately for each root need not produce one
+bound uniform across roots. -/
+theorem GlobalEndpointDriftBound.rootwise
+    (h : GlobalEndpointDriftBound) (n : OddNat) :
+    RootwiseEndpointDriftBound n := by
+  rcases h with ⟨B, hB⟩
+  exact ⟨B, hB n⟩
+
+/-! ## Exact positive-drift normal forms -/
+
+/-- Exact claim/capacity form with terminal capacity expressed by its 2-adic
+valuation.  Positivity is not needed for the identity. -/
+theorem endpointAccountingTerm_eq_claimCount_sub_terminalValuation
+    (n : OddNat) (m : ℕ) :
+    endpointAccountingTerm n m =
+      (canonicalBlockClaimCount n m : ℤ) -
+        canonicalBlockTerminalValuation n m := by
+  rw [endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount,
+    canonicalBlockCapacityCount_eq_terminalValuation]
+
+/-- Endpoint drift is bounded by block length minus terminal valuation. -/
+theorem endpointAccountingTerm_le_length_sub_terminalValuation
+    (n : OddNat) (m : ℕ) :
+    endpointAccountingTerm n m ≤
+      (canonicalBlockLength n m : ℤ) -
+        canonicalBlockTerminalValuation n m := by
+  simpa [canonicalBlockCapacityCount_eq_terminalValuation] using
+    endpointAccountingTerm_le_length_sub_capacity n m
+
+/-- Exact carry-word refinement: the gap between the coarse
+`length - valuation` ceiling and actual drift is precisely the number of
+missing claim depths. -/
+theorem endpointAccountingTerm_add_claimHoles_eq_length_sub_terminalValuation
+    (n : OddNat) (m : ℕ) :
+    endpointAccountingTerm n m + (canonicalBlockClaimHoles n m).card =
+      (canonicalBlockLength n m : ℤ) -
+        canonicalBlockTerminalValuation n m := by
+  rw [endpointAccountingTerm_eq_length_sub_terminalValuation_sub_claimHoles]
+  ring
+
+/-! ## Sufficient rootwise hypotheses
+
+These implications do not claim that any of their hypotheses holds.  They
+make explicit which arithmetic estimate would close the rootwise endpoint
+boundary.
+-/
+
+/-- A uniform canonical block-length ceiling is sufficient for rootwise drift
+boundedness. -/
+theorem rootwiseEndpointDriftBound_of_blockLength_bound
+    {n : OddNat} {B : ℕ}
+    (hB : ∀ m, canonicalBlockLength n m ≤ B) :
+    RootwiseEndpointDriftBound n := by
+  refine ⟨B, ?_⟩
+  intro m
+  calc
+    endpointAccountingTerm n m ≤
+        (canonicalBlockLength n m : ℤ) -
+          canonicalBlockTerminalValuation n m :=
+      endpointAccountingTerm_le_length_sub_terminalValuation n m
+    _ ≤ canonicalBlockLength n m := sub_le_self _ (Int.natCast_nonneg _)
+    _ ≤ B := Int.ofNat_le.mpr (hB m)
+
+/-- A direct uniform ceiling on `length - terminal valuation` is sufficient
+for rootwise endpoint-drift boundedness. -/
+theorem rootwiseEndpointDriftBound_of_length_sub_terminalValuation_bound
+    {n : OddNat} {B : ℤ}
+    (hB : ∀ m,
+      (canonicalBlockLength n m : ℤ) -
+        canonicalBlockTerminalValuation n m ≤ B) :
+    RootwiseEndpointDriftBound n := by
+  exact ⟨B, fun m =>
+    (endpointAccountingTerm_le_length_sub_terminalValuation n m).trans (hB m)⟩
+
+/-- A uniform additive bound on next-start width above start width is
+sufficient for rootwise endpoint-drift boundedness. -/
+theorem rootwiseEndpointDriftBound_of_nextStart_bitWidth_le_start_add
+    {n : OddNat} {B : ℕ}
+    (hB : ∀ m,
+      bitWidth (canonicalBlockNextStartState n m) ≤
+        bitWidth (canonicalBlockStartState n m) + B) :
+    RootwiseEndpointDriftBound n := by
+  refine ⟨B, ?_⟩
+  intro m
+  rw [endpointAccountingTerm_eq_canonicalBlock_bitWidth_sub]
+  have hwidth := hB m
+  omega
+
+end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteControlCounter.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteControlCounter.lean
new file mode 100644
index 00000000..caa4f6a1
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteControlCounter.lean
@@ -0,0 +1,138 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.FinitePotentialIncompleteness
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.FiniteControlCounter"
+
+namespace DkMath.Collatz
+
+/-!
+# Finite control with an unbounded counter
+
+A finite control projection need not store the full arithmetic resource.  This
+certificate keeps a separate signed counter, requires its exact recurrence,
+and requires a local guard that proves each realized transition preserves
+counter nonnegativity.  The soundness proof then derives all prefix
+inequalities by induction.
+
+This module intentionally does not instantiate the certificate with the
+canonical source-age deficit.  Such an instance is valid only after its local
+guard has been proved independently from canonical block arithmetic; using
+the desired prefix invariant itself as that guard would be circular.
+-/
+
+/-- A finite control sequence accompanied by an unrestricted integer counter.
+The recurrence and local guard are the arithmetic proof obligations. -/
+structure FiniteControlSignedCounterCertificate
+    (Signature : Type*) [Finite Signature] where
+  signature : ℕ → Signature
+  weight : ℕ → ℤ
+  credit : ℕ → ℤ
+  initial_credit_eq_zero : credit 0 = 0
+  credit_succ : ∀ m, credit (m + 1) = credit m - weight m
+  preserves_nonneg : ∀ m, 0 ≤ credit m → weight m ≤ credit m
+
+namespace FiniteControlSignedCounterCertificate
+
+variable {Signature : Type*} [Finite Signature]
+
+/-- Exact counter recurrence and the local guard preserve nonnegative credit
+at every realized transition. -/
+theorem credit_nonneg
+    (C : FiniteControlSignedCounterCertificate Signature) (M : ℕ) :
+    0 ≤ C.credit M := by
+  induction M with
+  | zero => rw [C.initial_credit_eq_zero]
+  | succ M ih =>
+      rw [C.credit_succ]
+      exact sub_nonneg.mpr (C.preserves_nonneg M ih)
+
+/-- Counter recurrence telescopes exactly: accumulated weight is initial
+credit minus final credit. -/
+theorem sum_weight_range_eq_credit_zero_sub
+    (C : FiniteControlSignedCounterCertificate Signature) (M : ℕ) :
+    (∑ m ∈ Finset.range M, C.weight m) = C.credit 0 - C.credit M := by
+  induction M with
+  | zero => simp
+  | succ M ih =>
+      rw [Finset.sum_range_succ, ih, C.credit_succ]
+      ring
+
+/-- Soundness: every prefix weight is nonpositive. -/
+theorem sum_weight_range_nonpos
+    (C : FiniteControlSignedCounterCertificate Signature) (M : ℕ) :
+    (∑ m ∈ Finset.range M, C.weight m) ≤ 0 := by
+  rw [C.sum_weight_range_eq_credit_zero_sub, C.initial_credit_eq_zero]
+  simpa only [zero_sub] using neg_nonpos.mpr (C.credit_nonneg M)
+
+end FiniteControlSignedCounterCertificate
+
+/-! ## Concrete realization on the incompleteness witness -/
+
+/-- Unbounded credit needed by the alternating sequence: zero after complete
+pairs and `k+1` after the negative term of pair `k`. -/
+def alternatingUnboundedCredit (M : ℕ) : ℤ :=
+  if M % 2 = 0 then 0 else ((M / 2 + 1 : ℕ) : ℤ)
+
+@[simp] theorem alternatingUnboundedCredit_even (k : ℕ) :
+    alternatingUnboundedCredit (2 * k) = 0 := by
+  simp [alternatingUnboundedCredit]
+
+@[simp] theorem alternatingUnboundedCredit_odd (k : ℕ) :
+    alternatingUnboundedCredit (2 * k + 1) = ((k + 1 : ℕ) : ℤ) := by
+  have hmod : (2 * k + 1) % 2 = 1 := by omega
+  have hdiv : (2 * k + 1) / 2 = k := by omega
+  simp [alternatingUnboundedCredit, hmod, hdiv]
+
+/-- Exact credit recurrence for the alternating witness. -/
+theorem alternatingUnboundedCredit_succ (M : ℕ) :
+    alternatingUnboundedCredit (M + 1) =
+      alternatingUnboundedCredit M - alternatingUnboundedWeight M := by
+  rcases Nat.even_or_odd M with ⟨k, rfl⟩ | ⟨k, rfl⟩
+  · have hpair : alternatingUnboundedCredit (2 * k + 1) =
+        alternatingUnboundedCredit (2 * k) -
+          alternatingUnboundedWeight (2 * k) := by simp
+    simpa [two_mul] using hpair
+  · have hpair : alternatingUnboundedCredit (2 * k + 1 + 1) =
+        alternatingUnboundedCredit (2 * k + 1) -
+          alternatingUnboundedWeight (2 * k + 1) := by
+      rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega]
+      simp
+    simpa [two_mul] using hpair
+
+/-- The explicit transition guard is checked locally from the parity branch,
+not inferred from a prefix theorem. -/
+theorem alternatingUnboundedWeight_le_credit
+    (M : ℕ) (hcredit : 0 ≤ alternatingUnboundedCredit M) :
+    alternatingUnboundedWeight M ≤ alternatingUnboundedCredit M := by
+  rcases Nat.even_or_odd M with ⟨k, rfl⟩ | ⟨k, rfl⟩
+  · have hpair : alternatingUnboundedWeight (2 * k) ≤
+        alternatingUnboundedCredit (2 * k) := by simp
+    simpa [two_mul] using hpair
+  · have hpair : alternatingUnboundedWeight (2 * k + 1) ≤
+        alternatingUnboundedCredit (2 * k + 1) := by simp
+    simpa [two_mul] using hpair
+
+/-- A one-state finite control with an unbounded arithmetic credit certifies
+the alternating sequence. -/
+def alternatingUnboundedCounterCertificate :
+    FiniteControlSignedCounterCertificate Unit where
+  signature := fun _ => ()
+  weight := alternatingUnboundedWeight
+  credit := alternatingUnboundedCredit
+  initial_credit_eq_zero := by simp [alternatingUnboundedCredit]
+  credit_succ := alternatingUnboundedCredit_succ
+  preserves_nonneg := alternatingUnboundedWeight_le_credit
+
+/-- Counter-certificate proof of the nonpositive-prefix property.  Together
+with the finite-table impossibility theorem, this is an explicit separation
+between finite potential and finite control with unbounded credit. -/
+theorem alternatingUnboundedCounterCertificate_sound (M : ℕ) :
+    (∑ m ∈ Finset.range M, alternatingUnboundedWeight m) ≤ 0 :=
+  alternatingUnboundedCounterCertificate.sum_weight_range_nonpos M
+
+end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FinitePotentialIncompleteness.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FinitePotentialIncompleteness.lean
new file mode 100644
index 00000000..4c0e73dc
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FinitePotentialIncompleteness.lean
@@ -0,0 +1,109 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.FinitePotentialIncompleteness"
+
+namespace DkMath.Collatz
+
+/-!
+# Finite-potential incompleteness witness
+
+Uniformly nonpositive prefix sums do not imply a pointwise upper bound on
+signed increments.  The explicit pair sequence below makes that distinction
+formal.  Consequently, a finite successor upper-weight table is a strictly
+stronger certificate shape than the prefix inequality it is intended to
+prove.
+-/
+
+/-- Alternating signed weights with cancelling pairs and unbounded positive
+odd-index terms:
+
+`w (2*k) = -(k+1)` and `w (2*k+1) = k+1`.
+-/
+def alternatingUnboundedWeight (m : ℕ) : ℤ :=
+  if m % 2 = 0 then -((m / 2 + 1 : ℕ) : ℤ)
+  else ((m / 2 + 1 : ℕ) : ℤ)
+
+@[simp] theorem alternatingUnboundedWeight_even (k : ℕ) :
+    alternatingUnboundedWeight (2 * k) = -((k + 1 : ℕ) : ℤ) := by
+  simp [alternatingUnboundedWeight]
+
+@[simp] theorem alternatingUnboundedWeight_odd (k : ℕ) :
+    alternatingUnboundedWeight (2 * k + 1) = ((k + 1 : ℕ) : ℤ) := by
+  have hmod : (2 * k + 1) % 2 = 1 := by omega
+  have hdiv : (2 * k + 1) / 2 = k := by omega
+  simp [alternatingUnboundedWeight, hmod, hdiv]
+
+/-- Every complete pair prefix has total zero. -/
+theorem sum_alternatingUnboundedWeight_range_even (k : ℕ) :
+    (∑ m ∈ Finset.range (2 * k), alternatingUnboundedWeight m) = 0 := by
+  induction k with
+  | zero => simp
+  | succ k ih =>
+      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
+        Finset.sum_range_succ,
+        show 2 * k + 1 = 2 * k + 1 by rfl,
+        Finset.sum_range_succ, ih]
+      simp
+
+/-- A prefix ending after a negative term has total `-(k+1)`. -/
+theorem sum_alternatingUnboundedWeight_range_odd (k : ℕ) :
+    (∑ m ∈ Finset.range (2 * k + 1), alternatingUnboundedWeight m) =
+      -((k + 1 : ℕ) : ℤ) := by
+  rw [Finset.sum_range_succ, sum_alternatingUnboundedWeight_range_even]
+  simp
+
+/-- Every prefix sum of the explicit sequence is nonpositive. -/
+theorem sum_alternatingUnboundedWeight_range_nonpos (M : ℕ) :
+    (∑ m ∈ Finset.range M, alternatingUnboundedWeight m) ≤ 0 := by
+  rcases Nat.even_or_odd M with ⟨k, rfl⟩ | ⟨k, rfl⟩
+  · simpa [two_mul] using
+      (show (∑ m ∈ Finset.range (2 * k), alternatingUnboundedWeight m) ≤ 0 by
+        rw [sum_alternatingUnboundedWeight_range_even])
+  · simpa [two_mul] using
+      (show (∑ m ∈ Finset.range (2 * k + 1), alternatingUnboundedWeight m) ≤ 0 by
+        rw [sum_alternatingUnboundedWeight_range_odd]
+        exact neg_nonpos.mpr (Int.natCast_nonneg _))
+
+/-- Positive individual terms of the sequence are unbounded above. -/
+theorem alternatingUnboundedWeight_not_bddAbove :
+    ∀ B : ℤ, ∃ m : ℕ, B < alternatingUnboundedWeight m := by
+  intro B
+  refine ⟨2 * B.natAbs + 1, ?_⟩
+  rw [alternatingUnboundedWeight_odd]
+  have habs : B ≤ |B| := le_abs_self B
+  have hcast : (B.natAbs : ℤ) = |B| := by simp
+  rw [← hcast] at habs
+  omega
+
+/-- No finite signature admits a sound successor upper-weight table for the
+explicit sequence, despite all of its prefixes being nonpositive. -/
+theorem no_finiteSignatureSuccessorUpperWeight_alternatingUnboundedWeight
+    {Signature : Type*} [Finite Signature]
+    (signature : ℕ → Signature) :
+    ¬ ∃ projectedUpperWeight : Signature → Signature → ℤ,
+      FiniteSignatureSuccessorUpperWeightSound signature
+        alternatingUnboundedWeight projectedUpperWeight := by
+  intro htable
+  have hbound :=
+    (exists_finiteSignatureSuccessorUpperWeight_iff_uniformUpperBound
+      signature alternatingUnboundedWeight).mp htable
+  rcases hbound with ⟨B, hB⟩
+  rcases alternatingUnboundedWeight_not_bddAbove B with ⟨m, hm⟩
+  exact (not_lt_of_ge (hB m)) hm
+
+/-!
+The two theorems
+`sum_alternatingUnboundedWeight_range_nonpos` and
+`no_finiteSignatureSuccessorUpperWeight_alternatingUnboundedWeight` formally
+separate the desired prefix property from the stronger finite-table method.
+Failure of that method is therefore not evidence that a prefix theorem is
+false; it is evidence that an unbounded counter may be required.
+-/
+
+end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-340.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-340.md
new file mode 100644
index 00000000..a277e376
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-340.md
@@ -0,0 +1,273 @@
+# Petal / Collatz implementation report: checkpoint 340
+
+Date: 2026-07-17
+
+## Status
+
+Checkpoint 340 attacked the endpoint-drift arithmetic boundary isolated by
+cp-339.  The requested exact normal forms, the cross-root all-ones family, the
+finite-potential counterexample, and the alternative finite-control counter
+surface are implemented without `sorry`.
+
+The new modules are:
+
+```text
+DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointDrift.lean
+DkMath/Collatz/PetalBridge/FloatWindow/CanonicalAllOnesDrift.lean
+DkMath/Collatz/PetalBridge/FloatWindow/FinitePotentialIncompleteness.lean
+DkMath/Collatz/PetalBridge/FloatWindow/FiniteControlCounter.lean
+```
+
+All four are exported by `DkMath.Collatz.PetalBridge.FloatWindow`.
+
+## Exact canonical endpoint ledger
+
+Lean now proves directly that every endpoint term is the signed binary-width
+change between consecutive canonical block starts:
+
+```text
+endpointAccountingTerm n m
+  = bitWidth (canonicalBlockNextStartState n m)
+      - bitWidth (canonicalBlockStartState n m).
+```
+
+The prefix telescope is also exposed under canonical names:
+
+```text
+sum_{k < m+1} endpointAccountingTerm n k
+  = bitWidth (canonicalBlockNextStartState n m) - bitWidth n.
+```
+
+Thus endpoint accounting is not an auxiliary approximation.  It is the exact
+width ledger of the canonical block process.
+
+## Rootwise and global boundedness
+
+Two predicates now prevent an invalid change of quantifiers:
+
+```text
+RootwiseEndpointDriftBound n
+  := exists B, forall m, endpointAccountingTerm n m <= B
+
+GlobalEndpointDriftBound
+  := exists B, forall n m, endpointAccountingTerm n m <= B.
+```
+
+The cp-339 fixed-horizon theorem is proved equivalent to the first predicate
+for the same fixed root `n`.  A global bound implies each rootwise bound, but
+no converse is asserted.
+
+## Odd all-ones root family
+
+For the root `2^L - 1`, Lean proves the exact first-block chain:
+
+```text
+block length       = L
+odd core           = 1
+terminal carrier   = 3^L - 1
+```
+
+For odd `L = 2*r+1` it additionally proves:
+
+```text
+v2 (3^(2*r+1) - 1) = 1
+next start = (3^(2*r+1) - 1) / 2.
+```
+
+The elementary exponential estimates in the module give:
+
+```text
+r <= endpointAccountingTerm (allOnesOdd (2*r+1)) 0.
+```
+
+Consequently, for every integer threshold `B`, there is an odd root whose
+initial endpoint drift exceeds `B`:
+
+```text
+exists_endpointAccountingTerm_gt (B : Int) :
+  exists n, B < endpointAccountingTerm n 0.
+```
+
+This proves:
+
+```text
+not_globalEndpointDriftBound : not GlobalEndpointDriftBound.
+```
+
+This is cross-root unboundedness.  The root depends on the threshold.  It does
+not prove `not (RootwiseEndpointDriftBound n)` for any fixed `n`.
+
+## Exact claim and valuation forms
+
+The endpoint term has the exact normal form:
+
+```text
+endpointAccountingTerm
+  = canonicalBlockClaimCount - canonicalBlockTerminalValuation.
+```
+
+It therefore satisfies the coarse estimate:
+
+```text
+endpointAccountingTerm
+  <= canonicalBlockLength - canonicalBlockTerminalValuation.
+```
+
+The exact loss from that ceiling is the finite claim-hole count:
+
+```text
+endpointAccountingTerm + card canonicalBlockClaimHoles
+  = canonicalBlockLength - canonicalBlockTerminalValuation.
+```
+
+This is the sharper universal statement requested in Stage E.  A large block
+with low terminal valuation creates only capacity; missing claim depths are
+the exact obstruction to realizing the full coarse drift.
+
+## Sufficient fixed-root conditions
+
+Three implications are now public:
+
+1. A uniform block-length bound implies rootwise endpoint-drift boundedness.
+2. A uniform bound on `blockLength - terminalValuation` implies it.
+3. A uniform additive bound on next-start width above start width implies it.
+
+These theorems do not claim that any hypothesis holds for a canonical orbit.
+They identify three honest arithmetic routes to the fixed-root goal.
+
+## Finite numerical audit
+
+For each listed root, the canonical recurrence was evaluated for at most 1000
+blocks, stopping earlier when a state repeated.  The table records the maximum
+observed endpoint drift and one block attaining it.
+
+| root | states | max drift | block | length | odd core | terminal v2 | claims | start width | next width |
+|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
+| 3 | 2 | 0 | 1 | 1 | 1 | 1 | 1 | 1 | 1 |
+| 7 | 4 | 1 | 0 | 3 | 1 | 1 | 2 | 3 | 4 |
+| 27 | 18 | 2 | 1 | 5 | 1 | 1 | 3 | 5 | 7 |
+| 31 | 17 | 2 | 0 | 5 | 1 | 1 | 3 | 5 | 7 |
+| 47 | 17 | 1 | 0 | 4 | 3 | 1 | 2 | 6 | 7 |
+| 59 | 7 | 1 | 0 | 2 | 15 | 1 | 2 | 6 | 7 |
+| 123 | 10 | 1 | 0 | 2 | 31 | 1 | 2 | 7 | 8 |
+| 255 | 8 | 0 | 0 | 8 | 1 | 5 | 5 | 8 | 8 |
+| 511 | 11 | 5 | 0 | 9 | 1 | 1 | 6 | 9 | 14 |
+| 1023 | 10 | 3 | 0 | 10 | 1 | 3 | 6 | 10 | 13 |
+| 2047 | 28 | 6 | 0 | 11 | 1 | 1 | 7 | 11 | 17 |
+| 4095 | 27 | 4 | 0 | 12 | 1 | 4 | 8 | 12 | 16 |
+
+The data visibly separates long block length from realized drift: root `255`
+has length eight but drift zero because valuation and missing claims absorb the
+capacity, while odd all-ones lengths with terminal valuation one can produce
+large initial drift.  No tested finite orbit is evidence for either rootwise
+boundedness or fixed-root unboundedness.
+
+## Finite-potential incompleteness witness
+
+The explicit signed sequence
+
+```text
+w (2*k)     = -(k+1)
+w (2*k + 1) =  (k+1)
+```
+
+is now formalized.  Lean proves:
+
+```text
+sum_{m < 2*k} w m     = 0
+sum_{m < 2*k+1} w m   = -(k+1)
+sum_{m < M} w m       <= 0
+```
+
+while its positive individual terms exceed every integer bound.  Therefore no
+finite signature can carry a sound finite successor upper-weight table for
+this sequence.
+
+This is a formal counterexample to completeness of the present finite-table
+method, not a counterexample to the desired prefix inequality.
+
+## Finite control with an unbounded counter
+
+`FiniteControlSignedCounterCertificate` separates finite control from an
+unrestricted integer credit.  Its obligations are:
+
+```text
+credit 0 = 0
+credit (m+1) = credit m - weight m
+0 <= credit m -> weight m <= credit m.
+```
+
+Lean derives nonnegative credit at every step, the exact telescope, and every
+nonpositive weight prefix.  The alternating witness is instantiated with a
+one-state finite control and an unbounded parity-dependent credit.
+
+The canonical source-age deficit is deliberately not instantiated.  Such an
+instance requires an independently proved arithmetic transition guard; using
+the desired prefix result as the guard would be circular.  Macro transitions
+were likewise not introduced, so no intermediate-prefix condition is hidden.
+
+## Facts now fixed
+
+1. Endpoint accounting is exactly canonical next-width minus start-width.
+2. Its prefixes telescope to the total canonical width change.
+3. Fixed-root and root-uniform boundedness are different public predicates.
+4. No endpoint-drift ceiling is uniform over all odd roots.
+5. The odd all-ones family proves this global failure symbolically.
+6. Cross-root failure does not decide any fixed-root bound.
+7. Claim holes exactly measure the loss from `length - valuation` capacity.
+8. Several useful arithmetic hypotheses are sufficient for a fixed-root bound.
+9. Nonpositive prefixes can coexist with unbounded positive increments and no
+   finite successor upper-weight table.
+10. Finite control plus an unbounded, independently guarded counter can still
+    certify all prefix inequalities.
+
+## Branch decision and honest boundary
+
+Stage C reached only global-across-roots unboundedness.  Per Stage K, the
+branch remains at the fixed-root investigation:
+
+```text
+RootwiseEndpointDriftBound n
+```
+
+is neither proved nor refuted for a general fixed root.  The all-ones roots
+cannot be reused to refute it because they vary with the requested threshold.
+
+The next meaningful attack must therefore prove one of:
+
+```text
+uniform block-length control for one fixed root;
+uniform control of blockLength - terminalValuation;
+uniform control of next-start width increments;
+or a symbolic repeated high-drift family inside one fixed root.
+```
+
+In parallel, the alternative counter route may proceed only after deriving a
+canonical exact recurrence and its nonnegativity-preservation guard directly
+from block arithmetic.  The diagnostic finite signature remains available,
+but no projected upper table should be claimed before the rootwise ceiling is
+proved.
+
+## Verification
+
+Passed during implementation:
+
+```text
+lake build DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointDrift
+lake build DkMath.Collatz.PetalBridge.FloatWindow.CanonicalAllOnesDrift
+lake build DkMath.Collatz.PetalBridge.FloatWindow.FinitePotentialIncompleteness
+lake build DkMath.Collatz.PetalBridge.FloatWindow.FiniteControlCounter
+lake build DkMath.Collatz.PetalBridge.FloatWindow
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath
+rg -n "\bsorry\b|\badmit\b" \
+  DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointDrift.lean \
+  DkMath/Collatz/PetalBridge/FloatWindow/CanonicalAllOnesDrift.lean \
+  DkMath/Collatz/PetalBridge/FloatWindow/FinitePotentialIncompleteness.lean \
+  DkMath/Collatz/PetalBridge/FloatWindow/FiniteControlCounter.lean
+git diff --check
+```
+
+The `rg` check returned no matches.  `DkMath.Collatz` is not a build target
+because this workspace has no aggregate `DkMath/Collatz.lean`; the actual
+top-level `DkMath` target passed instead.
````
`````
