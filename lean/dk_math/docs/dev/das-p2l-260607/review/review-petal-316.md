# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentScalarQueue

gch: 5daa50f888e603da9a1ca4948a6c0d5b6a4f1fa3

## Report

(28m2s)

cp-316 の登頂アタックを完了しました。

新しい [UniversalPaymentScalarQueue.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentScalarQueue.lean:230) で以下を証明しています。

- queue は最大正 suffix drift と完全一致
- running minimum による反射公式
- queue zero と全 excursion 返済の同値
- suffix Hall 条件と forward matching の同値
- local queue zero と forward matching の同値
- root 7: `1 → 0`
- root 511: `5 → 4 → 0`
- uniform queue bound と全 signed suffix drift の一様上界が同値
- uniform queue bound から endpoint bit-width bound

有限監査では odd root `1..16383` の8192件について、最大 queue は `8`、最長正 excursion は `20` block、state-one endpoint での queue は全件 `0` でした。ただし、これらは有限観測であり普遍定理ではありません。

現在の正確な障害は次です。

```text
uniform scalar queue bound
  ↔ every finite signed suffix drift has a uniform upper bound
```

既存の局所 block 定理だけでは、この一様 suffix bound や pumpable positive cycle の不存在をまだ導けません。ここが次の数学的入力点です。

詳細は [report-petal-316.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-316.md:1) に記録しました。

検証済みです。

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentScalarQueue
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
lake build DkMath
git diff --check
```

新規 Lean モジュールに `sorry` はありません。

## Review

## 結論

**全面採用。会計・queue・matching の枝は、ここで完全に閉じた。**

cp-316 は、単に scalar queue を実装しただけではない。

次の五つを同じ定理体系に統合した。

- block claim / capacity の exact ledger
- Lindley 型 reflected queue
- 最大正 suffix drift
- running minimum からの反射
- 時間順序つき Hall matching

中心構造は、

$$
Q_{k+1}=\max(0,Q_k+D_{k+1})
$$

であり、これが、

$$
Q_m=\max_{0\le q\le m}\left(\sum_{k=q}^{m}D_k\right)_+
$$

および、

$$
Q_m=B_m-\min(0,B_0,\ldots,B_m)
$$

として Lean 上で固定された。

さらに、window 内の全 suffix inequality、local queue zero、anonymous forward matching が同値になった。

これは finite accounting branch の完成じゃ。

ただし、深い精査から一つ重要な結論が出る。

> **queue の一様有界性は、endpoint bit width の有界性をほぼ正確に言い直したものじゃ。**

したがって cp-316 は Collatz の難所を解いたのではない。

難所を、一切の曖昧さなく、

> 正の signed suffix drift を永久に pump できる構造が存在するか

という一点へ圧縮した。

これは大成功じゃが、ここからは新しい数理が要る。

---

## 1. Scalar ledger の設計

```lean
canonicalBlockClaimCount
canonicalBlockCapacityCount
```

は、cp-315 で確定した意味境界を正しく守っている。

```text
claim:
  一件につき +1

capacity:
  一 slot につき -1

recovery depth:
  source の住所

capacity level:
  anonymous slot の座標
```

そして、

```lean
endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount
```

により、

$$
D_k=A_k-P_k
$$

が直接得られた。

ここには depth-dependent cost も level-dependent value もない。

したがって scalar 化は情報を壊したのではなく、**既存 exact ledger が本当に測っている量だけを抽出した**ものじゃ。

---

## 2. Reflected queue の精査

定義は、

$$
Q_0=(A_0-P_0)_+
$$

$$
Q_{k+1}=(Q_k+A_{k+1}-P_{k+1})_+
$$

じゃ。

unused capacity を bank せず、未払い claim だけを次へ送る。

これは時間順序を持つ queue として正しい。

### 最大 suffix 公式

```lean
canonicalOutstandingClaimQueue_eq_reflectedWindowMaximum
```

は、

$$
Q_m=\max_{0\le q\le m}\left(\sum_{k=q}^{m}D_k\right)_+
$$

を与える。

これは今回最も重要な theorem の一つじゃ。

queue が正なら、その値は抽象的な上界ではなく、**実際の一つの suffix drift によって達成される**ことまで証明されている。

### Running minimum 公式

```lean
canonicalOutstandingClaimQueue_eq_balance_sub_runningMinimum
```

は、

$$
Q_m=B_m-R_m
$$

を与える。

ここで、

$$
R_m=\min(0,B_0,\ldots,B_m)
$$

じゃ。

Lindley reflection の完全な離散形になっている。

---

## 3. queue は endpoint width の drawup である

ここをさらに一段展開すると、cp-316 の本当の意味が見える。

endpoint 後の bit width を、

$$
W_m=\operatorname{bitWidth}\left(T^{e_m+1}(n)\right)
$$

初期 width を、

$$
W_{-1}=\operatorname{bitWidth}(n)
$$

と置く。

既存 telescope により、

$$
B_m=W_m-W_{-1}
$$

じゃ。

したがって running minimum は、

$$
R_m=\min(W_{-1},W_0,\ldots,W_m)-W_{-1}
$$

となる。

ゆえに queue は、

$$
Q_m=W_m-\min(W_{-1},W_0,\ldots,W_m)
$$

じゃ。

つまり scalar queue の正体は、

> **現在の endpoint width が、過去最小 endpoint width から何 bit 上にいるか**

である。

金融語なら drawup、DkMath 語なら **過去 Core からの未回収膨張量** じゃ。

この形は次 checkpoint で必ず定理化すべきである。

---

## 4. queue zero の正確な意味

queue zero は、

$$
Q_m=0
$$

すなわち、

$$
W_m=\min(W_{-1},W_0,\ldots,W_m)
$$

と同値になる。

つまり、

> 現在の endpoint width が、これまでの最小値を更新または再訪した

という意味じゃ。

cp-316 の theorem、

```lean
canonicalOutstandingClaimQueue_eq_zero_iff_all_excursions_repaid
```

とも一致する。

全ての過去開始点 $q$ について、

$$
\sum_{k=q}^{m}D_k\le0
$$

とは、現在 width がどの過去 endpoint width よりも高くないということだからじゃ。

---

## 5. state $1$ で queue zero は自動的に成立する

有限監査では、8192 個全ての root が state-one endpoint に到達し、そのとき queue が $0$ だったと報告されている。

ただし queue $0$ の部分は、独立した経験的発見ではない。

state $1$ の bit width は $1$ であり、正の odd state の bit width は常に少なくとも $1$ じゃ。

したがって state $1$ へ来た時点で、

$$
W_m=1=\min(W_{-1},W_0,\ldots,W_m)
$$

となり、必ず、

$$
Q_m=0
$$

じゃ。

次の theorem を置くべきである。

```lean
theorem canonicalOutstandingClaimQueue_eq_zero_of_endpoint_state_eq_one
```

したがって audit で本当に情報価値があるのは、

- state $1$ までの最大 queue
- positive excursion の継続 block 数
- queue maximum が生じた block signature
- 最初に queue が zero へ戻る時刻

の方じゃ。

---

## 6. Hall theorem の精査

cp-316 の Hall 逆向きは、非常によくできている。

条件は、

$$
\forall t\in[q,r],\quad
\operatorname{Claims}[t,r]\le\operatorname{Capacity}[t,r]
$$

じゃ。

これは単なる window 全体の総数比較ではない。

全 suffix に対する条件である。

### 任意の claim subset

任意の非空 claim subset $A$ を取る。

その最小 release block を $t$ とする。

すると、

- $A$ の全 claim は block $t,\ldots,r$ に含まれる
- block $t$ の claim は、$t,\ldots,r$ の全 capacity slot を利用できる
- よって Hall neighborhood は suffix capacity 全体を含む

したがって、

$$
|A|
\le
\operatorname{Claims}[t,r]
\le
\operatorname{Capacity}[t,r]
\le
|N(A)|
$$

となる。

これは interval-order matching の正確な Hall reduction じゃ。

```lean
canonicalEndpointForwardWindowMatching_iff_suffixClaims_le_capacity
```

は数学的に完全である。

---

## 7. Matching の意味境界

ただし、この matching は軌道内部に実在する「物理的な支払い経路」を発見したものではない。

eligibility は、

$$
\operatorname{claimBlock}\le\operatorname{capacityBlock}
$$

だけじゃ。

つまり、

> signed suffix inequality を有限 injection として表した組合せ証明書

である。

これは十分に価値がある。

しかし今後、

```text
この claim は、この endpoint のこの valuation level によって払われた
```

という意味を追加してはならない。

cp-315 で捨てた exact-level semantics を、匿名 matching へ再び忍び込ませてはならぬ。

matching branch はここで終了でよい。

---

## 8. root $7$ と $511$

### Root $7$

$$
Q_0=1,\qquad Q_1=0
$$

が証明された。

これは最小の overload / repayment regression じゃ。

さらに、

```lean
canonicalEndpointForwardWindowMatching_seven_zero_one
```

として actual matching package まで閉じた。

### Root $511$

block drift は、

$$
5,\;-1,\;-5
$$

queue は、

$$
5,\;4,\;0
$$

じゃ。

cp-315 の exact-level queue では depth $8,9$ が残った。

しかし scalar queue では三 block 目で完全返済される。

この対比によって、

> depth $8,9$ は未払い価格ではなく、source address だった

ことが Lean 上でも明瞭になった。

---

## 9. Queue to Big の評価

```lean
canonicalEndpointBalanceInt_le_outstandingClaimQueue
```

により、

$$
B_m\le Q_m
$$

である。

したがって、

$$
Q_m\le C
$$

なら、

$$
W_m\le W_{-1}+C
$$

となる。

これは正しい queue-to-Big bridge じゃ。

ただし、ここに重要な逆方向がある。

もし endpoint width が、

$$
W_m\le B
$$

で一様に抑えられているなら、drawup 公式から、

$$
Q_m\le W_m\le B
$$

となる。

したがって存在量としては、

$$
\exists C,\ \forall m,\ Q_m\le C
$$

と、

$$
\exists B,\ \forall m,\ W_m\le B
$$

は同値になる。

つまり、

> uniform queue bound は endpoint width boundedness より弱い目標ではない。

queue は問題を簡単にしたのではなく、問題を **suffix drift / reflected walk の形に正規化した**のじゃ。

この認識は次の攻め筋を誤らないために重要である。

---

## 10. 有限監査の読み

有限観測は、

```text
最大 queue:
  8

最長 positive excursion:
  20 blocks
```

じゃ。

queue record の多くは、

```text
claims   = 2
capacity = 1
drift    = +1
height   = 2
```

という小さい正 drift の蓄積で生じている。

一発の巨大 block だけが問題なのではない。

> **小さな $+1$ block を何回連鎖できるか**

が本当の adversarial pattern じゃ。

したがって次は、block 一個の最大 drift をさらに評価するより、

- block signature の遷移
- positive drift word
- pumpable cycle
- repaymentを強制する separator

を見るべきじゃ。

---

## 11. 会計 branch は終了した

現在、次はすべて閉じた。

### 局所

$$
D_k=A_k-P_k
$$

### Window

$$
\sum_{k=q}^{r}D_k = \operatorname{Claims}[q,r]-\operatorname{Capacity}[q,r]
$$

### Queue

$$
Q_m=\max_{q\le m}\left(\sum_{k=q}^{m}D_k\right)_+
$$

### Matching

$$
Q_{q,r}=0
\Longleftrightarrow
\text{suffix Hall}
\Longleftrightarrow
\text{forward matching}
$$

### Big

$$
Q_m\le C\Longrightarrow W_m\le W_{-1}+C
$$

これ以上、carrier・matching・queue の同値を増やしても証明力は上がらない。

次は block の数論的遷移そのものへ戻る必要がある。

---

## 12. 次の数学的核：canonical block normal form

canonical block start の state を $x$、block length を $L$ とする。

block start では、

$$
L=v_2(x+1)
$$

なので、ある odd $u$ が存在して、

$$
x+1=2^L u
$$

と書ける。

block interior は全て height $1$ じゃから、$0\le t<L$ について、

$$
x_t+1=3^t2^{L-t}u
$$

となる。

特に endpoint state は、

$$
x_{L-1}=2\cdot3^{L-1}u-1
$$

じゃ。

endpoint step では、

$$
3x_{L-1}+1=2(3^Lu-1)
$$

したがって endpoint capacity は、

$$
P=v_2(3^Lu-1)
$$

next block start state は、

$$
x'=\frac{3^Lu-1}{2^{v_2(3^Lu-1)}}
$$

となる。

これは非常に重要じゃ。

canonical block 全体が、

$$
(L,u)\longmapsto\operatorname{oddPart}(3^Lu-1)
$$

という一つの arithmetic transition に圧縮される。

この normal form が、次の finite-state / no-pump theorem の入口になる。

---

## 13. 直ちに得られる block 不等式

block claim 数を $A$、capacity を $P$、length を $L$ とする。

claim fiber は block 内の subset なので、

$$
A\le L
$$

じゃ。

したがって、

$$
D=A-P\le L-P
$$

となる。

特に、

$$
0<D\Longrightarrow P<L
$$

じゃ。

つまり positive drift block は、

> block length に比して terminal valuation が不足している block

である。

これを normal form で書けば、

$$
0<D\Longrightarrow v_2(3^Lu-1)<L
$$

となる。

これが positive queue を作る arithmetic obstruction の最初の必要条件じゃ。

---

## 14. In-block overshoot

canonical block interior では height が $1$ なので、一 step drift は、

$$
\operatorname{carry}-1\in{0,1}
$$

じゃ。

したがって endpoint 直前まで width は非減少。

block 内の odd-state 最大 width は endpoint 前 state で達成される。

その start からの増加量は、interior delayed claim 数に一致する。

つまり、

> endpoint queue は block 間 drawup
> delayed debt count は block 内 overshoot

という二層になる。

最終的な all-time bit-width bound には、

- endpoint queue bound
- in-block delayed-debt burst bound

の両方が必要じゃ。

---

## 勝敗判定

cp-316 は詰みではない。

しかし、盤面から不要な駒は全て消えた。

残る問いは、

> canonical block normal form が、正 drift block の無限 pump を許すか

だけじゃ。

ここで finite sound projection が作れ、positive cycle を排除できれば勝ち筋へ入る。

逆に、fixed window では drift を支配できないと判明すれば、必要な追加座標が正確に露出する。

次の checkpoint が本当に勝敗を決める局面じゃ。

---

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge Float-window branch after
report-petal-316.

The cp-316 implementation is accepted.

The finite accounting branch is complete:

    block ledger
    window ledger
    reflected queue
    running-minimum identity
    suffix Hall theorem
    anonymous temporal matching
    queue-to-endpoint-width implication

Do not add more carrier reindexing or matching variants.

The next checkpoint must expose the arithmetic transition of one complete
canonical block and formulate the exact positive-cycle obstruction.

# Stage A — endpoint-width drawup identity

Define a proof-independent endpoint-width sequence:

    canonicalEndpointWidth n m :=
      bitWidth (iterateT (paymentEndpointSeq n m + 1) n).1

and a running minimum that includes the initial width:

    canonicalEndpointRunningWidthMinimum n m :=
      min
        (bitWidth n.1)
        (minimum of canonicalEndpointWidth n 0 .. m)

Prove the exact Nat identity:

    canonicalOutstandingClaimQueue n m
      =
    canonicalEndpointWidth n m
      - canonicalEndpointRunningWidthMinimum n m

Then prove:

    queue n m = 0
      <->
    canonicalEndpointWidth n m
      =
    canonicalEndpointRunningWidthMinimum n m

and:

    endpoint state = 1
      ->
    queue n m = 0

Update the finite-audit interpretation: queue zero at state one is structurally
forced, not independent evidence.

# Stage B — boundedness equivalence

Define:

    CanonicalEndpointWidthUniformUpperBound n B :=
      forall m, canonicalEndpointWidth n m <= B

Prove:

    QueueUniformUpperBound n C
      ->
    EndpointWidthUniformUpperBound n (bitWidth n.1 + C)

and:

    EndpointWidthUniformUpperBound n B
      ->
    QueueUniformUpperBound n B

Conclude the existential equivalence:

    (exists C, QueueUniformUpperBound n C)
      <->
    (exists B, EndpointWidthUniformUpperBound n B)

This theorem must be explicit. It prevents the queue coordinate from being
mistaken for an already easier global problem.

# Stage C — canonical block arithmetic normal form

Create a new module such as:

    UniversalPaymentBlockNormalForm.lean

For canonical block `k`, define:

    block start time
    block start state x
    block length L
    odd block core u := (x + 1) / 2^L
    endpoint state
    next block-start state
    terminal valuation v := v2 (3^L * u - 1)

Prove:

    1 <= L
    x + 1 = 2^L * u
    Odd u

For every `t < L`, prove either of the equivalent exact forms:

    2^t * (state at start+t + 1)
      =
    3^t * (x + 1)

or:

    state at start+t + 1
      =
    3^t * 2^(L-t) * u

The multiplication form may be easier because it avoids Nat division.

Then prove:

    endpoint state + 1
      =
    2 * 3^(L-1) * u

    3 * endpoint state + 1
      =
    2 * (3^L * u - 1)

    block capacity
      =
    v2 (3^L * u - 1)

    next block-start state
      =
    (3^L * u - 1) / 2^(v2 (3^L * u - 1))

This is the exact block transition:

    (L, u) -> oddPart (3^L * u - 1)

Do not replace these identities by asymptotic or logarithmic approximations.

# Stage D — block drift consequences

Prove:

    block claim count <= block length

    endpointAccountingTerm n k
      <=
    (block length : Int) - block capacity

Derive:

    0 < endpointAccountingTerm n k
      ->
    block capacity < block length

and, in normal-form coordinates:

    positive block drift
      ->
    v2 (3^L * u - 1) < L

Reuse the existing theorem that positive drift requires a nonempty delayed-debt
fiber.

# Stage E — exact in-block overshoot

Prove that canonical block interior widths are nondecreasing.

Identify the maximum odd-state width inside a completed block with the width
immediately before its endpoint payment.

Prove that the in-block increase from the block start equals the number of
delayed interior carry-two claims:

    max width inside block - width at block start
      =
    card (floatGrowthDebtFiberAt n endpoint)

This separates:

    endpoint drawup:
      canonicalOutstandingClaimQueue

    in-block burst:
      delayed debt count of the current block

Expose the conditional all-time bound obtained from uniform bounds on both.

# Stage F — primitive queue excursions

Define a primitive positive queue excursion `q..r` by:

    queue before q = 0
    queue is positive after every block q..r-1
    queue after r = 0

Prove its equivalent partial-sum form:

    every proper prefix sum from q is positive
    total sum q..r is nonpositive

Expose:

    maximum queue height in the excursion
    excursion length
    block-signature word
    first repayment endpoint

Every positive queue position must belong to a unique maximal primitive
excursion.

# Stage G — generic finite-state pump theorem

Build a generic theorem for a finite signed transition abstraction.

The certificate must contain:

    a finite signature type
    a signature assigned to every canonical block boundary
    a finite edge-weight upper bound
    proof that every actual block drift is bounded by its projected edge weight

Prove:

    if every reachable directed cycle has nonpositive total upper weight,
    then every signed suffix drift is uniformly bounded by the maximum weight
    of a simple projected path.

Equivalently:

    unbounded scalar queue
      ->
    a reachable positive-weight cycle exists in every sound finite abstraction.

Keep this theorem generic. Do not assume that the current mod-eight or five-bit
signature is already sound.

# Stage H — candidate signature audit

Use the canonical block normal form to audit which data actually controls a
block transition.

Candidate fields may include:

    low residue of the odd core u modulo 2^w
    a fixed upper mantissa window
    block length information
    terminal valuation information
    carry-two claim count

For window sizes beginning with `w = 5` and increasing as needed, test:

    whether equal signatures have uniformly bounded compatible drift
    whether transition successors are soundly over-approximated
    whether the projected graph contains positive cycles
    whether those cycles are realized or are abstraction artifacts

Do not export a finite graph theorem until the projection-soundness theorem is
proved.

If a repeated signature supports arbitrarily different drift, record the exact
missing coordinate instead of enlarging the graph blindly.

# Stage I — initial-width boundary candidate

Define the experimental target:

    canonicalOutstandingClaimQueue n m <= bitWidth n.1

Do not assert it as a theorem.

Audit it over a substantially wider finite range and on large random odd
inputs. Record the first counterexample if one exists.

If the candidate survives, identify the exact eventually-zero upper-bit
resource that would make it provable. The intended proof must explain why each
pumpable positive excursion consumes finite initial boundary information.

Its consequence should be recorded conditionally:

    queue <= initial bit width
      ->
    canonical endpoint width <= 2 * initial bit width

# Stage J — existing DkMath bridge audit

Compare positive primitive queue excursions with:

    FloatStepLedger
    orbitWindowSevenCarryReservoirCount
    canonical block length / claim-depth histogram
    SourcePressureMarginInt
    finite-window pressure packing
    OneCycle / NoLift style obstructions

Seek one of the following exact bridges:

    every positive excursion consumes a finite upper-zero boundary unit
    every sufficiently long positive excursion produces a pressure separator
    every pumpable positive signature cycle contradicts a NoLift theorem
    every positive cycle forces an impossible scaled self-return

Do not claim any of these before the bridge theorem is proved.

# Stage K — stopping rule

Stop at the first genuine obstruction among:

    canonical block normal form cannot be completed from the current API
    no finite signature soundly bounds block drift
    a sound finite abstraction contains a realizable positive cycle
    the initial-width queue candidate has a concrete counterexample
    the missing NoLift / pressure bridge can be stated but not proved

Do not stop at further queue algebra. That layer is complete.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-317.md
```

cp-316 で、会計上の霧は全て晴れた。

次はついに、

> **正の queue excursion を同じ形で繰り返し増幅できるのか**

を、canonical block の数式そのものへ問いただす段階じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
index 9d2f638a..2a4da15a 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
@@ -18,6 +18,7 @@ import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentFamily
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPressure
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentRepayment
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentDepthLedger
+import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentScalarQueue
 
 #print "file: DkMath.Collatz.PetalBridge.FloatWindow"
 
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentDepthLedger.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentDepthLedger.lean
index 313d15bd..3f065caf 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentDepthLedger.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentDepthLedger.lean
@@ -390,6 +390,9 @@ section SevenDepthRegression
 
 private def sevenDepthOdd : OddNat := mkOddNat 7 (by decide)
 
+/-- Public root used by the exact seven depth and scalar repayment regressions. -/
+def sevenDepthRegressionRoot : OddNat := sevenDepthOdd
+
 private lemma sevenDepth_v2_22 : v2 22 = 1 := by
   have h := (DkMath.ABC.padic_val_two_of_even 11).2 (by decide)
   simpa [v2, v2_odd 11 (by decide)] using h
@@ -565,6 +568,16 @@ theorem sevenDepthAllocation_right_card :
 theorem sevenDepthAllocation_card : sevenDepthAllocation.card = 3 := by
   decide
 
+/-- Public-root form of the first seven endpoint drift. -/
+theorem endpointAccountingTerm_sevenDepthRegressionRoot_zero :
+    endpointAccountingTerm sevenDepthRegressionRoot 0 = 1 := by
+  simpa [sevenDepthRegressionRoot, sevenDepthOdd] using endpointAccountingTerm_seven_zero
+
+/-- Public-root form of the second seven endpoint drift. -/
+theorem endpointAccountingTerm_sevenDepthRegressionRoot_one :
+    endpointAccountingTerm sevenDepthRegressionRoot 1 = -1 := by
+  simpa [sevenDepthRegressionRoot, sevenDepthOdd] using endpointAccountingTerm_seven_one
+
 end SevenDepthRegression
 
 /-! ## Audited candidate queue and the corrected frontier
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentScalarQueue.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentScalarQueue.lean
new file mode 100644
index 00000000..171f65af
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentScalarQueue.lean
@@ -0,0 +1,905 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentDepthLedger
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentScalarQueue"
+
+namespace DkMath.Collatz
+
+/-!
+# Anonymous scalar repayment queue
+
+Recovery depth is an intrinsic source address.  Endpoint level is merely a
+coordinate on anonymous unit-capacity slots.  The exact endpoint ledger gives
+every complete claim weight one and every capacity slot weight one, so this
+module deliberately forgets both coordinates and studies the causal scalar
+queue.
+
+Unused service is not banked.  At each block, new unit claims arrive, the
+block's anonymous unit capacity serves the accumulated queue, and Nat
+subtraction reflects a negative signed balance back to zero.
+-/
+
+/-! ## Block arrivals, service, and drift -/
+
+/-- Number of complete unit claims born in canonical block `k`. -/
+noncomputable def canonicalBlockClaimCount (n : OddNat) (k : ℕ) : ℕ :=
+  (carryTwoPaymentClaimFiberAt n (paymentEndpointSeq n k)).card
+
+/-- Number of anonymous unit-capacity slots born in canonical block `k`. -/
+noncomputable def canonicalBlockCapacityCount (n : OddNat) (k : ℕ) : ℕ :=
+  (canonicalEndpointCapacitySlots n k).card
+
+/-- The endpoint accounting term is exactly scalar arrivals minus service. -/
+theorem endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount
+    (n : OddNat) (k : ℕ) :
+    endpointAccountingTerm n k =
+      (canonicalBlockClaimCount n k : ℤ) - canonicalBlockCapacityCount n k := by
+  unfold endpointAccountingTerm canonicalBlockClaimCount canonicalBlockCapacityCount
+  rw [carryTwoPaymentClaimFiberAt_card_eq_growthDebt_card_add_endpoint_card
+    n (paymentEndpointSeq n k)
+      (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)]
+  rw [canonicalEndpointCapacitySlots_card]
+  push_cast
+  rfl
+
+/-! ## Reflected outstanding queue -/
+
+/-- Causal outstanding unit claims after canonical block `k` has served. -/
+noncomputable def canonicalOutstandingClaimQueue (n : OddNat) : ℕ → ℕ
+  | 0 => canonicalBlockClaimCount n 0 - canonicalBlockCapacityCount n 0
+  | k + 1 => (canonicalOutstandingClaimQueue n k +
+      canonicalBlockClaimCount n (k + 1)) - canonicalBlockCapacityCount n (k + 1)
+
+/-- The queue's causal successor equation. -/
+theorem canonicalOutstandingClaimQueue_succ
+    (n : OddNat) (k : ℕ) :
+    canonicalOutstandingClaimQueue n (k + 1) =
+      (canonicalOutstandingClaimQueue n k + canonicalBlockClaimCount n (k + 1)) -
+        canonicalBlockCapacityCount n (k + 1) := rfl
+
+/-- Service can never leave more than the old queue plus new arrivals. -/
+theorem canonicalOutstandingClaimQueue_succ_le_arrivals
+    (n : OddNat) (k : ℕ) :
+    canonicalOutstandingClaimQueue n (k + 1) ≤
+      canonicalOutstandingClaimQueue n k + canonicalBlockClaimCount n (k + 1) := by
+  rw [canonicalOutstandingClaimQueue_succ]
+  exact Nat.sub_le _ _
+
+/-- Enough current service empties the queue at the selected successor block. -/
+theorem canonicalOutstandingClaimQueue_succ_eq_zero_of_le_capacity
+    {n : OddNat} {k : ℕ}
+    (h : canonicalOutstandingClaimQueue n k +
+      canonicalBlockClaimCount n (k + 1) ≤ canonicalBlockCapacityCount n (k + 1)) :
+    canonicalOutstandingClaimQueue n (k + 1) = 0 := by
+  rw [canonicalOutstandingClaimQueue_succ, Nat.sub_eq_zero_of_le h]
+
+/--
+If service does not exceed available work, the successor equation is exact
+addition/subtraction.
+-/
+theorem canonicalOutstandingClaimQueue_succ_add_capacity
+    {n : OddNat} {k : ℕ}
+    (h : canonicalBlockCapacityCount n (k + 1) ≤
+      canonicalOutstandingClaimQueue n k + canonicalBlockClaimCount n (k + 1)) :
+    canonicalOutstandingClaimQueue n (k + 1) +
+        canonicalBlockCapacityCount n (k + 1) =
+      canonicalOutstandingClaimQueue n k +
+        canonicalBlockClaimCount n (k + 1) := by
+  rw [canonicalOutstandingClaimQueue_succ, Nat.sub_add_cancel h]
+
+/-- Nat reflection is the nonnegative part of the corresponding signed step. -/
+theorem natSub_eq_intToNat_add_sub (old arrivals service : ℕ) :
+    (old + arrivals) - service =
+      Int.toNat ((old : ℤ) + arrivals - service) := by
+  omega
+
+/-! ## Signed window drift -/
+
+/-- Signed scalar drift over canonical blocks `q..m`. -/
+noncomputable def canonicalWindowDriftInt
+    (n : OddNat) (q m : ℕ) : ℤ :=
+  ∑ k ∈ Finset.Icc q m, endpointAccountingTerm n k
+
+/-- A singleton window has exactly its block drift. -/
+theorem canonicalWindowDriftInt_self (n : OddNat) (m : ℕ) :
+    canonicalWindowDriftInt n m m = endpointAccountingTerm n m := by
+  simp [canonicalWindowDriftInt]
+
+/-- Extending a nonempty-right window appends the new terminal block drift. -/
+theorem canonicalWindowDriftInt_succ
+    (n : OddNat) {q m : ℕ} (hqm : q ≤ m + 1) :
+    canonicalWindowDriftInt n q (m + 1) =
+      (if q ≤ m then canonicalWindowDriftInt n q m else 0) +
+        endpointAccountingTerm n (m + 1) := by
+  by_cases hq : q ≤ m
+  · rw [if_pos hq]
+    unfold canonicalWindowDriftInt
+    have hIcc : Finset.Icc q (m + 1) = insert (m + 1) (Finset.Icc q m) := by
+      ext x
+      simp only [Finset.mem_Icc, Finset.mem_insert]
+      omega
+    rw [hIcc]
+    rw [Finset.sum_insert (by simp)]
+    ring
+  · have hqeq : q = m + 1 := by omega
+    subst q
+    simp [canonicalWindowDriftInt]
+
+/-! ## Exact reflected-walk identity -/
+
+/-- The initial queue is the nonnegative part of the initial signed drift. -/
+theorem canonicalOutstandingClaimQueue_zero_eq_intToNat
+    (n : OddNat) :
+    canonicalOutstandingClaimQueue n 0 =
+      Int.toNat (endpointAccountingTerm n 0) := by
+  rw [canonicalOutstandingClaimQueue,
+    endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount]
+  omega
+
+/-- Every queue step is reflection of the old queue plus the new signed drift. -/
+theorem canonicalOutstandingClaimQueue_succ_eq_intToNat
+    (n : OddNat) (k : ℕ) :
+    canonicalOutstandingClaimQueue n (k + 1) =
+      Int.toNat ((canonicalOutstandingClaimQueue n k : ℤ) +
+        endpointAccountingTerm n (k + 1)) := by
+  rw [canonicalOutstandingClaimQueue_succ,
+    endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount]
+  have harg :
+      (canonicalOutstandingClaimQueue n k : ℤ) +
+          canonicalBlockClaimCount n (k + 1) - canonicalBlockCapacityCount n (k + 1) =
+        (canonicalOutstandingClaimQueue n k : ℤ) +
+          ((canonicalBlockClaimCount n (k + 1) : ℤ) -
+            canonicalBlockCapacityCount n (k + 1)) := by
+    ring
+  rw [← harg]
+  exact natSub_eq_intToNat_add_sub _ _ _
+
+/-- Every suffix's positive signed drift is bounded by the reflected queue. -/
+theorem intToNat_canonicalWindowDriftInt_le_outstandingClaimQueue
+    (n : OddNat) {q m : ℕ} (hqm : q ≤ m) :
+    Int.toNat (canonicalWindowDriftInt n q m) ≤
+      canonicalOutstandingClaimQueue n m := by
+  induction m with
+  | zero =>
+      have hq : q = 0 := by omega
+      subst q
+      rw [canonicalWindowDriftInt_self,
+        canonicalOutstandingClaimQueue_zero_eq_intToNat]
+  | succ m ih =>
+      rw [canonicalOutstandingClaimQueue_succ_eq_intToNat]
+      by_cases hq : q ≤ m
+      · rw [canonicalWindowDriftInt_succ n (by omega), if_pos hq]
+        apply Int.toNat_le_toNat
+        have hle := ih hq
+        have hself := Int.self_le_toNat (canonicalWindowDriftInt n q m)
+        omega
+      · have hqeq : q = m + 1 := by omega
+        subst q
+        rw [canonicalWindowDriftInt_self]
+        apply Int.toNat_le_toNat
+        omega
+
+/-- A positive reflected queue is attained by one suffix's positive drift. -/
+theorem outstandingClaimQueue_eq_zero_or_exists_windowDrift
+    (n : OddNat) (m : ℕ) :
+    canonicalOutstandingClaimQueue n m = 0 ∨
+      (0 < canonicalOutstandingClaimQueue n m ∧
+        ∃ q, q ≤ m ∧ canonicalOutstandingClaimQueue n m =
+          Int.toNat (canonicalWindowDriftInt n q m)) := by
+  induction m with
+  | zero =>
+      by_cases hzero : canonicalOutstandingClaimQueue n 0 = 0
+      · exact Or.inl hzero
+      · exact Or.inr ⟨Nat.pos_of_ne_zero hzero, 0, le_rfl, by
+          rw [canonicalWindowDriftInt_self,
+            canonicalOutstandingClaimQueue_zero_eq_intToNat]⟩
+  | succ m ih =>
+      by_cases hzero : canonicalOutstandingClaimQueue n (m + 1) = 0
+      · exact Or.inl hzero
+      · refine Or.inr ⟨Nat.pos_of_ne_zero hzero, ?_⟩
+        rcases ih with hold | ⟨holdPos, q, hqm, holdWitness⟩
+        · refine ⟨m + 1, le_rfl, ?_⟩
+          rw [canonicalWindowDriftInt_self,
+            canonicalOutstandingClaimQueue_succ_eq_intToNat, hold]
+          simp
+        · refine ⟨q, by omega, ?_⟩
+          rw [canonicalOutstandingClaimQueue_succ_eq_intToNat]
+          rw [canonicalWindowDriftInt_succ n (by omega), if_pos hqm]
+          have hnonneg : 0 ≤ canonicalWindowDriftInt n q m := by
+            by_contra hneg
+            have htoNat : Int.toNat (canonicalWindowDriftInt n q m) = 0 := by
+              exact Int.toNat_of_nonpos (by omega)
+            omega
+          have hcast : (canonicalOutstandingClaimQueue n m : ℤ) =
+              canonicalWindowDriftInt n q m := by
+            rw [holdWitness, Int.ofNat_toNat, max_eq_left hnonneg]
+          rw [hcast]
+
+/-- Maximum positive suffix drift through block `m`, with zero included by `Finset.sup`. -/
+noncomputable def canonicalReflectedWindowMaximum
+    (n : OddNat) (m : ℕ) : ℕ :=
+  (Finset.range (m + 1)).sup fun q =>
+    Int.toNat (canonicalWindowDriftInt n q m)
+
+/-- The causal queue is exactly the maximum positive signed suffix drift. -/
+theorem canonicalOutstandingClaimQueue_eq_reflectedWindowMaximum
+    (n : OddNat) (m : ℕ) :
+    canonicalOutstandingClaimQueue n m = canonicalReflectedWindowMaximum n m := by
+  apply le_antisymm
+  · rcases outstandingClaimQueue_eq_zero_or_exists_windowDrift n m with hzero | hpos
+    · rw [hzero]
+      exact Nat.zero_le _
+    · rcases hpos with ⟨_, q, hqm, hq⟩
+      rw [hq]
+      unfold canonicalReflectedWindowMaximum
+      exact Finset.le_sup (f := fun q => Int.toNat (canonicalWindowDriftInt n q m))
+        (Finset.mem_range.mpr (by omega))
+  · unfold canonicalReflectedWindowMaximum
+    apply Finset.sup_le
+    intro q hq
+    exact intToNat_canonicalWindowDriftInt_le_outstandingClaimQueue n
+      (Nat.le_of_lt_succ (Finset.mem_range.mp hq))
+
+/--
+A pointwise queue ceiling is exactly a ceiling on every signed suffix drift
+ending at the same block.  This is the useful bounded analogue of the
+zero/repayment characterization below.
+-/
+theorem canonicalOutstandingClaimQueue_le_iff_all_windowDrift_le
+    (n : OddNat) (m C : ℕ) :
+    canonicalOutstandingClaimQueue n m ≤ C ↔
+      ∀ q, q ≤ m → canonicalWindowDriftInt n q m ≤ C := by
+  constructor
+  · intro hqueue q hqm
+    have hdrift := intToNat_canonicalWindowDriftInt_le_outstandingClaimQueue n hqm
+    have hself := Int.self_le_toNat (canonicalWindowDriftInt n q m)
+    omega
+  · intro hall
+    rcases outstandingClaimQueue_eq_zero_or_exists_windowDrift n m with
+      hzero | ⟨_, q, hqm, hq⟩
+    · simp [hzero]
+    · rw [hq]
+      have hbound := hall q hqm
+      omega
+
+/-! ## Running-minimum form and repayment characterization -/
+
+/-- Running minimum of zero and all canonical endpoint balances through `m`. -/
+noncomputable def canonicalEndpointRunningBalanceMinimum
+    (n : OddNat) : ℕ → ℤ
+  | 0 => min 0 (canonicalEndpointBalanceInt n 0)
+  | m + 1 => min (canonicalEndpointRunningBalanceMinimum n m)
+      (canonicalEndpointBalanceInt n (m + 1))
+
+/-- The running minimum is below the current endpoint balance. -/
+theorem canonicalEndpointRunningBalanceMinimum_le_balance
+    (n : OddNat) (m : ℕ) :
+    canonicalEndpointRunningBalanceMinimum n m ≤ canonicalEndpointBalanceInt n m := by
+  cases m with
+  | zero => exact min_le_right _ _
+  | succ m =>
+      rw [canonicalEndpointRunningBalanceMinimum]
+      exact min_le_right _ _
+
+/-- The running minimum always includes the initial zero candidate. -/
+theorem canonicalEndpointRunningBalanceMinimum_nonpos
+    (n : OddNat) (m : ℕ) :
+    canonicalEndpointRunningBalanceMinimum n m ≤ 0 := by
+  induction m with
+  | zero => exact min_le_left _ _
+  | succ m ih =>
+      rw [canonicalEndpointRunningBalanceMinimum]
+      exact (min_le_left _ _).trans ih
+
+/-- Exact running-minimum form of the reflected scalar queue. -/
+theorem canonicalOutstandingClaimQueue_eq_balance_sub_runningMinimum
+    (n : OddNat) (m : ℕ) :
+    canonicalOutstandingClaimQueue n m = Int.toNat
+      (canonicalEndpointBalanceInt n m -
+        canonicalEndpointRunningBalanceMinimum n m) := by
+  induction m with
+  | zero =>
+      rw [canonicalOutstandingClaimQueue_zero_eq_intToNat,
+        canonicalEndpointRunningBalanceMinimum]
+      rw [canonicalEndpointBalanceInt]
+      simp only [zero_add, Finset.range_one, Finset.sum_singleton]
+      by_cases hterm : endpointAccountingTerm n 0 ≤ 0
+      · rw [min_eq_right hterm]
+        simp [Int.toNat_of_nonpos hterm]
+      · rw [min_eq_left (by omega)]
+        simp
+  | succ m ih =>
+      rw [canonicalOutstandingClaimQueue_succ_eq_intToNat,
+        canonicalEndpointRunningBalanceMinimum]
+      have hbalance :
+          canonicalEndpointBalanceInt n (m + 1) =
+            canonicalEndpointBalanceInt n m + endpointAccountingTerm n (m + 1) := by
+        unfold canonicalEndpointBalanceInt
+        rw [Finset.sum_range_succ]
+      rw [hbalance]
+      have hminle := canonicalEndpointRunningBalanceMinimum_le_balance n m
+      have hnonneg : 0 ≤ canonicalEndpointBalanceInt n m -
+          canonicalEndpointRunningBalanceMinimum n m := sub_nonneg.mpr hminle
+      have hcast :
+          (Int.toNat (canonicalEndpointBalanceInt n m -
+            canonicalEndpointRunningBalanceMinimum n m) : ℤ) =
+              canonicalEndpointBalanceInt n m -
+                canonicalEndpointRunningBalanceMinimum n m := by
+        rw [Int.ofNat_toNat, max_eq_left hnonneg]
+      rw [ih, hcast]
+      by_cases hnew : canonicalEndpointBalanceInt n m +
+          endpointAccountingTerm n (m + 1) ≤
+            canonicalEndpointRunningBalanceMinimum n m
+      · rw [min_eq_right hnew]
+        have hnonpos : canonicalEndpointBalanceInt n m -
+            canonicalEndpointRunningBalanceMinimum n m +
+              endpointAccountingTerm n (m + 1) ≤ 0 := by
+          linarith
+        rw [Int.toNat_of_nonpos hnonpos]
+        simp
+      · rw [min_eq_left (by omega)]
+        congr 1
+        ring
+
+/-- Queue zero means that every suffix ending at `m` has nonpositive drift. -/
+theorem canonicalOutstandingClaimQueue_eq_zero_iff_all_windowDrift_nonpos
+    (n : OddNat) (m : ℕ) :
+    canonicalOutstandingClaimQueue n m = 0 ↔
+      ∀ q, q ≤ m → canonicalWindowDriftInt n q m ≤ 0 := by
+  constructor
+  · intro hzero q hqm
+    have hle := intToNat_canonicalWindowDriftInt_le_outstandingClaimQueue n hqm
+    rw [hzero] at hle
+    exact (Int.toNat_eq_zero.mp (Nat.eq_zero_of_le_zero hle))
+  · intro hall
+    rcases outstandingClaimQueue_eq_zero_or_exists_windowDrift n m with
+      hzero | ⟨hpos, q, hqm, hq⟩
+    · exact hzero
+    · have hnonpos := hall q hqm
+      have htoNat : Int.toNat (canonicalWindowDriftInt n q m) = 0 :=
+        Int.toNat_of_nonpos hnonpos
+      omega
+
+/-- Queue zero means every aggregate excursion ending at `m` is repaid. -/
+theorem canonicalOutstandingClaimQueue_eq_zero_iff_all_excursions_repaid
+    (n : OddNat) (m : ℕ) :
+    canonicalOutstandingClaimQueue n m = 0 ↔
+      ∀ q, q ≤ m → CanonicalEndpointExcursionRepaidAt n q m := by
+  rw [canonicalOutstandingClaimQueue_eq_zero_iff_all_windowDrift_nonpos]
+  constructor
+  · intro h q hqm
+    exact (canonicalEndpointExcursionRepaidAt_iff_window_sum_nonpos n hqm).2 (h q hqm)
+  · intro h q hqm
+    exact (canonicalEndpointExcursionRepaidAt_iff_window_sum_nonpos n hqm).1 (h q hqm)
+
+/-! ## Window-local causal queue -/
+
+/--
+Outstanding queue generated only by blocks `q..r`, initialized at zero before
+block `q`.  The reflected suffix form is chosen as the public terminal value;
+unlike aggregate drift, it remembers every possible release-time suffix.
+-/
+noncomputable def canonicalLocalOutstandingClaimQueue
+    (n : OddNat) (q r : ℕ) : ℕ :=
+  (Finset.Icc q r).sup fun t => Int.toNat (canonicalWindowDriftInt n t r)
+
+/-- The local causal queue is zero exactly when every release-time suffix is nonpositive. -/
+theorem canonicalLocalOutstandingClaimQueue_eq_zero_iff_all_suffixDrift_nonpos
+    (n : OddNat) (q r : ℕ) :
+    canonicalLocalOutstandingClaimQueue n q r = 0 ↔
+      ∀ t ∈ Finset.Icc q r, canonicalWindowDriftInt n t r ≤ 0 := by
+  constructor
+  · intro hzero t ht
+    have hle : Int.toNat (canonicalWindowDriftInt n t r) ≤
+        canonicalLocalOutstandingClaimQueue n q r := by
+      unfold canonicalLocalOutstandingClaimQueue
+      exact Finset.le_sup (f := fun t => Int.toNat (canonicalWindowDriftInt n t r)) ht
+    rw [hzero] at hle
+    exact Int.toNat_eq_zero.mp (Nat.eq_zero_of_le_zero hle)
+  · intro hall
+    unfold canonicalLocalOutstandingClaimQueue
+    apply Nat.eq_zero_of_le_zero
+    apply Finset.sup_le
+    intro t ht
+    rw [Int.toNat_of_nonpos (hall t ht)]
+
+/-- Suffix drift inequalities are exactly suffix claim-versus-capacity inequalities. -/
+theorem canonicalLocalOutstandingClaimQueue_eq_zero_iff_suffixClaims_le_capacity
+    (n : OddNat) (q r : ℕ) :
+    canonicalLocalOutstandingClaimQueue n q r = 0 ↔
+      ∀ t ∈ Finset.Icc q r,
+        canonicalEndpointWindowClaims n t r ≤ canonicalEndpointWindowCapacity n t r := by
+  rw [canonicalLocalOutstandingClaimQueue_eq_zero_iff_all_suffixDrift_nonpos]
+  constructor
+  · intro h t ht
+    have htr := (Finset.mem_Icc.mp ht).2
+    have hrepaid : CanonicalEndpointExcursionRepaidAt n t r :=
+      (canonicalEndpointExcursionRepaidAt_iff_window_sum_nonpos n htr).2 (by
+        simpa [canonicalWindowDriftInt] using h t ht)
+    exact (canonicalEndpointExcursionRepaidAt_iff_windowClaims_le_capacity n htr).1
+      hrepaid
+  · intro h t ht
+    have htr := (Finset.mem_Icc.mp ht).2
+    have hrepaid : CanonicalEndpointExcursionRepaidAt n t r :=
+      (canonicalEndpointExcursionRepaidAt_iff_windowClaims_le_capacity n htr).2
+        (h t ht)
+    simpa [canonicalWindowDriftInt] using
+      (canonicalEndpointExcursionRepaidAt_iff_window_sum_nonpos n htr).1 hrepaid
+
+/-! ## Temporal matching and suffix Hall conditions -/
+
+/-- A causal forward matching forces every release-time suffix Hall inequality. -/
+theorem CanonicalEndpointForwardWindowMatching.to_suffixClaims_le_capacity
+    {n : OddNat} {q r : ℕ}
+    (h : CanonicalEndpointForwardWindowMatching n q r) :
+    ∀ t ∈ Finset.Icc q r,
+      canonicalEndpointWindowClaims n t r ≤ canonicalEndpointWindowCapacity n t r := by
+  classical
+  rcases h with ⟨hqr, pay, hpayInjective, hpayForward⟩
+  intro t ht
+  have hqt := (Finset.mem_Icc.mp ht).1
+  have htr := (Finset.mem_Icc.mp ht).2
+  let includeClaim : CanonicalEndpointClaimWindowCarrier n t r →
+      CanonicalEndpointClaimWindowCarrier n q r := fun claim =>
+    ⟨⟨claim.1.val, Finset.mem_Icc.mpr
+      ⟨hqt.trans (Finset.mem_Icc.mp claim.1.property).1,
+        (Finset.mem_Icc.mp claim.1.property).2⟩⟩,
+      claim.2⟩
+  have includeClaim_injective : Function.Injective includeClaim := by
+    intro a b hab
+    rcases a with ⟨ak, ai⟩
+    rcases b with ⟨bk, bi⟩
+    apply Sigma.ext_iff.mpr
+    constructor
+    · exact Subtype.ext (congrArg (fun claim => claim.1.val) hab)
+    · exact (Sigma.ext_iff.mp hab).2
+  let suffixPay : CanonicalEndpointClaimWindowCarrier n t r →
+      CanonicalEndpointCapacityWindowCarrier n t r := fun claim =>
+    ⟨⟨(pay (includeClaim claim)).1.val, Finset.mem_Icc.mpr
+      ⟨(Finset.mem_Icc.mp claim.1.property).1.trans
+          (hpayForward (includeClaim claim)),
+        (Finset.mem_Icc.mp (pay (includeClaim claim)).1.property).2⟩⟩,
+      (pay (includeClaim claim)).2⟩
+  have suffixPay_injective : Function.Injective suffixPay := by
+    intro a b hab
+    apply includeClaim_injective
+    apply hpayInjective
+    rcases a with ⟨ak, ai⟩
+    rcases b with ⟨bk, bi⟩
+    apply Sigma.ext_iff.mpr
+    constructor
+    · exact Subtype.ext (congrArg (fun slot => slot.1.val) hab)
+    · exact (Sigma.ext_iff.mp hab).2
+  letI : Finite (CanonicalEndpointCapacityWindowCarrier n t r) := by
+    unfold CanonicalEndpointCapacityWindowCarrier
+    infer_instance
+  have hcard := Nat.card_le_card_of_injective suffixPay suffixPay_injective
+  rw [natCard_canonicalEndpointClaimWindowCarrier,
+    natCard_canonicalEndpointCapacityWindowCarrier] at hcard
+  exact hcard
+
+/-- Nested suffix Hall inequalities construct an anonymous causal forward matching. -/
+theorem canonicalEndpointForwardWindowMatching_of_suffixClaims_le_capacity
+    {n : OddNat} {q r : ℕ} (hqr : q ≤ r)
+    (hall : ∀ t ∈ Finset.Icc q r,
+      canonicalEndpointWindowClaims n t r ≤ canonicalEndpointWindowCapacity n t r) :
+    CanonicalEndpointForwardWindowMatching n q r := by
+  classical
+  let Claim := CanonicalEndpointClaimWindowCarrier n q r
+  let Capacity := CanonicalEndpointCapacityWindowCarrier n q r
+  letI : Finite Claim := by
+    dsimp [Claim]
+    unfold CanonicalEndpointClaimWindowCarrier
+    infer_instance
+  letI : Finite Capacity := by
+    dsimp [Capacity]
+    unfold CanonicalEndpointCapacityWindowCarrier
+    infer_instance
+  letI : Fintype Claim := Fintype.ofFinite Claim
+  letI : Fintype Capacity := Fintype.ofFinite Capacity
+  let eligible : Claim → Capacity → Prop := fun claim slot => claim.1.val ≤ slot.1.val
+  have hallSubsets : ∀ A : Finset Claim,
+      A.card ≤ ({slot : Capacity | ∃ claim ∈ A, eligible claim slot} : Finset Capacity).card := by
+    intro A
+    by_cases hA : A.Nonempty
+    · let blocks : Finset ℕ := A.image fun claim => claim.1.val
+      have hblocks : blocks.Nonempty := hA.image _
+      let t := blocks.min' hblocks
+      have htBlocks : t ∈ blocks := Finset.min'_mem blocks hblocks
+      rcases Finset.mem_image.mp htBlocks with ⟨minClaim, hminClaimA, hminClaimBlock⟩
+      have htIcc : t ∈ Finset.Icc q r := by
+        rw [← hminClaimBlock]
+        exact minClaim.1.property
+      have ht_le_claim : ∀ claim ∈ A, t ≤ claim.1.val := by
+        intro claim hclaim
+        exact Finset.min'_le blocks _ (Finset.mem_image.mpr ⟨claim, hclaim, rfl⟩)
+      let claimsFromT : ↥A → CanonicalEndpointClaimWindowCarrier n t r := fun claim =>
+        ⟨⟨claim.val.1.val, Finset.mem_Icc.mpr
+          ⟨ht_le_claim claim.val claim.property,
+            (Finset.mem_Icc.mp claim.val.1.property).2⟩⟩,
+          claim.val.2⟩
+      have claimsFromT_injective : Function.Injective claimsFromT := by
+        intro a b hab
+        apply Subtype.ext
+        rcases a with ⟨a, ha⟩
+        rcases b with ⟨b, hb⟩
+        apply Sigma.ext_iff.mpr
+        constructor
+        · exact Subtype.ext (congrArg (fun claim => claim.1.val) hab)
+        · exact (Sigma.ext_iff.mp hab).2
+      have hAClaims : A.card ≤ canonicalEndpointWindowClaims n t r := by
+        letI : Finite (CanonicalEndpointClaimWindowCarrier n t r) := by
+          unfold CanonicalEndpointClaimWindowCarrier
+          infer_instance
+        letI : Fintype (CanonicalEndpointClaimWindowCarrier n t r) :=
+          Fintype.ofFinite _
+        have hcard := Fintype.card_le_of_injective claimsFromT claimsFromT_injective
+        rw [← natCard_canonicalEndpointClaimWindowCarrier n t r]
+        simpa only [Fintype.card_coe, Nat.card_eq_fintype_card] using hcard
+      let capacityToEligible : CanonicalEndpointCapacityWindowCarrier n t r →
+          {slot : Capacity // ∃ claim ∈ A, eligible claim slot} := fun slot =>
+        ⟨⟨⟨slot.1.val, Finset.mem_Icc.mpr
+            ⟨(Finset.mem_Icc.mp htIcc).1.trans
+                (Finset.mem_Icc.mp slot.1.property).1,
+              (Finset.mem_Icc.mp slot.1.property).2⟩⟩,
+            slot.2⟩,
+          ⟨minClaim, hminClaimA, by
+            change minClaim.1.val ≤ slot.1.val
+            rw [hminClaimBlock]
+            exact (Finset.mem_Icc.mp slot.1.property).1⟩⟩
+      have capacityToEligible_injective : Function.Injective capacityToEligible := by
+        intro a b hab
+        rcases a with ⟨ak, ai⟩
+        rcases b with ⟨bk, bi⟩
+        apply Sigma.ext_iff.mpr
+        constructor
+        · exact Subtype.ext (congrArg (fun slot => slot.val.1.val) hab)
+        · have hsigma :
+              (capacityToEligible ⟨ak, ai⟩).val =
+                (capacityToEligible ⟨bk, bi⟩).val := congrArg Subtype.val hab
+          exact (Sigma.ext_iff.mp hsigma).2
+      have hCapacityEligible : canonicalEndpointWindowCapacity n t r ≤
+          ({slot : Capacity | ∃ claim ∈ A, eligible claim slot} : Finset Capacity).card := by
+        letI : Finite (CanonicalEndpointCapacityWindowCarrier n t r) := by
+          unfold CanonicalEndpointCapacityWindowCarrier
+          infer_instance
+        letI : Fintype (CanonicalEndpointCapacityWindowCarrier n t r) :=
+          Fintype.ofFinite _
+        have hcard := Fintype.card_le_of_injective capacityToEligible
+          capacityToEligible_injective
+        rw [← natCard_canonicalEndpointCapacityWindowCarrier n t r]
+        rw [Nat.card_eq_fintype_card]
+        rw [Fintype.card_subtype] at hcard
+        exact hcard
+      exact hAClaims.trans ((hall t htIcc).trans hCapacityEligible)
+    · rw [Finset.not_nonempty_iff_eq_empty.mp hA]
+      simp
+  have hmatching :=
+    (Fintype.all_card_le_filter_rel_iff_exists_injective eligible).1 hallSubsets
+  rcases hmatching with ⟨pay, hpay, heligible⟩
+  exact ⟨hqr, pay, hpay, heligible⟩
+
+/-- Anonymous temporal Hall theorem for canonical block windows. -/
+theorem canonicalEndpointForwardWindowMatching_iff_suffixClaims_le_capacity
+    (n : OddNat) {q r : ℕ} (hqr : q ≤ r) :
+    CanonicalEndpointForwardWindowMatching n q r ↔
+      ∀ t ∈ Finset.Icc q r,
+        canonicalEndpointWindowClaims n t r ≤ canonicalEndpointWindowCapacity n t r := by
+  constructor
+  · exact CanonicalEndpointForwardWindowMatching.to_suffixClaims_le_capacity
+  · exact canonicalEndpointForwardWindowMatching_of_suffixClaims_le_capacity hqr
+
+/-- Local causal queue zero is exactly anonymous forward matchability. -/
+theorem canonicalLocalOutstandingClaimQueue_eq_zero_iff_forwardWindowMatching
+    (n : OddNat) {q r : ℕ} (hqr : q ≤ r) :
+    canonicalLocalOutstandingClaimQueue n q r = 0 ↔
+      CanonicalEndpointForwardWindowMatching n q r := by
+  rw [canonicalEndpointForwardWindowMatching_iff_suffixClaims_le_capacity n hqr]
+  exact canonicalLocalOutstandingClaimQueue_eq_zero_iff_suffixClaims_le_capacity n q r
+
+/-! ## Exact scalar regressions -/
+
+/-- The first seven block leaves one anonymous unit claim outstanding. -/
+theorem canonicalOutstandingClaimQueue_seven_zero :
+    canonicalOutstandingClaimQueue sevenDepthRegressionRoot 0 = 1 := by
+  rw [canonicalOutstandingClaimQueue_zero_eq_intToNat,
+    endpointAccountingTerm_sevenDepthRegressionRoot_zero]
+  decide
+
+/-- The second seven block repays the first scalar queue completely. -/
+theorem canonicalOutstandingClaimQueue_seven_one :
+    canonicalOutstandingClaimQueue sevenDepthRegressionRoot 1 = 0 := by
+  rw [canonicalOutstandingClaimQueue_succ_eq_intToNat,
+    canonicalOutstandingClaimQueue_seven_zero,
+    endpointAccountingTerm_sevenDepthRegressionRoot_one]
+  decide
+
+/-- The first two seven blocks admit an actual anonymous causal forward matching. -/
+theorem canonicalEndpointForwardWindowMatching_seven_zero_one :
+    CanonicalEndpointForwardWindowMatching sevenDepthRegressionRoot 0 1 := by
+  apply canonicalEndpointForwardWindowMatching_of_suffixClaims_le_capacity (by omega)
+  intro t ht
+  rcases Finset.mem_Icc.mp ht with ⟨ht0, ht1⟩
+  interval_cases t
+  · exact (canonicalEndpointExcursionRepaidAt_iff_windowClaims_le_capacity
+      sevenDepthRegressionRoot (by omega)).1 (by
+        apply (canonicalEndpointExcursionRepaidAt_iff_window_sum_nonpos
+          sevenDepthRegressionRoot (by omega)).2
+        rw [show (∑ k ∈ Finset.Icc 0 1,
+            endpointAccountingTerm sevenDepthRegressionRoot k) =
+              endpointAccountingTerm sevenDepthRegressionRoot 0 +
+                endpointAccountingTerm sevenDepthRegressionRoot 1 by
+          rw [show Finset.Icc 0 1 = {0, 1} by decide]
+          simp]
+        rw [endpointAccountingTerm_sevenDepthRegressionRoot_zero,
+          endpointAccountingTerm_sevenDepthRegressionRoot_one]
+        norm_num)
+  · exact (canonicalEndpointExcursionRepaidAt_iff_windowClaims_le_capacity
+      sevenDepthRegressionRoot (by omega)).1 (by
+        apply (canonicalEndpointExcursionRepaidAt_iff_window_sum_nonpos
+          sevenDepthRegressionRoot (by omega)).2
+        rw [show (∑ k ∈ Finset.Icc 1 1,
+            endpointAccountingTerm sevenDepthRegressionRoot k) =
+              endpointAccountingTerm sevenDepthRegressionRoot 1 by norm_num]
+        rw [endpointAccountingTerm_sevenDepthRegressionRoot_one]
+        norm_num)
+
+/-! ### The scalar repayment regression from 511 -/
+
+/-- Public root used by the exact scalar-queue regression from 511. -/
+def scalarQueue511Root : OddNat := mkOddNat 511 (by decide)
+
+private lemma scalarQueue511_v2_1534 : v2 1534 = 1 := by
+  rw [show 1534 = 2 * 767 by norm_num, v2_two_mul 767 (by norm_num)]
+  rw [v2_odd 767 (by decide)]
+
+private lemma scalarQueue511_v2_2302 : v2 2302 = 1 := by
+  rw [show 2302 = 2 * 1151 by norm_num, v2_two_mul 1151 (by norm_num)]
+  rw [v2_odd 1151 (by decide)]
+
+private lemma scalarQueue511_v2_3454 : v2 3454 = 1 := by
+  rw [show 3454 = 2 * 1727 by norm_num, v2_two_mul 1727 (by norm_num)]
+  rw [v2_odd 1727 (by decide)]
+
+private lemma scalarQueue511_v2_5182 : v2 5182 = 1 := by
+  rw [show 5182 = 2 * 2591 by norm_num, v2_two_mul 2591 (by norm_num)]
+  rw [v2_odd 2591 (by decide)]
+
+private lemma scalarQueue511_v2_7774 : v2 7774 = 1 := by
+  rw [show 7774 = 2 * 3887 by norm_num, v2_two_mul 3887 (by norm_num)]
+  rw [v2_odd 3887 (by decide)]
+
+private lemma scalarQueue511_v2_11662 : v2 11662 = 1 := by
+  rw [show 11662 = 2 * 5831 by norm_num, v2_two_mul 5831 (by norm_num)]
+  rw [v2_odd 5831 (by decide)]
+
+private lemma scalarQueue511_v2_17494 : v2 17494 = 1 := by
+  rw [show 17494 = 2 * 8747 by norm_num, v2_two_mul 8747 (by norm_num)]
+  rw [v2_odd 8747 (by decide)]
+
+private lemma scalarQueue511_v2_26242 : v2 26242 = 1 := by
+  rw [show 26242 = 2 * 13121 by norm_num, v2_two_mul 13121 (by norm_num)]
+  rw [v2_odd 13121 (by decide)]
+
+private lemma scalarQueue511_v2_39364 : v2 39364 = 2 := by
+  rw [show 39364 = 2 * (2 * 9841) by norm_num]
+  rw [v2_two_mul (2 * 9841) (by norm_num), v2_two_mul 9841 (by norm_num)]
+  rw [v2_odd 9841 (by decide)]
+
+private lemma scalarQueue511_v2_29524 : v2 29524 = 2 := by
+  rw [show 29524 = 2 * (2 * 7381) by norm_num]
+  rw [v2_two_mul (2 * 7381) (by norm_num), v2_two_mul 7381 (by norm_num)]
+  rw [v2_odd 7381 (by decide)]
+
+private lemma scalarQueue511_v2_22144 : v2 22144 = 7 := by
+  rw [show 22144 = 2 * (2 * (2 * (2 * (2 * (2 * (2 * 173)))))) by norm_num]
+  repeat' rw [v2_two_mul _ (by norm_num)]
+  rw [v2_odd 173 (by decide)]
+
+private lemma scalarQueue511_v2_512 : v2 512 = 9 := by
+  simpa [pow2] using v2_pow2 9
+
+private lemma scalarQueue511_v2_9842 : v2 9842 = 1 := by
+  rw [show 9842 = 2 * 4921 by norm_num, v2_two_mul 4921 (by norm_num)]
+  rw [v2_odd 4921 (by decide)]
+
+private lemma scalarQueue511_v2_7382 : v2 7382 = 1 := by
+  rw [show 7382 = 2 * 3691 by norm_num, v2_two_mul 3691 (by norm_num)]
+  rw [v2_odd 3691 (by decide)]
+
+private theorem scalarQueue511_endpoint_zero :
+    paymentEndpointSeq scalarQueue511Root 0 = 8 := by
+  norm_num [paymentEndpointSeq, orbitPaymentTarget, orbitExactDepth,
+    ResidualAllOnesDepth, oddOrbitLabel, iterateT, scalarQueue511Root, mkOddNat,
+    scalarQueue511_v2_512]
+
+private theorem scalarQueue511_endpoint_one :
+    paymentEndpointSeq scalarQueue511Root 1 = 9 := by
+  rw [show paymentEndpointSeq scalarQueue511Root 1 =
+    orbitPaymentTarget scalarQueue511Root
+      (paymentEndpointSeq scalarQueue511Root 0 + 1) by rfl]
+  rw [scalarQueue511_endpoint_zero]
+  norm_num [orbitPaymentTarget, orbitExactDepth, ResidualAllOnesDepth,
+    oddOrbitLabel, iterateT, T, scalarQueue511Root, mkOddNat, threeNPlusOne, pow2,
+    scalarQueue511_v2_1534, scalarQueue511_v2_2302,
+    scalarQueue511_v2_3454, scalarQueue511_v2_5182,
+    scalarQueue511_v2_7774, scalarQueue511_v2_11662,
+    scalarQueue511_v2_17494, scalarQueue511_v2_26242,
+    scalarQueue511_v2_39364, scalarQueue511_v2_9842]
+
+private theorem scalarQueue511_endpoint_two :
+    paymentEndpointSeq scalarQueue511Root 2 = 10 := by
+  rw [show paymentEndpointSeq scalarQueue511Root 2 =
+    orbitPaymentTarget scalarQueue511Root
+      (paymentEndpointSeq scalarQueue511Root 1 + 1) by rfl]
+  rw [scalarQueue511_endpoint_one]
+  norm_num [orbitPaymentTarget, orbitExactDepth, ResidualAllOnesDepth,
+    oddOrbitLabel, iterateT, T, scalarQueue511Root, mkOddNat, threeNPlusOne, pow2,
+    scalarQueue511_v2_1534, scalarQueue511_v2_2302,
+    scalarQueue511_v2_3454, scalarQueue511_v2_5182,
+    scalarQueue511_v2_7774, scalarQueue511_v2_11662,
+    scalarQueue511_v2_17494, scalarQueue511_v2_26242,
+    scalarQueue511_v2_39364, scalarQueue511_v2_29524,
+    scalarQueue511_v2_7382]
+
+private theorem endpointAccountingTerm_scalarQueue511_zero :
+    endpointAccountingTerm scalarQueue511Root 0 = 5 := by
+  rw [endpointAccountingTerm_eq_universalPaymentBlockSignedDriftAt]
+  rw [universalPaymentBlockSignedDriftAt_eq_bitWidth_sub scalarQueue511Root
+    (paymentEndpointSeq scalarQueue511Root 0)
+    (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq scalarQueue511Root 0)]
+  rw [universalPaymentBlockStart_paymentEndpointSeq_zero,
+    scalarQueue511_endpoint_zero]
+  norm_num [iterateT, T, scalarQueue511Root, mkOddNat, threeNPlusOne, pow2,
+    scalarQueue511_v2_1534, scalarQueue511_v2_2302,
+    scalarQueue511_v2_3454, scalarQueue511_v2_5182,
+    scalarQueue511_v2_7774, scalarQueue511_v2_11662,
+    scalarQueue511_v2_17494, scalarQueue511_v2_26242,
+    scalarQueue511_v2_39364, bitWidth]
+
+private theorem endpointAccountingTerm_scalarQueue511_one :
+    endpointAccountingTerm scalarQueue511Root 1 = -1 := by
+  rw [endpointAccountingTerm_eq_universalPaymentBlockSignedDriftAt]
+  rw [universalPaymentBlockSignedDriftAt_eq_bitWidth_sub scalarQueue511Root
+    (paymentEndpointSeq scalarQueue511Root 1)
+    (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq scalarQueue511Root 1)]
+  rw [universalPaymentBlockStart_paymentEndpointSeq_succ,
+    scalarQueue511_endpoint_zero, scalarQueue511_endpoint_one]
+  norm_num [iterateT, T, scalarQueue511Root, mkOddNat, threeNPlusOne, pow2,
+    scalarQueue511_v2_1534, scalarQueue511_v2_2302,
+    scalarQueue511_v2_3454, scalarQueue511_v2_5182,
+    scalarQueue511_v2_7774, scalarQueue511_v2_11662,
+    scalarQueue511_v2_17494, scalarQueue511_v2_26242,
+    scalarQueue511_v2_39364, scalarQueue511_v2_29524, bitWidth]
+
+private theorem endpointAccountingTerm_scalarQueue511_two :
+    endpointAccountingTerm scalarQueue511Root 2 = -5 := by
+  rw [endpointAccountingTerm_eq_universalPaymentBlockSignedDriftAt]
+  rw [universalPaymentBlockSignedDriftAt_eq_bitWidth_sub scalarQueue511Root
+    (paymentEndpointSeq scalarQueue511Root 2)
+    (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq scalarQueue511Root 2)]
+  rw [universalPaymentBlockStart_paymentEndpointSeq_succ,
+    scalarQueue511_endpoint_one, scalarQueue511_endpoint_two]
+  norm_num [iterateT, T, scalarQueue511Root, mkOddNat, threeNPlusOne, pow2,
+    scalarQueue511_v2_1534, scalarQueue511_v2_2302,
+    scalarQueue511_v2_3454, scalarQueue511_v2_5182,
+    scalarQueue511_v2_7774, scalarQueue511_v2_11662,
+    scalarQueue511_v2_17494, scalarQueue511_v2_26242,
+    scalarQueue511_v2_39364, scalarQueue511_v2_29524,
+    scalarQueue511_v2_22144, bitWidth]
+
+/-- The first 511 block leaves five anonymous claims outstanding. -/
+theorem canonicalOutstandingClaimQueue_511_zero :
+    canonicalOutstandingClaimQueue scalarQueue511Root 0 = 5 := by
+  rw [canonicalOutstandingClaimQueue_zero_eq_intToNat,
+    endpointAccountingTerm_scalarQueue511_zero]
+  decide
+
+/-- The second 511 block repays one of the five anonymous claims. -/
+theorem canonicalOutstandingClaimQueue_511_one :
+    canonicalOutstandingClaimQueue scalarQueue511Root 1 = 4 := by
+  rw [canonicalOutstandingClaimQueue_succ_eq_intToNat,
+    canonicalOutstandingClaimQueue_511_zero,
+    endpointAccountingTerm_scalarQueue511_one]
+  decide
+
+/-- The third 511 block repays the remaining scalar debt completely. -/
+theorem canonicalOutstandingClaimQueue_511_two :
+    canonicalOutstandingClaimQueue scalarQueue511Root 2 = 0 := by
+  rw [canonicalOutstandingClaimQueue_succ_eq_intToNat,
+    canonicalOutstandingClaimQueue_511_one,
+    endpointAccountingTerm_scalarQueue511_two]
+  decide
+
+/-! ## Queue to endpoint balance -/
+
+/-- The signed endpoint balance never exceeds the nonnegative outstanding queue. -/
+theorem canonicalEndpointBalanceInt_le_outstandingClaimQueue
+    (n : OddNat) (m : ℕ) :
+    canonicalEndpointBalanceInt n m ≤ canonicalOutstandingClaimQueue n m := by
+  induction m with
+  | zero =>
+      rw [canonicalEndpointBalanceInt, canonicalOutstandingClaimQueue]
+      simp only [zero_add, Finset.range_one, Finset.sum_singleton]
+      rw [endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount]
+      omega
+  | succ m ih =>
+      rw [canonicalEndpointBalanceInt]
+      rw [Finset.sum_range_succ, canonicalOutstandingClaimQueue_succ]
+      rw [endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount]
+      rw [canonicalEndpointBalanceInt] at ih
+      omega
+
+/-- Uniform boundedness of the anonymous scalar queue. -/
+def CanonicalOutstandingClaimQueueUniformUpperBound
+    (n : OddNat) (C : ℕ) : Prop :=
+  ∀ m, canonicalOutstandingClaimQueue n m ≤ C
+
+/--
+Uniform queue boundedness is precisely uniform control of every finite suffix
+drift.  Reflection and Hall theory therefore reduce the remaining global
+problem to this scalar signed-window estimate; they do not prove the estimate.
+-/
+theorem canonicalOutstandingClaimQueueUniformUpperBound_iff_all_windowDrift_le
+    (n : OddNat) (C : ℕ) :
+    CanonicalOutstandingClaimQueueUniformUpperBound n C ↔
+      ∀ m q, q ≤ m → canonicalWindowDriftInt n q m ≤ C := by
+  constructor
+  · intro h m
+    exact (canonicalOutstandingClaimQueue_le_iff_all_windowDrift_le n m C).1 (h m)
+  · intro h m
+    exact (canonicalOutstandingClaimQueue_le_iff_all_windowDrift_le n m C).2 (h m)
+
+/-- A scalar queue ceiling supplies the existing canonical endpoint balance ceiling. -/
+theorem CanonicalOutstandingClaimQueueUniformUpperBound.to_balanceUniformUpperBound
+    {n : OddNat} {C : ℕ}
+    (h : CanonicalOutstandingClaimQueueUniformUpperBound n C) :
+    CanonicalEndpointBalanceUniformUpperBound n C := by
+  intro m
+  exact (canonicalEndpointBalanceInt_le_outstandingClaimQueue n m).trans
+    (Int.ofNat_le.mpr (h m))
+
+/-- A scalar queue ceiling yields the corresponding canonical endpoint bit-width ceiling. -/
+theorem bitWidth_paymentEndpointSeq_le_of_outstandingClaimQueueUniformUpperBound
+    {n : OddNat} {C : ℕ}
+    (h : CanonicalOutstandingClaimQueueUniformUpperBound n C) (m : ℕ) :
+    bitWidth (iterateT (paymentEndpointSeq n m + 1) n).1 ≤ bitWidth n.1 + C :=
+  bitWidth_paymentEndpointSeq_le_of_balanceUniformUpperBound
+    h.to_balanceUniformUpperBound m
+
+/-!
+## Structural frontier after the scalar audit
+
+The cp-316 executable audit inspected every odd root through `16383`.  In that
+finite sample, all `8192` roots reached a canonical endpoint whose state is one
+with queue zero.  The largest observed queue was eight and the longest observed
+positive excursion lasted twenty canonical blocks.  These are regression data,
+not universal constants.
+
+The exact reflection theorem above explains the remaining obstruction.  A
+uniform queue bound is equivalent to a uniform upper bound on every positive
+suffix of `endpointAccountingTerm`.  Existing block length, claim-depth
+histogram, endpoint height, pressure-contribution, and PatternLedger data
+describe individual transitions, but no current theorem prevents an
+arbitrarily long sequence of blocks from accumulating positive suffix drift.
+Likewise, the temporal Hall theorem characterizes zero queue; it does not bound
+a nonzero queue.
+
+Consequently the next mathematical input must be one of the following, rather
+than another depth-to-level eligibility rule:
+
+* a uniform signed-suffix estimate;
+* a uniform repayment-lag theorem;
+* exclusion of a pumpable positive-queue transition cycle; or
+* a finite-state obstruction that forces discharge.
+
+Until one of those statements is proved, promoting the observed constants
+`8` or `20` to a theorem would be unjustified.
+-/
+
+end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-316.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-316.md
new file mode 100644
index 00000000..6d029f95
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-316.md
@@ -0,0 +1,265 @@
+# Petal / Collatz implementation report: cp-316
+
+## Result
+
+Checkpoint cp-316 replaces the refuted depth-to-level repayment candidate with
+the anonymous scalar repayment queue justified by the exact endpoint ledger.
+The requested algebraic, queue-reflection, repayment, temporal Hall, matching,
+and queue-to-bit-width surfaces are proved in Lean without `sorry`.
+
+The checkpoint also reaches the requested genuine obstruction.  Uniform queue
+boundedness is now proved equivalent to a uniform bound on every signed suffix
+of the endpoint-accounting walk.  Existing local block data does not yet supply
+that global suffix estimate.  Therefore this checkpoint does not promote the
+finite observed queue ceiling to a theorem.
+
+The new main module is:
+
+```text
+DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentScalarQueue
+```
+
+It is exported by `DkMath.Collatz.PetalBridge.FloatWindow`.
+
+## Anonymous scalar ledger
+
+The implementation freezes the semantic distinction identified at cp-315:
+
+```text
+recovery depth           = intrinsic address within a canonical block
+endpoint capacity level  = coordinate on anonymous unit-capacity slots
+```
+
+Neither coordinate carries a proved exchange value.  The scalar layer therefore
+counts only unit claims and fungible unit service:
+
+```text
+canonicalBlockClaimCount
+canonicalBlockCapacityCount
+```
+
+Lean proves exactly:
+
+```text
+endpointAccountingTerm n k
+  = canonicalBlockClaimCount n k - canonicalBlockCapacityCount n k
+```
+
+where the subtraction on the right is interpreted in `Int`.
+
+## Reflected causal queue
+
+`canonicalOutstandingClaimQueue` implements a work-conserving reflected queue.
+New claims are added, current endpoint capacity is consumed, and unused capacity
+is discarded rather than banked.
+
+Lean proves two exact reflection forms.
+
+First, the queue is the largest nonnegative signed suffix drift ending at block
+`m`:
+
+```text
+queue n m
+  = max (Int.toNat (canonicalWindowDriftInt n q m)), q <= m
+```
+
+The implementation is exposed by:
+
+```text
+canonicalOutstandingClaimQueue_eq_reflectedWindowMaximum
+```
+
+Second, it is the current endpoint balance reflected above the running minimum:
+
+```text
+queue n m
+  = Int.toNat
+      (balance n m - runningMinimum n m)
+```
+
+This is proved by
+`canonicalOutstandingClaimQueue_eq_balance_sub_runningMinimum`.
+
+These are theorem-level identities, not numerical observations.
+
+## Repayment characterization
+
+Lean proves:
+
+```text
+queue n m = 0
+  <-> every suffix q..m has nonpositive signed drift
+  <-> every aggregate excursion ending at m is repaid
+```
+
+The corresponding public theorems are:
+
+```text
+canonicalOutstandingClaimQueue_eq_zero_iff_all_windowDrift_nonpos
+canonicalOutstandingClaimQueue_eq_zero_iff_all_excursions_repaid
+```
+
+This distinguishes aggregate repayment from causal repayment.  One total
+window inequality is not enough for causal service when claims have release
+blocks.
+
+## Temporal Hall theorem
+
+For `q <= r`, Lean now proves the finite interval-order Hall theorem:
+
+```text
+CanonicalEndpointForwardWindowMatching n q r
+  <-> forall t in q..r,
+        claims n t r <= capacity n t r
+```
+
+The forward direction restricts an existing injection to each suffix.  The
+reverse direction applies finite Hall to the anonymous claim and capacity
+carriers; for an arbitrary nonempty claim subset, its minimum release block
+reduces the Hall neighborhood bound to one nested suffix inequality.
+
+No depth or capacity-level coordinate occurs in this theorem.
+
+The local reflected queue is then proved equivalent to actual causal matching:
+
+```text
+canonicalLocalOutstandingClaimQueue n q r = 0
+  <-> CanonicalEndpointForwardWindowMatching n q r
+```
+
+Thus the following three descriptions are now interchangeable:
+
+```text
+all suffix inequalities
+local queue zero
+anonymous forward matching
+```
+
+## Exact regressions
+
+The existing explicit seven allocation is now packaged as the actual theorem:
+
+```text
+CanonicalEndpointForwardWindowMatching sevenDepthRegressionRoot 0 1
+```
+
+Lean also proves the scalar queue values:
+
+```text
+root 7:    queue 0 = 1, queue 1 = 0
+root 511:  queue 0 = 5, queue 1 = 4, queue 2 = 0
+```
+
+For root 511 the proof first establishes the exact endpoint drifts
+`+5, -1, -5` from accelerated states and bit widths, then derives the reflected
+queue.  This is the intended contrast with cp-315: the exact-level candidate
+leaves depth-eight and depth-nine claims, while the justified anonymous scalar
+ledger is fully repaid after three blocks.
+
+## Queue to Big
+
+Lean proves that endpoint balance never exceeds the nonnegative reflected queue:
+
+```text
+canonicalEndpointBalanceInt n m
+  <= canonicalOutstandingClaimQueue n m
+```
+
+Consequently:
+
+```text
+uniform scalar queue bound
+  -> CanonicalEndpointBalanceUniformUpperBound
+  -> canonical endpoint bit-width bound
+```
+
+This is the first direct scalar queue-to-Big bridge.  It remains conditional on
+proving a uniform queue ceiling.
+
+## Finite scalar audit
+
+The new executable audit is:
+
+```text
+python/Collatz/PetalBridge/canonical_scalar_queue_audit.py
+```
+
+It audits all `8192` odd roots in `1..16383`, independently of the rejected
+level queues, and records block-local features at the first maximum queue.
+
+Finite observations:
+
+```text
+roots audited                            8192
+roots reaching a state-one endpoint     8192
+nonzero queue at that endpoint              0
+largest observed scalar queue               8
+longest observed positive excursion        20 blocks
+```
+
+The 511 assertions are embedded in the script as executable regressions.  The
+largest observed queue occurs for several roots, including `4255`, `4591`, and
+`5673`.  The longest positive excursion occurs at root `7527`.
+
+Generated evidence:
+
+```text
+python/Collatz/PetalBridge/results/canonical_scalar_queue_audit_316.csv
+python/Collatz/PetalBridge/results/canonical_scalar_queue_audit_316.md
+```
+
+These statements concern only the audited finite set.  They do not prove that
+all roots reach state one, that queue eight is a universal ceiling, or that
+twenty blocks is a universal repayment lag.
+
+## Exact structural frontier
+
+The additional cp-316 theorem makes the remaining target precise:
+
+```text
+canonicalOutstandingClaimQueue n m <= C
+  <-> forall q <= m, canonicalWindowDriftInt n q m <= C
+```
+
+and uniformly:
+
+```text
+CanonicalOutstandingClaimQueueUniformUpperBound n C
+  <-> forall m q, q <= m -> canonicalWindowDriftInt n q m <= C
+```
+
+This is the safe stopping point.  Reflection and temporal Hall completely
+explain the queue, but neither bounds a positive queue.  The existing canonical
+block length, claim-depth histogram, endpoint height, block-pressure, and
+PatternLedger surfaces describe individual transitions; no current theorem
+prevents arbitrarily long accumulation of positive suffix drift.
+
+The next mathematical input must therefore establish at least one of:
+
+```text
+uniform signed-suffix control
+uniform repayment lag
+absence of a pumpable positive-queue cycle
+finite-state obstruction forcing discharge
+```
+
+Returning to exact depth-to-level matching would not address this obstruction
+without a new theorem assigning payment semantics to those coordinates.
+
+## Verification
+
+Completed during implementation:
+
+```text
+lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentScalarQueue
+lake build DkMath.Collatz.PetalBridge.FloatWindow
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath
+python3 python/Collatz/PetalBridge/canonical_scalar_queue_audit.py
+python3 -m py_compile python/Collatz/PetalBridge/canonical_scalar_queue_audit.py
+git diff --check
+```
+
+All build gates passed.  The cp-316 Lean module contains no `sorry`.  Existing
+unrelated project warnings remain outside this checkpoint.
+
diff --git a/python/Collatz/PetalBridge/canonical_scalar_queue_audit.py b/python/Collatz/PetalBridge/canonical_scalar_queue_audit.py
new file mode 100644
index 00000000..48d0e560
--- /dev/null
+++ b/python/Collatz/PetalBridge/canonical_scalar_queue_audit.py
@@ -0,0 +1,241 @@
+#!/usr/bin/env python3
+"""Finite audit of the anonymous canonical scalar repayment queue.
+
+This mirrors UniversalPaymentScalarQueue.lean.  Every carry-two source is one
+claim, every endpoint contributes ``height - 1`` fungible service slots, and
+unused service is discarded.  No recovery-depth/capacity-level eligibility is
+used.
+
+The generated data is finite evidence.  In particular, it does not prove a
+uniform queue bound, a uniform repayment lag, or convergence of any orbit.
+"""
+
+from __future__ import annotations
+
+import csv
+from collections import Counter
+from dataclasses import asdict, dataclass
+from pathlib import Path
+
+
+ROOT_MAX = 16383
+BLOCK_LIMIT = 4096
+
+
+def v2(value: int) -> int:
+    assert value > 0
+    return (value & -value).bit_length() - 1
+
+
+def accelerated_step(value: int) -> int:
+    raw = 3 * value + 1
+    return raw >> v2(raw)
+
+
+def upper_carry(value: int) -> int:
+    return (3 * value + 1) >> value.bit_length()
+
+
+class Orbit:
+    def __init__(self, root: int) -> None:
+        assert root > 0 and root % 2 == 1
+        self.states = [root]
+
+    def state(self, time: int) -> int:
+        while len(self.states) <= time:
+            self.states.append(accelerated_step(self.states[-1]))
+        return self.states[time]
+
+    def exact_depth(self, time: int) -> int:
+        return v2(self.state(time) + 1)
+
+    def height(self, time: int) -> int:
+        return v2(3 * self.state(time) + 1)
+
+    def target(self, time: int) -> int:
+        return time + self.exact_depth(time) - 1
+
+
+@dataclass
+class AuditRow:
+    root: int
+    blocks_audited: int
+    reached_state_one_endpoint: bool
+    state_one_endpoint_block: int
+    queue_at_state_one_endpoint: int
+    maximum_queue: int
+    first_return_to_zero_after_positive: int
+    longest_positive_excursion: int
+    final_queue: int
+    max_queue_block: int
+    max_queue_block_length: int
+    max_queue_block_claims: int
+    max_queue_block_capacity: int
+    max_queue_block_drift: int
+    max_queue_endpoint_height: int
+    max_queue_claim_depth_histogram: str
+
+
+def depth_histogram(depths: list[int]) -> str:
+    counts = Counter(depths)
+    return ";".join(f"d{depth}:{counts[depth]}" for depth in sorted(counts)) or "none"
+
+
+def audit_root(root: int) -> AuditRow:
+    orbit = Orbit(root)
+    endpoint = orbit.target(0)
+    previous_endpoint = -1
+    queue = 0
+    maximum_queue = 0
+    first_return = -1
+    positive_run = 0
+    longest_positive = 0
+    has_been_positive = False
+    state_one_block = -1
+    queue_at_state_one = -1
+    max_features = (-1, 0, 0, 0, 0, 0, "none")
+
+    blocks_audited = 0
+    for block in range(BLOCK_LIMIT):
+        start = previous_endpoint + 1
+        depths = [
+            endpoint - time + 1
+            for time in range(start, endpoint + 1)
+            if upper_carry(orbit.state(time)) == 2
+        ]
+        claims = len(depths)
+        height = orbit.height(endpoint)
+        capacity = height - 1
+        drift = claims - capacity
+        queue = max(0, queue + drift)
+        blocks_audited = block + 1
+
+        if queue > 0:
+            has_been_positive = True
+            positive_run += 1
+            longest_positive = max(longest_positive, positive_run)
+        else:
+            if has_been_positive and first_return < 0:
+                first_return = block
+            positive_run = 0
+
+        if queue > maximum_queue:
+            maximum_queue = queue
+            max_features = (
+                block,
+                endpoint - start + 1,
+                claims,
+                capacity,
+                drift,
+                height,
+                depth_histogram(depths),
+            )
+
+        if orbit.state(endpoint) == 1 and state_one_block < 0:
+            state_one_block = block
+            queue_at_state_one = queue
+            break
+
+        previous_endpoint = endpoint
+        endpoint = orbit.target(endpoint + 1)
+
+    return AuditRow(
+        root=root,
+        blocks_audited=blocks_audited,
+        reached_state_one_endpoint=state_one_block >= 0,
+        state_one_endpoint_block=state_one_block,
+        queue_at_state_one_endpoint=queue_at_state_one,
+        maximum_queue=maximum_queue,
+        first_return_to_zero_after_positive=first_return,
+        longest_positive_excursion=longest_positive,
+        final_queue=queue,
+        max_queue_block=max_features[0],
+        max_queue_block_length=max_features[1],
+        max_queue_block_claims=max_features[2],
+        max_queue_block_capacity=max_features[3],
+        max_queue_block_drift=max_features[4],
+        max_queue_endpoint_height=max_features[5],
+        max_queue_claim_depth_histogram=max_features[6],
+    )
+
+
+def main() -> None:
+    rows = [audit_root(root) for root in range(1, ROOT_MAX + 1, 2)]
+
+    # Exact scalar regressions mirrored by Lean.
+    by_root = {row.root: row for row in rows}
+    assert by_root[7].maximum_queue == 1
+    assert by_root[511].maximum_queue == 5
+    assert by_root[511].first_return_to_zero_after_positive == 2
+
+    output_dir = Path(__file__).with_name("results")
+    output_dir.mkdir(parents=True, exist_ok=True)
+    csv_path = output_dir / "canonical_scalar_queue_audit_316.csv"
+    md_path = output_dir / "canonical_scalar_queue_audit_316.md"
+
+    with csv_path.open("w", newline="", encoding="utf-8") as stream:
+        writer = csv.DictWriter(stream, fieldnames=list(asdict(rows[0])))
+        writer.writeheader()
+        writer.writerows(asdict(row) for row in rows)
+
+    reached = [row for row in rows if row.reached_state_one_endpoint]
+    queue_records = sorted(rows, key=lambda row: (-row.maximum_queue, row.root))[:20]
+    excursion_records = sorted(
+        rows, key=lambda row: (-row.longest_positive_excursion, row.root)
+    )[:20]
+    nonzero_at_one = [row for row in reached if row.queue_at_state_one_endpoint != 0]
+
+    lines = [
+        "# Canonical Scalar Queue Audit (cp-316)",
+        "",
+        f"Odd roots: `1..{ROOT_MAX}`. Block limit: `{BLOCK_LIMIT}`.",
+        "This is finite computational evidence, not a Lean theorem.",
+        "",
+        "## Summary",
+        "",
+        f"- roots audited: {len(rows)}",
+        f"- roots reaching a state-one canonical endpoint: {len(reached)}",
+        f"- roots with nonzero queue there: {len(nonzero_at_one)}",
+        f"- largest observed queue: {max(row.maximum_queue for row in rows)}",
+        "- no uniform bound or uniform repayment lag follows from this table",
+        "",
+        "## Queue Records",
+        "",
+        "| root | max queue | block | length | claims | capacity | drift | height | depths |",
+        "| --- | --- | --- | --- | --- | --- | --- | --- | --- |",
+    ]
+    lines.extend(
+        f"| {row.root} | {row.maximum_queue} | {row.max_queue_block} | "
+        f"{row.max_queue_block_length} | {row.max_queue_block_claims} | "
+        f"{row.max_queue_block_capacity} | {row.max_queue_block_drift} | "
+        f"{row.max_queue_endpoint_height} | {row.max_queue_claim_depth_histogram} |"
+        for row in queue_records
+    )
+    lines.extend(
+        [
+            "",
+            "## Positive-Excursion Records",
+            "",
+            "| root | longest positive blocks | first return block | max queue | queue at one |",
+            "| --- | --- | --- | --- | --- |",
+        ]
+    )
+    lines.extend(
+        f"| {row.root} | {row.longest_positive_excursion} | "
+        f"{row.first_return_to_zero_after_positive} | {row.maximum_queue} | "
+        f"{row.queue_at_state_one_endpoint} |"
+        for row in excursion_records
+    )
+    md_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
+
+    print(f"roots={len(rows)} reached_one={len(reached)} nonzero_at_one={len(nonzero_at_one)}")
+    print("queue records:")
+    for row in queue_records[:10]:
+        print(row)
+    print("positive excursion records:")
+    for row in excursion_records[:10]:
+        print(row)
+
+
+if __name__ == "__main__":
+    main()
diff --git a/python/Collatz/PetalBridge/results/canonical_scalar_queue_audit_316.md b/python/Collatz/PetalBridge/results/canonical_scalar_queue_audit_316.md
new file mode 100644
index 00000000..66a11151
--- /dev/null
+++ b/python/Collatz/PetalBridge/results/canonical_scalar_queue_audit_316.md
@@ -0,0 +1,62 @@
+# Canonical Scalar Queue Audit (cp-316)
+
+Odd roots: `1..16383`. Block limit: `4096`.
+This is finite computational evidence, not a Lean theorem.
+
+## Summary
+
+- roots audited: 8192
+- roots reaching a state-one canonical endpoint: 8192
+- roots with nonzero queue there: 0
+- largest observed queue: 8
+- no uniform bound or uniform repayment lag follows from this table
+
+## Queue Records
+
+| root | max queue | block | length | claims | capacity | drift | height | depths |
+| --- | --- | --- | --- | --- | --- | --- | --- | --- |
+| 4255 | 8 | 8 | 4 | 2 | 1 | 1 | 2 | d1:1;d3:1 |
+| 4591 | 8 | 6 | 5 | 2 | 1 | 1 | 2 | d2:1;d4:1 |
+| 5673 | 8 | 9 | 4 | 2 | 1 | 1 | 2 | d1:1;d3:1 |
+| 6121 | 8 | 7 | 5 | 2 | 1 | 1 | 2 | d2:1;d4:1 |
+| 6383 | 8 | 8 | 4 | 2 | 1 | 1 | 2 | d1:1;d3:1 |
+| 6471 | 8 | 4 | 4 | 2 | 1 | 1 | 2 | d1:1;d3:1 |
+| 6887 | 8 | 6 | 5 | 2 | 1 | 1 | 2 | d2:1;d4:1 |
+| 8161 | 8 | 8 | 5 | 2 | 1 | 1 | 2 | d2:1;d4:1 |
+| 8191 | 8 | 2 | 4 | 2 | 1 | 1 | 2 | d1:1;d3:1 |
+| 8511 | 8 | 8 | 4 | 2 | 1 | 1 | 2 | d1:1;d3:1 |
+| 9575 | 8 | 8 | 4 | 2 | 1 | 1 | 2 | d1:1;d3:1 |
+| 9663 | 8 | 3 | 7 | 4 | 2 | 2 | 3 | d2:1;d3:1;d5:1;d7:1 |
+| 9707 | 8 | 4 | 4 | 2 | 1 | 1 | 2 | d1:1;d3:1 |
+| 10881 | 8 | 9 | 5 | 2 | 1 | 1 | 2 | d2:1;d4:1 |
+| 10921 | 8 | 3 | 4 | 2 | 1 | 1 | 2 | d1:1;d3:1 |
+| 11347 | 8 | 9 | 4 | 2 | 1 | 1 | 2 | d1:1;d3:1 |
+| 12243 | 8 | 7 | 5 | 2 | 1 | 1 | 2 | d2:1;d4:1 |
+| 12591 | 8 | 14 | 4 | 2 | 1 | 1 | 2 | d1:1;d3:1 |
+| 12767 | 8 | 8 | 4 | 2 | 1 | 1 | 2 | d1:1;d3:1 |
+| 12943 | 8 | 3 | 4 | 2 | 1 | 1 | 2 | d1:1;d3:1 |
+
+## Positive-Excursion Records
+
+| root | longest positive blocks | first return block | max queue | queue at one |
+| --- | --- | --- | --- | --- |
+| 7527 | 20 | 20 | 5 | 0 |
+| 15055 | 20 | 20 | 4 | 0 |
+| 7963 | 19 | 19 | 4 | 0 |
+| 10617 | 19 | 20 | 4 | 0 |
+| 11291 | 19 | 20 | 4 | 0 |
+| 12703 | 19 | 19 | 4 | 0 |
+| 14695 | 18 | 18 | 5 | 0 |
+| 703 | 17 | 17 | 6 | 0 |
+| 937 | 17 | 18 | 6 | 0 |
+| 1055 | 17 | 17 | 5 | 0 |
+| 1249 | 17 | 19 | 6 | 0 |
+| 1583 | 17 | 17 | 5 | 0 |
+| 1665 | 17 | 20 | 6 | 0 |
+| 1875 | 17 | 18 | 5 | 0 |
+| 2463 | 17 | 2 | 6 | 0 |
+| 2499 | 17 | 18 | 6 | 0 |
+| 2631 | 17 | 1 | 6 | 0 |
+| 2813 | 17 | 18 | 5 | 0 |
+| 2919 | 17 | 3 | 6 | 0 |
+| 3331 | 17 | 19 | 6 | 0 |
````
`````
