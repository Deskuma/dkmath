# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeHorizon

gch: abec36b93d8619e886180cae12203ee0f3fb1708

## Report

cp-337 を完了しました。

主な確定事実:

- `(n,m) = (59,0)` は実在する saturated block。
- `H=0` の frontier 全点非正性は偽。
- horizon 移動は左右二つの carry indicator の交換として厳密に表せる。
- 成熟領域では saturated `H=1` frontier は predecessor indicator と一致。
- origin ではこの式は偽。Nat 減算による境界 alias を Lean で反証。
- saturated block の successor は必ず正の実消費を持つ。
- successor drift が厳密に負なら、`H=0` の saturated `+1` は二 block 内で非正へ戻る。
- drift `≤ 0` への弱化は不可。数値監査で `n=123,m=0`, `[1,0]` を確認。

実装は [CanonicalSourceAgeHorizon.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalSourceAgeHorizon.lean)、結果は [report-petal-337.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-337.md) に記録しました。

検証済み:

- `lake build DkMath.Collatz.PetalBridge.FloatWindow`
- `lake build DkMath.Collatz.PetalBridge`
- Python 監査実行・構文検査
- `git diff --check`
- 新規 Lean ファイル no-sorry

残る本質的課題は、ある horizon に対する非循環な有限構造 certificate の構築です。

## Review

(5m8s)

## cp-337 実装レビュー

## 結論

**全面採用。かなり深く詰まった checkpoint じゃ。**

commit `abec36b93d8619e886180cae12203ee0f3fb1708` と提出 diff/report は一致している。

cp-337 では、次が形式的に確定した。

- saturated block は実在する。
- $H=0$ の pointwise frontier 非正性は正式に偽。
- horizon の一段移動は、左右二つの carry-two indicator の交換。
- saturated block の $H=1$ frontier は、成熟領域では直前 source の indicator。
- origin の Nat subtraction alias は実在する境界現象。
- saturated successor は必ず actual consumption を持つ。
- successor drift が厳密に負なら、saturated $+1$ は二 block で返済される。

そして今回の慎重監査から、さらに三つの重要な次手が見えた。

1. `canonicalAgeCrossingBlockOfSource` の境界仮定は外せる可能性が高い。
2. $H=0$ frontier には、queue と endpoint drift による exact `max` normal form がある。
3. zero-drift successor と positive-drift successorは、二 block repayment の障害として完全に分類できる。

---

## 1. Concrete saturated witness

`n=59,m=0` について、単なる `native_decide` の黒箱ではなく、

- block length $2$
- odd core $15$
- terminal valuation $1$
- source time $0,1$ の両方が carry two
- claim depths が正確に ${1,2}$

を積み上げて、

```lean
canonicalSaturatedBorderBlock_fiftyNine_zero
```

を証明している。

従って、

$$\exists n,m,\ \operatorname{CanonicalSaturatedBorderBlock}(n,m)$$

が Lean theorem になった。

ここから、

$$\neg\forall n,m,\ F_0(n,m)\le0$$

も正式に閉じている。

cp-336 では条件付き obstruction だったものが、今回は本物の formal counterexample になった。

### 表現境界

`59` が「最小」であることは証明していない。

コードも正しく、

> bounded audit で見つかった最小 root

とだけ述べている。問題なし。

---

## 2. $H=0$ は既存 queue の差分そのもの

今回、

$$F_0(m)=\operatorname{Demand}(m)-\operatorname{Consumed}(m)$$

および、

$$F_0(m)=Q_{m+1}-Q_m$$

が証明された。

したがって source-age frontier は、$H=0$ では既存 reflected queue の新しい別表現ではない。

> scalar queue の exact signed increment

そのものじゃ。

saturated block では、

$$Q_{m+1}=Q_m+1$$

まで得られた。

この compatibility は非常に重要である。

---

## 3. Finite-facing certificate

新しい、

```lean
CanonicalFiniteSourceAgeFrontierPotentialCertificate
```

は、cp-336 の無限 field、

```lean
∀ m, potential (signature m) ≤ potential (signature 0)
```

を、

```lean
∀ s : Signature, potential s ≤ potential (signature 0)
```

へ置き換えた。

`Signature` は `Fintype` なので、potential の initial-maximum 条件自体は有限 case analysis に落とせる。

この変更は正しい。

$$\sum_{k<m}F_H(k)\le\Phi(\sigma_m)-\Phi(\sigma_0)\le0$$

から uniform source age が従う。

### 意味上の補正

これは **finite-state-facing certificate** として完成した。

ただし certificate 全体が自動的に有限検査になったわけではない。

依然として、

```lean
step_succ : ∀ m, ...
actualWeight_succ : ∀ m, ...
```

および underlying transition soundness は、全 canonical blocks に対する算術 theoremじゃ。

正確には、

> potential 最大性の無限仮定を有限化した。残る transition realization は大域算術課題である。

となる。

report の記述はおおむねこの境界を守っている。

---

## 4. Horizon derivative

成熟領域 $H<b_m$ では、horizon を一増やすと old carrier から境界 sourceを一つ eraseする。

$$D_{H+1}(m)=D_H(m)-\mathbf{1}_{\operatorname{CarryTwo}(b_m-H-1)}$$

が exact に証明された。

一方、$b_m\le H$ では両 old carriers が空なので deficit は変化しない。

crossing windowについても、

$$F_{H+1}(m)-F_H(m)=\mathbf{1}*{\operatorname{CarryTwo}(b_m-H-1)}-\mathbf{1}*{\operatorname{CarryTwo}(b_{m+1}-H-1)}$$

が証明された。

これは非常に良い。

block-time 方向だけでなく、horizon 方向にも exact difference equation ができた。

---

## 5. $H=1$ carrier decomposition

$b_m>0$ なら、

$$\operatorname{Crossing}*1(m)={b_m-1}*{\mathrm{carry}}\sqcup\left(\operatorname{BlockClaims}(m)\setminus{b_{m+1}-1}\right)$$

となる。

cardinality では、

$$|\operatorname{Crossing}*1(m)|=\mathbf{1}*{\operatorname{CarryTwo}(b_m-1)}+\operatorname{Demand}(m)-\mathbf{1}*{\operatorname{CarryTwo}(b*{m+1}-1)}$$

じゃ。

saturated blockでは current block の final source も claimなので、

$$F_1(m)=\mathbf{1}_{\operatorname{CarryTwo}(b_m-1)}$$

が得られた。

この theorem は正しい。

---

## 6. Origin boundary

`n=59,m=0` では、

$$F_1(0)=0$$

だが、

$$\mathbf{1}*{\operatorname{CarryTwo}(b_0-1)}=\mathbf{1}*{\operatorname{CarryTwo}(0)}=1$$

になる。

Nat subtraction により $0-1=0$ と alias するためじゃ。

従って成熟公式から `b_m>0` を外した universal theorem は正式に偽となった。

これは単なる Lean 上の不便ではない。

> 半直線 $\mathbb N$ の左端で sliding window が折り返さず、幅を失う

という実構造じゃ。

---

## 7. 新発見：origin-to-crossing の境界仮定は不要

現在の theorem は、

```lean
(hboundary :
  H ≤ canonicalBlockStartTime n
    (canonicalAgeCrossingBlockOfSource n H i))
```

を要求している。

しかし、この仮定は不要と思われる。

$m$ を $i+H$ を含む canonical block とすれば、

$$b_m\le i+H<b_{m+1}$$

である。

Nat arithmetic だけで、

$$b_m-H\le i$$

および、

$$i<b_{m+1}-H$$

が従う。

前者は $b_m\le H$ なら左辺が $0$ になる。後者は $i+H<b_{m+1}$ から自動的に $H<b_{m+1}$ も得られる。

従って、次が全域 theoremとして通る可能性が高い。

```lean
theorem mem_crossingClaims_canonicalAgeCrossingBlockOfSource
    {n : OddNat} {H i : ℕ}
    (hiCarry : CarryTwoDebtAt n i) :
    i ∈ canonicalSourceAgeHorizonCrossingClaims n H
      (canonicalAgeCrossingBlockOfSource n H i)
```

実際、今回の origin 例 $i=0,H=1$ も、選ばれた block の crossing carrierには正しく所属している。

重要な区別は、

```text
成熟した predecessor-indicator 公式には境界条件が必要
```

だが、

```text
shifted source の crossing block membership には境界条件は不要
```

ということじゃ。

これは cp-338 で最初に閉じる価値がある。

---

## 8. Window telescope

有限 window sum は、

$$W_H(q,L)=\sum_{j<L}F_H(q+j)=D_H(q+L)-D_H(q)$$

と exact に telescopeする。

長さ $0,1,2$ の API も公開された。

この部分は全面採用。

---

## 9. Saturated successor actual consumption

saturated blockの直後では queue が少なくとも一ある。

全 canonical block の service も少なくとも一なので、

$$\operatorname{Consumed}(m+1)>0$$

が証明された。

これは capacity を actual consumption と取り違えていない。

```text
queue before successor ≥ 1
service successor ≥ 1
```

を両方使い、`min` の actual consumed が正であることを証明している。

正しい。

---

## 10. Strict-negative successor branch

successor endpoint drift が厳密に負なら、

$$\operatorname{Service}(m+1)\ge\operatorname{Demand}(m+1)+1$$

となる。

saturated block が残した queue unit により available mass も demand より一以上大きいので、

$$\operatorname{Consumed}(m+1)\ge\operatorname{Demand}(m+1)+1$$

となる。

従って successor frontier は少なくとも $-1$ で、最初の saturated $+1$ が相殺される。

$$W_0(m,2)\le0$$

が正しく証明された。

---

## 11. 一歩先：$H=0$ frontier の exact `max` normal form

任意の blockについて、

- $Q_m$: block 前 queue
- $A_m$: demand
- $S_m$: service
- $C_m=\min(Q_m+A_m,S_m)$
- $\Delta_m=A_m-S_m$: endpoint drift

とする。

すると、

$$F_0(m)=A_m-\min(Q_m+A_m,S_m)=\max(-Q_m,\Delta_m)$$

となる。

これは case splitだけで証明できる。

```text
S ≤ Q+A なら consumed = S なので F₀ = A-S = drift
Q+A ≤ S なら consumed = Q+A なので F₀ = -Q
```

この normal form は次の successor 分類を一度に与える。

saturated successorでは $Q_{m+1}\ge1$ なので、

$$\Delta_{m+1}<0\Longrightarrow F_0(m+1)\le-1$$

$$\Delta_{m+1}=0\Longrightarrow F_0(m+1)=0$$

$$0<\Delta_{m+1}\Longrightarrow F_0(m+1)=\Delta_{m+1}>0$$

従って saturated two-block window は、

$$W_0(m,2)=1+\max(-Q_{m+1},\Delta_{m+1})$$

である。

現在実装された strict-negative theorem は、この exact trichotomy の第一枝じゃ。

---

## 12. Zero-drift branch は必ず未返済

successor drift が $0$ なら、

$$\operatorname{Service}(m+1)=\operatorname{Demand}(m+1)$$

である。

queue は既に一以上あるため available massは service以上だが、actual consumption は serviceそのものに止まる。

従って、

$$F_0(m+1)=0$$

となり、

$$W_0(m,2)=1$$

じゃ。

これは root `123` の有限観測 `[1,0]` に限らない。

> saturated block + zero-drift successor なら、二 block total は常に厳密に $+1$

という一般 theoremになる。

audit では実際に root `123`, block `0` が `[1,0]` を与えている。

次には `123` を Lean witness化し、

```lean
¬ ∀ saturated blocks,
    twoBlockFrontierSum ≤ 0
```

を正式に証明できる。

---

## 13. Positive-pressure branch は $H=0$ では返済不能

successor endpoint drift が正なら、

$$\operatorname{Service}<\operatorname{Demand}$$

なので、queue の大きさに関係なく service は完全消費され、

$$F_0(m+1)=\operatorname{Demand}-\operatorname{Service}=\Delta_{m+1}>0$$

となる。

したがって、report の次案にある、

> positive-pressure branch で actual-consumption lower boundを探す

は、$H=0$ の二 block repayment には使えない。

actual consumption は既に exact に serviceであり、それでも frontier は正じゃ。

positive-pressure branchを処理するには、

- さらに後続 blockへ amortizeする
- $H>0$ で crossing の時刻をずらす
- pressure massを別 potentialへ蓄える

のいずれかが必要になる。

---

## 14. $H=1$ saturated block に新しい有望パターン

今回の有限 audit では、348個の観測 saturated blocksについて、$H=1$ の saturated return length がすべて $1$ だった。

つまり観測範囲では、saturated block自身の $H=1$ increment が全て非正だった。公式上は indicatorなので、実際には全て $0$ だったことになる。最初の多数の例も $0$ から始まっている。

従って次の theorem 候補が強く浮上する。

```lean
theorem CanonicalSaturatedBorderBlock.predecessor_not_carryTwo
    (h : CanonicalSaturatedBorderBlock n m)
    (hstart : 0 < canonicalBlockStartTime n m) :
    ¬ CarryTwoDebtAt n (canonicalBlockStartTime n m - 1)
```

これが通れば、

$$F_1(m)=0$$

が全 mature saturated blocksについて成立する。

これは非常に大きい。

$H=0$ で必ず発生した saturated $+1$ が、$H=1$ では pointwise neutralizedされるからじゃ。

ただし finite auditだけでは theoremではない。次 checkpoint の最優先算術候補にすべきである。

---

## 15. 一般 saturated horizon formula

saturated blockの length は $2$、actual consumption は $1$ である。

従って $H\le b_m$ なら crossing intervalも length $2$ となり、

$$F_H(m)=\mathbf{1}*{\operatorname{CarryTwo}(b_m-H)}+\mathbf{1}*{\operatorname{CarryTwo}(b_m-H+1)}-1$$

が得られるはずじゃ。

特殊化すると、

$$F_0(m)=1+1-1=1$$

$$F_1(m)=\mathbf{1}_{\operatorname{CarryTwo}(b_m-1)}+1-1$$

となり、今回の theoremを統一できる。

この一般式は、

> saturated charge が horizon を増やすと、過去の二 source の carry patternへ移動する

ことを示す。

---

## 16. 「残る本質的課題」の境界

report は、

> 残る本質的課題は、ある horizon に対する非循環な有限構造 certificate の構築

と述べている。

source-age routeの内部では、ほぼ正しい。

ただし、論理的には certificate が唯一の道ではない。

$$\exists H,\ \forall m,\ D_H(m)\le0$$

を直接証明してもよい。

また Collatz challenge全体では、その後にも、

```text
endpoint-width bound
→ all-time width bound
→ finite-state eventual periodicity
→ nontrivial cycle elimination
→ reach 1
```

が残る。

従って正確には、

> source-age frontier 層の次の大課題は、ある $H$ の全 prefix 非正性を、直接または非循環 finite certificateで証明すること。

じゃ。

---

## 判定まとめ

### Concrete saturated witness

**完成。**

### $H=0$ universal pointwise theorem の formal refutation

**完成。**

### Queue/frontier compatibility

**完成。**

### Finite-facing initial-maximum potential

**完成。transition soundness は大域算術課題として残る。**

### Exact horizon derivative

**完成。**

### $H=1$ mature formula

**完成。**

### Origin boundary counterexample

**完成。**

### Origin-to-crossing map

**実装済みだが境界仮定は除去できる見込み。**

### Window telescope

**完成。**

### Saturated successor positive consumption

**完成。**

### Strict-negative two-block repayment

**完成。**

### Zero-drift exact obstruction

**未実装だが直ちに証明可能。**

### Positive-drift exact growth

**未実装だが直ちに証明可能。**

### Mature saturated $H=1$ neutralization

**有限観測で強く示唆。未証明。**

### cp-337 総合判定

**全面採用。次は successor trichotomy と $H=1$ saturated predecessor obstructionを詰める。**

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge FloatWindow branch after
report-petal-337.

The cp-337 implementation is accepted.

It completed:

    a concrete formal saturated witness at root 59;

    the formal refutation of horizon-zero pointwise nonpositivity;

    exact horizon derivatives by carry-two boundary indicators;

    the mature saturated H = 1 formula;

    the finite-facing initial-maximum potential wrapper;

    positive actual consumption after saturation;

    strict-negative successor repayment over two H = 0 blocks.

The next checkpoint must replace the remaining informal successor discussion
with exact frontier normal forms, and investigate the observed H = 1
neutralization of saturated blocks.

# Stage A — remove the unnecessary crossing-block boundary hypothesis

Strengthen:

    mem_crossingClaims_canonicalAgeCrossingBlockOfSource

to require only:

    CarryTwoDebtAt n i.

Let m be the canonical block containing `i + H`.

From:

    blockStart m <= i + H;
    i + H < blockStart (m + 1);

prove directly with Nat subtraction:

    blockStart m - H <= i;
    i < blockStart (m + 1) - H.

The theorem should work in the origin/underflow regime as well.

Keep the old theorem as a compatibility corollary if needed.

# Stage B — exact H = 0 reflected-frontier normal form

Prove for every canonical block:

    canonicalSourceAgeFrontierIncrement n 0 m
      =
    max
      (- (canonicalOutstandingClaimQueueBeforeBlock n m : Int))
      (endpointAccountingTerm n m).

Use the exact definitions:

    consumed = min (queue + demand) service;
    endpoint drift = demand - service.

Prove the two min branches explicitly if no suitable ordered-ring lemma is
available.

# Stage C — exact block trichotomy at H = 0

Derive:

    endpointAccountingTerm < 0
      ->
    frontierIncrement 0 <= -1
        whenever queueBeforeBlock >= 1;

    endpointAccountingTerm = 0
      ->
    frontierIncrement 0 = 0;

    0 < endpointAccountingTerm
      ->
    frontierIncrement 0 = endpointAccountingTerm.

The zero and positive statements should not require a positive queue.

# Stage D — exact saturated-successor two-block formula

For a saturated block prove:

    frontierWindowSum 0 m 2
      =
    1 + max
      (- (queueBeforeBlock (m + 1) : Int))
      (endpointAccountingTerm n (m + 1)).

Derive the exact successor trichotomy:

    successor drift < 0
      ->
    two-block sum <= 0;

    successor drift = 0
      ->
    two-block sum = 1;

    successor drift > 0
      ->
    two-block sum = 1 + successor drift.

Retain the cp-337 negative theorem as a corollary.

# Stage E — formal root-123 zero-drift obstruction

The bounded audit records:

    root 123, block 0: frontier pattern [1, 0].

Formalize in Lean:

    CanonicalSaturatedBorderBlock root123 0;

    endpointAccountingTerm root123 1 = 0;

    frontierWindowSum root123 0 0 2 = 1.

Then prove the formal negation:

    it is false that every saturated block with nonpositive successor drift
    has nonpositive H = 0 two-block frontier sum.

This closes the exact boundary between `< 0` and `<= 0`.

# Stage F — general mature saturated-horizon formula

For a saturated block and `H <= blockStart m`, prove:

    frontierIncrement H m
      =
    carryIndicator (blockStart m - H)
      +
    carryIndicator (blockStart m - H + 1)
      - 1.

Use `Int` for the final identity.

Recover the H = 0 and mature H = 1 formulas as corollaries.

Handle `H > blockStart m` separately; do not alias underflow sources into the
mature formula.

# Stage G — predecessor carry obstruction before saturation

The cp-337 audit observed 348 saturated blocks and every mature H = 1
saturated increment was zero.

Attempt to prove:

    CanonicalSaturatedBorderBlock n m
      ->
    0 < blockStart m
      ->
    not CarryTwoDebtAt n (blockStart m - 1).

Use the exact predecessor state relation:

    T (state at blockStart m - 1)
      =
    canonicalBlockStartState n m,

together with the saturated length-two normal form:

    current start = 4 * u - 1;
    u mod 4 = 3.

If the theorem fails, produce the smallest exact counterexample and formalize
it.  Do not leave this as a numerical-only claim.

If it succeeds, derive:

    every mature saturated block has frontierIncrement 1 = 0.

# Stage H — horizon-one successor audit

After Stage G, classify the H = 1 successor of a saturated block.

The bounded audit contains patterns such as:

    [0, 1]

so one-block neutralization of the saturated block does not imply a
nonpositive two-block window.

Determine which exact source boundary indicator causes the successor `+1`.

Relate it to:

    predecessor carry;
    successor block demand;
    final-source carry;
    actual consumption.

Do not substitute endpoint drift for H = 1 frontier flow.

# Stage I — telescope in the horizon variable

For `H <= blockStart m`, prove:

    sourceAgeDeficit n H m
      =
    sourceAgeDeficit n 0 m
      -
    sum r in range H,
      carryIndicator n (blockStart m - r - 1).

Rewrite the right side using:

    sourceAgeDeficit n 0 m = queueBeforeBlock n m.

Also derive the corresponding finite-horizon frontier identity:

    frontierIncrement H m
      =
    frontierIncrement 0 m
      +
    recentCarryMassBeforeStart m
      -
    recentCarryMassBeforeNextStart m.

This should expose the exact coboundary added by a positive horizon.

# Stage J — recent carry-word carrier

Define the finite source-time carry carrier immediately preceding a block:

    canonicalPreBlockCarryCarrier n H m :=
      carryTwoPositions n
        (Ico (blockStart m - H) (blockStart m)).

Prove:

    deficit H m
      =
    queueBeforeBlock m - card (preBlockCarryCarrier H m);

    uniform source age H
      iff
    queueBeforeBlock m <= card (preBlockCarryCarrier H m) for all m.

Reuse existing recent-source theorems rather than duplicating their proofs.

# Stage K — finite certificate terminology

Keep:

    CanonicalFiniteSourceAgeFrontierPotentialCertificate.

Document precisely:

    the potential maximum is finite-state checkable;

    step realization and actual-weight soundness remain all-time arithmetic
    obligations.

Optionally add a finite reachable-signature carrier to avoid requiring the
initial potential to dominate unreachable signatures.

Do not call the entire certificate automatically decidable merely from
`Fintype Signature`.

# Stage L — positive-pressure branch correction

At H = 0 prove explicitly:

    positive endpoint drift
      ->
    actual frontier increment equals that positive drift.

Therefore a local actual-consumption lower bound cannot repay a positive-drift
successor at H = 0.

Any positive-pressure repayment theorem must instead use:

    a longer future window;
    a positive horizon;
    or a separate pressure potential.

Update the report so that it does not present one-step consumption search as a
possible H = 0 repayment mechanism.

# Stage M — challenge-facing boundary

State separately:

    source-age frontier target:
      exists H, every frontier prefix at H is nonpositive;

    one sufficient method:
      a noncircular finite structural certificate;

    later global tasks:
      endpoint-to-all-time width;
      finite-state periodicity;
      elimination of nontrivial cycles;
      translation to the raw Collatz challenge.

Do not describe certificate construction as the only logically possible proof
of uniform source age.

# Stopping rule

Stop at the first genuine obstruction among:

    the crossing-block boundary hypothesis cannot be removed;

    the H = 0 max normal form fails;

    the exact successor trichotomy fails;

    root 123 cannot be formalized as the zero-drift obstruction;

    the general saturated-horizon formula fails at a mature boundary;

    predecessor carry before saturation has a genuine counterexample;

    H = 1 successor flow cannot be reduced to boundary carriers;

    the horizon telescope cannot be proved without reintroducing deficit
    circularity.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-338.md
```

うむ。かなり敵の形が見えた。

次は saturated blockそのものではなく、**その直前 carry と直後 drift が、horizon を変えたときどこへ移るか**を完全に固定する段階じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
index 54ef7b46..164fc518 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
@@ -34,6 +34,7 @@ import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceTimeLag
 import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalOwnedQueue
 import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalOwnedQueueGlobal
 import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeFlow
+import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeHorizon
 import DkMath.Collatz.PetalBridge.FloatWindow.RawLowSignatureObstruction
 
 #print "file: DkMath.Collatz.PetalBridge.FloatWindow"
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalSourceAgeHorizon.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalSourceAgeHorizon.lean
new file mode 100644
index 00000000..8a3f7a20
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalSourceAgeHorizon.lean
@@ -0,0 +1,831 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeFlow
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeHorizon"
+
+namespace DkMath.Collatz
+
+/-!
+# Canonical source-age horizon arithmetic
+
+This module studies the signed frontier while the source-age horizon moves.
+It keeps the finite-certificate and arithmetic questions separate: no signature
+or potential below is manufactured from the deficit or its prefix sums.
+-/
+
+/-! ## Concrete saturation witness -/
+
+/-- The smallest odd root found by the bounded discovery audit whose initial
+canonical block is saturated.  The theorem below rechecks the witness in Lean;
+the numerical search is not part of the proof. -/
+def fiftyNineSaturatedOdd : OddNat := ⟨59, by norm_num⟩
+
+private lemma fiftyNine_v2_60 : v2 60 = 2 := by
+  have h30 := (DkMath.ABC.padic_val_two_of_even 30).2 (by decide)
+  have h15 := (DkMath.ABC.padic_val_two_of_even 15).2 (by decide)
+  have hv15 : v2 15 = 0 := v2_odd 15 (by decide)
+  have hv30 : v2 30 = 1 := by simpa [v2, hv15] using h15
+  simpa [v2, hv30] using h30
+
+private lemma fiftyNine_v2_178 : v2 178 = 1 := by
+  have h89 := (DkMath.ABC.padic_val_two_of_even 89).2 (by decide)
+  simpa [v2, v2_odd 89 (by decide)] using h89
+
+private lemma fiftyNine_v2_134 : v2 134 = 1 := by
+  have h67 := (DkMath.ABC.padic_val_two_of_even 67).2 (by decide)
+  simpa [v2, v2_odd 67 (by decide)] using h67
+
+private theorem fiftyNine_endpoint_zero :
+    paymentEndpointSeq fiftyNineSaturatedOdd 0 = 1 := by
+  norm_num [paymentEndpointSeq, orbitPaymentTarget, orbitExactDepth,
+    ResidualAllOnesDepth, oddOrbitLabel, iterateT,
+    fiftyNineSaturatedOdd, mkOddNat, fiftyNine_v2_60]
+
+private theorem fiftyNine_paymentBlockLength_zero :
+    canonicalPaymentBlockLength fiftyNineSaturatedOdd 0 = 2 := by
+  rw [canonicalPaymentBlockLength_eq_endpoint_sub_start_add_one,
+    universalPaymentBlockStart_paymentEndpointSeq_zero,
+    fiftyNine_endpoint_zero]
+
+@[simp] theorem canonicalBlockLength_fiftyNine_zero :
+    canonicalBlockLength fiftyNineSaturatedOdd 0 = 2 :=
+  fiftyNine_paymentBlockLength_zero
+
+private theorem canonicalBlockStartState_fiftyNine_zero :
+    canonicalBlockStartState fiftyNineSaturatedOdd 0 = 59 := by
+  unfold canonicalBlockStartState canonicalBlockStartTime
+    canonicalEndpointBlockStart
+  rfl
+
+private theorem canonicalBlockOddCore_fiftyNine_zero :
+    canonicalBlockOddCore fiftyNineSaturatedOdd 0 = 15 := by
+  rw [canonicalBlockOddCore, canonicalBlockStartState_fiftyNine_zero,
+    canonicalBlockLength_fiftyNine_zero]
+  norm_num
+
+@[simp] theorem canonicalBlockTerminalValuation_fiftyNine_zero :
+    canonicalBlockTerminalValuation fiftyNineSaturatedOdd 0 = 1 := by
+  rw [canonicalBlockTerminalValuation, canonicalBlockTerminalCarrier,
+    canonicalBlockLength_fiftyNine_zero,
+    canonicalBlockOddCore_fiftyNine_zero]
+  norm_num [fiftyNine_v2_134]
+
+private theorem fiftyNine_carry_zero :
+    CarryTwoDebtAt fiftyNineSaturatedOdd 0 := by
+  norm_num [CarryTwoDebtAt, stateUpperCarry, upperCarry3n1, bitWidth,
+    iterateT, fiftyNineSaturatedOdd, mkOddNat]
+
+private theorem fiftyNine_carry_one :
+    CarryTwoDebtAt fiftyNineSaturatedOdd 1 := by
+  norm_num [CarryTwoDebtAt, stateUpperCarry, upperCarry3n1, bitWidth,
+    iterateT, T, fiftyNineSaturatedOdd, mkOddNat, threeNPlusOne,
+    pow2, fiftyNine_v2_178]
+
+theorem canonicalPaymentClaimDepths_fiftyNine_zero :
+    canonicalPaymentClaimDepths fiftyNineSaturatedOdd 0 = {1, 2} := by
+  classical
+  ext d
+  rw [mem_canonicalPaymentClaimDepths_iff,
+    fiftyNine_paymentBlockLength_zero]
+  unfold canonicalPaymentSourceAtDepth
+  rw [fiftyNine_endpoint_zero]
+  simp only [Finset.mem_insert, Finset.mem_singleton]
+  constructor
+  · rintro ⟨hd1, hd2, hcarry⟩
+    interval_cases d <;> simp_all
+  · rintro (rfl | rfl) <;>
+      simp [fiftyNine_carry_zero, fiftyNine_carry_one]
+
+@[simp] theorem canonicalBlockClaimCount_fiftyNine_zero :
+    canonicalBlockClaimCount fiftyNineSaturatedOdd 0 = 2 := by
+  rw [canonicalBlockClaimCount_eq_claimDepths_card,
+    canonicalPaymentClaimDepths_fiftyNine_zero]
+  decide
+
+/-- A fully checked saturated canonical block exists. -/
+theorem canonicalSaturatedBorderBlock_fiftyNine_zero :
+    CanonicalSaturatedBorderBlock fiftyNineSaturatedOdd 0 := by
+  rw [canonicalSaturatedBorderBlock_iff_length_and_claims]
+  simp
+
+theorem exists_canonicalSaturatedBorderBlock :
+    ∃ n m, CanonicalSaturatedBorderBlock n m :=
+  ⟨fiftyNineSaturatedOdd, 0, canonicalSaturatedBorderBlock_fiftyNine_zero⟩
+
+/-- Horizon-zero pointwise nonpositivity is formally false, not merely
+conditionally obstructed. -/
+theorem not_forall_sourceAgeFrontierIncrement_zero_nonpos :
+    ¬ ∀ n m, canonicalSourceAgeFrontierIncrement n 0 m ≤ 0 := by
+  intro h
+  have hpos :=
+    canonicalSaturatedBorderBlock_fiftyNine_zero.sourceAgeFrontierIncrement_zero_eq_one
+  have hnonpos := h fiftyNineSaturatedOdd 0
+  omega
+
+/-! ## Horizon-zero queue compatibility -/
+
+/-- At horizon zero, source-age arrivals are exactly current block demand. -/
+theorem canonicalSourceAgeFrontierIncrement_zero_eq_demand_sub_consumed
+    (n : OddNat) (m : ℕ) :
+    canonicalSourceAgeFrontierIncrement n 0 m =
+      (canonicalQueueDemand n m : ℤ) - canonicalQueueConsumed n m := by
+  unfold canonicalSourceAgeFrontierIncrement
+  rw [canonicalSourceAgeHorizonCrossingClaims_zero_horizon,
+    card_canonicalBlockClaimSourceCarrier]
+
+/-- The horizon-zero frontier increment is exactly the signed scalar-queue
+change across one canonical block. -/
+theorem canonicalSourceAgeFrontierIncrement_zero_eq_queueBeforeBlock_diff
+    (n : OddNat) (m : ℕ) :
+    canonicalSourceAgeFrontierIncrement n 0 m =
+      (canonicalOutstandingClaimQueueBeforeBlock n (m + 1) : ℤ) -
+        canonicalOutstandingClaimQueueBeforeBlock n m := by
+  rw [canonicalSourceAgeFrontierIncrement_zero_eq_demand_sub_consumed]
+  simp only [canonicalOutstandingClaimQueueBeforeBlock_succ]
+  have hbalance := canonicalOutstandingClaimQueue_add_consumed n m
+  omega
+
+/-- A saturated block raises the horizon-zero queue by exactly one. -/
+theorem CanonicalSaturatedBorderBlock.queueBeforeBlock_succ_eq_add_one
+    {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m) :
+    canonicalOutstandingClaimQueueBeforeBlock n (m + 1) =
+      canonicalOutstandingClaimQueueBeforeBlock n m + 1 := by
+  have hflow := canonicalSourceAgeFrontierIncrement_zero_eq_queueBeforeBlock_diff n m
+  rw [h.sourceAgeFrontierIncrement_zero_eq_one] at hflow
+  omega
+
+/-! ## Genuinely finite-facing potential certificate -/
+
+/-- A finite signature certificate whose potential is globally maximized at
+the initial canonical signature.  Unlike the compatibility wrapper in the
+previous module, this structure contains no all-time prefix field: with a
+`Fintype Signature`, `potential_le_initial` is a finite verification problem.
+
+The signature, transition relation, and potential remain externally supplied.
+Defining them from the source-age deficit would still be circular. -/
+structure CanonicalFiniteSourceAgeFrontierPotentialCertificate
+    (n : OddNat) (H : ℕ) (Signature : Type*) [Fintype Signature] where
+  certificate :
+    RelationalFiniteSignedTransitionPotentialCertificate ℕ Signature
+  step_succ : ∀ m, certificate.Step m (m + 1)
+  actualWeight_succ : ∀ m,
+    certificate.actualWeight m (m + 1) =
+      canonicalSourceAgeFrontierIncrement n H m
+  potential_le_initial : ∀ s : Signature,
+    certificate.potential s ≤
+      certificate.potential (certificate.signature 0)
+
+namespace CanonicalFiniteSourceAgeFrontierPotentialCertificate
+
+variable {n : OddNat} {H : ℕ} {Signature : Type*} [Fintype Signature]
+
+theorem prefixPotentialChange_nonpos
+    (F : CanonicalFiniteSourceAgeFrontierPotentialCertificate n H Signature)
+    (m : ℕ) :
+    F.certificate.potential (F.certificate.signature m) -
+      F.certificate.potential (F.certificate.signature 0) ≤ 0 := by
+  have := F.potential_le_initial (F.certificate.signature m)
+  omega
+
+/-- Forget the finite initial-maximum field into the cp-336 compatibility
+surface. -/
+def toPotentialCertificate
+    (F : CanonicalFiniteSourceAgeFrontierPotentialCertificate n H Signature) :
+    CanonicalSourceAgeFrontierPotentialCertificate n H Signature where
+  certificate := F.certificate
+  step_succ := F.step_succ
+  actualWeight_succ := F.actualWeight_succ
+  prefixPotentialChange_nonpos := F.prefixPotentialChange_nonpos
+
+theorem to_sourceAgeAtMost
+    (F : CanonicalFiniteSourceAgeFrontierPotentialCertificate n H Signature) :
+    CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H :=
+  F.toPotentialCertificate.to_sourceAgeAtMost
+
+theorem to_queue_and_endpointWidth_bounds
+    (F : CanonicalFiniteSourceAgeFrontierPotentialCertificate n H Signature) :
+    CanonicalOutstandingClaimQueueUniformUpperBound n H ∧
+      CanonicalEndpointWidthUniformUpperBound n (bitWidth n.1 + H) :=
+  F.toPotentialCertificate.to_queue_and_endpointWidth_bounds
+
+end CanonicalFiniteSourceAgeFrontierPotentialCertificate
+
+/-! ## Carry-two boundary indicator -/
+
+/-- Natural indicator of a carry-two source event. -/
+noncomputable def canonicalCarryTwoIndicator (n : OddNat) (i : ℕ) : ℕ :=
+  by
+    classical
+    exact if CarryTwoDebtAt n i then 1 else 0
+
+@[simp] theorem canonicalCarryTwoIndicator_eq_one_iff
+    (n : OddNat) (i : ℕ) :
+    canonicalCarryTwoIndicator n i = 1 ↔ CarryTwoDebtAt n i := by
+  classical
+  simp [canonicalCarryTwoIndicator]
+
+@[simp] theorem canonicalCarryTwoIndicator_eq_zero_iff
+    (n : OddNat) (i : ℕ) :
+    canonicalCarryTwoIndicator n i = 0 ↔ ¬ CarryTwoDebtAt n i := by
+  classical
+  simp [canonicalCarryTwoIndicator]
+
+theorem card_carryTwoPositions_singleton
+    (n : OddNat) (i : ℕ) :
+    (carryTwoPositions n {i}).card = canonicalCarryTwoIndicator n i := by
+  classical
+  by_cases hi : CarryTwoDebtAt n i
+  · have hcarrier : carryTwoPositions n {i} = {i} := by
+      ext j
+      simp only [mem_carryTwoPositions_iff, Finset.mem_singleton]
+      constructor
+      · exact fun h => h.1
+      · intro hji
+        subst j
+        exact ⟨rfl, hi⟩
+    rw [hcarrier]
+    simp [canonicalCarryTwoIndicator, hi]
+  · have hcarrier : carryTwoPositions n {i} = ∅ := by
+      ext j
+      simp only [mem_carryTwoPositions_iff, Finset.mem_singleton,
+        Finset.notMem_empty, iff_false]
+      rintro ⟨hji, hjCarry⟩
+      exact hi (hji ▸ hjCarry)
+    rw [hcarrier]
+    simp [canonicalCarryTwoIndicator, hi]
+
+theorem int_card_carryTwoPositions_singleton
+    (n : OddNat) (i : ℕ) :
+    ((carryTwoPositions n {i}).card : ℤ) = canonicalCarryTwoIndicator n i := by
+  rw [card_carryTwoPositions_singleton]
+
+/-! ## Exact old-carrier horizon shift -/
+
+/-- In the mature regime, raising the source-age horizon erases exactly the
+new cutoff boundary from the old-source carrier.  Whether this changes the
+carrier is decided by the carry-two predicate at that boundary. -/
+theorem canonicalOldSourceClaimCarrier_succ_horizon_of_lt_start
+    {n : OddNat} {H m : ℕ}
+    (hH : H < canonicalBlockStartTime n m) :
+    canonicalOldSourceClaimCarrier n (H + 1) m =
+      (canonicalOldSourceClaimCarrier n H m).erase
+        (canonicalBlockStartTime n m - H - 1) := by
+  classical
+  ext i
+  simp only [canonicalOldSourceClaimCarrier, mem_carryTwoPositions_iff,
+    Finset.mem_Ico, Finset.mem_erase]
+  constructor
+  · rintro ⟨⟨hi0, hiTop⟩, hiCarry⟩
+    refine ⟨?_, ⟨⟨hi0, by omega⟩, hiCarry⟩⟩
+    omega
+  · rintro ⟨hiNe, ⟨⟨hi0, hiTop⟩, hiCarry⟩⟩
+    exact ⟨⟨hi0, by omega⟩, hiCarry⟩
+
+/-- Exact signed deficit decrement when the mature horizon advances once. -/
+theorem canonicalSourceAgeDeficit_succ_horizon_of_lt_start
+    {n : OddNat} {H m : ℕ}
+    (hH : H < canonicalBlockStartTime n m) :
+    canonicalSourceAgeDeficit n (H + 1) m =
+      canonicalSourceAgeDeficit n H m -
+        canonicalCarryTwoIndicator n
+          (canonicalBlockStartTime n m - H - 1) := by
+  classical
+  let i := canonicalBlockStartTime n m - H - 1
+  have hiMemIco : i ∈ Finset.Ico 0 (canonicalBlockStartTime n m - H) := by
+    simp only [Finset.mem_Ico, i]
+    omega
+  rw [canonicalSourceAgeDeficit, canonicalSourceAgeDeficit,
+    canonicalOldSourceClaimCarrier_succ_horizon_of_lt_start hH]
+  by_cases hiCarry : CarryTwoDebtAt n i
+  · have hiMem : i ∈ canonicalOldSourceClaimCarrier n H m := by
+      rw [canonicalOldSourceClaimCarrier, mem_carryTwoPositions_iff]
+      exact ⟨hiMemIco, hiCarry⟩
+    have hcard : 1 ≤ (canonicalOldSourceClaimCarrier n H m).card := by
+      exact Finset.one_le_card.mpr ⟨i, hiMem⟩
+    rw [Finset.card_erase_of_mem hiMem]
+    rw [Nat.cast_sub hcard]
+    change CarryTwoDebtAt n
+      (canonicalBlockStartTime n m - H - 1) at hiCarry
+    simp [canonicalCarryTwoIndicator, hiCarry]
+    ring
+  · have hiNotMem : i ∉ canonicalOldSourceClaimCarrier n H m := by
+      intro hi
+      exact hiCarry (mem_carryTwoPositions_iff.mp hi).2
+    rw [Finset.erase_eq_self.mpr hiNotMem]
+    change ¬ CarryTwoDebtAt n
+      (canonicalBlockStartTime n m - H - 1) at hiCarry
+    simp [canonicalCarryTwoIndicator, hiCarry]
+
+/-- Once the horizon reaches the block start, both adjacent horizon carriers
+are empty.  The deficit therefore remains the negative cumulative service. -/
+theorem canonicalSourceAgeDeficit_succ_horizon_eq_of_start_le
+    {n : OddNat} {H m : ℕ}
+    (hH : canonicalBlockStartTime n m ≤ H) :
+    canonicalSourceAgeDeficit n (H + 1) m =
+      canonicalSourceAgeDeficit n H m := by
+  rw [canonicalSourceAgeDeficit,
+    canonicalOldSourceClaimCarrier_eq_empty_of_start_le (by omega),
+    canonicalSourceAgeDeficit,
+    canonicalOldSourceClaimCarrier_eq_empty_of_start_le hH]
+
+/-! ## Exact crossing-window horizon shift -/
+
+/-- Sliding the mature crossing window one source time to the left exchanges
+exactly its old upper boundary for its new lower boundary. -/
+theorem canonicalSourceAgeHorizonCrossingClaims_succ_union_upper_eq
+    {n : OddNat} {H m : ℕ}
+    (hH : H < canonicalBlockStartTime n m) :
+    canonicalSourceAgeHorizonCrossingClaims n (H + 1) m ∪
+        carryTwoPositions n
+          {canonicalBlockStartTime n (m + 1) - H - 1} =
+      carryTwoPositions n
+          {canonicalBlockStartTime n m - H - 1} ∪
+        canonicalSourceAgeHorizonCrossingClaims n H m := by
+  classical
+  have hstep : canonicalBlockStartTime n m + 1 ≤
+      canonicalBlockStartTime n (m + 1) := by
+    rw [canonicalBlockStartTime_succ]
+    exact Nat.add_le_add_left (one_le_canonicalBlockLength n m) _
+  ext i
+  simp only [canonicalSourceAgeHorizonCrossingClaims,
+    mem_carryTwoPositions_iff, Finset.mem_Ico, Finset.mem_union,
+    Finset.mem_singleton]
+  constructor
+  · rintro (⟨⟨hiLo, hiHi⟩, hiCarry⟩ | ⟨rfl, hiCarry⟩)
+    · by_cases hiLower : i = canonicalBlockStartTime n m - H - 1
+      · exact Or.inl ⟨hiLower, hiCarry⟩
+      · exact Or.inr ⟨⟨by omega, by omega⟩, hiCarry⟩
+    · exact Or.inr ⟨⟨by omega, by omega⟩, hiCarry⟩
+  · rintro (⟨rfl, hiCarry⟩ | ⟨⟨hiLo, hiHi⟩, hiCarry⟩)
+    · exact Or.inl ⟨⟨by omega, by omega⟩, hiCarry⟩
+    · by_cases hiUpper : i = canonicalBlockStartTime n (m + 1) - H - 1
+      · exact Or.inr ⟨hiUpper, hiCarry⟩
+      · exact Or.inl ⟨⟨by omega, by omega⟩, hiCarry⟩
+
+private theorem disjoint_crossing_succ_carry_upper
+    {n : OddNat} {H m : ℕ}
+    (_hH : H < canonicalBlockStartTime n m) :
+    Disjoint (canonicalSourceAgeHorizonCrossingClaims n (H + 1) m)
+      (carryTwoPositions n
+        {canonicalBlockStartTime n (m + 1) - H - 1}) := by
+  classical
+  rw [Finset.disjoint_left]
+  intro i hiCross hiUpper
+  have hiRange := (mem_carryTwoPositions_iff.mp hiCross).1
+  have hiEq := (mem_carryTwoPositions_iff.mp hiUpper).1
+  simp only [Finset.mem_Ico] at hiRange
+  simp only [Finset.mem_singleton] at hiEq
+  omega
+
+private theorem disjoint_carry_lower_crossing
+    {n : OddNat} {H m : ℕ}
+    (hH : H < canonicalBlockStartTime n m) :
+    Disjoint
+      (carryTwoPositions n {canonicalBlockStartTime n m - H - 1})
+      (canonicalSourceAgeHorizonCrossingClaims n H m) := by
+  classical
+  rw [Finset.disjoint_left]
+  intro i hiLower hiCross
+  have hiEq := (mem_carryTwoPositions_iff.mp hiLower).1
+  have hiRange := (mem_carryTwoPositions_iff.mp hiCross).1
+  simp only [Finset.mem_singleton] at hiEq
+  simp only [Finset.mem_Ico] at hiRange
+  omega
+
+/-- Exact signed cardinal law for a one-step mature horizon shift. -/
+theorem int_card_crossing_succ_horizon_sub_card_crossing
+    {n : OddNat} {H m : ℕ}
+    (hH : H < canonicalBlockStartTime n m) :
+    ((canonicalSourceAgeHorizonCrossingClaims n (H + 1) m).card : ℤ) -
+        (canonicalSourceAgeHorizonCrossingClaims n H m).card =
+      canonicalCarryTwoIndicator n
+          (canonicalBlockStartTime n m - H - 1) -
+        canonicalCarryTwoIndicator n
+          (canonicalBlockStartTime n (m + 1) - H - 1) := by
+  have hcarrier :=
+    canonicalSourceAgeHorizonCrossingClaims_succ_union_upper_eq hH
+  have hcard := congrArg Finset.card hcarrier
+  rw [Finset.card_union_of_disjoint (disjoint_crossing_succ_carry_upper hH),
+    Finset.card_union_of_disjoint (disjoint_carry_lower_crossing hH),
+    card_carryTwoPositions_singleton,
+    card_carryTwoPositions_singleton] at hcard
+  have hcardInt :
+      ((canonicalSourceAgeHorizonCrossingClaims n (H + 1) m).card : ℤ) +
+          canonicalCarryTwoIndicator n
+            (canonicalBlockStartTime n (m + 1) - H - 1) =
+        canonicalCarryTwoIndicator n
+            (canonicalBlockStartTime n m - H - 1) +
+          (canonicalSourceAgeHorizonCrossingClaims n H m).card := by
+    exact_mod_cast hcard
+  omega
+
+/-- Actual service is independent of the age horizon, so the frontier's
+horizon derivative is exactly the same two-boundary exchange. -/
+theorem canonicalSourceAgeFrontierIncrement_succ_horizon_sub
+    {n : OddNat} {H m : ℕ}
+    (hH : H < canonicalBlockStartTime n m) :
+    canonicalSourceAgeFrontierIncrement n (H + 1) m -
+        canonicalSourceAgeFrontierIncrement n H m =
+      canonicalCarryTwoIndicator n
+          (canonicalBlockStartTime n m - H - 1) -
+        canonicalCarryTwoIndicator n
+          (canonicalBlockStartTime n (m + 1) - H - 1) := by
+  unfold canonicalSourceAgeFrontierIncrement
+  calc
+    ((canonicalSourceAgeHorizonCrossingClaims n (H + 1) m).card : ℤ) -
+          canonicalQueueConsumed n m -
+        (((canonicalSourceAgeHorizonCrossingClaims n H m).card : ℤ) -
+          canonicalQueueConsumed n m) =
+        ((canonicalSourceAgeHorizonCrossingClaims n (H + 1) m).card : ℤ) -
+          (canonicalSourceAgeHorizonCrossingClaims n H m).card := by ring
+    _ = _ := int_card_crossing_succ_horizon_sub_card_crossing hH
+
+/-! ## Horizon-one block decomposition -/
+
+/-- At positive source time, the age-one crossing carrier consists of the
+predecessor source and the current block carrier with its final source
+removed. -/
+theorem canonicalSourceAgeHorizonCrossingClaims_one_eq
+    {n : OddNat} {m : ℕ}
+    (hstart : 0 < canonicalBlockStartTime n m) :
+    canonicalSourceAgeHorizonCrossingClaims n 1 m =
+      carryTwoPositions n {canonicalBlockStartTime n m - 1} ∪
+        (canonicalBlockClaimSourceCarrier n m).erase
+          (canonicalBlockStartTime n (m + 1) - 1) := by
+  classical
+  have hstep : canonicalBlockStartTime n m + 1 ≤
+      canonicalBlockStartTime n (m + 1) := by
+    rw [canonicalBlockStartTime_succ]
+    exact Nat.add_le_add_left (one_le_canonicalBlockLength n m) _
+  ext i
+  simp only [canonicalSourceAgeHorizonCrossingClaims,
+    canonicalBlockClaimSourceCarrier, mem_carryTwoPositions_iff,
+    Finset.mem_Ico, Finset.mem_union, Finset.mem_singleton,
+    Finset.mem_erase]
+  constructor
+  · rintro ⟨⟨hiLo, hiHi⟩, hiCarry⟩
+    by_cases hiPred : i = canonicalBlockStartTime n m - 1
+    · exact Or.inl ⟨hiPred, hiCarry⟩
+    · exact Or.inr ⟨by omega, ⟨⟨by omega, by omega⟩, hiCarry⟩⟩
+  · rintro (⟨rfl, hiCarry⟩ | ⟨hiFinal, ⟨⟨hiLo, hiHi⟩, hiCarry⟩⟩)
+    · exact ⟨⟨by omega, by omega⟩, hiCarry⟩
+    · exact ⟨⟨by omega, by omega⟩, hiCarry⟩
+
+private theorem disjoint_predecessor_erased_block
+    {n : OddNat} {m : ℕ}
+    (hstart : 0 < canonicalBlockStartTime n m) :
+    Disjoint (carryTwoPositions n {canonicalBlockStartTime n m - 1})
+      ((canonicalBlockClaimSourceCarrier n m).erase
+        (canonicalBlockStartTime n (m + 1) - 1)) := by
+  classical
+  rw [Finset.disjoint_left]
+  intro i hiPred hiBlock
+  have hiEq := (mem_carryTwoPositions_iff.mp hiPred).1
+  have hiRange := mem_canonicalBlockClaimSourceCarrier_interval
+    (Finset.mem_of_mem_erase hiBlock)
+  simp only [Finset.mem_singleton] at hiEq
+  have hiLo := (Finset.mem_Ico.mp hiRange).1
+  omega
+
+/-- Removing the final block source subtracts precisely its carry indicator. -/
+theorem card_erase_final_add_indicator_eq_blockClaimSourceCarrier
+    (n : OddNat) (m : ℕ) :
+    ((canonicalBlockClaimSourceCarrier n m).erase
+        (canonicalBlockStartTime n (m + 1) - 1)).card +
+      canonicalCarryTwoIndicator n
+        (canonicalBlockStartTime n (m + 1) - 1) =
+      (canonicalBlockClaimSourceCarrier n m).card := by
+  classical
+  let i := canonicalBlockStartTime n (m + 1) - 1
+  have hstep : canonicalBlockStartTime n m + 1 ≤
+      canonicalBlockStartTime n (m + 1) := by
+    rw [canonicalBlockStartTime_succ]
+    exact Nat.add_le_add_left (one_le_canonicalBlockLength n m) _
+  by_cases hiCarry : CarryTwoDebtAt n i
+  · have hiMem : i ∈ canonicalBlockClaimSourceCarrier n m := by
+      rw [canonicalBlockClaimSourceCarrier, mem_carryTwoPositions_iff]
+      exact ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hiCarry⟩
+    rw [Finset.card_erase_of_mem hiMem]
+    change CarryTwoDebtAt n
+      (canonicalBlockStartTime n (m + 1) - 1) at hiCarry
+    simp [canonicalCarryTwoIndicator, hiCarry]
+    have := Finset.one_le_card.mpr ⟨i, hiMem⟩
+    omega
+  · have hiNotMem : i ∉ canonicalBlockClaimSourceCarrier n m := by
+      intro hi
+      exact hiCarry (carryTwoDebtAt_of_mem_canonicalBlockClaimSourceCarrier hi)
+    rw [Finset.erase_eq_self.mpr hiNotMem]
+    change ¬ CarryTwoDebtAt n
+      (canonicalBlockStartTime n (m + 1) - 1) at hiCarry
+    simp [canonicalCarryTwoIndicator, hiCarry]
+
+/-- Exact cardinal form of the horizon-one predecessor/block/final split. -/
+theorem int_card_sourceAgeHorizonCrossingClaims_one
+    {n : OddNat} {m : ℕ}
+    (hstart : 0 < canonicalBlockStartTime n m) :
+    ((canonicalSourceAgeHorizonCrossingClaims n 1 m).card : ℤ) =
+      canonicalCarryTwoIndicator n (canonicalBlockStartTime n m - 1) +
+        canonicalQueueDemand n m -
+          canonicalCarryTwoIndicator n
+            (canonicalBlockStartTime n (m + 1) - 1) := by
+  have hcarrier := canonicalSourceAgeHorizonCrossingClaims_one_eq hstart
+  have hcard := congrArg Finset.card hcarrier
+  rw [Finset.card_union_of_disjoint
+      (disjoint_predecessor_erased_block hstart),
+    card_carryTwoPositions_singleton] at hcard
+  have hfinal := card_erase_final_add_indicator_eq_blockClaimSourceCarrier n m
+  rw [card_canonicalBlockClaimSourceCarrier] at hfinal
+  have hcardInt :
+      ((canonicalSourceAgeHorizonCrossingClaims n 1 m).card : ℤ) =
+        canonicalCarryTwoIndicator n (canonicalBlockStartTime n m - 1) +
+          (((canonicalBlockClaimSourceCarrier n m).erase
+            (canonicalBlockStartTime n (m + 1) - 1)).card : ℤ) := by
+    exact_mod_cast hcard
+  have hfinalInt :
+      (((canonicalBlockClaimSourceCarrier n m).erase
+          (canonicalBlockStartTime n (m + 1) - 1)).card : ℤ) +
+        canonicalCarryTwoIndicator n
+          (canonicalBlockStartTime n (m + 1) - 1) =
+        canonicalQueueDemand n m := by
+    exact_mod_cast hfinal
+  omega
+
+/-! ## Saturated horizon-one audit -/
+
+/-- Away from the origin boundary, a saturated block's horizon-one frontier
+is exactly the carry indicator of the predecessor source.  The two current
+claims contribute two, the final claim leaves the shifted window, and actual
+service consumes one. -/
+theorem CanonicalSaturatedBorderBlock.sourceAgeFrontierIncrement_one_eq_indicator
+    {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m)
+    (hstart : 0 < canonicalBlockStartTime n m) :
+    canonicalSourceAgeFrontierIncrement n 1 m =
+      canonicalCarryTwoIndicator n (canonicalBlockStartTime n m - 1) := by
+  have hfinalEq : canonicalBlockStartTime n (m + 1) - 1 =
+      paymentEndpointSeq n m := by
+    calc
+      canonicalBlockStartTime n (m + 1) - 1 =
+          canonicalBlockStartTime n m + canonicalBlockLength n m - 1 := by
+            rw [canonicalBlockStartTime_succ]
+      _ = paymentEndpointSeq n m :=
+        canonicalBlockStartTime_add_length_sub_one_eq_endpoint n m
+  have hendpointMem : paymentEndpointSeq n m ∈ canonicalPaymentBlock n m := by
+    rw [canonicalPaymentBlock_eq_sourceFiber]
+    exact endpoint_mem_orbitPaymentSourceFiberAt_of_nonempty
+      (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n m)
+  have hfinalCarry : CarryTwoDebtAt n
+      (canonicalBlockStartTime n (m + 1) - 1) := by
+    rw [hfinalEq]
+    exact h.carryTwo_of_mem hendpointMem
+  have hfinalIndicator : canonicalCarryTwoIndicator n
+      (canonicalBlockStartTime n (m + 1) - 1) = 1 :=
+    (canonicalCarryTwoIndicator_eq_one_iff n _).2 hfinalCarry
+  unfold canonicalSourceAgeFrontierIncrement
+  rw [int_card_sourceAgeHorizonCrossingClaims_one hstart,
+    hfinalIndicator, h.canonicalQueueConsumed_eq_one]
+  change (canonicalCarryTwoIndicator n (canonicalBlockStartTime n m - 1) : ℤ) +
+      (canonicalQueueDemand n m : ℤ) - 1 - 1 = _
+  rw [canonicalQueueDemand, h.2.1, h.length_eq_two]
+  ring
+
+/-- The origin is a genuine Nat-subtraction exception to the mature formula:
+the predecessor `start - 1` aliases source zero instead of lying outside the
+current block. -/
+theorem sourceAgeFrontierIncrement_one_fiftyNine_zero_eq_zero :
+    canonicalSourceAgeFrontierIncrement fiftyNineSaturatedOdd 1 0 = 0 := by
+  have hstart0 : canonicalBlockStartTime fiftyNineSaturatedOdd 0 = 0 := rfl
+  have hstart1 : canonicalBlockStartTime fiftyNineSaturatedOdd 1 = 2 := by
+    rw [canonicalBlockStartTime_succ, hstart0,
+      canonicalBlockLength_fiftyNine_zero]
+  have hcross : canonicalSourceAgeHorizonCrossingClaims
+      fiftyNineSaturatedOdd 1 0 = {0} := by
+    classical
+    ext i
+    rw [canonicalSourceAgeHorizonCrossingClaims,
+      mem_carryTwoPositions_iff]
+    simp only [hstart0, hstart1, Nat.zero_sub, Nat.reduceSub,
+      Finset.mem_Ico, Finset.mem_singleton]
+    constructor
+    · rintro ⟨⟨_, hi⟩, _⟩
+      omega
+    · intro hi
+      subst i
+      exact ⟨⟨by omega, by omega⟩, fiftyNine_carry_zero⟩
+  unfold canonicalSourceAgeFrontierIncrement
+  rw [hcross]
+  simp [canonicalSaturatedBorderBlock_fiftyNine_zero.canonicalQueueConsumed_eq_one]
+
+theorem canonicalCarryTwoIndicator_fiftyNine_origin_eq_one :
+    canonicalCarryTwoIndicator fiftyNineSaturatedOdd
+      (canonicalBlockStartTime fiftyNineSaturatedOdd 0 - 1) = 1 := by
+  rw [canonicalCarryTwoIndicator_eq_one_iff]
+  simpa using fiftyNine_carry_zero
+
+/-- Therefore the mature saturated `H = 1` formula cannot be extended across
+the origin without an explicit early-boundary correction. -/
+theorem not_saturated_frontier_one_eq_predecessor_indicator_without_start :
+    ¬ ∀ n m, CanonicalSaturatedBorderBlock n m →
+      canonicalSourceAgeFrontierIncrement n 1 m =
+        canonicalCarryTwoIndicator n (canonicalBlockStartTime n m - 1) := by
+  intro h
+  have hEq := h fiftyNineSaturatedOdd 0
+    canonicalSaturatedBorderBlock_fiftyNine_zero
+  rw [sourceAgeFrontierIncrement_one_fiftyNine_zero_eq_zero,
+    canonicalCarryTwoIndicator_fiftyNine_origin_eq_one] at hEq
+  omega
+
+/-! ## Origin-to-crossing block map -/
+
+/-- Every member of a canonical payment block lies in its exact half-open
+source-time interval. -/
+theorem mem_canonicalPaymentBlock_startTime_interval
+    {n : OddNat} {m i : ℕ} (hi : i ∈ canonicalPaymentBlock n m) :
+    i ∈ Finset.Ico (canonicalBlockStartTime n m)
+      (canonicalBlockStartTime n (m + 1)) := by
+  rw [canonicalPaymentBlock_eq_sourceFiber,
+    orbitPaymentSourceFiberAt_eq_Icc_universalPaymentBlockStart n
+      (paymentEndpointSeq n m)
+      (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n m)] at hi
+  have hiBounds := Finset.mem_Icc.mp hi
+  have hstart := canonicalBlockStartTime_eq_universalPaymentBlockStart n m
+  have hnext : canonicalBlockStartTime n (m + 1) =
+      paymentEndpointSeq n m + 1 := by
+    simp [canonicalBlockStartTime, canonicalEndpointBlockStart]
+  exact Finset.mem_Ico.mpr ⟨by simpa [hstart] using hiBounds.1,
+    by omega⟩
+
+/-- The unique canonical block containing source time `i + H`. -/
+noncomputable def canonicalAgeCrossingBlockOfSource
+    (n : OddNat) (H i : ℕ) : ℕ :=
+  Classical.choose (existsUnique_mem_canonicalPaymentBlock n (i + H))
+
+theorem shiftedSource_mem_canonicalAgeCrossingBlockOfSource
+    (n : OddNat) (H i : ℕ) :
+    i + H ∈ canonicalPaymentBlock n
+      (canonicalAgeCrossingBlockOfSource n H i) :=
+  (Classical.choose_spec
+    (existsUnique_mem_canonicalPaymentBlock n (i + H))).1
+
+/-- Subject to the exact non-underflow condition, a carry-two source belongs
+to the age-`H` crossing carrier of the block containing its shifted source
+time. -/
+theorem mem_crossingClaims_canonicalAgeCrossingBlockOfSource
+    {n : OddNat} {H i : ℕ} (hiCarry : CarryTwoDebtAt n i)
+    (hboundary : H ≤ canonicalBlockStartTime n
+      (canonicalAgeCrossingBlockOfSource n H i)) :
+    i ∈ canonicalSourceAgeHorizonCrossingClaims n H
+      (canonicalAgeCrossingBlockOfSource n H i) := by
+  let m := canonicalAgeCrossingBlockOfSource n H i
+  change H ≤ canonicalBlockStartTime n m at hboundary
+  have hiBlock : i + H ∈ canonicalPaymentBlock n m := by
+    exact shiftedSource_mem_canonicalAgeCrossingBlockOfSource n H i
+  have hiRange := Finset.mem_Ico.mp
+    (mem_canonicalPaymentBlock_startTime_interval hiBlock)
+  have hmono : canonicalBlockStartTime n m ≤
+      canonicalBlockStartTime n (m + 1) :=
+    canonicalBlockStartTime_mono n (by omega)
+  have hnextBoundary : H ≤ canonicalBlockStartTime n (m + 1) :=
+    hboundary.trans hmono
+  have hleftEq := Nat.sub_add_cancel hboundary
+  have hrightEq := Nat.sub_add_cancel hnextBoundary
+  change i ∈ canonicalSourceAgeHorizonCrossingClaims n H m
+  rw [canonicalSourceAgeHorizonCrossingClaims,
+    mem_carryTwoPositions_iff]
+  exact ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hiCarry⟩
+
+/-! ## Short-window frontier sums -/
+
+/-- Signed frontier flow through a consecutive finite block-index window. -/
+noncomputable def canonicalSourceAgeFrontierWindowSum
+    (n : OddNat) (H q L : ℕ) : ℤ :=
+  ∑ j ∈ Finset.range L, canonicalSourceAgeFrontierIncrement n H (q + j)
+
+/-- Every finite frontier window telescopes to the change in signed deficit. -/
+theorem canonicalSourceAgeFrontierWindowSum_eq_deficit_sub
+    (n : OddNat) (H q L : ℕ) :
+    canonicalSourceAgeFrontierWindowSum n H q L =
+      canonicalSourceAgeDeficit n H (q + L) -
+        canonicalSourceAgeDeficit n H q := by
+  induction L with
+  | zero => simp [canonicalSourceAgeFrontierWindowSum]
+  | succ L ih =>
+      rw [canonicalSourceAgeFrontierWindowSum, Finset.sum_range_succ]
+      change canonicalSourceAgeFrontierWindowSum n H q L +
+          canonicalSourceAgeFrontierIncrement n H (q + L) = _
+      have hq : q + (L + 1) = (q + L) + 1 := by omega
+      rw [ih, hq, canonicalSourceAgeDeficit_succ]
+      ring
+
+@[simp] theorem canonicalSourceAgeFrontierWindowSum_zero
+    (n : OddNat) (H q : ℕ) :
+    canonicalSourceAgeFrontierWindowSum n H q 0 = 0 := by
+  simp [canonicalSourceAgeFrontierWindowSum]
+
+@[simp] theorem canonicalSourceAgeFrontierWindowSum_one
+    (n : OddNat) (H q : ℕ) :
+    canonicalSourceAgeFrontierWindowSum n H q 1 =
+      canonicalSourceAgeFrontierIncrement n H q := by
+  simp [canonicalSourceAgeFrontierWindowSum]
+
+@[simp] theorem canonicalSourceAgeFrontierWindowSum_two
+    (n : OddNat) (H q : ℕ) :
+    canonicalSourceAgeFrontierWindowSum n H q 2 =
+      canonicalSourceAgeFrontierIncrement n H q +
+        canonicalSourceAgeFrontierIncrement n H (q + 1) := by
+  simp [canonicalSourceAgeFrontierWindowSum, Finset.sum_range_succ]
+
+/-- The shortest horizon-zero window at a saturated block has total `+1`. -/
+theorem CanonicalSaturatedBorderBlock.sourceAgeFrontierWindowSum_zero_one
+    {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m) :
+    canonicalSourceAgeFrontierWindowSum n 0 m 1 = 1 := by
+  rw [canonicalSourceAgeFrontierWindowSum_one,
+    h.sourceAgeFrontierIncrement_zero_eq_one]
+
+/-- At positive block start, the shortest horizon-one saturated window is
+exactly the predecessor carry indicator. -/
+theorem CanonicalSaturatedBorderBlock.sourceAgeFrontierWindowSum_one_one
+    {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m)
+    (hstart : 0 < canonicalBlockStartTime n m) :
+    canonicalSourceAgeFrontierWindowSum n 1 m 1 =
+      canonicalCarryTwoIndicator n (canonicalBlockStartTime n m - 1) := by
+  rw [canonicalSourceAgeFrontierWindowSum_one,
+    h.sourceAgeFrontierIncrement_one_eq_indicator hstart]
+
+/-! ## Saturated-successor actual-consumption bridge -/
+
+/-- Saturation leaves at least one queued claim for the successor, while every
+canonical successor offers at least one service slot.  Thus the successor's
+*actual* consumption is positive.  This conclusion uses queue conservation;
+it is not obtained by substituting endpoint capacity for actual service. -/
+theorem CanonicalSaturatedBorderBlock.successor_queueConsumed_pos
+    {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m) :
+    0 < canonicalQueueConsumed n (m + 1) := by
+  have hqueue : 1 ≤ canonicalOutstandingClaimQueueBeforeBlock n (m + 1) := by
+    rw [h.queueBeforeBlock_succ_eq_add_one]
+    omega
+  have havailable : 1 ≤
+      canonicalOutstandingClaimQueueBeforeBlock n (m + 1) +
+        canonicalQueueDemand n (m + 1) := by omega
+  have hservice : 1 ≤ canonicalQueueService n (m + 1) := by
+    unfold canonicalQueueService
+    rw [canonicalBlockCapacityCount_eq_terminalValuation]
+    exact one_le_canonicalBlockTerminalValuation n (m + 1)
+  unfold canonicalQueueConsumed
+  exact lt_of_lt_of_le Nat.zero_lt_one (le_min havailable hservice)
+
+/-- If the successor has strictly negative endpoint drift, its extra service
+slot is actually consumed, so the saturated `+1` is repaid within the exact
+two-block horizon-zero window.  Nonpositive drift is insufficient: zero drift
+can leave the two-block sum positive, as the bounded audit records. -/
+theorem
+    CanonicalSaturatedBorderBlock.sourceAgeFrontierWindowSum_zero_two_nonpos_of_successor_negative
+    {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m)
+    (hnegative : endpointAccountingTerm n (m + 1) < 0) :
+    canonicalSourceAgeFrontierWindowSum n 0 m 2 ≤ 0 := by
+  have hdrift := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount
+    n (m + 1)
+  change endpointAccountingTerm n (m + 1) =
+      (canonicalQueueDemand n (m + 1) : ℤ) -
+        canonicalQueueService n (m + 1) at hdrift
+  have hservice : canonicalQueueDemand n (m + 1) + 1 ≤
+      canonicalQueueService n (m + 1) := by omega
+  have hqueue : 1 ≤ canonicalOutstandingClaimQueueBeforeBlock n (m + 1) := by
+    rw [h.queueBeforeBlock_succ_eq_add_one]
+    omega
+  have havailable : canonicalQueueDemand n (m + 1) + 1 ≤
+      canonicalOutstandingClaimQueueBeforeBlock n (m + 1) +
+        canonicalQueueDemand n (m + 1) := by omega
+  have hconsumed : canonicalQueueDemand n (m + 1) + 1 ≤
+      canonicalQueueConsumed n (m + 1) := by
+    unfold canonicalQueueConsumed
+    exact le_min havailable hservice
+  rw [canonicalSourceAgeFrontierWindowSum_two,
+    h.sourceAgeFrontierIncrement_zero_eq_one,
+    canonicalSourceAgeFrontierIncrement_zero_eq_demand_sub_consumed]
+  omega
+
+/-!
+## Conditional challenge-facing boundary
+
+The positive route now has an exact public chain:
+
+1. externally construct a noncircular
+   `CanonicalFiniteSourceAgeFrontierPotentialCertificate n H Signature`;
+2. obtain all nonpositive frontier prefixes;
+3. obtain uniform actual source age `H`;
+4. obtain queue bound `H` and endpoint-width bound `bitWidth n + H`.
+
+This module does **not** construct such a signature/certificate or prove that
+some horizon `H` works.  The bounded audit is discovery evidence only.  The
+saturated-successor split supplies positive successor consumption, and its
+strictly-negative branch supplies a two-block repayment theorem, but the
+zero-drift and positive-pressure branches do not currently give the uniform
+window consumption lower bound required for the global certificate.
+-/
+
+end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-337.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-337.md
new file mode 100644
index 00000000..d07c990c
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-337.md
@@ -0,0 +1,183 @@
+# Petal / Collatz Implementation Report cp-337
+
+## Status
+
+`COMPLETE WITH EXPLICIT BOUNDARY`
+
+The source-age horizon arithmetic requested by cp-337 is now implemented in:
+
+- `DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeHorizon`
+- `python/Collatz/PetalBridge/source_age_frontier_audit.py`
+
+No `sorry` was added.  The public `FloatWindow` import surface includes the new
+Lean module.
+
+## Lean results
+
+### Concrete obstruction at horizon zero
+
+The bounded search found `(n,m) = (59,0)`, and Lean independently verifies:
+
+```text
+CanonicalSaturatedBorderBlock fiftyNineSaturatedOdd 0
+```
+
+Consequently the previously conditional obstruction is now unconditional:
+
+```text
+not_forall_sourceAgeFrontierIncrement_zero_nonpos
+```
+
+Thus horizon-zero pointwise nonpositivity is formally false.
+
+### Exact queue compatibility
+
+At `H = 0`, frontier flow is both:
+
+```text
+demand - actual consumed service
+queueBeforeBlock (m+1) - queueBeforeBlock m
+```
+
+A saturated block raises the queue by exactly one.
+
+### Finite-facing certificate
+
+`CanonicalFiniteSourceAgeFrontierPotentialCertificate` replaces the old
+all-time prefix assumption by a finite-state initial maximum:
+
+```text
+forall s : Signature, potential s <= potential (signature 0)
+```
+
+It forgets to the compatibility certificate and preserves the exact chain to
+uniform source age, queue bounds, and endpoint-width bounds.  Signature,
+transition, and potential remain externally supplied and cannot be defined
+from the target deficit without circularity.
+
+### Exact horizon derivative
+
+The carry indicator is connected to singleton carrier cardinality in both
+`Nat` and `Int` forms.  In the mature regime `H < blockStart m`:
+
+```text
+oldCarrier (H+1) m = erase (blockStart m - H - 1) (oldCarrier H m)
+
+deficit (H+1) m
+  = deficit H m - carryIndicator (blockStart m - H - 1)
+```
+
+The early cutoff regime is separate: both carriers are empty and the deficit
+is unchanged.
+
+For crossing flow, sliding the horizon exchanges exactly two boundaries:
+
+```text
+card crossing(H+1,m) - card crossing(H,m)
+  = indicator(blockStart m - H - 1)
+      - indicator(blockStart (m+1) - H - 1)
+```
+
+The same identity holds for frontier increments because actual consumption is
+independent of the horizon.
+
+### Horizon-one audit
+
+For positive block start, `crossing(1,m)` decomposes exactly into:
+
+```text
+predecessor source
+union
+current block claims with the final source erased
+```
+
+Hence a mature saturated block satisfies:
+
+```text
+frontierIncrement 1 m = indicator(blockStart m - 1)
+```
+
+The positivity hypothesis is necessary.  The checked root `59` proves that at
+the origin the frontier is zero while the Nat-subtracted predecessor indicator
+is one.  The unrestricted candidate is therefore formally false; this is a
+real Nat-boundary alias, not a proof artifact.
+
+### Origin-to-crossing assignment and window sums
+
+`canonicalAgeCrossingBlockOfSource n H i` uses the existing unique canonical
+block coverage of `i + H`.  Under the exact non-underflow condition, a
+carry-two source belongs to that block's age crossing carrier.
+
+Finite frontier windows telescope exactly:
+
+```text
+windowSum H q L = deficit H (q+L) - deficit H q
+```
+
+Length zero, one, and two interfaces are available.
+
+### New successor fact
+
+A saturated block leaves one queued claim.  Since every successor has at least
+one service slot, Lean proves:
+
+```text
+CanonicalSaturatedBorderBlock.successor_queueConsumed_pos
+```
+
+If successor endpoint drift is strictly negative, the extra service is
+actually consumed and the exact horizon-zero two-block window is nonpositive:
+
+```text
+sourceAgeFrontierWindowSum_zero_two_nonpos_of_successor_negative
+```
+
+This cannot currently be weakened to nonpositive successor drift.  Zero drift
+may consume only current demand and leave the preceding saturated unit unpaid.
+
+## Numerical discovery audit
+
+The deterministic audit covered odd roots through `4095`, at most `256`
+canonical blocks, horizons `0..4`, and window lengths `1..8`.
+
+| H | max increment | max prefix | saturated return range | two-block counterexample |
+| --- | ---: | ---: | --- | --- |
+| 0 | 6 at `(1819,1)` | 7 at `(1819,3)` | 2..9 | `(123,0): [1,0]` |
+| 1 | 5 at `(1819,1)` | 6 at `(1819,3)` | 1 | `(927,3): [0,1]` |
+| 2 | 6 at `(1819,1)` | 6 at `(1819,3)` | 1 | `(927,3): [0,1]` |
+| 3 | 5 at `(1819,1)` | 5 at `(1819,3)` | 1 | `(927,3): [0,1]` |
+| 4 | 6 at `(1915,4)` | 5 at `(1819,3)` | 1 | `(927,3): [0,1]` |
+
+These values are finite evidence only.  The `H=0`, root-123 pattern directly
+rejects the tempting claim that every saturated `+1` is repaid in two blocks.
+
+## Exact stopping boundary
+
+The conditional positive route is now explicit and intact:
+
+```text
+finite noncircular structural certificate for some H
+  -> every frontier prefix <= 0
+  -> uniform actual source age H
+  -> uniform queue bound H
+  -> endpoint-width bound bitWidth(n) + H
+```
+
+What remains absent is the first item: no structural signature/certificate and
+no successful universal horizon have been constructed.  The current successor
+grammar proves positive actual consumption and strict-negative two-block
+repayment, but its zero-drift and positive-pressure branches do not supply a
+uniform short-window actual-consumption lower bound.
+
+## Next implementation
+
+The next honest checkpoint should isolate the unresolved successor branches:
+
+1. characterize the zero-drift successor's exact retained queue unit;
+2. search for an actual-consumption lower bound in the positive-pressure
+   branch, without replacing consumption by capacity;
+3. formulate a finite window certificate only if both branches admit a common
+   noncircular potential or repayment invariant.
+
+If no common invariant appears, retain the present exact split and treat the
+root-123 zero-drift pattern as the obstruction witness.
diff --git a/python/Collatz/PetalBridge/source_age_frontier_audit.py b/python/Collatz/PetalBridge/source_age_frontier_audit.py
new file mode 100644
index 00000000..267e78cf
--- /dev/null
+++ b/python/Collatz/PetalBridge/source_age_frontier_audit.py
@@ -0,0 +1,157 @@
+#!/usr/bin/env python3
+"""cp-337 bounded discovery audit for canonical source-age frontier flow.
+
+The output is theorem-discovery evidence only.  It intentionally tracks actual
+scalar-queue consumption rather than endpoint capacity, and it never promotes
+a finite maximum or repayment lag to a universal claim.
+"""
+
+from __future__ import annotations
+
+import json
+from pathlib import Path
+
+
+ROOT_MAX = 4095
+BLOCK_LIMIT = 256
+HORIZONS = range(5)
+WINDOW_LENGTHS = range(1, 9)
+
+
+def v2(value: int) -> int:
+    assert value > 0
+    return (value & -value).bit_length() - 1
+
+
+def step(value: int) -> int:
+    raw = 3 * value + 1
+    return raw >> v2(raw)
+
+
+def carry_two(value: int) -> bool:
+    return (3 * value + 1) >> value.bit_length() == 2
+
+
+class Orbit:
+    def __init__(self, root: int) -> None:
+        self.states = [root]
+
+    def state(self, time: int) -> int:
+        while len(self.states) <= time:
+            self.states.append(step(self.states[-1]))
+        return self.states[time]
+
+    def target(self, time: int) -> int:
+        return time + v2(self.state(time) + 1) - 1
+
+
+def trace(root: int) -> list[dict[str, int | bool]]:
+    orbit = Orbit(root)
+    endpoint = orbit.target(0)
+    previous_endpoint = -1
+    queue = 0
+    blocks: list[dict[str, int | bool]] = []
+    for index in range(BLOCK_LIMIT):
+        start = previous_endpoint + 1
+        claims = sum(carry_two(orbit.state(i)) for i in range(start, endpoint + 1))
+        service = v2(3 * orbit.state(endpoint) + 1) - 1
+        consumed = min(queue + claims, service)
+        length = endpoint - start + 1
+        blocks.append(
+            {
+                "index": index,
+                "start": start,
+                "next_start": endpoint + 1,
+                "claims": claims,
+                "service": service,
+                "consumed": consumed,
+                "saturated": length == service + 1 and claims == length and service == 1,
+            }
+        )
+        queue = queue + claims - consumed
+        if orbit.state(endpoint) == 1:
+            break
+        previous_endpoint = endpoint
+        endpoint = orbit.target(endpoint + 1)
+    return blocks
+
+
+def frontier(orbit: Orbit, block: dict[str, int | bool], horizon: int) -> int:
+    low = max(0, int(block["start"]) - horizon)
+    high = max(0, int(block["next_start"]) - horizon)
+    arrivals = sum(carry_two(orbit.state(i)) for i in range(low, high))
+    return arrivals - int(block["consumed"])
+
+
+def main() -> None:
+    summary: dict[str, object] = {
+        "checkpoint": 337,
+        "root_max": ROOT_MAX,
+        "block_limit": BLOCK_LIMIT,
+        "horizons": list(HORIZONS),
+        "window_lengths": list(WINDOW_LENGTHS),
+        "results": {},
+    }
+    results: dict[str, object] = {}
+    for horizon in HORIZONS:
+        max_increment = (-10**9, None)
+        max_prefix = (-10**9, None)
+        max_window = {length: (-10**9, None) for length in WINDOW_LENGTHS}
+        saturated_patterns = []
+        shortest_returns = []
+        two_block_counterexample = None
+        for root in range(1, ROOT_MAX + 1, 2):
+            orbit = Orbit(root)
+            blocks = trace(root)
+            increments = [frontier(orbit, block, horizon) for block in blocks]
+            prefix = 0
+            for index, increment in enumerate(increments):
+                if increment > max_increment[0]:
+                    max_increment = (increment, [root, index])
+                prefix += increment
+                if prefix > max_prefix[0]:
+                    max_prefix = (prefix, [root, index])
+                for length in WINDOW_LENGTHS:
+                    if index + length <= len(increments):
+                        total = sum(increments[index : index + length])
+                        if total > max_window[length][0]:
+                            max_window[length] = (total, [root, index])
+                if bool(blocks[index]["saturated"]):
+                    pattern = increments[index : index + 8]
+                    saturated_patterns.append([root, index, pattern])
+                    running = 0
+                    return_length = None
+                    for offset, value in enumerate(increments[index:], start=1):
+                        running += value
+                        if running <= 0:
+                            return_length = offset
+                            break
+                    if return_length is not None:
+                        shortest_returns.append(return_length)
+                    if (
+                        two_block_counterexample is None
+                        and len(pattern) >= 2
+                        and sum(pattern[:2]) > 0
+                    ):
+                        two_block_counterexample = [root, index, pattern[:2]]
+        results[str(horizon)] = {
+            "maximum_frontier_increment": max_increment,
+            "maximum_prefix_frontier_sum": max_prefix,
+            "maximum_window_sums": {
+                str(length): value for length, value in max_window.items()
+            },
+            "saturated_blocks_observed": len(saturated_patterns),
+            "shortest_observed_return": min(shortest_returns, default=None),
+            "longest_observed_return": max(shortest_returns, default=None),
+            "two_block_nonpositive_counterexample": two_block_counterexample,
+            "first_saturated_patterns": saturated_patterns[:12],
+        }
+    summary["results"] = results
+    output = Path(__file__).with_name("results") / "source_age_frontier_audit_337.json"
+    output.parent.mkdir(parents=True, exist_ok=True)
+    output.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
+    print(json.dumps(summary, indent=2))
+
+
+if __name__ == "__main__":
+    main()
````
`````
