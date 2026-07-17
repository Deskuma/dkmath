# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalOwnedQueue, OldestFirstQueue

gch: b9364963ac6c329dfb07c148d13c03ae84f9a7c7

## Report

(30m17s)

Checkpoint 334 を完了しました。

- [CanonicalOwnedQueue.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalOwnedQueue.lean)  
  source identity を保持する再帰的 FIFO queue を実装。既存 scalar queue との cardinality が完全一致し、消費済み source が再登場しないことまで証明しました。
- [OldestFirstQueue.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/OldestFirstQueue.lean)  
  Collatz 非依存の FIFO API と、同一容量の他方策より古い source を隠せない minimax 性を実装しました。
- [RawLowSignatureObstruction.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/RawLowSignatureObstruction.lean)  
  top-two bits は旧 all-ones 反例を区別します。しかし `r = 1` では
  `55 → 83` と `39 → 59` が署名上の閉路を形成し、重み総和が `+1` になるため、この enriched signature にも大域的 bounded potential は存在しないことを Lean で証明しました。
- [report-petal-334.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-334.md)  
  正の source-age 路線と、否定された signature 路線を分離して記録しました。

確定した正の到達点は次です。

```text
uniform actual source-age bound H
  -> recent-source carrier membership
  -> uniform queue bound H
  -> endpoint-width bound bitWidth(n) + H
```

`H` の存在自体はまだ証明していません。

検証結果:

- `lake build DkMath`: 成功、`8648 jobs`
- 変更した FloatWindow ファイル: `sorry/admit` なし
- `git diff --check`: 成功

トップレベルログには別の既存研究モジュール由来の `sorry` 警告がありますが、今回の変更には含まれません。

## Review

(11m52s)

## cp-334 実装レビュー

## 結論

**全面採用。source ownership 層は正しく完成した。**

cp-334 は、cp-333 で残っていた意味上の穴を埋めた。

- 匿名の scalar queue を、実際の carry-two source time を保持する再帰的 FIFO queue として実現
- その cardinality が既存 scalar queue と完全一致
- 消費された source が後の queue に再登場しないことを証明
- actual source age から recent-source membership、queue bound、endpoint-width boundまで接続
- fixed-low signature の任意の coarsening を排除
- top-two-bit enrichment も、`55/39` の正の projected cycle によって排除

commit `b9364963…` と添付 diff は一致している。

実装上の欠陥は見つからなかった。

ただし、二つの意味境界は明記しておくべきじゃ。

第一に、owned queue が保持する source identity は本物だが、**どの capacity slot がどの source を払ったかという対応は、FIFO として選んだ combinatorial realization**である。Collatz 算術が特定の source-slot 対応を物理的に指定したわけではない。

第二に、`OldestFirstQueue` の minimax theorem は現在、一回の有限 carrier に対する局所比較である。時間をまたぐあらゆる work-conserving policy に対する大域最適性は、まだ明示 theorem になっていない。

---

## 1. Generic oldest-first queue

```lean
eraseOldestN c s
```

は有限 source set `s` から最小要素を最大 `c` 個削除する。

証明された cardinality は、

$$
|\operatorname{eraseOldestN}(c,s)|=|s|\mathbin{\dotminus}c
$$

消費 carrier は、

$$
\operatorname{consumedOldestN}(c,s)=s\setminus\operatorname{eraseOldestN}(c,s)
$$

であり、

$$
|\operatorname{consumedOldestN}(c,s)|=\min(c,|s|)
$$

となる。

さらに consumed と remainder は互いに素で、和集合が元の carrier を復元する。

FIFO の中心順序則も正しい。

$$
x\in\operatorname{Consumed},\ y\in\operatorname{Remainder}\Longrightarrow x\le y
$$

source time は小さいほど古いので、

> 消費された source は、残された全 source より古いか同時刻

となる。

---

## 2. Minimax theorem の正確な意味

```lean
exists_le_of_card_eq_card_eraseOldestN
```

は、FIFO remainder と同じ cardinality を持つ任意の別 remainder `t` に対して、

$$
\forall y\in R_{\mathrm{FIFO}},\ \exists x\in t,\ x\le y
$$

を証明している。

特に FIFO remainder が非空なら、その最小要素 $y_{\min}$ を選ぶことで、

$$
\min(t)\le\min(R_{\mathrm{FIFO}})
$$

となる。

現在時刻を $B$ とすれば最大 source age は、

$$
B-\min(R)
$$

なので、FIFO は一回の finite service において最大 source age を最小化する。

report の、

> 同じ容量の別方策は、FIFO より全 claim を新しくできない

という解釈は正しい。

ただし、現 theorem は一回の同じ available carrier に対する比較じゃ。異なる過去の選択によって remainder が変わる recursive policy 全体の比較は、次に大域化する必要がある。

---

## 3. Block claim source carrier

新しい、

```lean
canonicalBlockClaimSourceCarrier n k
```

は、

$$
[b_k,b_{k+1})
$$

内の `CarryTwoDebtAt` source time そのものじゃ。

次が証明された。

$$
|\operatorname{BlockClaimSourceCarrier}(k)|=\operatorname{canonicalQueueDemand}(k)
$$

また、異なる canonical blocks の carrier は disjoint であり、全要素が本当に `CarryTwoDebtAt` を満たす。

これで queue arrival は、

```text
Fin demand
```

ではなく、

```text
source time を identity とする actual claim carrier
```

になった。

---

## 4. Recursive owned queue

中心定義は、

```lean
ownedQueue 0 = ∅

ownedQueue (k + 1) =
  eraseOldestN
    (service k)
    (ownedQueue k ∪ blockClaimCarrier k)
```

じゃ。

これは重要な時間的一貫性を持つ。

各 endpoint で過去全体を再 matching していない。

前 block から実際に残った source set に、新 block の source を追加し、その場の service だけを適用している。

cp-323 の unordered complement のように、window を延長するたび matching が組み替わる問題はない。

---

## 5. Temporal support

owned queue に残る source $i$ は必ず、

$$
i<b_k
$$

を満たす。

さらに全要素が `CarryTwoDebtAt n i` を維持する。

旧 outstanding claims と新 block claims は、

$$
\operatorname{OldQueue}_k\cap\operatorname{NewClaims}_k=\varnothing
$$

である。

これは、

- old source は $b_k$ より前
- new source は $b_k$ 以上

という実 source-time separationから従っている。

---

## 6. 消費と再登場禁止

block $k$ では、

$$
\operatorname{Consumed}*k\sqcup\operatorname{Queue}*{k+1}=\operatorname{Available}_k
$$

が exact に成立する。

さらに、一度 block $k$ で消費された source $i$ は、任意の $m>k$ に対して、

$$
i\notin\operatorname{Queue}_m
$$

となる。

これは source identity を持つ queue を作った最大の成果の一つじゃ。

scalar queue では表現不能だった、

> 同じ claim を二度払わない

という ownership invariant が実装された。

### 一段先の補強

現在の theorem は「後の outstanding queue に現れない」までじゃ。

次には、

```lean
i ∉ canonicalOwnedAvailableClaimsAtBlock n m

i ∉ canonicalOwnedConsumedClaimsAtBlock n m
```

も証明できる。

これにより consumed source が、

- 後の queue
- 後の arrival
- 後の consumed carrier

のどこにも再登場しない完全な no-reuse theorem になる。

---

## 7. Scalar queue との exact agreement

最重要 theorem は、

```lean
card_canonicalOwnedOutstandingClaimsBeforeBlock
```

じゃ。

$$
|\operatorname{OwnedQueue}_k|=Q_k^{\mathrm{before}}
$$

が全 $k$ について証明された。

消費 carrier も、

$$
|\operatorname{OwnedConsumed}_k|=\operatorname{canonicalQueueConsumed}(k)
$$

となる。

したがって、この owned queue は scalar queue と似た別理論ではない。

> **既存 scalar reflected queue の source-preserving realization**

である。

ここは全面採用でよい。

---

## 8. 「actual」の意味境界

owned claim の source time は actual orbit source じゃ。

しかし capacity slot と source claim の pairing 自体は oldest-first として選ばれている。

従って、

```text
actual source identity
```

は正しいが、

```text
算術が指定した唯一の actual payment matching
```

と読んではならない。

現在証明されたのは、

> 同じ demand/service cardinalityを持つ queue を、FIFO source assignmentとして矛盾なく実現できる

という存在と一貫性じゃ。

queue bound を証明するには十分である。

なぜなら scalar queue cardinalityは、どの claim identity を選んで消費しても変わらないからじゃ。

---

## 9. Genuine source-age bridge

actual age predicate は、

```lean
CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H
```

として、

$$
i\in\operatorname{OwnedQueue}_m\Longrightarrow b_m-i\le H
$$

を要求する。

この仮定から実 source membership、

$$
i\in\operatorname{RecentSourceClaimCarrier}(H,m)
$$

が証明された。

さらに exact cardinality agreement を通じて、

$$
\operatorname{ActualAgeBound}(H)\Longrightarrow Q_m\le|\operatorname{RecentClaims}(H,m)|\le H
$$

となる。

従って、

$$
Q_m\le H
$$

および、

$$
\operatorname{EndpointWidth}_m\le\operatorname{bitWidth}(n)+H
$$

まで閉じた。

これは cp-333 の匿名 cardinal coverage と actual source-age の間にあった意味の空白を、正しく埋めている。

### 時間単位の注意

ここでの source time は accelerated orbit `iterateT` の index じゃ。

raw Collatz map `C` の一ステップ数ではない。

最終 challenge へ進む際には、既存の cumulative raw-time bridge と接続する必要がある。

---

## 10. uniform $H$ はまだ未証明

今回証明された chain は、

$$
\exists H,\ \operatorname{ActualSourceAgeBound}(H)\Longrightarrow\operatorname{UniformQueueBound}\Longrightarrow\operatorname{UniformEndpointWidthBound}
$$

じゃ。

しかし、

$$
\exists H,\ \operatorname{CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost}(n,H)
$$

は証明されていない。

ここは report の境界が正しい。

cp-334 は Collatz の大域 bound を証明したのではない。

しかし missing theorem を、

```text
匿名 queue が有界
```

から、

```text
FIFO queue に残る actual source の年齢が一様有界
```

へ具体化した。

これは大きな前進じゃ。

---

## 11. 次に証明できる FIFO global normal form

ここから重要な一歩先が見える。

block $m$ までの全 historical claim carrier を、

$$
\operatorname{HistoricalClaims}_m=\{i\in[0,b_m)\mid\operatorname{CarryTwoDebtAt}(n,i)\}
$$

とする。

また累積 consumed carrier を、

$$
\operatorname{ConsumedPrefix}*m=\bigcup*{k<m}\operatorname{OwnedConsumed}_k
$$

とする。

次の exact partition が証明できるはずじゃ。

$$
\operatorname{HistoricalClaims}_m=\operatorname{ConsumedPrefix}_m\sqcup\operatorname{OwnedQueue}_m
$$

さらに FIFO なので、

$$
x\in\operatorname{ConsumedPrefix}_m,\ y\in\operatorname{OwnedQueue}_m\Longrightarrow x\le y
$$

となる。

つまり owned queue は historical claims の **upper tail、最も新しい部分**である。

これが閉じれば、owned queue は単なる recursive constructionではなく、

$$
\operatorname{OwnedQueue}*m=\operatorname{eraseOldestN}\left(\sum*{k<m}\operatorname{Consumed}_k,\operatorname{HistoricalClaims}_m\right)
$$

という global normal formを持つ。

---

## 12. Actual age と cardinal coverage は同値になり得る

cp-333 では cardinal coverage は actual age より弱いと評価した。

cp-334 の FIFO upper-tail 性を大域化すれば、逆向きも証明できる可能性が高い。

recent claim carrierを、

$$
R_{H,m}=\{i\in[b_m-H,b_m)\mid\operatorname{CarryTwoDebtAt}(n,i)\}
$$

とする。

FIFO queue が historical claims の最も新しい $Q_m$ 個なら、

$$
Q_m\le|R_{H,m}|
$$

である限り、残っている $Q_m$ 個は全て recent carrier内に入る。

従って、

$$
\operatorname{ActualSourceAgeBound}(H)\iff\operatorname{CardinalityCoverage}(H)
$$

まで強化できる見込みがある。

これは非常に価値が高い。

cardinality coverage が arbitrary rematching による弱い代用品ではなく、

> FIFO realization に対しては actual source age の exact scalar characterization

になるからじゃ。

---

## 13. Source-age deficit normal form

old claim carrierを、

$$
O_{H,m}=\{i\in[0,b_m-H)\mid\operatorname{CarryTwoDebtAt}(n,i)\}
$$

とする。

累積 consumed 数を $C_m$ とすると、FIFO age condition は、

$$
|O_{H,m}|\le C_m
$$

と同値になる。

また historical claims は old と recent に分割され、

$$
|\operatorname{HistoricalClaims}*m|=|O*{H,m}|+|R_{H,m}|
$$

scalar prefix balance は、

$$
Q_m+C_m=|\operatorname{HistoricalClaims}_m|
$$

じゃ。

従って整数 deficit として、

$$
|O_{H,m}|-C_m=Q_m-|R_{H,m}|
$$

が得られる。

これは次の主力 normal form になる。

```text
uniform actual age H
  iff
all source-age deficits are nonpositive
```

この deficit なら、既存 pressure / finite-transition / Hall APIとの接続を試せる。

---

# 14. Generic closed-signature obstruction

```lean
false_of_step_of_signature_eq_of_actualWeight_pos
```

が generic theorem として抽出された。

一つの realized edgeについて、

$$
\operatorname{signature}(b)=\operatorname{signature}(a)
$$

かつ、

$$
0<w(a,b)
$$

なら、bounded potential certificate は矛盾する。

この抽象化は正しい。

cp-333 の all-ones theorem がその corollary へ整理されたのもよい。

---

## 15. Factor-through obstruction

任意の有限 map、

$$
f:\operatorname{FixedLowRawSignature}(r)\to\Sigma
$$

に対して、

$$
\sigma(x)=f(\operatorname{fixedLowSig}(x))
$$

と factorする certificateも排除された。

これは単なる exact structure の否定より強い。

- 座標を削る
- tag をまとめる
- post-processする
- 複数状態をさらに同一視する

といった任意の coarsening は、失われた upper-boundary 情報を復元できない。

ただし strict refinement は対象外である。この境界も正しい。

---

# 16. Top-two-bit enrichment

`normalizedTopTwoBits` は正数の normalized leading two-bit wordじゃ。

all-ones witnessでは、

$$
\operatorname{topTwo}(x_r)=3
$$

$$
\operatorname{topTwo}(T(x_r))=2
$$

となる。

従って cp-333 の positive self-loop は、この座標を追加することで分離された。

ただしこれは absolute width ではない。

`normalizedTopTwoBits` は scale-invariant な上位形状だけを保持する。

幅そのもの、上位 zero boundary までの距離、減少 rank は保持しない。

---

## 17. `55/39` projected cycle

$r=1$ において、次が exact に証明された。

$$
\operatorname{sig}(T(55))=\operatorname{sig}(39)
$$

$$
\operatorname{sig}(T(39))=\operatorname{sig}(55)
$$

実状態では、

$$
55\mapsto83
$$

$$
39\mapsto59
$$

じゃ。

幅 weight は、

$$
w(55,83)=1
$$

$$
w(39,59)=0
$$

となる。

従って signature graph 上には、

$$
\sigma(55)\xrightarrow{+1}\sigma(39)\xrightarrow{0}\sigma(55)
$$

という total weight $+1$ の projected cycle がある。

potential inequalitiesを二本足すと、

$$
1\le\Phi(\sigma(39))-\Phi(\sigma(55))
$$

$$
0\le\Phi(\sigma(55))-\Phi(\sigma(39))
$$

となり矛盾する。実装もこの二本を `linarith` で閉じている。

### 重要な点

具体状態は同じ orbit cycleを形成する必要がない。

potential は concrete state ではなく signature に付いている。

従って、異なる orbit から得た realized edges でも、signature graph 上で閉じれば正当な obstruction になる。

この解釈は完全に正しい。

---

## 18. 現 theorem は $r=1$ だけ

現在の top-two-bit enriched obstruction theorem は、

```lean
FixedLowUpperBoundarySignature 1
```

に対するものじゃ。

従って直接確定したのは $r=1$ の排除である。

report もこの範囲を守っている。

ただし、この `55/39` cycle は symbolic familyへ一般化できる。

---

## 19. 全 $r\ge1$ へ一般化できる二状態族

次を置く。

$$
A_r=7\cdot2^{r+2}-1
$$

$$
B_r=5\cdot2^{r+2}-1
$$

$r=1$ では、

$$
A_1=55,\qquad B_1=39
$$

じゃ。

accelerated successors は、

$$
T(A_r)=21\cdot2^{r+1}-1
$$

$$
T(B_r)=15\cdot2^{r+1}-1
$$

さらに、

$$
T^2(A_r)=63\cdot2^r-1
$$

$$
T^2(B_r)=45\cdot2^r-1
$$

となる。

幅は、

$$
\operatorname{width}(A_r)=\operatorname{width}(B_r)=r+5
$$

$$
\operatorname{width}(T(A_r))=r+6,\qquad\operatorname{width}(T(B_r))=r+5
$$

$$
\operatorname{width}(T^2(A_r))=\operatorname{width}(T^2(B_r))=r+6
$$

従って edge weights は、

$$
w(A_r,T(A_r))=1
$$

$$
w(B_r,T(B_r))=0
$$

じゃ。

また全状態は low $r$ bits が all onesであり、height class・upper carry・growth flag・normalized top-two bitsを監査すると、

$$
\operatorname{sig}(T(A_r))=\operatorname{sig}(B_r)
$$

$$
\operatorname{sig}(T(B_r))=\operatorname{sig}(A_r)
$$

となる。

したがって cp-334 の $r=1$ obstruction は、

> 任意の $r\ge1$ に対する symbolic positive two-cycle

へ強化できる可能性が高い。

これは次 checkpoint で優先して Lean に通す価値がある。

---

## 20. Challenge への現在地

正の route は現在、

```text
actual carry-two source carrier
→ recursive FIFO ownership
→ uniform actual source-age H                     [未証明]
→ uniform queue bound H
→ endpoint-width bound bitWidth(n) + H
```

じゃ。

否定 route は、

```text
fixed low signature
→ positive self-loop
→ 不可能

fixed low + normalized top-two
→ positive projected two-cycle
→ 不可能
```

まで進んだ。

cp-334 により、

- scalar quantity
- actual identity
- temporal consumption
- age

が初めて一つの chain になった。

これは DkMath Collatz 開発における明確な節目じゃ。

---

## 判定まとめ

### Generic FIFO carrier

**完成。**

### FIFO one-step minimax

**完成。**

### Recursive source-owned queue

**完成。**

### No-reappearance

**後の outstanding queue について完成。完全 no-reuse へ補強可能。**

### Scalar cardinality agreement

**完成。**

### Actual source-age bridge

**完成。uniform $H$ の存在のみ未証明。**

### Global FIFO optimality

**未実装。次の主題。**

### Fixed-low factor obstruction

**完成。**

### Top-two enrichment

**旧 self-loop の分離は完成。**

### Enriched signature obstruction

**$r=1$ の正 projected two-cycleとして完成。**

### 全 $r$ への enriched obstruction

**未実装だが明確な symbolic family が見える。**

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge FloatWindow branch after
report-petal-334.

The cp-334 implementation is accepted.

It completed:

    a recursive source-owned FIFO realization of the scalar queue;

    exact scalar cardinality agreement;

    genuine actual-source age semantics;

    factor-through obstruction for every coarsening of the fixed-low
    signature;

    a positive projected two-cycle rejecting the first top-two-bit enrichment
    at r = 1.

The next checkpoint must globalize the FIFO normal form and strengthen the
top-two-bit obstruction from one numerical depth to every r >= 1.

# Stage A — historical claim and consumed-prefix carriers

Define:

    canonicalHistoricalClaimSourceCarrier n m :=
      carryTwoPositions n
        (Ico 0 (canonicalBlockStartTime n m)).

Define the cumulative consumed carrier before block m as the union of:

    canonicalOwnedConsumedClaimsAtBlock n k

for k in range m.

Prove:

    consumed carriers from distinct blocks are disjoint;

    no consumed source belongs to any later available carrier;

    no consumed source belongs to any later consumed carrier;

    card cumulative consumed carrier
      =
    sum k in range m, canonicalQueueConsumed n k.

# Stage B — exact historical partition

Prove:

    canonicalHistoricalClaimSourceCarrier n m
      =
    cumulative consumed carrier before m
        union
      canonicalOwnedOutstandingClaimsBeforeBlock n m.

Prove the union is disjoint.

Recover the exact cardinal identity:

    historical claim count
      =
    cumulative consumed count + outstanding queue count.

Connect it to the existing scalar prefix balance.

# Stage C — global FIFO upper-tail theorem

Prove:

    for every source x in the cumulative consumed carrier
    and every source y in the outstanding owned queue,

      x <= y.

Then prove the global normal form:

    canonicalOwnedOutstandingClaimsBeforeBlock n m
      =
    eraseOldestN
      (sum k in range m, canonicalQueueConsumed n k)
      (canonicalHistoricalClaimSourceCarrier n m).

Do not replace the actual consumed count by total service; unused service does
not carry forward.

# Stage D — threshold theorem for oldest-first remainder

In `OldestFirstQueue.lean`, prove a generic threshold theorem.

For a finite source set s, cutoff t, and remainder:

    r = eraseOldestN c s,

prove:

    r subset {x in s | t <= x}
      <->
    card r <= card {x in s | t <= x}.

The reverse implication uses that `r` is the newest upper tail of `s`.

Handle the empty remainder explicitly.

# Stage E — actual age/cardinality equivalence

Use Stage D with:

    s = canonicalHistoricalClaimSourceCarrier n m;
    t = canonicalBlockStartTime n m - H.

Prove:

    CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H
      <->
    CanonicalOutstandingQueueCardCoveredByRecentSourceClaims n H.

Thus the cp-333 scalar cardinal condition becomes an exact characterization of
actual FIFO source age, not merely a one-way consequence.

Do not infer that such an H exists.

# Stage F — source-age deficit normal form

Define:

    canonicalOldSourceClaimCarrier n H m

as carry-two sources in:

    Ico 0 (canonicalBlockStartTime n m - H).

Define cumulative consumed count before m.

Prove the exact signed identity:

    oldSourceClaims.card - cumulativeConsumed
      =
    queueBeforeBlock m - recentSourceClaims.card.

Use Int for the signed statement.

Conclude:

    actual FIFO source age <= H at block m
      <->
    source-age deficit <= 0.

This should become the primary scalar target for the positive route.

# Stage G — oldest-source and maximum-age API

For a nonempty owned queue, define:

    canonicalOldestOutstandingSource n m

using `Finset.min'`.

Define:

    canonicalOwnedMaximumSourceAge n m.

Prove:

    uniform actual source age H
      <->
    every maximum source age is <= H.

Provide the empty-queue value explicitly, preferably zero.

# Stage H — global policy optimality

Define an admissible remainder at block m as any finite subset of historical
claims with cardinality equal to the scalar outstanding queue.

Prove:

    the FIFO owned queue maximizes the minimum retained source;

equivalently:

    the FIFO owned queue minimizes maximum source age.

This comparison does not need to model an entire alternative recursive policy;
every work-conserving policy produces such an admissible remainder.

State carefully that FIFO is optimal among source assignments realizing the
same scalar queue.

# Stage I — eventual consumption consequence

Assume a uniform actual source-age bound H.

Prove that every source claim born at time i is absent from the owned queue
once:

    canonicalBlockStartTime n m > i + H.

Using `one_le_canonicalBlockLength`, derive an explicit block-index repayment
lag, for example a safe bound of H + 2 blocks after the claim's birth block.

Construct the corresponding source-to-consumption-block witness.

# Stage J — generic projected two-cycle obstruction

In `FiniteSignedTransition.lean`, prove a reusable theorem:

    two realized edges
      a -> a'
      b -> b'

with:

    signature a' = signature b;
    signature b' = signature a;
    0 < actualWeight a a' + actualWeight b b';

contradict every sound bounded-potential certificate covering both edges.

Reprove the `55/39` theorem as a corollary.

# Stage K — symbolic top-two cycle for every low depth

For r >= 1 define odd states:

    upperCycleA r := 7 * 2^(r + 2) - 1;
    upperCycleB r := 5 * 2^(r + 2) - 1.

Prove:

    T (upperCycleA r) = 21 * 2^(r + 1) - 1;
    T (upperCycleB r) = 15 * 2^(r + 1) - 1;

    T (T (upperCycleA r)) = 63 * 2^r - 1;
    T (T (upperCycleB r)) = 45 * 2^r - 1.

Prove the exact widths:

    width A = r + 5;
    width B = r + 5;
    width (T A) = r + 6;
    width (T B) = r + 5;
    width (T² A) = r + 6;
    width (T² B) = r + 6.

Then prove:

    fixedLowUpperBoundarySignature r (T A)
      =
    fixedLowUpperBoundarySignature r B;

    fixedLowUpperBoundarySignature r (T B)
      =
    fixedLowUpperBoundarySignature r A.

The two edge weights are respectively +1 and 0.

Conclude for every r >= 1:

    no global bounded-potential certificate using
    `FixedLowUpperBoundarySignature r` can cover all accelerated odd edges.

Keep the cp-334 r = 1 witnesses as concrete regressions.

# Stage L — factor-through enriched obstruction

Generalize Stage K to every finite coarsening:

    f : FixedLowUpperBoundarySignature r -> Signature.

Prove that no certificate whose signature factors through f can cover every raw
odd transition.

Do not claim the result for a strict refinement carrying additional upper
information.

# Stage M — next upper-prefix audit

After Stage K closes, audit normalized top-three bits.

First test the exact projected three-cycle at r = 1:

    89 -> 67;
    39 -> 59;
    59 -> 89.

The signed width weights are:

    0, 0, +1.

Check the required signature identifications under:

    fixed low r = 1
      +
    normalized top-three bits.

Promote this to a theorem only after proving every coordinate exactly.

Do not infer a theorem for arbitrary upper-prefix length from one cycle.

# Stopping rule

Stop at the first genuine obstruction among:

    cumulative consumed carriers are not pairwise disjoint;

    the historical partition fails;

    recursive FIFO is not the global newest upper tail;

    cardinal coverage is not equivalent to FIFO source age;

    source-age deficit identity fails;

    global FIFO minimax cannot be derived;

    the symbolic A_r / B_r signature equalities fail;

    the enriched top-two cycle does not generalize to all r;

    the top-three experimental cycle does not close.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-335.md
```

cp-334 で queue は「数」から「履歴を持つ source 集合」になった。

次は、その集合が全履歴の**最も新しい尾部そのもの**であることを証明し、source age を exact deficit theorem へ変える番じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
index aa888a16..9a4ed104 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
@@ -31,6 +31,7 @@ import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmortizedResource
 import DkMath.Collatz.PetalBridge.FloatWindow.BoundedRepaymentLag
 import DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition
 import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceTimeLag
+import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalOwnedQueue
 import DkMath.Collatz.PetalBridge.FloatWindow.RawLowSignatureObstruction
 
 #print "file: DkMath.Collatz.PetalBridge.FloatWindow"
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalOwnedQueue.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalOwnedQueue.lean
new file mode 100644
index 00000000..6e892176
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalOwnedQueue.lean
@@ -0,0 +1,230 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceTimeLag
+import DkMath.Collatz.PetalBridge.FloatWindow.OldestFirstQueue
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalOwnedQueue"
+
+namespace DkMath.Collatz
+
+/-!
+# Canonical source-owned queue
+
+The scalar reflected queue records only a claim count.  This module realizes
+that count by a temporally coherent finite set whose elements remain the
+original carry-two source times.  Service always removes the oldest available
+source identities; no endpoint is independently rematched against history.
+-/
+
+/-- Source-bearing outstanding claims immediately before canonical block `k`. -/
+noncomputable def canonicalOwnedOutstandingClaimsBeforeBlock
+    (n : OddNat) : ℕ → Finset ℕ
+  | 0 => ∅
+  | k + 1 =>
+      eraseOldestN (canonicalQueueService n k)
+        (canonicalOwnedOutstandingClaimsBeforeBlock n k ∪
+          canonicalBlockClaimSourceCarrier n k)
+
+/-- All source-bearing claims available for service at canonical block `k`. -/
+noncomputable def canonicalOwnedAvailableClaimsAtBlock
+    (n : OddNat) (k : ℕ) : Finset ℕ :=
+  canonicalOwnedOutstandingClaimsBeforeBlock n k ∪
+    canonicalBlockClaimSourceCarrier n k
+
+/-- Source identities consumed by oldest-first service at block `k`. -/
+noncomputable def canonicalOwnedConsumedClaimsAtBlock
+    (n : OddNat) (k : ℕ) : Finset ℕ :=
+  consumedOldestN (canonicalQueueService n k)
+    (canonicalOwnedAvailableClaimsAtBlock n k)
+
+@[simp] theorem canonicalOwnedOutstandingClaimsBeforeBlock_zero
+    (n : OddNat) :
+    canonicalOwnedOutstandingClaimsBeforeBlock n 0 = ∅ := rfl
+
+@[simp] theorem canonicalOwnedOutstandingClaimsBeforeBlock_succ
+    (n : OddNat) (k : ℕ) :
+    canonicalOwnedOutstandingClaimsBeforeBlock n (k + 1) =
+      eraseOldestN (canonicalQueueService n k)
+        (canonicalOwnedAvailableClaimsAtBlock n k) := rfl
+
+/-- Every outstanding identity predates the block at which it is observed. -/
+theorem mem_canonicalOwnedOutstandingClaimsBeforeBlock_lt_start
+    {n : OddNat} {k i : ℕ}
+    (hi : i ∈ canonicalOwnedOutstandingClaimsBeforeBlock n k) :
+    i < canonicalBlockStartTime n k := by
+  induction k with
+  | zero => simp at hi
+  | succ k ih =>
+      have hiAvail := mem_of_mem_eraseOldestN hi
+      rcases Finset.mem_union.mp hiAvail with hiOld | hiNew
+      · have hlt := ih hiOld
+        rw [canonicalBlockStartTime_succ]
+        have hlen := one_le_canonicalBlockLength n k
+        omega
+      · exact (Finset.mem_Ico.mp
+          (mem_canonicalBlockClaimSourceCarrier_interval hiNew)).2
+
+/-- Every outstanding identity remains an actual carry-two source. -/
+theorem carryTwoDebtAt_of_mem_canonicalOwnedOutstandingClaimsBeforeBlock
+    {n : OddNat} {k i : ℕ}
+    (hi : i ∈ canonicalOwnedOutstandingClaimsBeforeBlock n k) :
+    CarryTwoDebtAt n i := by
+  induction k with
+  | zero => simp at hi
+  | succ k ih =>
+      have hiAvail := mem_of_mem_eraseOldestN hi
+      rcases Finset.mem_union.mp hiAvail with hiOld | hiNew
+      · exact ih hiOld
+      · exact carryTwoDebtAt_of_mem_canonicalBlockClaimSourceCarrier hiNew
+
+/-- Old outstanding identities and current-block arrivals cannot coincide. -/
+theorem disjoint_canonicalOwnedOutstandingClaimsBeforeBlock_blockCarrier
+    (n : OddNat) (k : ℕ) :
+    Disjoint (canonicalOwnedOutstandingClaimsBeforeBlock n k)
+      (canonicalBlockClaimSourceCarrier n k) := by
+  classical
+  apply Finset.disjoint_left.mpr
+  intro i hiOld hiNew
+  have hlt := mem_canonicalOwnedOutstandingClaimsBeforeBlock_lt_start hiOld
+  have hle := (Finset.mem_Ico.mp
+    (mem_canonicalBlockClaimSourceCarrier_interval hiNew)).1
+  omega
+
+/-- Consumed identities and the successor outstanding queue are disjoint. -/
+theorem disjoint_canonicalOwnedConsumedClaimsAtBlock_nextOutstanding
+    (n : OddNat) (k : ℕ) :
+    Disjoint (canonicalOwnedConsumedClaimsAtBlock n k)
+      (canonicalOwnedOutstandingClaimsBeforeBlock n (k + 1)) := by
+  exact disjoint_consumedOldestN_eraseOldestN _ _
+
+/-- Consumption plus the next queue reconstructs all claims available now. -/
+theorem canonicalOwnedConsumed_union_nextOutstanding
+    (n : OddNat) (k : ℕ) :
+    canonicalOwnedConsumedClaimsAtBlock n k ∪
+        canonicalOwnedOutstandingClaimsBeforeBlock n (k + 1) =
+      canonicalOwnedAvailableClaimsAtBlock n k := by
+  exact consumedOldestN_union_eraseOldestN _ _
+
+/-- Every source consumed at block `k` predates the next block start. -/
+theorem mem_canonicalOwnedConsumedClaimsAtBlock_lt_next_start
+    {n : OddNat} {k i : ℕ}
+    (hi : i ∈ canonicalOwnedConsumedClaimsAtBlock n k) :
+    i < canonicalBlockStartTime n (k + 1) := by
+  have hiAvail := (Finset.mem_sdiff.mp hi).1
+  rcases Finset.mem_union.mp hiAvail with hiOld | hiNew
+  · have hlt := mem_canonicalOwnedOutstandingClaimsBeforeBlock_lt_start hiOld
+    rw [canonicalBlockStartTime_succ]
+    have hlen := one_le_canonicalBlockLength n k
+    omega
+  · exact (Finset.mem_Ico.mp
+      (mem_canonicalBlockClaimSourceCarrier_interval hiNew)).2
+
+/-- Once consumed, a source identity never reappears in a later owned queue. -/
+theorem not_mem_canonicalOwnedOutstandingClaimsBeforeBlock_of_consumed
+    {n : OddNat} {k m i : ℕ}
+    (hi : i ∈ canonicalOwnedConsumedClaimsAtBlock n k)
+    (hkm : k < m) :
+    i ∉ canonicalOwnedOutstandingClaimsBeforeBlock n m := by
+  induction m generalizing k i with
+  | zero => omega
+  | succ m ih =>
+      intro hiLater
+      have hiAvail := mem_of_mem_eraseOldestN hiLater
+      by_cases hkmEq : k = m
+      · subst k
+        exact (Finset.disjoint_left.mp
+          (disjoint_canonicalOwnedConsumedClaimsAtBlock_nextOutstanding n m)
+          hi hiLater)
+      · have hkmLt : k < m := by omega
+        rcases Finset.mem_union.mp hiAvail with hiOld | hiNew
+        · exact ih hi hkmLt hiOld
+        · have hiLt :=
+            mem_canonicalOwnedConsumedClaimsAtBlock_lt_next_start hi
+          have hstart := canonicalBlockStartTime_mono n
+            (show k + 1 ≤ m by omega)
+          have hiGe := (Finset.mem_Ico.mp
+            (mem_canonicalBlockClaimSourceCarrier_interval hiNew)).1
+          omega
+
+/-- The source-bearing outstanding queue realizes the existing scalar queue. -/
+theorem card_canonicalOwnedOutstandingClaimsBeforeBlock
+    (n : OddNat) (k : ℕ) :
+    (canonicalOwnedOutstandingClaimsBeforeBlock n k).card =
+      canonicalOutstandingClaimQueueBeforeBlock n k := by
+  induction k with
+  | zero => simp
+  | succ k ih =>
+      rw [canonicalOwnedOutstandingClaimsBeforeBlock_succ,
+        card_eraseOldestN, canonicalOwnedAvailableClaimsAtBlock,
+        Finset.card_union_of_disjoint
+          (disjoint_canonicalOwnedOutstandingClaimsBeforeBlock_blockCarrier n k),
+        ih, card_canonicalBlockClaimSourceCarrier,
+        canonicalOutstandingClaimQueueBeforeBlock_succ]
+      have hbalance := canonicalOutstandingClaimQueue_add_consumed n k
+      unfold canonicalQueueConsumed at hbalance
+      omega
+
+/-- Owned oldest-first consumption realizes the scalar consumed count. -/
+theorem card_canonicalOwnedConsumedClaimsAtBlock
+    (n : OddNat) (k : ℕ) :
+    (canonicalOwnedConsumedClaimsAtBlock n k).card =
+      canonicalQueueConsumed n k := by
+  rw [canonicalOwnedConsumedClaimsAtBlock, card_consumedOldestN,
+    canonicalOwnedAvailableClaimsAtBlock,
+    Finset.card_union_of_disjoint
+      (disjoint_canonicalOwnedOutstandingClaimsBeforeBlock_blockCarrier n k),
+    card_canonicalOwnedOutstandingClaimsBeforeBlock,
+    card_canonicalBlockClaimSourceCarrier]
+  unfold canonicalQueueConsumed
+  exact Nat.min_comm _ _
+
+/-- Uniform actual source age for every identity retained by the owned queue. -/
+def CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost
+    (n : OddNat) (H : ℕ) : Prop :=
+  ∀ m i, i ∈ canonicalOwnedOutstandingClaimsBeforeBlock n m →
+    canonicalBlockStartTime n m - i ≤ H
+
+/-- An owned source satisfying the age bound belongs to the actual recent
+source carrier, not merely to a set of the same cardinality. -/
+theorem CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost.mem_recentCarrier
+    {n : OddNat} {H m i : ℕ}
+    (h : CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H)
+    (hi : i ∈ canonicalOwnedOutstandingClaimsBeforeBlock n m) :
+    i ∈ canonicalRecentSourceClaimCarrier n H m := by
+  rw [canonicalRecentSourceClaimCarrier, mem_carryTwoPositions_iff]
+  have hlt := mem_canonicalOwnedOutstandingClaimsBeforeBlock_lt_start hi
+  have hage := h m i hi
+  have hcarry :=
+    carryTwoDebtAt_of_mem_canonicalOwnedOutstandingClaimsBeforeBlock hi
+  exact ⟨Finset.mem_Ico.mpr ⟨by omega, hlt⟩, hcarry⟩
+
+/-- A genuine owned-queue age theorem implies the cp-333 scalar cardinal
+coverage predicate. -/
+theorem CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost.to_cardCovered
+    {n : OddNat} {H : ℕ}
+    (h : CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H) :
+    CanonicalOutstandingQueueCardCoveredByRecentSourceClaims n H := by
+  intro m
+  rw [← card_canonicalOwnedOutstandingClaimsBeforeBlock]
+  exact Finset.card_le_card fun i hi => h.mem_recentCarrier hi
+
+/-- Actual uniform source age gives a uniform scalar queue bound. -/
+theorem CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost.to_queueUniformUpperBound
+    {n : OddNat} {H : ℕ}
+    (h : CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H) :
+    CanonicalOutstandingClaimQueueUniformUpperBound n H :=
+  h.to_cardCovered.to_queueUniformUpperBound
+
+/-- Actual uniform source age reaches the endpoint-width theorem.  No theorem
+in this module asserts that such a uniform `H` exists. -/
+theorem CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost.to_endpointWidthUniformUpperBound
+    {n : OddNat} {H : ℕ}
+    (h : CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H) :
+    CanonicalEndpointWidthUniformUpperBound n (bitWidth n.1 + H) :=
+  h.to_cardCovered.to_endpointWidthUniformUpperBound
+
+end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalSourceTimeLag.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalSourceTimeLag.lean
index 9f848969..f6f62714 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalSourceTimeLag.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalSourceTimeLag.lean
@@ -80,6 +80,13 @@ theorem recentCanonicalDemand_le_sourceTimeSpan
 
 /-! ## Exact block/source carrier identification -/
 
+/-- Carry-two claim sources born in canonical block `k`. -/
+noncomputable def canonicalBlockClaimSourceCarrier
+    (n : OddNat) (k : ℕ) : Finset ℕ :=
+  carryTwoPositions n
+    (Finset.Ico (canonicalBlockStartTime n k)
+      (canonicalBlockStartTime n (k + 1)))
+
 /-- The claims born in one canonical block are exactly its carry-two source
 addresses in the half-open block interval. -/
 theorem canonicalQueueDemand_eq_carryTwoPositions_block_card
@@ -117,6 +124,27 @@ theorem canonicalQueueDemand_eq_carryTwoPositions_block_card
       have := (Finset.mem_Ico.mp hi).2
       omega⟩, hcarry⟩
 
+/-- Named-carrier form of the exact one-block demand identity. -/
+theorem card_canonicalBlockClaimSourceCarrier
+    (n : OddNat) (k : ℕ) :
+    (canonicalBlockClaimSourceCarrier n k).card = canonicalQueueDemand n k := by
+  exact (canonicalQueueDemand_eq_carryTwoPositions_block_card n k).symm
+
+/-- Every block claim source lies in that exact half-open source-time block. -/
+theorem mem_canonicalBlockClaimSourceCarrier_interval
+    {n : OddNat} {k i : ℕ}
+    (hi : i ∈ canonicalBlockClaimSourceCarrier n k) :
+    i ∈ Finset.Ico (canonicalBlockStartTime n k)
+      (canonicalBlockStartTime n (k + 1)) := by
+  exact (mem_carryTwoPositions_iff.mp hi).1
+
+/-- Every member of a block claim carrier is an actual carry-two debt source. -/
+theorem carryTwoDebtAt_of_mem_canonicalBlockClaimSourceCarrier
+    {n : OddNat} {k i : ℕ}
+    (hi : i ∈ canonicalBlockClaimSourceCarrier n k) :
+    CarryTwoDebtAt n i := by
+  exact (mem_carryTwoPositions_iff.mp hi).2
+
 /-- Block-start time is monotone in the block index. -/
 theorem canonicalBlockStartTime_mono
     (n : OddNat) {q m : ℕ} (hqm : q ≤ m) :
@@ -127,6 +155,28 @@ theorem canonicalBlockStartTime_mono
     sum_canonicalBlockLength_range_eq_startTime] at hsplit
   omega
 
+/-- Distinct canonical blocks have disjoint source-address carriers. -/
+theorem disjoint_canonicalBlockClaimSourceCarrier
+    (n : OddNat) {j k : ℕ} (hjk : j ≠ k) :
+    Disjoint (canonicalBlockClaimSourceCarrier n j)
+      (canonicalBlockClaimSourceCarrier n k) := by
+  classical
+  have disj_of_lt : ∀ {a b : ℕ}, a < b →
+      Disjoint (canonicalBlockClaimSourceCarrier n a)
+        (canonicalBlockClaimSourceCarrier n b) := by
+    intro a b hab
+    apply Finset.disjoint_left.mpr
+    intro i hia hib
+    have ha := Finset.mem_Ico.mp
+      (mem_canonicalBlockClaimSourceCarrier_interval hia)
+    have hb := Finset.mem_Ico.mp
+      (mem_canonicalBlockClaimSourceCarrier_interval hib)
+    have hstart := canonicalBlockStartTime_mono n (show a + 1 ≤ b by omega)
+    omega
+  rcases lt_or_gt_of_ne hjk with hjklt | hkjlt
+  · exact disj_of_lt hjklt
+  · exact (disj_of_lt hkjlt).symm
+
 /-- Prefix demand is exactly the number of carry-two source addresses before
 the corresponding block start. -/
 theorem sum_canonicalQueueDemand_range_eq_sourceClaims_card
@@ -279,13 +329,20 @@ theorem card_canonicalRecentSourceClaimCarrier_le
     canonicalRecentSourceClaimCarrier n 0 m = ∅ := by
   simp [canonicalRecentSourceClaimCarrier, carryTwoPositions]
 
-/-- Conditional source-age surface: every outstanding anonymous claim is
-represented by a carry-two source in the preceding `H` orbit times. -/
-def CanonicalOutstandingQueueCoveredByRecentSourceClaims
+/--
+Scalar cardinality coverage: the anonymous outstanding queue count is no
+larger than the number of recent carry-two sources.  This does not identify
+queue elements with those sources and is not itself a claim-age theorem.
+-/
+def CanonicalOutstandingQueueCardCoveredByRecentSourceClaims
     (n : OddNat) (H : ℕ) : Prop :=
   ∀ m, canonicalOutstandingClaimQueueBeforeBlock n m ≤
     (canonicalRecentSourceClaimCarrier n H m).card
 
+/-- Compatibility alias for the cp-333 cardinality-only predicate. -/
+abbrev CanonicalOutstandingQueueCoveredByRecentSourceClaims :=
+  CanonicalOutstandingQueueCardCoveredByRecentSourceClaims
+
 /-- Uniform source-age coverage immediately bounds every pre-block queue. -/
 theorem canonicalQueueBeforeBlock_le_of_recentSourceClaims
     {n : OddNat} {H : ℕ}
@@ -309,6 +366,20 @@ theorem CanonicalOutstandingQueueCoveredByRecentSourceClaims.to_endpointWidthUni
     CanonicalEndpointWidthUniformUpperBound n (bitWidth n.1 + H) :=
   h.to_queueUniformUpperBound.to_endpointWidthUniformUpperBound
 
+/-- Precisely named cardinal-coverage route to the scalar queue bound. -/
+theorem CanonicalOutstandingQueueCardCoveredByRecentSourceClaims.to_queueUniformUpperBound
+    {n : OddNat} {H : ℕ}
+    (h : CanonicalOutstandingQueueCardCoveredByRecentSourceClaims n H) :
+    CanonicalOutstandingClaimQueueUniformUpperBound n H :=
+  CanonicalOutstandingQueueCoveredByRecentSourceClaims.to_queueUniformUpperBound h
+
+/-- Precisely named cardinal-coverage route to the endpoint-width bound. -/
+theorem CanonicalOutstandingQueueCardCoveredByRecentSourceClaims.to_endpointWidthUniformUpperBound
+    {n : OddNat} {H : ℕ}
+    (h : CanonicalOutstandingQueueCardCoveredByRecentSourceClaims n H) :
+    CanonicalEndpointWidthUniformUpperBound n (bitWidth n.1 + H) :=
+  h.to_queueUniformUpperBound.to_endpointWidthUniformUpperBound
+
 /-!
 No uniform `H` is asserted here.  The remaining input on this route is exactly
 a theorem that every outstanding canonical claim has source age at most one
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean
index bbe77bcf..76d3b47f 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean
@@ -79,6 +79,21 @@ namespace RelationalFiniteSignedTransitionPotentialCertificate
 
 variable {State Signature : Type*} [Fintype Signature]
 
+/-- A single related edge with positive concrete weight cannot close at one
+projected signature under a sound bounded-potential certificate. -/
+theorem false_of_step_of_signature_eq_of_actualWeight_pos
+    (C : RelationalFiniteSignedTransitionPotentialCertificate State Signature)
+    {a b : State}
+    (hstep : C.Step a b)
+    (hclosed : C.signature b = C.signature a)
+    (hpos : 0 < C.actualWeight a b) : False := by
+  have hactual := C.actual_le_projected a b hstep
+  have hprojected := C.projected_le_potential_diff
+    (C.signature a) (C.signature b)
+  rw [hclosed] at hactual hprojected
+  simp only [sub_self] at hprojected
+  omega
+
 /-- Concrete signed weight along a finite sequence of related transitions. -/
 def pathWeight
     (C : RelationalFiniteSignedTransitionPotentialCertificate State Signature)
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/OldestFirstQueue.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/OldestFirstQueue.lean
new file mode 100644
index 00000000..a28f41e4
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/OldestFirstQueue.lean
@@ -0,0 +1,159 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import Mathlib
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.OldestFirstQueue"
+
+namespace DkMath
+
+/-!
+# Oldest-first finite source queue
+
+This module is independent of the Collatz definitions.  Natural numbers are
+source times, so deleting the least member implements FIFO service while
+preserving the identity of every unconsumed source.
+-/
+
+/-- Remove at most `c` least source times from a finite source set. -/
+noncomputable def eraseOldestN : ℕ → Finset ℕ → Finset ℕ
+  | 0, s => s
+  | c + 1, s =>
+      if h : s.Nonempty then
+        eraseOldestN c (s.erase (s.min' h))
+      else
+        ∅
+
+@[simp] theorem eraseOldestN_zero (s : Finset ℕ) :
+    eraseOldestN 0 s = s := rfl
+
+/-- Oldest-first service never introduces a source. -/
+theorem eraseOldestN_subset (c : ℕ) (s : Finset ℕ) :
+    eraseOldestN c s ⊆ s := by
+  induction c generalizing s with
+  | zero => simp
+  | succ c ih =>
+      rw [eraseOldestN]
+      split_ifs with h
+      · exact (ih _).trans (Finset.erase_subset _ _)
+      · simp
+
+/-- Oldest-first service removes exactly `min c s.card` sources. -/
+theorem card_eraseOldestN (c : ℕ) (s : Finset ℕ) :
+    (eraseOldestN c s).card = s.card - c := by
+  induction c generalizing s with
+  | zero => simp
+  | succ c ih =>
+      rw [eraseOldestN]
+      split_ifs with h
+      · rw [ih, Finset.card_erase_of_mem (Finset.min'_mem s h)]
+        omega
+      · have hs : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
+        simp [hs]
+
+/-- Sources removed by oldest-first service. -/
+noncomputable def consumedOldestN (c : ℕ) (s : Finset ℕ) : Finset ℕ :=
+  s \ eraseOldestN c s
+
+/-- The consumed source count is exactly the available service. -/
+theorem card_consumedOldestN (c : ℕ) (s : Finset ℕ) :
+    (consumedOldestN c s).card = min c s.card := by
+  rw [consumedOldestN,
+    Finset.card_sdiff_of_subset (eraseOldestN_subset c s),
+    card_eraseOldestN]
+  by_cases h : c ≤ s.card
+  · rw [min_eq_left h]
+    omega
+  · rw [min_eq_right (by omega)]
+    omega
+
+/-- Consumed and remaining source identities are disjoint. -/
+theorem disjoint_consumedOldestN_eraseOldestN (c : ℕ) (s : Finset ℕ) :
+    Disjoint (consumedOldestN c s) (eraseOldestN c s) := by
+  exact Finset.sdiff_disjoint
+
+/-- Consumed and remaining sources reconstruct the original source set. -/
+theorem consumedOldestN_union_eraseOldestN (c : ℕ) (s : Finset ℕ) :
+    consumedOldestN c s ∪ eraseOldestN c s = s := by
+  unfold consumedOldestN
+  exact Finset.sdiff_union_of_subset (eraseOldestN_subset c s)
+
+/-- Membership in the remainder implies membership in the original set. -/
+theorem mem_of_mem_eraseOldestN
+    {c : ℕ} {s : Finset ℕ} {i : ℕ}
+    (hi : i ∈ eraseOldestN c s) : i ∈ s :=
+  eraseOldestN_subset c s hi
+
+/--
+FIFO invariant: every consumed source is no later than every source left in
+the oldest-first remainder.
+-/
+theorem consumedOldestN_le_eraseOldestN
+    (c : ℕ) (s : Finset ℕ) :
+    ∀ x ∈ consumedOldestN c s, ∀ y ∈ eraseOldestN c s, x ≤ y := by
+  induction c generalizing s with
+  | zero => simp [consumedOldestN]
+  | succ c ih =>
+      rw [eraseOldestN]
+      split_ifs with h
+      · let m := s.min' h
+        let s' := s.erase m
+        intro x hx y hy
+        have hyS' : y ∈ s' := eraseOldestN_subset c s' hy
+        have hyS : y ∈ s := Finset.mem_of_mem_erase hyS'
+        by_cases hxm : x = m
+        · subst x
+          exact Finset.min'_le s y hyS
+        · have hxS : x ∈ s := (Finset.mem_sdiff.mp hx).1
+          have hxS' : x ∈ s' := Finset.mem_erase.mpr ⟨hxm, hxS⟩
+          have hxNotOld : x ∉ eraseOldestN (c + 1) s :=
+            (Finset.mem_sdiff.mp hx).2
+          have hxNot : x ∉ eraseOldestN c s' := by
+            simpa [eraseOldestN, h, s', m] using hxNotOld
+          exact ih s' x (Finset.mem_sdiff.mpr ⟨hxS', hxNot⟩) y hy
+      · have hs : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
+        simp [hs, consumedOldestN]
+
+/-!
+## Policy comparison
+
+Source time increases toward the present, so a smaller source is older.  The
+following finite comparison is the useful minimax form of FIFO optimality: no
+other subset of the original carrier with the same remainder cardinality can
+make every retained source newer than one retained FIFO source.
+-/
+
+/-- Every same-cardinality alternative remainder contains a source no newer
+than each chosen source in the oldest-first remainder. -/
+theorem exists_le_of_card_eq_card_eraseOldestN
+    {c : ℕ} {s t : Finset ℕ}
+    (ht : t ⊆ s)
+    (hcard : t.card = (eraseOldestN c s).card)
+    {y : ℕ} (hy : y ∈ eraseOldestN c s) :
+    ∃ x ∈ t, x ≤ y := by
+  by_contra hnone
+  push Not at hnone
+  have hsub : t ⊆ (eraseOldestN c s).erase y := by
+    intro x hx
+    have hxs : x ∈ s := ht hx
+    have hxUnion : x ∈ consumedOldestN c s ∪ eraseOldestN c s := by
+      rw [consumedOldestN_union_eraseOldestN]
+      exact hxs
+    rcases Finset.mem_union.mp hxUnion with hxConsumed | hxRemaining
+    · have hxy := consumedOldestN_le_eraseOldestN c s x hxConsumed y hy
+      exact False.elim ((Nat.not_lt_of_ge hxy) (hnone x hx))
+    · exact Finset.mem_erase.mpr ⟨by
+        exact ne_of_gt (hnone x hx), hxRemaining⟩
+  have hle := Finset.card_le_card hsub
+  have hlt := Finset.card_erase_lt_of_mem hy
+  have : (eraseOldestN c s).card < (eraseOldestN c s).card := by
+    calc
+      (eraseOldestN c s).card = t.card := hcard.symm
+      _ ≤ ((eraseOldestN c s).erase y).card := hle
+      _ < (eraseOldestN c s).card := hlt
+  exact (Nat.lt_irrefl _ this)
+
+end DkMath
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/RawLowSignatureObstruction.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/RawLowSignatureObstruction.lean
index fe2fe960..56d372a2 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/RawLowSignatureObstruction.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/RawLowSignatureObstruction.lean
@@ -5,6 +5,7 @@ Authors: D. and Wise Wolf.
 -/
 
 import DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition
+import DkMath.Collatz.PetalBridge.FloatWindow.DyadicFloat
 
 #print "file: DkMath.Collatz.PetalBridge.FloatWindow.RawLowSignatureObstruction"
 
@@ -321,6 +322,268 @@ theorem rawSignedWidthWeight_rawAllOnesWitness_eq_one
   rw [bitWidth_T_rawAllOnesWitness_eq_add_one]
   omega
 
+/-- Every realized accelerated odd edge increases binary width by at most one. -/
+theorem rawSignedWidthWeight_T_le_one (x : OddNat) :
+    rawSignedWidthWeight x (T x) ≤ 1 := by
+  unfold rawSignedWidthWeight
+  have hbalance := bitWidth_T_add_height_eq_bitWidth_add_upperCarry x
+  have hheight := s_pos x
+  have hxpos : 0 < x.1 := by
+    have hodd := x.2
+    omega
+  have hcarry : stateUpperCarry x.1 ≤ 2 :=
+    upperCarry3n1_le_two_of_lt_pow (lt_pow_bitWidth hxpos)
+  omega
+
+/-! ## First strict upper-boundary enrichment -/
+
+/-- The exact normalized leading two-bit word of a positive natural. -/
+def normalizedTopTwoBits (x : ℕ) : ℕ :=
+  upperPrefix 2 x
+
+/-- The all-ones source has normalized leading word `11₂`. -/
+theorem normalizedTopTwoBits_rawAllOnesWitness_eq_three
+    {r : ℕ} (hr : 1 ≤ r) :
+    normalizedTopTwoBits (rawAllOnesWitness r).1 = 3 := by
+  unfold normalizedTopTwoBits upperPrefix
+  rw [bitWidth_rawAllOnesWitness r]
+  have hp : 0 < 2 ^ r := pow_pos (by norm_num) _
+  have hpow : 2 ^ (r + 2) = 4 * 2 ^ r := by
+    rw [pow_add]
+    norm_num [Nat.mul_comm]
+  rw [show r + 2 - 2 = r by omega]
+  apply Nat.div_eq_of_lt_le
+  · rw [rawAllOnesWitness_val, hpow]
+    omega
+  · rw [rawAllOnesWitness_val, hpow]
+    omega
+
+/-- Its height-one target has normalized leading word `10₂`. -/
+theorem normalizedTopTwoBits_T_rawAllOnesWitness_eq_two
+    {r : ℕ} (hr : 1 ≤ r) :
+    normalizedTopTwoBits (T (rawAllOnesWitness r)).1 = 2 := by
+  unfold normalizedTopTwoBits upperPrefix
+  rw [bitWidth_T_rawAllOnesWitness]
+  have hp : 0 < 2 ^ (r + 1) := pow_pos (by norm_num) _
+  rw [show r + 3 - 2 = r + 1 by omega]
+  apply Nat.div_eq_of_lt_le
+  · rw [T_rawAllOnesWitness_val]
+    unfold rawAllOnesFirstTargetValue
+    omega
+  · rw [T_rawAllOnesWitness_val]
+    unfold rawAllOnesFirstTargetValue
+    omega
+
+/-- The normalized upper-boundary coordinate separates the cp-333 positive
+closed edge.  This alone does not construct a bounded potential. -/
+theorem normalizedTopTwoBits_T_rawAllOnesWitness_ne
+    {r : ℕ} (hr : 1 ≤ r) :
+    normalizedTopTwoBits (T (rawAllOnesWitness r)).1 ≠
+      normalizedTopTwoBits (rawAllOnesWitness r).1 := by
+  rw [normalizedTopTwoBits_T_rawAllOnesWitness_eq_two hr,
+    normalizedTopTwoBits_rawAllOnesWitness_eq_three hr]
+  norm_num
+
+/-- First experimental strict refinement: fixed low data plus normalized
+leading two bits.  Reduction modulo four is representational only; the
+normalized observation is already a two-bit word on positive states. -/
+structure FixedLowUpperBoundarySignature (r : ℕ) where
+  low : FixedLowRawSignature r
+  topTwo : Fin 4
+  deriving DecidableEq, Fintype
+
+/-- Enriched finite observation used for the next projected-graph audit. -/
+noncomputable def fixedLowUpperBoundarySignature
+    (r : ℕ) (x : OddNat) : FixedLowUpperBoundarySignature r where
+  low := fixedLowRawSignature r x
+  topTwo := ⟨normalizedTopTwoBits x.1 % 4, Nat.mod_lt _ (by norm_num)⟩
+
+/-- The strict enrichment removes the known all-ones positive self-loop. -/
+theorem fixedLowUpperBoundarySignature_T_rawAllOnesWitness_ne
+    {r : ℕ} (hr : 1 ≤ r) :
+    fixedLowUpperBoundarySignature r (T (rawAllOnesWitness r)) ≠
+      fixedLowUpperBoundarySignature r (rawAllOnesWitness r) := by
+  intro h
+  have htop := congrArg FixedLowUpperBoundarySignature.topTwo h
+  apply congrArg Fin.val at htop
+  change normalizedTopTwoBits (T (rawAllOnesWitness r)).1 % 4 =
+    normalizedTopTwoBits (rawAllOnesWitness r).1 % 4 at htop
+  rw [normalizedTopTwoBits_T_rawAllOnesWitness_eq_two hr,
+    normalizedTopTwoBits_rawAllOnesWitness_eq_three hr] at htop
+  norm_num at htop
+
+/-! ## Enriched projected-cycle audit
+
+The old all-ones self-loop is gone, but the realized signature-pair graph still
+has a positive cycle.  Its two edges come from different concrete states,
+which is sufficient: projected potential inequalities are attached to
+signature pairs and therefore telescope around the projected cycle.
+-/
+
+/-- An odd state congruent to three modulo four has exact height one. -/
+theorem s_eq_one_of_mod_four_eq_three
+    {x : OddNat} (hmod : x.1 % 4 = 3) :
+    s x = 1 := by
+  have hpos := s_pos x
+  have hnot : ¬ 2 ≤ s x := by
+    intro htwo
+    have hdiv : 4 ∣ 3 * x.1 + 1 :=
+      (rawHeightLabel_two_le_iff_four_dvd_threeNPlusOne x.1).mp htwo
+    have hone :=
+      (odd_four_dvd_three_mul_add_one_iff_mod_four_eq_one x.2).mp hdiv
+    omega
+  omega
+
+/-- First exact edge identification in the enriched `r = 1` cycle audit. -/
+theorem fixedLowUpperBoundarySignature_T_55_eq_39 :
+    fixedLowUpperBoundarySignature 1 (T (⟨55, by decide⟩ : OddNat)) =
+      fixedLowUpperBoundarySignature 1 (⟨39, by decide⟩ : OddNat) := by
+  let a : OddNat := ⟨55, by decide⟩
+  let b : OddNat := ⟨83, by decide⟩
+  let c : OddNat := ⟨39, by decide⟩
+  let d : OddNat := ⟨125, by decide⟩
+  let e : OddNat := ⟨59, by decide⟩
+  have ha : s a = 1 := s_eq_one_of_mod_four_eq_three (by decide)
+  have hb : s b = 1 := s_eq_one_of_mod_four_eq_three (by decide)
+  have hc : s c = 1 := s_eq_one_of_mod_four_eq_three (by decide)
+  have hTa : T a = b := by
+    apply Subtype.ext
+    rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one a ha]
+    norm_num [a, b]
+  have hTb : T b = d := by
+    apply Subtype.ext
+    rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one b hb]
+    norm_num [b, d]
+  have hTc : T c = e := by
+    apply Subtype.ext
+    rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one c hc]
+    norm_num [c, e]
+  have wb : bitWidth b.1 = 7 := by decide
+  have wc : bitWidth c.1 = 6 := by decide
+  have wd : bitWidth d.1 = 7 := by decide
+  have we : bitWidth e.1 = 6 := by decide
+  change fixedLowUpperBoundarySignature 1 (T a) =
+    fixedLowUpperBoundarySignature 1 c
+  rw [hTa]
+  unfold fixedLowUpperBoundarySignature
+  congr 1
+  · unfold fixedLowRawSignature
+    congr 1
+    · apply Fin.ext
+      norm_num [b, c]
+    · apply Fin.ext
+      norm_num [stateUpperCarry, upperCarry3n1, wb, wc, b, c]
+    · simp [hb, hc]
+    · simp [hTb, hTc, wb, wc, wd, we]
+  · apply Fin.ext
+    norm_num [normalizedTopTwoBits, upperPrefix, wb, wc, b, c]
+
+/-- Second exact edge identification closing the enriched `r = 1` cycle. -/
+theorem fixedLowUpperBoundarySignature_T_39_eq_55 :
+    fixedLowUpperBoundarySignature 1 (T (⟨39, by decide⟩ : OddNat)) =
+      fixedLowUpperBoundarySignature 1 (⟨55, by decide⟩ : OddNat) := by
+  let a : OddNat := ⟨39, by decide⟩
+  let b : OddNat := ⟨59, by decide⟩
+  let c : OddNat := ⟨55, by decide⟩
+  let d : OddNat := ⟨89, by decide⟩
+  let e : OddNat := ⟨83, by decide⟩
+  have ha : s a = 1 := s_eq_one_of_mod_four_eq_three (by decide)
+  have hb : s b = 1 := s_eq_one_of_mod_four_eq_three (by decide)
+  have hc : s c = 1 := s_eq_one_of_mod_four_eq_three (by decide)
+  have hTa : T a = b := by
+    apply Subtype.ext
+    rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one a ha]
+    norm_num [a, b]
+  have hTb : T b = d := by
+    apply Subtype.ext
+    rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one b hb]
+    norm_num [b, d]
+  have hTc : T c = e := by
+    apply Subtype.ext
+    rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one c hc]
+    norm_num [c, e]
+  have wb : bitWidth b.1 = 6 := by decide
+  have wc : bitWidth c.1 = 6 := by decide
+  have wd : bitWidth d.1 = 7 := by decide
+  have we : bitWidth e.1 = 7 := by decide
+  change fixedLowUpperBoundarySignature 1 (T a) =
+    fixedLowUpperBoundarySignature 1 c
+  rw [hTa]
+  unfold fixedLowUpperBoundarySignature
+  congr 1
+  · unfold fixedLowRawSignature
+    congr 1
+    · apply Fin.ext
+      norm_num [b, c]
+    · apply Fin.ext
+      norm_num [stateUpperCarry, upperCarry3n1, wb, wc, b, c]
+    · simp [hb, hc]
+    · simp [hTb, hTc, wb, wc, wd, we]
+  · apply Fin.ext
+    norm_num [normalizedTopTwoBits, upperPrefix, wb, wc, b, c]
+
+/-- The `55 -> 83` realized edge has signed width `+1`. -/
+theorem rawSignedWidthWeight_55_eq_one :
+    rawSignedWidthWeight (⟨55, by decide⟩ : OddNat)
+      (T (⟨55, by decide⟩ : OddNat)) = 1 := by
+  let a : OddNat := ⟨55, by decide⟩
+  have ha : s a = 1 := s_eq_one_of_mod_four_eq_three (by decide)
+  have hTa : (T a).1 = 83 := by
+    rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one a ha]
+    norm_num [a]
+  unfold rawSignedWidthWeight
+  rw [hTa]
+  decide
+
+/-- The `39 -> 59` realized edge has signed width zero. -/
+theorem rawSignedWidthWeight_39_eq_zero :
+    rawSignedWidthWeight (⟨39, by decide⟩ : OddNat)
+      (T (⟨39, by decide⟩ : OddNat)) = 0 := by
+  let a : OddNat := ⟨39, by decide⟩
+  have ha : s a = 1 := s_eq_one_of_mod_four_eq_three (by decide)
+  have hTa : (T a).1 = 59 := by
+    rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one a ha]
+    norm_num [a]
+  unfold rawSignedWidthWeight
+  rw [hTa]
+  decide
+
+/-- Global transition coverage contract for the first enriched signature. -/
+def CoversAllRawOddTransitionsWithFixedLowUpperBoundarySignature
+    (C : RelationalFiniteSignedTransitionPotentialCertificate
+      OddNat (FixedLowUpperBoundarySignature 1)) : Prop :=
+  (∀ x, C.Step x (T x)) ∧
+    (∀ x, C.signature x = fixedLowUpperBoundarySignature 1 x) ∧
+      (∀ x, C.actualWeight x (T x) = rawSignedWidthWeight x (T x))
+
+/-- The normalized top-two-bit enrichment rejects the old self-loop but still
+admits the positive projected cycle witnessed by `55 -> 83` and `39 -> 59`.
+Consequently it cannot support a global sound bounded potential. -/
+theorem not_coversAllRawOddTransitionsWithFixedLowUpperBoundarySignature
+    (C : RelationalFiniteSignedTransitionPotentialCertificate
+      OddNat (FixedLowUpperBoundarySignature 1)) :
+    ¬ CoversAllRawOddTransitionsWithFixedLowUpperBoundarySignature C := by
+  rintro ⟨hstep, hsignature, hweight⟩
+  let a : OddNat := ⟨55, by decide⟩
+  let b : OddNat := ⟨39, by decide⟩
+  have hab : C.signature (T a) = C.signature b := by
+    rw [hsignature, hsignature]
+    exact fixedLowUpperBoundarySignature_T_55_eq_39
+  have hba : C.signature (T b) = C.signature a := by
+    rw [hsignature, hsignature]
+    exact fixedLowUpperBoundarySignature_T_39_eq_55
+  have hactualAB := C.actual_le_projected a (T a) (hstep a)
+  have hactualBA := C.actual_le_projected b (T b) (hstep b)
+  have hpotentialAB := C.projected_le_potential_diff
+    (C.signature a) (C.signature b)
+  have hpotentialBA := C.projected_le_potential_diff
+    (C.signature b) (C.signature a)
+  rw [hab] at hactualAB
+  rw [hba] at hactualBA
+  rw [hweight, rawSignedWidthWeight_55_eq_one] at hactualAB
+  rw [hweight, rawSignedWidthWeight_39_eq_zero] at hactualBA
+  linarith
+
 /-!
 `CoversAllRawOddTransitionsWithFixedLowSignature` is intentionally stronger
 than observing a finite table: it requires the certificate relation and its
@@ -357,13 +620,44 @@ theorem not_coversAllRawOddTransitionsWithFixedLowSignature
   have hsig : C.signature (T x) = C.signature x := by
     rw [hsignature, hsignature]
     exact fixedLowRawSignature_T_rawAllOnesWitness_eq hr
-  have hactual := C.actual_le_projected x (T x) (hstep x)
-  have hprojected := C.projected_le_potential_diff
-    (C.signature x) (C.signature (T x))
-  rw [hsig] at hactual hprojected
-  simp only [sub_self] at hprojected
-  rw [hweight, rawSignedWidthWeight_rawAllOnesWitness_eq_one] at hactual
-  omega
+  apply C.false_of_step_of_signature_eq_of_actualWeight_pos (hstep x) hsig
+  rw [hweight, rawSignedWidthWeight_rawAllOnesWitness_eq_one]
+  norm_num
+
+/-!
+The obstruction survives every coarsening computed solely from the fixed low
+signature.  The theorem does not cover a strict refinement carrying new upper
+boundary information.
+-/
+
+/-- Coverage contract for an arbitrary finite coarsening of the audited fixed
+low signature. -/
+def CoversAllRawOddTransitionsThroughFixedLowSignature
+    {r : ℕ} {Signature : Type*} [Fintype Signature]
+    (f : FixedLowRawSignature r → Signature)
+    (C : RelationalFiniteSignedTransitionPotentialCertificate
+      OddNat Signature) : Prop :=
+  (∀ x, C.Step x (T x)) ∧
+    (∀ x, C.signature x = f (fixedLowRawSignature r x)) ∧
+      (∀ x, C.actualWeight x (T x) = rawSignedWidthWeight x (T x))
+
+/-- No finite factor of the fixed low signature can remove its positive
+closed-edge obstruction. -/
+theorem not_coversAllRawOddTransitionsThroughFixedLowSignature
+    {r : ℕ} (hr : 1 ≤ r)
+    {Signature : Type*} [Fintype Signature]
+    (f : FixedLowRawSignature r → Signature)
+    (C : RelationalFiniteSignedTransitionPotentialCertificate
+      OddNat Signature) :
+    ¬ CoversAllRawOddTransitionsThroughFixedLowSignature f C := by
+  rintro ⟨hstep, hsignature, hweight⟩
+  let x := rawAllOnesWitness r
+  have hlow := fixedLowRawSignature_T_rawAllOnesWitness_eq hr
+  have hsig : C.signature (T x) = C.signature x := by
+    rw [hsignature, hsignature, hlow]
+  apply C.false_of_step_of_signature_eq_of_actualWeight_pos (hstep x) hsig
+  rw [hweight, rawSignedWidthWeight_rawAllOnesWitness_eq_one]
+  norm_num
 
 /-- Existential form: the audited fixed low signature admits no global sound
 bounded-potential certificate. -/
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-334.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-334.md
new file mode 100644
index 00000000..93593beb
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-334.md
@@ -0,0 +1,271 @@
+# Petal / FloatWindow implementation report - checkpoint 334
+
+## Result
+
+This checkpoint replaces scalar source-coverage language by an actual
+source-bearing FIFO queue and audits the first upper-boundary refinement of the
+fixed low signature.
+
+The two routes now have precise boundaries:
+
+1. the source-age route has a temporally coherent owned queue whose cardinality
+   agrees exactly with the existing scalar queue;
+2. the fixed-low signature remains impossible under every finite coarsening,
+   and the first top-two-bit refinement is also rejected by an exact positive
+   projected cycle at depth `r = 1`.
+
+The positive conclusion remains conditional.  Lean proves that a uniform
+actual source-age bound implies uniform queue and endpoint-width bounds.  It
+does not prove that such a uniform age bound exists.
+
+## Cardinal-only correction from checkpoint 333
+
+The cp-333 predicate has been given the precise name
+
+```text
+CanonicalOutstandingQueueCardCoveredByRecentSourceClaims n H.
+```
+
+It states only that the scalar outstanding count is no larger than the number
+of recent carry-two source addresses.  It does not match outstanding claims to
+those sources and does not preserve source identity.  The former name
+
+```text
+CanonicalOutstandingQueueCoveredByRecentSourceClaims
+```
+
+remains as a compatibility abbreviation, with this limitation documented at
+the definition site.
+
+The existing scalar consequences are unchanged:
+
+```text
+card coverage
+  -> canonical queue upper bound H
+  -> endpoint-width upper bound bitWidth(n) + H.
+```
+
+## Exact block source carriers
+
+`canonicalBlockClaimSourceCarrier n k` is the set of carry-two source times in
+the exact canonical block interval
+
+```text
+[canonicalBlockStartTime n k, canonicalBlockStartTime n (k + 1)).
+```
+
+Lean proves:
+
+```text
+card block carrier = canonicalQueueDemand n k;
+every member is in the exact block interval;
+every member satisfies CarryTwoDebtAt n;
+distinct block carriers are disjoint.
+```
+
+This carrier supplies source identities to the recursive queue instead of
+rematching an endpoint count against an unrelated historical window.
+
+## Generic oldest-first queue
+
+The new `OldestFirstQueue.lean` is independent of Collatz.  For a finite set of
+natural-number source times, `eraseOldestN c s` removes at most `c` least
+members and `consumedOldestN c s` records exactly the removed members.
+
+The generic API proves:
+
+```text
+eraseOldestN c s subset s;
+card (eraseOldestN c s) = card s - c;
+card (consumedOldestN c s) = min c s.card;
+consumed and remaining sets are disjoint;
+consumed union remaining = s;
+every consumed source <= every remaining source.
+```
+
+The comparison theorem
+
+```text
+exists_le_of_card_eq_card_eraseOldestN
+```
+
+also proves the required finite minimax statement.  If `t` is any subset of
+the original carrier with the same cardinality as the FIFO remainder, then for
+every FIFO-retained source `y`, `t` contains a source `x <= y`.  Therefore a
+different same-capacity policy cannot make every retained source strictly
+newer than FIFO.
+
+## Canonical owned queue
+
+`CanonicalOwnedQueue.lean` defines the recursive source-bearing realization
+
+```text
+ownedQueue 0 = empty
+
+ownedQueue (k + 1)
+  = eraseOldestN (service k) (ownedQueue k union blockCarrier k).
+```
+
+The accompanying consumed set is the set difference between the available
+claims and this oldest-first remainder.  Source time itself is the claim
+identity.
+
+Lean proves the temporal and ownership invariants:
+
+```text
+every outstanding source before block k is earlier than block start k;
+every outstanding source remains a CarryTwoDebtAt source;
+old outstanding claims and current block arrivals are disjoint;
+consumed claims and the next outstanding queue are disjoint;
+consumed union next outstanding reconstructs all available claims;
+a consumed source never appears in any later owned queue.
+```
+
+Most importantly, the concrete queue agrees exactly with the pre-existing
+scalar recurrence:
+
+```text
+card ownedQueue(k) = canonicalOutstandingClaimQueueBeforeBlock n k;
+card ownedConsumed(k) = canonicalQueueConsumed n k.
+```
+
+Thus the owned queue is not merely an alternative model.  It is a
+source-preserving realization of the scalar queue already used by the endpoint
+accounting theorems.
+
+## Genuine source-age bridge
+
+The predicate
+
+```text
+CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H
+```
+
+requires every actual source `i` retained before every block `m` to satisfy
+
+```text
+canonicalBlockStartTime n m - i <= H.
+```
+
+Using temporal support and preserved `CarryTwoDebtAt`, Lean proves that such an
+owned source belongs to `canonicalRecentSourceClaimCarrier n H m`.  Exact
+cardinality agreement then gives the complete implication chain
+
+```text
+uniform actual source age H
+  -> actual owned queue embeds in the recent-source carrier
+  -> scalar cardinal coverage
+  -> uniform scalar queue bound H
+  -> uniform endpoint-width bound bitWidth(n) + H.
+```
+
+No theorem in this checkpoint asserts
+
+```text
+exists H, CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H.
+```
+
+That existence statement is the remaining positive problem on this route.
+
+## Generic closed-signature obstruction
+
+`FiniteSignedTransition.lean` now isolates the logical one-edge obstruction:
+if a realized related edge has positive actual weight, equal endpoint
+signatures, and is covered by the certificate step relation, then the
+certificate is contradictory.  Equal signatures force zero potential change,
+while soundness requires it to dominate a positive weight.
+
+The previous all-ones theorem is now a corollary of this generic result.
+
+The factor-through theorem strengthens the negative boundary.  For any finite
+map
+
+```text
+f : FixedLowRawSignature r -> Sigma,
+```
+
+no certificate that uses `f (fixedLowRawSignature r x)` and covers every raw
+odd transition can exist.  Therefore post-processing, merging, or otherwise
+coarsening the four fixed-low coordinates cannot repair their information
+loss.  This does not reject strict refinements that retain new information.
+
+## Top-two-bit refinement
+
+The normalized top-two-bit observation distinguishes the cp-333 all-ones
+edge.  For every `r >= 1`, its source has normalized bits `11`, while its
+successor has normalized bits `10`.  Consequently the old positive projected
+self-loop is absent after adding this coordinate.
+
+This is only a local repair.  It does not imply that the enriched signature
+admits a bounded potential.
+
+## Exact enriched-signature obstruction
+
+The first enriched candidate is
+
+```text
+fixedLowUpperBoundarySignature r x
+  = (fixedLowRawSignature r x, normalizedTopTwoBits x).
+```
+
+Exploratory enumeration found no positive projected self-loop in the sampled
+range, but it found positive projected cycles.  Numerical search was used only
+to locate witnesses; it was not promoted to a global claim.
+
+For `r = 1`, the exact witnesses were then proved in Lean:
+
+```text
+55 -> 83, raw signed-width weight = +1;
+39 -> 59, raw signed-width weight =  0;
+
+signature(83) = signature(39);
+signature(59) = signature(55).
+```
+
+The two realized signature edges therefore form a projected two-cycle with
+total weight `+1`.  Summing the two potential inequalities gives a strict
+positive demand around a closed signature cycle, which is impossible.  The
+concrete states do not need to form one orbit cycle: a projected certificate
+assigns potential to signatures, so any closed cycle in the realized
+signature-pair graph is sufficient.
+
+Lean consequently proves
+
+```text
+not_coversAllRawOddTransitionsWithFixedLowUpperBoundarySignature.
+```
+
+This is the genuine Stage L stopping obstruction.  The top-two coordinate
+removes the old one-edge collision but does not contain enough information to
+support a global bounded potential even at depth one.
+
+## Route decision
+
+The owned-source route remains open at one honest theorem:
+
+```text
+existence of a uniform actual source-age bound H
+  -> uniform queue and endpoint-width bounds.
+```
+
+The audited signature route has advanced from a positive self-loop obstruction
+to a positive projected-cycle obstruction.  A next signature candidate must
+separate at least one side of the exact `55/39` cycle, and it must be audited
+again for all positive projected cycles rather than only self-loops.
+
+## Verification
+
+The following build gates passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.FloatWindow.OldestFirstQueue
+lake build DkMath.Collatz.PetalBridge.FloatWindow.CanonicalOwnedQueue
+lake build DkMath.Collatz.PetalBridge.FloatWindow.RawLowSignatureObstruction
+lake build DkMath.Collatz.PetalBridge.FloatWindow
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath
+git diff --check
+```
+
+The changed FloatWindow implementation files contain no `sorry` or `admit`.
+The full top-level `DkMath` build completed successfully.
````
`````
