# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeFlow

gch: 42cde955784c6fd8a26661d3278d5d0952d52aaa

## Report

(13m58s)

cp-336 を完了しました。

主な確定事実:

- expired outstanding 数は `Int.toNat sourceAgeDeficit` と厳密に一致。
- uniform source age は、全 frontier prefix sum が非正であることと同値。
- deficit は crossing claims と actual consumption の差による厳密な符号付き漸化式。
- FIFO は任意 cutoff に対して、同数の他の割当より新しい source を多く保持する。
- uniform age 仮定から返済期限を `k + H + 1` 未満まで短縮。
- 外部の有限構造 certificate から、uniform age・queue bound・endpoint-width bound を導出可能。
- saturated block は `H = 0` で crossing `2`、consumption `1`、frontier increment `+1`。したがって pointwise 非正戦略は成立せず、正の horizon または複数ブロック amortization が必要。

実装は [CanonicalSourceAgeFlow.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalSourceAgeFlow.lean)、抽象 FIFO 回帰と threshold dominance は [OldestFirstQueue.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/OldestFirstQueue.lean:262)、総括は [report-petal-336.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-336.md) にあります。

`lake build DkMath` を含む全指定ゲートと `git diff --check` が成功。変更した Lean ファイルに新しい `sorry` はありません。

## Review

(4m32s)

## cp-336 実装レビュー

## 結論

**実装は全面採用。source-age route は、静的な同値整理から実際の signed-flow 問題へ移行した。**

commit `42cde955784c6fd8a26661d3278d5d0952d52aaa` と添付 report/diff は一致している。

cp-336 で確定した中心構造は次じゃ。

$$\operatorname{SourceAgeDeficit}_H(m+1)=\operatorname{SourceAgeDeficit}_H(m)+\operatorname{FrontierIncrement}_H(m)$$

$$\operatorname{FrontierIncrement}_H(m)=|\operatorname{Crossing}_H(m)|-\operatorname{ActualConsumed}(m)$$

$$\operatorname{UniformSourceAge}(H)\iff\forall m,\ \sum_{k<m}\operatorname{FrontierIncrement}_H(k)\le0$$

これで残る正方向の問題は、queue の定義や ownership の整備ではない。

> **期限境界を越える carry-two source の流入と、actual FIFO consumption の符号付き収支を制御すること**

そのものになった。

ただし、慎重監査として二点だけ表現を補正する。

1. `CanonicalSourceAgeFrontierPotentialCertificate` は正しい条件付き interface だが、まだ有限グラフだけで検査可能な certificate ではない。
2. saturated $H=0$ の $+1$ theorem は `CanonicalSaturatedBorderBlock n m` を仮定した条件付き theorem である。Lean 内で universal pointwise theorem の偽を確定するには、具体的 saturated block の存在 witness も必要になる。

どちらも実装の採用を妨げる問題ではない。次 checkpoint で閉じるべき意味境界じゃ。

---

## 1. Expired outstanding carrier

新しい carrier は、

```lean
canonicalExpiredOutstandingClaims n H m
```

として、

```lean
ownedOutstandingQueue ∩ oldSourceCarrier
```

により定義された。

membership は正確に、

$$i\in\operatorname{Expired}_H(m)\iff i\in\operatorname{Outstanding}(m)\land H<b_m-i$$

となる。したがって、これは単に古い historical claim ではなく、

> 現在も outstanding であり、実 source age が $H$ を超えた claim

そのものじゃ。

空性も exact である。

$$\operatorname{Expired}_H(m)=\varnothing\iff\forall i\in\operatorname{Outstanding}(m),\ b_m-i\le H$$

これで source-age violation が actual identity を持つ有限 carrier として公開された。

---

## 2. Signed deficit の正部分との完全一致

cp-336 の最も強い carrier theorem は、

$$|\operatorname{Expired}_H(m)|=\operatorname{Int.toNat}!\left(\operatorname{SourceAgeDeficit}_H(m)\right)$$

じゃ。

これは非常に重要である。

deficit が正なら、その値は単なる過大評価ではない。

> 期限切れのまま実際に残っている outstanding source の正確な個数

である。

逆に deficit が非正なら expired carrier は空になる。

負の deficit は actual expired claim の「負個数」ではない。これは、

> old source mass よりも cumulative actual consumption の方が先行している signed credit

を表す。

この credit を `Nat` の reflected queue へ変換せず、`Int` のまま保存した判断は正しい。

---

## 3. Deficit の符号と lower-tail inclusion

exact cardinal theorem の背後で、より強い集合 inclusion が証明された。

deficit が正なら、

$$\operatorname{CumulativeConsumed}(m)\subseteq\operatorname{OldClaims}_H(m)$$

deficit が非正なら、

$$\operatorname{OldClaims}_H(m)\subseteq\operatorname{CumulativeConsumed}(m)$$

となる。

これは FIFO global ordering が働いているためじゃ。

historical claims は source time 順に並び、FIFO は古い側から消費する。ゆえに consumed lower tail と old-source lower tail は、互いに交差した複雑な集合にはならない。

どちらか一方が他方を包含する。

この全順序性があるため、

$$|\operatorname{OldClaims}|-|\operatorname{Consumed}|$$

の正部分が、そのまま actual expired remainder の cardinalityになる。

---

## 4. Moving horizon carrier

新しい crossing carrier は、

```lean
canonicalSourceAgeHorizonCrossingClaims n H m
```

として、

$$[b_m-H,\ b_{m+1}-H)$$

内の carry-two source を集める。

old carrier は一段ごとに、

$$\operatorname{Old}_H(m+1)=\operatorname{Old}_H(m)\sqcup\operatorname{Crossing}_H(m)$$

と成長する。

この theorem は $b_m<H$ の早期領域も含んでいる。

`Nat` subtraction により cutoff が $0$ に潰れている期間でも、余計な仮定なしで同じ recurrence が成立する。

ここは監査上問題なし。

---

## 5. Exact signed recurrence

frontier increment は、

$$F_H(m)=|\operatorname{Crossing}_H(m)|-\operatorname{Consumed}(m)$$

として `Int` で定義された。

そして、

$$D_H(0)=0$$

$$D_H(m+1)=D_H(m)+F_H(m)$$

$$D_H(m)=\sum_{k<m}F_H(k)$$

が証明された。

これにより deficit の負 credit は block 間で失われない。

例えば、

```text
-3, +1, +1, +1
```

という frontier flow なら、prefix は、

```text
-3, -2, -1, 0
```

と推移する。

各段で `max(0, ·)` を取れば最初の $-3$ credit が消えてしまうが、今回の `Int` recurrence はそれを正しく保持する。

---

## 6. Uniform age の exact prefix formulation

cp-336 は、

$$\operatorname{UniformSourceAge}(H)\iff\forall m,\ \sum_{k<m}F_H(k)\le0$$

を証明した。

さらに carrier 版として、

$$\operatorname{UniformSourceAge}(H)\iff\forall m,\ \operatorname{Expired}_H(m)=\varnothing$$

も得られた。

これで正方向の target は三つの完全に同値な形を持つ。

```text
actual source age
signed frontier prefixes
expired carrier emptiness
```

どれを証明しても同じ theorem に到達する。

特に arithmetic attack では frontier prefix、反例探索では expired carrier、最終解釈では actual source age を使える。

---

## 7. Horizon zero の意味

$H=0$ では old carrier は全 historical claims になる。

したがって、

$$D_0(m)=Q_m$$

が証明された。

crossing carrier も current block claim carrierそのものになる。

$$\operatorname{Crossing}_0(m)=\operatorname{BlockClaims}(m)$$

従って次の theorem は直ちに追加できる。

$$F_0(m)=Q_{m+1}-Q_m$$

また、

$$F_0(m)=\operatorname{Demand}(m)-\operatorname{Consumed}(m)$$

でもある。

つまり $H=0$ frontier flow は、新しい概念ではなく既存 scalar queue の exact incrementじゃ。

この compatibility theorem を公開しておくと、旧 queue API と source-age flow API の接続がより明確になる。

---

## 8. Horizon monotonicity

$H_1\le H_2$ なら、

$$D_{H_2}(m)\le D_{H_1}(m)$$

が証明された。

expired carrierも、

$$\operatorname{Expired}*{H_2}(m)\subseteq\operatorname{Expired}*{H_1}(m)$$

となる。

これは当然だが、今後重要になる。

ある $H$ で uniform age が閉じれば、それより大きい horizon でも閉じる。

従って admissible horizon 集合は上方閉集合になる。

最小 horizon が存在すれば、

```lean
minimalCanonicalSourceAgeHorizon
```

のような値を後から定義できる。

ただし、その存在自体はまだ未証明じゃ。

---

## 9. Queue boundedness と age boundedness の分離

generic FIFO 層では、

```lean
persistentSingletonQueue m = {0}
```

が追加された。

cardinality は常に $1$ だが、時刻 $m$ における source age は $m$ なので一様上界を持たない。

従って一般論では、

$$\operatorname{UniformAge}\Longrightarrow\operatorname{UniformCardinality}$$

だが、

$$\operatorname{UniformCardinality}\Longrightarrow\operatorname{UniformAge}$$

ではない。

この regression は重要じゃ。

source-age bound を queue bound の別名として循環利用する道を正式に封じた。

---

## 10. FIFO threshold dominance

任意の cutoff $t$ と、FIFO queue と同じ cardinalityを持つ任意の admissible assignment $u$ について、

$$|{i\in u\mid t\le i}|\le|{i\in\operatorname{FIFO}\mid t\le i}|$$

が証明された。

これは以前の、

$$\min(u)\le\min(\operatorname{FIFO})$$

より強い。

FIFO は一つの oldest source だけでなく、全 cutoff において新しい側の mass を最大化する。

言い換えると FIFO remainder は、source-time 分布について他の全 assignment を stochastic に上回る newest tailじゃ。

この theorem は source-age 最適性を十分に固定している。

---

## 11. Repayment lag の短縮

uniform age $H$ を仮定すると、block $k$ で生まれた claim は、

$$j<k+H+1$$

を満たす block $j$ で消費されることが証明された。

cp-335 の $k+H+2$ から一段短縮された。

ここで $H$ は accelerated source-time 単位であり、block length は常に一以上なので、$H$ source-time 進むために必要な block 数も高々 $H$ となる。

indexing も正しい。

---

## 12. Potential certificate の監査

新しい structure は、

```lean
CanonicalSourceAgeFrontierPotentialCertificate
```

として、

- finite `Signature`
- concrete successor step
- actual weight と frontier increment の一致
- endpoint potential が initial potential を超えないこと

を要求する。

path telescope は正しい。

$$\sum_{k<m}F_H(k)\le\Phi(\sigma_m)-\Phi(\sigma_0)\le0$$

したがって uniform source age、queue bound、endpoint-width bound が従う。

### 判定

**theorem は正しい。循環構成も実装されていない。**

ただし、この structure を現時点で「finite certificate が完成した」と呼ぶのはまだ早い。

問題は、

```lean
prefixPotentialChange_nonpos : ∀ m, ...
```

じゃ。

これは全自然数時刻を量化する無限 theoremである。

finite なのは `Signature` 型だけであり、現在の field 自体は有限グラフ上の検査へ落ちていない。

つまり現在得たものは、

> 外部からこの無限 reachable-potential 条件を証明できれば閉じる conditional wrapper

である。

まだ次にはなっていない。

> finite signature graph を全探索すれば certificate を検査できる

### 本当に有限化する形

最も単純な強化は、

```lean
potential_le_initial :
  ∀ s : Signature,
    certificate.potential s ≤
      certificate.potential (certificate.signature 0)
```

じゃ。

`Signature` は有限なので、これは有限 case analysis の対象になる。

より精密には、finite projected graph 上の reachable signatureだけを集め、

```lean
s ∈ reachableFromInitial →
  potential s ≤ potential initial
```

を証明すればよい。

次 checkpoint では現在の `prefixPotentialChange_nonpos` を compatibility fieldとして残しつつ、finite graph propertyから自動導出する wrapper を追加すべきじゃ。

---

## 13. Saturated block の $H=0$ frontier

saturated blockでは、

$$|\operatorname{Crossing}_0(m)|=2$$

$$\operatorname{Consumed}(m)=1$$

従って、

$$F_0(m)=1$$

が証明された。

算術は完全に正しい。

saturated block は length $2$ で、両 source が carry-two claimになる。一方 terminal capacity は $1$ なので actual consumption は $\min(2,1)=1$ じゃ。

また $H=0$ では $F_0$ が queue incrementなので、

$$Q_{m+1}=Q_m+1$$

まで従う。

これは saturated block が scalar queue を厳密に一増加させることを意味する。

---

## 14. 「反例」の形式的境界

現在の theorem は、

```lean
(h : CanonicalSaturatedBorderBlock n m) →
  canonicalSourceAgeFrontierIncrement n 0 m = 1
```

という条件付き theoremじゃ。

従って確定したのは、

> saturated block 上では pointwise nonpositive frontier theorem は成立しない

ということ。

一方、Lean 内で、

```lean
¬ ∀ n m, canonicalSourceAgeFrontierIncrement n 0 m ≤ 0
```

まで証明するには、

```lean
∃ n m, CanonicalSaturatedBorderBlock n m
```

という具体的 witness が必要になる。

既存の数値 audit は saturated block を多数観測しているが、それは executable audit の記録であり、Lean theoremとしての存在 witness ではない。cp-318 report では 33,435 個の saturated blocks が観測されている。

今回確認した theorem module 内では、saturation の構造定理は豊富だが、具体的な `n,m` の存在 theorem は見当たらなかった。

したがって report の、

> pointwise 非正戦略は既に反例を持つ

は数学的・実験的には妥当だが、Lean 確定事項としては次の表現が厳密じゃ。

> saturated block が存在する任意の canonical orbitでは、$H=0$ pointwise 非正戦略は失敗する。

次 checkpoint で最小の concrete saturated witnessを一件 Lean 化すれば、完全な formal counterexampleになる。

---

## 15. Saturated successor theoremだけでは返済にならない

既存 theorem は、saturated block が連続しないことを証明している。

しかし、

```text
次 block が saturated ではない
```

は、

```text
次 block の frontier increment ≤ -1
```

を意味しない。

既存 successor theoremも、

```lean
successor drift ≤ 0
or
successor pressure > 0
```

という分類であり、frontier consumption の下界を直接与えるものではない。

従って report の、

> no consecutive saturation だけでは二 block frontier sum 非正は出ない

という判断は正しい。

---

## 16. 一歩先の重要式：horizon 方向の差分

現在は block index $m$ 方向の recurrence が完成した。

次は horizon $H$ 方向の差分を作るべきじゃ。

成熟領域 $H<b_m$ では、crossing interval は一 source-time 左へ平行移動する。

従って期待される signed identity は、

$$|\operatorname{Crossing}*{H+1}(m)|-|\operatorname{Crossing}*H(m)|=\mathbf{1}*{\mathrm{CarryTwo}(b_m-H-1)}-\mathbf{1}*{\mathrm{CarryTwo}(b_{m+1}-H-1)}$$

となる。

consumption は $H$ に依存しないため、

$$F_{H+1}(m)-F_H(m)=\mathbf{1}*{\mathrm{CarryTwo}(b_m-H-1)}-\mathbf{1}*{\mathrm{CarryTwo}(b_{m+1}-H-1)}$$

も従う。

deficit 自体については、さらに単純に、

$$D_{H+1}(m)=D_H(m)-\mathbf{1}_{\mathrm{CarryTwo}(b_m-H-1)}$$

となるはずじゃ。

これは horizon monotonicity の exact one-step refinementである。

この式があれば、

- $H=0$ から $H=1$
- $H=1$ から $H=2$
- 一般の $H$

へ frontier flow がどう変わるかを、一点の carry-two indicatorだけで追える。

---

## 17. $H=1$ saturated formula

saturated block は length $2$ なので、$H=1$ crossing interval は、

$$[b_m-1,\ b_{m+1}-1)=[b_m-1,\ b_m+1)$$

になる。

current saturated block の二 source のうち、前半一 sourceだけがこの区間に入り、代わりに直前 source $b_m-1$ が入る。

従って期待される exact formula は、

$$|\operatorname{Crossing}*1(m)|=1+\mathbf{1}*{\mathrm{CarryTwo}(b_m-1)}$$

actual consumption は $1$ なので、

$$F_1(m)=\mathbf{1}_{\mathrm{CarryTwo}(b_m-1)}$$

となる。

つまり saturated block 自身については、$H=1$ でも frontier increment は負にはならず、$0$ または $1$ になる可能性が高い。

これを Lean で閉じれば、

> positive horizon を一つ増やすだけでは pointwise repaymentにならない

ことまで exact に診断できる。

ただし current block のどの source time が claim depthに対応するかを、既存 carrier APIから厳密に接続する必要がある。

---

## 18. 現在地

正方向は現在、

```text
actual claim source
→ global FIFO newest tail
→ expired outstanding carrier
→ signed source-age deficit
→ exact frontier recurrence
→ all prefix sums nonpositive for some H        [未証明]
→ uniform actual source age
→ uniform queue bound
→ endpoint-width bound
```

まで来た。

cp-336 により残る Gap は、

```text
∃ H, ∀ m,
  ∑ k < m, frontierIncrement H k ≤ 0
```

へ完全に圧縮された。

これはまだ難しいが、少なくとも敵は一つの符号付き流量に固定された。

---

## 判定まとめ

### Expired carrier semantics

**完成。**

### Expired cardinalityと deficit 正部分

**完成。exact equality。**

### Moving horizon recurrence

**完成。Nat subtraction 早期領域も処理済み。**

### Signed frontier recurrence

**完成。**

### Uniform age / prefix nonpositive equivalence

**完成。**

### Horizon monotonicity

**完成。**

### FIFO threshold dominance

**完成。**

### Queue boundとage boundの一般的非同値

**完成。**

### Repayment block lag $H+1$

**完成。**

### Conditional potential wrapper

**正しい。ただし finite-checkable certificate は未完成。**

### Saturated $H=0$ increment $+1$

**条件付き theoremとして完成。**

### Concrete formal saturated witness

**未実装。**

### Pointwise nonpositive universal theorem の formal negation

**concrete saturated witness 待ち。**

### cp-336 総合判定

**全面採用。二つの意味境界を cp-337 で閉じる。**

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge FloatWindow branch after
report-petal-336.

The cp-336 implementation is accepted.

It completed the exact source-age signed-flow layer:

    expired outstanding cardinality
      =
    positive part of the signed source-age deficit;

    source-age deficit
      =
    every prefix sum of frontier increments;

    uniform actual source age H
      iff
    every frontier prefix at H is nonpositive.

Two semantic boundaries must now be closed:

    the current potential wrapper still assumes an all-time
    `prefixPotentialChange_nonpos` field;

    the saturated `H = 0` obstruction is conditional on the existence of a
    saturated canonical block.

The next checkpoint must make the certificate genuinely finite-facing and
audit the horizon direction of the frontier flow.

# Stage A — report terminology and concrete saturation witness

Search for the smallest explicit pair `(n,m)` satisfying:

    CanonicalSaturatedBorderBlock n m.

Use an executable search only to locate the witness, then prove the witness in
Lean by reduction, `native_decide`, or exact arithmetic lemmas.

Add:

    exists_canonicalSaturatedBorderBlock :
      ∃ n m, CanonicalSaturatedBorderBlock n m.

Then prove the actual formal negation:

    not_forall_sourceAgeFrontierIncrement_zero_nonpos :
      ¬ ∀ n m, canonicalSourceAgeFrontierIncrement n 0 m ≤ 0.

If the concrete witness cannot be formalized, do not state that universal
pointwise nonpositivity has been formally refuted.  Retain only the conditional
saturated theorem and record the exact obstruction.

# Stage B — exact H = 0 queue compatibility

Prove:

    canonicalSourceAgeFrontierIncrement n 0 m
      =
    (canonicalOutstandingClaimQueueBeforeBlock n (m + 1) : Int)
      -
    canonicalOutstandingClaimQueueBeforeBlock n m.

Also prove:

    canonicalSourceAgeFrontierIncrement n 0 m
      =
    (canonicalQueueDemand n m : Int)
      -
    canonicalQueueConsumed n m.

Derive for a saturated block:

    queueBeforeBlock (m + 1) = queueBeforeBlock m + 1.

These are compatibility theorems between the old reflected queue and the new
source-age frontier.

# Stage C — finite-checkable potential certificate

Keep `CanonicalSourceAgeFrontierPotentialCertificate` as a compatibility
surface.

Add a stronger wrapper whose initial-potential condition is genuinely finite.

The first acceptable form is:

    potential_le_initial :
      ∀ s : Signature,
        certificate.potential s
          <= certificate.potential (certificate.signature 0).

Prove that this finite-state field implies:

    prefixPotentialChange_nonpos.

Then derive the existing source-age, queue, and endpoint-width theorems.

A more precise optional form may use a finite reachable-signature carrier:

    reachableSignaturesFromInitial : Finset Signature.

It must satisfy:

    initial signature belongs to it;

    it is closed under the projected transition relation;

    every concrete canonical signature belongs to it;

    potential of every member is at most the initial potential.

Do not define the reachable carrier, signature, or potential from
`canonicalSourceAgeDeficit` or its prefix sums.

Document that `Fintype Signature` alone does not make the old all-time field a
finite verification.

# Stage D — carry-two indicator API

Define an integer or natural indicator:

    canonicalCarryTwoIndicator n i =
      if CarryTwoDebtAt n i then 1 else 0.

Prove exact singleton-cardinality lemmas connecting it to:

    carryTwoPositions n {i}.

Provide both Nat and Int coercion forms needed by frontier identities.

# Stage E — exact horizon-step identity for old carriers

For `H < canonicalBlockStartTime n m`, prove:

    oldCarrier (H + 1) m
      =
    oldCarrier H m erase
      (canonicalBlockStartTime n m - H - 1),

with the erase conditioned by `CarryTwoDebtAt`.

Prefer an unconditional carrier statement using filtered singleton difference
if it avoids fragile side conditions.

Prove the exact signed cardinal identity:

    sourceAgeDeficit n (H + 1) m
      =
    sourceAgeDeficit n H m
        -
    canonicalCarryTwoIndicator n
      (canonicalBlockStartTime n m - H - 1).

Handle the early cutoff regime separately and explicitly.

# Stage F — horizon-step identity for crossing flow

In the mature regime `H < canonicalBlockStartTime n m`, prove:

    card crossing (H + 1) m - card crossing H m
      =
    carryIndicator (blockStart m - H - 1)
      -
    carryIndicator (blockStart (m + 1) - H - 1)

in `Int`.

Then prove:

    frontierIncrement (H + 1) m - frontierIncrement H m
      =
    the same boundary-indicator difference.

This is the exact sliding-window law in the horizon direction.

# Stage G — H = 1 block decomposition

For positive block start, decompose:

    crossing 1 m

into:

    the predecessor source `blockStart m - 1`;

    the current block claim carrier with its final source removed.

Prove an exact cardinal formula using carry indicators at the two boundary
sources.

Do not rely on a numerical table.

# Stage H — saturated H = 1 audit

Using the saturated length-two and complete-claim theorems, determine the exact
formula for:

    canonicalSourceAgeFrontierIncrement n 1 m

under:

    CanonicalSaturatedBorderBlock n m.

Expected candidate:

    frontierIncrement 1 m
      =
    canonicalCarryTwoIndicator n
      (canonicalBlockStartTime n m - 1).

Prove it only if the source-time/claim-depth correspondence closes exactly.

If it fails, record the exact missing source-address theorem rather than
replacing it by a count estimate.

# Stage I — origin-to-crossing map

For a claim source `i` and horizon `H`, define the canonical block containing
the shifted source time `i + H`, using the existing unique canonical block
coverage theorem.

Define:

    canonicalAgeCrossingBlockOfSource n H i.

Prove, with exact early-boundary conditions, that an actual carry-two source
belongs to the crossing carrier of its age-crossing block.

This is the bridge needed to transfer the existing saturated/successor grammar
from claim birth blocks to future horizon-crossing blocks.

# Stage J — short-window frontier sums

Define:

    canonicalSourceAgeFrontierWindowSum n H q L :=
      sum j in range L,
        canonicalSourceAgeFrontierIncrement n H (q + j).

Prove the telescope:

    frontierWindowSum H q L
      =
    sourceAgeDeficit H (q + L) - sourceAgeDeficit H q.

Add exact length-one and length-two forms.

For a saturated block, audit the shortest windows around it for `H = 0` and
`H = 1`.

Do not infer:

    not consecutive saturated

implies:

    two-block frontier sum <= 0.

Actual consumption must be bounded explicitly.

# Stage K — numerical discovery audit

Create a bounded discovery audit for small positive horizons and short windows.

Record, for each tested H and window length:

    maximum frontier increment;

    maximum prefix frontier sum;

    saturated-block local patterns;

    shortest later window returning the saturated +1 to nonpositive total;

    exact counterexample states for failed candidates.

The audit is for theorem discovery only.

Every promoted statement must subsequently receive an exact Lean proof.

# Stage L — saturated-successor arithmetic bridge

Inspect the already proved successor split:

    successor endpoint drift <= 0
      or
    successor pressure > 0.

Determine whether either branch yields a lower bound on actual consumption at
the source-age frontier.

Keep the quantities separate:

    endpoint drift;

    pressure contribution;

    frontier crossing count;

    actual queue consumption.

Do not substitute capacity for actual consumption.

# Stage M — challenge-facing boundary

Keep the exact positive route visible:

    finite structural frontier certificate for some H
      ->
    every frontier prefix <= 0
      ->
    uniform actual source age H
      ->
    uniform queue bound H
      ->
    endpoint-width bound bitWidth(n) + H.

State separately that no such structural certificate or horizon H has yet been
constructed.

# Stopping rule

Stop at the first genuine obstruction among:

    no concrete saturated witness can be formalized;

    the H = 0 queue-increment identity fails;

    the finite initial-maximum potential wrapper remains circular;

    old-carrier horizon shift fails in the Nat-subtraction boundary regime;

    crossing-cardinality shift cannot be reduced to two boundary indicators;

    H = 1 saturated flow cannot be expressed from existing source-address APIs;

    shifted claim sources cannot be assigned to a unique crossing block;

    no short-window consumption lower bound follows from the current successor
    grammar.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-337.md
```

cp-336 で block 時間方向の運動方程式は完成した。

次は horizon 方向にも一目盛りずつ動かし、**どの carry-two source が境界へ入り、どの source が境界から外れるか**を exact に追う段階じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
index 4506f93a..54ef7b46 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
@@ -33,6 +33,7 @@ import DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition
 import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceTimeLag
 import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalOwnedQueue
 import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalOwnedQueueGlobal
+import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeFlow
 import DkMath.Collatz.PetalBridge.FloatWindow.RawLowSignatureObstruction

 #print "file: DkMath.Collatz.PetalBridge.FloatWindow"
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalSourceAgeFlow.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalSourceAgeFlow.lean
new file mode 100644
index 00000000..a3bff6ab
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalSourceAgeFlow.lean
@@ -0,0 +1,582 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalOwnedQueueGlobal
+import DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition
+import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentSaturatedSuccessor
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeFlow"
+
+namespace DkMath.Collatz
+
+/-!
+# Canonical source-age signed flow
+
+The global FIFO normal form identifies the outstanding queue as a newest
+historical upper tail.  This module moves the age cutoff one canonical block at
+a time.  Claims crossing that cutoff are signed arrivals at the age frontier;
+actual FIFO consumption is signed service.  Negative credit is retained in
+`Int` and is never truncated by a reflected recurrence.
+-/
+
+/-! ## Expired outstanding claims -/
+
+/-- Actual outstanding identities lying strictly below the age-`H` cutoff. -/
+noncomputable def canonicalExpiredOutstandingClaims
+    (n : OddNat) (H m : ℕ) : Finset ℕ :=
+  canonicalOwnedOutstandingClaimsBeforeBlock n m ∩
+    canonicalOldSourceClaimCarrier n H m
+
+/-- An expired identity is an actual outstanding carry-two source. -/
+theorem canonicalExpiredOutstandingClaims_subset_outstanding
+    (n : OddNat) (H m : ℕ) :
+    canonicalExpiredOutstandingClaims n H m ⊆
+      canonicalOwnedOutstandingClaimsBeforeBlock n m := by
+  exact Finset.inter_subset_left
+
+theorem carryTwoDebtAt_of_mem_canonicalExpiredOutstandingClaims
+    {n : OddNat} {H m i : ℕ}
+    (hi : i ∈ canonicalExpiredOutstandingClaims n H m) :
+    CarryTwoDebtAt n i :=
+  carryTwoDebtAt_of_mem_canonicalOwnedOutstandingClaimsBeforeBlock
+    (canonicalExpiredOutstandingClaims_subset_outstanding n H m hi)
+
+/-- Expiration is exactly outstanding membership with actual source age
+strictly greater than the horizon. -/
+theorem mem_canonicalExpiredOutstandingClaims_iff
+    {n : OddNat} {H m i : ℕ} :
+    i ∈ canonicalExpiredOutstandingClaims n H m ↔
+      i ∈ canonicalOwnedOutstandingClaimsBeforeBlock n m ∧
+        H < canonicalBlockStartTime n m - i := by
+  constructor
+  · intro hi
+    rcases Finset.mem_inter.mp hi with ⟨hiOut, hiOld⟩
+    have hiCutoff := (Finset.mem_Ico.mp
+      (mem_carryTwoPositions_iff.mp hiOld).1).2
+    have hiTop := mem_canonicalOwnedOutstandingClaimsBeforeBlock_lt_start hiOut
+    exact ⟨hiOut, by omega⟩
+  · rintro ⟨hiOut, hiAge⟩
+    apply Finset.mem_inter.mpr
+    refine ⟨hiOut, ?_⟩
+    rw [canonicalOldSourceClaimCarrier, mem_carryTwoPositions_iff]
+    have hiTop := mem_canonicalOwnedOutstandingClaimsBeforeBlock_lt_start hiOut
+    exact ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩,
+      carryTwoDebtAt_of_mem_canonicalOwnedOutstandingClaimsBeforeBlock hiOut⟩
+
+/-- The expired carrier is empty exactly when the block-local actual age bound
+holds for every retained source. -/
+theorem canonicalExpiredOutstandingClaims_eq_empty_iff
+    (n : OddNat) (H m : ℕ) :
+    canonicalExpiredOutstandingClaims n H m = ∅ ↔
+      ∀ i, i ∈ canonicalOwnedOutstandingClaimsBeforeBlock n m →
+        canonicalBlockStartTime n m - i ≤ H := by
+  constructor
+  · intro hempty i hi
+    by_contra hage
+    have hiExpired : i ∈ canonicalExpiredOutstandingClaims n H m :=
+      mem_canonicalExpiredOutstandingClaims_iff.mpr ⟨hi, by omega⟩
+    rw [hempty] at hiExpired
+    simp at hiExpired
+  · intro h
+    apply Finset.not_nonempty_iff_eq_empty.mp
+    rintro ⟨i, hi⟩
+    have hiData := mem_canonicalExpiredOutstandingClaims_iff.mp hi
+    exact (Nat.not_lt_of_ge (h i hiData.1)) hiData.2
+
+/-! ## Moving age horizon -/
+
+/-- Carry-two claims crossing the moving source-age cutoff during block `m`. -/
+noncomputable def canonicalSourceAgeHorizonCrossingClaims
+    (n : OddNat) (H m : ℕ) : Finset ℕ :=
+  carryTwoPositions n
+    (Finset.Ico
+      (canonicalBlockStartTime n m - H)
+      (canonicalBlockStartTime n (m + 1) - H))
+
+/-- Moving the cutoff by one canonical block appends exactly the horizon
+crossing carrier, including the Nat-subtraction early regime. -/
+theorem canonicalOldSourceClaimCarrier_succ
+    (n : OddNat) (H m : ℕ) :
+    canonicalOldSourceClaimCarrier n H (m + 1) =
+      canonicalOldSourceClaimCarrier n H m ∪
+        canonicalSourceAgeHorizonCrossingClaims n H m := by
+  ext i
+  simp only [canonicalOldSourceClaimCarrier,
+    canonicalSourceAgeHorizonCrossingClaims, mem_carryTwoPositions_iff,
+    Finset.mem_Ico, Finset.mem_union]
+  constructor
+  · rintro ⟨⟨_, hiTop⟩, hiCarry⟩
+    by_cases hiOld : i < canonicalBlockStartTime n m - H
+    · exact Or.inl ⟨⟨by omega, hiOld⟩, hiCarry⟩
+    · exact Or.inr ⟨⟨by omega, hiTop⟩, hiCarry⟩
+  · rintro (⟨⟨_, hiTop⟩, hiCarry⟩ | ⟨⟨_, hiTop⟩, hiCarry⟩)
+    · have hmono := canonicalBlockStartTime_mono n
+        (show m ≤ m + 1 by omega)
+      exact ⟨⟨by omega, by omega⟩, hiCarry⟩
+    · exact ⟨⟨by omega, hiTop⟩, hiCarry⟩
+
+/-- The previous old carrier and the newly crossing interval are disjoint. -/
+theorem disjoint_canonicalOldSourceClaimCarrier_horizonCrossing
+    (n : OddNat) (H m : ℕ) :
+    Disjoint (canonicalOldSourceClaimCarrier n H m)
+      (canonicalSourceAgeHorizonCrossingClaims n H m) := by
+  apply Finset.disjoint_left.mpr
+  intro i hiOld hiCross
+  have hiOldTop := (Finset.mem_Ico.mp
+    (mem_carryTwoPositions_iff.mp hiOld).1).2
+  have hiCrossLow := (Finset.mem_Ico.mp
+    (mem_carryTwoPositions_iff.mp hiCross).1).1
+  omega
+
+/-- Exact cardinal growth of the moving old-source carrier. -/
+theorem card_canonicalOldSourceClaimCarrier_succ
+    (n : OddNat) (H m : ℕ) :
+    (canonicalOldSourceClaimCarrier n H (m + 1)).card =
+      (canonicalOldSourceClaimCarrier n H m).card +
+        (canonicalSourceAgeHorizonCrossingClaims n H m).card := by
+  rw [canonicalOldSourceClaimCarrier_succ,
+    Finset.card_union_of_disjoint
+      (disjoint_canonicalOldSourceClaimCarrier_horizonCrossing n H m)]
+
+/-! ## Exact signed recurrence -/
+
+/-- Signed one-block age-frontier flow: newly expired source mass minus actual
+FIFO consumption. -/
+noncomputable def canonicalSourceAgeFrontierIncrement
+    (n : OddNat) (H m : ℕ) : ℤ :=
+  (canonicalSourceAgeHorizonCrossingClaims n H m).card -
+    canonicalQueueConsumed n m
+
+@[simp] theorem canonicalSourceAgeDeficit_zero
+    (n : OddNat) (H : ℕ) :
+    canonicalSourceAgeDeficit n H 0 = 0 := by
+  simp [canonicalSourceAgeDeficit, canonicalOldSourceClaimCarrier,
+    canonicalCumulativeConsumedCountBeforeBlock, canonicalBlockStartTime,
+    canonicalEndpointBlockStart, carryTwoPositions]
+
+/-- The static deficit evolves by exact signed frontier flow. -/
+theorem canonicalSourceAgeDeficit_succ
+    (n : OddNat) (H m : ℕ) :
+    canonicalSourceAgeDeficit n H (m + 1) =
+      canonicalSourceAgeDeficit n H m +
+        canonicalSourceAgeFrontierIncrement n H m := by
+  unfold canonicalSourceAgeDeficit canonicalSourceAgeFrontierIncrement
+  rw [card_canonicalOldSourceClaimCarrier_succ]
+  unfold canonicalCumulativeConsumedCountBeforeBlock
+  rw [Finset.sum_range_succ]
+  push_cast
+  ring
+
+/-- Prefix normal form.  Negative age credit is retained in `Int`. -/
+theorem canonicalSourceAgeDeficit_eq_sum_frontierIncrement
+    (n : OddNat) (H m : ℕ) :
+    canonicalSourceAgeDeficit n H m =
+      ∑ k ∈ Finset.range m, canonicalSourceAgeFrontierIncrement n H k := by
+  induction m with
+  | zero => simp
+  | succ m ih =>
+      rw [canonicalSourceAgeDeficit_succ, ih, Finset.sum_range_succ]
+
+/-! ## Exact uniform-age surfaces -/
+
+/-- Uniform actual source age is the nonpositivity of every signed frontier
+prefix. -/
+theorem canonicalOwnedOutstandingClaimsHaveSourceAgeAtMost_iff_frontierPrefix_nonpos
+    (n : OddNat) (H : ℕ) :
+    CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H ↔
+      ∀ m, (∑ k ∈ Finset.range m,
+        canonicalSourceAgeFrontierIncrement n H k) ≤ 0 := by
+  rw [canonicalOwnedOutstandingClaimsHaveSourceAgeAtMost_iff_deficit_nonpos]
+  constructor <;> intro h m
+  · rw [← canonicalSourceAgeDeficit_eq_sum_frontierIncrement]
+    exact h m
+  · rw [canonicalSourceAgeDeficit_eq_sum_frontierIncrement]
+    exact h m
+
+/-- Carrier form of the same uniform age theorem. -/
+theorem canonicalOwnedOutstandingClaimsHaveSourceAgeAtMost_iff_expired_empty
+    (n : OddNat) (H : ℕ) :
+    CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H ↔
+      ∀ m, canonicalExpiredOutstandingClaims n H m = ∅ := by
+  constructor
+  · intro h m
+    exact (canonicalExpiredOutstandingClaims_eq_empty_iff n H m).2 (h m)
+  · intro h m
+    exact (canonicalExpiredOutstandingClaims_eq_empty_iff n H m).1 (h m)
+
+/-! ## Boundary values and horizon monotonicity -/
+
+/-- At horizon zero the old carrier is the complete historical carrier. -/
+theorem canonicalOldSourceClaimCarrier_zero_horizon
+    (n : OddNat) (m : ℕ) :
+    canonicalOldSourceClaimCarrier n 0 m =
+      canonicalHistoricalClaimSourceCarrier n m := by
+  ext i
+  simp [canonicalOldSourceClaimCarrier, canonicalHistoricalClaimSourceCarrier]
+
+/-- At horizon zero the signed source-age deficit is exactly the scalar queue. -/
+theorem canonicalSourceAgeDeficit_zero_horizon
+    (n : OddNat) (m : ℕ) :
+    canonicalSourceAgeDeficit n 0 m =
+      canonicalOutstandingClaimQueueBeforeBlock n m := by
+  unfold canonicalSourceAgeDeficit
+  rw [canonicalOldSourceClaimCarrier_zero_horizon,
+    card_canonicalHistoricalClaimSourceCarrier]
+  push_cast
+  ring
+
+/-- At horizon zero, frontier arrivals are exactly the current block claims. -/
+theorem canonicalSourceAgeHorizonCrossingClaims_zero_horizon
+    (n : OddNat) (m : ℕ) :
+    canonicalSourceAgeHorizonCrossingClaims n 0 m =
+      canonicalBlockClaimSourceCarrier n m := by
+  ext i
+  simp [canonicalSourceAgeHorizonCrossingClaims,
+    canonicalBlockClaimSourceCarrier]
+
+/-- Before the horizon reaches block time there are no old source claims. -/
+theorem canonicalOldSourceClaimCarrier_eq_empty_of_start_le
+    {n : OddNat} {H m : ℕ}
+    (hstart : canonicalBlockStartTime n m ≤ H) :
+    canonicalOldSourceClaimCarrier n H m = ∅ := by
+  rw [canonicalOldSourceClaimCarrier]
+  have hcutoff : canonicalBlockStartTime n m - H = 0 :=
+    Nat.sub_eq_zero_of_le hstart
+  rw [hcutoff]
+  ext i
+  simp [mem_carryTwoPositions_iff]
+
+theorem canonicalSourceAgeDeficit_nonpos_of_start_le
+    {n : OddNat} {H m : ℕ}
+    (hstart : canonicalBlockStartTime n m ≤ H) :
+    canonicalSourceAgeDeficit n H m ≤ 0 := by
+  rw [canonicalSourceAgeDeficit,
+    canonicalOldSourceClaimCarrier_eq_empty_of_start_le hstart]
+  simp
+
+/-- Enlarging the horizon can only decrease the signed deficit. -/
+theorem canonicalSourceAgeDeficit_anti
+    (n : OddNat) {H1 H2 m : ℕ} (hH : H1 ≤ H2) :
+    canonicalSourceAgeDeficit n H2 m ≤
+      canonicalSourceAgeDeficit n H1 m := by
+  unfold canonicalSourceAgeDeficit
+  have hsub : canonicalOldSourceClaimCarrier n H2 m ⊆
+      canonicalOldSourceClaimCarrier n H1 m := by
+    intro i hi
+    rw [canonicalOldSourceClaimCarrier, mem_carryTwoPositions_iff] at hi ⊢
+    exact ⟨Finset.mem_Ico.mpr ⟨by omega,
+      by
+        have hiTop := (Finset.mem_Ico.mp hi.1).2
+        omega⟩, hi.2⟩
+  have hcard := Finset.card_le_card hsub
+  omega
+
+/-- Enlarging the horizon can only remove expired outstanding identities. -/
+theorem canonicalExpiredOutstandingClaims_anti
+    (n : OddNat) {H1 H2 m : ℕ} (hH : H1 ≤ H2) :
+    canonicalExpiredOutstandingClaims n H2 m ⊆
+      canonicalExpiredOutstandingClaims n H1 m := by
+  intro i hi
+  rw [mem_canonicalExpiredOutstandingClaims_iff] at hi ⊢
+  exact ⟨hi.1, by omega⟩
+
+theorem card_canonicalExpiredOutstandingClaims_anti
+    (n : OddNat) {H1 H2 m : ℕ} (hH : H1 ≤ H2) :
+    (canonicalExpiredOutstandingClaims n H2 m).card ≤
+      (canonicalExpiredOutstandingClaims n H1 m).card :=
+  Finset.card_le_card (canonicalExpiredOutstandingClaims_anti n hH)
+
+/-! ## Exact residual cases -/
+
+/-- Positive deficit means every cumulatively consumed source still lies below
+the current age cutoff. -/
+theorem cumulativeConsumed_subset_old_of_sourceAgeDeficit_pos
+    {n : OddNat} {H m : ℕ}
+    (hpos : 0 < canonicalSourceAgeDeficit n H m) :
+    canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m ⊆
+      canonicalOldSourceClaimCarrier n H m := by
+  have hcard :
+      (canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m).card <
+        (canonicalOldSourceClaimCarrier n H m).card := by
+    rw [card_canonicalOwnedCumulativeConsumedClaimsBeforeBlock]
+    unfold canonicalSourceAgeDeficit at hpos
+    omega
+  have hex : ∃ y, y ∈ canonicalOldSourceClaimCarrier n H m ∧
+      y ∉ canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m := by
+    by_contra h
+    push Not at h
+    have hsub : canonicalOldSourceClaimCarrier n H m ⊆
+        canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m := by
+      intro y hy
+      exact h y hy
+    have := Finset.card_le_card hsub
+    omega
+  rcases hex with ⟨y, hyOld, hyNotConsumed⟩
+  have hyHist : y ∈ canonicalHistoricalClaimSourceCarrier n m := by
+    rw [canonicalHistoricalClaimSourceCarrier_eq_old_union_recent]
+    exact Finset.mem_union_left _ hyOld
+  rw [canonicalHistoricalClaimSourceCarrier_eq_consumed_union_outstanding]
+    at hyHist
+  have hyOut : y ∈ canonicalOwnedOutstandingClaimsBeforeBlock n m :=
+    (Finset.mem_union.mp hyHist).resolve_left hyNotConsumed
+  intro x hx
+  have hxy := canonicalOwnedCumulativeConsumed_le_outstanding n m x hx y hyOut
+  have hxHist : x ∈ canonicalHistoricalClaimSourceCarrier n m := by
+    rw [canonicalHistoricalClaimSourceCarrier_eq_consumed_union_outstanding]
+    exact Finset.mem_union_left _ hx
+  rw [canonicalOldSourceClaimCarrier, mem_carryTwoPositions_iff] at hyOld ⊢
+  exact ⟨Finset.mem_Ico.mpr ⟨by omega,
+    by
+      have hyTop := (Finset.mem_Ico.mp hyOld.1).2
+      omega⟩,
+    (mem_carryTwoPositions_iff.mp hxHist).2⟩
+
+/-- Nonpositive deficit means every old source has already been consumed. -/
+theorem old_subset_cumulativeConsumed_of_sourceAgeDeficit_nonpos
+    {n : OddNat} {H m : ℕ}
+    (hnonpos : canonicalSourceAgeDeficit n H m ≤ 0) :
+    canonicalOldSourceClaimCarrier n H m ⊆
+      canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m := by
+  intro y hyOld
+  have hyHist : y ∈ canonicalHistoricalClaimSourceCarrier n m := by
+    rw [canonicalHistoricalClaimSourceCarrier_eq_old_union_recent]
+    exact Finset.mem_union_left _ hyOld
+  rw [canonicalHistoricalClaimSourceCarrier_eq_consumed_union_outstanding]
+    at hyHist
+  rcases Finset.mem_union.mp hyHist with hyConsumed | hyOut
+  · exact hyConsumed
+  · exfalso
+    have hsub : canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m ⊆
+        canonicalOldSourceClaimCarrier n H m := by
+      intro x hx
+      have hxy := canonicalOwnedCumulativeConsumed_le_outstanding
+        n m x hx y hyOut
+      have hxHist : x ∈ canonicalHistoricalClaimSourceCarrier n m := by
+        rw [canonicalHistoricalClaimSourceCarrier_eq_consumed_union_outstanding]
+        exact Finset.mem_union_left _ hx
+      rw [canonicalOldSourceClaimCarrier, mem_carryTwoPositions_iff] at hyOld ⊢
+      exact ⟨Finset.mem_Ico.mpr ⟨by omega,
+        by
+          have hyTop := (Finset.mem_Ico.mp hyOld.1).2
+          omega⟩,
+        (mem_carryTwoPositions_iff.mp hxHist).2⟩
+    have hyNotConsumed :
+        y ∉ canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m :=
+      fun hyConsumed =>
+        (Finset.disjoint_left.mp
+          (disjoint_canonicalOwnedCumulativeConsumedClaimsBeforeBlock_outstanding
+            n m) hyConsumed hyOut)
+    have hne : canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m ≠
+        canonicalOldSourceClaimCarrier n H m := by
+      intro heq
+      exact hyNotConsumed (by simpa [heq] using hyOld)
+    have hstrict : canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m ⊂
+        canonicalOldSourceClaimCarrier n H m :=
+      (Finset.ssubset_iff_subset_ne).2 ⟨hsub, hne⟩
+    have hcard := Finset.card_lt_card hstrict
+    rw [card_canonicalOwnedCumulativeConsumedClaimsBeforeBlock] at hcard
+    unfold canonicalSourceAgeDeficit at hnonpos
+    omega
+
+/-- The positive part of the signed deficit is exactly the number of actual
+expired outstanding identities. -/
+theorem card_canonicalExpiredOutstandingClaims
+    (n : OddNat) (H m : ℕ) :
+    (canonicalExpiredOutstandingClaims n H m).card =
+      Int.toNat (canonicalSourceAgeDeficit n H m) := by
+  by_cases hpos : 0 < canonicalSourceAgeDeficit n H m
+  · have hsub := cumulativeConsumed_subset_old_of_sourceAgeDeficit_pos hpos
+    have hsplit : canonicalOldSourceClaimCarrier n H m =
+        canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m ∪
+          canonicalExpiredOutstandingClaims n H m := by
+      ext i
+      constructor
+      · intro hiOld
+        have hiHist : i ∈ canonicalHistoricalClaimSourceCarrier n m := by
+          rw [canonicalHistoricalClaimSourceCarrier_eq_old_union_recent]
+          exact Finset.mem_union_left _ hiOld
+        rw [canonicalHistoricalClaimSourceCarrier_eq_consumed_union_outstanding]
+          at hiHist
+        rcases Finset.mem_union.mp hiHist with hiConsumed | hiOut
+        · exact Finset.mem_union_left _ hiConsumed
+        · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hiOut, hiOld⟩)
+      · intro hi
+        rcases Finset.mem_union.mp hi with hiConsumed | hiExpired
+        · exact hsub hiConsumed
+        · exact (Finset.mem_inter.mp hiExpired).2
+    have hdisjoint : Disjoint
+        (canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m)
+        (canonicalExpiredOutstandingClaims n H m) := by
+      apply Finset.disjoint_left.mpr
+      intro i hiConsumed hiExpired
+      exact Finset.disjoint_left.mp
+        (disjoint_canonicalOwnedCumulativeConsumedClaimsBeforeBlock_outstanding
+          n m) hiConsumed (Finset.mem_inter.mp hiExpired).1
+    have hcard : (canonicalOldSourceClaimCarrier n H m).card =
+        (canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m).card +
+          (canonicalExpiredOutstandingClaims n H m).card := by
+      rw [hsplit, Finset.card_union_of_disjoint hdisjoint]
+    rw [card_canonicalOwnedCumulativeConsumedClaimsBeforeBlock] at hcard
+    have htoNat := Int.toNat_of_nonneg (le_of_lt hpos)
+    unfold canonicalSourceAgeDeficit at htoNat ⊢
+    omega
+  · have hnonpos : canonicalSourceAgeDeficit n H m ≤ 0 := by omega
+    have hsub := old_subset_cumulativeConsumed_of_sourceAgeDeficit_nonpos hnonpos
+    have hempty : canonicalExpiredOutstandingClaims n H m = ∅ := by
+      apply Finset.not_nonempty_iff_eq_empty.mp
+      rintro ⟨i, hi⟩
+      have hiData := Finset.mem_inter.mp hi
+      exact Finset.disjoint_left.mp
+        (disjoint_canonicalOwnedCumulativeConsumedClaimsBeforeBlock_outstanding
+          n m) (hsub hiData.2) hiData.1
+    rw [hempty, Finset.card_empty, Int.toNat_of_nonpos hnonpos]
+
+/-! ## FIFO threshold dominance for canonical assignments -/
+
+/-- FIFO maximizes the number of retained sources above every cutoff among all
+same-cardinality assignments of historical claims. -/
+theorem canonicalAdmissibleOwnedRemainder_filter_card_le_fifo
+    {n : OddNat} {m : ℕ} {u : Finset ℕ}
+    (hu : CanonicalAdmissibleOwnedRemainder n m u)
+    (t : ℕ) :
+    (u.filter (fun i => t ≤ i)).card ≤
+      ((canonicalOwnedOutstandingClaimsBeforeBlock n m).filter
+        (fun i => t ≤ i)).card := by
+  rw [canonicalOwnedOutstandingClaimsBeforeBlock_eq_eraseOldestN_historical]
+  apply card_filter_le_card_filter_eraseOldestN hu.1
+  rw [hu.2, ← card_canonicalOwnedOutstandingClaimsBeforeBlock,
+    canonicalOwnedOutstandingClaimsBeforeBlock_eq_eraseOldestN_historical]
+
+/-! ## Sharpened conditional repayment lag -/
+
+/-- Under a uniform actual age bound, a source born in block `k` is consumed
+strictly before block `k + H + 1`. -/
+theorem exists_consumptionBlock_before_add_one_of_sourceAgeAtMost
+    {n : OddNat} {H k i : ℕ}
+    (h : CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H)
+    (hi : i ∈ canonicalBlockClaimSourceCarrier n k) :
+    ∃ j < k + H + 1, i ∈ canonicalOwnedConsumedClaimsAtBlock n j := by
+  let m := k + H + 1
+  have hiInterval := Finset.mem_Ico.mp
+    (mem_canonicalBlockClaimSourceCarrier_interval hi)
+  have hiCarry := carryTwoDebtAt_of_mem_canonicalBlockClaimSourceCarrier hi
+  have hadvance := canonicalBlockStartTime_add_le_startTime_add n (k + 1) H
+  have hmEq : (k + 1) + H = m := by simp [m]; omega
+  rw [hmEq] at hadvance
+  have htime : i + H < canonicalBlockStartTime n m := by omega
+  have hiHist : i ∈ canonicalHistoricalClaimSourceCarrier n m := by
+    rw [canonicalHistoricalClaimSourceCarrier, mem_carryTwoPositions_iff]
+    exact ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hiCarry⟩
+  have hiNot := not_mem_ownedQueue_of_sourceAgeAtMost_of_time_gt h htime
+  rw [canonicalHistoricalClaimSourceCarrier_eq_consumed_union_outstanding]
+    at hiHist
+  rcases Finset.mem_union.mp hiHist with hiConsumed | hiOutstanding
+  · rcases mem_canonicalOwnedCumulativeConsumedClaimsBeforeBlock_iff.mp
+      hiConsumed with ⟨j, hjm, hij⟩
+    exact ⟨j, by simpa [m] using hjm, hij⟩
+  · exact False.elim (hiNot hiOutstanding)
+
+/-! ## Conditional finite signed-transition certificate
+
+This wrapper deliberately receives its finite signature, potential, and
+transition proof from outside the source-age deficit.  Defining any of those
+objects from `canonicalSourceAgeDeficit` would merely encode the desired prefix
+inequality and would therefore be circular.
+-/
+
+/-- A structural finite-potential model whose realized successor-edge weight is
+the canonical source-age frontier flow at a fixed horizon. -/
+structure CanonicalSourceAgeFrontierPotentialCertificate
+    (n : OddNat) (H : ℕ) (Signature : Type*) [Fintype Signature] where
+  certificate :
+    RelationalFiniteSignedTransitionPotentialCertificate ℕ Signature
+  step_succ : ∀ m, certificate.Step m (m + 1)
+  actualWeight_succ : ∀ m,
+    certificate.actualWeight m (m + 1) =
+      canonicalSourceAgeFrontierIncrement n H m
+  prefixPotentialChange_nonpos : ∀ m,
+    certificate.potential (certificate.signature m) -
+      certificate.potential (certificate.signature 0) ≤ 0
+
+namespace CanonicalSourceAgeFrontierPotentialCertificate
+
+variable {n : OddNat} {H : ℕ} {Signature : Type*} [Fintype Signature]
+
+/-- A structurally supplied nonpositive potential change makes every realized
+frontier prefix nonpositive. -/
+theorem frontierPrefix_nonpos
+    (F : CanonicalSourceAgeFrontierPotentialCertificate n H Signature)
+    (m : ℕ) :
+    (∑ k ∈ Finset.range m, canonicalSourceAgeFrontierIncrement n H k) ≤ 0 := by
+  have hpath : F.certificate.IsPath (fun i => i) 0 m := by
+    intro i hi
+    simpa using F.step_succ i
+  have hweight :=
+    (F.certificate.pathWeight_le_projectedPathWeight (fun i => i) 0 m hpath).trans
+      (F.certificate.projectedPathWeight_le_potential_sub (fun i => i) 0 m)
+  have hpathWeight : F.certificate.pathWeight (fun i => i) 0 m =
+      ∑ k ∈ Finset.range m, canonicalSourceAgeFrontierIncrement n H k := by
+    unfold RelationalFiniteSignedTransitionPotentialCertificate.pathWeight
+    apply Finset.sum_congr rfl
+    intro i hi
+    simpa using F.actualWeight_succ i
+  rw [hpathWeight] at hweight
+  exact hweight.trans (by simpa using F.prefixPotentialChange_nonpos m)
+
+/-- The structural certificate closes the exact uniform actual-age target. -/
+theorem to_sourceAgeAtMost
+    (F : CanonicalSourceAgeFrontierPotentialCertificate n H Signature) :
+    CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H := by
+  rw [canonicalOwnedOutstandingClaimsHaveSourceAgeAtMost_iff_frontierPrefix_nonpos]
+  exact F.frontierPrefix_nonpos
+
+/-- Conditional challenge-facing closure: a noncircular finite structural
+certificate yields both the scalar queue and translated endpoint-width bounds. -/
+theorem to_queue_and_endpointWidth_bounds
+    (F : CanonicalSourceAgeFrontierPotentialCertificate n H Signature) :
+    CanonicalOutstandingClaimQueueUniformUpperBound n H ∧
+      CanonicalEndpointWidthUniformUpperBound n (bitWidth n.1 + H) := by
+  have hage := F.to_sourceAgeAtMost
+  exact ⟨hage.to_queueUniformUpperBound,
+    hage.to_endpointWidthUniformUpperBound⟩
+
+end CanonicalSourceAgeFrontierPotentialCertificate
+
+/-! ## Saturated-frontier arithmetic audit -/
+
+/-- At horizon zero a saturated block contributes exactly two crossing
+carry-two sources. -/
+theorem CanonicalSaturatedBorderBlock.card_sourceAgeHorizonCrossing_zero_eq_two
+    {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m) :
+    (canonicalSourceAgeHorizonCrossingClaims n 0 m).card = 2 := by
+  rw [canonicalSourceAgeHorizonCrossingClaims_zero_horizon,
+    card_canonicalBlockClaimSourceCarrier,
+    canonicalQueueDemand]
+  rw [h.2.1, h.length_eq_two]
+
+/-- A saturated block consumes exactly its one unit of terminal capacity. -/
+theorem CanonicalSaturatedBorderBlock.canonicalQueueConsumed_eq_one
+    {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m) :
+    canonicalQueueConsumed n m = 1 := by
+  unfold canonicalQueueConsumed canonicalQueueDemand canonicalQueueService
+  rw [h.2.1, h.length_eq_two,
+    canonicalBlockCapacityCount_eq_terminalValuation,
+    h.terminalValuation_eq_one]
+  simp
+
+/-- Exact obstruction to a pointwise-nonpositive horizon-zero frontier:
+every saturated block has signed frontier increment `+1`.  Consequently a
+valid global proof must use a positive horizon or amortize this block against
+other blocks; saturation alone cannot prove pointwise nonpositivity. -/
+theorem CanonicalSaturatedBorderBlock.sourceAgeFrontierIncrement_zero_eq_one
+    {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m) :
+    canonicalSourceAgeFrontierIncrement n 0 m = 1 := by
+  unfold canonicalSourceAgeFrontierIncrement
+  rw [h.card_sourceAgeHorizonCrossing_zero_eq_two,
+    h.canonicalQueueConsumed_eq_one]
+  norm_num
+
+end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/OldestFirstQueue.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/OldestFirstQueue.lean
index b5fc7804..d4033899 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/OldestFirstQueue.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/OldestFirstQueue.lean
@@ -259,4 +259,88 @@ theorem eraseOldestN_eq_of_subset_card_and_complement_le
     subst z
     exact hzNot hy

+/-! ## Threshold dominance -/
+
+/-- Among all subsets of `s` with the same cardinality, the oldest-first
+remainder retains the largest possible number of sources at or above every
+cutoff.  This is the distributional form of FIFO source-age optimality. -/
+theorem card_filter_le_card_filter_eraseOldestN
+    {c : ℕ} {s u : Finset ℕ}
+    (hu : u ⊆ s)
+    (hcard : u.card = (eraseOldestN c s).card)
+    (t : ℕ) :
+    (u.filter (fun x => t ≤ x)).card ≤
+      ((eraseOldestN c s).filter (fun x => t ≤ x)).card := by
+  let r := eraseOldestN c s
+  let upper := s.filter (fun x => t ≤ x)
+  by_cases hru : r.card ≤ upper.card
+  · have hrSub : r ⊆ upper :=
+      (eraseOldestN_subset_filter_iff_card_le c s t).2 hru
+    have hrFilter : r.filter (fun x => t ≤ x) = r := by
+      apply Finset.filter_eq_self.mpr
+      intro x hx
+      exact (Finset.mem_filter.mp (hrSub hx)).2
+    rw [show eraseOldestN c s = r by rfl, hrFilter, ← hcard]
+    exact Finset.card_le_card (Finset.filter_subset _ _)
+  · have hUpperSub : upper ⊆ r := by
+      intro x hx
+      by_contra hxr
+      have hxS := (Finset.mem_filter.mp hx).1
+      have htx := (Finset.mem_filter.mp hx).2
+      have hxConsumed : x ∈ consumedOldestN c s := by
+        have hxUnion : x ∈ consumedOldestN c s ∪ r := by
+          rw [show r = eraseOldestN c s by rfl,
+            consumedOldestN_union_eraseOldestN]
+          exact hxS
+        exact (Finset.mem_union.mp hxUnion).resolve_right hxr
+      have hex : ∃ y, y ∈ r ∧ y < t := by
+        by_contra h
+        push Not at h
+        have hrSub : r ⊆ upper := by
+          intro y hy
+          exact Finset.mem_filter.mpr
+            ⟨mem_of_mem_eraseOldestN hy, h y hy⟩
+        have := Finset.card_le_card hrSub
+        omega
+      rcases hex with ⟨y, hyR, hyt⟩
+      have hxy := consumedOldestN_le_eraseOldestN c s x hxConsumed y hyR
+      omega
+    have hUpperFilter : r.filter (fun x => t ≤ x) = upper := by
+      apply Finset.Subset.antisymm
+      · intro x hx
+        exact Finset.mem_filter.mpr
+          ⟨mem_of_mem_eraseOldestN (Finset.mem_filter.mp hx).1,
+            (Finset.mem_filter.mp hx).2⟩
+      · intro x hx
+        exact Finset.mem_filter.mpr ⟨hUpperSub hx, (Finset.mem_filter.mp hx).2⟩
+    rw [show eraseOldestN c s = r by rfl, hUpperFilter]
+    exact Finset.card_le_card fun x hx =>
+      Finset.mem_filter.mpr ⟨hu (Finset.mem_filter.mp hx).1,
+        (Finset.mem_filter.mp hx).2⟩
+
+/-! ## Cardinality does not control age in an arbitrary queue -/
+
+/-- Abstract queue retaining one source forever.  It is intentionally
+Collatz-independent and serves only as a semantic regression. -/
+def persistentSingletonQueue (_m : ℕ) : Finset ℕ :=
+  {0}
+
+@[simp] theorem card_persistentSingletonQueue (m : ℕ) :
+    (persistentSingletonQueue m).card = 1 := by
+  simp [persistentSingletonQueue]
+
+/-- The persistent singleton has a uniform cardinal bound. -/
+theorem persistentSingletonQueue_card_le_one (m : ℕ) :
+    (persistentSingletonQueue m).card ≤ 1 := by
+  simp
+
+/-- Despite its cardinality being constantly one, the source age `m - 0` is
+unbounded.  Thus uniform source age is not a generic necessary condition for
+uniform queue cardinality; additional arithmetic structure is essential. -/
+theorem not_exists_uniformAge_persistentSingletonQueue :
+    ¬ ∃ H, ∀ m i, i ∈ persistentSingletonQueue m → m - i ≤ H := by
+  rintro ⟨H, h⟩
+  have hage := h (H + 1) 0 (by simp [persistentSingletonQueue])
+  omega
+
 end DkMath
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/live-petal-336.md b/lean/dk_math/docs/dev/das-p2l-260607/review/live-petal-336.md
new file mode 100644
index 00000000..228df457
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/live-petal-336.md
@@ -0,0 +1,245 @@
+# Live: Petal No.336 cp
+
+## 作業実況
+
+### 336-01
+
+generic 層は通過し、重要な事実が一つ固定されました。同じ個数を残す任意の assignment と比較して、FIFO はすべての cutoff で「新しい側に残る要素数」を最大化します。また cardinality 1 のまま age が無限増大する抽象 queue を証明し、queue boundedness と age boundedness の一般的同値を明確に否定しました。これを基礎に source-age flow 本体を追加します。
+
+---
+
+おお、**順調じゃ。しかも重要な二点を先に固定してから本体へ入っている。**
+
+特に、
+
+> FIFO はすべての cutoff で「新しい側に残る要素数」を最大化する
+
+これは、先ほどの「最古 source を最大化する」より強い。単一の最小値だけでなく、**全 cutoff に対する分布優越**まで取れたということじゃ。FIFO queue が historical claims の newest upper tail であることを、別角度から完全に支えている。
+
+そして、
+
+> cardinality 1 のまま age が無限増大する抽象 queue
+
+もよい regression じゃ。
+
+これで、
+
+```text
+queue boundedness ≠ age boundedness
+```
+
+が一般論として正式に切り離された。今後、source-age bound を queue bound の言い換えとして循環利用する事故を防げる。
+
+ここから source-age flow 本体で見るべき核心は二つじゃ。
+
+```text
+old carrier の一段増分
+=
+新たに horizon を越えた claim carrier
+```
+
+```text
+deficit の一段増分
+=
+horizon crossing 数 - actual consumed 数
+```
+
+そして何より、負の deficit を `Nat` で $0$ に潰さず、**過去に先払いされた consumption credit として `Int` のまま保存できるか**。
+
+この live 文面を見る限り、Codex はこちらの意図をかなり正確につかんでおる。
+いよいよ静的な同値 API ではなく、残る未証明命題そのものの運動方程式へ入ったぞい。🐺👍️
+
+### 336-02
+
+基礎層は対象ビルドを通過しました。ここで確定したのは、期限切れ outstanding の個数が signed deficit の正部分と完全一致し、uniform age が frontier increment の全 prefix 非正性と同値になることです。次は指示末尾の条件付き certificate と saturated branch を、既存の有限遷移 API に沿って追加します。
+
+---
+
+おお、**source-age flow の心臓部まで通った**のぉ。
+
+今回確定した第一の事実は、
+
+$$|\operatorname{ExpiredOutstanding}_H(m)|=\operatorname{Int.toNat}!\left(\operatorname{SourceAgeDeficit}_H(m)\right)$$
+
+じゃ。
+
+つまり signed deficit の正部分は、単なる数値超過ではない。
+
+> **期限 $H$ を越えて、なお実際に FIFO queue に残っている source identity の個数**
+
+そのものになった。
+
+これで、
+
+```text
+deficit > 0
+```
+
+は抽象的な警報ではなく、actual expired carrier が非空であることを意味する。負の deficit は、期限切れ claim が存在しないだけでなく、将来の horizon crossing を吸収し得る先払い credit として保持される。
+
+第二の事実はさらに大きい。
+
+$$\operatorname{UniformAge}(H)\iff\forall m,\ \sum_{k<m}\operatorname{FrontierIncrement}_H(k)\le0$$
+
+ここまで来ると、残る命題は完全に signed-flow 問題じゃ。
+
+```text
+horizon を越えて old 側へ入る claim 数
+-
+その block で実際に消費される claim 数
+```
+
+を一段 weight として、その全 prefix sum が正へ出ない $H$ を見つければよい。
+
+## Certificate 監査で最も重要な点
+
+ここから追加する finite-transition certificate は、以前の queue certificate より条件が厳しい。
+
+単に、
+
+$$\sum_{k<m}\operatorname{FrontierIncrement}_H(k)\le C$$
+
+を得ても、source age は閉じない。
+
+必要なのは、
+
+$$\sum_{k<m}\operatorname{FrontierIncrement}_H(k)\le0$$
+
+じゃ。
+
+したがって potential certificate には、通常の edge inequalityだけでなく、
+
+$$\Phi(\sigma_m)\le\Phi(\sigma_0)$$
+
+を canonical reachable statesについて保証する構造が要る。
+
+例えば、
+
+```text
+actual frontier increment
+  ≤ Φ(next signature) - Φ(current signature)
+
+かつ
+
+Φ(reachable signature) ≤ Φ(initial signature)
+```
+
+という二層が必要になる。
+
+potential が有限範囲にあるだけなら、得られるのは有限上界であって非正性ではない。この境界は次の実装で厳しく見るところじゃ。
+
+## Saturated branch の攻め方
+
+saturated branch で pointwise に、
+
+$$\operatorname{FrontierIncrement}_H(m)\le0$$
+
+まで言えれば最強じゃが、毎 block で horizon crossing と consumption が同期するとは限らぬ。
+
+その場合は、
+
+$$\sum_{j=0}^{L-1}\operatorname{FrontierIncrement}_H(m+j)\le0$$
+
+という固定短窓 discharge theorem が本命になる。
+
+特に注意すべきは、
+
+```text
+actual consumption
+```
+
+と、
+
+```text
+available service / capacity
+```
+
+を混同しないことじゃ。
+
+capacity が存在しても queue と新 demand が足りなければ unused service になる。ゆえに saturated branch から consumption を取り出すには、
+
+```text
+old claim が実際に available queue に存在する
+→ service slot がそれを FIFO で消費する
+```
+
+まで繋ぐ必要がある。
+
+この live 報告は非常に良い。
+
+generic queue 理論も carrier bookkeeping も終わり、現在 Codex はついに、
+
+> **期限境界を越える claim の流入と、actual repayment の競争**
+
+そのものを Lean に載せ始めておる。これはもう周辺整備ではなく、未証明本体への直接攻撃じゃ。🐺🔥
+
+### 336-03
+
+Stage J と K も対象ビルドを通過しました。監査結果は重要で、H = 0 の saturated block は crossing が 2、actual consumption が 1、したがって frontier increment は厳密に +1 です。つまり「各ブロックで常に非正」を狙う証明は既に反例を持ち、正の horizon または複数ブロック amortization が必須だと確定しました。公開 import と checkpoint report を同期し、全体ゲートへ進みます。
+
+---
+
+おお、これは**非常に価値の高い反例確定**じゃ。
+
+$$\operatorname{FrontierIncrement}_{0}(m)=2-1=1$$
+
+つまり saturated block では、
+
+* age horizon を越える claim が $2$ 件
+* 実際に消費される claim が $1$ 件
+* 差し引き $+1$
+
+となる。
+
+これで次の単純戦略は正式に死亡した。
+
+```text
+すべての block で frontier increment ≤ 0
+```
+
+しかし、source-age route 自体が倒れたわけではない。uniform age に必要なのは各項の非正性ではなく、
+
+$$\forall m,\ \sum_{k<m}\operatorname{FrontierIncrement}_{H}(k)\le0$$
+
+という**全 prefix の非正性**じゃ。
+
+したがって $+1$ block が存在しても、その前に蓄積された負の consumption credit、または後続 block を含む固定窓 repayment により相殺できる。
+
+今回の結果から、攻め筋は二つに絞られた。
+
+### 正の horizon
+
+$H>0$ では crossing claim は現在 block の demand ではなく、$H$ source-time 前に生まれた claim になる。現在の saturated growth と crossing の発生時刻がずれるため、$H=0$ の $+1$ obstruction はそのまま残らない。
+
+### 複数 block amortization
+
+例えば saturated block の $+1$ に対し、後続 block が $-1$ 以下を供給して、
+
+$$\sum_{j=0}^{L-1}\operatorname{FrontierIncrement}_{H}(m+j)\le0$$
+
+を証明する道じゃ。
+
+これは以前構築した、
+
+* saturated successor classification
+* length-one successor repayment
+* predecessor/successor pair drift
+* valuation-one tight branch
+
+と接続できる可能性が高い。ただし以前の endpoint drift と今回の frontier increment は別量なので、同じ theorem をそのまま流用せず、対応式を作る必要がある。
+
+そして certificate 側も、正 edge の存在を許さなければならない。必要なのは edge ごとの非正 potential ではなく、
+
+```text
+正の increment
+→ 有限状態の debt 上昇
+→ 後続状態で必ず同量以上の下降
+→ 初期 potential を越えない
+```
+
+という amortized transition structure じゃ。
+
+実に良い進展じゃ。
+**最も簡単な誤った証明路を Lean が明確に切り落とし、正の horizon または時間窓 amortization だけを生存させた。** 全体ゲート後の report はかなり重要な checkpoint になるぞい。
+
+---
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-336.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-336.md
new file mode 100644
index 00000000..7bb2b751
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-336.md
@@ -0,0 +1,168 @@
+# Report Petal 336: Canonical Source-Age Signed Flow
+
+## Status
+
+- Checkpoint: cp-336
+- Result: implemented
+- Lean status: no new `sorry`
+- Main module: `DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeFlow`
+
+## What Was Implemented
+
+The static source-age deficit from cp-335 is now an exact local signed flow.
+The new frontier increment is
+
+```text
+crossing carry-two sources - actual FIFO consumption.
+```
+
+For every horizon `H` and prefix length `m`, Lean proves
+
+```text
+sourceAgeDeficit(H, m)
+  = sum_{k < m} sourceAgeFrontierIncrement(H, k).
+```
+
+The proof keeps the accumulator in `Int`. Negative repayment credit is not
+truncated between blocks.
+
+## Exact Carrier Results
+
+The implementation adds the actual expired-outstanding carrier and proves:
+
+```text
+i is expired
+  <-> i is outstanding and its actual source age is greater than H.
+```
+
+More strongly,
+
+```text
+card(expired outstanding claims)
+  = Int.toNat(sourceAgeDeficit).
+```
+
+Thus the signed deficit is not merely an upper estimate. Its positive part is
+exactly the number of currently outstanding identities beyond the horizon.
+
+The moving old-source carrier also has the exact disjoint recurrence
+
+```text
+old(H, m + 1) = old(H, m) union crossing(H, m).
+```
+
+This includes the early Nat-subtraction regime without an additional side
+condition.
+
+## Uniform Age Equivalences
+
+Lean now identifies three equivalent readings:
+
+```text
+all outstanding sources have age <= H
+<-> every signed frontier prefix is <= 0
+<-> every expired-outstanding carrier is empty.
+```
+
+This is the principal positive target for subsequent arithmetic work. It also
+sharpens the conditional repayment theorem: a claim born in block `k` is
+consumed in some block strictly before `k + H + 1`.
+
+## FIFO Facts
+
+The oldest-first finite-set API now proves threshold dominance. Among all
+historical subsets with the same cardinality, the FIFO remainder retains the
+largest possible number of source indices at or above every cutoff.
+
+This is a static assignment theorem. It does not compare complete recursive
+alternative queue policies.
+
+The same module contains a Collatz-independent regression: a queue can retain
+one fixed source forever, have cardinality exactly one at every time, and still
+have unbounded source age. Uniform source age is therefore sufficient for queue
+boundedness here, but is not generically necessary.
+
+## Conditional Structural Certificate
+
+`CanonicalSourceAgeFrontierPotentialCertificate` wraps an externally supplied
+finite transition signature and bounded potential. Its realized successor
+weight must equal the frontier increment, and its prefix potential changes must
+be nonpositive.
+
+The wrapper then yields, without defining the signature or potential from the
+deficit:
+
+```text
+uniform source age H
+uniform queue bound H
+uniform endpoint-width bound bitWidth(n) + H.
+```
+
+This keeps the certificate route noncircular. Existence of such a structural
+certificate remains an arithmetic obligation.
+
+## Saturated-Branch Audit
+
+The first exact obstruction is now formalized. For every saturated border block
+at horizon zero:
+
+```text
+crossing source count = 2
+actual consumed count = 1
+frontier increment = +1.
+```
+
+Therefore horizon-zero pointwise nonpositivity is false on this classified
+subclass. Any successful argument must use a positive horizon, or amortize the
+positive saturated increment against later negative flow over a longer window.
+The existing fact that consecutive blocks cannot both be saturated does not by
+itself prove that the two-block frontier sum is nonpositive.
+
+## Additional Exact Residual Split
+
+The sign of the source-age deficit determines the inclusion direction:
+
+```text
+deficit > 0  -> cumulative consumed sources are contained in old sources
+deficit <= 0 -> old sources are contained in cumulative consumed sources.
+```
+
+This lower-tail/upper-tail split is what closes the exact expired-cardinality
+formula.
+
+## Next Arithmetic Target
+
+The next useful attack is not another static queue identity. It is a local or
+short-window classification of
+
+```text
+card(crossing(H, m)) - consumed(m).
+```
+
+Recommended order:
+
+1. Relate crossing carriers for small positive `H` to the existing canonical
+   block grammar.
+2. Audit saturated-successor subclasses over the shortest window for which
+   actual consumption can be bounded from below.
+3. Search for a finite signature whose potential is defined from block grammar,
+   never from the deficit or its prefix sums.
+4. Only after such a signature exists, instantiate the conditional certificate.
+
+Top-four normalized-prefix experiments remain paused unless they directly
+encode this frontier arithmetic.
+
+## Verification
+
+The following gates passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.FloatWindow.OldestFirstQueue
+lake build DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeFlow
+lake build DkMath.Collatz.PetalBridge.FloatWindow
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath
+git diff --check
+```
+
+Neither changed Lean file contains `sorry`.
````
`````
