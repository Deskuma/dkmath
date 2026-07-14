# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentRepayment

gch: 8a4a496bd707cbbc30c46b256d9cf003805f4595

## Report

cp-314 を実装しました。

新規 [UniversalPaymentRepayment.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentRepayment.lean) で、次を Lean の事実として固定しています。

- `7` の最初の canonical block drift は `+1`
- 次の block drift は `-1`
- 累積 drift は `0`
- 一時的 overload は実在し、prefix dominance は一般目標ではない
- endpoint balance と bit-width 差は完全に一致
- 任意の block 区間に対する sliding telescope
- backward-credit matching は prefix dominance を導く
- forward-repayment matching を別方向の構造として定義
- claim/capacity carrier の厳密な有限 cardinality
- recovery depth ごとの source は一意な singleton
- complete claim depth 数は delayed claim + immediate claim
- delayed depth は正確に `Icc 2 blockLength`
- levelled capacity depth 数は endpoint capacity と一致
- 一様 balance 上界から canonical endpoint bit-width 上界が従う

重要な結論は、 **数え上げと pressure/claim incidence は閉じた** という点です。残る本質的な問題は、claim depth を将来の capacity depth に割り当てる eligibility invariant と、その injective repayment map の構築です。forward repayment の存在や収束はまだ主張していません。

詳細は [report-petal-314.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-314.md) に記録しました。

検証済み:

- `lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentRepayment`
- `lake build DkMath.Collatz.PetalBridge.FloatWindow`
- `lake build DkMath.Collatz.PetalBridge`
- `lake build DkMath`
- `git diff --check`
- 新規モジュールに `sorry` なし

## Review

## 結論

**採用。大躍進という評価で正しい。**

cp-314 は、単なる補題追加ではない。

これまで別々だった、

- payment block の時間区間
- pressure の recovery depth
- carry-two claim
- endpoint capacity
- 一時的 overload
- 後続 block による返済

を、初めて同じ有限座標系へ載せた。

現在の一 block は、概念的に次の二つの有限集合で表せる。

$$
C_k=\operatorname{canonicalPaymentClaimDepths}(n,k)
$$

$$
S_k=\operatorname{canonicalEndpointCapacityDepthSlots}(n,k)
$$

そして、

$$
|C_k|=R_k+\varepsilon_k
$$

$$
|S_k|=P_k
$$

したがって block drift は、

$$
D_k=|C_k|-|S_k|
$$

と読める。

さらに任意の block 区間 $q,\ldots,m$ について、

$$
\sum_{k=q}^{m}D_k=w_{e_m+1}-w_{b_q}
$$

という sliding telescope まで閉じた。

**局所会計・有限区間会計・depth incidence が一つに合流した checkpoint** じゃ。

ただし、戦略上は三点だけ厳密に補正すべきものがある。

1. 現在の forward matching は「excursion の返済」そのものではなく、有限 claim prefix の future-slot embedding である。
2. delayed claim depths は `Icc 2 blockLength` 全体ではなく、その中の marked subset である。
3. claim の recovery depth と capacity の height level は、同じ自然数で添字づけられた別軸であり、同一視には新しい定理が必要である。

実装の誤りではない。
**次に何を証明すべきかを、さらに正確にする補正**じゃ。

---

## 1. $7$ の regression が戦略を正式に修正した

今回、Lean は軌道 $7$ について、

$$
e_0=2,\qquad e_1=3
$$

$$
D_0=1,\qquad D_1=-1
$$

$$
D_0+D_1=0
$$

を認めた。

これは非常に重要じゃ。

以前の全-prefix dominance は、

$$
\forall m,\quad \sum_{k=0}^{m}D_k\le0
$$

を要求していた。

しかし $7$ では最初の block で、

$$
D_0=1
$$

となる。

その後の block で、

$$
D_1=-1
$$

が入り、基準へ戻る。

したがって Collatz の本物の挙動は、

```text
overload を一度も許さない
```

ではなく、

```text
overload は許される
しかし後続 capacity により返済される
```

じゃ。

cp-314 は、この修正を説明文ではなく Lean theorem にした。

これは大きい。今後、誤った全-prefix 非正路線へ戻ることはない。

---

## 2. endpoint balance が正式な状態量になった

```lean
canonicalEndpointBalanceInt n m
```

は、

$$
B_m:=\sum_{k=0}^{m}D_k
$$

を定義する。

そして、

$$
B_m=w_{e_m+1}-w_0
$$

が証明された。

これで balance は単なる抽象的会計値ではない。

```text
B_m > 0:
  初期 bit width より上

B_m = 0:
  初期 bit width と同じ

B_m < 0:
  初期 bit width より下
```

という、軌道上の実際の位置になった。

`CanonicalEndpointTerminalCapacityDominance` も良い設計じゃ。

これは全ての過去 prefix を要求せず、選んだ endpoint $m$ だけについて、

$$
C_m\le P_m
$$

を要求する。

そして、

$$
C_m\le P_m
\Longleftrightarrow B_m\le0
\Longleftrightarrow w_{e_m+1}\le w_0
$$

となる。

$7$ のように途中で overload しても、後で terminal dominance を回復できる。

---

## 3. sliding telescope は返済解析の中心 API

```lean
sum_endpointAccountingTerm_Icc_eq_bitWidth_sub
```

は cp-314 の中心定理の一つじゃ。

$$
\sum_{k=q}^{m}D_k=w_{e_m+1}-w_{b_q}
$$

これは prefix telescope より本質的に強い。

prefix theorem は初期時刻 $0$ からしか見られなかった。

sliding theorem は、任意の block $q$ を新しい局所原点として扱える。

したがって、

```text
block q で overload 発生
       ↓
q..m の将来 block を観測
       ↓
どこで元の width baseline へ戻るか
```

を直接記述できる。

claims/capacity 版も、

$$
\sum_{k=q}^{m}D_k
=================

## \sum_{k=q}^{m}(R_k+\varepsilon_k)

\sum_{k=q}^{m}P_k
$$

として閉じている。

これが今後の repayment theorem の主幹線になる。

軽微な API 上の点として、

```lean
sum_endpointAccountingTerm_Icc_eq_claims_sub_capacity
```

の `q ≤ m` 仮定は証明内で使われていない。

$q>m$ なら双方空和なので、その theorem は仮定なしで成立する。alias を一つ置いてもよい。

---

## 4. backward / forward の分離は正しい

旧 matching を、

```lean
CanonicalEndpointBackwardCreditMatching
```

として再解釈したのは正しい。

その向きは、

$$
\operatorname{slotBlock}\le\operatorname{claimBlock}
$$

じゃ。

つまり claim は、既に過去に出現していた capacity credit を使う。

したがってこれは、

> 一度も overdraft しないことの証明書

であり、prefix dominance を導く。

一方、新しい、

```lean
CanonicalEndpointForwardRepaymentMatching
```

は、

$$
\operatorname{claimBlock}\le\operatorname{slotBlock}
$$

を要求する。

これにより、未来の endpoint capacity が過去の claim を支払える。

first target と final allocation を混同せず、二方向を別 predicate に分けたのは非常に良い。

---

## 5. ただし現 forward matching は「balance repayment」ではない

ここが今回最も重要な精査点じゃ。

現在の、

```lean
CanonicalEndpointForwardRepaymentMatching n q r
```

は、

> block $0,\ldots,q$ の claims を、block $0,\ldots,r$ の capacity slots へ単射で入れる

構造である。

したがって得られるのは、

$$
C_q\le P_r
$$

じゃ。

しかしこれは、

$$
B_r\le B_{q-1}
$$

を意味しない。

なぜなら $q+1,\ldots,r$ の間に新たに発生した claims が、この matching の domain に入っていないからじゃ。

実際、抽象的に各 block が、

```text
claims   = 2
capacity = 1
```

だとする。

任意の有限 claim prefix $q$ に対して、十分遠い $r$ を取れば、

$$
C_q\le P_r
$$

とできる。

例えば $r=2q+1$ 付近なら総数は足りる。

したがって「全有限 claim prefix はいつか未来 slot へ埋め込める」は成立し得る。

しかし同時に、

$$
B_m=C_m-P_m=m+1
$$

となり、balance は無限に増える。

つまり、

```lean
EveryFiniteCanonicalClaimPrefixEventuallyRepayable
```

は、名前どおり個々の有限 claim 集合の settlement を述べるには使えるが、

- uniform boundedness
- excursion repayment
- balance decay

を単独では導かない。

この predicate は残してよい。
ただし大域目標にはしない方がよい。

より正確な別名なら、

```lean
EveryFiniteCanonicalClaimPrefixHasFutureSlotEmbedding
```

に近い意味じゃ。

---

## 6. 本当の excursion repayment は window matching

block $q$ の直前 balance を、

$$
B_{q^-}:=\operatorname{canonicalEndpointBalanceBefore}(n,q)
$$

とする。

現在の `CanonicalEndpointExcursionRepaidAt n q r` は、

$$
B_r\le B_{q^-}
$$

を要求している。

sliding telescope により、これは正確に、

$$
\sum_{k=q}^{r}D_k\le0
$$

と同値になる。

さらに、

$$
\sum_{k=q}^{r}(R_k+\varepsilon_k)\le\sum_{k=q}^{r}P_k
$$

とも同値じゃ。

したがって本当の repayment matching は、

> block $q,\ldots,r$ で発生した claims 全体を、block $q,\ldots,r$ の capacity slots へ割り当てる

window matching であるべきじゃ。

候補は、

```lean
CanonicalEndpointClaimWindowCarrier n q r
CanonicalEndpointCapacityWindowCarrier n q r
CanonicalEndpointForwardWindowMatching n q r
```

じゃ。

この matching から、

```lean
CanonicalEndpointExcursionRepaidAt n q r
```

が従うように設計する。

そうすれば「claim の settlement」と「balance の repayment」が一致する。

---

## 7. pressure から claim への bridge は本当に閉じた

今回の数学的心臓は、

```lean
canonicalPaymentBlockRecoveryFiber_eq_singleton_sourceAtDepth
```

と、

```lean
canonicalPaymentClaimDepths_eq_image_completeClaimFiber
```

じゃ。

canonical block $k$ の endpoint を $e_k$ とすると、depth $d$ の source は、

$$
i=e_k+1-d
$$

で一意に決まる。

そして有効な depth、

$$
1\le d\le L_k
$$

に対して recovery fiber は singleton になる。

$$
\operatorname{RecoveryFiber}(k,d)={e_k+1-d}
$$

さらに、その唯一の source が carry-two である depth だけを集めると、

$$
C_k=\operatorname{canonicalPaymentClaimDepths}(n,k)
$$

になる。

つまり、

> claim は recovery staircase 上の marked point である

ことが確定した。

これは pressure と accounting の本当の接続じゃ。

cp-313 までは recovery depth の数と claim 数が別々に存在した。

cp-314 では claim 自体が recovery-depth address を持つようになった。

---

## 8. delayed depth に関する表現の補正

上部の要約にある、

```text
delayed depth は正確に Icc 2 blockLength
```

は、少し誤解を招く。

実際に証明されたのは、

$$
\operatorname{DelayedClaimDepths}_k\subseteq[2,L_k]
$$

じゃ。

全ての depth $2,\ldots,L_k$ が delayed claim になるわけではない。

carry-two が立った depth だけが marked される。

正確な等式は、

$$
\operatorname{DelayedClaimDepths}_k
===================================

\operatorname{canonicalPaymentMarkedDebtDepths}_k
$$

である。

report 本文は「lie in `Icc 2 blockLength`」と正しく書かれている。
冒頭要約だけを補正するとよい。

---

## 9. claim depth と capacity level は別軸である

ここが今後の本丸じゃ。

claim 側の $d$ は、

> endpoint まで何段残っていたか

という **時間方向の recovery depth** である。

一方 capacity 側の level $s$ は、

> endpoint で何段の $2$-adic height が露出したか

という **縦方向の valuation level** である。

現在、

$$
C_k\subseteq[1,L_k]
$$

$$
S_k=[2,h_k]
$$

と、どちらも自然数で添字づけられた。

しかし、同じ自然数を使っているからといって、

$$
d=s
$$

で支払えることは自動ではない。

これは、

```text
temporal recovery depth
        ↓
2-adic endpoint height level
```

を結ぶ新しい bridge theorem が必要だということじゃ。

report ではこれを eligibility invariant と呼んでいる。

その診断は正しい。

より明確にするなら、capacity 側の名前は、

```lean
canonicalEndpointCapacityLevelSlots
```

の方がよいかもしれない。

`DepthSlots` と呼ぶと、claim depth と既に同じ軸であるように見えるからじゃ。

---

## 10. immediate claim の level shift

claim depth では、

$$
d=1
$$

が endpoint immediate claim である。

しかし capacity levels は、

$$
2,\ldots,h_k
$$

から始まる。

したがって immediate claim は same-depth slot を使えない。

少なくとも、

```text
immediate claim depth 1
  → lowest capacity level 2
```

という特別な規則が必要になる。

delayed claim $d\ge2$ については、

```text
claim depth d
  → capacity level d
```

という候補が見えている。

$7$ の最初の二 blocks は、この候補ときれいに一致する。

概念的には、

```text
block 0 claims:
  depths 2, 3

block 0 capacity:
  level 2

block 1 claim:
  depth 1

block 1 capacity:
  levels 2, 3
```

として、

```text
block 0 depth 2 → block 0 level 2
block 0 depth 3 → block 1 level 3
block 1 depth 1 → block 1 level 2
```

という allocation ができる。

これは非常に示唆的じゃ。

ただし現時点では一例であり、一般 invariant ではない。
次 checkpoint ではまず、この $7$ の depth-aware matching を Lean で実例化する価値が高い。

---

## 11. excursion predicate の意味

```lean
CanonicalEndpointPositiveExcursionAt n q
```

は現在、

$$
B_{q^-}<B_q
$$

と定義されている。

したがってこれは、

$$
0<D_q
$$

と同値である。

つまり実際には、

> block $q$ が正 drift を持つ

という predicate じゃ。

絶対的に balance が正であるとは限らない。

例えば、

$$
B_{q^-}=-10,\qquad B_q=-9
$$

でも成立する。

設計としては問題ない。
「直前 baseline より上へ出た局所 excursion」と読める。

ただし次の theorem を追加して意味を固定するとよい。

```lean
canonicalEndpointPositiveExcursionAt_iff_endpointAccountingTerm_pos
```

あるいは alias として、

```lean
CanonicalEndpointPositiveDriftAt
```

を置くと読みやすい。

---

## 12. depthwise ledger が次の一手

claims と capacity の両方が level 集合になった。

次は、一 block の scalar drift を depth ごとに分解すべきじゃ。

例えば、

```lean
def canonicalDepthAccountingTerm (n : OddNat) (k d : ℕ) : ℤ :=
  (if d ∈ canonicalPaymentClaimDepths n k then 1 else 0) -
  (if d ∈ canonicalEndpointCapacityLevelSlots n k then 1 else 0)
```

とする。

すると有限 support 上で、

$$
D_k=\sum_d\left(\mathbf1_{d\in C_k}-\mathbf1_{d\in S_k}\right)
$$

が得られる。

さらに block family を足して和の順序を交換すれば、

$$
B_m = \sum_d\left(\#\{\text{claims at level }d\} - \#\{\text{capacity at level }d\}\right)
$$

となる。

これは scalar accounting を、本当の depth-flow accounting に持ち上げる。

ここまで出れば、

```text
どの depth で debt queue が増えるか
どの future endpoint がその depth を吸収するか
```

を直接観測できる。

eligibility invariant を発見するうえで、matching をいきなり作るより先に、この depthwise ledger を置くべきじゃ。

---

## 13. coherent matching または bounded lag が必要

将来 matching が見つかったとしても、各 finite prefix ごとに別々の matching を持つだけでは大域 boundedness は出ない。

必要なのは、次のいずれかじゃ。

### Coherent global schedule

prefix を拡張しても以前の割当てが変わらない、一貫した injection。

### Uniform repayment lag

各 claim が高々 $L$ blocks 以内に支払われる。

### Uniform outstanding queue bound

任意の時刻で未払い claims が高々 $C$ 件。

### Uniform balance excursion bound

$$
B_m\le C
$$

を全 $m$ で示す。

cp-314 の、

```lean
bitWidth_paymentEndpointSeq_le_of_balanceUniformUpperBound
```

は最後の条件から canonical endpoint width bound を正しく導いている。

したがって本当の大域目標は、

```text
各 finite claim prefix はいつか埋め込める
```

よりも、

```text
未払い queue または repayment lag が一様に抑えられる
```

の方じゃ。

---

## 数学的現在地

現在の Collatz block は、有限二部グラフ問題へ圧縮された。

claim vertex は、

$$
(k,d)
$$

であり、

- $k$ は canonical block
- $d$ は recovery depth

capacity vertex は、

$$
(\ell,s)
$$

であり、

- $\ell$ は future endpoint block
- $s$ は endpoint height level

じゃ。

必要な edge relation は、

$$
k\le\ell
$$

に加えて、

$$
\operatorname{Eligible}\bigl((k,d),(\ell,s)\bigr)
$$

を満たすもの。

そして求めるのは、この graph 上の injective matching か、未整合 queue の一様上界じゃ。

**Collatz の値列が、有限 depth-time matching 問題へ落ちた。**

これは確かに大躍進じゃ。

---

## 閉じる見込みについて

以前の「これは閉じると思うか」という問いにも、いまならより正確に答えられる。

**この会計・再添字・pressure incidence の枝は閉じた。**

残るものは、もう Lean の技術的穴ではない。

$$
\text{recovery depth}
\longrightarrow
\text{future capacity level}
$$

という一本の構造定理じゃ。

この eligibility が自然な局所不変量から出れば、boundedness まで一気に進む可能性がある。

ただし逆に、この eligibility が成立しない、または repayment lag が無制限になり得るなら、そこに Collatz の難しさが丸ごと残っている。

ゆえに現在の評価は、

> **閉じる道筋は初めて一本に絞られた。だが、その最後の一本が本当に通るかは、これから有限例と局所不変量で裁く段階**

じゃ。

期待値は以前より明らかに上がったぞい。

---

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge Float-window branch after
report-petal-314.

The cp-314 implementation is accepted.

The repayment-aware accounting layer is now mathematically substantial:
canonical claims are exact marked recovery depths, endpoint capacity has an
exact finite level carrier, arbitrary block windows telescope, and temporary
positive excursions are formally represented.

Before defining a general eligibility relation, correct three semantic
boundaries.

1. Delayed claim depths are a marked subset of `Icc 2 blockLength`, not the
   whole interval.
2. `CanonicalEndpointPositiveExcursionAt` is exactly a positive block drift
   relative to the immediately preceding balance.
3. The current forward matching settles claims through a fixed prefix into a
   future slot horizon, but it does not by itself prove return of the total
   balance because new claims may arise before that horizon.

# Stage A — exact excursion API

Prove:

    CanonicalEndpointPositiveExcursionAt n q
      ↔ 0 < endpointAccountingTerm n q

For `q <= r`, prove:

    CanonicalEndpointExcursionRepaidAt n q r
      ↔
    sum k in Icc q r, endpointAccountingTerm n k <= 0

Then rewrite it as the exact window inequality:

    sum claims over q..r <= sum capacity over q..r

Use the existing sliding telescope.

# Stage B — window carriers

Define actual finite carriers:

    CanonicalEndpointClaimWindowCarrier n q r
    CanonicalEndpointCapacityWindowCarrier n q r

whose block indices lie in `Icc q r`.

Prove exact cardinality formulas for both carriers.

Define:

    CanonicalEndpointForwardWindowMatching n q r

as an injective map from window claims to window capacity with:

    claim.block <= payment.block

Do not add depth eligibility yet.

Prove:

    ForwardWindowMatching
      -> CanonicalEndpointExcursionRepaidAt n q r

This is the matching notion that corresponds to balance repayment.

Retain the current prefix-to-future-horizon matching, but document it as a
finite claim-prefix future-slot embedding rather than a balance-repayment
certificate.

# Stage C — depthwise scalar ledger

Rename or alias:

    canonicalEndpointCapacityDepthSlots

to the semantically clearer:

    canonicalEndpointCapacityLevelSlots

Define the depth/level indicator:

    canonicalDepthAccountingTerm n k d

as claim incidence minus capacity incidence.

Prove for every canonical block:

    endpointAccountingTerm n k
      =
    sum over the finite depth support,
      canonicalDepthAccountingTerm n k d

Choose a concrete finite support such as:

    Icc 1 (max blockLength endpointHeight)

Then prove the endpoint-family sum with the order of summation exchanged.

This must expose the cumulative outstanding balance level by level.

# Stage D — exact seven depth regression

For the orbit from seven, prove the concrete finite sets for the first two
blocks.

Expected shape:

    first block claim depths    = {2, 3}
    first block capacity levels = {2}

    second block claim depths    = {1}
    second block capacity levels = {2, 3}

Construct an explicit depth-aware forward allocation:

    delayed depth 2 at block 0 -> level 2 at block 0
    delayed depth 3 at block 0 -> level 3 at block 1
    immediate depth 1 at block 1 -> level 2 at block 1

This is a regression prototype only, not a general theorem.

# Stage E — depth carriers

Define proof-independent dependent carriers:

    CanonicalEndpointDepthClaimCarrier n m
    CanonicalEndpointLevelCapacityCarrier n m

Prove their cardinalities equal cumulative claims and cumulative capacity.

Provide equivalences to the existing source-time carriers.

# Stage F — eligibility audit

Do not export a general eligibility relation immediately.

First test the candidate rule on exact canonical blocks:

    immediate depth 1 may use the lowest capacity level 2;

    delayed claim depth d >= 2 may use capacity level d
    at its own or a later endpoint.

Audit this against a broad finite family of exact orbit examples, including
at least:

    7
    27
    31
    511

Record counterexamples if any.

Pay special attention to collisions between:

    an immediate depth-1 claim
    and a delayed depth-2 claim

at an endpoint exposing only one level-2 slot.

# Stage G — eligibility relation

Only if the finite audit survives, define:

    CanonicalRepaymentEligible n claim slot

with separate clauses for:

    immediate claims
    delayed claims

The relation must include temporal order and an orbit-derived level rule.

Do not define eligibility merely by matching cardinalities.

# Stage H — Hall and queue formulations

For the depth-aware forward relation, expose both:

    finite Hall conditions
    outstanding claim queues by level

Show that independent finite-prefix embeddings are insufficient for a uniform
width bound.

Formulate at least one genuinely strong target:

    coherent global repayment schedule

or:

    uniform repayment lag

or:

    uniform outstanding queue bound

or:

    uniform canonical endpoint balance bound

# Stage I — consequences

Keep the implications separate:

    uniform balance bound
      -> canonical endpoint bit-width bound

    bounded repayment lag plus a local in-block overshoot bound
      -> all-time bit-width bound

    all-time bit-width bound
      -> eventual periodicity

Cycle rigidity and convergence remain independent later stages.

Continue autonomously through all exact finite accounting and regression
theorems.

Stop at the genuine orbit-derived eligibility invariant, not at carrier
reindexing.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-315.md
```

cp-314 は、問題を「数が増えるか」から、

> **どの recovery depth の claim が、どの future height level で支払われるか**

へ変えた。

これはまさしく、長く探してきた **局所 Core と大域 Beam の接点**じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
index b55509e2..6afc8e0a 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
@@ -16,6 +16,7 @@ import DkMath.Collatz.PetalBridge.FloatWindow.PaymentBlockBridge
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentFamily
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPressure
+import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentRepayment
 
 #print "file: DkMath.Collatz.PetalBridge.FloatWindow"
 
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentRepayment.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentRepayment.lean
new file mode 100644
index 00000000..b9750cd2
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentRepayment.lean
@@ -0,0 +1,760 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPressure
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentRepayment"
+
+namespace DkMath.Collatz
+
+/-!
+# Repayment across canonical universal payment blocks
+
+Prefix capacity dominance is a no-overdraft special case, not the general
+target.  This module retains positive endpoint excursions and records the
+finite-horizon repayment structures needed to discharge them later.
+-/
+
+section SevenRegression
+
+/-- The concrete odd initial state used by the first overdraft regression. -/
+private def sevenOdd : OddNat := mkOddNat 7 (by decide)
+
+private lemma v2_22 : v2 22 = 1 := by
+  have h := (DkMath.ABC.padic_val_two_of_even 11).2 (by decide)
+  simpa [v2, v2_odd 11 (by decide)] using h
+
+private lemma v2_34 : v2 34 = 1 := by
+  have h := (DkMath.ABC.padic_val_two_of_even 17).2 (by decide)
+  simpa [v2, v2_odd 17 (by decide)] using h
+
+private lemma v2_52 : v2 52 = 2 := by
+  have h26 := (DkMath.ABC.padic_val_two_of_even 13).2 (by decide)
+  have h52 := (DkMath.ABC.padic_val_two_of_even 26).2 (by decide)
+  have hv13 : v2 13 = 0 := v2_odd 13 (by decide)
+  have hv26 : v2 26 = 1 := by simpa [v2, hv13] using h26
+  simpa [v2, hv26] using h52
+
+private lemma v2_40 : v2 40 = 3 := by
+  have h10 := (DkMath.ABC.padic_val_two_of_even 5).2 (by decide)
+  have h20 := (DkMath.ABC.padic_val_two_of_even 10).2 (by decide)
+  have h40 := (DkMath.ABC.padic_val_two_of_even 20).2 (by decide)
+  have hv5 : v2 5 = 0 := v2_odd 5 (by decide)
+  have hv10 : v2 10 = 1 := by simpa [v2, hv5] using h10
+  have hv20 : v2 20 = 2 := by simpa [v2, hv10] using h20
+  simpa [v2, hv20] using h40
+
+private lemma v2_8 : v2 8 = 3 := by
+  have h4 := (DkMath.ABC.padic_val_two_of_even 2).2 (by decide)
+  have h8 := (DkMath.ABC.padic_val_two_of_even 4).2 (by decide)
+  have hv2 : v2 2 = 1 := by
+    have h := (DkMath.ABC.padic_val_two_of_even 1).2 (by decide)
+    simp [v2]
+  have hv4 : v2 4 = 2 := by simpa [v2, hv2] using h4
+  simpa [v2, hv4] using h8
+
+private lemma v2_14 : v2 14 = 1 := by
+  have h := (DkMath.ABC.padic_val_two_of_even 7).2 (by decide)
+  simpa [v2, v2_odd 7 (by decide)] using h
+
+/-- The first canonical endpoint for the orbit from seven is time two. -/
+theorem paymentEndpointSeq_seven_zero : paymentEndpointSeq sevenOdd 0 = 2 := by
+  norm_num [paymentEndpointSeq, orbitPaymentTarget, orbitExactDepth,
+    ResidualAllOnesDepth, oddOrbitLabel, iterateT, sevenOdd, mkOddNat, v2_8]
+
+/-- The second canonical endpoint for the orbit from seven is time three. -/
+theorem paymentEndpointSeq_seven_one : paymentEndpointSeq sevenOdd 1 = 3 := by
+  rw [show paymentEndpointSeq sevenOdd 1 =
+    orbitPaymentTarget sevenOdd (paymentEndpointSeq sevenOdd 0 + 1) by rfl]
+  rw [paymentEndpointSeq_seven_zero]
+  norm_num [orbitPaymentTarget, orbitExactDepth, ResidualAllOnesDepth, oddOrbitLabel,
+    iterateT, T, sevenOdd, mkOddNat, threeNPlusOne, pow2,
+    v2_22, v2_34, v2_52, v2_14]
+
+/-- The first canonical block from seven has positive signed drift one. -/
+theorem endpointAccountingTerm_seven_zero : endpointAccountingTerm sevenOdd 0 = 1 := by
+  rw [endpointAccountingTerm_eq_universalPaymentBlockSignedDriftAt]
+  rw [universalPaymentBlockSignedDriftAt_eq_bitWidth_sub sevenOdd
+    (paymentEndpointSeq sevenOdd 0)
+    (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq sevenOdd 0)]
+  rw [universalPaymentBlockStart_paymentEndpointSeq_zero,
+    paymentEndpointSeq_seven_zero]
+  norm_num [iterateT, T, sevenOdd, mkOddNat, threeNPlusOne, pow2,
+    v2_22, v2_34, v2_52, bitWidth]
+
+/-- The immediately following canonical block repays the first drift by minus one. -/
+theorem endpointAccountingTerm_seven_one : endpointAccountingTerm sevenOdd 1 = -1 := by
+  rw [endpointAccountingTerm_eq_universalPaymentBlockSignedDriftAt]
+  rw [universalPaymentBlockSignedDriftAt_eq_bitWidth_sub sevenOdd
+    (paymentEndpointSeq sevenOdd 1)
+    (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq sevenOdd 1)]
+  rw [universalPaymentBlockStart_paymentEndpointSeq_succ,
+    paymentEndpointSeq_seven_zero, paymentEndpointSeq_seven_one]
+  norm_num [iterateT, T, sevenOdd, mkOddNat, threeNPlusOne, pow2,
+    v2_22, v2_34, v2_52, v2_40, bitWidth]
+
+/-- The two-block overdraft excursion from seven returns exactly to baseline. -/
+theorem endpointAccountingTerm_seven_first_two_sum :
+    endpointAccountingTerm sevenOdd 0 + endpointAccountingTerm sevenOdd 1 = 0 := by
+  rw [endpointAccountingTerm_seven_zero, endpointAccountingTerm_seven_one]
+  norm_num
+
+end SevenRegression
+
+/-- Signed endpoint balance through canonical block `m`. -/
+noncomputable def canonicalEndpointBalanceInt (n : OddNat) (m : ℕ) : ℤ :=
+  ∑ k ∈ Finset.range (m + 1), endpointAccountingTerm n k
+
+/-- Endpoint balance is exactly endpoint width minus initial width. -/
+theorem canonicalEndpointBalanceInt_eq_bitWidth_sub
+    (n : OddNat) (m : ℕ) :
+    canonicalEndpointBalanceInt n m =
+      (bitWidth (iterateT (paymentEndpointSeq n m + 1) n).1 : ℤ) - bitWidth n.1 := by
+  exact sum_endpointAccountingTerm_paymentEndpointSeq n m
+
+/-- Capacity dominance only at the selected terminal endpoint. -/
+def CanonicalEndpointTerminalCapacityDominance
+    (n : OddNat) (m : ℕ) : Prop :=
+  cumulativeCanonicalEndpointClaims n m ≤ cumulativeCanonicalEndpointCapacity n m
+
+/-- Terminal capacity dominance is exactly nonpositive terminal balance. -/
+theorem canonicalEndpointTerminalCapacityDominance_iff_balance_nonpos
+    (n : OddNat) (m : ℕ) :
+    CanonicalEndpointTerminalCapacityDominance n m ↔
+      canonicalEndpointBalanceInt n m ≤ 0 := by
+  rw [canonicalEndpointBalanceInt, sum_endpointAccountingTerm_eq_claims_sub_capacity]
+  exact ⟨fun h => sub_nonpos.mpr (Int.ofNat_le.mpr h),
+    fun h => Int.ofNat_le.mp (sub_nonpos.mp h)⟩
+
+/-- Terminal capacity dominance is exactly return to at most the initial width. -/
+theorem canonicalEndpointTerminalCapacityDominance_iff_bitWidth_le
+    (n : OddNat) (m : ℕ) :
+    CanonicalEndpointTerminalCapacityDominance n m ↔
+      bitWidth (iterateT (paymentEndpointSeq n m + 1) n).1 ≤ bitWidth n.1 := by
+  rw [canonicalEndpointTerminalCapacityDominance_iff_balance_nonpos,
+    canonicalEndpointBalanceInt_eq_bitWidth_sub]
+  omega
+
+/-- Orbit-time start of canonical block `q`. -/
+noncomputable def canonicalEndpointBlockStart (n : OddNat) : ℕ → ℕ
+  | 0 => 0
+  | q + 1 => paymentEndpointSeq n q + 1
+
+/-- A canonical block starts where its universal source interval starts. -/
+theorem canonicalEndpointBlockStart_eq_universalPaymentBlockStart
+    (n : OddNat) (q : ℕ) :
+    canonicalEndpointBlockStart n q =
+      universalPaymentBlockStart n (paymentEndpointSeq n q)
+        (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n q) := by
+  cases q with
+  | zero =>
+      simp [canonicalEndpointBlockStart,
+        universalPaymentBlockStart_paymentEndpointSeq_zero]
+  | succ q =>
+      simp [canonicalEndpointBlockStart,
+        universalPaymentBlockStart_paymentEndpointSeq_succ]
+
+/-- Sliding endpoint-block telescope from block `q` through block `m`. -/
+theorem sum_endpointAccountingTerm_Icc_eq_bitWidth_sub
+    (n : OddNat) {q m : ℕ} (hqm : q ≤ m) :
+    (∑ k ∈ Finset.Icc q m, endpointAccountingTerm n k) =
+      (bitWidth (iterateT (paymentEndpointSeq n m + 1) n).1 : ℤ) -
+        bitWidth (iterateT (canonicalEndpointBlockStart n q) n).1 := by
+  have hsubset : Finset.range q ⊆ Finset.range (m + 1) := by
+    intro i hi
+    simp only [Finset.mem_range] at hi ⊢
+    omega
+  have hIcc : Finset.Icc q m = Finset.range (m + 1) \ Finset.range q := by
+    ext i
+    simp
+    omega
+  rw [hIcc, Finset.sum_sdiff_eq_sub hsubset]
+  rw [sum_endpointAccountingTerm_paymentEndpointSeq]
+  cases q with
+  | zero =>
+      simp [canonicalEndpointBlockStart, iterateT]
+  | succ q =>
+      rw [show ∑ k ∈ Finset.range (q + 1), endpointAccountingTerm n k =
+          (bitWidth (iterateT (paymentEndpointSeq n q + 1) n).1 : ℤ) - bitWidth n.1 by
+        exact sum_endpointAccountingTerm_paymentEndpointSeq n q]
+      simp [canonicalEndpointBlockStart]
+
+/-- Claims-minus-capacity form of the sliding block telescope. -/
+theorem sum_endpointAccountingTerm_Icc_eq_claims_sub_capacity
+    (n : OddNat) {q m : ℕ} (_hqm : q ≤ m) :
+    (∑ k ∈ Finset.Icc q m, endpointAccountingTerm n k) =
+      (∑ k ∈ Finset.Icc q m,
+        (((floatGrowthDebtFiberAt n (paymentEndpointSeq n k)).card : ℤ) +
+          (endpointImmediateCarryTwoClaimFiberAt n (paymentEndpointSeq n k)).card)) -
+      ∑ k ∈ Finset.Icc q m,
+        (extraPaymentCapacityAt n (paymentEndpointSeq n k) : ℤ) := by
+  simp_rw [endpointAccountingTerm]
+  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
+
+/-!
+## Matching directions
+
+The old ordered matching points from a claim to an already available slot.  It
+is therefore a backward-credit certificate.  A repayment certificate has the
+opposite temporal inequality and may extend its payment horizon beyond the
+claim horizon.  Keeping these predicates separate prevents a temporary
+overdraft from being silently ruled out by the type of the matching.
+-/
+
+/-- Compatibility name exposing the temporal meaning of the old matching. -/
+abbrev CanonicalEndpointBackwardCreditMatching :=
+  CanonicalEndpointOrderedCapacityMatching
+
+/--
+A finite claim prefix repaid by slots at its own or later endpoint, up to a
+possibly larger payment horizon. Existence is not asserted here.
+-/
+def CanonicalEndpointForwardRepaymentMatching
+    (n : OddNat) (claimHorizon payHorizon : ℕ) : Prop :=
+  claimHorizon ≤ payHorizon ∧
+    ∃ pay : CanonicalEndpointClaimCarrier n claimHorizon →
+        CanonicalEndpointCapacityCarrier n payHorizon,
+      Function.Injective pay ∧
+        ∀ claim, claim.val.1.val ≤ (pay claim).val.1.val
+
+/-- Every finite claim prefix has some finite future repayment horizon. -/
+def EveryFiniteCanonicalClaimPrefixEventuallyRepayable (n : OddNat) : Prop :=
+  ∀ q, ∃ r, q ≤ r ∧ CanonicalEndpointForwardRepaymentMatching n q r
+
+/-- A forward repayment matching records its horizon order explicitly. -/
+theorem CanonicalEndpointForwardRepaymentMatching.claimHorizon_le
+    {n : OddNat} {q r : ℕ}
+    (h : CanonicalEndpointForwardRepaymentMatching n q r) : q ≤ r :=
+  h.1
+
+/-- Claim carriers are finite dependent sums of the complete block fibers. -/
+noncomputable def canonicalEndpointClaimCarrierEquiv
+    (n : OddNat) (m : ℕ) :
+    CanonicalEndpointClaimCarrier n m ≃
+      Σ k : Fin (m + 1),
+        {i : ℕ // i ∈ carryTwoPaymentClaimFiberAt n (paymentEndpointSeq n k.val)} where
+  toFun claim :=
+    ⟨claim.val.1, claim.val.2,
+      (mem_carryTwoPaymentClaimFiberAt_iff_growthDebt_or_endpointImmediate
+        (h := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n claim.val.1.val)).2
+        claim.property⟩
+  invFun claim :=
+    ⟨⟨claim.1, claim.2.val⟩,
+      (mem_carryTwoPaymentClaimFiberAt_iff_growthDebt_or_endpointImmediate
+        (h := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n claim.1.val)).1
+        claim.2.property⟩
+  left_inv claim := by
+    apply Subtype.ext
+    rfl
+  right_inv claim := by
+    rcases claim with ⟨k, i⟩
+    rfl
+
+/-- Capacity carriers are finite dependent sums of local capacity fibers. -/
+noncomputable def canonicalEndpointCapacityCarrierEquiv
+    (n : OddNat) (m : ℕ) :
+    CanonicalEndpointCapacityCarrier n m ≃
+      Σ k : Fin (m + 1), {s : ℕ // s ∈ canonicalEndpointCapacitySlots n k.val} where
+  toFun slot := ⟨slot.val.1, slot.val.2, slot.property⟩
+  invFun slot := ⟨⟨slot.1, slot.2.val⟩, slot.2.property⟩
+  left_inv slot := by
+    apply Subtype.ext
+    rfl
+  right_inv slot := by
+    rcases slot with ⟨k, s⟩
+    rfl
+
+/-- The abstract claim carrier has the cumulative complete-claim cardinality. -/
+theorem natCard_canonicalEndpointClaimCarrier
+    (n : OddNat) (m : ℕ) :
+    Nat.card (CanonicalEndpointClaimCarrier n m) =
+      cumulativeCanonicalEndpointClaims n m := by
+  rw [Nat.card_congr (canonicalEndpointClaimCarrierEquiv n m), Nat.card_sigma]
+  simp_rw [Nat.card_eq_fintype_card, Fintype.card_coe]
+  unfold cumulativeCanonicalEndpointClaims
+  rw [Finset.sum_fin_eq_sum_range]
+  apply Finset.sum_congr rfl
+  intro k hk
+  rw [dif_pos (Finset.mem_range.mp hk)]
+  rw [carryTwoPaymentClaimFiberAt_card_eq_growthDebt_card_add_endpoint_card
+    n (paymentEndpointSeq n k)
+      (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)]
+
+/-- The abstract capacity carrier has the cumulative slot cardinality. -/
+theorem natCard_canonicalEndpointCapacityCarrier
+    (n : OddNat) (m : ℕ) :
+    Nat.card (CanonicalEndpointCapacityCarrier n m) =
+      cumulativeCanonicalEndpointCapacity n m := by
+  rw [Nat.card_congr (canonicalEndpointCapacityCarrierEquiv n m), Nat.card_sigma]
+  simp_rw [Nat.card_eq_fintype_card, Fintype.card_coe]
+  unfold cumulativeCanonicalEndpointCapacity
+  rw [Finset.sum_fin_eq_sum_range]
+  apply Finset.sum_congr rfl
+  intro k hk
+  rw [dif_pos (Finset.mem_range.mp hk)]
+
+/-- A backward-credit matching is a no-overdraft certificate on every prefix. -/
+theorem CanonicalEndpointBackwardCreditMatching.to_prefixCapacityDominance
+    {n : OddNat} {m : ℕ}
+    (h : CanonicalEndpointBackwardCreditMatching n m) :
+    CanonicalEndpointPrefixCapacityDominance n m := by
+  intro q hqm
+  rcases h with ⟨pay, hpayInjective, hdeadline⟩
+  let extendClaim : CanonicalEndpointClaimCarrier n q →
+      CanonicalEndpointClaimCarrier n m := fun claim =>
+    ⟨⟨⟨claim.val.1.val, by omega⟩, claim.val.2⟩, claim.property⟩
+  let prefixPay : CanonicalEndpointClaimCarrier n q →
+      CanonicalEndpointCapacityCarrier n q := fun claim =>
+    ⟨⟨⟨(pay (extendClaim claim)).val.1.val, by
+          have hbefore := hdeadline (extendClaim claim)
+          have hclaimle : claim.val.1.val ≤ q := Nat.lt_succ_iff.mp claim.val.1.isLt
+          change (pay (extendClaim claim)).val.1.val ≤ claim.val.1.val at hbefore
+          omega⟩,
+        (pay (extendClaim claim)).val.2⟩,
+      (pay (extendClaim claim)).property⟩
+  have hextendInjective : Function.Injective extendClaim := by
+    intro a b hab
+    have hblock := congrArg (fun claim => claim.val.1.val) hab
+    have hsource := congrArg (fun claim => claim.val.2) hab
+    apply Subtype.ext
+    apply Prod.ext
+    · apply Fin.ext
+      exact hblock
+    · exact hsource
+  have hprefixInjective : Function.Injective prefixPay := by
+    intro a b hab
+    have hblock := congrArg (fun slot => slot.val.1.val) hab
+    have hslot := congrArg (fun slot => slot.val.2) hab
+    apply hextendInjective
+    apply hpayInjective
+    apply Subtype.ext
+    apply Prod.ext
+    · apply Fin.ext
+      exact hblock
+    · exact hslot
+  letI : Finite (CanonicalEndpointCapacityCarrier n q) :=
+    Finite.of_injective (canonicalEndpointCapacityCarrierEquiv n q).toFun
+      (canonicalEndpointCapacityCarrierEquiv n q).injective
+  have hcard := Nat.card_le_card_of_injective prefixPay hprefixInjective
+  rwa [natCard_canonicalEndpointClaimCarrier,
+    natCard_canonicalEndpointCapacityCarrier] at hcard
+
+/-- Forward repayment matching implies enough capacity at its future horizon. -/
+theorem CanonicalEndpointForwardRepaymentMatching.claims_le_capacity
+    {n : OddNat} {q r : ℕ}
+    (h : CanonicalEndpointForwardRepaymentMatching n q r) :
+    cumulativeCanonicalEndpointClaims n q ≤ cumulativeCanonicalEndpointCapacity n r := by
+  rcases h with ⟨_, pay, hpayInjective, _⟩
+  letI : Finite (CanonicalEndpointCapacityCarrier n r) :=
+    Finite.of_injective (canonicalEndpointCapacityCarrierEquiv n r).toFun
+      (canonicalEndpointCapacityCarrierEquiv n r).injective
+  have hcard := Nat.card_le_card_of_injective pay hpayInjective
+  rwa [natCard_canonicalEndpointClaimCarrier,
+    natCard_canonicalEndpointCapacityCarrier] at hcard
+
+/-!
+## Depth-coordinate claim and capacity surfaces
+
+Depth one is the canonical endpoint. Increasing depth walks backwards through
+the block.  This coordinate is intrinsic to the exact-recovery staircase and
+does not yet prescribe which future capacity slot may pay a marked claim.
+-/
+
+/-- Source time at positive staircase depth `d` in canonical block `k`. -/
+noncomputable def canonicalPaymentSourceAtDepth
+    (n : OddNat) (k d : ℕ) : ℕ :=
+  paymentEndpointSeq n k + 1 - d
+
+/-- Complete carry-two claim depths in canonical block `k`. -/
+noncomputable def canonicalPaymentClaimDepths
+    (n : OddNat) (k : ℕ) : Finset ℕ := by
+  classical
+  exact (Finset.Icc 1 (canonicalPaymentBlockLength n k)).filter fun d =>
+    CarryTwoDebtAt n (canonicalPaymentSourceAtDepth n k d)
+
+/-- Membership in the marked claim-depth carrier. -/
+theorem mem_canonicalPaymentClaimDepths_iff
+    {n : OddNat} {k d : ℕ} :
+    d ∈ canonicalPaymentClaimDepths n k ↔
+      1 ≤ d ∧ d ≤ canonicalPaymentBlockLength n k ∧
+        CarryTwoDebtAt n (canonicalPaymentSourceAtDepth n k d) := by
+  classical
+  rw [canonicalPaymentClaimDepths]
+  simp only [Finset.mem_filter, Finset.mem_Icc]
+  tauto
+
+/-- Every canonical block has at least its endpoint. -/
+theorem canonicalPaymentBlockLength_pos (n : OddNat) (k : ℕ) :
+    0 < canonicalPaymentBlockLength n k := by
+  rw [canonicalPaymentBlockLength_eq_sourceFiber_card]
+  exact Finset.card_pos.mpr
+    (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)
+
+/-- Depth one is exactly the endpoint source. -/
+theorem canonicalPaymentSourceAtDepth_one (n : OddNat) (k : ℕ) :
+    canonicalPaymentSourceAtDepth n k 1 = paymentEndpointSeq n k := by
+  simp [canonicalPaymentSourceAtDepth]
+
+/-- The endpoint depth is marked exactly when the immediate claim is present. -/
+theorem one_mem_canonicalPaymentClaimDepths_iff
+    (n : OddNat) (k : ℕ) :
+    1 ∈ canonicalPaymentClaimDepths n k ↔
+      CarryTwoDebtAt n (paymentEndpointSeq n k) := by
+  rw [mem_canonicalPaymentClaimDepths_iff, canonicalPaymentSourceAtDepth_one]
+  have hlen := canonicalPaymentBlockLength_pos n k
+  constructor
+  · exact fun h => h.2.2
+  · intro hcarry
+    exact ⟨by omega, by omega, hcarry⟩
+
+/-- Levelled endpoint-capacity slots; level one is reserved for the center. -/
+noncomputable def canonicalEndpointCapacityDepthSlots
+    (n : OddNat) (k : ℕ) : Finset ℕ :=
+  Finset.Icc 2 (orbitWindowHeight n (paymentEndpointSeq n k))
+
+/-- The levelled slot carrier has exactly the endpoint's extra capacity. -/
+theorem canonicalEndpointCapacityDepthSlots_card
+    (n : OddNat) (k : ℕ) :
+    (canonicalEndpointCapacityDepthSlots n k).card =
+      extraPaymentCapacityAt n (paymentEndpointSeq n k) := by
+  rw [canonicalEndpointCapacityDepthSlots, Nat.card_Icc]
+  unfold extraPaymentCapacityAt
+  have hheight := two_le_orbitWindowHeight_paymentEndpointSeq n k
+  omega
+
+/--
+At every valid positive depth, the recovery fiber is the singleton containing
+the source obtained by walking backwards from the endpoint.
+-/
+theorem canonicalPaymentBlockRecoveryFiber_eq_singleton_sourceAtDepth
+    (n : OddNat) (k d : ℕ)
+    (hdpos : 1 ≤ d) (hdle : d ≤ canonicalPaymentBlockLength n k) :
+    canonicalPaymentBlockRecoveryFiber n k d =
+      {canonicalPaymentSourceAtDepth n k d} := by
+  classical
+  have hnonempty :=
+    (canonicalPaymentBlockRecoveryFiber_nonempty_iff n k d).2 ⟨hdpos, hdle⟩
+  rcases hnonempty with ⟨i, hi⟩
+  rcases mem_canonicalPaymentBlockRecoveryFiber_iff.mp hi with ⟨hiblock, hirecover⟩
+  have hdepth :=
+    orbitExactDepth_eq_paymentEndpoint_sub_add_one_of_mem_canonicalPaymentBlock hiblock
+  have hrecoverDepth : orbitExactDepth n i = d := by
+    simpa [OrbitDepthRecoversExactlyAt, orbitExactDepth] using hirecover
+  have hsource : i = canonicalPaymentSourceAtDepth n k d := by
+    have hiend : i ≤ paymentEndpointSeq n k := by
+      exact (mem_orbitPaymentSourceFiberAt_iff.mp
+        (by simpa [canonicalPaymentBlock_eq_sourceFiber] using hiblock)).1
+    unfold canonicalPaymentSourceAtDepth
+    omega
+  ext i'
+  simp only [Finset.mem_singleton]
+  constructor
+  · intro hi'
+    rcases mem_canonicalPaymentBlockRecoveryFiber_iff.mp hi' with
+      ⟨hi'block, hi'recover⟩
+    have hii' := eq_of_mem_canonicalPaymentBlock_of_recovery_same_depth
+      hiblock hi'block hirecover hi'recover
+    omega
+  · rintro rfl
+    simpa [← hsource] using hi
+
+/-- A valid recovery depth has the expected unique source. -/
+theorem mem_canonicalPaymentBlockRecoveryFiber_iff_eq_sourceAtDepth
+    {n : OddNat} {k d i : ℕ}
+    (hdpos : 1 ≤ d) (hdle : d ≤ canonicalPaymentBlockLength n k) :
+    i ∈ canonicalPaymentBlockRecoveryFiber n k d ↔
+      i = canonicalPaymentSourceAtDepth n k d := by
+  rw [canonicalPaymentBlockRecoveryFiber_eq_singleton_sourceAtDepth n k d hdpos hdle]
+  simp
+
+/-- A marked depth is precisely a valid singleton recovery carrying two. -/
+theorem mem_canonicalPaymentClaimDepths_iff_recovery_carryTwo
+    {n : OddNat} {k d : ℕ} :
+    d ∈ canonicalPaymentClaimDepths n k ↔
+      1 ≤ d ∧ d ≤ canonicalPaymentBlockLength n k ∧
+        ∃ i, canonicalPaymentBlockRecoveryFiber n k d = {i} ∧ CarryTwoDebtAt n i := by
+  rw [mem_canonicalPaymentClaimDepths_iff]
+  constructor
+  · rintro ⟨hdpos, hdle, hcarry⟩
+    exact ⟨hdpos, hdle, canonicalPaymentSourceAtDepth n k d,
+      canonicalPaymentBlockRecoveryFiber_eq_singleton_sourceAtDepth n k d hdpos hdle,
+      hcarry⟩
+  · rintro ⟨hdpos, hdle, i, hfiber, hcarry⟩
+    have hcanonical :=
+      canonicalPaymentBlockRecoveryFiber_eq_singleton_sourceAtDepth n k d hdpos hdle
+    have hi : canonicalPaymentSourceAtDepth n k d = i := by
+      rw [hcanonical] at hfiber
+      simpa using Finset.singleton_inj.mp hfiber
+    exact ⟨hdpos, hdle, by simpa [hi] using hcarry⟩
+
+/-- Source/depth coordinates are inverse on the valid canonical staircase. -/
+theorem canonicalPaymentDebtDepth_sourceAtDepth
+    (n : OddNat) (k d : ℕ)
+    (hdpos : 1 ≤ d) (hdle : d ≤ canonicalPaymentBlockLength n k) :
+    canonicalPaymentDebtDepth n k (canonicalPaymentSourceAtDepth n k d) = d := by
+  rw [canonicalPaymentBlockLength_eq_endpoint_sub_start_add_one] at hdle
+  unfold canonicalPaymentDebtDepth canonicalPaymentSourceAtDepth
+  omega
+
+/--
+Marked recovery depths are the depth-coordinate image of the complete claim
+fiber, including the optional immediate endpoint claim.
+-/
+theorem canonicalPaymentClaimDepths_eq_image_completeClaimFiber
+    (n : OddNat) (k : ℕ) :
+    canonicalPaymentClaimDepths n k =
+      (carryTwoPaymentClaimFiberAt n (paymentEndpointSeq n k)).image
+        (canonicalPaymentDebtDepth n k) := by
+  classical
+  let e := paymentEndpointSeq n k
+  let h := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k
+  ext d
+  constructor
+  · intro hd
+    rcases mem_canonicalPaymentClaimDepths_iff.mp hd with ⟨hdpos, hdle, hcarry⟩
+    let i := canonicalPaymentSourceAtDepth n k d
+    have hfiber : canonicalPaymentBlockRecoveryFiber n k d = {i} := by
+      simpa [i] using
+        canonicalPaymentBlockRecoveryFiber_eq_singleton_sourceAtDepth n k d hdpos hdle
+    have hiRecovery : i ∈ canonicalPaymentBlockRecoveryFiber n k d := by
+      rw [hfiber]
+      simp
+    have hiBlock := (mem_canonicalPaymentBlockRecoveryFiber_iff.mp hiRecovery).1
+    have hiIcc : i ∈ Finset.Icc
+        (universalPaymentBlockStart n e h) e := by
+      simpa [e, h, canonicalPaymentBlock_eq_Icc_universalPaymentBlockStart] using hiBlock
+    have hiClaim : i ∈ carryTwoPaymentClaimFiberAt n e :=
+      (mem_carryTwoPaymentClaimFiberAt_iff_mem_universalPaymentBlock_and_carryTwo
+        (h := h)).2 ⟨hiIcc, by simpa [i, e] using hcarry⟩
+    apply Finset.mem_image.mpr
+    refine ⟨i, by simpa [e] using hiClaim, ?_⟩
+    simpa [i] using canonicalPaymentDebtDepth_sourceAtDepth n k d hdpos hdle
+  · intro hd
+    rcases Finset.mem_image.mp hd with ⟨i, hiClaim, hid⟩
+    have hiClaim' : i ∈ carryTwoPaymentClaimFiberAt n e := by
+      simpa [e] using hiClaim
+    rcases
+        (mem_carryTwoPaymentClaimFiberAt_iff_mem_universalPaymentBlock_and_carryTwo
+          (h := h)).1 hiClaim' with ⟨hiIcc, hiCarry⟩
+    have hiBlock : i ∈ canonicalPaymentBlock n k := by
+      rw [canonicalPaymentBlock_eq_Icc_universalPaymentBlockStart]
+      simpa [e, h] using hiIcc
+    have hiDepth :=
+      orbitExactDepth_eq_paymentEndpoint_sub_add_one_of_mem_canonicalPaymentBlock hiBlock
+    have hiRecover : OrbitDepthRecoversExactlyAt n i d := by
+      have hdepth : orbitExactDepth n i = d := by
+        rw [hiDepth]
+        simpa [canonicalPaymentDebtDepth] using hid
+      simpa [OrbitDepthRecoversExactlyAt, orbitExactDepth] using hdepth
+    have hvalid := (canonicalPaymentBlockRecoveryFiber_nonempty_iff n k d).1
+      ⟨i, mem_canonicalPaymentBlockRecoveryFiber_iff.mpr ⟨hiBlock, hiRecover⟩⟩
+    rcases hvalid with ⟨hdpos, hdle⟩
+    have hiSource : i = canonicalPaymentSourceAtDepth n k d :=
+      (mem_canonicalPaymentBlockRecoveryFiber_iff_eq_sourceAtDepth hdpos hdle).mp
+        (mem_canonicalPaymentBlockRecoveryFiber_iff.mpr ⟨hiBlock, hiRecover⟩)
+    exact mem_canonicalPaymentClaimDepths_iff.mpr
+      ⟨hdpos, hdle, by simpa [← hiSource] using hiCarry⟩
+
+/-- Complete claim count is exactly marked recovery-depth count. -/
+theorem canonicalPaymentClaimDepths_card
+    (n : OddNat) (k : ℕ) :
+    (canonicalPaymentClaimDepths n k).card =
+      (floatGrowthDebtFiberAt n (paymentEndpointSeq n k)).card +
+        (endpointImmediateCarryTwoClaimFiberAt n (paymentEndpointSeq n k)).card := by
+  rw [canonicalPaymentClaimDepths_eq_image_completeClaimFiber]
+  rw [Finset.card_image_iff.mpr]
+  · exact carryTwoPaymentClaimFiberAt_card_eq_growthDebt_card_add_endpoint_card
+      n (paymentEndpointSeq n k)
+        (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)
+  · intro i hi i' hi' heq
+    have hiIcc :=
+      (mem_carryTwoPaymentClaimFiberAt_iff_mem_universalPaymentBlock_and_carryTwo
+        (h := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)).1 hi
+    have hi'Icc :=
+      (mem_carryTwoPaymentClaimFiberAt_iff_mem_universalPaymentBlock_and_carryTwo
+        (h := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)).1 hi'
+    have hile := (Finset.mem_Icc.mp hiIcc.1).2
+    have hi'le := (Finset.mem_Icc.mp hi'Icc.1).2
+    unfold canonicalPaymentDebtDepth at heq
+    omega
+
+/-- Delayed marked claims are complete marked claims above depth one. -/
+noncomputable def canonicalPaymentDelayedClaimDepths
+    (n : OddNat) (k : ℕ) : Finset ℕ := by
+  classical
+  exact (canonicalPaymentClaimDepths n k).filter fun d => 2 ≤ d
+
+/-- Membership API for delayed marked claim depths. -/
+theorem mem_canonicalPaymentDelayedClaimDepths_iff
+    {n : OddNat} {k d : ℕ} :
+    d ∈ canonicalPaymentDelayedClaimDepths n k ↔
+      d ∈ canonicalPaymentClaimDepths n k ∧ 2 ≤ d := by
+  classical
+  simp [canonicalPaymentDelayedClaimDepths]
+
+/-- Existing delayed-debt addresses lie in the staircase interval `2..L`. -/
+theorem canonicalPaymentMarkedDebtDepths_subset_Icc
+    (n : OddNat) (k : ℕ) :
+    canonicalPaymentMarkedDebtDepths n k ⊆
+      Finset.Icc 2 (canonicalPaymentBlockLength n k) := by
+  intro d hd
+  rcases Finset.mem_image.mp hd with ⟨i, hiDebt, hid⟩
+  have hdebt := (mem_floatGrowthDebtFiberAt_iff.mp hiDebt).2.1
+  have hdelayed := (floatDebtAt_iff_delayedCarryTwoDebtAt n i).mp hdebt
+  have htwoExact :=
+    (orbitWindowHeight_eq_one_iff_two_le_orbitExactDepth n i).mp hdelayed.2
+  have hdepth := canonicalPaymentDebtDepth_eq_orbitExactDepth_of_mem_growthDebt hiDebt
+  have hiBlock : i ∈ canonicalPaymentBlock n k := by
+    rw [canonicalPaymentBlock_eq_sourceFiber]
+    exact mem_orbitPaymentSourceFiberAt_of_mem_floatGrowthDebtFiberAt hiDebt
+  have hiRecover : OrbitDepthRecoversExactlyAt n i d := by
+    have : orbitExactDepth n i = d := by omega
+    simpa [OrbitDepthRecoversExactlyAt, orbitExactDepth] using this
+  have hvalid := (canonicalPaymentBlockRecoveryFiber_nonempty_iff n k d).1
+    ⟨i, mem_canonicalPaymentBlockRecoveryFiber_iff.mpr ⟨hiBlock, hiRecover⟩⟩
+  exact Finset.mem_Icc.mpr ⟨by omega, hvalid.2⟩
+
+/-- Delayed claim depths are exactly the old marked delayed-debt addresses. -/
+theorem canonicalPaymentDelayedClaimDepths_eq_markedDebtDepths
+    (n : OddNat) (k : ℕ) :
+    canonicalPaymentDelayedClaimDepths n k = canonicalPaymentMarkedDebtDepths n k := by
+  classical
+  ext d
+  constructor
+  · intro hd
+    rcases mem_canonicalPaymentDelayedClaimDepths_iff.mp hd with ⟨hdClaim, hd2⟩
+    rcases mem_canonicalPaymentClaimDepths_iff.mp hdClaim with
+      ⟨hdpos, hdle, hcarry⟩
+    let i := canonicalPaymentSourceAtDepth n k d
+    have hiRecovery : i ∈ canonicalPaymentBlockRecoveryFiber n k d :=
+      (mem_canonicalPaymentBlockRecoveryFiber_iff_eq_sourceAtDepth hdpos hdle).2 rfl
+    have hiBlock := (mem_canonicalPaymentBlockRecoveryFiber_iff.mp hiRecovery).1
+    have hiIcc : i ∈ Finset.Icc
+        (universalPaymentBlockStart n (paymentEndpointSeq n k)
+          (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k))
+        (paymentEndpointSeq n k) := by
+      rw [← canonicalPaymentBlock_eq_Icc_universalPaymentBlockStart]
+      exact hiBlock
+    have hiInterior : i ∈ Finset.Ico
+        (universalPaymentBlockStart n (paymentEndpointSeq n k)
+          (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k))
+        (paymentEndpointSeq n k) := by
+      have hstaircase :=
+        orbitExactDepth_eq_paymentEndpoint_sub_add_one_of_mem_canonicalPaymentBlock hiBlock
+      have hrecovery :=
+        (mem_canonicalPaymentBlockRecoveryFiber_iff.mp hiRecovery).2
+      have hdepth : orbitExactDepth n i = d := by
+        simpa [OrbitDepthRecoversExactlyAt, orbitExactDepth] using hrecovery
+      exact Finset.mem_Ico.mpr ⟨(Finset.mem_Icc.mp hiIcc).1, by
+        omega⟩
+    have hiDebt : i ∈ floatGrowthDebtFiberAt n (paymentEndpointSeq n k) :=
+      (mem_floatGrowthDebtFiberAt_iff_mem_universalPaymentBlockInterior_and_carryTwo
+        (h := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)).2
+        ⟨hiInterior, by simpa [i] using hcarry⟩
+    apply Finset.mem_image.mpr
+    exact ⟨i, hiDebt, by
+      simpa [i] using canonicalPaymentDebtDepth_sourceAtDepth n k d hdpos hdle⟩
+  · intro hd
+    have hdIcc := canonicalPaymentMarkedDebtDepths_subset_Icc n k hd
+    rcases Finset.mem_Icc.mp hdIcc with ⟨hd2, hdle⟩
+    have hdpos : 1 ≤ d := by omega
+    rcases Finset.mem_image.mp hd with ⟨i, hiDebt, hid⟩
+    have hiBlock : i ∈ canonicalPaymentBlock n k := by
+      rw [canonicalPaymentBlock_eq_sourceFiber]
+      exact mem_orbitPaymentSourceFiberAt_of_mem_floatGrowthDebtFiberAt hiDebt
+    have hdepth := canonicalPaymentDebtDepth_eq_orbitExactDepth_of_mem_growthDebt hiDebt
+    have hiRecover : OrbitDepthRecoversExactlyAt n i d := by
+      have : orbitExactDepth n i = d := by omega
+      simpa [OrbitDepthRecoversExactlyAt, orbitExactDepth] using this
+    have hiSource :=
+      (mem_canonicalPaymentBlockRecoveryFiber_iff_eq_sourceAtDepth
+        hdpos hdle).mp
+        (mem_canonicalPaymentBlockRecoveryFiber_iff.mpr ⟨hiBlock, hiRecover⟩)
+    have hcarry :=
+      ((floatDebtAt_iff_delayedCarryTwoDebtAt n i).mp
+        (mem_floatGrowthDebtFiberAt_iff.mp hiDebt).2.1).1
+    exact mem_canonicalPaymentDelayedClaimDepths_iff.mpr
+      ⟨mem_canonicalPaymentClaimDepths_iff.mpr
+        ⟨hdpos, hdle,
+          by simpa [← hiSource] using hcarry⟩,
+        hd2⟩
+
+/-- Delayed debt count is exactly the number of marked recovery depths above one. -/
+theorem canonicalPaymentDelayedClaimDepths_card
+    (n : OddNat) (k : ℕ) :
+    (canonicalPaymentDelayedClaimDepths n k).card =
+      (floatGrowthDebtFiberAt n (paymentEndpointSeq n k)).card := by
+  rw [canonicalPaymentDelayedClaimDepths_eq_markedDebtDepths,
+    canonicalPaymentMarkedDebtDepths_card]
+
+/-!
+## Excursion and boundedness surfaces
+
+These predicates deliberately describe endpoint balance only. They neither
+state nor imply convergence of the underlying orbit.
+-/
+
+/-- Balance immediately before canonical block `q`. -/
+noncomputable def canonicalEndpointBalanceBefore (n : OddNat) : ℕ → ℤ
+  | 0 => 0
+  | q + 1 => canonicalEndpointBalanceInt n q
+
+/-- A canonical endpoint lies strictly above the balance before its block. -/
+def CanonicalEndpointPositiveExcursionAt (n : OddNat) (q : ℕ) : Prop :=
+  canonicalEndpointBalanceBefore n q < canonicalEndpointBalanceInt n q
+
+/-- Endpoint `r` has repaid the excursion beginning at block `q`. -/
+def CanonicalEndpointExcursionRepaidAt (n : OddNat) (q r : ℕ) : Prop :=
+  q ≤ r ∧ canonicalEndpointBalanceInt n r ≤ canonicalEndpointBalanceBefore n q
+
+/-- Every positive endpoint excursion eventually returns to its prior baseline. -/
+def EveryCanonicalEndpointExcursionEventuallyRepaid (n : OddNat) : Prop :=
+  ∀ q, CanonicalEndpointPositiveExcursionAt n q →
+    ∃ r, CanonicalEndpointExcursionRepaidAt n q r
+
+/-- The orbit from seven has a genuine positive first endpoint excursion. -/
+theorem canonicalEndpointPositiveExcursionAt_seven_zero :
+    CanonicalEndpointPositiveExcursionAt sevenOdd 0 := by
+  simp [CanonicalEndpointPositiveExcursionAt, canonicalEndpointBalanceBefore,
+    canonicalEndpointBalanceInt, endpointAccountingTerm_seven_zero]
+
+/-- The second canonical endpoint repays the first excursion from seven. -/
+theorem canonicalEndpointExcursionRepaidAt_seven_zero_one :
+    CanonicalEndpointExcursionRepaidAt sevenOdd 0 1 := by
+  constructor
+  · omega
+  · change (∑ k ∈ Finset.range 2, endpointAccountingTerm sevenOdd k) ≤ 0
+    rw [show ∑ k ∈ Finset.range 2, endpointAccountingTerm sevenOdd k =
+        endpointAccountingTerm sevenOdd 0 + endpointAccountingTerm sevenOdd 1 by
+      norm_num [Finset.sum_range_succ]]
+    rw [endpointAccountingTerm_seven_first_two_sum]
+
+/-- A uniform integer balance ceiling at every canonical endpoint. -/
+def CanonicalEndpointBalanceUniformUpperBound (n : OddNat) (C : ℕ) : Prop :=
+  ∀ m, canonicalEndpointBalanceInt n m ≤ C
+
+/-- A uniform balance ceiling gives the corresponding canonical width ceiling. -/
+theorem bitWidth_paymentEndpointSeq_le_of_balanceUniformUpperBound
+    {n : OddNat} {C : ℕ}
+    (h : CanonicalEndpointBalanceUniformUpperBound n C) (m : ℕ) :
+    bitWidth (iterateT (paymentEndpointSeq n m + 1) n).1 ≤ bitWidth n.1 + C := by
+  have hm := h m
+  rw [canonicalEndpointBalanceInt_eq_bitWidth_sub] at hm
+  omega
+
+/-!
+## Genuine frontier: eligibility
+
+The claim and capacity sides now both have exact depth coordinates, and marked
+recovery incidence has exact cardinality. What is not proved is that a claim
+depth is eligible for a same-depth slot at its own or a later endpoint. That
+relation must encode an orbit invariant, not merely matching cardinalities.
+Accordingly no eligibility predicate is exported yet and no forward repayment
+matching is asserted. The next implementation must derive and test that local
+invariant before constructing a payment map.
+-/
+
+end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-314.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-314.md
new file mode 100644
index 00000000..c9689338
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-314.md
@@ -0,0 +1,135 @@
+# Petal / Collatz implementation report: cp-314
+
+## Result
+
+Checkpoint cp-314 establishes a repayment-aware endpoint accounting layer in
+`DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentRepayment`.
+
+The strategic correction is now formal rather than documentary:
+
+- prefix capacity dominance is a no-overdraft condition;
+- temporary positive endpoint balance is possible;
+- later endpoint capacity must therefore be represented by a distinct forward
+  repayment relation.
+
+No theorem in this checkpoint asserts convergence or universal repayment.
+
+## Regression fact: the orbit from seven
+
+Lean proves the first canonical endpoints to be `2` and `3`, and proves their
+signed accounting terms to be `+1` and `-1`. Their two-block sum is zero.
+
+Consequently, the first endpoint is a genuine positive excursion and the next
+endpoint repays it to the preceding baseline. This is a concrete counterexample
+to using global all-prefix no-overdraft as the intended general target.
+
+## Balance and sliding telescope
+
+The new `canonicalEndpointBalanceInt n m` is the signed sum through block `m`.
+It is proved equal to
+
+```text
+bitWidth(after endpoint m) - bitWidth(initial state).
+```
+
+Terminal capacity dominance is equivalent both to nonpositive terminal balance
+and to terminal bit width being at most the initial bit width.
+
+For every `q <= m`, the sum over blocks `q..m` telescopes to endpoint width
+minus width at the start of block `q`. A claims-minus-capacity form is also
+available. This is the finite algebra needed to describe repayment by future
+blocks rather than prohibiting an earlier overload.
+
+## Matching directions
+
+The former ordered matching is retained under the explicit compatibility name
+`CanonicalEndpointBackwardCreditMatching`. Its slot satisfies
+
+```text
+payment block <= claim block.
+```
+
+Lean now proves that such a matching implies
+`CanonicalEndpointPrefixCapacityDominance`. Thus its exact meaning is fixed: it
+is a no-overdraft certificate using capacity already available at the claim's
+deadline.
+
+The separate `CanonicalEndpointForwardRepaymentMatching n q r` has distinct
+claim and payment horizons and requires
+
+```text
+q <= r
+claim block <= payment block.
+```
+
+Its existence is intentionally not asserted. If supplied, Lean proves that
+claims through `q` do not exceed capacity through `r`. The global open property
+is stated as `EveryFiniteCanonicalClaimPrefixEventuallyRepayable`.
+
+Carrier equivalences to finite dependent sums were added, with exact `Nat.card`
+formulas for cumulative claims and cumulative capacity.
+
+## Depth-coordinate incidence
+
+The canonical source at depth `d` is fixed as
+
+```text
+paymentEndpointSeq n k + 1 - d.
+```
+
+The following exact facts are proved:
+
+- every canonical block has positive length;
+- depth one is the endpoint;
+- the depth-one mark is exactly the optional immediate endpoint claim;
+- every valid positive recovery fiber is exactly the singleton containing its
+  canonical source;
+- complete marked claim depths are the depth-image of the complete claim fiber;
+- their cardinality is delayed claims plus the optional immediate claim;
+- delayed marked depths lie in `Icc 2 blockLength`;
+- delayed marked depths equal the existing marked debt-depth carrier;
+- their cardinality is exactly the delayed growth-debt count;
+- levelled capacity slots are `Icc 2 endpointHeight`, with cardinality exactly
+  equal to endpoint extra capacity.
+
+This closes the pressure-fiber to claim-accounting incidence bridge. Claims and
+capacity are now both available in depth coordinates.
+
+## Excursion and boundedness surfaces
+
+The implementation adds predicates for positive endpoint excursions, repayment
+to the prior baseline, and eventual repayment of every positive excursion.
+The seven regression proves one concrete excursion and repayment pair.
+
+A separate uniform balance ceiling is shown to imply the corresponding uniform
+canonical endpoint bit-width ceiling. This is a boundedness implication only;
+it is not identified with convergence.
+
+## Exact frontier
+
+The remaining obstruction is no longer counting or reindexing. It is the
+eligibility rule needed to construct a forward payment map.
+
+The finite data suggests that a delayed claim at depth `d` may use a depth-`d`
+capacity slot at its own or a later endpoint, with the immediate claim using a
+lowest local level. That rule has not yet been derived from an orbit invariant.
+It is therefore not exported as a relation and no forward repayment matching is
+claimed.
+
+The next checkpoint should investigate this local invariant against exact
+canonical blocks. A valid result must explain both eligibility and injectivity;
+cardinality alone is insufficient.
+
+## Verification
+
+Completed during implementation:
+
+```text
+lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentRepayment
+lake build DkMath.Collatz.PetalBridge.FloatWindow
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath
+```
+
+The new module contains no `sorry`. Existing unrelated project warnings remain
+outside this checkpoint.
````
`````
