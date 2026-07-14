# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPressure

gch: b4f17e8c8309127c375cecd20b8293115aa73a38

## Report

cp-313 を実装し、有限 pressure 計数層を閉じました。

主な確定事実:

- 長さ `L` の canonical block は深度 `1..L` をちょうど一度ずつ回復する。
- depth `0` の recovery は存在しない。
- depth `d` の continuation 数は正確に `L - d`。
- 局所 pressure は `(L - d) - recovery` と完全分類できる。
- 既存の `SourcePressureMarginInt` は canonical block pressure の有限和と一致する。
- delayed debt の source は、互いに異なる exact-depth address を持つ。
- claim、capacity slot、prefix Hall 条件、順序保存 matching の型を固定した。
- prefix capacity dominance を仮定すれば、全 canonical endpoint の bit width は初期値以下。

重要な結論は、**各ブロックの pressure は必ずしも非正ではない**ことです。浅い深度では長いブロックが正の pressure を持ちます。したがって残る問題は局所符号ではなく、端点間で claim を capacity slot へ割り当てる順序保存 matching です。

実装: [UniversalPaymentPressure.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentPressure.lean:193)  
レポート: [report-petal-313.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-313.md:1)

検証済み:

- `lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPressure`
- `lake build DkMath.Collatz.PetalBridge.FloatWindow`
- `lake build DkMath.Collatz.PetalBridge`
- `lake build DkMath`
- `git diff --check`
- 新規 `sorry` / `axiom` なし

まだ収束は証明していません。有限再添字は完了し、真相の次の関門が **ordered capacity matching または最小 overload prefix からの rigidity 抽出**であることまで確定しました。

## Review

# cp-313 実装レビュー

## 結論

**Lean 実装は全面採用。有限 pressure 計数層は本当に閉じた。**

ただし、戦略上の結論には一箇所、大きな修正が必要じゃ。

cp-313 は次を完全に証明した。

- canonical block は深度 $1,\ldots,L$ を一度ずつ持つ。
- recovery / continuation の実際の `Finset` と閉形式が一致する。
- 既存 `SourcePressureMarginInt` は block-local pressure の有限和になる。
- delayed debt は block 内で一意な depth address を持つ。
- claim と capacity の実 carrier が定義された。
- 累積会計と bit width の telescope が接続された。

ここまでは極めて良い。

しかし、

> 全 prefix で累積 claim が累積 capacity 以下になることが、残る最終符号問題である

という診断は強すぎる。

その条件は、既に観測済みの収束軌道でも破れる。
したがって、**証明すべき最終定理ではなく、「一度も初期 width を超えない軌道」の特殊条件**じゃ。

---

## 1. pressure fiber の実装は正確

今回、結論式を先に定義することなく、実際の時刻集合を filter した。

```lean
canonicalPaymentBlockRecoveryFiber
canonicalPaymentBlockContinuationFiber
```

これは正しい設計じゃ。

### Recovery

長さ $L$ の block について、

$$
\#\operatorname{Recovery}(d)=\begin{cases}1&1\le d\le L\\0&\text{otherwise}\end{cases}
$$

depth zero を明示的に除外したことも重要じゃ。

$$
\#\operatorname{Recovery}(0)=0
$$

以前の粗い候補、

$$
\mathbf 1_{d\le L}
$$

では $d=0$ を誤って一件と数える。今回そこを正しく修正している。

### Continuation

$$
\#\operatorname{Continuation}(d)=L-d
$$

これは $d=0$ でも成立する。

$$
\#\operatorname{Continuation}(0)=L
$$

また `canonicalPaymentBlockContinuationFiber_eq_Icc` に $d<L$ を要求したのも正しい。

Nat の切り詰め減算で偽の interval endpoint を作らないための、本質的な仮定じゃ。

---

## 2. block-local pressure の完全分類

```lean
blockPressureContributionInt
```

は、

$$
M_k(d)=\#\operatorname{Continuation}_k(d)-\#\operatorname{Recovery}_k(d)
$$

として実際の fiber から定義された。

閉形式は、

$$
M_k(d)=(L_k-d)-\mathbf 1_{1\le d\le L_k}
$$

じゃ。

正の depth では、

| Block length | Pressure |
| ------------ | -------: |
| $L<d$        |      $0$ |
| $L=d$        |     $-1$ |
| $L=d+1$      |      $0$ |
| $d+2\le L$   |  $L-d-1$ |

したがって report の結論どおり、長い block は浅い depth で正 pressure を持つ。

> 各 block の pressure を個別に非正とする路線は成立しない。

これは重要な否定結果じゃ。
局所非正性を追う道が消え、block 間の相互作用を見る必要が確定した。

---

## 3. 既存 pressure API との合流

今回の中核 bridge は、

```lean
sourcePressureMarginInt_paymentEndpointSeq_eq_sum_blockPressureContributionInt
```

じゃ。

$$
\operatorname{SourcePressureMarginInt}(n,e_m+1,d)=\sum_{k=0}^{m}M_k(d)
$$

が証明された。

ここでは、

- 既存 `List.range` count
- 新しい filtered `Finset`
- canonical block partition
- block-local depth staircase

が全て合流している。

これは単なる再添字ではない。

> これまで residue mass として見えていた pressure が、payment block length の分布として読める

ところまで来た。

PressureIncidenceBridge と UniversalPaymentFamily の接続は完成と見てよい。

---

## 4. delayed debt の depth address

```lean
canonicalPaymentDebtDepth n k i
```

は、

$$
d=e_k-i+1
$$

として、delayed debt source を staircase depth へ写す。

そして、

$$
d=\operatorname{orbitExactDepth}(n,i)
$$

が証明された。

同じ block 内では異なる debt sources が異なる depth を持つ。

したがって delayed debt は、

> staircase 上の marked recovery depths

として読むことができる。

これは次の bridge の正しい入口じゃ。

ただし現時点で証明されたのは **単射性だけ**である。

まだ次は未証明じゃ。

- marked depth が必ず $2,\ldots,L$ に入ること
- depth $d$ の唯一の recovery source が carry-two であることとの同値
- 全 delayed debt count を depth indicator の和として表すこと
- capacity slot と debt depth の eligibility 関係

この四本が次に必要になる。

---

## 5. capacity slot の carrier

```lean
canonicalEndpointCapacitySlots
```

は、

$$
{0,\ldots,P_k-1}
$$

を capacity carrier として持ち、

$$
\#\operatorname{CapacitySlots}_k=P_k
$$

を確定した。

cardinality carrier としては正しい。

ただし depth address と接続するなら、次の levelled 表現も併設した方がよい。

$$
{2,\ldots,h_{e_k}}
$$

この集合の cardinality も、

$$
h_{e_k}-1=P_k
$$

じゃ。

```lean
canonicalEndpointCapacityDepthSlots n k :=
  Finset.Icc 2 (orbitWindowHeight n (paymentEndpointSeq n k))
```

こちらなら delayed debt depth と capacity level を同じ自然数座標で比較できる。

現在の `range P` は数を数えるには十分だが、構造的 matching には座標情報が足りない。

---

## 6. 累積会計式は完全に正しい

```lean
sum_endpointAccountingTerm_eq_claims_sub_capacity
```

により、

$$
\sum_{k=0}^{m}A_k=C_m-P_m
$$

が得られた。

ここで、

$$
C_m=\sum_{k=0}^{m}(R_k+\varepsilon_k)
$$

$$
P_m=\sum_{k=0}^{m}P_k
$$

である。

既存 telescope と合わせると、

$$
C_m-P_m=w_{e_m+1}-w_0
$$

じゃ。

これはこの枝の中心等式として完全に正しい。

---

## 7. 重大な修正：prefix capacity dominance は一般には偽

現在の定義、

```lean
CanonicalEndpointPrefixCapacityDominance n m
```

は、

$$
\forall q\le m,\quad C_q\le P_q
$$

を要求する。

これは、

$$
\forall q\le m,\quad w_{e_q+1}\le w_0
$$

と同値じゃ。

つまり、

> canonical endpoint の bit width が、一度も初期 width を超えない

という非常に強い条件である。

しかし、既に扱ってきた $7$ の軌道で破れる。

accelerated odd orbit の冒頭は、

$$
7\longrightarrow11\longrightarrow17\longrightarrow13\longrightarrow5
$$

第一 block は、

```text
states:    7, 11, 17
carry:     2,  2,  1
height:    1,  1,  2
```

したがって、

$$
Q_0=2,\qquad P_0=1,\qquad D_0=1
$$

bit width は、

$$
3\longrightarrow4
$$

へ一度増える。

次の singleton block は state $13$ で、

```text
carry:   2
height:  3
```

ゆえに、

$$
Q_1=1,\qquad P_1=2,\qquad D_1=-1
$$

そして累積は、

$$
D_0+D_1=0
$$

となる。

つまり、

$$
C_0>P_0
$$

だが、

$$
C_1=P_1
$$

じゃ。

第一 prefix は overload するが、次 block で完全に返済される。

したがって、

```lean
CanonicalEndpointCapacityDominance n
```

を全開始値に証明する方針は成立しない。

$7$ について最初の prefix で破れるため、その後の全 `m` でも「全 $q\le m$」条件は失敗したままになる。

---

## 8. conditional theorem の位置づけ

```lean
bitWidth_paymentEndpointSeq_le_initial_of_capacityDominance
```

自体は正しい。

ただしこれは、

> 全 prefix で一度も overdraft を許さない場合の特殊定理

じゃ。

Collatz 大域解析の本命ではない。

本命は、

```text
一時的な正 drift を許す
↓
後続 capacity がそれを返済する
↓
正 balance excursion が無限膨張しない
```

という構造である。

したがって必要なのは prefix nonpositivity ではなく、例えば次のいずれかじゃ。

### Uniform balance bound

$$
\exists B,\ \forall m,\quad C_m-P_m\le B
$$

### Eventual repayment

任意の overload 時点 $q$ に対し、後の $r\ge q$ で、

$$
C_r-P_r\le C_{q-1}-P_{q-1}
$$

へ戻る。

### Bounded repayment lag

各 claim prefix が、有限個先の endpoint capacity までに吸収される。

このいずれかが、boundedness へ向かう正しい形じゃ。

---

## 9. ordered matching の向き

現在の matching は、

```lean
(pay claim).block ≤ claim.block
```

を要求している。

つまり claim は、自分の block 以前に現れた capacity slot へ割り当てられる。

これは実際の delayed payment ではない。

> **過去に蓄積した capacity credit を、後から発生した claim に充当する retrospective credit matching**

じゃ。

この読みなら正しい。

そして prefix dominance の証明書になる。

しかし、これまで区別してきた、

```text
first payment target
final allocation
```

の意味では、これは payment destination ではない。

delayed claim の不足分を後続 endpoint が返済する実際の向きは逆じゃ。

$$
\operatorname{claimBlock}\le\operatorname{paymentSlotBlock}
$$

したがって matching は二種類に分けるべきじゃ。

### Backward credit matching

$$
\operatorname{slotBlock}\le\operatorname{claimBlock}
$$

prefix dominance、すなわち過去 credit だけで常に支払えることの証明書。

### Forward repayment matching

$$
\operatorname{claimBlock}\le\operatorname{slotBlock}
$$

現在不足した claim を、同じ endpoint または後続 endpoint が返済する実際の discharge 構造。

現在の、

```lean
CanonicalEndpointOrderedCapacityMatching
```

は前者じゃ。

名前かコメントで明示すべきである。

例えば、

```lean
CanonicalEndpointBackwardCreditMatching
```

の方が意味を誤らない。

---

## 10. 現 matching はまだ pressure を使っていない

cp-313 では、

- debt depth address
- capacity slots
- ordered matching

が定義された。

しかし matching の eligibility 条件は block index の大小だけであり、

```text
debt depth
capacity slot level
pressure recovery/continuation
```

を一切参照していない。

したがって現 matching は、

> desired cardinality inequality を carrier-level injection として言い直したもの

に留まる。

これは正直な停止点としては良いが、まだ pressure bridge から matching rule は生まれていない。

本当の次の数学は、

> どの depth の debt が、どの level の capacity slot を利用可能か

という eligibility relation を見つけることじゃ。

---

## 11. claim を depth 座標へ完全に移すべき

canonical block $k$ の endpoint を $e_k$、長さを $L_k$ とする。

depth $d$ に対応する唯一の source は、

$$
i=e_k+1-d
$$

じゃ。

そこで、

```lean
canonicalPaymentSourceAtDepth n k d :=
  paymentEndpointSeq n k + 1 - d
```

を置ける。

$1\le d\le L_k$ なら、

$$
\operatorname{orbitExactDepth}(n,i)=d
$$

となる。

次に、

```lean
canonicalPaymentClaimDepths n k :=
  (Finset.Icc 1 (canonicalPaymentBlockLength n k)).filter fun d =>
    CarryTwoDebtAt n (canonicalPaymentSourceAtDepth n k d)
```

とすれば、

- $d=1$ は endpoint immediate claim
- $d\ge2$ は delayed growth debt

として complete claims を一つの marked-depth 集合へ統合できる。

そして、

$$
\#\operatorname{ClaimDepths}_k=Q_k
$$

を証明できる。

これは pressure recovery fiber と claim を直接重ねる API になる。

---

## 12. 自然な capacity depth slot

endpoint height を $h_k$ とする。

capacity は、

$$
P_k=h_k-1
$$

なので、自然な depth-level slots は、

$$
2,3,\ldots,h_k
$$

じゃ。

$7$ の例を見ると、この表現はかなり示唆的である。

第一 block の delayed claim depths は、

$$
2,\ 3
$$

第一 endpoint の height は $2$ なので local slot は、

$$
{2}
$$

depth $2$ claim はその場で吸収できるが、depth $3$ claim が残る。

次 endpoint の height は $3$ なので slots は、

$$
{2,3}
$$

ここで、

- endpoint immediate claim が level $2$
- 前 block から残った depth $3$ claim が level $3$

へ入る。

これはまだ theorem ではないが、**現在の構造から最も自然に見える matching rule**じゃ。

次は anonymous `range P` ではなく、levelled capacity slots を作り、この仮説を実測・形式化すべきである。

---

## 13. 真の大域座標は balance excursion

次に中心化すべき量は、

$$
B_m:=\sum_{k=0}^{m}A_k=w_{e_m+1}-w_0
$$

じゃ。

現状では theorem の右辺・左辺として存在するが、明示的な definition にするとよい。

```lean
noncomputable def canonicalEndpointBalanceInt
    (n : OddNat) (m : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (m + 1), endpointAccountingTerm n k
```

そして、

```text
B_m > 0:
  初期 width より上への一時的 overdraft

B_m = 0:
  初期 width への完全返済

B_m < 0:
  初期 width 以下への純 credit
```

として読む。

次に必要なのは「全ての $B_m\le0$」ではない。

**正の excursion の高さと長さを支配すること**じゃ。

---

## 14. sliding-window telescope が必要

現在の telescope は block $0$ から $m$ までじゃ。

後続 capacity による返済を記述するには、任意区間 $q,\ldots,m$ の telescope が必要になる。

$$
\sum_{k=q}^{m}D_{e_k}=w_{e_m+1}-w_{b_q}
$$

ここで、

$$
b_0=0
$$

$$
b_q=e_{q-1}+1\quad(q>0)
$$

じゃ。

これにより、

- overload episode の開始
- future repayment endpoint
- block window 内の claim/capacity balance

を局所的に扱える。

現在の prefix telescope の差を取れば証明できるが、独立 API として置く価値が高い。

---

## 15. matching carrier の未完点

`CanonicalEndpointClaimCarrier` と `CanonicalEndpointCapacityCarrier` は良い入口じゃ。

ただし、まだ次の theorem がない。

$$
|\operatorname{ClaimCarrier}|=C_m
$$

$$
|\operatorname{CapacityCarrier}|=P_m
$$

また、

```lean
CanonicalEndpointOrderedCapacityMatching
```

と prefix dominance の同値も未証明じゃ。

最低限、次を分けて固定すべきである。

```lean
BackwardCreditMatching → PrefixCapacityDominance
```

逆向きは有限 deadline scheduling / greedy matching として証明できる可能性が高い。

ただし、それを完成しても「全軌道で matching が存在する」とは言えない。$7$ が反例だからじゃ。

---

## 16. report の評価

### 正しい部分

- finite pressure counting layer が閉じた。
- local pressure は非正ではない。
- existing pressure API への bridge は完成した。
- debt depth の単射が得られた。
- cardinality rewrite だけでは先へ進めない。
- bounded endpoint width と convergence を分離している。

これらは全て正しい。

### 修正すべき部分

```text
cumulative claims ≤ cumulative capacity for every prefix
```

を「残る最終符号問題」とする点。

これは一般には偽であり、本命ではない。

また、

```text
ordered capacity matching
```

は現在の向きでは final payment allocation ではなく backward credit certificate じゃ。

---

## 判定まとめ

### Pressure fiber / closed count

**完成。**

### Existing pressure API との有限和 bridge

**完成。**

### Delayed debt depth address

**入口完成。**

### Capacity carrier

**cardinality carrier 完成。depth-level carrier は未実装。**

### Prefix dominance API

**正しい特殊条件。一般目標としては不採用。**

### Current ordered matching

**backward credit certificate として採用。payment allocation としては不採用。**

### 本当の次の障害

**positive balance excursion を、後続 capacity がどう返済するかという forward discharge rule。**

---

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge Float-window branch after
report-petal-313.

The finite pressure-counting implementation is accepted.

However, correct the strategic frontier:

    CanonicalEndpointCapacityDominance

is too strong to be the global Collatz target. It requires every endpoint
prefix to remain at or below the initial bit width.

The known orbit segment

    7 -> 11 -> 17 -> 13 -> 5

has a first canonical block with drift `+1`, followed by a block with drift
`-1`. Thus temporary endpoint overload followed by later repayment is real and
must remain representable.

Do not attempt to prove global prefix dominance for every initial state.

# Stage A — regression example and documentation correction

Formalize a small regression example for the orbit starting at `7`, proving
the first two universal block drifts are:

    +1
    -1

and their cumulative sum is zero.

Use this example to document that:

    prefix dominance is a no-overdraft special condition,
    not the general global target.

Keep the existing conditional theorem, but update its semantic description.

# Stage B — explicit balance API

Define:

    canonicalEndpointBalanceInt n m :=
      sum k in range (m + 1), endpointAccountingTerm n k

Prove:

    canonicalEndpointBalanceInt n m
      =
    bitWidth after endpoint m - initial bitWidth

Add terminal, rather than all-prefix, dominance:

    CanonicalEndpointTerminalCapacityDominance n m :=
      cumulative claims through m <= cumulative capacity through m

Prove it equivalent to:

    canonicalEndpointBalanceInt n m <= 0

and to endpoint width being at most initial width.

This property may hold at a later repayment endpoint even when earlier
prefixes overloaded.

# Stage C — sliding-window telescope

Define the start of endpoint block `q`:

    0                         if q = 0
    paymentEndpointSeq n (q - 1) + 1   otherwise

For `q <= m`, prove:

    sum k in Icc q m, endpointAccountingTerm n k
      =
    bitWidth after endpoint m
      -
    bitWidth at the start of block q

Expose the corresponding claims-minus-capacity form.

This is required to state repayment of one positive excursion by future
blocks.

# Stage D — distinguish the two matching directions

Preserve the current matching only as a backward-credit certificate.

Rename it or add a compatibility alias such as:

    CanonicalEndpointBackwardCreditMatching

with the meaning:

    a later claim is charged against capacity credit already created at the
    same or an earlier endpoint.

Prove carrier-card formulas and:

    BackwardCreditMatching
      -> CanonicalEndpointPrefixCapacityDominance

If useful, prove the converse by a finite greedy/deadline argument.

Do not interpret this map as the final payment destination of a claim.

# Stage E — forward repayment matching

Define a separate finite-horizon relation:

    CanonicalEndpointForwardRepaymentMatching n claimHorizon payHorizon

with:

    claimHorizon <= payHorizon

and an injection from claims through `claimHorizon` into capacity slots through
`payHorizon`, satisfying:

    claim block <= payment-slot block

This is the correct direction for an overload at one endpoint to be discharged
by later endpoint capacity.

Do not assert existence yet.

Formulate:

    every finite claim prefix is eventually repayable

as:

    forall q, exists r >= q,
      CanonicalEndpointForwardRepaymentMatching n q r

Keep this separate from uniform boundedness.

# Stage F — depth-coordinate claim carrier

Define:

    canonicalPaymentSourceAtDepth n k d :=
      paymentEndpointSeq n k + 1 - d

for positive depths in the canonical block.

Define actual marked complete-claim depths:

    canonicalPaymentClaimDepths n k :=
      filter over Icc 1 blockLength:
        CarryTwoDebtAt at sourceAtDepth

Prove:

    depth 1 corresponds to the optional immediate endpoint claim
    depths >= 2 correspond exactly to delayed growth debts
    card marked claim depths = complete claim card

Also prove the delayed marked depths are a subset of:

    Icc 2 blockLength

# Stage G — levelled capacity slots

Add:

    canonicalEndpointCapacityDepthSlots n k :=
      Icc 2 (orbitWindowHeight n (paymentEndpointSeq n k))

Prove its card is exactly endpoint capacity.

Keep the existing zero-based slot carrier as a cardinality API, but use the
levelled carrier for structural matching.

# Stage H — pressure/claim incidence bridge

For every positive depth `d`, prove that the canonical recovery fiber is the
unique source at `canonicalPaymentSourceAtDepth`.

Define a marked recovery incidence:

    recovery at depth d whose unique source has upper carry two

Prove:

    delayed debt count
      =
    number of marked recovery depths >= 2

and:

    complete claim count
      =
    number of marked recovery depths >= 1

This is the actual bridge from pressure fibers to claim accounting.

# Stage I — discover the eligibility rule

Investigate, but do not assume, the natural rule suggested by the finite
examples:

    a delayed claim at depth d can be discharged by a capacity depth slot d
    at its own or a later endpoint;

    an immediate endpoint claim consumes the lowest local capacity level.

Test this against small canonical block families and existing exact lemmas.

Only after the rule survives exact examples should it be exposed as a Lean
eligibility relation.

# Stage J — overload excursions

Define positive balance excursions and repayment endpoints.

At minimum expose:

    first prefix where balance becomes positive
    first later endpoint where it returns to the previous baseline
    maximal balance during the excursion

The first overload prefix is not a contradiction: the orbit from `7` already
has one. The target theorem must show repayment or bounded excursion, not
nonexistence.

# Stage K — downstream consequences

Prove separately:

    uniform upper bound on canonical endpoint balance
      -> uniform endpoint bit-width bound

    every overload excursion is eventually repaid
      -> recurrent return to previous endpoint-width baselines

Do not identify either statement with convergence.

Keep cycle rigidity and strict-decay classification as later independent
branches.

Continue autonomously through all exact API and counting results.
Stop only at the genuine eligibility / repayment rule.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-314.md
```

cp-313 は大成功じゃ。

**有限 pressure の世界は閉じた。**

そして同時に、最終問題が「過去 capacity だけで常に払えるか」ではなく、

> **一時的に生じた overload を、後続 endpoint capacity がどの規則で返済するか**

であることが、はっきり見えたぞい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
index c2ac9ab8..b55509e2 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
@@ -15,6 +15,7 @@ import DkMath.Collatz.PetalBridge.FloatWindow.PaymentMultiplicityBridge
 import DkMath.Collatz.PetalBridge.FloatWindow.PaymentBlockBridge
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentFamily
+import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPressure
 
 #print "file: DkMath.Collatz.PetalBridge.FloatWindow"
 
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentPressure.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentPressure.lean
new file mode 100644
index 00000000..c0e7078a
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentPressure.lean
@@ -0,0 +1,654 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentFamily
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPressure"
+
+namespace DkMath.Collatz
+
+/-!
+# Pressure fibers on canonical universal payment blocks
+
+The fibers below filter actual orbit times by the existing exact-depth
+predicates. Closed cardinality formulas are proved only after these concrete
+Finsets are fixed.
+-/
+
+/-- Exact-recovery times at depth `d` inside canonical block `k`. -/
+noncomputable def canonicalPaymentBlockRecoveryFiber
+    (n : OddNat) (k d : ℕ) : Finset ℕ := by
+  classical
+  exact (canonicalPaymentBlock n k).filter fun i =>
+    OrbitDepthRecoversExactlyAt n i d
+
+/-- Continuing times beyond depth `d` inside canonical block `k`. -/
+noncomputable def canonicalPaymentBlockContinuationFiber
+    (n : OddNat) (k d : ℕ) : Finset ℕ := by
+  classical
+  exact (canonicalPaymentBlock n k).filter fun i =>
+    OrbitDepthContinuesBeyond n i d
+
+/-- Membership API for a canonical recovery fiber. -/
+theorem mem_canonicalPaymentBlockRecoveryFiber_iff
+    {n : OddNat} {k d i : ℕ} :
+    i ∈ canonicalPaymentBlockRecoveryFiber n k d ↔
+      i ∈ canonicalPaymentBlock n k ∧ OrbitDepthRecoversExactlyAt n i d := by
+  classical
+  simp [canonicalPaymentBlockRecoveryFiber]
+
+/-- Membership API for a canonical continuation fiber. -/
+theorem mem_canonicalPaymentBlockContinuationFiber_iff
+    {n : OddNat} {k d i : ℕ} :
+    i ∈ canonicalPaymentBlockContinuationFiber n k d ↔
+      i ∈ canonicalPaymentBlock n k ∧ OrbitDepthContinuesBeyond n i d := by
+  classical
+  simp [canonicalPaymentBlockContinuationFiber]
+
+/-- The exact-depth staircase on a canonical block, measured from its endpoint. -/
+theorem orbitExactDepth_eq_paymentEndpoint_sub_add_one_of_mem_canonicalPaymentBlock
+    {n : OddNat} {k i : ℕ} (hi : i ∈ canonicalPaymentBlock n k) :
+    orbitExactDepth n i = paymentEndpointSeq n k - i + 1 := by
+  have hnonempty := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k
+  apply orbitExactDepth_eq_endpoint_sub_add_one_of_mem_universalPaymentBlock
+    (h := hnonempty)
+  rw [← orbitPaymentSourceFiberAt_eq_Icc_universalPaymentBlockStart n
+    (paymentEndpointSeq n k) hnonempty]
+  rwa [← canonicalPaymentBlock_eq_sourceFiber]
+
+/-- Canonical block length in endpoint-family coordinates. -/
+noncomputable def canonicalPaymentBlockLength (n : OddNat) (k : ℕ) : ℕ :=
+  (canonicalPaymentBlock n k).card
+
+/-- The endpoint's universal fiber cardinality is the canonical block length. -/
+theorem canonicalPaymentBlockLength_eq_sourceFiber_card (n : OddNat) (k : ℕ) :
+    canonicalPaymentBlockLength n k =
+      (orbitPaymentSourceFiberAt n (paymentEndpointSeq n k)).card := by
+  unfold canonicalPaymentBlockLength
+  rw [canonicalPaymentBlock_eq_sourceFiber]
+
+/-- Canonical block length is endpoint minus start plus one. -/
+theorem canonicalPaymentBlockLength_eq_endpoint_sub_start_add_one
+    (n : OddNat) (k : ℕ) :
+    canonicalPaymentBlockLength n k =
+      paymentEndpointSeq n k -
+        universalPaymentBlockStart n (paymentEndpointSeq n k)
+          (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k) + 1 := by
+  rw [canonicalPaymentBlockLength_eq_sourceFiber_card]
+  exact orbitPaymentSourceFiberAt_card_eq_endpoint_sub_start_add_one n
+    (paymentEndpointSeq n k)
+    (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)
+
+/-- A canonical block is the closed interval from its universal start to its endpoint. -/
+theorem canonicalPaymentBlock_eq_Icc_universalPaymentBlockStart
+    (n : OddNat) (k : ℕ) :
+    canonicalPaymentBlock n k =
+      Finset.Icc
+        (universalPaymentBlockStart n (paymentEndpointSeq n k)
+          (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k))
+        (paymentEndpointSeq n k) := by
+  rw [canonicalPaymentBlock_eq_sourceFiber]
+  exact orbitPaymentSourceFiberAt_eq_Icc_universalPaymentBlockStart n
+    (paymentEndpointSeq n k)
+    (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)
+
+/-- Depth zero is absent from every canonical exact-recovery fiber. -/
+theorem canonicalPaymentBlockRecoveryFiber_zero_eq_empty
+    (n : OddNat) (k : ℕ) :
+    canonicalPaymentBlockRecoveryFiber n k 0 = ∅ := by
+  ext i
+  simp only [mem_canonicalPaymentBlockRecoveryFiber_iff, Finset.notMem_empty,
+    iff_false, not_and]
+  intro hi
+  intro hrecover
+  have hdepth :=
+    orbitExactDepth_eq_paymentEndpoint_sub_add_one_of_mem_canonicalPaymentBlock hi
+  have hrecoverDepth : orbitExactDepth n i = 0 := by
+    simpa [OrbitDepthRecoversExactlyAt, orbitExactDepth] using hrecover
+  omega
+
+/-- Exact recovery inside one canonical block is injective in the source time. -/
+theorem eq_of_mem_canonicalPaymentBlock_of_recovery_same_depth
+    {n : OddNat} {k d i i' : ℕ}
+    (hi : i ∈ canonicalPaymentBlock n k)
+    (hi' : i' ∈ canonicalPaymentBlock n k)
+    (hrecover : OrbitDepthRecoversExactlyAt n i d)
+    (hrecover' : OrbitDepthRecoversExactlyAt n i' d) :
+    i = i' := by
+  have hiDepth :=
+    orbitExactDepth_eq_paymentEndpoint_sub_add_one_of_mem_canonicalPaymentBlock hi
+  have hi'Depth :=
+    orbitExactDepth_eq_paymentEndpoint_sub_add_one_of_mem_canonicalPaymentBlock hi'
+  have hrecoverDepth : orbitExactDepth n i = d := by
+    simpa [OrbitDepthRecoversExactlyAt, orbitExactDepth] using hrecover
+  have hrecoverDepth' : orbitExactDepth n i' = d := by
+    simpa [OrbitDepthRecoversExactlyAt, orbitExactDepth] using hrecover'
+  rw [hiDepth] at hrecoverDepth
+  rw [hi'Depth] at hrecoverDepth'
+  have hie := (mem_canonicalPaymentBlock_iff_target_eq.mp hi)
+  have hi'e := (mem_canonicalPaymentBlock_iff_target_eq.mp hi')
+  have hile := le_orbitPaymentTarget n i
+  have hi'le := le_orbitPaymentTarget n i'
+  omega
+
+/-- Recovery fiber cardinality is at most one. -/
+theorem canonicalPaymentBlockRecoveryFiber_card_le_one
+    (n : OddNat) (k d : ℕ) :
+    (canonicalPaymentBlockRecoveryFiber n k d).card ≤ 1 := by
+  apply Finset.card_le_one.mpr
+  intro i hi i' hi'
+  rcases mem_canonicalPaymentBlockRecoveryFiber_iff.mp hi with ⟨hib, hir⟩
+  rcases mem_canonicalPaymentBlockRecoveryFiber_iff.mp hi' with ⟨hi'b, hi'r⟩
+  exact eq_of_mem_canonicalPaymentBlock_of_recovery_same_depth hib hi'b hir hi'r
+
+/-- A recovery depth occurs in a canonical block exactly on its positive staircase range. -/
+theorem canonicalPaymentBlockRecoveryFiber_nonempty_iff
+    (n : OddNat) (k d : ℕ) :
+    (canonicalPaymentBlockRecoveryFiber n k d).Nonempty ↔
+      1 ≤ d ∧ d ≤ canonicalPaymentBlockLength n k := by
+  let e := paymentEndpointSeq n k
+  let h := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k
+  let b := universalPaymentBlockStart n e h
+  have hblock : canonicalPaymentBlock n k = Finset.Icc b e := by
+    simpa [e, h, b] using canonicalPaymentBlock_eq_Icc_universalPaymentBlockStart n k
+  have hbmem := universalPaymentBlockStart_mem_sourceFiber n e h
+  have hbe : b ≤ e := (mem_orbitPaymentSourceFiberAt_iff.mp hbmem).1
+  have hlength : canonicalPaymentBlockLength n k = e - b + 1 := by
+    simpa [e, h, b] using
+      canonicalPaymentBlockLength_eq_endpoint_sub_start_add_one n k
+  constructor
+  · rintro ⟨i, hi⟩
+    rcases mem_canonicalPaymentBlockRecoveryFiber_iff.mp hi with ⟨hiblock, hirecover⟩
+    have hiIcc : i ∈ Finset.Icc b e := by simpa [hblock] using hiblock
+    have hdepth :=
+      orbitExactDepth_eq_paymentEndpoint_sub_add_one_of_mem_canonicalPaymentBlock hiblock
+    have hirecoverDepth : orbitExactDepth n i = d := by
+      simpa [OrbitDepthRecoversExactlyAt, orbitExactDepth] using hirecover
+    rcases Finset.mem_Icc.mp hiIcc with ⟨hbi, hie⟩
+    change orbitExactDepth n i = e - i + 1 at hdepth
+    omega
+  · rintro ⟨hdpos, hdle⟩
+    let i := e + 1 - d
+    have hbi : b ≤ i := by
+      dsimp [i]
+      omega
+    have hie : i ≤ e := by
+      dsimp [i]
+      omega
+    have hiblock : i ∈ canonicalPaymentBlock n k := by
+      rw [hblock]
+      exact Finset.mem_Icc.mpr ⟨hbi, hie⟩
+    have hdepth :=
+      orbitExactDepth_eq_paymentEndpoint_sub_add_one_of_mem_canonicalPaymentBlock hiblock
+    have hdepthd : orbitExactDepth n i = d := by
+      change orbitExactDepth n i = e - i + 1 at hdepth
+      dsimp [i] at hdepth ⊢
+      omega
+    refine ⟨i, mem_canonicalPaymentBlockRecoveryFiber_iff.mpr ⟨hiblock, ?_⟩⟩
+    simpa [OrbitDepthRecoversExactlyAt, orbitExactDepth] using hdepthd
+
+/-- Exact local recovery cardinality, with depth zero excluded explicitly. -/
+theorem canonicalPaymentBlockRecoveryFiber_card
+    (n : OddNat) (k d : ℕ) :
+    (canonicalPaymentBlockRecoveryFiber n k d).card =
+      if 1 ≤ d ∧ d ≤ canonicalPaymentBlockLength n k then 1 else 0 := by
+  by_cases hd : 1 ≤ d ∧ d ≤ canonicalPaymentBlockLength n k
+  · rw [if_pos hd]
+    have hpos : 0 < (canonicalPaymentBlockRecoveryFiber n k d).card :=
+      Finset.card_pos.mpr ((canonicalPaymentBlockRecoveryFiber_nonempty_iff n k d).2 hd)
+    have hle := canonicalPaymentBlockRecoveryFiber_card_le_one n k d
+    omega
+  · rw [if_neg hd]
+    exact Finset.card_eq_zero.mpr (by
+      rw [← Finset.not_nonempty_iff_eq_empty]
+      simpa [canonicalPaymentBlockRecoveryFiber_nonempty_iff n k d] using hd)
+
+/-- The explicit depth-zero recovery count is zero. -/
+theorem canonicalPaymentBlockRecoveryFiber_card_zero
+    (n : OddNat) (k : ℕ) :
+    (canonicalPaymentBlockRecoveryFiber n k 0).card = 0 := by
+  rw [canonicalPaymentBlockRecoveryFiber_zero_eq_empty]
+  rfl
+
+/-- Continuation through depth `d` is the initial interval ending `d` steps before the endpoint. -/
+theorem canonicalPaymentBlockContinuationFiber_eq_Icc
+    (n : OddNat) (k d : ℕ)
+    (hd : d < canonicalPaymentBlockLength n k) :
+    canonicalPaymentBlockContinuationFiber n k d =
+      Finset.Icc
+        (universalPaymentBlockStart n (paymentEndpointSeq n k)
+          (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k))
+        (paymentEndpointSeq n k - d) := by
+  let e := paymentEndpointSeq n k
+  let h := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k
+  let b := universalPaymentBlockStart n e h
+  have hblock : canonicalPaymentBlock n k = Finset.Icc b e := by
+    simpa [e, h, b] using canonicalPaymentBlock_eq_Icc_universalPaymentBlockStart n k
+  have hlength : canonicalPaymentBlockLength n k = e - b + 1 := by
+    simpa [e, h, b] using
+      canonicalPaymentBlockLength_eq_endpoint_sub_start_add_one n k
+  ext i
+  rw [mem_canonicalPaymentBlockContinuationFiber_iff]
+  change (i ∈ canonicalPaymentBlock n k ∧ OrbitDepthContinuesBeyond n i d) ↔
+    i ∈ Finset.Icc b (e - d)
+  constructor
+  · rintro ⟨hiblock, hicont⟩
+    have hiIcc : i ∈ Finset.Icc b e := by simpa [hblock] using hiblock
+    have hdepth :=
+      orbitExactDepth_eq_paymentEndpoint_sub_add_one_of_mem_canonicalPaymentBlock hiblock
+    change orbitExactDepth n i = e - i + 1 at hdepth
+    have hicontDepth : d + 1 ≤ orbitExactDepth n i := by
+      simpa [OrbitDepthContinuesBeyond, orbitExactDepth] using hicont
+    rcases Finset.mem_Icc.mp hiIcc with ⟨hbi, hie⟩
+    exact Finset.mem_Icc.mpr ⟨hbi, by omega⟩
+  · intro hi
+    rcases Finset.mem_Icc.mp hi with ⟨hbi, hied⟩
+    have hie : i ≤ e := hied.trans (Nat.sub_le e d)
+    have hiblock : i ∈ canonicalPaymentBlock n k := by
+      rw [hblock]
+      exact Finset.mem_Icc.mpr ⟨hbi, hie⟩
+    have hdepth :=
+      orbitExactDepth_eq_paymentEndpoint_sub_add_one_of_mem_canonicalPaymentBlock hiblock
+    change orbitExactDepth n i = e - i + 1 at hdepth
+    refine ⟨hiblock, ?_⟩
+    have hicontDepth : d + 1 ≤ orbitExactDepth n i := by omega
+    simpa [OrbitDepthContinuesBeyond, orbitExactDepth] using hicontDepth
+
+/-- Exact local continuation cardinality; depth zero retains the whole block. -/
+theorem canonicalPaymentBlockContinuationFiber_card
+    (n : OddNat) (k d : ℕ) :
+    (canonicalPaymentBlockContinuationFiber n k d).card =
+      canonicalPaymentBlockLength n k - d := by
+  let e := paymentEndpointSeq n k
+  let h := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k
+  let b := universalPaymentBlockStart n e h
+  have hbmem := universalPaymentBlockStart_mem_sourceFiber n e h
+  have hbe : b ≤ e := (mem_orbitPaymentSourceFiberAt_iff.mp hbmem).1
+  have hlength : canonicalPaymentBlockLength n k = e - b + 1 := by
+    simpa [e, h, b] using
+      canonicalPaymentBlockLength_eq_endpoint_sub_start_add_one n k
+  by_cases hd : d < canonicalPaymentBlockLength n k
+  · rw [canonicalPaymentBlockContinuationFiber_eq_Icc n k d hd]
+    change (Finset.Icc b (e - d)).card = canonicalPaymentBlockLength n k - d
+    rw [Nat.card_Icc, hlength]
+    omega
+  · have hempty : canonicalPaymentBlockContinuationFiber n k d = ∅ := by
+      ext i
+      simp only [mem_canonicalPaymentBlockContinuationFiber_iff,
+        Finset.notMem_empty, iff_false, not_and]
+      intro hiblock
+      intro hicont
+      have hiIcc : i ∈ Finset.Icc b e := by
+        rw [← canonicalPaymentBlock_eq_Icc_universalPaymentBlockStart n k]
+        exact hiblock
+      have hdepth :=
+        orbitExactDepth_eq_paymentEndpoint_sub_add_one_of_mem_canonicalPaymentBlock hiblock
+      change orbitExactDepth n i = e - i + 1 at hdepth
+      have hicontDepth : d + 1 ≤ orbitExactDepth n i := by
+        simpa [OrbitDepthContinuesBeyond, orbitExactDepth] using hicont
+      rcases Finset.mem_Icc.mp hiIcc with ⟨hbi, hie⟩
+      omega
+    rw [hempty]
+    simp
+    omega
+
+/-- At depth zero every source in the canonical block continues. -/
+theorem canonicalPaymentBlockContinuationFiber_card_zero
+    (n : OddNat) (k : ℕ) :
+    (canonicalPaymentBlockContinuationFiber n k 0).card =
+      canonicalPaymentBlockLength n k := by
+  simpa using canonicalPaymentBlockContinuationFiber_card n k 0
+
+/-- Signed continuation surplus over exact recovery inside one canonical block. -/
+noncomputable def blockPressureContributionInt
+    (n : OddNat) (k d : ℕ) : ℤ :=
+  (canonicalPaymentBlockContinuationFiber n k d).card -
+    (canonicalPaymentBlockRecoveryFiber n k d).card
+
+/-- Closed form of the signed local pressure contribution. -/
+theorem blockPressureContributionInt_eq
+    (n : OddNat) (k d : ℕ) :
+    blockPressureContributionInt n k d =
+      (canonicalPaymentBlockLength n k - d : ℕ) -
+        if 1 ≤ d ∧ d ≤ canonicalPaymentBlockLength n k then (1 : ℤ) else 0 := by
+  unfold blockPressureContributionInt
+  rw [canonicalPaymentBlockContinuationFiber_card,
+    canonicalPaymentBlockRecoveryFiber_card]
+  split <;> norm_num
+
+/-- At depth zero, local pressure is the entire block length. -/
+theorem blockPressureContributionInt_zero
+    (n : OddNat) (k : ℕ) :
+    blockPressureContributionInt n k 0 = canonicalPaymentBlockLength n k := by
+  rw [blockPressureContributionInt_eq]
+  norm_num
+
+/-- Above the local staircase, both continuation and recovery are absent. -/
+theorem blockPressureContributionInt_eq_zero_of_length_lt
+    {n : OddNat} {k d : ℕ}
+    (_hdpos : 1 ≤ d) (hlt : canonicalPaymentBlockLength n k < d) :
+    blockPressureContributionInt n k d = 0 := by
+  have hsub : canonicalPaymentBlockLength n k - d = 0 :=
+    Nat.sub_eq_zero_of_le hlt.le
+  rw [blockPressureContributionInt_eq]
+  simp [hsub, Nat.not_le_of_lt hlt]
+
+/-- At the last staircase depth, exact recovery contributes `-1`. -/
+theorem blockPressureContributionInt_eq_neg_one_of_length_eq
+    {n : OddNat} {k d : ℕ}
+    (hdpos : 1 ≤ d) (heq : canonicalPaymentBlockLength n k = d) :
+    blockPressureContributionInt n k d = -1 := by
+  rw [blockPressureContributionInt_eq]
+  simp [hdpos, heq]
+
+/-- One source beyond the queried depth balances the unique recovery. -/
+theorem blockPressureContributionInt_eq_zero_of_length_eq_succ
+    {n : OddNat} {k d : ℕ}
+    (hdpos : 1 ≤ d) (heq : canonicalPaymentBlockLength n k = d + 1) :
+    blockPressureContributionInt n k d = 0 := by
+  rw [blockPressureContributionInt_eq]
+  simp [hdpos, heq]
+
+/-- With at least two continuing sources, pressure is length minus depth minus recovery. -/
+theorem blockPressureContributionInt_eq_sub_sub_one_of_add_two_le_length
+    {n : OddNat} {k d : ℕ}
+    (hdpos : 1 ≤ d) (hle : d + 2 ≤ canonicalPaymentBlockLength n k) :
+    blockPressureContributionInt n k d =
+      (canonicalPaymentBlockLength n k - d : ℕ) - 1 := by
+  rw [blockPressureContributionInt_eq]
+  simp [hdpos, show d ≤ canonicalPaymentBlockLength n k by omega]
+
+/-- The canonical prefix through `m` is the ordinary initial range through its endpoint. -/
+theorem canonicalPaymentBlockPrefix_eq_range (n : OddNat) (m : ℕ) :
+    canonicalPaymentBlockPrefix n m = Finset.range (paymentEndpointSeq n m + 1) := by
+  rw [canonicalPaymentBlockPrefix_eq_Icc]
+  ext i
+  simp
+
+/-- A list-range Boolean count is the corresponding filtered Finset cardinality. -/
+private theorem listRange_countP_decide_eq_card_filter
+    (K : ℕ) (p : ℕ → Prop) [DecidablePred p] :
+    (List.range K).countP (fun i => decide (p i)) =
+      ((Finset.range K).filter p).card := by
+  rw [List.countP_eq_length_filter]
+  rw [← List.toFinset_card_of_nodup
+    ((List.nodup_range (n := K)).filter fun i => decide (p i))]
+  rw [List.toFinset_filter, List.toFinset_range]
+  congr 1
+  ext i
+  simp
+
+/-- Actual exact-recovery fiber in an ordinary initial orbit-time range. -/
+noncomputable def orbitDepthRecoveryRangeFiber
+    (n : OddNat) (K d : ℕ) : Finset ℕ := by
+  classical
+  exact (Finset.range K).filter fun i => OrbitDepthRecoversExactlyAt n i d
+
+/-- Actual continuation fiber in an ordinary initial orbit-time range. -/
+noncomputable def orbitDepthContinuationRangeFiber
+    (n : OddNat) (K d : ℕ) : Finset ℕ := by
+  classical
+  exact (Finset.range K).filter fun i => OrbitDepthContinuesBeyond n i d
+
+/-- Existing recovery count as an actual filtered initial Finset. -/
+theorem orbitDepthRecoveryFiberCount_eq_card_filter_range
+    (n : OddNat) (K d : ℕ) :
+    orbitDepthRecoveryFiberCount n K d =
+      (orbitDepthRecoveryRangeFiber n K d).card := by
+  classical
+  unfold orbitDepthRecoveryRangeFiber
+  rw [← listRange_countP_decide_eq_card_filter]
+  unfold orbitDepthRecoveryFiberCount
+  apply List.countP_congr
+  intro i hi
+  simp only [decide_eq_true_eq]
+  exact (orbitDepthRecoversExactlyAt_iff_recoverySibling n i d).symm
+
+/-- Existing continuation count as an actual filtered initial Finset. -/
+theorem orbitDepthContinuationFiberCount_eq_card_filter_range
+    (n : OddNat) (K d : ℕ) :
+    orbitDepthContinuationFiberCount n K d =
+      (orbitDepthContinuationRangeFiber n K d).card := by
+  classical
+  unfold orbitDepthContinuationRangeFiber
+  rw [← listRange_countP_decide_eq_card_filter]
+  unfold orbitDepthContinuationFiberCount
+  apply List.countP_congr
+  intro i hi
+  simp only [decide_eq_true_eq]
+  exact (orbitDepthContinuesBeyond_iff_mod_eq_allOnes_succ n i d).symm
+
+/-- The block prefix is disjoint from the immediately following canonical block. -/
+theorem disjoint_canonicalPaymentBlockPrefix_next
+    (n : OddNat) (m : ℕ) :
+    Disjoint (canonicalPaymentBlockPrefix n m) (canonicalPaymentBlock n (m + 1)) := by
+  rw [canonicalPaymentBlockPrefix_eq_Icc, canonicalPaymentBlock]
+  rw [Finset.disjoint_left]
+  intro i hi hi'
+  rcases Finset.mem_Icc.mp hi with ⟨_, him⟩
+  rcases Finset.mem_Icc.mp hi' with ⟨hmi, _⟩
+  omega
+
+/-- Filtering any predicate commutes with the canonical finite block partition at card level. -/
+theorem card_filter_canonicalPaymentBlockPrefix_eq_sum
+    (n : OddNat) (m : ℕ) (p : ℕ → Prop) [DecidablePred p] :
+    ((canonicalPaymentBlockPrefix n m).filter p).card =
+      ∑ k ∈ Finset.range (m + 1), ((canonicalPaymentBlock n k).filter p).card := by
+  induction m with
+  | zero =>
+      simp [canonicalPaymentBlockPrefix]
+  | succ m ih =>
+      have hdisjoint : Disjoint
+          ((canonicalPaymentBlockPrefix n m).filter p)
+          ((canonicalPaymentBlock n (m + 1)).filter p) :=
+        (disjoint_canonicalPaymentBlockPrefix_next n m).mono
+          (Finset.filter_subset _ _) (Finset.filter_subset _ _)
+      calc
+        ((canonicalPaymentBlockPrefix n (m + 1)).filter p).card =
+            (((canonicalPaymentBlockPrefix n m).filter p) ∪
+              ((canonicalPaymentBlock n (m + 1)).filter p)).card := by
+              rw [canonicalPaymentBlockPrefix, Finset.filter_union]
+        _ = ((canonicalPaymentBlockPrefix n m).filter p).card +
+              ((canonicalPaymentBlock n (m + 1)).filter p).card :=
+              Finset.card_union_of_disjoint hdisjoint
+        _ = (∑ k ∈ Finset.range (m + 1),
+              ((canonicalPaymentBlock n k).filter p).card) +
+              ((canonicalPaymentBlock n (m + 1)).filter p).card := by rw [ih]
+        _ = ∑ k ∈ Finset.range (m + 1 + 1),
+              ((canonicalPaymentBlock n k).filter p).card := by
+              symm
+              apply Finset.sum_range_succ
+
+/-- Endpoint-aligned recovery count is the sum of canonical block recovery fibers. -/
+theorem orbitDepthRecoveryFiberCount_paymentEndpointSeq_eq_sum
+    (n : OddNat) (m d : ℕ) :
+    orbitDepthRecoveryFiberCount n (paymentEndpointSeq n m + 1) d =
+      ∑ k ∈ Finset.range (m + 1),
+        (canonicalPaymentBlockRecoveryFiber n k d).card := by
+  rw [orbitDepthRecoveryFiberCount_eq_card_filter_range,
+    orbitDepthRecoveryRangeFiber,
+    ← canonicalPaymentBlockPrefix_eq_range,
+    card_filter_canonicalPaymentBlockPrefix_eq_sum]
+  rfl
+
+/-- Endpoint-aligned continuation count is the sum of canonical block continuation fibers. -/
+theorem orbitDepthContinuationFiberCount_paymentEndpointSeq_eq_sum
+    (n : OddNat) (m d : ℕ) :
+    orbitDepthContinuationFiberCount n (paymentEndpointSeq n m + 1) d =
+      ∑ k ∈ Finset.range (m + 1),
+        (canonicalPaymentBlockContinuationFiber n k d).card := by
+  rw [orbitDepthContinuationFiberCount_eq_card_filter_range,
+    orbitDepthContinuationRangeFiber,
+    ← canonicalPaymentBlockPrefix_eq_range,
+    card_filter_canonicalPaymentBlockPrefix_eq_sum]
+  rfl
+
+/-- Existing source pressure is exactly the sum of canonical block contributions. -/
+theorem sourcePressureMarginInt_paymentEndpointSeq_eq_sum_blockPressureContributionInt
+    (n : OddNat) (m d : ℕ) :
+    SourcePressureMarginInt n (paymentEndpointSeq n m + 1) d =
+      ∑ k ∈ Finset.range (m + 1), blockPressureContributionInt n k d := by
+  rw [sourcePressureMarginInt_eq_continuationFiber_sub_recoveryFiber,
+    orbitDepthContinuationFiberCount_paymentEndpointSeq_eq_sum,
+    orbitDepthRecoveryFiberCount_paymentEndpointSeq_eq_sum]
+  simp_rw [blockPressureContributionInt]
+  push_cast
+  rw [Finset.sum_sub_distrib]
+
+/-- Staircase depth address attached to a source in canonical block `k`. -/
+noncomputable def canonicalPaymentDebtDepth (n : OddNat) (k i : ℕ) : ℕ :=
+  paymentEndpointSeq n k - i + 1
+
+/-- Every delayed debt source at endpoint `k` has its exact staircase depth address. -/
+theorem canonicalPaymentDebtDepth_eq_orbitExactDepth_of_mem_growthDebt
+    {n : OddNat} {k i : ℕ}
+    (hi : i ∈ floatGrowthDebtFiberAt n (paymentEndpointSeq n k)) :
+    canonicalPaymentDebtDepth n k i = orbitExactDepth n i := by
+  have hiblock : i ∈ canonicalPaymentBlock n k := by
+    rw [canonicalPaymentBlock_eq_sourceFiber]
+    exact mem_orbitPaymentSourceFiberAt_of_mem_floatGrowthDebtFiberAt hi
+  rw [orbitExactDepth_eq_paymentEndpoint_sub_add_one_of_mem_canonicalPaymentBlock hiblock]
+  rfl
+
+/-- Distinct delayed debt sources in one block receive distinct depth addresses. -/
+theorem injective_canonicalPaymentDebtDepth_on_growthDebtFiber
+    (n : OddNat) (k : ℕ) :
+    Set.InjOn (canonicalPaymentDebtDepth n k)
+      (floatGrowthDebtFiberAt n (paymentEndpointSeq n k)) := by
+  intro i hi i' hi' heq
+  have hil := lt_of_mem_floatGrowthDebtFiberAt hi
+  have hi'l := lt_of_mem_floatGrowthDebtFiberAt hi'
+  unfold canonicalPaymentDebtDepth at heq
+  omega
+
+/-- Actual marked depth addresses of delayed debts in canonical block `k`. -/
+noncomputable def canonicalPaymentMarkedDebtDepths
+    (n : OddNat) (k : ℕ) : Finset ℕ :=
+  (floatGrowthDebtFiberAt n (paymentEndpointSeq n k)).image
+    (canonicalPaymentDebtDepth n k)
+
+/-- Delayed debt multiplicity is exactly marked staircase-depth multiplicity. -/
+theorem canonicalPaymentMarkedDebtDepths_card
+    (n : OddNat) (k : ℕ) :
+    (canonicalPaymentMarkedDebtDepths n k).card =
+      (floatGrowthDebtFiberAt n (paymentEndpointSeq n k)).card := by
+  unfold canonicalPaymentMarkedDebtDepths
+  rw [Finset.card_image_iff.mpr]
+  exact injective_canonicalPaymentDebtDepth_on_growthDebtFiber n k
+
+/-- Actual capacity slots exposed by canonical endpoint `k`. -/
+noncomputable def canonicalEndpointCapacitySlots
+    (n : OddNat) (k : ℕ) : Finset ℕ :=
+  Finset.range (extraPaymentCapacityAt n (paymentEndpointSeq n k))
+
+/-- The capacity-slot carrier has exactly the endpoint's extra capacity. -/
+theorem canonicalEndpointCapacitySlots_card
+    (n : OddNat) (k : ℕ) :
+    (canonicalEndpointCapacitySlots n k).card =
+      extraPaymentCapacityAt n (paymentEndpointSeq n k) := by
+  simp [canonicalEndpointCapacitySlots]
+
+/-- Total delayed and immediate claims through canonical endpoint `m`. -/
+noncomputable def cumulativeCanonicalEndpointClaims
+    (n : OddNat) (m : ℕ) : ℕ :=
+  ∑ k ∈ Finset.range (m + 1),
+    ((floatGrowthDebtFiberAt n (paymentEndpointSeq n k)).card +
+      (endpointImmediateCarryTwoClaimFiberAt n (paymentEndpointSeq n k)).card)
+
+/-- Total endpoint capacity through canonical endpoint `m`. -/
+noncomputable def cumulativeCanonicalEndpointCapacity
+    (n : OddNat) (m : ℕ) : ℕ :=
+  ∑ k ∈ Finset.range (m + 1),
+    (canonicalEndpointCapacitySlots n k).card
+
+/-- Cumulative accounting term is claims minus capacity. -/
+theorem sum_endpointAccountingTerm_eq_claims_sub_capacity
+    (n : OddNat) (m : ℕ) :
+    (∑ k ∈ Finset.range (m + 1), endpointAccountingTerm n k) =
+      (cumulativeCanonicalEndpointClaims n m : ℤ) -
+        cumulativeCanonicalEndpointCapacity n m := by
+  unfold endpointAccountingTerm cumulativeCanonicalEndpointClaims
+    cumulativeCanonicalEndpointCapacity
+  simp_rw [canonicalEndpointCapacitySlots_card]
+  push_cast
+  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
+
+/-- Prefix Hall condition: every initial endpoint family has enough cumulative capacity. -/
+def CanonicalEndpointPrefixCapacityDominance
+    (n : OddNat) (m : ℕ) : Prop :=
+  ∀ q, q ≤ m →
+    cumulativeCanonicalEndpointClaims n q ≤ cumulativeCanonicalEndpointCapacity n q
+
+/-- The finite Hall frontier is exactly nonpositivity of every accounting prefix. -/
+theorem canonicalEndpointPrefixCapacityDominance_iff_accounting_nonpos
+    (n : OddNat) (m : ℕ) :
+    CanonicalEndpointPrefixCapacityDominance n m ↔
+      ∀ q, q ≤ m →
+        (∑ k ∈ Finset.range (q + 1), endpointAccountingTerm n k) ≤ 0 := by
+  constructor
+  · intro h q hqm
+    rw [sum_endpointAccountingTerm_eq_claims_sub_capacity]
+    exact sub_nonpos.mpr (Int.ofNat_le.mpr (h q hqm))
+  · intro h q hqm
+    have hq := h q hqm
+    rw [sum_endpointAccountingTerm_eq_claims_sub_capacity] at hq
+    exact Int.ofNat_le.mp (sub_nonpos.mp hq)
+
+/-- A claim is identified by its block and source time. -/
+def CanonicalEndpointClaimCarrier
+    (n : OddNat) (m : ℕ) :=
+  {p : Fin (m + 1) × ℕ //
+    p.2 ∈ floatGrowthDebtFiberAt n (paymentEndpointSeq n p.1.val) ∨
+      p.2 ∈ endpointImmediateCarryTwoClaimFiberAt n (paymentEndpointSeq n p.1.val)}
+
+/-- A capacity slot is identified by its endpoint block and local slot. -/
+def CanonicalEndpointCapacityCarrier
+    (n : OddNat) (m : ℕ) :=
+  {p : Fin (m + 1) × ℕ // p.2 ∈ canonicalEndpointCapacitySlots n p.1.val}
+
+/--
+The honest finite matching target. A claim may use a capacity slot at its own
+endpoint or an earlier endpoint in the selected prefix. Existence is deliberately not asserted:
+constructing this ordered injection is the remaining structural sign problem.
+-/
+def CanonicalEndpointOrderedCapacityMatching
+    (n : OddNat) (m : ℕ) : Prop :=
+  ∃ pay : CanonicalEndpointClaimCarrier n m → CanonicalEndpointCapacityCarrier n m,
+    Function.Injective pay ∧ ∀ claim, (pay claim).val.1.val ≤ claim.val.1.val
+
+/-- Prefix capacity dominance conditionally bounds bit width at the selected endpoint. -/
+theorem bitWidth_paymentEndpointSeq_le_initial_of_prefixCapacityDominance
+    {n : OddNat} {m : ℕ}
+    (h : CanonicalEndpointPrefixCapacityDominance n m) :
+    bitWidth (iterateT (paymentEndpointSeq n m + 1) n).1 ≤ bitWidth n.1 := by
+  have hnonpos :=
+    (canonicalEndpointPrefixCapacityDominance_iff_accounting_nonpos n m).mp h m le_rfl
+  rw [sum_endpointAccountingTerm_paymentEndpointSeq] at hnonpos
+  omega
+
+/-- Global version of the still-open cumulative capacity dominance condition. -/
+def CanonicalEndpointCapacityDominance (n : OddNat) : Prop :=
+  ∀ m, CanonicalEndpointPrefixCapacityDominance n m
+
+/-- Global capacity dominance conditionally bounds every canonical endpoint width. -/
+theorem bitWidth_paymentEndpointSeq_le_initial_of_capacityDominance
+    {n : OddNat} (h : CanonicalEndpointCapacityDominance n) (m : ℕ) :
+    bitWidth (iterateT (paymentEndpointSeq n m + 1) n).1 ≤ bitWidth n.1 :=
+  bitWidth_paymentEndpointSeq_le_initial_of_prefixCapacityDominance (h m)
+
+/-!
+## Exact stopping point
+
+All finite reindexing, block-local depth counting, and pressure summation are
+now closed. The next theorem cannot be obtained by another cardinality rewrite:
+one must construct `CanonicalEndpointOrderedCapacityMatching`, or prove the
+equivalent prefix-capacity dominance by a structural rule. The conditional bit
+width bound above is boundedness at canonical endpoints only. It is not a
+convergence theorem; strict decay or a rigidity classification of zero-drift
+families remains separate.
+-/
+
+end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-313.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-313.md
new file mode 100644
index 00000000..51855122
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-313.md
@@ -0,0 +1,179 @@
+# Petal / Collatz implementation report: cp-313
+
+## Status
+
+`UniversalPaymentPressure.lean` now closes the finite pressure-accounting layer
+over the canonical universal payment-block family.  The implementation remains
+`sorry`-free.  The branch stops at a genuine ordered matching problem, rather
+than at another partition or reindexing task.
+
+## Implemented module
+
+New module:
+
+```text
+DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPressure
+```
+
+It is exported by `DkMath.Collatz.PetalBridge.FloatWindow`.
+
+## Lean-certified facts
+
+### 1. Honest local pressure fibers
+
+The recovery and continuation objects are actual filtered `Finset`s inside a
+canonical block.  Their membership theorems expose the existing
+`OrbitDepthRecoversExactlyAt` and `OrbitDepthContinuesBeyond` predicates.
+
+### 2. A canonical block is an exact depth staircase
+
+For every source time `i` in block `k`,
+
+```text
+orbitExactDepth n i = paymentEndpointSeq n k - i + 1.
+```
+
+Consequently, a block of length `L` contains exactly one recovery incidence at
+each depth `1, ..., L`, and no recovery incidence at depth zero:
+
+```text
+card recovery(k,d) = if 1 <= d and d <= L then 1 else 0.
+```
+
+### 3. Continuation has an exact closed count
+
+The continuation fiber at depth `d` has cardinality
+
+```text
+card continuation(k,d) = L - d.
+```
+
+At depth zero this is the whole block.  When `d < L`, the fiber is the initial
+closed interval ending at `endpoint - d`.  The interval theorem intentionally
+requires `d < L`: without that hypothesis, natural-number truncated subtraction
+can manufacture a false endpoint at zero even though the real fiber is empty.
+
+### 4. Local signed pressure is fully classified
+
+The actual local contribution is
+
+```text
+continuation card - recovery card
+  = (L - d) - if 1 <= d and d <= L then 1 else 0.
+```
+
+For positive `d`:
+
+```text
+L < d      ->  0
+L = d      -> -1
+L = d + 1  ->  0
+d + 2 <= L ->  L - d - 1
+```
+
+Thus local pressure is not uniformly nonpositive.  Long blocks can contribute
+positive pressure at shallow depths.  A global sign theorem cannot be obtained
+by proving every local block nonpositive.
+
+### 5. Existing pressure counts are exactly the block sums
+
+The existing `List.range` counts were converted to actual filtered initial
+`Finset`s.  The canonical prefix is exactly
+
+```text
+Finset.range (paymentEndpointSeq n m + 1),
+```
+
+and filtering commutes with its disjoint block decomposition at card level.
+Therefore both recovery and continuation counts split over the first `m + 1`
+canonical blocks.  In particular:
+
+```text
+SourcePressureMarginInt n (paymentEndpointSeq n m + 1) d
+  = sum k in range (m + 1), blockPressureContributionInt n k d.
+```
+
+This is the direct bridge from the new staircase calculation to the established
+pressure API.
+
+### 6. Delayed debts have injective depth addresses
+
+Every delayed debt source in block `k` is marked by
+
+```text
+canonicalPaymentDebtDepth n k i = endpoint(k) - i + 1.
+```
+
+This address equals `orbitExactDepth n i`.  Distinct delayed debt sources in
+one block have distinct depth addresses, so the marked-depth image has exactly
+the delayed-debt cardinality.
+
+### 7. Capacity is represented by actual slots
+
+The endpoint capacity carrier is
+
+```text
+Finset.range (extraPaymentCapacityAt n (paymentEndpointSeq n k)),
+```
+
+whose card is definitionally the endpoint capacity.  Immediate endpoint claims
+remain separate from delayed debt claims.
+
+### 8. The exact sign frontier is now named
+
+`CanonicalEndpointPrefixCapacityDominance n m` states that every prefix through
+`m` has at least as much cumulative endpoint capacity as cumulative delayed and
+immediate claims.  Lean proves this equivalent to nonpositivity of every prefix
+sum of `endpointAccountingTerm`.
+
+An honest carrier-level target,
+`CanonicalEndpointOrderedCapacityMatching`, asks for an injective payment map
+from claims to capacity slots, with every slot occurring no later than its
+claim endpoint.  Its existence is not asserted.
+
+## Conditional consequence
+
+If prefix capacity dominance is supplied, Lean proves
+
+```text
+bitWidth (iterateT (paymentEndpointSeq n m + 1) n).1 <= bitWidth n.1.
+```
+
+The global dominance predicate gives this bound for every canonical endpoint.
+This is a conditional endpoint-boundedness theorem only.  It is not a proof of
+convergence, nor by itself a proof of eventual periodicity.
+
+## Genuine obstruction
+
+All finite partitioning, staircase counting, list-to-Finset conversion, and
+pressure summation requested in cp-313 are complete.  The remaining theorem is
+structural:
+
+```text
+cumulative delayed claims + cumulative immediate claims
+  <= cumulative endpoint capacity.
+```
+
+Equivalently, one must construct the ordered capacity matching, or derive its
+prefix inequalities from a new orbit rule.  Cardinality algebra alone cannot
+choose the payment destination of a claim across endpoint blocks.
+
+## Next implementation direction
+
+1. Inspect how `extraPaymentCapacityAt` changes between consecutive canonical
+   endpoints and whether a delayed debt depth determines a canonical capacity
+   slot.
+2. Attempt a monotone greedy matching on the explicit claim and capacity
+   carriers.
+3. If greedy matching fails, formalize the first minimal prefix where claims
+   exceed capacity and extract the resulting rigidity/overload witness.
+4. Only after global dominance is established, build the finite-state argument
+   needed for endpoint-state recurrence.  Do not infer eventual periodicity
+   from bounded bit width without a deterministic endpoint transition theorem.
+5. Keep strict decay, zero-drift-family classification, and cycle exclusion as
+   separate downstream branches.
+
+## Verification
+
+The final build gate for this checkpoint is recorded in the completion message.
+
````
`````
