# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentDepthLedger

gch: 3604034a1fc4a85336efb569cd1cf2e200ae7e50

## Report

cp-315 を完了しました。

Lean 側では以下を証明・実装しています。

- 正の excursion と block drift の同値
- window repayment と `claims ≤ capacity` の同値
- forward window matching から repayment
- depth/level ごとの scalar ledger
- source claim ↔ depth claim の `Equiv`
- zero-based capacity ↔ level capacity の `Equiv`
- 7 の最初の二ブロックと明示的 allocation

重要な監査結果として、候補則

```text
depth 1, 2 -> level 2
depth d >= 3 -> level d
```

は一般には成立しません。

- `27`: depth 5 が残存
- `31`: depth 5 が残存
- `511`: depth 8, 9 が残存
- いずれも状態 `1` 到達後は level 2 しか現れないため、exact-level 固定では支払い不能

したがって、偽となる `CanonicalRepaymentEligible` は定義せず、反証された規則を観測する queue API として隔離しました。次の eligibility は、正当化された cross-level payment または別の capacity 座標を必要とします。

実装は [UniversalPaymentDepthLedger.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentDepthLedger.lean)、詳細結果は [report-petal-315.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-315.md) にあります。

検証済みです。

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentDepthLedger
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
lake build DkMath
git diff --check
```

新規 Lean module は no-sorry です。

## Review

## 結論

**採用。しかも、これは「失敗を見つけた checkpoint」ではなく、勝ち筋を誤った座標から救い出した checkpoint じゃ。**

cp-315 は、候補だった

```text
depth 1, 2 → level 2
depth d ≥ 3 → level d
```

を、$27,31,511$ の具体軌道で退けた。

ここで倒れたのは repayment 構想ではない。

倒れたのは、

> **claim の recovery depth と、endpoint capacity の height level は、同じ自然数なら同じ支払単位である**

という仮定じゃ。

そして、cp-315 自身が既にその理由を半分証明しておる。

- claim depth は source time から一意に定まる内在的な住所
- capacity level は匿名 slot を $s\mapsto s+2$ で番号づけた座標
- exact ledger が使用するのは両者の **cardinality だけ**
- drift 式には depth-dependent cost が一切現れない

したがって次の一手は、別の cross-level 規則を思いつきで足すことではない。

> **depth は claim の住所として残し、支払いは fungible な一単位 claim / 一単位 capacity の scalar queue として扱う。**

これが今回の詰将棋における本命手じゃ。

---

## 1. cp-315 が完全に閉じた部分

今回、次の有限会計層は完全に閉じた。

### Excursion の正確な意味

```lean
canonicalEndpointPositiveExcursionAt_iff_accountingTerm_pos
```

により、

$$
\operatorname{PositiveExcursionAt}(q)\Longleftrightarrow0<D_q
$$

となった。

これは以前指摘した通り、「balance が正である」という意味ではなく、

> block $q$ が直前の baseline から正方向へ動く

という意味じゃ。

定義と名称の意味境界が Lean 上で固定された。

### Window repayment

$q\le r$ に対して、

$$
\operatorname{RepaidAt}(q,r)
\Longleftrightarrow
\sum_{k=q}^{r}D_k\le0
$$

さらに、

$$
\operatorname{RepaidAt}(q,r)
\Longleftrightarrow
\sum_{k=q}^{r}A_k\le
\sum_{k=q}^{r}P_k
$$

となった。

ここで、

$$
A_k=R_k+\varepsilon_k
$$

は block claim 数、

$$
P_k=h_{e_k}-1
$$

は block capacity じゃ。

これで aggregate repayment の定義は完全に閉じた。

### 実 carrier

```lean
CanonicalEndpointClaimWindowCarrier
CanonicalEndpointCapacityWindowCarrier
```

が入り、その `Nat.card` が window claim / capacity と正確に一致した。

もはや単なる和の式ではなく、実際の有限集合がある。

### Forward window matching

```lean
CanonicalEndpointForwardWindowMatching
```

は、

$$
\operatorname{claimBlock}\le\operatorname{slotBlock}
$$

を要求する。

そして、

$$
\operatorname{ForwardWindowMatching}(q,r)
\Longrightarrow
\operatorname{RepaidAt}(q,r)
$$

が証明された。

これは正しい。

ただし、後で述べる通り逆は一般には出ない。

---

## 2. depth ledger の到達点

今回の、

```lean
canonicalDepthAccountingTerm
```

は、一 block の accounting term を、

$$
D_k=\sum_d\left(\mathbf1_{d\in C_k} - \mathbf1_{d\in S_k}\right)
$$

へ分解した。

ここで、

$$
C_k=\operatorname{canonicalPaymentClaimDepths}(n,k)
$$

$$
S_k=\operatorname{canonicalEndpointCapacityLevelSlots}(n,k)
$$

じゃ。

これは正確な signed histogram である。

特に、

```lean
CanonicalEndpointClaimCarrier
  ≃ CanonicalEndpointDepthClaimCarrier
```

により、source-time claim と recovery-depth claim は完全に同じデータになった。

claim depth は単なる注釈ではない。

$$
d=e_k-i+1
$$

として source $i$ を一意に復元できる、本物の座標じゃ。

一方 capacity 側も、

```lean
CanonicalEndpointCapacityCarrier
  ≃ CanonicalEndpointLevelCapacityCarrier
```

となった。

ただし、この二つの `Equiv` は数学的意味が異なる。

### Claim 側

source time と depth は、軌道幾何から強制される。

### Capacity 側

zero-based slot $s$ を level $s+2$ と呼び替えている。

つまり capacity level は現時点では **ラベル** じゃ。

この非対称性が、次の勝ち筋を決める。

---

## 3. $7$ regression の評価

$7$ の最初の二 block について、

```text
block 0 claims    = {2, 3}
block 0 capacity  = {2}

block 1 claims    = {1}
block 1 capacity  = {2, 3}
```

が Lean で閉じた。

そして allocation、

```text
(0, 2) → (0, 2)
(0, 3) → (1, 3)
(1, 1) → (1, 2)
```

も有限集合として検証された。

これは候補 exact-level 規則が $7$ では美しく動くことを示している。

ただし現在の theorem は、

- 各 entry が有効
- claim 側 image が三件
- capacity 側 image が三件
- allocation 自体が三件

までじゃ。

まだ、

```lean
CanonicalEndpointForwardWindowMatching sevenDepthOdd 0 1
```

そのものとして package されてはいない。

軽微な未包装部分であり、次に一 theorem 足せば閉じる。

---

## 4. audit が本当に反証したもの

audit は、

```text
depth 1, 2 → level 2
depth d ≥ 3 → level d
```

という固定規則を反証した。

$27$ と $31$ では depth $5$ が残り、$511$ では depth $8,9$ が残る。

その後 state $1$ へ到達すると、endpoint height は常に $2$ なので level $2$ しか出ない。

したがって exact-level rule のもとでは、それらは永久に支払えない。

この反証は正しい。

だが、ここで極めて重要な読み替えがある。

> 残った high-level queue は、本当に未払いの bit-width debt なのか。
> それとも、誤った level label に閉じ込められた token なのか。

答えは後者である可能性が非常に高い。

---

## 5. $511$ が示す決定的な事実

$511$ の最初の三 blocks を scalar count だけで見ると、次になる。

```text
block 0:
  claims   = 6
  capacity = 1
  drift    = +5

block 1:
  claims   = 0
  capacity = 1
  drift    = -1

block 2:
  claims   = 1
  capacity = 6
  drift    = -5
```

未払い scalar queue を、

$$
U_{-1}=0
$$

$$
U_k=(U_{k-1}+A_k)\mathbin{\dot-}P_k
$$

とすれば、

$$
0\longrightarrow5\longrightarrow4\longrightarrow0
$$

じゃ。

つまり **block 2 で全 scalar debt は返済済み** である。

しかし exact-level rule では、depth $8,9$ が残る。

これは何を意味するか。

```text
scalar accounting:
  debt は既にゼロ

exact-level queue:
  depth 8, 9 が永久残存
```

したがって depth $8,9$ の残存は、実際の会計不足ではない。

> level $8,9$ 以外での支払いを禁止した座標規則が作った人工的残債

じゃ。

これは次の一手をほぼ決定している。

---

## 6. 賢狼の補助再計算

cp-315 と同じ block 定義を用い、level 条件を外した scalar FIFO queue を再計算した。

これはまだ Lean theorem ではない。

|  root | exact-level 残存  | scalar queue 最大 | scalar queue が初めて再び $0$ になる block | state $1$ の block |
| ----: | ----------------: | ----------------: | -----------------------------------------: | -----------------: |
|   $7$ |               $0$ |               $1$ |                                        $1$ |                $3$ |
|  $27$ |  depth $5$ が一件 |               $5$ |                                       $14$ |               $17$ |
|  $31$ |  depth $5$ が一件 |               $5$ |                                       $13$ |               $16$ |
| $511$ |       depth $8,9$ |               $5$ |                                        $2$ |               $10$ |

三つの反例全てで、

> exact-level queue は残るが、scalar queue は state $1$ より前に完全に空になる

という結果になった。

これは非常に強い観測じゃ。

exact-level rule が repayment の本質を捕らえていないことを、ほぼ明示している。

---

## 7. claim depth は「価格」ではなく「住所」

現在の exact block ledger は、

$$
D_k=A_k-P_k
$$

である。

一つの claim が depth $2$ でも depth $9$ でも、accounting への寄与は常に、

$$
+1
$$

じゃ。

一つの capacity slot が level $2$ でも level $9$ でも、寄与は常に、

$$
-1
$$

である。

式の中には、

$$
d
$$

も、

$$
s
$$

も重みとして現れない。

したがって現在 Lean が証明している世界では、

```text
claim depth:
  claim がどこから来たかを示す住所

capacity level:
  endpoint capacity h - 1 個を番号づけたラベル

claim cost:
  常に 1

capacity value:
  常に 1
```

じゃ。

よって、現段階で mathematically justified な repayment は、

> 一単位 claim を、同時刻または後続時刻の一単位 capacity へ割り当てる

だけである。

depth equality は必要ない。

---

## 8. scalar queue が本当の次の状態量

block claim 数を $A_k$、capacity を $P_k$ と置く。

次の reflected queue を定義する。

$$
U_{-1}=0
$$

$$
U_k=\max(0,U_{k-1}+A_k-P_k)
$$

Nat なら、

$$
U_k=(U_{k-1}+A_k)\mathbin{\dot-}P_k
$$

じゃ。

これは、

- unused capacity を未来へ bank しない
- 未払い claim だけを未来へ送る
- 同一 depth を要求しない
- 時間順序だけを守る

という、最小の causal repayment queue になる。

この queue には標準的な閉形式がある。

$$
U_m=\max\left(0,\;\max_{0\le q\le m}\sum_{k=q}^{m}D_k\right)
$$

つまり、

> 現在時刻 $m$ で残っている debt は、過去のどの block から開始した excursion が最も返済不足か

である。

balance を、

$$
B_m=\sum_{k=0}^{m}D_k
$$

とすれば、

$$
U_m=B_m-\min(0,B_0,\ldots,B_m)
$$

でもある。

これは重要じゃ。

`canonicalEndpointBalanceInt` が net wealth なら、$U_m$ は historical minimum から見た outstanding overdraft になる。

---

## 9. scalar queue と Big の接続

上式から、

$$
B_m\le U_m
$$

が直ちに従う。

したがって、

$$
\forall m,\quad U_m\le C
$$

を得れば、

$$
\forall m,\quad B_m\le C
$$

となる。

既存 theorem と合わせれば、

$$
w_{e_m+1}\le w_0+C
$$

じゃ。

つまり、

> **scalar outstanding queue の一様上界は、そのまま canonical endpoint bit-width Big になる。**

これは exact-level eligibility より、はるかに直接的じゃ。

さらに、

$$
U_m=0
$$

なら、

$$
\forall q\le m,\quad\sum_{k=q}^{m}D_k\le0
$$

となる。

したがって時刻 $m$ では、全ての過去 block を始点とする excursion が aggregate 上返済済みになる。

---

## 10. Forward matching と repayment の厳密な違い

cp-315 の、

```lean
ForwardWindowMatching → ExcursionRepaidAt
```

は正しい。

しかし逆は一般には成立しない。

例えば、

```text
block q:
  capacity 10
  claim 0

block r:
  capacity 0
  claim 10
```

なら window total は釣り合う。

$$
\sum A=\sum P
$$

しかし未来 claim は過去 capacity を使えないので、forward matching は存在しない。

したがって forward matching が存在するための条件は、window 全体の一式だけでは足りない。

必要なのは全 suffix に対する条件じゃ。

$$
\forall t\in[q,r],\quad
\sum_{k=t}^{r}A_k
\le
\sum_{k=t}^{r}P_k
$$

これは nested-neighborhood 型 Hall 条件になる。

そして scalar queue が $r$ で $0$ になることと一致する。

つまり次に閉じるべき三角形は、

$$
\text{scalar queue at }r=0
$$

$$
\Longleftrightarrow
\text{all suffix inequalities}
$$

$$
\Longleftrightarrow
\text{anonymous forward window matching exists}
$$

じゃ。

ここでは depth eligibility は不要である。

---

## 11. depth ledger は捨てない

exact-level matching が偽でも、depth ledger は無駄ではない。

claim depth は、

- block length
- pressure recovery
- continuation
- carry-two incidence
- claim arrival pattern

を接続する。

したがって depth 側の役目は、

> queue に何件の claim が、どの形で流入するかを説明する

ことじゃ。

capacity level と直接結婚させる必要はない。

```text
depth / pressure:
  arrival process の内部構造

scalar capacity:
  service process

reflected queue:
  両者の時間方向の合流
```

この三層に分けるのが正しい。

---

## 12. cp-315 の細かなレビュー

### `canonicalDepthAccountingTerm`

正しい signed histogram じゃ。

ただし現在の family theorem は、

$$
\sum_k\sum_d
$$

という block-local 二重和までであり、共通 depth support 上で、

$$
\sum_d\sum_k
$$

へ交換した theorem ではない。

report の「level by level」という表現は、局所 histogram としては正しいが、大域 depth flow まではまだ出ていない。

exact-level route が偽と分かった現在、無理に大域 depth sum を主幹線にする必要もない。

### `ForwardWindowMatching.to_excursionRepaidAt`

証明では temporal inequality を使用していない。

cardinality injection だけで total claims $\le$ capacity が出るからじゃ。

これは theorem の誤りではない。

むしろ temporal inequality の本当の意味は、今後の逆向き、

```text
suffix Hall conditions
  → forward matching
```

で初めて現れる。

### Candidate level queue

反証済みモデルを観測 API として隔離した判断は正しい。

ただし以後、これを大域主幹線へ戻してはならない。

---

## 判定

### Exact finite window accounting

**完成。**

### Source claim と depth claim の同一視

**完成。**

### Capacity slot と level slot の座標変換

**完成。**

### Exact-level eligibility

**反証。廃棄。**

### Cross-level eligibility の新規発明

**現時点では不要。**

### 次の本丸

**fungible scalar capacity による reflected outstanding queue**

### 勝敗を分ける theorem

$$
U_m=
\max_{0\le q\le m}\left(\sum_{k=q}^{m}D_k\right)_+
$$

および、

$$
U_m=0\Longleftrightarrow\text{forward temporal matching exists through }m.
$$

---

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge Float-window branch after
report-petal-315.

The cp-315 implementation is accepted.

The exact-level candidate is refuted, but the repayment branch is not refuted.
The audit shows that recovery depth and endpoint capacity level must not be
treated as equal-denomination payment coordinates.

Freeze the following semantic distinction:

    recovery depth:
      an intrinsic source address inside a canonical block

    endpoint capacity level:
      a chosen coordinate on `height - 1` anonymous unit-capacity slots

The exact endpoint ledger assigns unit weight to every claim and every capacity
slot. No theorem currently gives a depth-dependent claim cost or a
level-dependent capacity value.

Do not invent another cross-level eligibility relation in the next checkpoint.

The next mainline is the anonymous scalar repayment queue.

# Stage A — close the seven matching package

Package the existing explicit allocation as an actual theorem:

    CanonicalEndpointForwardWindowMatching sevenDepthOdd 0 1

or provide an equivalent finite carrier injection theorem.

Keep this as a regression example only.

# Stage B — scalar arrivals, service, and drift

Define proof-independent block quantities:

    canonicalBlockClaimCount n k
    canonicalBlockCapacityCount n k

using the existing exact claim and capacity fibers.

Prove:

    endpointAccountingTerm n k
      =
    (canonicalBlockClaimCount n k : Int)
      - canonicalBlockCapacityCount n k

Do not retain depth or level in these scalar definitions.

# Stage C — reflected outstanding queue

Define the causal outstanding-claim queue:

    canonicalOutstandingClaimQueue n 0
      =
    canonicalBlockClaimCount n 0
        - canonicalBlockCapacityCount n 0

    canonicalOutstandingClaimQueue n (k + 1)
      =
    canonicalOutstandingClaimQueue n k
        + canonicalBlockClaimCount n (k + 1)
        - canonicalBlockCapacityCount n (k + 1)

Use Nat subtraction with explicit parentheses:

    (oldQueue + newClaims) - newCapacity

Unused capacity is not banked. Claims are unit tokens and capacity slots are
fungible unit service.

Expose the successor equation and basic monotonic comparison lemmas.

# Stage D — reflection identity

Define the signed window drift:

    canonicalWindowDriftInt n q m
      :=
    sum k in Icc q m, endpointAccountingTerm n k

For every `m`, prove the exact reflected-walk formula:

    canonicalOutstandingClaimQueue n m
      =
    max over q <= m of
      Int.toNat (canonicalWindowDriftInt n q m)

Include the zero candidate explicitly.

Also prove the equivalent running-min formula:

    queue m
      =
    balance m - minimum of
        0, balance 0, ..., balance m

with a suitable Nat/Int formulation.

Do not leave this as a numerical observation.

# Stage E — repayment characterization

Prove:

    canonicalOutstandingClaimQueue n m = 0
      <->
    forall q <= m,
      canonicalWindowDriftInt n q m <= 0

Rewrite this as:

    forall q <= m,
      CanonicalEndpointExcursionRepaidAt n q m

using the existing exact excursion theorem.

Thus queue zero means every currently open aggregate excursion has been
repaid by endpoint `m`.

# Stage F — temporal Hall theorem

For `q <= r`, prove that the existing anonymous forward-window matching is
equivalent to the nested suffix inequalities:

    CanonicalEndpointForwardWindowMatching n q r
      <->
    forall t in Icc q r,
      canonicalEndpointWindowClaims n t r
        <=
      canonicalEndpointWindowCapacity n t r

This is the finite interval-order/Hall theorem for unit claims released at
their block and capacity slots available at their block.

A greedy proof from the last block backwards is acceptable.

Do not use claim depth or capacity level in this matching theorem.

# Stage G — queue/matching bridge

Define the queue local to a window `q..r`, initialized at zero at block `q`.

Prove:

    localQueue q r = 0
      <->
    CanonicalEndpointForwardWindowMatching n q r

or prove both directions through the suffix Hall characterization.

Distinguish clearly:

    aggregate repayment:
      only the total q..r inequality

    causal repayment:
      all suffix inequalities / forward matching / queue zero

# Stage H — boundedness consequence

Prove:

    canonicalEndpointBalanceInt n m
      <=
    canonicalOutstandingClaimQueue n m

as an integer inequality.

Then prove:

    uniform scalar queue bound
      ->
    CanonicalEndpointBalanceUniformUpperBound

and reuse the existing theorem to obtain:

    canonical endpoint bit-width bound.

This is the first direct queue-to-Big theorem.

# Stage I — exact scalar regressions

Formalize small scalar queue regressions.

At minimum prove:

    root 7:
      queue 0 = 1
      queue 1 = 0

    root 511:
      queue 0 = 5
      queue 1 = 4
      queue 2 = 0

The 511 regression is critical: it demonstrates in Lean that scalar debt is
fully repaid even though the rejected exact-level candidate leaves depths
eight and nine outstanding.

Add 27 and 31 if their concrete evaluation remains manageable.

# Stage J — finite scalar audit

Extend the Python audit with the scalar queue, separate from the rejected
level queues.

Record for each root:

    maximum scalar queue
    first block returning to zero
    longest positive queue excursion
    queue value on entry to state one

Audit a broad finite root range, not only 7, 27, 31, and 511.

This remains evidence, not a theorem.

# Stage K — next structural frontier

After the reflected queue and Hall theorem are complete, inspect the scalar
queue transitions against:

    canonical block length
    claim-depth histogram
    endpoint height
    block pressure contribution
    existing PatternLedger / DriftNode data

The next genuine mathematical target is one of:

    a uniform scalar queue bound
    a uniform repayment lag
    absence of a pumpable positive-queue cycle
    a finite-state obstruction forcing queue discharge

Do not return to exact numeric depth-level matching unless a new orbit theorem
first proves that those coordinates carry payment semantics.

Continue autonomously through the exact queue identities and temporal matching
theorems.

Stop at the first genuine obstruction to bounding the scalar queue.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-316.md
```

これが次の一手じゃ。

**depth を支払額と読むのをやめ、claim 一件を一件として数える。**

cp-315 は敗北報告ではない。
余計な駒を一枚盤上から外し、王手筋を一本に絞った checkpoint じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
index 6afc8e0a..9d2f638a 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
@@ -17,6 +17,7 @@ import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentFamily
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPressure
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentRepayment
+import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentDepthLedger
 
 #print "file: DkMath.Collatz.PetalBridge.FloatWindow"
 
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentDepthLedger.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentDepthLedger.lean
new file mode 100644
index 00000000..313d15bd
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentDepthLedger.lean
@@ -0,0 +1,639 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentRepayment
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentDepthLedger"
+
+namespace DkMath.Collatz
+
+/-!
+# Window repayment and depth ledgers
+
+This module distinguishes two finite statements:
+
+* a fixed old claim prefix embeds into a larger future slot prefix;
+* all claims born in a window `q..r` are paid by slots born in that same window.
+
+Only the second statement certifies repayment of that window's balance drift.
+No general depth eligibility relation is assumed here.
+-/
+
+/-! ## Exact excursion identities -/
+
+/-- Balance immediately before block `q` is its block-start width drift. -/
+theorem canonicalEndpointBalanceBefore_eq_bitWidth_sub
+    (n : OddNat) (q : ℕ) :
+    canonicalEndpointBalanceBefore n q =
+      (bitWidth (iterateT (canonicalEndpointBlockStart n q) n).1 : ℤ) - bitWidth n.1 := by
+  cases q with
+  | zero => simp [canonicalEndpointBalanceBefore, canonicalEndpointBlockStart, iterateT]
+  | succ q =>
+      rw [canonicalEndpointBalanceBefore, canonicalEndpointBalanceInt_eq_bitWidth_sub]
+      rfl
+
+/-- A positive excursion at `q` is exactly a positive drift of block `q`. -/
+theorem canonicalEndpointPositiveExcursionAt_iff_accountingTerm_pos
+    (n : OddNat) (q : ℕ) :
+    CanonicalEndpointPositiveExcursionAt n q ↔ 0 < endpointAccountingTerm n q := by
+  unfold CanonicalEndpointPositiveExcursionAt
+  cases q with
+  | zero =>
+      simp [canonicalEndpointBalanceBefore, canonicalEndpointBalanceInt]
+  | succ q =>
+      simp only [canonicalEndpointBalanceBefore, canonicalEndpointBalanceInt]
+      rw [show ∑ k ∈ Finset.range (q + 1 + 1), endpointAccountingTerm n k =
+          (∑ k ∈ Finset.range (q + 1), endpointAccountingTerm n k) +
+            endpointAccountingTerm n (q + 1) by
+        simp [Finset.sum_range_succ]]
+      omega
+
+/-- A window drift is the difference between its terminal and prior balances. -/
+theorem sum_endpointAccountingTerm_Icc_eq_balance_sub_before
+    (n : OddNat) {q r : ℕ} (hqr : q ≤ r) :
+    (∑ k ∈ Finset.Icc q r, endpointAccountingTerm n k) =
+      canonicalEndpointBalanceInt n r - canonicalEndpointBalanceBefore n q := by
+  rw [sum_endpointAccountingTerm_Icc_eq_bitWidth_sub n hqr,
+    canonicalEndpointBalanceInt_eq_bitWidth_sub,
+    canonicalEndpointBalanceBefore_eq_bitWidth_sub]
+  omega
+
+/-- Repayment at `r` is exactly nonpositive signed drift over `q..r`. -/
+theorem canonicalEndpointExcursionRepaidAt_iff_window_sum_nonpos
+    (n : OddNat) {q r : ℕ} (hqr : q ≤ r) :
+    CanonicalEndpointExcursionRepaidAt n q r ↔
+      (∑ k ∈ Finset.Icc q r, endpointAccountingTerm n k) ≤ 0 := by
+  rw [sum_endpointAccountingTerm_Icc_eq_balance_sub_before n hqr]
+  unfold CanonicalEndpointExcursionRepaidAt
+  constructor
+  · exact fun h => sub_nonpos.mpr h.2
+  · exact fun h => ⟨hqr, sub_nonpos.mp h⟩
+
+/-- Claims born in the selected canonical block window. -/
+noncomputable def canonicalEndpointWindowClaims
+    (n : OddNat) (q r : ℕ) : ℕ :=
+  ∑ k ∈ Finset.Icc q r,
+    ((floatGrowthDebtFiberAt n (paymentEndpointSeq n k)).card +
+      (endpointImmediateCarryTwoClaimFiberAt n (paymentEndpointSeq n k)).card)
+
+/-- Capacity born in the selected canonical block window. -/
+noncomputable def canonicalEndpointWindowCapacity
+    (n : OddNat) (q r : ℕ) : ℕ :=
+  ∑ k ∈ Finset.Icc q r, extraPaymentCapacityAt n (paymentEndpointSeq n k)
+
+/-- Exact claims-versus-capacity criterion for repayment of a block window. -/
+theorem canonicalEndpointExcursionRepaidAt_iff_windowClaims_le_capacity
+    (n : OddNat) {q r : ℕ} (hqr : q ≤ r) :
+    CanonicalEndpointExcursionRepaidAt n q r ↔
+      canonicalEndpointWindowClaims n q r ≤ canonicalEndpointWindowCapacity n q r := by
+  rw [canonicalEndpointExcursionRepaidAt_iff_window_sum_nonpos n hqr]
+  rw [sum_endpointAccountingTerm_Icc_eq_claims_sub_capacity n hqr]
+  unfold canonicalEndpointWindowClaims canonicalEndpointWindowCapacity
+  rw [sub_nonpos]
+  constructor <;> intro h <;> exact_mod_cast h
+
+/-! ## Actual finite window carriers -/
+
+/-- Claims identified by a block in `q..r` and a source in its complete claim fiber. -/
+def CanonicalEndpointClaimWindowCarrier
+    (n : OddNat) (q r : ℕ) :=
+  Σ k : {k : ℕ // k ∈ Finset.Icc q r},
+    {i : ℕ // i ∈ carryTwoPaymentClaimFiberAt n (paymentEndpointSeq n k.val)}
+
+/-- Capacity slots identified by a block in `q..r` and its local zero-based slot. -/
+def CanonicalEndpointCapacityWindowCarrier
+    (n : OddNat) (q r : ℕ) :=
+  Σ k : {k : ℕ // k ∈ Finset.Icc q r},
+    {s : ℕ // s ∈ canonicalEndpointCapacitySlots n k.val}
+
+/-- Exact cardinality of the complete claim window carrier. -/
+theorem natCard_canonicalEndpointClaimWindowCarrier
+    (n : OddNat) (q r : ℕ) :
+    Nat.card (CanonicalEndpointClaimWindowCarrier n q r) =
+      canonicalEndpointWindowClaims n q r := by
+  unfold CanonicalEndpointClaimWindowCarrier
+  rw [Nat.card_sigma]
+  simp_rw [Nat.card_eq_fintype_card, Fintype.card_coe]
+  rw [Finset.univ_eq_attach]
+  calc
+    ∑ x ∈ (Finset.Icc q r).attach,
+        (carryTwoPaymentClaimFiberAt n (paymentEndpointSeq n x.val)).card =
+        ∑ k ∈ Finset.Icc q r,
+          (carryTwoPaymentClaimFiberAt n (paymentEndpointSeq n k)).card :=
+      Finset.sum_attach (Finset.Icc q r) fun k =>
+        (carryTwoPaymentClaimFiberAt n (paymentEndpointSeq n k)).card
+    _ = canonicalEndpointWindowClaims n q r := by
+      unfold canonicalEndpointWindowClaims
+      apply Finset.sum_congr rfl
+      intro k hk
+      exact carryTwoPaymentClaimFiberAt_card_eq_growthDebt_card_add_endpoint_card
+        n (paymentEndpointSeq n k)
+          (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)
+
+/-- Exact cardinality of the capacity window carrier. -/
+theorem natCard_canonicalEndpointCapacityWindowCarrier
+    (n : OddNat) (q r : ℕ) :
+    Nat.card (CanonicalEndpointCapacityWindowCarrier n q r) =
+      canonicalEndpointWindowCapacity n q r := by
+  unfold CanonicalEndpointCapacityWindowCarrier
+  rw [Nat.card_sigma]
+  simp_rw [Nat.card_eq_fintype_card, Fintype.card_coe]
+  rw [Finset.univ_eq_attach]
+  calc
+    ∑ x ∈ (Finset.Icc q r).attach,
+        (canonicalEndpointCapacitySlots n x.val).card =
+        ∑ k ∈ Finset.Icc q r, (canonicalEndpointCapacitySlots n k).card :=
+      Finset.sum_attach (Finset.Icc q r) fun k =>
+        (canonicalEndpointCapacitySlots n k).card
+    _ = canonicalEndpointWindowCapacity n q r := by
+      unfold canonicalEndpointWindowCapacity
+      apply Finset.sum_congr rfl
+      intro k hk
+      exact canonicalEndpointCapacitySlots_card n k
+
+/--
+All claims born in `q..r` are injected into slots born in `q..r`, without
+paying a claim before its own block.
+-/
+def CanonicalEndpointForwardWindowMatching
+    (n : OddNat) (q r : ℕ) : Prop :=
+  q ≤ r ∧
+    ∃ pay : CanonicalEndpointClaimWindowCarrier n q r →
+        CanonicalEndpointCapacityWindowCarrier n q r,
+      Function.Injective pay ∧ ∀ claim, claim.1.val ≤ (pay claim).1.val
+
+/-- A forward window matching certifies repayment of that same window. -/
+theorem CanonicalEndpointForwardWindowMatching.to_excursionRepaidAt
+    {n : OddNat} {q r : ℕ}
+    (h : CanonicalEndpointForwardWindowMatching n q r) :
+    CanonicalEndpointExcursionRepaidAt n q r := by
+  rcases h with ⟨hqr, pay, hpay, _⟩
+  letI : Finite (CanonicalEndpointCapacityWindowCarrier n q r) := by
+    unfold CanonicalEndpointCapacityWindowCarrier
+    infer_instance
+  have hcard := Nat.card_le_card_of_injective pay hpay
+  rw [natCard_canonicalEndpointClaimWindowCarrier,
+    natCard_canonicalEndpointCapacityWindowCarrier] at hcard
+  exact (canonicalEndpointExcursionRepaidAt_iff_windowClaims_le_capacity n hqr).2 hcard
+
+/-! ## Scalar depth ledger -/
+
+/-- Semantic alias: endpoint capacity coordinates are levels, not recovery depths. -/
+noncomputable abbrev canonicalEndpointCapacityLevelSlots :=
+  canonicalEndpointCapacityDepthSlots
+
+/-- Claim incidence minus capacity incidence at one numeric depth/level coordinate. -/
+noncomputable def canonicalDepthAccountingTerm
+    (n : OddNat) (k d : ℕ) : ℤ := by
+  classical
+  exact (if d ∈ canonicalPaymentClaimDepths n k then 1 else 0) -
+    if d ∈ canonicalEndpointCapacityLevelSlots n k then 1 else 0
+
+/-- Finite support containing every claim depth and capacity level of block `k`. -/
+noncomputable def canonicalDepthAccountingSupport
+    (n : OddNat) (k : ℕ) : Finset ℕ :=
+  canonicalPaymentClaimDepths n k ∪ canonicalEndpointCapacityLevelSlots n k
+
+/-- Endpoint drift is exactly the sum of its scalar depth ledger. -/
+theorem endpointAccountingTerm_eq_sum_canonicalDepthAccountingTerm
+    (n : OddNat) (k : ℕ) :
+    endpointAccountingTerm n k =
+      ∑ d ∈ canonicalDepthAccountingSupport n k,
+        canonicalDepthAccountingTerm n k d := by
+  classical
+  unfold canonicalDepthAccountingTerm canonicalDepthAccountingSupport
+  rw [Finset.sum_sub_distrib]
+  simp only [Finset.sum_boole]
+  have hclaimFilter :
+      (canonicalPaymentClaimDepths n k ∪ canonicalEndpointCapacityLevelSlots n k).filter
+        (· ∈ canonicalPaymentClaimDepths n k) = canonicalPaymentClaimDepths n k := by
+    ext d
+    simp only [Finset.mem_filter, Finset.mem_union]
+    tauto
+  have hcapacityFilter :
+      (canonicalPaymentClaimDepths n k ∪ canonicalEndpointCapacityLevelSlots n k).filter
+        (· ∈ canonicalEndpointCapacityLevelSlots n k) =
+          canonicalEndpointCapacityLevelSlots n k := by
+    ext d
+    simp only [Finset.mem_filter, Finset.mem_union]
+    tauto
+  rw [hclaimFilter, hcapacityFilter, canonicalPaymentClaimDepths_card,
+    canonicalEndpointCapacityDepthSlots_card]
+  rfl
+
+/-- Family accounting is the iterated sum of the block-local scalar ledgers. -/
+theorem sum_endpointAccountingTerm_eq_sum_depthLedger
+    (n : OddNat) (m : ℕ) :
+    (∑ k ∈ Finset.range (m + 1), endpointAccountingTerm n k) =
+      ∑ k ∈ Finset.range (m + 1),
+        ∑ d ∈ canonicalDepthAccountingSupport n k,
+          canonicalDepthAccountingTerm n k d := by
+  apply Finset.sum_congr rfl
+  intro k hk
+  exact endpointAccountingTerm_eq_sum_canonicalDepthAccountingTerm n k
+
+/-! ## Proof-independent depth and level carriers -/
+
+/-- Complete claims through `m`, addressed by block and recovery depth. -/
+def CanonicalEndpointDepthClaimCarrier
+    (n : OddNat) (m : ℕ) :=
+  Σ k : Fin (m + 1), {d : ℕ // d ∈ canonicalPaymentClaimDepths n k.val}
+
+/-- Capacity through `m`, addressed by block and positive capacity level. -/
+def CanonicalEndpointLevelCapacityCarrier
+    (n : OddNat) (m : ℕ) :=
+  Σ k : Fin (m + 1),
+    {l : ℕ // l ∈ canonicalEndpointCapacityLevelSlots n k.val}
+
+/-- Depth-addressed claim carrier has exactly the cumulative claim count. -/
+theorem natCard_canonicalEndpointDepthClaimCarrier
+    (n : OddNat) (m : ℕ) :
+    Nat.card (CanonicalEndpointDepthClaimCarrier n m) =
+      cumulativeCanonicalEndpointClaims n m := by
+  unfold CanonicalEndpointDepthClaimCarrier
+  rw [Nat.card_sigma]
+  simp_rw [Nat.card_eq_fintype_card, Fintype.card_coe]
+  rw [Finset.sum_fin_eq_sum_range]
+  unfold cumulativeCanonicalEndpointClaims
+  apply Finset.sum_congr rfl
+  intro k hk
+  rw [dif_pos (Finset.mem_range.mp hk), canonicalPaymentClaimDepths_card]
+
+/-- Level-addressed capacity carrier has exactly the cumulative capacity count. -/
+theorem natCard_canonicalEndpointLevelCapacityCarrier
+    (n : OddNat) (m : ℕ) :
+    Nat.card (CanonicalEndpointLevelCapacityCarrier n m) =
+      cumulativeCanonicalEndpointCapacity n m := by
+  unfold CanonicalEndpointLevelCapacityCarrier
+  rw [Nat.card_sigma]
+  simp_rw [Nat.card_eq_fintype_card, Fintype.card_coe]
+  rw [Finset.sum_fin_eq_sum_range]
+  unfold cumulativeCanonicalEndpointCapacity
+  apply Finset.sum_congr rfl
+  intro k hk
+  rw [dif_pos (Finset.mem_range.mp hk),
+    canonicalEndpointCapacityDepthSlots_card, canonicalEndpointCapacitySlots_card]
+
+/-- Source-time claims mapped to their exact canonical recovery depths. -/
+noncomputable def canonicalEndpointClaimToDepth
+    (n : OddNat) (m : ℕ) :
+    CanonicalEndpointClaimCarrier n m → CanonicalEndpointDepthClaimCarrier n m :=
+  fun claim => ⟨claim.val.1,
+    canonicalPaymentDebtDepth n claim.val.1.val claim.val.2,
+    by
+      rw [canonicalPaymentClaimDepths_eq_image_completeClaimFiber]
+      apply Finset.mem_image.mpr
+      exact ⟨claim.val.2,
+        (mem_carryTwoPaymentClaimFiberAt_iff_growthDebt_or_endpointImmediate
+          (h := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n claim.val.1.val)).2
+          claim.property,
+        rfl⟩⟩
+
+/-- Source-time and recovery-depth claim carriers are equivalent. -/
+noncomputable def canonicalEndpointClaimCarrierEquivDepthClaimCarrier
+    (n : OddNat) (m : ℕ) :
+    CanonicalEndpointClaimCarrier n m ≃ CanonicalEndpointDepthClaimCarrier n m :=
+  Equiv.ofBijective (canonicalEndpointClaimToDepth n m) ⟨by
+    intro a b hab
+    have hblock : a.val.1 = b.val.1 := congrArg Sigma.fst hab
+    have hdepth : canonicalPaymentDebtDepth n a.val.1.val a.val.2 =
+        canonicalPaymentDebtDepth n b.val.1.val b.val.2 := by
+      exact congrArg (fun claim => claim.2.val) hab
+    apply Subtype.ext
+    apply Prod.ext hblock
+    unfold canonicalPaymentDebtDepth at hdepth
+    have haClaim :=
+      (mem_carryTwoPaymentClaimFiberAt_iff_growthDebt_or_endpointImmediate
+        (h := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n a.val.1.val)).2
+        a.property
+    have hbClaim :=
+      (mem_carryTwoPaymentClaimFiberAt_iff_growthDebt_or_endpointImmediate
+        (h := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n b.val.1.val)).2
+        b.property
+    have hale := (Finset.mem_Icc.mp
+      ((mem_carryTwoPaymentClaimFiberAt_iff_mem_universalPaymentBlock_and_carryTwo
+        (h := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n a.val.1.val)).1
+        haClaim).1).2
+    have hble := (Finset.mem_Icc.mp
+      ((mem_carryTwoPaymentClaimFiberAt_iff_mem_universalPaymentBlock_and_carryTwo
+        (h := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n b.val.1.val)).1
+        hbClaim).1).2
+    have hendpoint : paymentEndpointSeq n a.val.1.val =
+        paymentEndpointSeq n b.val.1.val := by rw [hblock]
+    omega,
+  by
+    intro depth
+    have hdepthMem : depth.2.val ∈
+        (carryTwoPaymentClaimFiberAt n (paymentEndpointSeq n depth.1.val)).image
+          (canonicalPaymentDebtDepth n depth.1.val) := by
+      rw [← canonicalPaymentClaimDepths_eq_image_completeClaimFiber]
+      exact depth.2.property
+    rcases Finset.mem_image.mp hdepthMem with ⟨i, hiClaim, hiDepth⟩
+    refine ⟨⟨⟨depth.1, i⟩,
+      (mem_carryTwoPaymentClaimFiberAt_iff_growthDebt_or_endpointImmediate
+        (h := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n depth.1.val)).1
+        hiClaim⟩, ?_⟩
+    exact Sigma.ext rfl (heq_of_eq (Subtype.ext hiDepth))⟩
+
+/-- Zero-based capacity slots mapped to their positive endpoint levels. -/
+noncomputable def canonicalEndpointCapacityToLevel
+    (n : OddNat) (m : ℕ) :
+    CanonicalEndpointCapacityCarrier n m → CanonicalEndpointLevelCapacityCarrier n m :=
+  fun slot => ⟨slot.val.1, slot.val.2 + 2, by
+    rw [canonicalEndpointCapacityLevelSlots, canonicalEndpointCapacityDepthSlots]
+    have hslt : slot.val.2 <
+        extraPaymentCapacityAt n (paymentEndpointSeq n slot.val.1.val) := by
+      simpa [canonicalEndpointCapacitySlots] using slot.property
+    have hheight := two_le_orbitWindowHeight_paymentEndpointSeq n slot.val.1.val
+    unfold extraPaymentCapacityAt at hslt
+    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
+
+/-- The zero-based and level-addressed endpoint-capacity carriers are equivalent. -/
+noncomputable def canonicalEndpointCapacityCarrierEquivLevelCapacityCarrier
+    (n : OddNat) (m : ℕ) :
+    CanonicalEndpointCapacityCarrier n m ≃ CanonicalEndpointLevelCapacityCarrier n m :=
+  Equiv.ofBijective (canonicalEndpointCapacityToLevel n m) ⟨by
+    intro a b hab
+    have hblock : a.val.1 = b.val.1 := congrArg Sigma.fst hab
+    have hslot : a.val.2 + 2 = b.val.2 + 2 :=
+      congrArg (fun slot => slot.2.val) hab
+    apply Subtype.ext
+    exact Prod.ext hblock (by omega),
+  by
+    intro level
+    rcases level with ⟨k, level⟩
+    have hlevel : level.val ∈
+        canonicalEndpointCapacityDepthSlots n k.val := level.property
+    rw [canonicalEndpointCapacityDepthSlots] at hlevel
+    rcases Finset.mem_Icc.mp hlevel with ⟨hlevelTwo, hlevelHeight⟩
+    have hheight := two_le_orbitWindowHeight_paymentEndpointSeq n k.val
+    refine ⟨⟨⟨k, level.val - 2⟩, ?_⟩, ?_⟩
+    · change level.val - 2 ∈ canonicalEndpointCapacitySlots n k.val
+      rw [canonicalEndpointCapacitySlots, Finset.mem_range]
+      unfold extraPaymentCapacityAt
+      omega
+    · unfold canonicalEndpointCapacityToLevel
+      apply Sigma.ext_iff.mpr
+      constructor
+      · rfl
+      · apply heq_of_eq
+        apply Subtype.ext
+        change level.val - 2 + 2 = level.val
+        omega⟩
+
+/-! ## Exact depth regression for the orbit from seven -/
+
+section SevenDepthRegression
+
+private def sevenDepthOdd : OddNat := mkOddNat 7 (by decide)
+
+private lemma sevenDepth_v2_22 : v2 22 = 1 := by
+  have h := (DkMath.ABC.padic_val_two_of_even 11).2 (by decide)
+  simpa [v2, v2_odd 11 (by decide)] using h
+
+private lemma sevenDepth_v2_34 : v2 34 = 1 := by
+  have h := (DkMath.ABC.padic_val_two_of_even 17).2 (by decide)
+  simpa [v2, v2_odd 17 (by decide)] using h
+
+private lemma sevenDepth_v2_52 : v2 52 = 2 := by
+  have h26 := (DkMath.ABC.padic_val_two_of_even 13).2 (by decide)
+  have h52 := (DkMath.ABC.padic_val_two_of_even 26).2 (by decide)
+  have hv13 : v2 13 = 0 := v2_odd 13 (by decide)
+  have hv26 : v2 26 = 1 := by simpa [v2, hv13] using h26
+  simpa [v2, hv26] using h52
+
+private lemma sevenDepth_v2_40 : v2 40 = 3 := by
+  have h10 := (DkMath.ABC.padic_val_two_of_even 5).2 (by decide)
+  have h20 := (DkMath.ABC.padic_val_two_of_even 10).2 (by decide)
+  have h40 := (DkMath.ABC.padic_val_two_of_even 20).2 (by decide)
+  have hv5 : v2 5 = 0 := v2_odd 5 (by decide)
+  have hv10 : v2 10 = 1 := by simpa [v2, hv5] using h10
+  have hv20 : v2 20 = 2 := by simpa [v2, hv10] using h20
+  simpa [v2, hv20] using h40
+
+private lemma sevenDepth_v2_8 : v2 8 = 3 := by
+  have h4 := (DkMath.ABC.padic_val_two_of_even 2).2 (by decide)
+  have h8 := (DkMath.ABC.padic_val_two_of_even 4).2 (by decide)
+  have hv2 : v2 2 = 1 := by
+    have h := (DkMath.ABC.padic_val_two_of_even 1).2 (by decide)
+    simp [v2]
+  have hv4 : v2 4 = 2 := by simpa [v2, hv2] using h4
+  simpa [v2, hv4] using h8
+
+private lemma sevenDepth_v2_14 : v2 14 = 1 := by
+  have h := (DkMath.ABC.padic_val_two_of_even 7).2 (by decide)
+  simpa [v2, v2_odd 7 (by decide)] using h
+
+private theorem sevenDepth_endpoint_zero : paymentEndpointSeq sevenDepthOdd 0 = 2 := by
+  norm_num [paymentEndpointSeq, orbitPaymentTarget, orbitExactDepth,
+    ResidualAllOnesDepth, oddOrbitLabel, iterateT, sevenDepthOdd, mkOddNat,
+    sevenDepth_v2_8]
+
+private theorem sevenDepth_endpoint_one : paymentEndpointSeq sevenDepthOdd 1 = 3 := by
+  rw [show paymentEndpointSeq sevenDepthOdd 1 =
+    orbitPaymentTarget sevenDepthOdd (paymentEndpointSeq sevenDepthOdd 0 + 1) by rfl]
+  rw [sevenDepth_endpoint_zero]
+  norm_num [orbitPaymentTarget, orbitExactDepth, ResidualAllOnesDepth, oddOrbitLabel,
+    iterateT, T, sevenDepthOdd, mkOddNat, threeNPlusOne, pow2,
+    sevenDepth_v2_22, sevenDepth_v2_34, sevenDepth_v2_52, sevenDepth_v2_14]
+
+private theorem sevenDepth_blockLength_zero :
+    canonicalPaymentBlockLength sevenDepthOdd 0 = 3 := by
+  rw [canonicalPaymentBlockLength_eq_endpoint_sub_start_add_one,
+    universalPaymentBlockStart_paymentEndpointSeq_zero, sevenDepth_endpoint_zero]
+
+private theorem sevenDepth_blockLength_one :
+    canonicalPaymentBlockLength sevenDepthOdd 1 = 1 := by
+  rw [canonicalPaymentBlockLength_eq_endpoint_sub_start_add_one,
+    universalPaymentBlockStart_paymentEndpointSeq_succ,
+    sevenDepth_endpoint_zero, sevenDepth_endpoint_one]
+
+private theorem sevenDepth_carry_zero : CarryTwoDebtAt sevenDepthOdd 0 := by
+  norm_num [CarryTwoDebtAt, stateUpperCarry, upperCarry3n1, bitWidth,
+    iterateT, sevenDepthOdd, mkOddNat]
+
+private theorem sevenDepth_carry_one : CarryTwoDebtAt sevenDepthOdd 1 := by
+  norm_num [CarryTwoDebtAt, stateUpperCarry, upperCarry3n1, bitWidth,
+    iterateT, T, sevenDepthOdd, mkOddNat, threeNPlusOne, pow2,
+    sevenDepth_v2_22]
+
+private theorem sevenDepth_not_carry_two : ¬ CarryTwoDebtAt sevenDepthOdd 2 := by
+  norm_num [CarryTwoDebtAt, stateUpperCarry, upperCarry3n1, bitWidth,
+    iterateT, T, sevenDepthOdd, mkOddNat, threeNPlusOne, pow2,
+    sevenDepth_v2_22, sevenDepth_v2_34]
+
+private theorem sevenDepth_carry_three : CarryTwoDebtAt sevenDepthOdd 3 := by
+  norm_num [CarryTwoDebtAt, stateUpperCarry, upperCarry3n1, bitWidth,
+    iterateT, T, sevenDepthOdd, mkOddNat, threeNPlusOne, pow2,
+    sevenDepth_v2_22, sevenDepth_v2_34, sevenDepth_v2_52]
+
+/-- The first seven-regression block has delayed claim depths two and three. -/
+theorem canonicalPaymentClaimDepths_seven_zero :
+    canonicalPaymentClaimDepths sevenDepthOdd 0 = {2, 3} := by
+  classical
+  ext d
+  rw [mem_canonicalPaymentClaimDepths_iff]
+  rw [sevenDepth_blockLength_zero]
+  unfold canonicalPaymentSourceAtDepth
+  rw [sevenDepth_endpoint_zero]
+  simp only [Finset.mem_insert, Finset.mem_singleton]
+  constructor
+  · rintro ⟨hd1, hd3, hcarry⟩
+    interval_cases d <;>
+      simp_all [sevenDepth_carry_zero, sevenDepth_carry_one,
+        sevenDepth_not_carry_two]
+  · rintro (rfl | rfl) <;>
+      simp [sevenDepth_carry_zero, sevenDepth_carry_one]
+
+/-- The first seven-regression endpoint exposes only capacity level two. -/
+theorem canonicalEndpointCapacityLevelSlots_seven_zero :
+    canonicalEndpointCapacityLevelSlots sevenDepthOdd 0 = {2} := by
+  classical
+  rw [canonicalEndpointCapacityLevelSlots, canonicalEndpointCapacityDepthSlots,
+    sevenDepth_endpoint_zero]
+  norm_num [orbitWindowHeight_eq_s_iterateT, s, iterateT, T, sevenDepthOdd,
+    mkOddNat, threeNPlusOne, pow2, sevenDepth_v2_22, sevenDepth_v2_34,
+    sevenDepth_v2_52]
+
+/-- The second seven-regression block has only its immediate depth-one claim. -/
+theorem canonicalPaymentClaimDepths_seven_one :
+    canonicalPaymentClaimDepths sevenDepthOdd 1 = {1} := by
+  classical
+  ext d
+  rw [mem_canonicalPaymentClaimDepths_iff]
+  rw [sevenDepth_blockLength_one]
+  unfold canonicalPaymentSourceAtDepth
+  rw [sevenDepth_endpoint_one]
+  simp only [Finset.mem_singleton]
+  constructor
+  · rintro ⟨hd1, hdle, hcarry⟩
+    omega
+  · rintro rfl
+    simp [sevenDepth_carry_three]
+
+/-- The second seven-regression endpoint exposes capacity levels two and three. -/
+theorem canonicalEndpointCapacityLevelSlots_seven_one :
+    canonicalEndpointCapacityLevelSlots sevenDepthOdd 1 = {2, 3} := by
+  classical
+  rw [canonicalEndpointCapacityLevelSlots, canonicalEndpointCapacityDepthSlots,
+    sevenDepth_endpoint_one]
+  norm_num [orbitWindowHeight_eq_s_iterateT, s, iterateT, T, sevenDepthOdd,
+    mkOddNat, threeNPlusOne, pow2, sevenDepth_v2_22, sevenDepth_v2_34,
+    sevenDepth_v2_52, sevenDepth_v2_40]
+  ext d
+  simp
+  omega
+
+/-- One concrete claim-to-capacity assignment entry. -/
+def CanonicalDepthAllocationEntry
+    (n : OddNat) (entry : (ℕ × ℕ) × (ℕ × ℕ)) : Prop :=
+  entry.1.2 ∈ canonicalPaymentClaimDepths n entry.1.1 ∧
+    entry.2.2 ∈ canonicalEndpointCapacityLevelSlots n entry.2.1 ∧
+      entry.1.1 ≤ entry.2.1
+
+/-- The explicit three-claim repayment allocation for the first two blocks from seven. -/
+private def sevenDepthAllocation : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
+  {((0, 2), (0, 2)), ((0, 3), (1, 3)), ((1, 1), (1, 2))}
+
+/-- Every entry of the concrete seven allocation is valid and forward in time. -/
+theorem sevenDepthAllocation_valid :
+    ∀ entry ∈ sevenDepthAllocation,
+      CanonicalDepthAllocationEntry sevenDepthOdd entry := by
+  intro entry hentry
+  simp only [sevenDepthAllocation, Finset.mem_insert, Finset.mem_singleton] at hentry
+  rcases hentry with rfl | rfl | rfl <;>
+    simp [CanonicalDepthAllocationEntry,
+      canonicalPaymentClaimDepths_seven_zero,
+      canonicalPaymentClaimDepths_seven_one,
+      canonicalEndpointCapacityLevelSlots_seven_zero,
+      canonicalEndpointCapacityLevelSlots_seven_one]
+
+/-- The concrete allocation contains all three claims without duplication. -/
+theorem sevenDepthAllocation_left_card :
+    (sevenDepthAllocation.image Prod.fst).card = 3 := by
+  decide
+
+/-- The concrete allocation uses three distinct capacity slots. -/
+theorem sevenDepthAllocation_right_card :
+    (sevenDepthAllocation.image Prod.snd).card = 3 := by
+  decide
+
+/-- The concrete allocation itself has exactly three entries. -/
+theorem sevenDepthAllocation_card : sevenDepthAllocation.card = 3 := by
+  decide
+
+end SevenDepthRegression
+
+/-! ## Audited candidate queue and the corrected frontier
+
+The first orbit-derived eligibility candidate was intentionally audited before
+being exported as a relation.  It assigned depths one and two to level two and
+assigned every depth `d >= 3` only to level `d`, at the same or a later block.
+The finite cp-315 audit refutes that rule: roots 27 and 31 retain a depth-five
+claim, while root 511 retains depth-eight and depth-nine claims after exact
+integer evaluation reaches the fixed state one, which exposes only level two.
+Consequently this module does **not** define `CanonicalRepaymentEligible`.
+
+The definitions below retain the rejected rule only as an observable queue.
+They are useful for stating the exact obstruction and for testing a future
+eligibility rule that permits a justified cross-level payment.  A bounded
+candidate queue would still be weaker than a coherent repayment schedule, and
+neither follows from independent finite-prefix cardinality embeddings.
+-/
+
+/-- Required level under the audited, but refuted, exact-level candidate rule. -/
+def canonicalCandidateRequiredLevel (depth : ℕ) : ℕ :=
+  max 2 depth
+
+/-- Number of claims in block `k` routed to candidate level `level`. -/
+noncomputable def canonicalCandidateLevelDemand
+    (n : OddNat) (k level : ℕ) : ℕ :=
+  ((canonicalPaymentClaimDepths n k).filter fun depth =>
+    canonicalCandidateRequiredLevel depth = level).card
+
+/-- Whether canonical block `k` exposes the selected capacity level. -/
+noncomputable def canonicalCandidateLevelCapacity
+    (n : OddNat) (k level : ℕ) : ℕ :=
+  if level ∈ canonicalEndpointCapacityLevelSlots n k then 1 else 0
+
+/--
+FIFO outstanding queue generated by the audited exact-level candidate.
+
+Capacity is not banked: each block first adds its demand and then consumes its
+single slot at that level when present.  This is an executable obstruction
+observable, not a valid general repayment theorem.
+-/
+noncomputable def canonicalCandidateLevelOutstandingQueue
+    (n : OddNat) (level : ℕ) : ℕ → ℕ
+  | 0 => canonicalCandidateLevelDemand n 0 level -
+      canonicalCandidateLevelCapacity n 0 level
+  | k + 1 => canonicalCandidateLevelOutstandingQueue n level k +
+      canonicalCandidateLevelDemand n (k + 1) level -
+        canonicalCandidateLevelCapacity n (k + 1) level
+
+/-- The candidate queue's successor equation, exposed for later comparisons. -/
+theorem canonicalCandidateLevelOutstandingQueue_succ
+    (n : OddNat) (level k : ℕ) :
+    canonicalCandidateLevelOutstandingQueue n level (k + 1) =
+      canonicalCandidateLevelOutstandingQueue n level k +
+        canonicalCandidateLevelDemand n (k + 1) level -
+          canonicalCandidateLevelCapacity n (k + 1) level := rfl
+
+/-- Strong queue target; the cp-315 audit does not establish this predicate. -/
+def CanonicalCandidateLevelQueuesUniformlyBounded
+    (n : OddNat) (C : ℕ) : Prop :=
+  ∀ level k, canonicalCandidateLevelOutstandingQueue n level k ≤ C
+
+/-!
+The valid global target remains `CanonicalEndpointBalanceUniformUpperBound`,
+already proved to imply a canonical endpoint bit-width bound.  Passing from an
+endpoint bound to an all-time bound additionally requires a uniform in-block
+overshoot estimate.  Passing from an all-time bit-width bound to eventual
+periodicity is a separate finite-state argument.  Neither implication is
+silently folded into the rejected exact-level queue model.
+-/
+
+end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentRepayment.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentRepayment.lean
index b9750cd2..1ba744eb 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentRepayment.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentRepayment.lean
@@ -752,9 +752,11 @@ The claim and capacity sides now both have exact depth coordinates, and marked
 recovery incidence has exact cardinality. What is not proved is that a claim
 depth is eligible for a same-depth slot at its own or a later endpoint. That
 relation must encode an orbit invariant, not merely matching cardinalities.
-Accordingly no eligibility predicate is exported yet and no forward repayment
-matching is asserted. The next implementation must derive and test that local
-invariant before constructing a payment map.
+Accordingly no eligibility predicate is exported here and no forward repayment
+matching is asserted.  The cp-315 audit in `UniversalPaymentDepthLedger` tests
+the first exact-level candidate and refutes it on roots 27, 31, and 511.  A
+future relation must therefore justify cross-level payment or identify a
+different orbit-derived capacity coordinate before constructing a payment map.
 -/
 
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-315.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-315.md
new file mode 100644
index 00000000..9061a527
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-315.md
@@ -0,0 +1,202 @@
+# Petal / Collatz implementation report: cp-315
+
+## Result
+
+Checkpoint cp-315 closes the exact finite accounting and carrier-reindexing
+work requested after cp-314, then reaches a genuine semantic obstruction.
+
+Lean now proves exact excursion, window repayment, depth-ledger, carrier
+equivalence, and seven-regression theorems.  A separate executable audit then
+refutes the proposed exact-level eligibility rule on three of the four required
+roots.  In each failing case exact integer evaluation reaches fixed state `1`
+while a higher-level claim remains.  Consequently no general
+`CanonicalRepaymentEligible` relation was exported.
+
+This is the intended safe stopping condition: the rejected rule is represented
+as an observable queue, not promoted into a false repayment API.
+
+## Exact excursion and window repayment
+
+The new module is
+`DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentDepthLedger`.
+
+Lean proves:
+
+```text
+CanonicalEndpointPositiveExcursionAt n q
+  <-> 0 < endpointAccountingTerm n q
+```
+
+For `q <= r`, Lean also proves that repayment from `q` through `r` is
+equivalent to both:
+
+```text
+sum (endpointAccountingTerm n k), k in q..r <= 0
+```
+
+and
+
+```text
+window claims q..r <= window capacity q..r.
+```
+
+The proof uses the sliding endpoint-balance telescope.  It does not reuse the
+weaker prefix-to-future-horizon embedding as a balance certificate.
+
+Actual window claim and capacity carriers were added.  Their `Nat.card` values
+are exactly the corresponding window totals.  The new
+`CanonicalEndpointForwardWindowMatching` is an injective within-window map
+whose payment block is not earlier than its claim block.  Lean proves that any
+such matching repays the selected excursion.
+
+## Scalar depth ledger
+
+`canonicalEndpointCapacityLevelSlots` is the semantic alias for endpoint
+capacity coordinates.  The signed term
+`canonicalDepthAccountingTerm n k d` records claim incidence minus capacity
+incidence at one numeric coordinate.
+
+For every canonical block, Lean proves:
+
+```text
+endpointAccountingTerm n k
+  = sum d in canonicalDepthAccountingSupport n k,
+      canonicalDepthAccountingTerm n k d.
+```
+
+The family theorem then sums this exact block-local decomposition over all
+blocks through `m`.  Thus the signed endpoint ledger is exposed level by level
+without asserting that equal numeric levels are valid payment partners.
+
+## Proof-independent carriers
+
+The following carriers were added:
+
+```text
+CanonicalEndpointDepthClaimCarrier n m
+CanonicalEndpointLevelCapacityCarrier n m
+```
+
+Their cardinalities are exactly cumulative claims and cumulative capacity.
+More strongly, Lean constructs actual equivalences:
+
+```text
+CanonicalEndpointClaimCarrier n m
+  ~= CanonicalEndpointDepthClaimCarrier n m
+
+CanonicalEndpointCapacityCarrier n m
+  ~= CanonicalEndpointLevelCapacityCarrier n m
+```
+
+The claim equivalence uses the injective exact recovery-depth coordinate.  The
+capacity equivalence is the coordinate translation `slot s <-> level s + 2`.
+
+## Exact seven regression
+
+Lean proves the required finite sets:
+
+```text
+block 0 claims    = {2, 3}
+block 0 capacity  = {2}
+block 1 claims    = {1}
+block 1 capacity  = {2, 3}
+```
+
+It also verifies the explicit forward allocation:
+
+```text
+(block 0, depth 2) -> (block 0, level 2)
+(block 0, depth 3) -> (block 1, level 3)
+(block 1, depth 1) -> (block 1, level 2)
+```
+
+The allocation has three distinct claims and three distinct capacity slots.
+
+## Eligibility audit
+
+The audit implementation is:
+
+```text
+python/Collatz/PetalBridge/canonical_depth_eligibility_audit.py
+```
+
+It mirrors the Lean definitions and asserts the exact seven regression before
+running.  It tests claims from the first 1024 canonical blocks against capacity
+through block 4095, and separately observes the streaming queue over all 4096
+blocks.
+
+The audited candidate was:
+
+```text
+depth 1 -> level 2
+depth 2 -> level 2
+depth d, d >= 3 -> level d
+payment block >= claim block
+```
+
+Results:
+
+| root | first state-1 time | prefix claims | outstanding | persistent detail | max lag |
+| --- | ---: | ---: | ---: | --- | ---: |
+| 7 | 5 | 1025 | 0 | none | 1 |
+| 27 | 41 | 1032 | 1 | block 9, depth 5 -> level 5 | 14 |
+| 31 | 39 | 1032 | 1 | block 8, depth 5 -> level 5 | 14 |
+| 511 | 20 | 1027 | 2 | block 0, depths 8 and 9 -> levels 8 and 9 | 2 |
+
+Roots 27 and 31 each also exhibit one simultaneous depth-1/depth-2 collision at
+an endpoint with only one level-2 slot.  The queue can delay one of these
+claims, so this collision alone is not the decisive counterexample.  The
+decisive obstruction is a high-depth claim whose required exact level cannot
+reappear after the simulation reaches state `1`: the accelerated step fixes
+`1`, and its endpoint height is two.  This is an exact finite computation
+followed by a fixed-point observation, but it is not promoted here to a Lean
+theorem about these concrete roots.
+
+Generated evidence is recorded in:
+
+```text
+python/Collatz/PetalBridge/results/canonical_depth_eligibility_audit_315.csv
+python/Collatz/PetalBridge/results/canonical_depth_eligibility_audit_315.md
+```
+
+These files are finite computational evidence, not Lean proofs of an infinite
+orbit statement.
+
+## Corrected frontier
+
+The rejected rule is retained only through:
+
+```text
+canonicalCandidateRequiredLevel
+canonicalCandidateLevelDemand
+canonicalCandidateLevelCapacity
+canonicalCandidateLevelOutstandingQueue
+CanonicalCandidateLevelQueuesUniformlyBounded
+```
+
+This makes the obstruction measurable and gives a comparison surface for a
+future corrected rule.  The next rule must justify cross-level payment, or it
+must derive a different capacity coordinate from the orbit.  Equal numeric
+depth and level cannot be required globally.
+
+The valid strong target remains a uniform canonical endpoint balance bound.
+It implies a canonical endpoint bit-width bound by an existing theorem.  An
+all-time bit-width bound still additionally needs a uniform in-block overshoot
+bound, and eventual periodicity remains a separate finite-state implication.
+No convergence or cycle-rigidity claim is made here.
+
+## Verification
+
+Completed during implementation:
+
+```text
+lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentDepthLedger
+lake build DkMath.Collatz.PetalBridge.FloatWindow
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath
+python3 python/Collatz/PetalBridge/canonical_depth_eligibility_audit.py
+git diff --check
+```
+
+All build gates passed.  The new Lean module contains no `sorry`.  Existing
+unrelated project warnings remain outside this checkpoint.
diff --git a/python/Collatz/PetalBridge/canonical_depth_eligibility_audit.py b/python/Collatz/PetalBridge/canonical_depth_eligibility_audit.py
new file mode 100644
index 00000000..5bc2edb3
--- /dev/null
+++ b/python/Collatz/PetalBridge/canonical_depth_eligibility_audit.py
@@ -0,0 +1,213 @@
+#!/usr/bin/env python3
+"""Finite audit of the canonical depth/level repayment candidate.
+
+This mirrors the Lean definitions used by UniversalPaymentDepthLedger:
+
+* the state at time i is the i-th accelerated odd state;
+* exact depth is v2(state + 1);
+* endpoint height is v2(3 * state + 1);
+* canonical endpoints iterate target(i) = i + exact_depth(i) - 1;
+* every carry-two source in a block produces its endpoint-relative depth;
+* an endpoint of height h exposes one slot at every level in [2, h].
+
+The candidate eligibility rule sends depth one and depth two to level two,
+and every delayed depth d >= 3 to level d, at the same or a later block.
+The script is evidence only.  It does not turn a finite audit into a theorem.
+"""
+
+from __future__ import annotations
+
+import csv
+from collections import defaultdict, deque
+from dataclasses import dataclass
+from pathlib import Path
+
+
+ROOTS = (7, 27, 31, 511)
+CLAIM_BLOCKS = 1024
+HORIZON_BLOCKS = 4096
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
+def bit_width(value: int) -> int:
+    return value.bit_length()
+
+
+def upper_carry(value: int) -> int:
+    return (3 * value + 1) >> bit_width(value)
+
+
+@dataclass(frozen=True)
+class Claim:
+    block: int
+    depth: int
+
+    @property
+    def required_level(self) -> int:
+        return 2 if self.depth <= 2 else self.depth
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
+def canonical_endpoints(orbit: Orbit, count: int) -> list[int]:
+    endpoints = [orbit.target(0)]
+    while len(endpoints) < count:
+        endpoints.append(orbit.target(endpoints[-1] + 1))
+    return endpoints
+
+
+def block_claims(orbit: Orbit, endpoints: list[int], block: int) -> list[Claim]:
+    start = 0 if block == 0 else endpoints[block - 1] + 1
+    endpoint = endpoints[block]
+    return [
+        Claim(block, endpoint - time + 1)
+        for time in range(start, endpoint + 1)
+        if upper_carry(orbit.state(time)) == 2
+    ]
+
+
+def audit_root(root: int) -> dict[str, int | bool]:
+    orbit = Orbit(root)
+    endpoints = canonical_endpoints(orbit, HORIZON_BLOCKS)
+    claims_by_block = [
+        block_claims(orbit, endpoints, block) for block in range(HORIZON_BLOCKS)
+    ]
+
+    prefix_queues: dict[int, deque[Claim]] = defaultdict(deque)
+    stream_queues: dict[int, deque[Claim]] = defaultdict(deque)
+    prefix_claims = 0
+    prefix_paid = 0
+    max_prefix_lag = 0
+    max_stream_total = 0
+    max_stream_level_two = 0
+    collisions = 0
+    collisions_one_level_two_slot = 0
+    first_collision = "none"
+
+    for block in range(HORIZON_BLOCKS):
+        claims = claims_by_block[block]
+        depths = {claim.depth for claim in claims}
+        if 1 in depths and 2 in depths:
+            collisions += 1
+            if first_collision == "none":
+                first_collision = (
+                    f"b{block}:endpoint{endpoints[block]}:"
+                    f"height{orbit.height(endpoints[block])}"
+                )
+            if orbit.height(endpoints[block]) == 2:
+                collisions_one_level_two_slot += 1
+
+        for claim in claims:
+            stream_queues[claim.required_level].append(claim)
+            if block < CLAIM_BLOCKS:
+                prefix_queues[claim.required_level].append(claim)
+                prefix_claims += 1
+
+        for level in range(2, orbit.height(endpoints[block]) + 1):
+            if prefix_queues[level]:
+                claim = prefix_queues[level].popleft()
+                prefix_paid += 1
+                max_prefix_lag = max(max_prefix_lag, block - claim.block)
+            if stream_queues[level]:
+                stream_queues[level].popleft()
+
+        max_stream_total = max(max_stream_total, sum(map(len, stream_queues.values())))
+        max_stream_level_two = max(max_stream_level_two, len(stream_queues[2]))
+
+    prefix_outstanding = sum(map(len, prefix_queues.values()))
+    stream_outstanding = sum(map(len, stream_queues.values()))
+    first_state_one_time = next(
+        (time for time, state in enumerate(orbit.states) if state == 1), -1
+    )
+    prefix_outstanding_detail = ";".join(
+        f"b{claim.block}:d{claim.depth}->l{level}"
+        for level in sorted(prefix_queues)
+        for claim in prefix_queues[level]
+    )
+    return {
+        "root": root,
+        "claim_blocks": CLAIM_BLOCKS,
+        "horizon_blocks": HORIZON_BLOCKS,
+        "prefix_claims": prefix_claims,
+        "prefix_paid": prefix_paid,
+        "prefix_outstanding": prefix_outstanding,
+        "prefix_outstanding_detail": prefix_outstanding_detail or "none",
+        "first_state_one_time": first_state_one_time,
+        "prefix_max_lag": max_prefix_lag,
+        "stream_outstanding": stream_outstanding,
+        "stream_max_total_queue": max_stream_total,
+        "stream_max_level_two_queue": max_stream_level_two,
+        "depth1_depth2_collisions": collisions,
+        "collisions_with_one_level_two_slot": collisions_one_level_two_slot,
+        "first_depth1_depth2_collision": first_collision,
+        "prefix_candidate_survived": prefix_outstanding == 0,
+    }
+
+
+def main() -> None:
+    seven = Orbit(7)
+    seven_endpoints = canonical_endpoints(seven, 2)
+    assert [claim.depth for claim in block_claims(seven, seven_endpoints, 0)] == [3, 2]
+    assert [claim.depth for claim in block_claims(seven, seven_endpoints, 1)] == [1]
+    assert list(range(2, seven.height(seven_endpoints[0]) + 1)) == [2]
+    assert list(range(2, seven.height(seven_endpoints[1]) + 1)) == [2, 3]
+
+    rows = [audit_root(root) for root in ROOTS]
+    output_dir = Path(__file__).with_name("results")
+    output_dir.mkdir(parents=True, exist_ok=True)
+    csv_path = output_dir / "canonical_depth_eligibility_audit_315.csv"
+    md_path = output_dir / "canonical_depth_eligibility_audit_315.md"
+
+    with csv_path.open("w", newline="", encoding="utf-8") as stream:
+        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
+        writer.writeheader()
+        writer.writerows(rows)
+
+    headers = list(rows[0])
+    lines = [
+        "# Canonical Depth Eligibility Audit (cp-315)",
+        "",
+        f"Claim prefix: {CLAIM_BLOCKS} blocks. Capacity horizon: {HORIZON_BLOCKS} blocks.",
+        "This is finite computational evidence, not a Lean theorem.",
+        "",
+        "| " + " | ".join(headers) + " |",
+        "| " + " | ".join("---" for _ in headers) + " |",
+    ]
+    lines.extend(
+        "| " + " | ".join(str(row[key]) for key in headers) + " |" for row in rows
+    )
+    md_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
+
+    for row in rows:
+        print(row)
+
+
+if __name__ == "__main__":
+    main()
diff --git a/python/Collatz/PetalBridge/results/canonical_depth_eligibility_audit_315.csv b/python/Collatz/PetalBridge/results/canonical_depth_eligibility_audit_315.csv
new file mode 100644
index 00000000..feaa8bbd
--- /dev/null
+++ b/python/Collatz/PetalBridge/results/canonical_depth_eligibility_audit_315.csv
@@ -0,0 +1,5 @@
+root,claim_blocks,horizon_blocks,prefix_claims,prefix_paid,prefix_outstanding,prefix_outstanding_detail,first_state_one_time,prefix_max_lag,stream_outstanding,stream_max_total_queue,stream_max_level_two_queue,depth1_depth2_collisions,collisions_with_one_level_two_slot,first_depth1_depth2_collision,prefix_candidate_survived
+7,1024,4096,1025,1025,0,none,5,1,0,1,0,0,0,none,True
+27,1024,4096,1032,1031,1,b9:d5->l5,41,14,1,6,1,1,1,b7:endpoint20:height2,False
+31,1024,4096,1032,1031,1,b8:d5->l5,39,14,1,6,1,1,1,b6:endpoint18:height2,False
+511,1024,4096,1027,1025,2,b0:d8->l8;b0:d9->l9,20,2,2,5,0,0,0,none,False
diff --git a/python/Collatz/PetalBridge/results/canonical_depth_eligibility_audit_315.md b/python/Collatz/PetalBridge/results/canonical_depth_eligibility_audit_315.md
new file mode 100644
index 00000000..246151f7
--- /dev/null
+++ b/python/Collatz/PetalBridge/results/canonical_depth_eligibility_audit_315.md
@@ -0,0 +1,11 @@
+# Canonical Depth Eligibility Audit (cp-315)
+
+Claim prefix: 1024 blocks. Capacity horizon: 4096 blocks.
+This is finite computational evidence, not a Lean theorem.
+
+| root | claim_blocks | horizon_blocks | prefix_claims | prefix_paid | prefix_outstanding | prefix_outstanding_detail | first_state_one_time | prefix_max_lag | stream_outstanding | stream_max_total_queue | stream_max_level_two_queue | depth1_depth2_collisions | collisions_with_one_level_two_slot | first_depth1_depth2_collision | prefix_candidate_survived |
+| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
+| 7 | 1024 | 4096 | 1025 | 1025 | 0 | none | 5 | 1 | 0 | 1 | 0 | 0 | 0 | none | True |
+| 27 | 1024 | 4096 | 1032 | 1031 | 1 | b9:d5->l5 | 41 | 14 | 1 | 6 | 1 | 1 | 1 | b7:endpoint20:height2 | False |
+| 31 | 1024 | 4096 | 1032 | 1031 | 1 | b8:d5->l5 | 39 | 14 | 1 | 6 | 1 | 1 | 1 | b6:endpoint18:height2 | False |
+| 511 | 1024 | 4096 | 1027 | 1025 | 2 | b0:d8->l8;b0:d9->l9 | 20 | 2 | 2 | 5 | 0 | 0 | 0 | none | False |
````
`````
