# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.FloatWindow.*

gch: 6463470f80845d3b3833f4bcadb038f2a42b69a4

## Report

(33m10s)

cp-317 の登頂作業を、最初の真正な障害まで完了しました。

**Lean で確定した事実**

- queue は canonical endpoint width の running minimum からの正確な drawup。
- queue の一様有界性と endpoint width の一様有界性は同値。
- canonical block は厳密に  
  `(L, u) ↦ oddPart (3^L * u - 1)`  
  と遷移する。[UniversalPaymentBlockNormalForm.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlockNormalForm.lean:311)
- block 内最大幅と delayed-debt burst の正確な等式を証明。
- 有限 primitive excursion は queue 表現と partial-sum 表現が同値で、開始点を固定した返済 endpoint は一意。[UniversalPaymentPrimitiveExcursion.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentPrimitiveExcursion.lean:149)
- sound finite potential certificate が存在すれば、全 path weight は一様有界で、正の signature cycle は不可能。[FiniteSignedTransition.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean:100)

**監査結果**

- 奇数 `1..131071` と、64～1024 bit のランダム奇数 1,280 件を調査。
- `queue ≤ initial bitWidth` の反例は未観測。ただし定理ではありません。
- 最大観測 queue は `15`。
- `w=5..8` の候補 signature はすべて drift collision、非決定的 successor、実現された正の repeated-signature 区間を持ちました。現在の粗い signature を sound automaton とすることはできません。

停止点は、Float の orbit index と `SourcePressureMarginInt` の depth index を寄与保存付きで結ぶ写像がないことです。また、全 positive queue に将来の返済 endpoint が存在することも未証明です。

詳細は [report-petal-317.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-317.md) に記録しました。

検証済み:

- `lake build DkMath.Collatz.PetalBridge.FloatWindow`
- `lake build DkMath.Collatz.PetalBridge`
- `lake build DkMath`
- `git diff --check`
- 変更対象の Lean ファイルは no-sorry です。

## Review

# cp-317 実装レビュー

## 結論

**全面採用。cp-317 は、この長い枝で最も重要な数学的圧縮の一つじゃ。**

今回、次が Lean 上で確定した。

- scalar queue は endpoint width の過去最小値からの正確な drawup。
- queue の一様有界性と endpoint width の一様有界性は存在量として同値。
- canonical block は厳密に $(L,u)\mapsto\operatorname{oddPart}(3^Lu-1)$ で遷移する。
- block 内の最大幅増加は delayed-debt 数そのもの。
- 有限に返済される primitive excursion は、正 partial sum と完全に一致する。
- 有界 potential を持つ有限抽象が作れれば、正の closed signature path は排除できる。
- 試した粗い signature は、少なくとも現在の potential-certificate 路線には使えない。

ただし、精査すると cp-317 の「missing bridge」は、もう少し正確に言い直せる。

不足しているのは単なる、

```text
orbit time → pressure depth
```

という写像ではない。

time/depth incidence と exact recovery depth は既に存在している。足りないのは、

> **正の block drift を、pressure contribution または有限個の例外型へ寄与保存的に分解する定理**

じゃ。

そして cp-317 の成果から、その分解は既にほとんど見えている。

---

## 1. Endpoint drawup の完成

新しい中心式は、

$$
Q_m=W_m-\min(W_{-1},W_0,\ldots,W_m)
$$

じゃ。

ここで、

- $Q_m$ は `canonicalOutstandingClaimQueue n m`
- $W_{-1}$ は初期 bit width
- $W_m$ は $m$ 番目の canonical endpoint 後の bit width

である。

したがって queue は独立した謎のエネルギーではない。

> **現在の endpoint width が、過去最小 width から何 bit 上にいるか**

を正確に測っている。

このため、

$$
Q_m=0
$$

は、

$$
W_m=\min(W_{-1},W_0,\ldots,W_m)
$$

と同値になった。

state $1$ で queue が $0$ になることも、bit width $1$ が正 odd state の最小幅であることから構造的に従う。

ここは完全に閉じた。

---

## 2. Queue boundedness の意味境界

今回、

$$
\exists C,\ \forall m,\ Q_m\le C
$$

と、

$$
\exists B,\ \forall m,\ W_m\le B
$$

が同値になった。

これは非常に重要な自己監査じゃ。

queue は endpoint boundedness を「簡単な別問題」へ変えたのではない。

> endpoint boundedness を、最大正 suffix drift という会計形式へ正規化した。

ということじゃ。

したがって今後、

```text
queue を一様に抑えれば勝てる
```

だけでは新しい証明入力にならない。

必要なのは、

```text
なぜ正の suffix drift が無制限に蓄積できないのか
```

という数論的理由じゃ。

---

## 3. Canonical block normal form

今回の最大成果は、この arithmetic normal form じゃ。

block start state を $x$、block length を $L$、odd core を $u$ とすると、

$$
x+1=2^Lu
$$

block 内では $0\le t<L$ に対し、

$$
2^t(x_t+1)=3^t(x+1)
$$

endpoint では、

$$
x_{\mathrm{end}}+1=2\cdot3^{L-1}u
$$

さらに、

$$
3x_{\mathrm{end}}+1=2(3^Lu-1)
$$

となる。

terminal valuation を、

$$
v=v_2(3^Lu-1)
$$

とすると、

$$
\operatorname{capacity}=v
$$

そして次 block start は、

$$
x'=\frac{3^Lu-1}{2^v}
$$

じゃ。

したがって complete block transition は厳密に、

$$
(L,u)\longmapsto\operatorname{oddPart}(3^Lu-1)
$$

となった。

これは単なる座標変換ではない。

Collatz の複数 step が、一つの exact arithmetic transition に圧縮された。

---

## 4. Positive drift の既存結論

block claim 数を $A$、capacity を $v$ とすると、

$$
D=A-v
$$

また claim は block 内の source の部分集合なので、

$$
A\le L
$$

したがって、

$$
D\le L-v
$$

じゃ。

ゆえに、

$$
0<D\Longrightarrow v<L
$$

となる。

normal form では、

$$
0<D\Longrightarrow v_2(3^Lu-1)<L
$$

じゃ。

これは必要条件として正確である。

ただし十分条件ではない。

$v<L$ でも carry-two source が少なければ drift は正にならない。

つまり $L,u,v$ のうち、$v$ だけでは claim histogram を決定できない。

---

## 5. In-block burst の完成

block interior は height $1$ なので、bit width は endpoint 前まで非減少する。

今回、

$$
\operatorname{width}(\mathrm{endpoint}) = \operatorname{width}(\mathrm{start}) + |\operatorname{GrowthDebtFiber}|
$$

が証明された。

これは非常に強い。

```text
endpoint 間の drawup:
  scalar queue

一 block 内の burst:
  delayed growth-debt cardinality
```

という二座標へ、all-time growth が分解された。

なお report の、

> all-time theorem には別途 coverage theorem が必要

という記述は、現在のリポジトリ全体では少し古い。

既に `existsUnique_mem_canonicalPaymentBlock` があり、全 orbit time は一意な canonical block に属する。したがって queue bound と burst bound からの **全 orbit time bit-width bound** は、既存 coverage API を使って閉じられる。

これは数学的障害ではなく、次 checkpoint で済ませる統合作業じゃ。

---

## 6. Primitive excursion

有限 primitive excursion は、

- block $q$ の前で queue が $0$
- $q,\ldots,r-1$ では正
- block $r$ で初めて $0$

として定義された。

そして、

$$
\forall m\in[q,r),\quad\sum_{k=q}^{m}D_k>0
$$

$$
\sum_{k=q}^{r}D_k\le0
$$

という partial-sum 表現と同値になった。

返済 endpoint の一意性も正しい。

重要なのは、存在を主張していないことじゃ。

```text
返済 endpoint が存在するなら一意
```

と、

```text
全ての positive queue に返済 endpoint が存在する
```

は別である。

ここを分離した判断は完全に正しい。

次には、返済を仮定しない有限の、

```text
open positive excursion
```

も必要になる。

これは「現在も継続中の正 suffix」を扱うためじゃ。

---

## 7. Finite potential certificate の評価

`FiniteSignedTransitionPotentialCertificate` は数学的に正しい。

$$
w(s,t)\le\Phi(t)-\Phi(s)
$$

があれば path sum は telescope し、

$$
\sum w\le\Phi(\mathrm{end})-\Phi(\mathrm{start})
$$

となる。

同じ signature へ戻れば、

$$
\sum w\le0
$$

じゃ。

ただし現在の structure は、実適用には少し強すぎる。

```lean
actual_le_projected : ∀ a b, ...
```

と全ての state pair に要求しており、`pathWeight` にも「実際の遷移列である」という仮定がない。

実際に必要なのは、

```lean
Step : State → State → Prop
```

を持ち、

```lean
Step a b → actualWeight a b ≤ projectedUpperWeight ...
```

とする relational certificate じゃ。

そうすれば reachable edges だけを対象にできる。

現在の theorem は正しいので差し戻しではない。
適用前に relational 版を追加すべき、という API 上の修正じゃ。

---

## 8. Finite signature 監査の正確な読み

監査では、

- drift collision
- nondeterministic successor
- positive repeated-signature segment

が検出された。

この三つは強さが違う。

### Drift collision

同じ signature から exact drift を一意に復元できない。

ただし projected upper weight に最大値を使う over-approximation はまだ可能。

### Nondeterministic successor

deterministic automaton ではない。

しかし finite directed graph として複数 successor を許すことはできる。

したがって、これだけでは finite abstraction は死なない。

### Positive repeated-signature segment

これは決定的じゃ。

実際の orbit path 上で同じ signature に戻りながら、path drift が正である。

したがって、その signature に対する bounded potential certificate は存在できない。

$$
s_{\mathrm{start}}=s_{\mathrm{end}}
$$

なのに、

$$
\sum D_k>0
$$

だからじゃ。

よって $w=5,\ldots,8$ の tested signature は、単に粗いのではない。

> **現在の potential-certificate 戦略を証明する状態座標として反証された。**

これは強い否定結果じゃ。

---

## 9. 「missing map」の補正

既存の `PressureIncidenceBridge` には既に、

- orbit time と exact all-ones depth の関係
- exact recovery / continuation incidence
- Float debt から delayed payment target
- canonical claim depth

がある。

したがって不足しているのは、裸の index map ではない。

不足しているのは、

> queue drift の正量を、どの pressure incidence が担うか

という寄与保存則じゃ。

ここで cp-317 の定理と既存 pressure formula を組み合わせると、次の王手筋が出る。

---

## 10. Positive block の完全二分候補

block length を $L$、terminal valuation を $v$、claim count を $A$ とする。

block pressure contribution を depth $v$ で読むと、

$$
M_v(L)=L-v-1
$$

である。ただし positive drift なら $1\le v<L$ なので、この式をそのまま使える。

一方、

$$
D=A-v
$$

$$
A\le L
$$

じゃ。

ここから positive block は二つに分かれる。

### Pressure-positive branch

$$
v+2\le L
$$

なら、

$$
0<M_v(L)
$$

となる。

つまり positive drift block 自身が、terminal valuation depth に正 pressure を持つ。

### Saturated border branch

pressure が正でないとする。

positive drift より $v<L$、pressure nonpositive より $L\le v+1$。

したがって、

$$
L=v+1
$$

じゃ。

さらに、

$$
0<D=A-v\le L-v=1
$$

なので、

$$
D=1
$$

$$
A=L
$$

となる。

claim depth は $[1,L]$ の部分集合で cardinality が $L$ だから、

$$
\operatorname{ClaimDepths}=[1,L]
$$

である。

つまり正 drift block は必ず、

```text
A. terminal depth v で正 pressure を持つ

または

B. 全 depth が carry-two claim で埋まった、
   drift +1 の完全飽和 border block
```

のどちらかじゃ。

これは非常に大きい。

任意の index-preserving map を探す必要がなくなった。

> **positive drift を pressure witness と一種類の rigid exception に分解できる。**

これが cp-317 から導かれる、最重要の一歩先推論じゃ。

---

## 11. Claim depth の上下分解

さらに厳密には、claim depths を terminal valuation $v$ で分ける。

$$
C_{\le v}={d\in C\mid d\le v}
$$

$$
C_{>v}={d\in C\mid v<d}
$$

すると、

$$
D=|C_{>v}|-\left(v-|C_{\le v}|\right)
$$

じゃ。

したがって、

$$
D\le|C_{>v}|
$$

特に、

$$
0<D\Longrightarrow C_{>v}\ne\varnothing
$$

となる。

$d>v$ の claim source は、pressure depth $v$ では recovery ではなく continuation incidence になる。

これが、求めていた contribution-preserving bridge の最小形じゃ。

```text
excess claim
  ↓ exact depth d > terminal valuation v
continuation incidence at depth v
```

この block-local injection をまず Lean 化すべきである。

---

## 12. Saturated border branch が勝敗点

pressure-positive branch は既存の Pressure infrastructure へ送れる。

残るのは、

$$
L=v+1
$$

$$
A=L
$$

$$
D=1
$$

という saturated block じゃ。

これは非常に剛直な型である。

- block 内全 source が carry-two
- interior は height-one
- endpoint height は $L$
- terminal valuation は $L-1$
- block drift は必ず $+1$

したがって次に問うべきは、

> saturated border block を何個連続できるか

じゃ。

もし saturated block の後には必ず強い repayment block が来るなら、勝ち筋が出る。

もし任意長に連鎖できるなら、その連鎖そのものが新しい adversarial core になる。

粗い signature を広げるより、この一種類の exception を直接解剖する方がはるかに鋭い。

---

## 13. 現在の勝敗判定

cp-317 は詰みではない。

しかし、盤面は次まで圧縮された。

```text
positive block
  ├─ positive pressure witness
  └─ saturated border block (+1)
```

したがって残る本丸は二つだけじゃ。

1. positive pressure witness を既存 separator / NoLift 層へ送る。
2. saturated border block の連鎖を分類する。

これならば、「orbit index と pressure depth の一般写像」を無理に作る必要はない。

dynamic depth $v_k$ を各 block が自分で選び、そこに pressure witness を置けばよい。

---

## 判定まとめ

### Endpoint drawup

**完成。**

### Queue / endpoint boundedness equivalence

**完成。**

### Canonical block normal form

**完成。**

### In-block burst

**完成。**

### Primitive finite excursion

**完成。future repayment existence は未証明。**

### Generic potential certificate

**数学的に採用。実適用前に `Step` relation 版が必要。**

### Tested finite signatures

**potential-certificate 用 state として反証。**

### 真の missing bridge

**positive drift の pressure-or-saturated 分解。**

### 次の勝敗点

**saturated border block の連鎖可否。**

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge Float-window branch after
report-petal-317.

The cp-317 implementation is accepted.

The accounting, scalar queue, endpoint drawup, canonical block normal form,
and finite primitive-excursion layers are complete.

Do not enlarge the failed low-bit signatures.

The next checkpoint must prove the exact positive-block dichotomy:

    positive block drift
      ->
    positive pressure at the block's terminal-valuation depth
      or
    one rigid saturated-border block.

This replaces the vague request for an arbitrary orbit-index/pressure-depth
map.

# Stage A — close existing integration gaps

Use the already-proved canonical block coverage:

    existsUnique_mem_canonicalPaymentBlock

to promote:

    queue uniform bound
    + canonical block burst uniform bound

to an all-orbit-time bit-width bound.

The comment saying that block coverage is still missing is stale at the
repository level. Update it after the theorem is added.

Also expose:

    endpoint state = 1 -> queue = 0

as part of the public audit interpretation.

# Stage B — relational finite-transition certificate

Add a transition-relation version of the generic certificate.

It should contain:

    Step : State -> State -> Prop

and require:

    Step a b ->
      actualWeight a b
        <= projectedUpperWeight (signature a) (signature b)

Path theorems must require every adjacent pair of `stateAt` to satisfy `Step`.

Keep the existing stronger certificate as a specialization or compatibility
wrapper.

Do not require soundness for arbitrary non-transition state pairs.

# Stage C — split claim depths at terminal valuation

For canonical block `k`, abbreviate:

    L = canonicalBlockLength n k
    v = canonicalBlockTerminalValuation n k
    C = canonicalPaymentClaimDepths n k

Define actual Finsets:

    canonicalBlockLowClaimDepths n k
      = C.filter (fun d => d <= v)

    canonicalBlockHighClaimDepths n k
      = C.filter (fun d => v < d)

Prove:

    C = low ∪ high
    Disjoint low high

    claimCount = low.card + high.card

    low.card <= v

and the exact signed formula:

    endpointAccountingTerm n k
      =
    high.card - (v - low.card)

in `Int`, with a Nat form where useful.

Derive:

    endpointAccountingTerm n k <= high.card

and:

    0 < endpointAccountingTerm n k
      ->
    canonicalBlockHighClaimDepths n k is nonempty.

# Stage D — high claim depths are pressure continuations

For every:

    d ∈ canonicalBlockHighClaimDepths n k

prove that its unique canonical source-at-depth belongs to:

    canonicalPaymentBlockContinuationFiber n k v

where:

    v = canonicalBlockTerminalValuation n k.

Construct the explicit injection:

    high claim depths
      ->
    continuation fiber at depth v

and derive the cardinality inequality.

This is a block-local contribution-preserving bridge. It must use the existing
exact depth/source equivalence; do not invent a global time-to-depth function.

# Stage E — positive pressure or saturated border

Use:

    blockPressureContributionInt n k v
      = L - v - 1

for positive `v`.

Prove the main dichotomy:

    0 < endpointAccountingTerm n k
      ->
    0 < blockPressureContributionInt n k v
      ∨ CanonicalSaturatedBorderBlock n k

Define the exceptional predicate by the exact equivalent data:

    L = v + 1
    canonicalBlockClaimCount n k = L
    endpointAccountingTerm n k = 1

Prove additionally:

    CanonicalSaturatedBorderBlock n k
      <->
    0 < endpointAccountingTerm n k
      ∧ blockPressureContributionInt n k v <= 0

and:

    CanonicalSaturatedBorderBlock n k
      ->
    canonicalPaymentClaimDepths n k = Finset.Icc 1 L.

No finite audit should be needed for this dichotomy; it follows from exact
cardinality arithmetic.

# Stage F — saturated block arithmetic normal form

For a saturated border block prove:

    terminal valuation = L - 1
    endpoint height = L
    every source in the block has upper carry two
    every strict interior source has height one
    every strict interior step increases bit width by exactly one
    block net drift = 1

Express the normal-form constraints:

    x + 1 = 2^L * u
    v2 (3^L * u - 1) = L - 1

and expose the exact residue consequences modulo powers of two.

Do not approximate with logarithms.

# Stage G — saturated-chain audit

Add a finite audit dedicated only to consecutive saturated border blocks.

Record:

    maximum consecutive saturated length
    transition from one saturated block to the next
    residues of odd core u
    next block length
    next terminal valuation
    next block drift
    first repayment after a saturated run

Audit the existing exhaustive and random root sets.

The purpose is not to infer a universal constant. It is to discover the exact
successor grammar of the rigid exception.

# Stage H — saturated successor theorem

Using:

    TailGrammar
    DriftBudget
    mod-eight delayed reservoir
    canonical block normal form

seek the strongest exact theorem of one of these forms:

    saturated block -> next block has nonpositive drift

or:

    two consecutive saturated blocks -> following block repays both

or:

    a saturated run of length r forces terminal capacity >= r

or:

    saturated block transitions into a strictly smaller finite residue class.

Do not assert any form before the finite audit identifies the correct one.

# Stage I — open positive excursions

Define an open primitive positive excursion `q..m`:

    queue before q = 0
    queue is positive after every block q..m

with no future repayment assumption.

Prove that every positive queue position has a unique open-excursion start:
the block immediately after the last preceding queue zero.

Decompose every positive-drift block in its signature word using the
pressure-or-saturated dichotomy.

This permits analysis of an unreturned excursion without assuming the global
future-zero theorem.

# Stage J — pressure branch packaging

Define a block-local witness carrying:

    block index k
    dynamic pressure depth v_k
    positive block pressure at v_k

for the non-saturated branch.

Do not claim that different blocks use one fixed global depth.

Investigate how these dynamic-depth witnesses enter:

    PressureFrontier
    PressureAccounting
    PressureBeam
    delayed-reservoir budget

The target is an exact statement that a long positive excursion must produce
either:

    a pressure separator / obstruction

or:

    a long saturated run.

# Stage K — finite-signature interpretation

Record the precise meaning of the cp-317 diagnostics:

    drift collision:
      exact deterministic drift recovery fails

    nondeterministic successor:
      deterministic automaton fails but graph abstraction may remain possible

    realized positive repeated-signature segment:
      no bounded potential certificate can exist for that signature

Do not treat nondeterminism alone as refuting a sound over-approximation.

# Stage L — stopping rule

Stop at the first genuine obstruction among:

    the high-depth-to-continuation injection cannot be proved
    the pressure-or-saturated dichotomy fails
    saturated successor behavior has no stable exact rule
    dynamic-depth pressure witnesses cannot enter any existing separator API
    an open positive excursion can avoid both pressure obstruction and saturated
      rigidity in a concrete audited pattern

Do not return to queue algebra or generic carrier matching.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-318.md
```

うむ。

次の一手は「どの finite signature が正しいか」ではない。

> **正 drift を生む block は、pressure を生むか、完全飽和した一種類の例外になる。**

この二分を Lean に固定できれば、敵の逃げ道は本当に二本だけになるぞい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
index 2a4da15a..63c219c6 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
@@ -19,6 +19,9 @@ import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPressure
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentRepayment
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentDepthLedger
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentScalarQueue
+import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlockNormalForm
+import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPrimitiveExcursion
+import DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition
 
 #print "file: DkMath.Collatz.PetalBridge.FloatWindow"
 
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean
new file mode 100644
index 00000000..4aca983b
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean
@@ -0,0 +1,144 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPrimitiveExcursion
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition"
+
+namespace DkMath.Collatz
+
+/-!
+# Sound finite signed-transition certificates
+
+A finite projection is useful only after its edge weights are proved to bound
+the concrete transition.  This module records a potential certificate, a
+standard stronger form of the nonpositive-cycle condition.  It deliberately
+does not instantiate the certificate with the experimental low-bit block
+signatures: the cp-317 audit found drift collisions and nondeterministic
+successors in those projections.
+-/
+
+/--
+A sound finite signed abstraction equipped with a bounded potential.  Concrete
+edge weight is bounded by projected edge weight, and projected edge weight is
+bounded by the change in potential.
+-/
+structure FiniteSignedTransitionPotentialCertificate
+    (State Signature : Type*) [Fintype Signature] where
+  signature : State → Signature
+  actualWeight : State → State → ℤ
+  projectedUpperWeight : Signature → Signature → ℤ
+  potential : Signature → ℤ
+  bound : ℕ
+  actual_le_projected : ∀ a b,
+    actualWeight a b ≤ projectedUpperWeight (signature a) (signature b)
+  projected_le_potential_diff : ∀ s t,
+    projectedUpperWeight s t ≤ potential t - potential s
+  potential_nonneg : ∀ s, 0 ≤ potential s
+  potential_le_bound : ∀ s, potential s ≤ bound
+
+namespace FiniteSignedTransitionPotentialCertificate
+
+variable {State Signature : Type*} [Fintype Signature]
+
+/-- Concrete signed weight along `length` successive transitions from `start`. -/
+def pathWeight
+    (C : FiniteSignedTransitionPotentialCertificate State Signature)
+    (stateAt : ℕ → State) (start length : ℕ) : ℤ :=
+  ∑ i ∈ Finset.range length,
+    C.actualWeight (stateAt (start + i)) (stateAt (start + i + 1))
+
+/-- Projected upper weight along the same finite transition path. -/
+def projectedPathWeight
+    (C : FiniteSignedTransitionPotentialCertificate State Signature)
+    (stateAt : ℕ → State) (start length : ℕ) : ℤ :=
+  ∑ i ∈ Finset.range length,
+    C.projectedUpperWeight
+      (C.signature (stateAt (start + i)))
+      (C.signature (stateAt (start + i + 1)))
+
+/-- Sound edge projection bounds every concrete finite path. -/
+theorem pathWeight_le_projectedPathWeight
+    (C : FiniteSignedTransitionPotentialCertificate State Signature)
+    (stateAt : ℕ → State) (start length : ℕ) :
+    C.pathWeight stateAt start length ≤
+      C.projectedPathWeight stateAt start length := by
+  unfold pathWeight projectedPathWeight
+  exact Finset.sum_le_sum fun i _ => C.actual_le_projected _ _
+
+/-- Projected path weight telescopes below the endpoint potential difference. -/
+theorem projectedPathWeight_le_potential_sub
+    (C : FiniteSignedTransitionPotentialCertificate State Signature)
+    (stateAt : ℕ → State) (start length : ℕ) :
+    C.projectedPathWeight stateAt start length ≤
+      C.potential (C.signature (stateAt (start + length))) -
+        C.potential (C.signature (stateAt start)) := by
+  induction length with
+  | zero => simp [projectedPathWeight]
+  | succ length ih =>
+      rw [projectedPathWeight, Finset.sum_range_succ]
+      unfold projectedPathWeight at ih
+      change
+        (∑ i ∈ Finset.range length,
+          C.projectedUpperWeight
+            (C.signature (stateAt (start + i)))
+            (C.signature (stateAt (start + i + 1)))) +
+            C.projectedUpperWeight
+              (C.signature (stateAt (start + length)))
+              (C.signature (stateAt (start + length + 1))) ≤ _
+      have hedge := C.projected_le_potential_diff
+        (C.signature (stateAt (start + length)))
+        (C.signature (stateAt (start + length + 1)))
+      have hend : start + (length + 1) = start + length + 1 := by omega
+      rw [hend]
+      linarith
+
+/-- Every concrete path weight is uniformly bounded by the certificate bound. -/
+theorem pathWeight_le_bound
+    (C : FiniteSignedTransitionPotentialCertificate State Signature)
+    (stateAt : ℕ → State) (start length : ℕ) :
+    C.pathWeight stateAt start length ≤ C.bound := by
+  have hpath := (C.pathWeight_le_projectedPathWeight stateAt start length).trans
+    (C.projectedPathWeight_le_potential_sub stateAt start length)
+  have hnonneg := C.potential_nonneg (C.signature (stateAt start))
+  have hbound := C.potential_le_bound
+    (C.signature (stateAt (start + length)))
+  omega
+
+/-- A projected closed path has nonpositive upper weight. -/
+theorem projectedPathWeight_nonpos_of_signature_eq
+    (C : FiniteSignedTransitionPotentialCertificate State Signature)
+    (stateAt : ℕ → State) (start length : ℕ)
+    (hclosed : C.signature (stateAt (start + length)) =
+      C.signature (stateAt start)) :
+    C.projectedPathWeight stateAt start length ≤ 0 := by
+  have h := C.projectedPathWeight_le_potential_sub stateAt start length
+  rw [hclosed, sub_self] at h
+  exact h
+
+/-- Consequently a sound potential certificate excludes positive concrete cycles. -/
+theorem pathWeight_nonpos_of_signature_eq
+    (C : FiniteSignedTransitionPotentialCertificate State Signature)
+    (stateAt : ℕ → State) (start length : ℕ)
+    (hclosed : C.signature (stateAt (start + length)) =
+      C.signature (stateAt start)) :
+    C.pathWeight stateAt start length ≤ 0 :=
+  (C.pathWeight_le_projectedPathWeight stateAt start length).trans
+    (C.projectedPathWeight_nonpos_of_signature_eq stateAt start length hclosed)
+
+/-!
+The converse graph theorem, deriving such a bounded potential from only
+"every reachable directed cycle has nonpositive weight", requires a separate
+finite weighted-graph cycle-elimination argument.  More importantly for the
+canonical block application, no current finite signature has a proved
+`actual_le_projected` field.  The low-bit candidates fail even exact drift and
+successor determinism in the finite audit, so manufacturing that field would
+be unsound.
+-/
+
+end FiniteSignedTransitionPotentialCertificate
+
+end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlockNormalForm.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlockNormalForm.lean
new file mode 100644
index 00000000..0aebdb5e
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlockNormalForm.lean
@@ -0,0 +1,575 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentScalarQueue
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlockNormalForm"
+
+namespace DkMath.Collatz
+
+/-!
+# Exact arithmetic normal form of a canonical payment block
+
+This module exposes the arithmetic hidden by the source-fiber geometry.  A
+canonical block starts at an odd state `x` whose all-ones depth is its block
+length `L`.  Removing that exact power of two gives an odd core `u`.  The
+height-one interior then evolves by an exact affine recurrence, and the next
+block starts at the odd part of `3^L * u - 1`.
+
+No logarithmic or asymptotic approximation is used here.
+-/
+
+/-- Proof-independent orbit time at which canonical block `k` starts. -/
+noncomputable def canonicalBlockStartTime (n : OddNat) (k : ℕ) : ℕ :=
+  canonicalEndpointBlockStart n k
+
+/-- Odd state at the start of canonical block `k`. -/
+noncomputable def canonicalBlockStartState (n : OddNat) (k : ℕ) : ℕ :=
+  (iterateT (canonicalBlockStartTime n k) n).1
+
+/-- Length of canonical block `k`. -/
+noncomputable def canonicalBlockLength (n : OddNat) (k : ℕ) : ℕ :=
+  canonicalPaymentBlockLength n k
+
+/-- Odd core obtained by removing the exact block-length power of two. -/
+noncomputable def canonicalBlockOddCore (n : OddNat) (k : ℕ) : ℕ :=
+  (canonicalBlockStartState n k + 1) / 2 ^ canonicalBlockLength n k
+
+/-- State at the final source time of canonical block `k`. -/
+noncomputable def canonicalBlockEndpointState (n : OddNat) (k : ℕ) : ℕ :=
+  (iterateT (paymentEndpointSeq n k) n).1
+
+/-- State immediately after canonical block `k` has completed. -/
+noncomputable def canonicalBlockNextStartState (n : OddNat) (k : ℕ) : ℕ :=
+  (iterateT (paymentEndpointSeq n k + 1) n).1
+
+/-- Terminal arithmetic carrier whose odd part starts the next block. -/
+noncomputable def canonicalBlockTerminalCarrier (n : OddNat) (k : ℕ) : ℕ :=
+  3 ^ canonicalBlockLength n k * canonicalBlockOddCore n k - 1
+
+/-- Terminal 2-adic valuation removed at the endpoint transition. -/
+noncomputable def canonicalBlockTerminalValuation (n : OddNat) (k : ℕ) : ℕ :=
+  v2 (canonicalBlockTerminalCarrier n k)
+
+/-- Every canonical block contains at least its endpoint source. -/
+theorem one_le_canonicalBlockLength (n : OddNat) (k : ℕ) :
+    1 ≤ canonicalBlockLength n k := by
+  exact canonicalPaymentBlockLength_pos n k
+
+/-- The proof-independent start is the universal source-fiber minimum. -/
+theorem canonicalBlockStartTime_eq_universalPaymentBlockStart
+    (n : OddNat) (k : ℕ) :
+    canonicalBlockStartTime n k =
+      universalPaymentBlockStart n (paymentEndpointSeq n k)
+        (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k) := by
+  exact canonicalEndpointBlockStart_eq_universalPaymentBlockStart n k
+
+/-- The start time is no later than its canonical endpoint. -/
+theorem canonicalBlockStartTime_le_endpoint (n : OddNat) (k : ℕ) :
+    canonicalBlockStartTime n k ≤ paymentEndpointSeq n k := by
+  rw [canonicalBlockStartTime_eq_universalPaymentBlockStart]
+  exact (mem_orbitPaymentSourceFiberAt_iff.mp
+    (universalPaymentBlockStart_mem_sourceFiber n (paymentEndpointSeq n k)
+      (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k))).1
+
+/-- Block length is the exact all-ones depth of the start state. -/
+theorem canonicalBlockLength_eq_v2_startState_add_one
+    (n : OddNat) (k : ℕ) :
+    canonicalBlockLength n k = v2 (canonicalBlockStartState n k + 1) := by
+  unfold canonicalBlockLength canonicalBlockStartState canonicalBlockStartTime
+  rw [canonicalPaymentBlockLength_eq_sourceFiber_card]
+  rw [orbitPaymentSourceFiberAt_card_eq_orbitExactDepth_start n
+    (paymentEndpointSeq n k)
+    (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)]
+  simp [orbitExactDepth, ResidualAllOnesDepth, oddOrbitLabel,
+    canonicalEndpointBlockStart_eq_universalPaymentBlockStart]
+
+/-- The start word plus one is exactly `2^L` times the odd block core. -/
+theorem canonicalBlockStartState_add_one_eq_pow_mul_oddCore
+    (n : OddNat) (k : ℕ) :
+    canonicalBlockStartState n k + 1 =
+      2 ^ canonicalBlockLength n k * canonicalBlockOddCore n k := by
+  unfold canonicalBlockOddCore
+  rw [canonicalBlockLength_eq_v2_startState_add_one]
+  exact (Nat.mul_div_cancel' (by
+    simpa [v2] using
+      (pow_padicValNat_dvd
+        (p := 2) (n := canonicalBlockStartState n k + 1)))).symm
+
+/-- Removing the maximal two-power from a positive natural leaves an odd word. -/
+private theorem div_pow_v2_mod_two_eq_one {a : ℕ} (ha : 0 < a) :
+    (a / 2 ^ v2 a) % 2 = 1 := by
+  let u := a / 2 ^ v2 a
+  have hdvd : 2 ^ v2 a ∣ a := by
+    simpa [v2] using (pow_padicValNat_dvd (p := 2) (n := a))
+  have haeq : a = 2 ^ v2 a * u := by
+    simpa [u] using (Nat.mul_div_cancel' hdvd).symm
+  rcases Nat.mod_two_eq_zero_or_one u with hu | hu
+  · have htwo : 2 ∣ u := Nat.dvd_iff_mod_eq_zero.mpr hu
+    rcases htwo with ⟨w, huw⟩
+    have hsucc : 2 ^ (v2 a + 1) ∣ a := by
+      refine ⟨w, ?_⟩
+      calc
+        a = 2 ^ v2 a * u := haeq
+        _ = 2 ^ v2 a * (2 * w) := by rw [huw]
+        _ = 2 ^ (v2 a + 1) * w := by rw [pow_succ]; ring
+    have hnot : ¬ 2 ^ (v2 a + 1) ∣ a := by
+      simpa [v2] using (pow_succ_padicValNat_not_dvd ha.ne')
+    exact (hnot hsucc).elim
+  · exact hu
+
+/-- The canonical block core is odd. -/
+theorem canonicalBlockOddCore_mod_two_eq_one (n : OddNat) (k : ℕ) :
+    canonicalBlockOddCore n k % 2 = 1 := by
+  unfold canonicalBlockOddCore
+  rw [canonicalBlockLength_eq_v2_startState_add_one]
+  apply div_pow_v2_mod_two_eq_one
+  omega
+
+/-- The canonical block core is positive. -/
+theorem canonicalBlockOddCore_pos (n : OddNat) (k : ℕ) :
+    0 < canonicalBlockOddCore n k := by
+  have hodd := canonicalBlockOddCore_mod_two_eq_one n k
+  omega
+
+/-- One exact height-one orbit step in add-one coordinates. -/
+theorem two_mul_iterateT_succ_add_one_eq_three_mul_iterateT_add_one
+    (n : OddNat) (i : ℕ) (hheight : orbitWindowHeight n i = 1) :
+    2 * ((iterateT (i + 1) n).1 + 1) =
+      3 * ((iterateT i n).1 + 1) := by
+  have hs : s (iterateT i n) = 1 := by
+    simpa [orbitWindowHeight_eq_s_iterateT] using hheight
+  have hraw := threeNPlusOne_eq_pow_height_mul_T (iterateT i n)
+  rw [hs] at hraw
+  rw [iterateT_succ_eq_T_iterateT]
+  simp [threeNPlusOne] at hraw
+  omega
+
+/-- The canonical endpoint is `start + L - 1`. -/
+theorem canonicalBlockStartTime_add_length_sub_one_eq_endpoint
+    (n : OddNat) (k : ℕ) :
+    canonicalBlockStartTime n k + canonicalBlockLength n k - 1 =
+      paymentEndpointSeq n k := by
+  rw [canonicalBlockLength]
+  rw [canonicalPaymentBlockLength_eq_endpoint_sub_start_add_one]
+  rw [canonicalBlockStartTime_eq_universalPaymentBlockStart]
+  have hle := canonicalBlockStartTime_le_endpoint n k
+  rw [canonicalBlockStartTime_eq_universalPaymentBlockStart] at hle
+  omega
+
+/-- Exact multiplicative trajectory throughout a completed canonical block. -/
+theorem canonicalBlock_iterate_add_one_normal_form
+    (n : OddNat) (k t : ℕ) (ht : t < canonicalBlockLength n k) :
+    2 ^ t * ((iterateT (canonicalBlockStartTime n k + t) n).1 + 1) =
+      3 ^ t * (canonicalBlockStartState n k + 1) := by
+  induction t with
+  | zero => simp [canonicalBlockStartState]
+  | succ t ih =>
+      have htPrev : t < canonicalBlockLength n k := by omega
+      have htInterior : t < canonicalBlockLength n k - 1 := by omega
+      have hstartExact : OrbitDepthRecoversExactlyAt n
+          (canonicalBlockStartTime n k) (canonicalBlockLength n k) := by
+        simp [OrbitDepthRecoversExactlyAt, ResidualAllOnesDepth,
+          oddOrbitLabel, canonicalBlockLength_eq_v2_startState_add_one,
+          canonicalBlockStartState]
+      have hheight :=
+        (orbitDepthRecoversExactlyAt_prePayment_chain n
+          (canonicalBlockStartTime n k) (canonicalBlockLength n k)
+          (by omega) hstartExact).1 t htInterior |>.2
+      have hstep := two_mul_iterateT_succ_add_one_eq_three_mul_iterateT_add_one
+        n (canonicalBlockStartTime n k + t) hheight
+      rw [show canonicalBlockStartTime n k + (t + 1) =
+        (canonicalBlockStartTime n k + t) + 1 by omega]
+      rw [pow_succ, pow_succ]
+      calc
+        2 ^ t * 2 * ((iterateT ((canonicalBlockStartTime n k + t) + 1) n).1 + 1) =
+            2 ^ t *
+              (2 * ((iterateT ((canonicalBlockStartTime n k + t) + 1) n).1 + 1)) := by
+          ring
+        _ = 2 ^ t *
+              (3 * ((iterateT (canonicalBlockStartTime n k + t) n).1 + 1)) := by
+          rw [hstep]
+        _ = 3 *
+              (2 ^ t * ((iterateT (canonicalBlockStartTime n k + t) n).1 + 1)) := by
+          ring
+        _ = 3 * (3 ^ t * (canonicalBlockStartState n k + 1)) := by
+          rw [ih htPrev]
+        _ = 3 ^ t * 3 * (canonicalBlockStartState n k + 1) := by
+          ring
+
+/-- Division-free state formula in block-core coordinates. -/
+theorem canonicalBlock_iterate_add_one_eq_pow_mul_pow_mul_oddCore
+    (n : OddNat) (k t : ℕ) (ht : t < canonicalBlockLength n k) :
+    2 ^ t * ((iterateT (canonicalBlockStartTime n k + t) n).1 + 1) =
+      3 ^ t * (2 ^ canonicalBlockLength n k * canonicalBlockOddCore n k) := by
+  rw [canonicalBlock_iterate_add_one_normal_form n k t ht,
+    canonicalBlockStartState_add_one_eq_pow_mul_oddCore]
+
+/-- Exact endpoint state in canonical block-core coordinates. -/
+theorem canonicalBlockEndpointState_add_one_eq
+    (n : OddNat) (k : ℕ) :
+    canonicalBlockEndpointState n k + 1 =
+      2 * 3 ^ (canonicalBlockLength n k - 1) * canonicalBlockOddCore n k := by
+  have hL := one_le_canonicalBlockLength n k
+  have h := canonicalBlock_iterate_add_one_eq_pow_mul_pow_mul_oddCore
+    n k (canonicalBlockLength n k - 1) (by omega)
+  have hindex :
+      canonicalBlockStartTime n k + (canonicalBlockLength n k - 1) =
+        paymentEndpointSeq n k := by
+    have hend := canonicalBlockStartTime_add_length_sub_one_eq_endpoint n k
+    omega
+  rw [hindex] at h
+  unfold canonicalBlockEndpointState
+  have hpow : 2 ^ canonicalBlockLength n k =
+      2 ^ (canonicalBlockLength n k - 1) * 2 := by
+    conv_lhs => rw [show canonicalBlockLength n k =
+      (canonicalBlockLength n k - 1) + 1 by omega]
+    rw [pow_succ]
+  rw [hpow] at h
+  have htwoPos : 0 < 2 ^ (canonicalBlockLength n k - 1) := pow_pos (by omega) _
+  nlinarith
+
+/-- Raw endpoint transition before its terminal two-adic payment. -/
+theorem three_mul_canonicalBlockEndpointState_add_one_eq
+    (n : OddNat) (k : ℕ) :
+    3 * canonicalBlockEndpointState n k + 1 =
+      2 * canonicalBlockTerminalCarrier n k := by
+  unfold canonicalBlockTerminalCarrier
+  have hend := canonicalBlockEndpointState_add_one_eq n k
+  have hL := one_le_canonicalBlockLength n k
+  have hpow : 3 ^ canonicalBlockLength n k =
+      3 ^ (canonicalBlockLength n k - 1) * 3 := by
+    conv_lhs => rw [show canonicalBlockLength n k =
+      (canonicalBlockLength n k - 1) + 1 by omega]
+    rw [pow_succ]
+  rw [hpow]
+  have hu := canonicalBlockOddCore_pos n k
+  have hcarrier :
+      3 ^ (canonicalBlockLength n k - 1) * 3 * canonicalBlockOddCore n k =
+        3 * (3 ^ (canonicalBlockLength n k - 1) * canonicalBlockOddCore n k) := by
+    ring
+  rw [hcarrier]
+  have hend' : canonicalBlockEndpointState n k + 1 =
+      2 * (3 ^ (canonicalBlockLength n k - 1) * canonicalBlockOddCore n k) := by
+    simpa [mul_assoc] using hend
+  have hfactor : 0 <
+      3 ^ (canonicalBlockLength n k - 1) * canonicalBlockOddCore n k :=
+    Nat.mul_pos (pow_pos (by omega) _) hu
+  omega
+
+/-- The terminal carrier is positive. -/
+theorem canonicalBlockTerminalCarrier_pos (n : OddNat) (k : ℕ) :
+    0 < canonicalBlockTerminalCarrier n k := by
+  unfold canonicalBlockTerminalCarrier
+  have hL := one_le_canonicalBlockLength n k
+  have hu := canonicalBlockOddCore_pos n k
+  have hpow : 3 ≤ 3 ^ canonicalBlockLength n k := by
+    have hbase : 0 < (3 : ℕ) := by omega
+    exact Nat.pow_le_pow_right hbase hL
+  have hproduct : 3 ≤
+      3 ^ canonicalBlockLength n k * canonicalBlockOddCore n k := by
+    calc
+      3 ≤ 3 ^ canonicalBlockLength n k := hpow
+      _ = 3 ^ canonicalBlockLength n k * 1 := by simp
+      _ ≤ 3 ^ canonicalBlockLength n k * canonicalBlockOddCore n k :=
+        Nat.mul_le_mul_left _ hu
+  omega
+
+/-- The endpoint height is one plus the terminal carrier valuation. -/
+theorem canonicalBlock_endpointHeight_eq_terminalValuation_add_one
+    (n : OddNat) (k : ℕ) :
+    orbitWindowHeight n (paymentEndpointSeq n k) =
+      canonicalBlockTerminalValuation n k + 1 := by
+  rw [orbitWindowHeight_eq_s_iterateT]
+  unfold s canonicalBlockTerminalValuation
+  change v2 (threeNPlusOne (canonicalBlockEndpointState n k)) =
+    v2 (canonicalBlockTerminalCarrier n k) + 1
+  have hraw := three_mul_canonicalBlockEndpointState_add_one_eq n k
+  have hraw' : threeNPlusOne (canonicalBlockEndpointState n k) =
+      2 * canonicalBlockTerminalCarrier n k := by
+    simpa [threeNPlusOne] using hraw
+  rw [hraw']
+  have hv := (DkMath.ABC.padic_val_two_of_even
+    (canonicalBlockTerminalCarrier n k)).2
+      (canonicalBlockTerminalCarrier_pos n k).ne'
+  simpa [v2, Nat.add_comm] using hv
+
+/-- Canonical anonymous capacity is exactly the terminal 2-adic valuation. -/
+theorem canonicalBlockCapacityCount_eq_terminalValuation
+    (n : OddNat) (k : ℕ) :
+    canonicalBlockCapacityCount n k = canonicalBlockTerminalValuation n k := by
+  unfold canonicalBlockCapacityCount
+  rw [canonicalEndpointCapacitySlots_card]
+  unfold extraPaymentCapacityAt
+  rw [canonicalBlock_endpointHeight_eq_terminalValuation_add_one]
+  omega
+
+/-- The next canonical start is the odd part of the terminal carrier. -/
+theorem canonicalBlockNextStartState_eq_terminalCarrier_div_pow_valuation
+    (n : OddNat) (k : ℕ) :
+    canonicalBlockNextStartState n k =
+      canonicalBlockTerminalCarrier n k /
+        2 ^ canonicalBlockTerminalValuation n k := by
+  unfold canonicalBlockNextStartState
+  rw [iterateT_succ_eq_T_iterateT]
+  change threeNPlusOne (canonicalBlockEndpointState n k) /
+      2 ^ v2 (threeNPlusOne (canonicalBlockEndpointState n k)) =
+    canonicalBlockTerminalCarrier n k /
+      2 ^ canonicalBlockTerminalValuation n k
+  have hraw := three_mul_canonicalBlockEndpointState_add_one_eq n k
+  have hraw' : threeNPlusOne (canonicalBlockEndpointState n k) =
+      2 * canonicalBlockTerminalCarrier n k := by
+    simpa [threeNPlusOne] using hraw
+  rw [hraw']
+  have hv : v2 (2 * canonicalBlockTerminalCarrier n k) =
+      1 + v2 (canonicalBlockTerminalCarrier n k) := by
+    simpa [v2] using (DkMath.ABC.padic_val_two_of_even
+      (canonicalBlockTerminalCarrier n k)).2
+        (canonicalBlockTerminalCarrier_pos n k).ne'
+  rw [hv]
+  rw [pow_add]
+  unfold canonicalBlockTerminalValuation
+  change 2 * canonicalBlockTerminalCarrier n k /
+      (2 * 2 ^ v2 (canonicalBlockTerminalCarrier n k)) =
+    canonicalBlockTerminalCarrier n k /
+      2 ^ v2 (canonicalBlockTerminalCarrier n k)
+  exact Nat.mul_div_mul_left _ _ (by omega)
+
+/-! ## Exact block-drift consequences -/
+
+/-- Complete carry-two claims form a subfamily of the canonical block. -/
+theorem canonicalBlockClaimCount_le_length (n : OddNat) (k : ℕ) :
+    canonicalBlockClaimCount n k ≤ canonicalBlockLength n k := by
+  classical
+  unfold canonicalBlockClaimCount canonicalBlockLength
+  rw [canonicalPaymentBlockLength_eq_sourceFiber_card]
+  rw [carryTwoPaymentClaimFiberAt_eq_filter_universalPaymentBlock_carryTwo n
+    (paymentEndpointSeq n k)
+    (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)]
+  rw [orbitPaymentSourceFiberAt_eq_Icc_universalPaymentBlockStart n
+    (paymentEndpointSeq n k)
+    (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)]
+  exact Finset.card_filter_le _ _
+
+/-- Signed block drift is bounded by length minus endpoint capacity. -/
+theorem endpointAccountingTerm_le_length_sub_capacity
+    (n : OddNat) (k : ℕ) :
+    endpointAccountingTerm n k ≤
+      (canonicalBlockLength n k : ℤ) - canonicalBlockCapacityCount n k := by
+  rw [endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount]
+  exact sub_le_sub_right
+    (Int.ofNat_le.mpr (canonicalBlockClaimCount_le_length n k)) _
+
+/-- Positive block drift forces terminal service capacity below block length. -/
+theorem canonicalBlockCapacityCount_lt_length_of_endpointAccountingTerm_pos
+    {n : OddNat} {k : ℕ} (hpos : 0 < endpointAccountingTerm n k) :
+    canonicalBlockCapacityCount n k < canonicalBlockLength n k := by
+  have hle := endpointAccountingTerm_le_length_sub_capacity n k
+  omega
+
+/-- Normal-form reading: positive drift forces `v₂(3^L*u-1) < L`. -/
+theorem canonicalBlockTerminalValuation_lt_length_of_endpointAccountingTerm_pos
+    {n : OddNat} {k : ℕ} (hpos : 0 < endpointAccountingTerm n k) :
+    canonicalBlockTerminalValuation n k < canonicalBlockLength n k := by
+  rw [← canonicalBlockCapacityCount_eq_terminalValuation]
+  exact canonicalBlockCapacityCount_lt_length_of_endpointAccountingTerm_pos hpos
+
+/-- Positive canonical drift cannot occur without delayed interior debt. -/
+theorem canonicalBlockGrowthDebtFiber_nonempty_of_endpointAccountingTerm_pos
+    {n : OddNat} {k : ℕ} (hpos : 0 < endpointAccountingTerm n k) :
+    (floatGrowthDebtFiberAt n (paymentEndpointSeq n k)).Nonempty := by
+  apply floatGrowthDebtFiberAt_nonempty_of_universalPaymentBlockSignedDriftAt_pos
+    n (paymentEndpointSeq n k)
+      (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)
+  rwa [← endpointAccountingTerm_eq_universalPaymentBlockSignedDriftAt]
+
+/-! ## Exact in-block overshoot -/
+
+/-- Width is nondecreasing at every height-one interior step of a canonical block. -/
+theorem canonicalBlockInterior_bitWidth_le_succ
+    {n : OddNat} {k i : ℕ}
+    (hi : i ∈ Finset.Ico (canonicalBlockStartTime n k) (paymentEndpointSeq n k)) :
+    bitWidth (iterateT i n).1 ≤ bitWidth (iterateT (i + 1) n).1 := by
+  have hnonempty := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k
+  have hheight : orbitWindowHeight n i = 1 := by
+    apply orbitWindowHeight_eq_one_of_mem_universalPaymentBlockInterior
+    simpa [canonicalBlockStartTime_eq_universalPaymentBlockStart] using hi
+  have hs : s (iterateT i n) = 1 := by
+    simpa [orbitWindowHeight_eq_s_iterateT] using hheight
+  have hbalance := bitWidth_T_add_height_eq_bitWidth_add_upperCarry (iterateT i n)
+  have hpos : 0 < (iterateT i n).1 := by
+    have hodd := (iterateT i n).2
+    omega
+  have hcarry := stateUpperCarry_one_or_two hpos
+  rw [iterateT_succ_eq_T_iterateT]
+  omega
+
+/-- The endpoint-before-payment width is the maximum width attained inside the block. -/
+theorem canonicalBlock_bitWidth_le_endpoint
+    (n : OddNat) (k t : ℕ) (ht : t < canonicalBlockLength n k) :
+    bitWidth (iterateT (canonicalBlockStartTime n k + t) n).1 ≤
+      bitWidth (canonicalBlockEndpointState n k) := by
+  have hL := one_le_canonicalBlockLength n k
+  have htLast : t ≤ canonicalBlockLength n k - 1 := by omega
+  have hspan : ∀ d,
+      t + d ≤ canonicalBlockLength n k - 1 →
+        bitWidth (iterateT (canonicalBlockStartTime n k + t) n).1 ≤
+          bitWidth (iterateT (canonicalBlockStartTime n k + (t + d)) n).1 := by
+    intro d
+    induction d with
+    | zero => simp
+    | succ d ih =>
+        intro htd
+        have hprev := ih (by omega)
+        have hstep := canonicalBlockInterior_bitWidth_le_succ
+          (n := n) (k := k) (i := canonicalBlockStartTime n k + (t + d))
+          (Finset.mem_Ico.mpr ⟨by omega, by
+            have hend := canonicalBlockStartTime_add_length_sub_one_eq_endpoint n k
+            omega⟩)
+        rw [show canonicalBlockStartTime n k + (t + (d + 1)) =
+          (canonicalBlockStartTime n k + (t + d)) + 1 by omega]
+        exact hprev.trans hstep
+  have hlast := hspan (canonicalBlockLength n k - 1 - t) (by omega)
+  have hindex :
+      canonicalBlockStartTime n k +
+          (t + (canonicalBlockLength n k - 1 - t)) =
+        paymentEndpointSeq n k := by
+    have hend := canonicalBlockStartTime_add_length_sub_one_eq_endpoint n k
+    omega
+  rw [hindex] at hlast
+  exact hlast
+
+/-- Interior extra-height capacity is zero before the endpoint payment. -/
+theorem shiftedExtraPaymentCapacity_canonicalBlockInterior_eq_zero
+    (n : OddNat) (k : ℕ) :
+    shiftedExtraPaymentCapacity n (canonicalBlockStartTime n k)
+      (paymentEndpointSeq n k - canonicalBlockStartTime n k) = 0 := by
+  rw [shiftedExtraPaymentCapacity_eq_extraPaymentCapacityOn_Ico]
+  have hindex : canonicalBlockStartTime n k +
+      (paymentEndpointSeq n k - canonicalBlockStartTime n k) =
+        paymentEndpointSeq n k := by
+    exact Nat.add_sub_of_le (canonicalBlockStartTime_le_endpoint n k)
+  rw [hindex]
+  unfold extraPaymentCapacityOn
+  apply Finset.sum_eq_zero
+  intro i hi
+  have hheight := orbitWindowHeight_eq_one_of_mem_universalPaymentBlockInterior
+    (n := n) (j := paymentEndpointSeq n k)
+    (h := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)
+    (by simpa [canonicalBlockStartTime_eq_universalPaymentBlockStart] using hi)
+  rw [hheight]
+  rfl
+
+/-- Interior carry-two count is exactly the delayed-debt cardinality. -/
+theorem shiftedOrbitCarryTwoCount_canonicalBlockInterior_eq_growthDebt_card
+    (n : OddNat) (k : ℕ) :
+    shiftedOrbitCarryTwoCount n (canonicalBlockStartTime n k)
+      (paymentEndpointSeq n k - canonicalBlockStartTime n k) =
+        (floatGrowthDebtFiberAt n (paymentEndpointSeq n k)).card := by
+  have hindex : canonicalBlockStartTime n k +
+      (paymentEndpointSeq n k - canonicalBlockStartTime n k) =
+        paymentEndpointSeq n k := by
+    exact Nat.add_sub_of_le (canonicalBlockStartTime_le_endpoint n k)
+  calc
+    shiftedOrbitCarryTwoCount n (canonicalBlockStartTime n k)
+        (paymentEndpointSeq n k - canonicalBlockStartTime n k) =
+        (shiftedCarryTwoOffsets n (canonicalBlockStartTime n k)
+          (paymentEndpointSeq n k - canonicalBlockStartTime n k)).card :=
+      shiftedOrbitCarryTwoCount_eq_offset_card _ _ _
+    _ = (carryTwoPositions n (Finset.Ico (canonicalBlockStartTime n k)
+          (canonicalBlockStartTime n k +
+            (paymentEndpointSeq n k - canonicalBlockStartTime n k)))).card :=
+      shiftedCarryTwoOffsets_card_eq_carryTwoPositions_Ico_card _ _ _
+    _ = (carryTwoPositions n (Finset.Ico (canonicalBlockStartTime n k)
+          (paymentEndpointSeq n k))).card := by rw [hindex]
+    _ = (floatGrowthDebtFiberAt n (paymentEndpointSeq n k)).card := by
+      congr 1
+      ext i
+      rw [mem_carryTwoPositions_iff,
+        mem_floatGrowthDebtFiberAt_iff_mem_universalPaymentBlockInterior_and_carryTwo
+          (h := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)]
+      simp [canonicalBlockStartTime_eq_universalPaymentBlockStart]
+
+/-- Exact in-block burst: endpoint width gain equals delayed interior claims. -/
+theorem canonicalBlockEndpoint_bitWidth_eq_start_add_growthDebt_card
+    (n : OddNat) (k : ℕ) :
+    bitWidth (canonicalBlockEndpointState n k) =
+      bitWidth (canonicalBlockStartState n k) +
+        (floatGrowthDebtFiberAt n (paymentEndpointSeq n k)).card := by
+  have hledger := bitWidth_iterateT_add_shiftedExtraPaymentCapacity_eq_shiftedCarryTwo
+    n (canonicalBlockStartTime n k)
+      (paymentEndpointSeq n k - canonicalBlockStartTime n k)
+  have hindex : canonicalBlockStartTime n k +
+      (paymentEndpointSeq n k - canonicalBlockStartTime n k) =
+        paymentEndpointSeq n k := by
+    exact Nat.add_sub_of_le (canonicalBlockStartTime_le_endpoint n k)
+  rw [hindex,
+    shiftedExtraPaymentCapacity_canonicalBlockInterior_eq_zero,
+    shiftedOrbitCarryTwoCount_canonicalBlockInterior_eq_growthDebt_card] at hledger
+  simpa [canonicalBlockEndpointState, canonicalBlockStartState] using hledger
+
+/-- Subtractive form of the exact in-block burst identity. -/
+theorem canonicalBlockEndpoint_bitWidth_sub_start_eq_growthDebt_card
+    (n : OddNat) (k : ℕ) :
+    bitWidth (canonicalBlockEndpointState n k) -
+        bitWidth (canonicalBlockStartState n k) =
+      (floatGrowthDebtFiberAt n (paymentEndpointSeq n k)).card := by
+  rw [canonicalBlockEndpoint_bitWidth_eq_start_add_growthDebt_card]
+  omega
+
+/-- Uniform ceiling on the delayed-debt burst produced inside each canonical block. -/
+def CanonicalBlockBurstUniformUpperBound (n : OddNat) (D : ℕ) : Prop :=
+  ∀ k, (floatGrowthDebtFiberAt n (paymentEndpointSeq n k)).card ≤ D
+
+/-- A queue ceiling controls every canonical block-start width. -/
+theorem canonicalBlockStart_bitWidth_le_of_queueUniformUpperBound
+    {n : OddNat} {C : ℕ}
+    (hqueue : CanonicalOutstandingClaimQueueUniformUpperBound n C) (k : ℕ) :
+    bitWidth (canonicalBlockStartState n k) ≤ bitWidth n.1 + C := by
+  cases k with
+  | zero =>
+      unfold canonicalBlockStartState canonicalBlockStartTime
+      simp [canonicalEndpointBlockStart, iterateT]
+  | succ k =>
+      have hendpoint :=
+        hqueue.to_endpointWidthUniformUpperBound k
+      unfold canonicalBlockStartState canonicalBlockStartTime
+      simpa [canonicalEndpointBlockStart, canonicalEndpointWidth] using hendpoint
+
+/-- Queue drawup plus in-block burst bounds every state inside a canonical block. -/
+theorem canonicalBlock_bitWidth_le_of_queue_and_burst_bounds
+    {n : OddNat} {C D k t : ℕ}
+    (hqueue : CanonicalOutstandingClaimQueueUniformUpperBound n C)
+    (hburst : CanonicalBlockBurstUniformUpperBound n D)
+    (ht : t < canonicalBlockLength n k) :
+    bitWidth (iterateT (canonicalBlockStartTime n k + t) n).1 ≤
+      bitWidth n.1 + C + D := by
+  have hmax := canonicalBlock_bitWidth_le_endpoint n k t ht
+  have hend := canonicalBlockEndpoint_bitWidth_eq_start_add_growthDebt_card n k
+  have hstart := canonicalBlockStart_bitWidth_le_of_queueUniformUpperBound hqueue k
+  have hdebt := hburst k
+  omega
+
+/-!
+This is the precise two-coordinate conditional bound available at this layer.
+It ranges over every state *inside a named canonical block*.  Promoting it to
+an unqualified all-time orbit theorem requires a separate coverage theorem
+showing that the canonical block family covers every natural orbit index; that
+coverage statement is intentionally not smuggled into the burst argument.
+-/
+
+/-!
+The completed arithmetic transition is therefore exact:
+
+`(L, u) ↦ oddPart (3^L * u - 1)`.
+
+The terminal valuation is not an auxiliary estimate.  It is definitionally
+the endpoint service capacity after the preceding theorem, so later drift
+arguments can compare `L` and this valuation without translating between two
+independent coordinate systems.
+-/
+
+end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentPrimitiveExcursion.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentPrimitiveExcursion.lean
new file mode 100644
index 00000000..777b48d5
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentPrimitiveExcursion.lean
@@ -0,0 +1,237 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlockNormalForm
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPrimitiveExcursion"
+
+namespace DkMath.Collatz
+
+/-!
+# Primitive positive excursions of the canonical scalar queue
+
+This module packages a *finite, repaid* positive excursion.  It does not assume
+or assert that every positive queue position has a future zero.  That future
+repayment statement is the global obstruction left after the finite accounting
+and block-normal-form layers.
+-/
+
+/-- Queue value immediately before canonical block `q` is processed. -/
+noncomputable def canonicalOutstandingClaimQueueBefore
+    (n : OddNat) : ℕ → ℕ
+  | 0 => 0
+  | q + 1 => canonicalOutstandingClaimQueue n q
+
+/--
+A primitive positive excursion starts from an empty queue, stays positive after
+every proper block, and is first empty again after block `r`.
+-/
+def CanonicalPrimitivePositiveQueueExcursion
+    (n : OddNat) (q r : ℕ) : Prop :=
+  q < r ∧
+    canonicalOutstandingClaimQueueBefore n q = 0 ∧
+      (∀ m ∈ Finset.Ico q r, 0 < canonicalOutstandingClaimQueue n m) ∧
+        canonicalOutstandingClaimQueue n r = 0
+
+/-- Signed partial-sum presentation of a primitive positive excursion. -/
+def CanonicalPrimitivePositiveDriftExcursion
+    (n : OddNat) (q r : ℕ) : Prop :=
+  q < r ∧
+    canonicalOutstandingClaimQueueBefore n q = 0 ∧
+      (∀ m ∈ Finset.Ico q r, 0 < canonicalWindowDriftInt n q m) ∧
+        canonicalWindowDriftInt n q r ≤ 0
+
+/-- Number of canonical blocks in the closed excursion interval `q..r`. -/
+def canonicalPrimitiveQueueExcursionLength (q r : ℕ) : ℕ :=
+  r - q + 1
+
+/-- Maximum queue height attained on the closed excursion interval. -/
+noncomputable def canonicalPrimitiveQueueExcursionMaximum
+    (n : OddNat) (q r : ℕ) : ℕ :=
+  (Finset.Icc q r).sup (canonicalOutstandingClaimQueue n)
+
+/-- Exact signed block word carried by the closed excursion interval. -/
+noncomputable def canonicalPrimitiveQueueExcursionSignature
+    (n : OddNat) (q r : ℕ) : List ℤ :=
+  List.ofFn fun i : Fin (canonicalPrimitiveQueueExcursionLength q r) =>
+    endpointAccountingTerm n (q + i.1)
+
+/-- Orbit time of the endpoint that performs the primitive excursion's first repayment. -/
+noncomputable def canonicalPrimitiveQueueExcursionFirstRepaymentEndpoint
+    (n : OddNat) (r : ℕ) : ℕ :=
+  paymentEndpointSeq n r
+
+/-- The queue-before coordinate unfolds to the preceding queue at positive indices. -/
+theorem canonicalOutstandingClaimQueueBefore_succ (n : OddNat) (q : ℕ) :
+    canonicalOutstandingClaimQueueBefore n (q + 1) =
+      canonicalOutstandingClaimQueue n q := rfl
+
+/-- Starting empty makes the first block queue the positive part of its own drift. -/
+private theorem queue_eq_intToNat_windowDrift_self_of_before_eq_zero
+    {n : OddNat} {q : ℕ}
+    (hbefore : canonicalOutstandingClaimQueueBefore n q = 0) :
+    canonicalOutstandingClaimQueue n q =
+      Int.toNat (canonicalWindowDriftInt n q q) := by
+  cases q with
+  | zero =>
+      rw [canonicalOutstandingClaimQueue_zero_eq_intToNat,
+        canonicalWindowDriftInt_self]
+  | succ q =>
+      rw [canonicalOutstandingClaimQueueBefore_succ] at hbefore
+      rw [canonicalOutstandingClaimQueue_succ_eq_intToNat, hbefore,
+        canonicalWindowDriftInt_self]
+      simp
+
+/--
+While every preceding partial queue is positive, reflection is inactive and
+the queue equals the ordinary signed partial sum from the excursion start.
+-/
+private theorem queue_eq_intToNat_windowDrift_of_positive_prefix
+    {n : OddNat} {q m : ℕ} (hqm : q ≤ m)
+    (hbefore : canonicalOutstandingClaimQueueBefore n q = 0)
+    (hpositive : ∀ t ∈ Finset.Ico q m,
+      0 < canonicalOutstandingClaimQueue n t) :
+    canonicalOutstandingClaimQueue n m =
+      Int.toNat (canonicalWindowDriftInt n q m) := by
+  induction m, hqm using Nat.le_induction with
+  | base => exact queue_eq_intToNat_windowDrift_self_of_before_eq_zero hbefore
+  | succ m hqm ih =>
+      rw [canonicalOutstandingClaimQueue_succ_eq_intToNat]
+      rw [canonicalWindowDriftInt_succ n (by omega), if_pos hqm]
+      have hmPos : 0 < canonicalOutstandingClaimQueue n m :=
+        hpositive m (Finset.mem_Ico.mpr ⟨hqm, by omega⟩)
+      have hsumPos : 0 < canonicalWindowDriftInt n q m := by
+        have hEq := ih (fun t ht => hpositive t (by
+          exact Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp ht).1,
+            (Finset.mem_Ico.mp ht).2.trans_le (by omega)⟩))
+        have hnonneg : 0 ≤ canonicalWindowDriftInt n q m := by
+          by_contra hneg
+          have : Int.toNat (canonicalWindowDriftInt n q m) = 0 :=
+            Int.toNat_of_nonpos (by omega)
+          omega
+        omega
+      have hcast : (Int.toNat (canonicalWindowDriftInt n q m) : ℤ) =
+          canonicalWindowDriftInt n q m := by
+        rw [Int.ofNat_toNat, max_eq_left (le_of_lt hsumPos)]
+      rw [ih (fun t ht => hpositive t (by
+        exact Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp ht).1,
+          (Finset.mem_Ico.mp ht).2.trans_le (by omega)⟩)), hcast]
+
+/-- Positive signed proper prefixes likewise keep reflection inactive. -/
+private theorem queue_eq_intToNat_windowDrift_of_positive_drift_prefix
+    {n : OddNat} {q m : ℕ} (hqm : q ≤ m)
+    (hbefore : canonicalOutstandingClaimQueueBefore n q = 0)
+    (hpositive : ∀ t ∈ Finset.Ico q m,
+      0 < canonicalWindowDriftInt n q t) :
+    canonicalOutstandingClaimQueue n m =
+      Int.toNat (canonicalWindowDriftInt n q m) := by
+  induction m, hqm using Nat.le_induction with
+  | base => exact queue_eq_intToNat_windowDrift_self_of_before_eq_zero hbefore
+  | succ m hqm ih =>
+      have hprefix : ∀ t ∈ Finset.Ico q m,
+          0 < canonicalWindowDriftInt n q t := by
+        intro t ht
+        exact hpositive t (Finset.mem_Ico.mpr
+          ⟨(Finset.mem_Ico.mp ht).1, (Finset.mem_Ico.mp ht).2.trans (by omega)⟩)
+      have hmPos : 0 < canonicalWindowDriftInt n q m :=
+        hpositive m (Finset.mem_Ico.mpr ⟨hqm, by omega⟩)
+      have hcast : (Int.toNat (canonicalWindowDriftInt n q m) : ℤ) =
+          canonicalWindowDriftInt n q m := by
+        rw [Int.ofNat_toNat, max_eq_left (le_of_lt hmPos)]
+      rw [canonicalOutstandingClaimQueue_succ_eq_intToNat,
+        canonicalWindowDriftInt_succ n (by omega), if_pos hqm,
+        ih hprefix, hcast]
+
+/-- Queue and signed-partial-sum presentations of a repaid primitive excursion agree. -/
+theorem canonicalPrimitivePositiveQueueExcursion_iff_driftExcursion
+    (n : OddNat) (q r : ℕ) :
+    CanonicalPrimitivePositiveQueueExcursion n q r ↔
+      CanonicalPrimitivePositiveDriftExcursion n q r := by
+  constructor
+  · rintro ⟨hqr, hbefore, hpositive, hzero⟩
+    refine ⟨hqr, hbefore, ?_, ?_⟩
+    · intro m hm
+      rcases Finset.mem_Ico.mp hm with ⟨hqm, hmr⟩
+      have hEq := queue_eq_intToNat_windowDrift_of_positive_prefix
+        (n := n) (q := q) (m := m) hqm hbefore (fun t ht =>
+          hpositive t (Finset.mem_Ico.mpr
+            ⟨(Finset.mem_Ico.mp ht).1, (Finset.mem_Ico.mp ht).2.trans hmr⟩))
+      have hmPos := hpositive m (Finset.mem_Ico.mpr ⟨hqm, hmr⟩)
+      have hself := Int.self_le_toNat (canonicalWindowDriftInt n q m)
+      omega
+    · have hEq := queue_eq_intToNat_windowDrift_of_positive_prefix
+        (n := n) (q := q) (m := r) (by omega) hbefore hpositive
+      rw [hzero] at hEq
+      exact Int.toNat_eq_zero.mp hEq.symm
+  · rintro ⟨hqr, hbefore, hpositive, htotal⟩
+    refine ⟨hqr, hbefore, ?_, ?_⟩
+    · intro m hm
+      rcases Finset.mem_Ico.mp hm with ⟨hqm, hmr⟩
+      have hEq := queue_eq_intToNat_windowDrift_of_positive_drift_prefix
+        (n := n) (q := q) (m := m) hqm hbefore (fun t ht =>
+          hpositive t (Finset.mem_Ico.mpr
+            ⟨(Finset.mem_Ico.mp ht).1, (Finset.mem_Ico.mp ht).2.trans hmr⟩))
+      rw [hEq]
+      have hself := Int.self_le_toNat (canonicalWindowDriftInt n q m)
+      have hsum := hpositive m (Finset.mem_Ico.mpr ⟨hqm, hmr⟩)
+      omega
+    · have hEq := queue_eq_intToNat_windowDrift_of_positive_drift_prefix
+        (n := n) (q := q) (m := r) (Nat.le_of_lt hqr) hbefore hpositive
+      rw [hEq, Int.toNat_of_nonpos htotal]
+
+/-- The signature contains exactly one entry for each block in the closed interval. -/
+theorem canonicalPrimitiveQueueExcursionSignature_length
+    (n : OddNat) (q r : ℕ) :
+    (canonicalPrimitiveQueueExcursionSignature n q r).length =
+      canonicalPrimitiveQueueExcursionLength q r := by
+  simp [canonicalPrimitiveQueueExcursionSignature]
+
+/-- The maximum surface dominates every queue value in its excursion interval. -/
+theorem canonicalOutstandingClaimQueue_le_primitiveExcursionMaximum
+    (n : OddNat) {q r m : ℕ} (hm : m ∈ Finset.Icc q r) :
+    canonicalOutstandingClaimQueue n m ≤
+      canonicalPrimitiveQueueExcursionMaximum n q r := by
+  unfold canonicalPrimitiveQueueExcursionMaximum
+  exact Finset.le_sup (f := canonicalOutstandingClaimQueue n) hm
+
+/-- A primitive excursion's stated endpoint is its first zero after its positive run. -/
+theorem CanonicalPrimitivePositiveQueueExcursion.first_repayment
+    {n : OddNat} {q r : ℕ}
+    (h : CanonicalPrimitivePositiveQueueExcursion n q r) :
+    canonicalOutstandingClaimQueue n r = 0 ∧
+      ∀ m ∈ Finset.Ico q r, canonicalOutstandingClaimQueue n m ≠ 0 := by
+  exact ⟨h.2.2.2, fun m hm => (h.2.2.1 m hm).ne'⟩
+
+/-- A primitive excursion has a uniquely determined repayment block for its start. -/
+theorem canonicalPrimitivePositiveQueueExcursion_right_unique
+    {n : OddNat} {q r r' : ℕ}
+    (h : CanonicalPrimitivePositiveQueueExcursion n q r)
+    (h' : CanonicalPrimitivePositiveQueueExcursion n q r') :
+    r = r' := by
+  by_contra hne
+  rcases lt_or_gt_of_ne hne with hlt | hgt
+  · exact (h'.2.2.1 r (Finset.mem_Ico.mpr ⟨Nat.le_of_lt h.1, hlt⟩)).ne'
+      h.2.2.2
+  · exact (h.2.2.1 r' (Finset.mem_Ico.mpr ⟨Nat.le_of_lt h'.1, hgt⟩)).ne'
+      h'.2.2.2
+
+/-!
+## Exact remaining obstruction
+
+For a fixed start `q`, the preceding theorem makes a finite repayment endpoint
+unique.  Existence is different: proving that every positive queue position is
+contained in such an interval requires a future block `r` with queue zero.
+Neither the reflected-walk identities nor the exact transition
+
+`(L, u) ↦ oddPart (3^L * u - 1)`
+
+currently supplies that future zero.  Consequently no unconditional
+"every positive position belongs to a unique maximal finite excursion" theorem
+is exported here.  Adding it without a repayment hypothesis would merely hide
+the remaining global problem in a definition.
+-/
+
+end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentScalarQueue.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentScalarQueue.lean
index 171f65af..007a0541 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentScalarQueue.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentScalarQueue.lean
@@ -346,6 +346,130 @@ theorem canonicalOutstandingClaimQueue_eq_balance_sub_runningMinimum
         congr 1
         ring
 
+/-! ## Endpoint-width drawup form -/
+
+/-- Width immediately after canonical endpoint block `m`. -/
+noncomputable def canonicalEndpointWidth (n : OddNat) (m : ℕ) : ℕ :=
+  bitWidth (iterateT (paymentEndpointSeq n m + 1) n).1
+
+/-- Running minimum of the initial width and all completed endpoint widths. -/
+noncomputable def canonicalEndpointRunningWidthMinimum
+    (n : OddNat) : ℕ → ℕ
+  | 0 => min (bitWidth n.1) (canonicalEndpointWidth n 0)
+  | m + 1 => min (canonicalEndpointRunningWidthMinimum n m)
+      (canonicalEndpointWidth n (m + 1))
+
+/-- The running width minimum is no larger than the current endpoint width. -/
+theorem canonicalEndpointRunningWidthMinimum_le_width
+    (n : OddNat) (m : ℕ) :
+    canonicalEndpointRunningWidthMinimum n m ≤ canonicalEndpointWidth n m := by
+  cases m with
+  | zero => exact min_le_right _ _
+  | succ m =>
+      rw [canonicalEndpointRunningWidthMinimum]
+      exact min_le_right _ _
+
+/-- The initial width remains a candidate in every running width minimum. -/
+theorem canonicalEndpointRunningWidthMinimum_le_initial
+    (n : OddNat) (m : ℕ) :
+    canonicalEndpointRunningWidthMinimum n m ≤ bitWidth n.1 := by
+  induction m with
+  | zero => exact min_le_left _ _
+  | succ m ih =>
+      rw [canonicalEndpointRunningWidthMinimum]
+      exact (min_le_left _ _).trans ih
+
+/-- Every positive word has at least one binary digit. -/
+theorem one_le_bitWidth_of_pos {x : ℕ} (hx : 0 < x) :
+    1 ≤ bitWidth x := by
+  rw [bitWidth_eq_log_two_add_one hx.ne']
+  omega
+
+/-- Every canonical endpoint width is positive. -/
+theorem one_le_canonicalEndpointWidth (n : OddNat) (m : ℕ) :
+    1 ≤ canonicalEndpointWidth n m := by
+  unfold canonicalEndpointWidth
+  apply one_le_bitWidth_of_pos
+  have hodd := (iterateT (paymentEndpointSeq n m + 1) n).2
+  omega
+
+/-- The running width minimum remains positive. -/
+theorem one_le_canonicalEndpointRunningWidthMinimum
+    (n : OddNat) (m : ℕ) :
+    1 ≤ canonicalEndpointRunningWidthMinimum n m := by
+  induction m with
+  | zero =>
+      rw [canonicalEndpointRunningWidthMinimum]
+      apply le_min
+      · apply one_le_bitWidth_of_pos
+        have hodd := n.2
+        omega
+      · exact one_le_canonicalEndpointWidth n 0
+  | succ m ih =>
+      rw [canonicalEndpointRunningWidthMinimum]
+      exact le_min ih (one_le_canonicalEndpointWidth n (m + 1))
+
+/-- The signed running minimum is the width minimum translated by the initial width. -/
+theorem canonicalEndpointRunningBalanceMinimum_eq_widthMinimum_sub_initial
+    (n : OddNat) (m : ℕ) :
+    canonicalEndpointRunningBalanceMinimum n m =
+      (canonicalEndpointRunningWidthMinimum n m : ℤ) - bitWidth n.1 := by
+  induction m with
+  | zero =>
+      rw [canonicalEndpointRunningBalanceMinimum,
+        canonicalEndpointRunningWidthMinimum,
+        canonicalEndpointBalanceInt_eq_bitWidth_sub]
+      change min 0 ((canonicalEndpointWidth n 0 : ℤ) - bitWidth n.1) = _
+      push_cast
+      omega
+  | succ m ih =>
+      rw [canonicalEndpointRunningBalanceMinimum,
+        canonicalEndpointRunningWidthMinimum,
+        canonicalEndpointBalanceInt_eq_bitWidth_sub, ih]
+      change min
+        ((canonicalEndpointRunningWidthMinimum n m : ℤ) - bitWidth n.1)
+        ((canonicalEndpointWidth n (m + 1) : ℤ) - bitWidth n.1) = _
+      push_cast
+      omega
+
+/--
+The scalar queue is exactly endpoint-width drawup above the historical minimum
+that also includes the initial width.
+-/
+theorem canonicalOutstandingClaimQueue_eq_width_sub_runningWidthMinimum
+    (n : OddNat) (m : ℕ) :
+    canonicalOutstandingClaimQueue n m =
+      canonicalEndpointWidth n m - canonicalEndpointRunningWidthMinimum n m := by
+  rw [canonicalOutstandingClaimQueue_eq_balance_sub_runningMinimum,
+    canonicalEndpointBalanceInt_eq_bitWidth_sub,
+    canonicalEndpointRunningBalanceMinimum_eq_widthMinimum_sub_initial]
+  change Int.toNat
+      (((canonicalEndpointWidth n m : ℤ) - bitWidth n.1) -
+        ((canonicalEndpointRunningWidthMinimum n m : ℤ) - bitWidth n.1)) = _
+  have hle := canonicalEndpointRunningWidthMinimum_le_width n m
+  omega
+
+/-- Queue zero means that the current endpoint width attains the running minimum. -/
+theorem canonicalOutstandingClaimQueue_eq_zero_iff_width_eq_runningWidthMinimum
+    (n : OddNat) (m : ℕ) :
+    canonicalOutstandingClaimQueue n m = 0 ↔
+      canonicalEndpointWidth n m = canonicalEndpointRunningWidthMinimum n m := by
+  rw [canonicalOutstandingClaimQueue_eq_width_sub_runningWidthMinimum]
+  have hle := canonicalEndpointRunningWidthMinimum_le_width n m
+  omega
+
+/-- A completed endpoint whose next state is one structurally has zero queue. -/
+theorem canonicalOutstandingClaimQueue_eq_zero_of_endpointState_eq_one
+    {n : OddNat} {m : ℕ}
+    (hstate : (iterateT (paymentEndpointSeq n m + 1) n).1 = 1) :
+    canonicalOutstandingClaimQueue n m = 0 := by
+  apply (canonicalOutstandingClaimQueue_eq_zero_iff_width_eq_runningWidthMinimum
+    n m).2
+  have hminPos := one_le_canonicalEndpointRunningWidthMinimum n m
+  have hminLe := canonicalEndpointRunningWidthMinimum_le_width n m
+  simp [canonicalEndpointWidth, hstate, bitWidth] at hminLe ⊢
+  omega
+
 /-- Queue zero means that every suffix ending at `m` has nonpositive drift. -/
 theorem canonicalOutstandingClaimQueue_eq_zero_iff_all_windowDrift_nonpos
     (n : OddNat) (m : ℕ) :
@@ -840,6 +964,64 @@ def CanonicalOutstandingClaimQueueUniformUpperBound
     (n : OddNat) (C : ℕ) : Prop :=
   ∀ m, canonicalOutstandingClaimQueue n m ≤ C
 
+/-- Uniform boundedness of completed canonical endpoint widths. -/
+def CanonicalEndpointWidthUniformUpperBound
+    (n : OddNat) (B : ℕ) : Prop :=
+  ∀ m, canonicalEndpointWidth n m ≤ B
+
+/-- A queue ceiling gives the translated endpoint-width ceiling. -/
+theorem CanonicalOutstandingClaimQueueUniformUpperBound.to_endpointWidthUniformUpperBound
+    {n : OddNat} {C : ℕ}
+    (h : CanonicalOutstandingClaimQueueUniformUpperBound n C) :
+    CanonicalEndpointWidthUniformUpperBound n (bitWidth n.1 + C) := by
+  intro m
+  have hqueue := h m
+  have hdrawup := canonicalOutstandingClaimQueue_eq_width_sub_runningWidthMinimum n m
+  have hminLeWidth := canonicalEndpointRunningWidthMinimum_le_width n m
+  have hminLeInitial := canonicalEndpointRunningWidthMinimum_le_initial n m
+  omega
+
+/-- Any endpoint-width ceiling also bounds endpoint drawup and hence the queue. -/
+theorem CanonicalEndpointWidthUniformUpperBound.to_outstandingClaimQueueUniformUpperBound
+    {n : OddNat} {B : ℕ}
+    (h : CanonicalEndpointWidthUniformUpperBound n B) :
+    CanonicalOutstandingClaimQueueUniformUpperBound n B := by
+  intro m
+  rw [canonicalOutstandingClaimQueue_eq_width_sub_runningWidthMinimum]
+  exact (Nat.sub_le _ _).trans (h m)
+
+/-- Queue boundedness and canonical endpoint-width boundedness are existentially equivalent. -/
+theorem exists_outstandingClaimQueueUniformUpperBound_iff_exists_endpointWidthUniformUpperBound
+    (n : OddNat) :
+    (∃ C, CanonicalOutstandingClaimQueueUniformUpperBound n C) ↔
+      ∃ B, CanonicalEndpointWidthUniformUpperBound n B := by
+  constructor
+  · rintro ⟨C, hC⟩
+    exact ⟨bitWidth n.1 + C, hC.to_endpointWidthUniformUpperBound⟩
+  · rintro ⟨B, hB⟩
+    exact ⟨B, hB.to_outstandingClaimQueueUniformUpperBound⟩
+
+/-!
+## Experimental initial-boundary target
+
+The following predicate deliberately names, but does not prove, the cp-317
+candidate observed by finite computation.  Keeping the candidate behind a
+`Prop` prevents the numerical audit from being mistaken for a theorem while
+still allowing its exact mathematical consequence to be used conditionally.
+-/
+
+/-- Experimental target: endpoint drawup never exceeds the root's initial width. -/
+def CanonicalOutstandingClaimQueueLeInitialWidth (n : OddNat) : Prop :=
+  ∀ m, canonicalOutstandingClaimQueue n m ≤ bitWidth n.1
+
+/-- The experimental queue target would bound endpoint width by twice the initial width. -/
+theorem CanonicalOutstandingClaimQueueLeInitialWidth.endpointWidth_le_two_mul_initial
+    {n : OddNat} (h : CanonicalOutstandingClaimQueueLeInitialWidth n) (m : ℕ) :
+    canonicalEndpointWidth n m ≤ 2 * bitWidth n.1 := by
+  have hbound : CanonicalOutstandingClaimQueueUniformUpperBound n (bitWidth n.1) := h
+  have hend := hbound.to_endpointWidthUniformUpperBound m
+  omega
+
 /--
 Uniform queue boundedness is precisely uniform control of every finite suffix
 drift.  Reflection and Hall theory therefore reduce the remaining global
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-317.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-317.md
new file mode 100644
index 00000000..6a3a1bef
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-317.md
@@ -0,0 +1,281 @@
+# cp-317 Implementation Report
+
+## Status
+
+**Completed to the first genuine obstruction.**
+
+The finite queue-accounting layer was not extended with more matching variants.
+This checkpoint instead exposed the exact arithmetic transition of a complete
+canonical block, separated endpoint drawup from in-block burst, formalized
+finite primitive repayment excursions, and built a sound generic
+finite-transition certificate surface.
+
+All new Lean files are `no-sorry`.
+
+## 1. Endpoint-width drawup
+
+`UniversalPaymentScalarQueue.lean` now defines:
+
+- `canonicalEndpointWidth`
+- `canonicalEndpointRunningWidthMinimum`
+- `CanonicalEndpointWidthUniformUpperBound`
+
+The exact identity is proved:
+
+```text
+canonicalOutstandingClaimQueue n m
+  = canonicalEndpointWidth n m
+      - canonicalEndpointRunningWidthMinimum n m
+```
+
+Consequences include:
+
+- queue zero iff the current endpoint width attains the running minimum;
+- a completed endpoint whose next state is `1` has queue zero;
+- uniform queue boundedness iff uniform completed-endpoint-width boundedness.
+
+Thus the cp-316 observation "state one had queue zero" is structurally forced,
+not independent numerical evidence.
+
+The experimental candidate
+
+```text
+queue n m <= bitWidth n.1
+```
+
+is named by `CanonicalOutstandingClaimQueueLeInitialWidth`, but is not asserted.
+Only its valid conditional consequence is proved:
+
+```text
+candidate -> canonicalEndpointWidth n m <= 2 * bitWidth n.1
+```
+
+## 2. Exact canonical block normal form
+
+New module:
+
+```text
+DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlockNormalForm
+```
+
+For canonical block `k`, it defines the start time/state, block length `L`, odd
+core `u`, endpoint state, terminal carrier, terminal valuation, and next start.
+
+The following exact arithmetic is proved:
+
+```text
+x + 1 = 2^L * u
+u % 2 = 1
+
+2^t * (state(start+t) + 1) = 3^t * (x + 1),  t < L
+
+endpoint + 1 = 2 * 3^(L-1) * u
+3 * endpoint + 1 = 2 * (3^L * u - 1)
+
+capacity = v2 (3^L * u - 1)
+next start = (3^L * u - 1) / 2^v2(3^L * u - 1)
+```
+
+Therefore the complete block transition is now a Lean theorem:
+
+```text
+(L, u) -> oddPart (3^L * u - 1)
+```
+
+No logarithmic or asymptotic approximation occurs in this layer.
+
+## 3. Drift and in-block burst
+
+The normal-form module also proves:
+
+- block claim count is at most block length;
+- signed block drift is at most `L - capacity`;
+- positive drift implies `capacity < L`;
+- equivalently, positive drift implies `v2(3^L*u-1) < L`;
+- positive drift requires a nonempty delayed-debt fiber.
+
+Within a canonical block, bit width is nondecreasing before endpoint payment,
+so the endpoint-before-payment width is the block maximum.  The exact burst is:
+
+```text
+endpointWidthBeforePayment - blockStartWidth
+  = card (floatGrowthDebtFiberAt n endpoint)
+```
+
+This separates two coordinates:
+
+```text
+completed-endpoint drawup = canonicalOutstandingClaimQueue
+current in-block burst     = delayed-debt cardinality
+```
+
+A conditional all-state bound is proved for every state in a named canonical
+block when both coordinates have uniform bounds.  No global block-coverage
+claim was inserted into that theorem.
+
+## 4. Primitive queue excursions
+
+New module:
+
+```text
+DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPrimitiveExcursion
+```
+
+It defines a finite primitive positive excursion `q..r` by:
+
+- queue before `q` is zero;
+- queue after every block in `[q,r)` is positive;
+- queue after `r` is zero.
+
+The queue presentation is proved equivalent to the signed partial-sum form:
+
+- every proper prefix drift from `q` is positive;
+- total drift through `r` is nonpositive.
+
+The module exposes excursion length, maximum queue, exact signed block word,
+first repayment endpoint, and uniqueness of the repayment block for a fixed
+start.
+
+The important separation is now formal:
+
+```text
+finite repayment endpoint -> unique
+future repayment endpoint exists -> not yet proved
+```
+
+Therefore the unconditional statement that every positive queue position lies
+in a finite primitive excursion is intentionally not exported.
+
+## 5. Generic finite signed-transition certificate
+
+New module:
+
+```text
+DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition
+```
+
+`FiniteSignedTransitionPotentialCertificate` requires:
+
+- a finite signature type;
+- a concrete-to-signature map;
+- concrete and projected edge weights;
+- proof that projected weight bounds concrete drift;
+- a bounded potential whose difference bounds every projected edge.
+
+Lean proves:
+
+- projected path weight bounds concrete path weight;
+- projected path weight telescopes below endpoint potential difference;
+- every concrete path weight is uniformly bounded by the certificate bound;
+- a path returning to the same signature has nonpositive projected and concrete
+  weight.
+
+This is a sound, stronger potential form of the desired nonpositive-cycle
+certificate.  The converse weighted-graph theorem from cycle conditions alone
+remains separate work.
+
+## 6. Finite audit
+
+New executable audit:
+
+```text
+python/Collatz/PetalBridge/canonical_block_normal_form_audit.py
+```
+
+Recorded outputs:
+
+```text
+python/Collatz/PetalBridge/results/canonical_block_normal_form_audit_317.json
+python/Collatz/PetalBridge/results/canonical_block_normal_form_audit_317.md
+```
+
+Range:
+
+- all 65,536 odd roots through `131071`;
+- 1,280 deterministic random odd roots of widths 64, 128, 256, 512, and 1024;
+- exact block-normal-form traces for 9,472 roots (8,192 small plus all random roots);
+- up to 4,096 canonical blocks per root;
+- random seed `54039`.
+
+Every audited block passed the exact normal-form assertions.  No counterexample
+to `queue <= initial bitWidth` was observed.  The largest observed queue was
+`15`, at a 512-bit random root.  These are finite observations only.
+
+## 7. Candidate signature result
+
+The candidate finite signatures used:
+
+- capped block length;
+- low `w` bits of odd core `u`;
+- high `w` bits of start state;
+- capped terminal valuation;
+- capped claim count.
+
+For every tested width `w = 5,6,7,8`, equal signatures had conflicting drift
+or successor behavior.  The audit also found realized positive-weight segments
+between repeated signatures:
+
+| w | drift collisions | nondeterministic successors | positive repeated segments |
+| --- | --- | --- | --- |
+| 5 | 514 | 2477 | 419 |
+| 6 | 363 | 8411 | 103 |
+| 7 | 369 | 24807 | 10 |
+| 8 | 476 | 65724 | 5 |
+
+This does not prove that no finite abstraction can work.  It does prove that
+the tested projection cannot be treated as an exact deterministic automaton,
+and the data gives no basis for constructing its required Lean soundness field.
+
+## 8. Existing bridge audit and stopping point
+
+The existing `FloatStepLedger`, mod-eight reservoir, canonical block histogram,
+pressure margin, finite-window packing, `OneCycle`, and NoLift-facing surfaces
+were inspected.
+
+The exact missing bridge agrees with the source comment already present in
+`DriftBridge.lean`:
+
+```text
+Float/payment data is indexed by orbit time.
+SourcePressureMarginInt is indexed by source depth.
+No proved map currently identifies these slots while preserving contribution.
+```
+
+Without this index-preserving map, a positive primitive queue excursion cannot
+be sent to a pressure separator or NoLift obstruction.  Likewise, the tested
+finite signatures cannot instantiate `actual_le_projected` in the generic
+certificate.
+
+This is the first genuine cp-317 obstruction.  Continuing with more queue
+algebra would not address it.
+
+## 9. Verified builds
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPrimitiveExcursion
+lake build DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition
+lake build DkMath.Collatz.PetalBridge.FloatWindow
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath
+git diff --check
+```
+
+No `sorry` occurs in the changed Float-window files.
+
+## Next implementation
+
+Do not enlarge the coarse signature blindly.  The next productive checkpoint
+must prove one of these missing contracts:
+
+1. an orbit-index to pressure-depth map preserving claim/payment contribution;
+2. a different finite signature with a theorem proving concrete drift is bounded
+   by projected edge weight;
+3. an eventually-zero or finite-repayment theorem for the scalar queue;
+4. an initial upper-boundary resource theorem implying
+   `CanonicalOutstandingClaimQueueLeInitialWidth`.
+
+The first option is the most direct bridge to the existing pressure and NoLift
+infrastructure.  The fourth is the most direct route to the surviving initial
+width candidate.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/review-petal-316.md b/lean/dk_math/docs/dev/das-p2l-260607/review/review-petal-316.md
index e7178d0a..f3f4e15f 100644
--- a/lean/dk_math/docs/dev/das-p2l-260607/review/review-petal-316.md
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/review-petal-316.md
@@ -6,6 +6,8 @@ gch: 5daa50f888e603da9a1ca4948a6c0d5b6a4f1fa3
 
 ## Report
 
+28m2s
+
 cp-316 の登頂アタックを完了しました。
 
 新しい [UniversalPaymentScalarQueue.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentScalarQueue.lean:230) で以下を証明しています。
diff --git a/python/Collatz/PetalBridge/canonical_block_normal_form_audit.py b/python/Collatz/PetalBridge/canonical_block_normal_form_audit.py
new file mode 100644
index 00000000..13c5565d
--- /dev/null
+++ b/python/Collatz/PetalBridge/canonical_block_normal_form_audit.py
@@ -0,0 +1,237 @@
+#!/usr/bin/env python3
+"""cp-317 audit for canonical block normal form and queue-bound candidates.
+
+The script validates the exact ``(L, u) -> oddPart(3^L*u - 1)`` transition,
+checks the experimental queue/initial-width inequality, and measures collisions
+in deliberately finite block signatures.  Its output is computational evidence,
+not a Lean proof.
+"""
+
+from __future__ import annotations
+
+import json
+import random
+from collections import defaultdict
+from pathlib import Path
+
+from canonical_scalar_queue_audit import BLOCK_LIMIT, Orbit, audit_root, upper_carry, v2
+
+
+EXHAUSTIVE_MAX = 131_071
+RANDOM_SEED = 0xD317
+RANDOM_PER_WIDTH = 256
+RANDOM_WIDTHS = (64, 128, 256, 512, 1024)
+SIGNATURE_WIDTHS = (5, 6, 7, 8)
+
+
+def odd_with_exact_width(rng: random.Random, width: int) -> int:
+    return rng.getrandbits(width - 1) | (1 << (width - 1)) | 1
+
+
+def block_trace(root: int) -> list[dict[str, int]]:
+    orbit = Orbit(root)
+    endpoint = orbit.target(0)
+    previous_endpoint = -1
+    queue = 0
+    blocks: list[dict[str, int]] = []
+    for block in range(BLOCK_LIMIT):
+        start = previous_endpoint + 1
+        x = orbit.state(start)
+        length = v2(x + 1)
+        assert endpoint == start + length - 1
+        core = (x + 1) >> length
+        assert core & 1 == 1
+        terminal = pow(3, length) * core - 1
+        terminal_valuation = v2(terminal)
+        next_state = terminal >> terminal_valuation
+        assert orbit.state(endpoint + 1) == next_state
+
+        claims = sum(
+            upper_carry(orbit.state(time)) == 2
+            for time in range(start, endpoint + 1)
+        )
+        capacity = orbit.height(endpoint) - 1
+        assert capacity == terminal_valuation
+        drift = claims - capacity
+        queue = max(0, queue + drift)
+        blocks.append(
+            {
+                "block": block,
+                "start": start,
+                "endpoint": endpoint,
+                "start_state": x,
+                "length": length,
+                "core": core,
+                "terminal_valuation": terminal_valuation,
+                "claims": claims,
+                "capacity": capacity,
+                "drift": drift,
+                "queue": queue,
+                "next_state": next_state,
+            }
+        )
+        if orbit.state(endpoint) == 1:
+            break
+        previous_endpoint = endpoint
+        endpoint = orbit.target(endpoint + 1)
+    return blocks
+
+
+def top_bits(value: int, width: int) -> int:
+    shift = max(0, value.bit_length() - width)
+    return value >> shift
+
+
+def signature(block: dict[str, int], width: int) -> tuple[int, ...]:
+    """A finite candidate signature; capped fields intentionally lose data."""
+    cap = width
+    return (
+        min(block["length"], cap),
+        block["core"] % (1 << width),
+        top_bits(block["start_state"], width),
+        min(block["terminal_valuation"], cap),
+        min(block["claims"], cap),
+    )
+
+
+def signature_summary(traces: list[list[dict[str, int]]], width: int) -> dict[str, int]:
+    drifts: dict[tuple[int, ...], set[int]] = defaultdict(set)
+    successors: dict[tuple[int, ...], set[tuple[int, ...]]] = defaultdict(set)
+    repeated_positive_segments = 0
+    for blocks in traces:
+        sigs = [signature(block, width) for block in blocks]
+        prefix = [0]
+        for block in blocks:
+            prefix.append(prefix[-1] + block["drift"])
+        positions: dict[tuple[int, ...], list[int]] = defaultdict(list)
+        for i, (sig, block) in enumerate(zip(sigs, blocks)):
+            drifts[sig].add(block["drift"])
+            positions[sig].append(i)
+            if i + 1 < len(sigs):
+                successors[sig].add(sigs[i + 1])
+        for indices in positions.values():
+            for left, right in zip(indices, indices[1:]):
+                if prefix[right] - prefix[left] > 0:
+                    repeated_positive_segments += 1
+    return {
+        "signature_width": width,
+        "distinct_signatures": len(drifts),
+        "drift_collision_signatures": sum(len(values) > 1 for values in drifts.values()),
+        "largest_observed_drift_spread": max(
+            (max(values) - min(values) for values in drifts.values()), default=0
+        ),
+        "nondeterministic_successor_signatures": sum(
+            len(values) > 1 for values in successors.values()
+        ),
+        "realized_repeated_signature_positive_segments": repeated_positive_segments,
+    }
+
+
+def main() -> None:
+    exhaustive_rows = []
+    first_counterexample = None
+    for root in range(1, EXHAUSTIVE_MAX + 1, 2):
+        row = audit_root(root)
+        exhaustive_rows.append(row)
+        if row.maximum_queue > root.bit_length() and first_counterexample is None:
+            first_counterexample = {
+                "root": root,
+                "initial_width": root.bit_length(),
+                "maximum_queue": row.maximum_queue,
+            }
+
+    rng = random.Random(RANDOM_SEED)
+    random_roots = [
+        odd_with_exact_width(rng, width)
+        for width in RANDOM_WIDTHS
+        for _ in range(RANDOM_PER_WIDTH)
+    ]
+    random_rows = [audit_root(root) for root in random_roots]
+    for root, row in zip(random_roots, random_rows):
+        if row.maximum_queue > root.bit_length() and first_counterexample is None:
+            first_counterexample = {
+                "root": root,
+                "initial_width": root.bit_length(),
+                "maximum_queue": row.maximum_queue,
+            }
+
+    # A representative deterministic subset is enough for collision diagnostics.
+    trace_roots = list(range(1, 16_384, 2)) + random_roots
+    traces = [block_trace(root) for root in trace_roots]
+    sig_summaries = [signature_summary(traces, width) for width in SIGNATURE_WIDTHS]
+
+    all_rows = exhaustive_rows + random_rows
+    queue_record = max(all_rows, key=lambda row: (row.maximum_queue, -row.root))
+    result = {
+        "checkpoint": 317,
+        "exhaustive_odd_roots": len(exhaustive_rows),
+        "exhaustive_max": EXHAUSTIVE_MAX,
+        "random_seed": RANDOM_SEED,
+        "random_roots": len(random_roots),
+        "random_widths": list(RANDOM_WIDTHS),
+        "block_limit": BLOCK_LIMIT,
+        "normal_form_trace_roots": len(trace_roots),
+        "normal_form_assertions": "passed",
+        "initial_width_candidate_first_counterexample": first_counterexample,
+        "largest_observed_queue": queue_record.maximum_queue,
+        "largest_observed_queue_root": queue_record.root,
+        "largest_observed_queue_root_width": queue_record.root.bit_length(),
+        "signature_summaries": sig_summaries,
+    }
+
+    output_dir = Path(__file__).with_name("results")
+    output_dir.mkdir(parents=True, exist_ok=True)
+    json_path = output_dir / "canonical_block_normal_form_audit_317.json"
+    md_path = output_dir / "canonical_block_normal_form_audit_317.md"
+    json_path.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
+
+    counterexample_text = (
+        "none observed" if first_counterexample is None else f"`{first_counterexample}`"
+    )
+    lines = [
+        "# Canonical Block Normal-Form Audit (cp-317)",
+        "",
+        "This is finite computational evidence, not a Lean theorem.",
+        "",
+        "## Range",
+        "",
+        f"- exhaustive odd roots: `1..{EXHAUSTIVE_MAX}` ({len(exhaustive_rows)} roots)",
+        f"- deterministic random roots: {len(random_roots)} over widths {RANDOM_WIDTHS}",
+        f"- random seed: `{RANDOM_SEED}`",
+        f"- per-root block limit: `{BLOCK_LIMIT}`",
+        f"- exact normal-form trace roots: `{len(trace_roots)}`",
+        "",
+        "## Results",
+        "",
+        "- every audited block passed the exact normal-form transition assertions",
+        f"- first `queue > initial bitWidth` counterexample: {counterexample_text}",
+        f"- largest observed queue: `{queue_record.maximum_queue}` at root `{queue_record.root}` "
+        f"(initial width `{queue_record.root.bit_length()}`)",
+        "",
+        "## Finite Signature Diagnostics",
+        "",
+        "| w | signatures | drift collisions | max drift spread | nondeterministic successors | realized positive repeated segments |",
+        "| --- | --- | --- | --- | --- | --- |",
+    ]
+    lines.extend(
+        f"| {item['signature_width']} | {item['distinct_signatures']} | "
+        f"{item['drift_collision_signatures']} | {item['largest_observed_drift_spread']} | "
+        f"{item['nondeterministic_successor_signatures']} | "
+        f"{item['realized_repeated_signature_positive_segments']} |"
+        for item in sig_summaries
+    )
+    lines.extend(
+        [
+            "",
+            "The candidate signatures use capped length, capped terminal valuation, capped claim count,",
+            "the low `w` core bits, and the high `w` start-state bits.  A collision or nondeterministic",
+            "successor is evidence that this projection is not an exact automaton state.  Absence of an",
+            "observed collision would still not establish projection soundness.",
+        ]
+    )
+    md_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
+    print(json.dumps(result, indent=2))
+
+
+if __name__ == "__main__":
+    main()
diff --git a/python/Collatz/PetalBridge/results/canonical_block_normal_form_audit_317.json b/python/Collatz/PetalBridge/results/canonical_block_normal_form_audit_317.json
new file mode 100644
index 00000000..a269e59f
--- /dev/null
+++ b/python/Collatz/PetalBridge/results/canonical_block_normal_form_audit_317.json
@@ -0,0 +1,55 @@
+{
+  "checkpoint": 317,
+  "exhaustive_odd_roots": 65536,
+  "exhaustive_max": 131071,
+  "random_seed": 54039,
+  "random_roots": 1280,
+  "random_widths": [
+    64,
+    128,
+    256,
+    512,
+    1024
+  ],
+  "block_limit": 4096,
+  "normal_form_trace_roots": 9472,
+  "normal_form_assertions": "passed",
+  "initial_width_candidate_first_counterexample": null,
+  "largest_observed_queue": 15,
+  "largest_observed_queue_root": 13007082825098195174285279455291089318240773657547195000348700458518007247903840970390548671397537876859751635784391081095674028805451362190390027793449173,
+  "largest_observed_queue_root_width": 512,
+  "signature_summaries": [
+    {
+      "signature_width": 5,
+      "distinct_signatures": 2562,
+      "drift_collision_signatures": 514,
+      "largest_observed_drift_spread": 18,
+      "nondeterministic_successor_signatures": 2477,
+      "realized_repeated_signature_positive_segments": 419
+    },
+    {
+      "signature_width": 6,
+      "distinct_signatures": 9785,
+      "drift_collision_signatures": 363,
+      "largest_observed_drift_spread": 17,
+      "nondeterministic_successor_signatures": 8411,
+      "realized_repeated_signature_positive_segments": 103
+    },
+    {
+      "signature_width": 7,
+      "distinct_signatures": 31053,
+      "drift_collision_signatures": 369,
+      "largest_observed_drift_spread": 15,
+      "nondeterministic_successor_signatures": 24807,
+      "realized_repeated_signature_positive_segments": 10
+    },
+    {
+      "signature_width": 8,
+      "distinct_signatures": 90457,
+      "drift_collision_signatures": 476,
+      "largest_observed_drift_spread": 15,
+      "nondeterministic_successor_signatures": 65724,
+      "realized_repeated_signature_positive_segments": 5
+    }
+  ]
+}
diff --git a/python/Collatz/PetalBridge/results/canonical_block_normal_form_audit_317.md b/python/Collatz/PetalBridge/results/canonical_block_normal_form_audit_317.md
new file mode 100644
index 00000000..734a22bf
--- /dev/null
+++ b/python/Collatz/PetalBridge/results/canonical_block_normal_form_audit_317.md
@@ -0,0 +1,31 @@
+# Canonical Block Normal-Form Audit (cp-317)
+
+This is finite computational evidence, not a Lean theorem.
+
+## Range
+
+- exhaustive odd roots: `1..131071` (65536 roots)
+- deterministic random roots: 1280 over widths (64, 128, 256, 512, 1024)
+- random seed: `54039`
+- per-root block limit: `4096`
+- exact normal-form trace roots: `9472`
+
+## Results
+
+- every audited block passed the exact normal-form transition assertions
+- first `queue > initial bitWidth` counterexample: none observed
+- largest observed queue: `15` at root `13007082825098195174285279455291089318240773657547195000348700458518007247903840970390548671397537876859751635784391081095674028805451362190390027793449173` (initial width `512`)
+
+## Finite Signature Diagnostics
+
+| w | signatures | drift collisions | max drift spread | nondeterministic successors | realized positive repeated segments |
+| --- | --- | --- | --- | --- | --- |
+| 5 | 2562 | 514 | 18 | 2477 | 419 |
+| 6 | 9785 | 363 | 17 | 8411 | 103 |
+| 7 | 31053 | 369 | 15 | 24807 | 10 |
+| 8 | 90457 | 476 | 15 | 65724 | 5 |
+
+The candidate signatures use capped length, capped terminal valuation, capped claim count,
+the low `w` core bits, and the high `w` start-state bits.  A collision or nondeterministic
+successor is evidence that this projection is not an exact automaton state.  Absence of an
+observed collision would still not establish projection soundness.
````
`````
