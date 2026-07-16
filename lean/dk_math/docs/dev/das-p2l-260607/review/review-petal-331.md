# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.FloatWindow.BoundedRepaymentLag

gch: c52758ef50b369a3e736e6809231b620c9eea2e7

## Report

(10m4s)

checkpoint 331 を完了しました。

**確定した事実**

累積 inflow 全体の有界性は、queue 安定性に必要ではありません。Lean で次の安定 throughput を証明しました。

```text
queue = 0
potential = 0
outflow = 1
inflow = 1
```

queue は常にゼロですが、累積 inflow は無限に増加します。

正しい一般則は、outflow を捨てない次の telescope です。

```text
queue m + potential m + Σ outflow
  ≤ queue 0 + potential 0 + Σ inflow
```

したがって累積 net inflow が `B` 以下なら、

```text
queue m ≤ queue 0 + potential 0 + B
```

が成立します。

**Canonical 接続**

canonical reflected queue を `FiniteAmortizedBalance` の具体例として実装しました。

- inflow: block claim count
- outflow: 実際に消費された service
- unused service: service から consumed を除いた量
- queue: block 処理直前の outstanding queue

次の厳密保存則も通っています。

```text
queueAfter + consumed = queueBefore + demand
service = consumed + unusedService
queueAfter = queueBefore + demand - consumed
```

**二つの追加ルート**

有限 signed-transition certificate から、

```text
全 canonical window drift の上界
→ canonical queue 上界
→ endpoint width 上界
```

までの conditional chain を完成させました。

また bounded repayment lag について、

```text
最大 lag = L
block ごとの arrivals ≤ A
→ queue ≤ L * A
```

を一般定理として追加しました。

現在の三ルートの欠落点は明確です。

1. finite signature: sound な projected upper edge weight
2. repayment lag: 全 canonical claim に対する一様 lag
3. owned carrier: source identity と時間方向の非再利用を保つ再帰 carrier

いずれか一つだけが必須とは、まだ結論していません。

`lake build DkMath` を含む全ビルドと `git diff --check` が成功しました。変更ファイルに `sorry`、`maxHeartbeats` はありません。

詳細: [report-petal-331.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-331.md)

## Review

## cp-331 実装レビュー

## 結論

GitHub branch `dev/petal-collatz-bridge-260630-v7` の checkpoint 331 commit、

```text
c52758ef50b369a3e736e6809231b620c9eea2e7
```

を直接参照した。添付 diff・report と branch 上の完成ファイルは一致している。

判定は **条件付き採用**じゃ。

次は全面採用できる。

- cumulative outflow を保持した強い telescope
- stable-throughput regression
- canonical queue の exact scalar balance
- unused service 分解
- finite signed-transition certificate から queue / width への conditional bridge
- bounded repayment-lag の一般的な counting lemma

ただし bounded-lag route には二つの補正が必要になる。

1. 現在の「直前 $L$ slot」の定義は、$m<L$ のとき未来の arrival を数える。
2. canonical specialization に必要なのは uniform lag だけではない。各 block の arrival 上界、または各 $L$-window の arrival 総量上界も必要である。

したがって report の、

> bounded repayment-lag route で欠けているのは全 claim に対する一様 lag

は強すぎる。

正確には、

> **一様 lag と、その lag-window 内で生成される demand 総量の一様上界**

の二つが必要じゃ。

---

## 1. Strong balance telescope

`FiniteAmortizedBalance` への改名は正しい。

```lean
structure FiniteAmortizedBalance where
  queue : ℕ → ℕ
  potential : ℕ → ℕ
  outflow : ℕ → ℕ
  inflow : ℕ → ℕ
```

とし、resource ownership を含まない純粋な scalar balance であることが明記された。

中心 theorem は、

$$Q_m+P_m+\sum_{k<m}O_k\le Q_0+P_0+\sum_{k<m}I_k$$

じゃ。

```lean
queue_add_potential_add_sum_outflow_le_initial_add_sum_inflow
```

は、一段保存則を outflow ごと telescope している。前 checkpoint のように outflow を途中で捨てていない。

そこから、

$$\sum_{k<m}I_k\le\sum_{k<m}O_k+B$$

なら、

$$Q_m\le Q_0+P_0+B$$

が得られた。

これは正しい amortized surplus theoremじゃ。

---

## 2. Stable-throughput regression

```lean
stableUnitThroughputBalance
```

は、

$$Q_k=0,\qquad P_k=0,\qquad O_k=1,\qquad I_k=1$$

という定常流を表す。

queue は常に $0$ だが、

$$\sum_{k<m}I_k=m$$

なので累積 inflow に有限上界は存在しない。

これにより、

```text
bounded cumulative inflow
```

は queue 安定性の必要条件ではないことが Lean 上で固定された。

この regression は cp-330 の循環性 regression と同じく、今後も残す価値が高い。

---

## 3. Canonical scalar balance

```lean
canonicalQueueFiniteAmortizedBalance
```

の indexing は正しい。

block $k$ の処理直前 queue を、

```lean
canonicalOutstandingClaimQueueBeforeBlock n k
```

とし、

$$Q^{\mathrm{before}}_0=0$$

$$Q^{\mathrm{before}}_{k+1}=Q^{\mathrm{after}}_k$$

としている。

canonical instance は、

```text
queue     = queue before block
potential = 0
outflow   = consumed service
inflow    = new block demand
```

じゃ。

一段保存則は実際には不等式ではなく exact equality、

$$Q^{\mathrm{after}}_k+C_k=Q^{\mathrm{before}}_k+A_k$$

から得ている。

ここは全面採用でよい。

---

## 4. Exact prefix conservation を追加できる

cp-331 の一段 equality を telescope すれば、canonical queue ではさらに強く、

$$Q^{\mathrm{before}}*m+\sum*{k<m}C_k=\sum_{k<m}A_k$$

が得られる。

初期 queue が $0$ だからじゃ。

したがって、

$$Q^{\mathrm{before}}*m=\sum*{k<m}A_k-\sum_{k<m}C_k$$

も得られる。

次の theorem を置く価値がある。

```lean
theorem canonicalQueueBefore_add_sumConsumed_eq_sumDemand
    (n : OddNat) (m : ℕ) :
    canonicalOutstandingClaimQueueBeforeBlock n m +
        ∑ k ∈ Finset.range m, canonicalQueueConsumed n k =
      ∑ k ∈ Finset.range m, canonicalQueueDemand n k
```

これは canonical queue が「抽象 potential」ではなく、実 demand と実 consumed capacity の差そのものであることを固定する。

---

## 5. Unused service

```lean
canonicalQueueUnusedService
```

について、

$$S_k=C_k+U_k$$

$$Q^{\mathrm{after}}_k=Q^{\mathrm{before}}_k+A_k-C_k$$

まで閉じた。

scalar accounting として完全じゃ。

ただし `unused service` は未来へ繰り越される resource ではない。

現在の reflected queue では、block $k$ で使われなかった capacity は、その場で失効する。

したがって、

```text
unusedService = future reserve
```

とは読んではならない。

この失効性こそ、causal queue と unordered total balance の差を作っている。

---

## 6. Finite signed-transition bridge

新しい conditional chain は正しく閉じている。

certificate は、

- concrete edge weight
- finite signature pair の projected upper weight
- finite potential difference

を持ち、

$$w_{\mathrm{actual}}(a,b)\le w_{\mathrm{proj}}(\sigma(a),\sigma(b))\le\Phi(\sigma(b))-\Phi(\sigma(a))$$

を要求する。

canonical block window $q,\ldots,m$ は、edge path、

$$q\to q+1\to\cdots\to m+1$$

の $m-q+1$ 本に対応する。

各 edge $k\to k+1$ の actual weight を `endpointAccountingTerm n k` とすれば、

$$\operatorname{WindowDrift}(q,m)\le C.\operatorname{bound}$$

が得られる。

そこから、

$$\operatorname{Queue}\le C.\operatorname{bound}$$

$$\operatorname{EndpointWidth}\le\operatorname{bitWidth}(n)+C.\operatorname{bound}$$

まで接続した。

この route は、三ルートの中で現時点では最短の challenge-facing conditional chainじゃ。

---

## 7. Finite signature route の本当の二条件

finite signature を作るとき、必要なのは単なる finite state ではない。

まず、同じ signature pair に射影される concrete edges の drift が、上から有限値で抑えられなければならない。

```text
edgewise boundedness
```

が第一条件じゃ。

その後、projected graph が bounded potential を持つ必要がある。

```text
no positive projected cycle
```

が第二条件になる。

したがって candidate signature の監査順序は、

```text
finite signature
→ signature pair ごとの edge drift 上界
→ projected finite graph
→ positive cycle の有無
→ potential 構成
```

であるべきじゃ。

positive cycle の監査へ進む前に、同一 signature edge 内で actual drift が無制限に大きくならないことを示さねばならない。

---

## 8. `FloatStepLedger` はまだ finite signature ではない

既存の、

```lean
structure FloatStepLedger where
  widthBefore : ℕ
  upperCarry : ℕ
  height : ℕ
  widthAfter : ℕ
  residue8 : Fin 8
```

は exact ledger だが、`widthBefore`、`height`、`widthAfter` が自然数なので finite signature ではない。

finite projection を作るには、

- width を捨てるか差だけにする
- height を `1 / ≥2` 等へ clip する
- residue を mod $8,16,32,64$ へ落とす
- saturation / deepest-hole 等の finite tag を加える

必要がある。

ただし clipping 後にも edge weight 上界が証明できることが必要じゃ。

---

## 9. Raw-step projection も再検討すべき

block-level edge は、多数の accelerated steps を一つに集約している。

一方、raw accelerated step には既に exact ledger、

$$\operatorname{widthBefore}+\operatorname{upperCarry}=\operatorname{height}+\operatorname{widthAfter}$$

がある。

さらに width growth は、

$$\operatorname{upperCarry}=2,\qquad\operatorname{height}=1$$

の場合に限られ、growth channel は mod $8$ の $3$ または $7$ に制限されている。

既存 `DriftBridge` では、growth のうち mod $8=3$ は次の delayed payment receiver に接続され、未払い reservoir は mod $8=7$ に絞られている。

したがって block-signature pair の drift 上界が作りにくい場合は、

> raw accelerated-step の有限 signature certificateを作り、そこから canonical endpoint width を sample する

route も候補になる。

block を先に圧縮しすぎない方が、有限 graph の edge weight は扱いやすい可能性がある。

---

## 10. Bounded repayment-lag の初期区間バグ

現在の定義は、

```lean
∀ m, queue m ≤ ∑ j ∈ Finset.range L, arrivals (m - L + j)
```

じゃ。

$m\ge L$ なら、

$$m-L,\ldots,m-1$$

を数えるので正しい。

しかし、例えば $m=1,L=3$ なら、

$$m-L=0$$

となり、index は、

$$0,1,2$$

になる。

block $1$ より未来の arrival $2$ まで数えてしまう。

この predicate は actual lag から導かれる弱い scalar consequence ではあるが、それ単体では causal lag を表さない。

正しい preceding-window は、

```lean
∑ k ∈ Finset.Ico (m - L) m, arrivals k
```

じゃ。

これなら、

- $m<L$ では $0,\ldots,m-1$
- $m\ge L$ では $m-L,\ldots,m-1$

を正しく数える。

---

## 11. Lag route に不足する第二条件

generic theorem は、

```lean
harrivals : ∀ k, arrivals k ≤ A
```

も仮定している。

したがって canonical queue へ適用するには、

```lean
∀ k, canonicalBlockClaimCount n k ≤ A
```

が必要になる。

cp-331 には、この uniform arrival bound は実装されていない。

よって missing Collatz theorem は lag だけではない。

正確には次のどちらかが必要じゃ。

### 分離型

$$\text{uniform lag }L+\text{per-block arrival bound }A$$

### 直接型

$$\forall m,\ \sum_{k\in[m-L,m)}A_k\le B$$

直接型の方が一般的である。

一 block の demand が大きくても、周辺 block が小さければ window total は抑えられるからじゃ。

---

## 12. Lag route の正しい public surface

次の二段構造がよい。

```lean
def recentArrivalMass
    (arrivals : ℕ → ℕ) (L m : ℕ) : ℕ :=
  ∑ k ∈ Finset.Ico (m - L) m, arrivals k
```

```lean
def OutstandingBeforeQueueCoveredByRecentArrivals
    (queue arrivals : ℕ → ℕ) (L : ℕ) : Prop :=
  ∀ m, queue m ≤ recentArrivalMass arrivals L m
```

その上で、

```lean
theorem queue_le_of_recentArrivalMass_le
```

と、

```lean
theorem queue_le_mul_of_recentLag_of_arrivals_le
```

を分ける。

canonical route の missing theorem も、

```text
all claims have age < L
```

だけでなく、

```text
recent canonical demand mass is uniformly bounded
```

と明記できる。

---

## 13. 三ルートの現在地

### Finite signed transition

最短 conditional chain は完成。

不足は、

```text
sound finite signature
finite edge-weight upper bounds
bounded potential / no positive cycle
```

じゃ。

### Bounded repayment lag

generic counting lemma は完成。

不足は、

```text
uniform causal lag
uniform recent-window demand bound
```

の二つじゃ。

### Owned carrier

source identity と temporal nonreuse を保持できる。

直接 queue bound を与えるとは限らないが、lag theorem を証明するための最も自然な中間層になり得る。

したがって owned carrier は第三の競合 routeというより、

> bounded-lag route を支える証明装置

にもなり得る。

---

## 14. 判定まとめ

### Strong net-flow telescope

**完成。**

### Stable-throughput regression

**完成。**

### Canonical scalar instance

**完成。**

### Exact unused service

**完成。**

### Finite signed certificate bridge

**完成。**

### Bounded lag counting theorem

**数値 theorem は完成。**

### Lag window semantics

**$m<L$ で未来 arrival を含むため修正が必要。**

### Canonical lag route

**一様 lag に加え、arrival-window 上界も未実装。**

### 最短次路

**lag API を補正後、finite signed projection の edgewise boundedness を監査。**

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge FloatWindow branch after
report-petal-331.

The cp-331 strong balance telescope, canonical scalar balance, signed-certificate
bridge, and generic lag counting lemma are accepted.

Two corrections are required before the bounded-lag route is used:

    the current preceding-L-slot formula includes future arrivals when m < L;

    uniform lag alone does not imply a uniform queue bound without a bound on
    arrivals in each lag window.

## Stage A — exact recent-arrival window

Define:

    recentArrivalMass arrivals L m :=
      sum k in Finset.Ico (m - L) m, arrivals k.

Prove:

    m < L ->
      recentArrivalMass arrivals L m
        = sum k in Finset.range m, arrivals k;

    L <= m ->
      recentArrivalMass arrivals L m
        = sum j in Finset.range L, arrivals (m - L + j);

    (Finset.Ico (m - L) m).card <= L.

Do not use future arrival indices in the early window.

## Stage B — corrected scalar lag predicate

Define:

    OutstandingBeforeQueueCoveredByRecentArrivals queue arrivals L :=
      forall m, queue m <= recentArrivalMass arrivals L m.

Deprecate or document the old `OutstandingQueueHasRepaymentLag` as a coarse
compatibility predicate.

Prove:

    recent-arrival mass <= B
      ->
    queue <= B;

and:

    arrivals k <= A
      ->
    queue m <= L * A.

Include explicit regressions for:

    m = 0;
    m < L;
    m = L;
    L = 0.

## Stage C — exact canonical prefix balance

Prove:

    canonicalOutstandingClaimQueueBeforeBlock n m
      + sum k in range m, canonicalQueueConsumed n k
      =
    sum k in range m, canonicalQueueDemand n k.

Derive:

    canonicalOutstandingClaimQueueBeforeBlock n m
      =
    sum demand - sum consumed.

Use the exact block conservation, not the generic inequality telescope.

## Stage D — canonical lag interfaces

Define a conditional canonical predicate using:

    queue    = canonicalOutstandingClaimQueueBeforeBlock n;
    arrivals = canonicalQueueDemand n.

Provide two separate consequence theorems:

    uniform lag L + per-block demand bound A
      ->
    canonical queue bound L*A;

    uniform lag L + direct recent-window demand bound B
      ->
    canonical queue bound B.

Record that no uniform canonical `A`, `B`, or `L` is currently proved.

Do not report the lag theorem as the sole missing input.

## Stage E — specialized canonical finite projection wrapper

Wrap the existing relational certificate in a surface whose concrete edge
weight is definitionally:

    endpointAccountingTerm n k.

A candidate wrapper may contain:

    signature : Nat -> Signature;
    projectedUpperWeight : Signature -> Signature -> Int;
    potential : Signature -> Int;
    bound : Nat;
    actual_le_projected :
      endpointAccountingTerm n k
        <=
      projectedUpperWeight (signature k) (signature (k + 1));
    projected_le_potential_diff;
    potential bounds.

Prove that this wrapper implies the existing relational certificate and hence
the canonical queue and endpoint-width bounds.

This removes arbitrary `actualWeight` bookkeeping from candidate construction.

## Stage F — edgewise boundedness before cycle search

For every candidate finite signature, first audit:

    for each realized signature pair s -> t,
    are all concrete endpointAccountingTerm values uniformly bounded above?

Do not search for a potential until this edgewise upper-bound obligation is
closed.

A drift collision is harmless if all collided drifts share a finite upper
bound.  An unbounded positive collision rejects the signature immediately.

## Stage G — initial block-signature candidates

Audit finite combinations of already proved data:

    odd core residue modulo 8, 16, 32, or 64;
    start-state upper carry;
    terminal valuation clipped to 1 / at least 2;
    drift sign;
    saturated / nonsaturated;
    deepest-hole flag;
    tight valuation-one flag.

Avoid unbounded fields such as exact width, exact block length, or exact
terminal valuation unless they are clipped.

For each rejected candidate, record one of:

    unbounded edge weight within one signature pair;
    realized positive closed-signature path;
    inability to prove transition soundness.

## Stage H — raw-step alternative

If block-level edge weights cannot be bounded by a useful finite signature,
build an alternative certificate at accelerated-step level.

Use the existing exact identity:

    widthBefore + upperCarry = height + widthAfter.

Define raw signed weight:

    bitWidth (T x) - bitWidth x.

Use finite information such as:

    residue modulo 8 or 16;
    upper carry one/two;
    height one/at-least-two;
    width growth flag.

Prove a conditional bridge:

    bounded raw-step width drawup
      ->
    bounded canonical endpoint width
      ->
    bounded canonical queue.

Do not assume that a block-level projection is intrinsically superior.

## Stage I — finite graph potential criterion

For a fixed finite candidate graph, expose the two independent obligations:

    every realized edge is bounded by its projected edge weight;

    every realized closed-signature path has nonpositive total projected
    weight.

If practical, prove a finite difference-constraint theorem constructing a
potential from nonpositive cycle weights.

Otherwise keep potential construction candidate-specific.

## Stage J — owned claim carrier scope

Continue design of a recursive source-bearing outstanding-claim carrier, but
state its purpose precisely:

    preserve claim origin;
    ensure consumed claims never reappear;
    support claim-age and bounded-lag arguments.

Do not require it to be an initial finite upper-bit resource.

The owned claim carrier may support the lag route even if no independent
upper-boundary carrier exists.

## Stage K — report correction

Record:

    bounded total inflow is not necessary;

    bounded net inflow is sufficient;

    finite signed transition currently has the shortest complete conditional
    chain;

    bounded repayment lag needs both lag control and recent-arrival-mass
    control;

    owned claim carriers may serve as the mechanism for proving lag.

## Stopping rule

Stop at the first genuine obstruction among:

    the corrected recent-arrival window cannot be expressed cleanly;
    the exact canonical prefix balance fails;
    no canonical recent-window demand bound can be isolated;
    every finite block signature has unbounded positive edge collisions;
    a candidate admits a realized positive closed-signature path;
    raw-step signatures also admit uncontrolled positive cycles;
    recursive claim ownership cannot preserve source identity.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-332.md
```

cp-331 で三本の登山路は揃った。

次はそのうち finite-signature route について、いきなり「閉路が悪い」と見るのではなく、まず **一つの有限 edge に無限の正 drift が押し込まれていないか**を裁く段階じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
index f4770a5f..e56c93e7 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
@@ -28,6 +28,7 @@ import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentSelectedCarrier
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude
 import DkMath.Collatz.PetalBridge.FloatWindow.FiniteAmortizedResource
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmortizedResource
+import DkMath.Collatz.PetalBridge.FloatWindow.BoundedRepaymentLag
 import DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition
 
 #print "file: DkMath.Collatz.PetalBridge.FloatWindow"
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/BoundedRepaymentLag.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/BoundedRepaymentLag.lean
new file mode 100644
index 00000000..d3ef1cd1
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/BoundedRepaymentLag.lean
@@ -0,0 +1,55 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import Mathlib.Algebra.Order.BigOperators.Group.Finset
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.BoundedRepaymentLag"
+
+namespace DkMath.Collatz
+
+/-!
+# Generic bounded repayment lag
+
+The predicate below is the scalar consequence of an owned statement saying
+that every outstanding arrival at time `m` was born in one of the preceding
+`L` slots.  It is independent of Collatz and deliberately does not manufacture
+claim ownership.
+-/
+
+/-- Outstanding work is covered by arrivals in the preceding `L` slots. -/
+def OutstandingQueueHasRepaymentLag
+    (queue arrivals : ℕ → ℕ) (L : ℕ) : Prop :=
+  ∀ m, queue m ≤ ∑ j ∈ Finset.range L, arrivals (m - L + j)
+
+/-- A lag bound `L` and per-slot arrival bound `A` imply queue bound `L*A`. -/
+theorem queue_le_mul_of_repaymentLag_of_arrivals_le
+    {queue arrivals : ℕ → ℕ} {L A : ℕ}
+    (hlag : OutstandingQueueHasRepaymentLag queue arrivals L)
+    (harrivals : ∀ k, arrivals k ≤ A) (m : ℕ) :
+    queue m ≤ L * A := by
+  calc
+    queue m ≤ ∑ j ∈ Finset.range L, arrivals (m - L + j) := hlag m
+    _ ≤ ∑ _j ∈ Finset.range L, A :=
+      Finset.sum_le_sum fun j _ => harrivals (m - L + j)
+    _ = L * A := by simp
+
+/-- Caller-facing uniform form of the generic lag theorem. -/
+theorem repaymentLag_uniformUpperBound
+    {queue arrivals : ℕ → ℕ} {L A : ℕ}
+    (hlag : OutstandingQueueHasRepaymentLag queue arrivals L)
+    (harrivals : ∀ k, arrivals k ≤ A) :
+    ∀ m, queue m ≤ L * A :=
+  fun m => queue_le_mul_of_repaymentLag_of_arrivals_le hlag harrivals m
+
+/-!
+For the canonical Collatz queue, the missing theorem is not the generic
+counting argument above.  It is an owned statement that each actual claim is
+consumed within one uniform number of later canonical blocks.  The current
+residue and saturated-successor grammar proves repayment for selected local
+branches, but no theorem supplies a uniform lag for all canonical claims.
+-/
+
+end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteAmortizedResource.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteAmortizedResource.lean
index a2128411..5c331185 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteAmortizedResource.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteAmortizedResource.lean
@@ -12,67 +12,129 @@ import Mathlib.Algebra.BigOperators.Group.Finset.Basic
 namespace DkMath.Collatz
 
 /-!
-# Finite amortized resource telescope
+# Finite amortized balance telescope
 
-This module is deliberately independent of the Collatz observables.  It only
-records a scalar queue, a scalar potential, consumed mass, replenishment, and
-one-step conservation.  In particular, there is no phantom state carrier.
+This scalar combinator has no ownership semantics.  `inflow` and `outflow`
+are neutral accounting streams; a caller must separately prove that they come
+from concrete resources if that interpretation is required.
 -/
 
-/-- Generic finite-step amortized accounting data. -/
-structure FiniteAmortizedResource where
+/-- Generic finite-step balance data. -/
+structure FiniteAmortizedBalance where
   queue : ℕ → ℕ
   potential : ℕ → ℕ
-  consumed : ℕ → ℕ
-  replenishment : ℕ → ℕ
+  outflow : ℕ → ℕ
+  inflow : ℕ → ℕ
   step_conservation :
-    ∀ k, queue (k + 1) + potential (k + 1) + consumed k ≤
-      queue k + potential k + replenishment k
+    ∀ k, queue (k + 1) + potential (k + 1) + outflow k ≤
+      queue k + potential k + inflow k
 
-namespace FiniteAmortizedResource
+/-- Compatibility alias for the original scalar type name. -/
+abbrev FiniteAmortizedResource := FiniteAmortizedBalance
 
-/-- Iterating one-step conservation gives the finite-prefix resource ceiling. -/
-theorem queue_add_potential_le_initial_add_sum
-    (A : FiniteAmortizedResource) (m : ℕ) :
-    A.queue m + A.potential m ≤
-      A.queue 0 + A.potential 0 + ∑ k ∈ Finset.range m, A.replenishment k := by
+namespace FiniteAmortizedBalance
+
+/-- Keeping all outflow terms gives the strongest finite-prefix telescope. -/
+theorem queue_add_potential_add_sum_outflow_le_initial_add_sum_inflow
+    (A : FiniteAmortizedBalance) (m : ℕ) :
+    A.queue m + A.potential m + ∑ k ∈ Finset.range m, A.outflow k ≤
+      A.queue 0 + A.potential 0 + ∑ k ∈ Finset.range m, A.inflow k := by
   induction m with
   | zero => simp
   | succ m ih =>
       have hstep := A.step_conservation m
-      rw [Finset.sum_range_succ]
+      rw [Finset.sum_range_succ, Finset.sum_range_succ]
       omega
 
-/-- The sharp queue estimate uses only the initial potential. -/
-theorem queue_le_initial_add_potential_add_cumulativeReplenishment
-    (A : FiniteAmortizedResource) (m : ℕ) :
+/-- Dropping the nonnegative cumulative outflow gives the weaker telescope. -/
+theorem queue_add_potential_le_initial_add_sum
+    (A : FiniteAmortizedBalance) (m : ℕ) :
+    A.queue m + A.potential m ≤
+      A.queue 0 + A.potential 0 + ∑ k ∈ Finset.range m, A.inflow k := by
+  have h := A.queue_add_potential_add_sum_outflow_le_initial_add_sum_inflow m
+  omega
+
+/-- The direct queue estimate uses only the initial potential. -/
+theorem queue_le_initial_add_potential_add_cumulativeInflow
+    (A : FiniteAmortizedBalance) (m : ℕ) :
     A.queue m ≤
-      A.queue 0 + A.potential 0 + ∑ k ∈ Finset.range m, A.replenishment k := by
+      A.queue 0 + A.potential 0 + ∑ k ∈ Finset.range m, A.inflow k := by
   have h := A.queue_add_potential_le_initial_add_sum m
   omega
 
-/-- Initial potential and cumulative replenishment bounds give a queue bound. -/
+/-- Bounded cumulative net inflow, rather than bounded total inflow, controls
+the queue in a stable system with ongoing throughput. -/
+theorem queue_le_of_cumulativeInflow_le_cumulativeOutflow_add
+    (A : FiniteAmortizedBalance) {B : ℕ}
+    (hnet : ∀ m, ∑ k ∈ Finset.range m, A.inflow k ≤
+      (∑ k ∈ Finset.range m, A.outflow k) + B) (m : ℕ) :
+    A.queue m ≤ A.queue 0 + A.potential 0 + B := by
+  have htel := A.queue_add_potential_add_sum_outflow_le_initial_add_sum_inflow m
+  have hm := hnet m
+  omega
+
+/-- Wrapper using an explicit upper bound for the initial potential. -/
+theorem queue_le_of_initialPotential_and_boundedNetInflow
+    (A : FiniteAmortizedBalance) {P B : ℕ}
+    (hpotential : A.potential 0 ≤ P)
+    (hnet : ∀ m, ∑ k ∈ Finset.range m, A.inflow k ≤
+      (∑ k ∈ Finset.range m, A.outflow k) + B) (m : ℕ) :
+    A.queue m ≤ A.queue 0 + P + B := by
+  have hqueue := A.queue_le_of_cumulativeInflow_le_cumulativeOutflow_add hnet m
+  omega
+
+/-- Compatibility theorem for the stronger bounded-total-inflow hypothesis. -/
 theorem queue_le_of_initialPotential_and_cumulativeReplenishment_bounds
-    (A : FiniteAmortizedResource) {P R : ℕ}
+    (A : FiniteAmortizedBalance) {P R : ℕ}
     (hpotential : A.potential 0 ≤ P)
-    (hreplenishment : ∀ m,
-      ∑ k ∈ Finset.range m, A.replenishment k ≤ R) (m : ℕ) :
+    (hinflow : ∀ m, ∑ k ∈ Finset.range m, A.inflow k ≤ R) (m : ℕ) :
     A.queue m ≤ A.queue 0 + P + R := by
-  have hqueue := A.queue_le_initial_add_potential_add_cumulativeReplenishment m
-  have hrepl := hreplenishment m
+  have hqueue := A.queue_le_initial_add_potential_add_cumulativeInflow m
+  have hm := hinflow m
   omega
 
-/-- Compatibility corollary: a uniform potential bound is stronger than the
-initial bound actually used by the telescope. -/
+/-- Compatibility corollary with an unnecessarily uniform potential bound. -/
 theorem queue_le_of_potential_and_cumulative_replenishment_bounds
-    (A : FiniteAmortizedResource) {P R : ℕ}
+    (A : FiniteAmortizedBalance) {P R : ℕ}
     (hpotential : ∀ k, A.potential k ≤ P)
-    (hreplenishment : ∀ m,
-      ∑ k ∈ Finset.range m, A.replenishment k ≤ R) (m : ℕ) :
+    (hinflow : ∀ m, ∑ k ∈ Finset.range m, A.inflow k ≤ R) (m : ℕ) :
     A.queue m ≤ A.queue 0 + P + R :=
   A.queue_le_of_initialPotential_and_cumulativeReplenishment_bounds
-    (hpotential 0) hreplenishment m
+    (hpotential 0) hinflow m
+
+end FiniteAmortizedBalance
+
+/-! ## Stable-throughput regression -/
+
+/-- A stable balance with one unit entering and leaving at every step. -/
+def stableUnitThroughputBalance : FiniteAmortizedBalance where
+  queue _ := 0
+  potential _ := 0
+  outflow _ := 1
+  inflow _ := 1
+  step_conservation _ := by simp
+
+/-- The stable-throughput queue is identically zero. -/
+theorem stableUnitThroughputBalance_queue (k : ℕ) :
+    stableUnitThroughputBalance.queue k = 0 := rfl
+
+/-- Conservation in the stable-throughput example is exact. -/
+theorem stableUnitThroughputBalance_step_exact (k : ℕ) :
+    stableUnitThroughputBalance.queue (k + 1) +
+        stableUnitThroughputBalance.potential (k + 1) +
+          stableUnitThroughputBalance.outflow k =
+      stableUnitThroughputBalance.queue k +
+        stableUnitThroughputBalance.potential k +
+          stableUnitThroughputBalance.inflow k := by
+  rfl
 
-end FiniteAmortizedResource
+/-- No finite constant bounds every cumulative inflow prefix, even though the
+queue is uniformly zero. -/
+theorem stableUnitThroughputBalance_no_cumulativeInflow_bound :
+    ¬ ∃ R, ∀ m, ∑ k ∈ Finset.range m,
+      stableUnitThroughputBalance.inflow k ≤ R := by
+  rintro ⟨R, hR⟩
+  have h := hR (R + 1)
+  simp [stableUnitThroughputBalance] at h
 
 end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean
index e46e2e80..df465e4d 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean
@@ -164,6 +164,68 @@ theorem pathWeight_nonpos_of_signature_eq
 
 end RelationalFiniteSignedTransitionPotentialCertificate
 
+/-! ## Conditional canonical-block projection -/
+
+/-- A canonical signed window is the corresponding consecutive range sum. -/
+theorem canonicalWindowDriftInt_add_eq_sum_range
+    (n : OddNat) (q length : ℕ) :
+    canonicalWindowDriftInt n q (q + length) =
+      ∑ i ∈ Finset.range (length + 1), endpointAccountingTerm n (q + i) := by
+  induction length with
+  | zero => simp [canonicalWindowDriftInt_self]
+  | succ length ih =>
+      change canonicalWindowDriftInt n q ((q + length) + 1) = _
+      rw [canonicalWindowDriftInt_succ n (by omega), if_pos (by omega), ih]
+      conv_rhs => rw [Finset.sum_range_succ]
+      congr 2
+
+/-- A sound relational finite projection of all canonical successor edges
+bounds every canonical signed window. -/
+theorem relationalFiniteSignedCertificate_canonicalWindowDrift_le
+    {Signature : Type*} [Fintype Signature]
+    (n : OddNat)
+    (C : RelationalFiniteSignedTransitionPotentialCertificate ℕ Signature)
+    (hstep : ∀ k, C.Step k (k + 1))
+    (hweight : ∀ k, C.actualWeight k (k + 1) = endpointAccountingTerm n k)
+    {q m : ℕ} (hqm : q ≤ m) :
+    canonicalWindowDriftInt n q m ≤ C.bound := by
+  let length := m - q + 1
+  have hm : q + (m - q) = m := Nat.add_sub_of_le hqm
+  have hpath : C.IsPath (fun k => k) q length := by
+    intro i hi
+    simpa [length, add_assoc] using hstep (q + i)
+  have hbound := C.pathWeight_le_bound (fun k => k) q length hpath
+  unfold RelationalFiniteSignedTransitionPotentialCertificate.pathWeight at hbound
+  simp only [hweight] at hbound
+  rw [← canonicalWindowDriftInt_add_eq_sum_range n q (m - q), hm] at hbound
+  exact hbound
+
+/-- A sound canonical finite signed projection yields a uniform reflected-queue
+bound without choosing its signature from an assumed queue ceiling. -/
+theorem relationalFiniteSignedCertificate_to_queueUniformUpperBound
+    {Signature : Type*} [Fintype Signature]
+    (n : OddNat)
+    (C : RelationalFiniteSignedTransitionPotentialCertificate ℕ Signature)
+    (hstep : ∀ k, C.Step k (k + 1))
+    (hweight : ∀ k, C.actualWeight k (k + 1) = endpointAccountingTerm n k) :
+    CanonicalOutstandingClaimQueueUniformUpperBound n C.bound := by
+  rw [canonicalOutstandingClaimQueueUniformUpperBound_iff_all_windowDrift_le]
+  intro m q hqm
+  exact relationalFiniteSignedCertificate_canonicalWindowDrift_le
+    n C hstep hweight hqm
+
+/-- The same sound finite projection gives the translated endpoint-width
+ceiling. -/
+theorem relationalFiniteSignedCertificate_to_endpointWidthUniformUpperBound
+    {Signature : Type*} [Fintype Signature]
+    (n : OddNat)
+    (C : RelationalFiniteSignedTransitionPotentialCertificate ℕ Signature)
+    (hstep : ∀ k, C.Step k (k + 1))
+    (hweight : ∀ k, C.actualWeight k (k + 1) = endpointAccountingTerm n k) :
+    CanonicalEndpointWidthUniformUpperBound n (bitWidth n.1 + C.bound) :=
+  (relationalFiniteSignedCertificate_to_queueUniformUpperBound
+    n C hstep hweight).to_endpointWidthUniformUpperBound
+
 namespace FiniteSignedTransitionPotentialCertificate
 
 variable {State Signature : Type*} [Fintype Signature]
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmortizedResource.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmortizedResource.lean
index c39e3167..a8dd9538 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmortizedResource.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmortizedResource.lean
@@ -30,10 +30,10 @@ abbrev CanonicalAmortizedResourceTransition (_n : OddNat) :=
 canonical reflected queue.  It intentionally makes no ownership claim. -/
 def CanonicalAbstractAmortizationCertificate
     (n : OddNat) (P R : ℕ) : Prop :=
-  ∃ A : FiniteAmortizedResource,
+  ∃ A : FiniteAmortizedBalance,
     (∀ m, A.queue m = canonicalOutstandingClaimQueue n m) ∧
       A.potential 0 ≤ P ∧
-        ∀ m, ∑ k ∈ Finset.range m, A.replenishment k ≤ R
+        ∀ m, ∑ k ∈ Finset.range m, A.inflow k ≤ R
 
 /-- Deprecated compatibility alias.  Despite its historical name, this
 predicate is not noncircular; see
@@ -62,15 +62,39 @@ theorem CanonicalAbstractAmortizationCertificate.to_endpointWidthUniformUpperBou
       (bitWidth n.1 + (canonicalOutstandingClaimQueue n 0 + P + R)) :=
   h.to_queueUniformUpperBound.to_endpointWidthUniformUpperBound
 
+namespace CanonicalNoncircularGlobalAmortizationLaw
+
+/-- Deprecated fully qualified wrapper for the former public theorem. -/
+@[deprecated CanonicalAbstractAmortizationCertificate.to_queueUniformUpperBound
+  (since := "2026-07-16")]
+theorem to_queueUniformUpperBound
+    {n : OddNat} {P R : ℕ}
+    (h : CanonicalAbstractAmortizationCertificate n P R) :
+    CanonicalOutstandingClaimQueueUniformUpperBound n
+      (canonicalOutstandingClaimQueue n 0 + P + R) :=
+  CanonicalAbstractAmortizationCertificate.to_queueUniformUpperBound h
+
+/-- Deprecated fully qualified wrapper for the former public theorem. -/
+@[deprecated CanonicalAbstractAmortizationCertificate.to_endpointWidthUniformUpperBound
+  (since := "2026-07-16")]
+theorem to_endpointWidthUniformUpperBound
+    {n : OddNat} {P R : ℕ}
+    (h : CanonicalAbstractAmortizationCertificate n P R) :
+    CanonicalEndpointWidthUniformUpperBound n
+      (bitWidth n.1 + (canonicalOutstandingClaimQueue n 0 + P + R)) :=
+  CanonicalAbstractAmortizationCertificate.to_endpointWidthUniformUpperBound h
+
+end CanonicalNoncircularGlobalAmortizationLaw
+
 /-- Reverse construction exposing the circular complement potential. -/
 noncomputable def trivialAmortizedTransitionOfQueueBound
     {n : OddNat} {C : ℕ}
     (hC : CanonicalOutstandingClaimQueueUniformUpperBound n C) :
-    FiniteAmortizedResource where
+    FiniteAmortizedBalance where
   queue k := canonicalOutstandingClaimQueue n k
   potential k := C - canonicalOutstandingClaimQueue n k
-  consumed _ := 0
-  replenishment _ := 0
+  outflow _ := 0
+  inflow _ := 0
   step_conservation k := by
     have hk := hC k
     have hks := hC (k + 1)
@@ -154,6 +178,62 @@ theorem canonicalOutstandingClaimQueue_add_consumed
         rw [Nat.min_eq_left hle, Nat.sub_eq_zero_of_le hle]
         simp
 
+/-- The queue before the initial block is empty. -/
+@[simp] theorem canonicalOutstandingClaimQueueBeforeBlock_zero (n : OddNat) :
+    canonicalOutstandingClaimQueueBeforeBlock n 0 = 0 := rfl
+
+/-- Before successor block `k+1`, the queue is the queue after block `k`. -/
+@[simp] theorem canonicalOutstandingClaimQueueBeforeBlock_succ
+    (n : OddNat) (k : ℕ) :
+    canonicalOutstandingClaimQueueBeforeBlock n (k + 1) =
+      canonicalOutstandingClaimQueue n k := rfl
+
+/-- The exact canonical reflected queue as a neutral scalar balance. -/
+noncomputable def canonicalQueueFiniteAmortizedBalance
+    (n : OddNat) : FiniteAmortizedBalance where
+  queue := canonicalOutstandingClaimQueueBeforeBlock n
+  potential _ := 0
+  outflow := canonicalQueueConsumed n
+  inflow := canonicalQueueDemand n
+  step_conservation k := by
+    simp only [canonicalOutstandingClaimQueueBeforeBlock_succ]
+    exact (canonicalOutstandingClaimQueue_add_consumed n k).le
+
+/-! ## Exact unused service -/
+
+/-- Capacity not used by the reflected queue in canonical block `k`. -/
+noncomputable def canonicalQueueUnusedService (n : OddNat) (k : ℕ) : ℕ :=
+  canonicalQueueService n k - canonicalQueueConsumed n k
+
+/-- Actual consumption never exceeds current service capacity. -/
+theorem canonicalQueueConsumed_le_service (n : OddNat) (k : ℕ) :
+    canonicalQueueConsumed n k ≤ canonicalQueueService n k := by
+  exact min_le_right _ _
+
+/-- Actual consumption never exceeds available old and new work. -/
+theorem canonicalQueueConsumed_le_available (n : OddNat) (k : ℕ) :
+    canonicalQueueConsumed n k ≤
+      canonicalOutstandingClaimQueueBeforeBlock n k + canonicalQueueDemand n k := by
+  exact min_le_left _ _
+
+/-- Service partitions exactly into consumed and unused capacity. -/
+theorem canonicalQueueService_eq_consumed_add_unusedService
+    (n : OddNat) (k : ℕ) :
+    canonicalQueueService n k =
+      canonicalQueueConsumed n k + canonicalQueueUnusedService n k := by
+  unfold canonicalQueueUnusedService
+  exact (Nat.add_sub_of_le (canonicalQueueConsumed_le_service n k)).symm
+
+/-- The post-block queue is available work minus actual consumption. -/
+theorem canonicalOutstandingClaimQueue_eq_available_sub_consumed
+    (n : OddNat) (k : ℕ) :
+    canonicalOutstandingClaimQueue n k =
+      canonicalOutstandingClaimQueueBeforeBlock n k + canonicalQueueDemand n k -
+        canonicalQueueConsumed n k := by
+  have hconserve := canonicalOutstandingClaimQueue_add_consumed n k
+  have hle := canonicalQueueConsumed_le_available n k
+  omega
+
 /-!
 ## Owned-resource frontier
 
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-330.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-330.md
index 4c5b261d..521acf9a 100644
--- a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-330.md
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-330.md
@@ -96,9 +96,10 @@ together with disjoint ownership, injective consumption, unique temporal
 origin, and temporal nonreuse.  Without those data, local saturated-successor
 discharge is not formally connected to global amortization.
 
-The next admissible step is therefore carrier discovery, not another scalar
-potential predicate.  Any proposed owned law must be audited against the same
-reverse construction before it is accepted.
+Carrier discovery is one admissible route, but checkpoint 331 records two
+others: a sound finite signed-transition potential and a bounded repayment-lag
+theorem.  Any proposed scalar or owned law must still be audited against the
+same reverse construction before it is accepted.
 
 ## Verification
 
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-331.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-331.md
new file mode 100644
index 00000000..cd3b72ad
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-331.md
@@ -0,0 +1,140 @@
+# Petal / FloatWindow implementation report - checkpoint 331
+
+## Result
+
+The remaining amortization overrestriction has been removed.  Uniformly
+bounded cumulative inflow is sufficient but not necessary for a bounded
+queue.  The correct generic control is bounded cumulative net inflow after
+outflow is retained.
+
+This checkpoint also constructs the exact canonical scalar balance, connects
+the existing finite signed-transition certificate to canonical windows and
+queue bounds, and proves a generic bounded repayment-lag theorem.
+
+## Strong balance telescope
+
+The generic structure is now named `FiniteAmortizedBalance`, with neutral
+fields `inflow` and `outflow`.  The old resource name remains an alias only.
+Lean proves the full telescope:
+
+```text
+queue m + potential m + sum(outflow, range m)
+  <= queue 0 + potential 0 + sum(inflow, range m).
+```
+
+Consequently, if
+
+```text
+sum(inflow, range m) <= sum(outflow, range m) + B
+```
+
+for every prefix, then
+
+```text
+queue m <= queue 0 + potential 0 + B.
+```
+
+Only the initial potential is used.
+
+## Stable-throughput regression
+
+Lean verifies the abstract transition
+
+```text
+queue = 0, potential = 0, outflow = 1, inflow = 1.
+```
+
+Its conservation law is exact and its queue is uniformly zero, while no
+finite constant bounds all cumulative inflow sums.  This formally disproves
+the necessity of bounded total inflow for queue stability.
+
+## Exact canonical scalar balance
+
+`canonicalQueueFiniteAmortizedBalance n` uses:
+
+```text
+queue     = queue before block
+potential = 0
+outflow   = actual consumed service
+inflow    = block demand.
+```
+
+The exact reflected-queue identity proves its step law.  Unused service is
+also explicit, with the proved scalar identities:
+
+```text
+consumed <= service
+consumed <= queueBefore + demand
+service = consumed + unusedService
+queueAfter = queueBefore + demand - consumed.
+```
+
+These are scalar accounting facts and do not assert claim ownership.
+
+## Finite signed-transition route
+
+The relational certificate now has a canonical application theorem.  Given a
+fixed finite signature certificate whose relation contains every edge
+`k -> k+1` and whose actual edge weight is exactly
+`endpointAccountingTerm n k`, Lean proves:
+
+```text
+every canonical window drift <= certificate.bound
+canonical outstanding queue <= certificate.bound
+canonical endpoint width <= bitWidth n + certificate.bound.
+```
+
+The first missing Collatz theorem on this route is a concrete finite signature
+with a sound projected upper edge weight and bounded potential.  Existing
+low-bit collision evidence rules out exact deterministic recovery, but does
+not by itself rule out a nondeterministic upper-weight projection.
+
+## Bounded repayment-lag route
+
+`BoundedRepaymentLag.lean` proves the generic implication:
+
+```text
+all outstanding work lies among the previous L arrival slots
+each slot creates at most A arrivals
+------------------------------------------------------------
+queue m <= L * A.
+```
+
+The first missing Collatz theorem is a uniform lag for all actual canonical
+claims.  Current saturated-successor results repay selected local subclasses,
+but do not provide such a global lag.
+
+## Owned-carrier route
+
+The first missing theorem remains a recursive source-bearing claim carrier
+whose consumption preserves source identity and temporal nonreuse, and whose
+cardinality agrees with the scalar reflected queue.  No such existence claim
+is made in this checkpoint.
+
+## Route comparison
+
+The three noncircular routes are now separate:
+
+1. finite signed transition: missing a sound finite canonical signature;
+2. bounded repayment lag: missing a uniform canonical claim-lag theorem;
+3. owned upper resource: missing a temporally coherent recursive carrier.
+
+None is currently proved uniquely necessary.  The first route now has the
+shortest complete conditional chain to endpoint width; the latter two retain
+more claim-level information if their Collatz-specific obligations can be
+proved.
+
+## Verification
+
+All required gates passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmortizedResource
+lake build DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition
+lake build DkMath.Collatz.PetalBridge.FloatWindow
+lake build DkMath
+git diff --check
+```
+
+All changed FloatWindow Lean files remain free of `sorry` and local heartbeat
+overrides.
````
`````
