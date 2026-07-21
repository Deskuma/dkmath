# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.FloatWindow.FiniteAmortizedResource

gch: ff1ada0d61ce5da722c5d71ad8de4527468487ce

## Report

(11m20s)

checkpoint 330 を完了しました。

**確定した事実**

- 旧 amortization law は非循環ではありませんでした。
- queue 上界 `C` から `potential k := C - queue k` を構成可能です。
- Lean で次の存在同値が成立しました。

```text
抽象 amortization certificate が存在
  ↔
canonical queue の一様上界が存在
```

したがって旧 predicate は問題を簡約せず、目標を potential に符号化していました。

**有効な成果**

- Collatz 非依存の `FiniteAmortizedResource` を新設
- phantom state を除去
- 鋭い telescope bound を証明

```text
queue m ≤ queue 0 + potential 0 + cumulativeReplenishment m
```

- canonical demand/service/consumed を定義
- reflected queue の厳密保存則を証明

```text
queueAfterBlock k + consumed k
  = queueBeforeBlock k + demand k
```

**Canonical 回帰**

奇数根 `23` の第0 block について Lean が以下を証明しました。

```text
block length = 3
odd core = 3
core words = 53, 35, 23
claim depths = {1, 3}
claim holes = {2}
```

これにより、canonical block 内でも carry の単調性は成立しないことが確定しました。ただし、residue・odd core・block width を併用する密度定理までは否定していません。

**現在の真正な停止点**

不足しているのは、初期値 `n` から独立に構成される具体的 resource carrier です。今後は consumed atom の一意所有、replenishment の発生源、時間方向の非再利用を証明する必要があります。scalar potential を追加するだけでは先へ進めません。

全 focused build、公開 `FloatWindow`、トップレベル `DkMath`、`git diff --check` が成功しています。変更対象に `sorry` と `maxHeartbeats` はありません。

詳細: [report-petal-330.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-330.md)

## Review

## cp-330 実装レビュー

## 結論

**条件付き採用。循環性監査と canonical queue 保存則は全面採用じゃ。**

cp-330 は、前 checkpoint の誤った「非循環」解釈を Lean 上で正式に撤回した。

$$\exists P,R,\ \operatorname{AbstractAmortizationCertificate}(P,R)\iff\exists C,\ \operatorname{QueueUniformUpperBound}(C)$$

が証明されたため、旧 amortization law は問題を簡約せず、queue 上界を complement potential に埋め込んでいただけだったことが確定した。

同時に、

- Collatz 非依存の scalar telescope
- exact canonical demand / service / consumed
- block ごとの reflected queue 保存則
- root $23$ における canonical carry alternation

が正しく実装された。

ただし、report の、

> 次は初期値から有限 upper-resource carrier を発見する

という停止診断は、**ownership route の停止点としては正しいが、唯一の次路ではない**。

さらに、現在の generic telescope は累積 `consumed` を落としているため、

> 累積 replenishment が有界でなければ queue を抑えられない

ように見えてしまう。

これは強すぎる。安定して無限に demand と service が流れる正常な queue では、累積 inflow は無限でも queue は有界だからじゃ。

---

## 1. Snapshot 検証

最新 snapshot、

```text
__snapshot-dk_math-lean-code-260716-1648.tar.gz
```

の SHA-256 は、提示された、

```text
69d2786fc502f1009b2b398a400590e9f9288000097dc354c199743536fe6e11
```

と一致した。

snapshot 内の、

- `UniversalPaymentScalarQueue.lean`
- `UniversalPaymentAmplitude.lean`
- `FiniteSignedTransition.lean`
- `PatternLedger.lean`
- `DriftBridge.lean`
- `TailGrammar.lean`

まで照合した。

---

## 2. 循環性 regression

```lean
trivialAmortizedTransitionOfQueueBound
```

は、前回指摘した逆構成をそのまま閉じている。

queue ceiling を $Q_k\le C$ とすると、

$$P_k=C-Q_k$$

と置ける。

すると、

$$Q_k+P_k=C$$

なので、一段保存則は自明になる。

`demand`、actual resource、ownership を何も用いずに certificate が作れるため、旧 predicate が非循環ではなかったという判定は完全に正しい。

```lean
exists_abstractAmortizationCertificate_iff_exists_queueUniformUpperBound
```

は今後も semantic regression として残すべき重要 theoremじゃ。

新しい potential / resource law を作るたびに、この逆構成が再び成立しないかを検査できる。

---

## 3. `FiniteAmortizedResource`

phantom な、

```lean
State
state
```

を除去したのは正しい。

新 structure は純粋に、

```lean
queue
potential
consumed
replenishment
step_conservation
```

だけを持つ。

この層はもはや Collatz theorem ではなく、有限非負列の telescope lemma じゃ。

```lean
queue_add_potential_le_initial_add_sum
```

および、

```lean
queue_le_initial_add_potential_add_cumulativeReplenishment
```

は正しい。

また、必要なのが全時刻の potential ceiling ではなく、

$$P_0\le P$$

だけであることを API に反映した点もよい。

---

## 4. Exact canonical queue observable

今回定義された、

```lean
canonicalOutstandingClaimQueueBeforeBlock
canonicalQueueDemand
canonicalQueueService
canonicalQueueConsumed
```

の indexing は正しい。

`canonicalOutstandingClaimQueue n k` は block $k$ の service 後の queue。

一方、

```lean
canonicalOutstandingClaimQueueBeforeBlock n 0 = 0
```

```lean
canonicalOutstandingClaimQueueBeforeBlock n (k + 1)
  = canonicalOutstandingClaimQueue n k
```

である。

したがって block $k$ の exact conservation は、

$$Q_{\mathrm{after},k}+C_k=Q_{\mathrm{before},k}+A_k$$

となる。

Lean theorem、

```lean
canonicalOutstandingClaimQueue_add_consumed
```

は、この reflected subtraction の exact 分解を正しく証明している。

ここで、

$$C_k=\min(Q_{\mathrm{before},k}+A_k,\ S_k)$$

なので、service が不足すると全 service を使い、service が余ると全 available claims を消費する。

---

## 5. 名前の補強

現在の theorem 名、

```lean
canonicalOutstandingClaimQueue_add_consumed
```

だけでは、左右の queue が before / after のどちらか分かりにくい。

互換性を維持した wrapper として、

```lean
canonicalQueueAfterBlock_add_consumed_eq_beforeBlock_add_demand
```

を追加するとよい。

また次の simp theorem も公開した方がよい。

```lean
@[simp] theorem canonicalOutstandingClaimQueueBeforeBlock_zero

@[simp] theorem canonicalOutstandingClaimQueueBeforeBlock_succ

theorem canonicalOutstandingClaimQueueBeforeBlock_succ_eq_afterBlock
```

今後の carrier transition の証明がかなり読みやすくなる。

---

## 6. Canonical carry alternation regression

root $23$ の第 $0$ block について、

$$L=3$$

$$u=3$$

$$W_1=53,\qquad W_2=35,\qquad W_3=23$$

が証明された。

claim profile は、

$$\operatorname{Claims}={1,3}$$

$$\operatorname{Holes}={2}$$

じゃ。

これは abstract な数値反例ではなく、実 canonical block 内で、

$$2\longrightarrow1\longrightarrow2$$

という carry alternation が発生することを示す。

report が、

> monotone carry は否定されたが、追加の residue・width 情報を使う density theorem までは否定していない

と境界を修正したのも正確じゃ。

---

## 7. 重要な不足：累積 `consumed` を保持した telescope

現在の telescope は、各段の `consumed` を途中で捨てている。

しかし一段保存則は、

$$Q_{k+1}+P_{k+1}+C_k\le Q_k+P_k+R_k$$

じゃ。

これを正確に累積すれば、本来は、

$$Q_m+P_m+\sum_{k<m}C_k\le Q_0+P_0+\sum_{k<m}R_k$$

が得られる。

この theorem の方が一段強い。

```lean
theorem queue_add_potential_add_sumConsumed_le_initial_add_sumReplenishment
    (A : FiniteAmortizedResource) (m : ℕ) :
    A.queue m + A.potential m +
        ∑ k ∈ Finset.range m, A.consumed k ≤
      A.queue 0 + A.potential 0 +
        ∑ k ∈ Finset.range m, A.replenishment k
```

これにより、必要な仮定は「replenishment 総量が有限」ではなく、

$$\sum_{k<m}R_k\le\sum_{k<m}C_k+B$$

という **累積 net inflow 上界**まで弱められる。

すると、

$$Q_m\le Q_0+P_0+B$$

が得られる。

---

## 8. Cumulative replenishment ceiling は必要条件ではない

次の安定 queue を考える。

```text
queue k         = 0
potential k     = 0
consumed k      = 1
replenishment k = 1
```

各段で、

$$0+0+1=0+0+1$$

なので保存則は完全に成立する。

queue は常に $0$ で一様有界。

しかし、

$$\sum_{k<m}\operatorname{replenishment}(k)=m$$

なので、有限定数 $R$ による累積上界は存在しない。

つまり、

```text
cumulative replenishment is uniformly bounded
```

は queue boundedness に必要ではない。

必要なのは、inflow が consumption をどれだけ上回るかという **net surplus** の上界じゃ。

この abstract regression も Lean に固定すべきである。

---

## 9. `replenishment` は実質的に `inflow`

canonical queue を generic telescope に入れる場合、自然な instance は次になる。

```lean
queue         := canonicalOutstandingClaimQueueBeforeBlock n
potential     := 0
consumed      := canonicalQueueConsumed n
replenishment := canonicalQueueDemand n
```

なぜなら、

$$Q_{k+1}+C_k=Q_k+A_k$$

だからじゃ。

この instance では `replenishment` は resource の再補充ではなく、**新しく到着した claim demand** になっている。

したがって generic structure では、

```text
replenishment
```

より、

```text
inflow
```

または、

```text
input
```

の方が意味に合う。

`FiniteAmortizedResource` という名称も少し強い。

中立名としては、

```lean
FiniteAmortizedBalance
```

がより正確じゃ。

既存名は alias として残せる。

---

## 10. Canonical scalar instance を作るべき

次には、exact queue conservation を generic structure の実 instance として package すべきである。

```lean
noncomputable def canonicalQueueFiniteAmortizedBalance
    (n : OddNat) : FiniteAmortizedResource where
  queue := canonicalOutstandingClaimQueueBeforeBlock n
  potential := fun _ => 0
  consumed := canonicalQueueConsumed n
  replenishment := canonicalQueueDemand n
  step_conservation := by
    intro k
    simpa using canonicalOutstandingClaimQueue_add_consumed n k
```

これで generic telescope と canonical queue が初めて正式に接続される。

現在は exact conservation theorem が存在するだけで、`FiniteAmortizedResource` の canonical instance 自体はまだない。

---

## 11. 「具体的 initial upper carrier」は唯一の次路ではない

report の ownership 問題は本物じゃ。

しかし snapshot 内の `UniversalPaymentScalarQueue.lean` は、残る数学入力を既に四種類へ分けている。

```text
uniform signed-suffix estimate
uniform repayment-lag theorem
exclusion of a pumpable positive transition cycle
finite-state obstruction forcing discharge
```

したがって、次の道は少なくとも三本ある。

### Ownership route

actual carrier を構成し、atom の消費と非再利用を証明する。

### Bounded-lag route

全 claim が一定 block 数以内に service されることを示し、queue の年齢を抑える。

### Finite signed-transition route

有限 signature と bounded potential によって、全 path drift を抑える。

既存の、

```lean
RelationalFiniteSignedTransitionPotentialCertificate
```

は既に、

$$\operatorname{pathWeight}\le\operatorname{bound}$$

を証明している。

したがって、これを canonical block driftへ接続できれば、そのまま、

```lean
CanonicalOutstandingClaimQueueUniformUpperBound
```

が得られる。

---

## 12. Finite signed transition との未接続 bridge

既存 module には、

```lean
RelationalFiniteSignedTransitionPotentialCertificate.pathWeight_le_bound
```

がある。

一方 scalar queue 側には、

```lean
canonicalOutstandingClaimQueueUniformUpperBound_iff_all_windowDrift_le
```

がある。

この二つを結ぶ conditional theorem がまだない。

必要なのは概ね次じゃ。

```lean
theorem canonicalQueueUniformUpperBound_of_relationalFiniteCertificate
    {Signature : Type*} [Fintype Signature]
    (C : RelationalFiniteSignedTransitionPotentialCertificate
      ℕ Signature)
    (hstep : ∀ k, C.Step k (k + 1))
    (hweight : ∀ k,
      C.actualWeight k (k + 1) = endpointAccountingTerm n k) :
    CanonicalOutstandingClaimQueueUniformUpperBound n C.bound
```

証明は、

$$\operatorname{WindowDrift}(q,m)=\operatorname{pathWeight}(q,m-q+1)$$

と書き、`pathWeight_le_bound` を使うだけじゃ。

これは非循環な challenge-facing bridge になる。

有限 certificate の存在自体は未証明でも、

> 何を構成すれば queue bound が得られるか

を exact theorem として固定できる。

---

## 13. Low-bit signature failure の意味

既存 `FiniteSignedTransition.lean` では、cp-317 の audit により、

- 同じ low-bit signature から異なる drift
- 同じ signature から複数 successor

が見つかっている。

したがって deterministic exact automaton は失敗した。

しかし既存 module が正しく述べる通り、これは、

```text
nondeterministic sound over-approximation
```

まで否定しない。

必要なのは、

$$\operatorname{actualWeight}\le\operatorname{projectedUpperWeight}$$

と、

$$\operatorname{projectedUpperWeight}(s,t)\le\Phi(t)-\Phi(s)$$

じゃ。

次に探索すべき signature は drift を完全復元する必要はない。

**上から支配できればよい。**

---

## 14. Source-bearing queue carrier

ownership route を進めるなら、いきなり upper-zero bit carrier を探すより先に、canonical claims 自身から actual outstanding queue を作る方が自然じゃ。

各 block で、

```text
old outstanding claims
⊕ new block claims
```

を作り、capacity slots で可能なだけ消費する。

次 queue は、消費 image の補集合として定義する。

これにより、

- claim の block index
- source time
- arrival origin
- consumed / unconsumed
- 一度消費された claim の非再利用

を全て保持できる。

cardinality は scalar queue と一致する。

これは初期 upper resource ではなく、**actual debt ownership carrier**じゃ。

この carrier があれば、bounded repayment lag や claim age を直接定義できる。

---

## 15. 真の次戦線

cp-330 で確定したものは、

```text
arbitrary scalar potential は循環する
```

という否定と、

```text
canonical queue は exact demand/service conservation を持つ
```

という肯定じゃ。

次に必要なのは、直ちに「有限初期資源」を仮定することではない。

まず、

```text
inflow - consumed の net telescope
actual outstanding claim ownership
bounded repayment lag
finite signed transition certificate
```

のいずれが既存 grammar と最も強く接続できるかを Lean で比較する段階じゃ。

---

## 判定まとめ

### Circularity regression

**完成。全面採用。**

### Generic scalar telescope

**完成。ただし cumulative consumed を保持する強化余地あり。**

### Initial-potential bound

**完成。**

### Canonical demand / service / consumed

**完成。**

### Exact block conservation

**完成。**

### Canonical carry alternation

**完成。**

### Cumulative replenishment ceiling

**queue boundedness の必要条件ではない。意味修正が必要。**

### Concrete initial upper resource

**未実装。ただし唯一の次路ではない。**

### 最優先候補

**net-flow telescope、canonical scalar instance、finite signed certificate bridge、actual outstanding claim carrier。**

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge FloatWindow branch after
report-petal-330.

The cp-330 circularity audit, generic telescope, exact canonical queue
observables, and canonical carry-alternation regression are accepted.

The next checkpoint must correct one remaining semantic overrestriction:

    a uniformly bounded cumulative replenishment stream is sufficient for a
    queue bound, but it is not necessary.

Stable systems may have infinite cumulative inflow and infinite cumulative
consumption while the outstanding queue remains uniformly bounded.

Do not treat discovery of a finite initial upper-resource carrier as the only
admissible next route.

## Stage A — cumulative consumed telescope

Strengthen `FiniteAmortizedResource` with:

    queue m + potential m + sum consumed over range m
      <=
    queue 0 + potential 0 + sum replenishment over range m.

Prove this by induction without discarding the consumed terms.

Keep the existing weaker telescope as a corollary.

## Stage B — bounded net-inflow corollary

Prove:

    if for every m,

      sum replenishment over range m
        <=
      sum consumed over range m + B,

    then:

      queue m <= queue 0 + potential 0 + B.

Add the bounded initial-potential wrapper if useful.

This is the correct amortized surplus theorem.

## Stage C — throughput regression

Define an abstract stable transition:

    queue k         = 0
    potential k     = 0
    consumed k      = 1
    replenishment k = 1.

Prove:

    queue is uniformly zero;

    the one-step conservation is exact;

    no finite R bounds all cumulative replenishment sums.

Record explicitly:

    cumulative replenishment boundedness is not necessary for queue
    boundedness.

## Stage D — neutral terminology

Add neutral aliases or rename the generic fields:

    replenishment -> inflow
    consumed      -> outflow

and preferably:

    FiniteAmortizedResource -> FiniteAmortizedBalance.

Compatibility aliases may remain.

Do not use the generic scalar type as evidence of actual resource ownership.

## Stage E — canonical scalar instance

Construct:

    canonicalQueueFiniteAmortizedBalance n

with:

    queue         = canonicalOutstandingClaimQueueBeforeBlock n
    potential     = 0
    consumed      = canonicalQueueConsumed n
    inflow        = canonicalQueueDemand n.

Prove the step law by the exact theorem:

    canonicalOutstandingClaimQueue_add_consumed.

Add simp theorems for:

    queueBeforeBlock 0;
    queueBeforeBlock (k + 1);
    queueBeforeBlock (k + 1) = queueAfterBlock k.

## Stage F — exact unused service

Define:

    canonicalQueueUnusedService n k :=
      canonicalQueueService n k - canonicalQueueConsumed n k.

Prove:

    consumed <= service;

    consumed <= queueBefore + demand;

    service = consumed + unusedService;

    queueAfter = queueBefore + demand - consumed.

These are scalar identities only.

## Stage G — finite signed certificate to queue bridge

Using the existing
`RelationalFiniteSignedTransitionPotentialCertificate`, prove a conditional
bridge from a sound canonical block projection to the queue bound.

The bridge should assume:

    every adjacent canonical block pair satisfies `Step`;

    actual edge weight on k -> k+1 equals
      endpointAccountingTerm n k.

Then prove:

    every canonical window drift <= certificate.bound;

    CanonicalOutstandingClaimQueueUniformUpperBound n certificate.bound;

    the corresponding endpoint-width uniform bound.

This theorem must not existentially choose the signature type from an assumed
queue bound.

## Stage H — candidate signature audit

Audit finite candidate signatures only after Stage G fixes the exact
obligations.

Begin with combinations of already proved finite data:

    residue modulo 8, 16, 32, or 64;
    upper carry;
    clipped terminal valuation;
    saturated / nonsaturated tag;
    zero / positive / negative drift tag;
    deepest-hole flag;
    tight valuation-one flag.

The signature does not need to recover exact drift or a deterministic
successor.  It only needs a sound projected upper edge weight.

Record explicit collision witnesses when a candidate cannot support a bounded
potential.

## Stage I — generic actual outstanding-claim carrier

In a separate module, design a source-bearing reflected queue.

At block k, form:

    previous outstanding claims
      Sum
    new actual claim carrier.

Use the actual canonical capacity-slot carrier to consume as many claims as
possible.

Define the next outstanding carrier as the complement of the consumed image.

Required invariants:

    every outstanding element retains its original block and source address;

    consumed and outstanding claims are disjoint;

    a consumed claim never reappears;

    cardinality equals the scalar reflected queue.

The local choice may be noncomputable, but the transition must be recursive
and temporally coherent.  Do not independently rematch the whole historical
window at every endpoint.

## Stage J — bounded repayment-lag theorem

Prove a generic theorem:

    if every actual claim is consumed within at most L later blocks
    and each block creates at most A claims,
    then the outstanding queue is bounded by an explicit function of A and L.

Keep this theorem independent of Collatz.

Then audit whether existing residue and saturated-successor grammar proves such
a lag for any nontrivial claim subclass.

Do not claim a uniform Collatz lag without a theorem.

## Stage K — route comparison

At the end of the checkpoint, compare three genuinely noncircular routes:

    finite signed-transition potential;
    bounded repayment lag;
    concrete owned upper-boundary resource.

For each route state the first missing Collatz-specific theorem.

Do not declare the owned upper-resource route uniquely necessary.

## Stage L — compatibility surface

The deprecated alias for
`CanonicalNoncircularGlobalAmortizationLaw` preserves the predicate name, but
audit whether old fully qualified theorem names also require deprecated
wrappers:

    CanonicalNoncircularGlobalAmortizationLaw.to_queueUniformUpperBound
    CanonicalNoncircularGlobalAmortizationLaw.to_endpointWidthUniformUpperBound.

Add wrappers only if they were part of the public surface.

## Stopping rule

Stop at the first genuine obstruction among:

    the stronger telescope with cumulative consumed fails;
    the stable-throughput regression cannot be expressed;
    the canonical scalar instance has an indexing mismatch;
    the finite signed certificate cannot be connected to window drift;
    every tested finite signature admits a positive closed-signature path;
    a recursive actual claim carrier cannot preserve source identity;
    bounded repayment lag cannot be connected to any existing grammar.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-331.md
```

cp-330 は、偽の resource law を正しく壊した。

次は「有限資源があるはず」と先に置くのではなく、**流入と消費の差、claim の年齢、有限 signature の正 drift cycle**という三つの具体的な敵を並べて裁く段階じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
index 4c7a4327..f4770a5f 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
@@ -26,6 +26,7 @@ import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPrimitiveExcursion
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentSaturatedSuccessor
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentSelectedCarrier
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude
+import DkMath.Collatz.PetalBridge.FloatWindow.FiniteAmortizedResource
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmortizedResource
 import DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition

diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteAmortizedResource.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteAmortizedResource.lean
new file mode 100644
index 00000000..a2128411
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteAmortizedResource.lean
@@ -0,0 +1,78 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import Mathlib.Algebra.Order.Ring.Nat
+import Mathlib.Algebra.BigOperators.Group.Finset.Basic
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.FiniteAmortizedResource"
+
+namespace DkMath.Collatz
+
+/-!
+# Finite amortized resource telescope
+
+This module is deliberately independent of the Collatz observables.  It only
+records a scalar queue, a scalar potential, consumed mass, replenishment, and
+one-step conservation.  In particular, there is no phantom state carrier.
+-/
+
+/-- Generic finite-step amortized accounting data. -/
+structure FiniteAmortizedResource where
+  queue : ℕ → ℕ
+  potential : ℕ → ℕ
+  consumed : ℕ → ℕ
+  replenishment : ℕ → ℕ
+  step_conservation :
+    ∀ k, queue (k + 1) + potential (k + 1) + consumed k ≤
+      queue k + potential k + replenishment k
+
+namespace FiniteAmortizedResource
+
+/-- Iterating one-step conservation gives the finite-prefix resource ceiling. -/
+theorem queue_add_potential_le_initial_add_sum
+    (A : FiniteAmortizedResource) (m : ℕ) :
+    A.queue m + A.potential m ≤
+      A.queue 0 + A.potential 0 + ∑ k ∈ Finset.range m, A.replenishment k := by
+  induction m with
+  | zero => simp
+  | succ m ih =>
+      have hstep := A.step_conservation m
+      rw [Finset.sum_range_succ]
+      omega
+
+/-- The sharp queue estimate uses only the initial potential. -/
+theorem queue_le_initial_add_potential_add_cumulativeReplenishment
+    (A : FiniteAmortizedResource) (m : ℕ) :
+    A.queue m ≤
+      A.queue 0 + A.potential 0 + ∑ k ∈ Finset.range m, A.replenishment k := by
+  have h := A.queue_add_potential_le_initial_add_sum m
+  omega
+
+/-- Initial potential and cumulative replenishment bounds give a queue bound. -/
+theorem queue_le_of_initialPotential_and_cumulativeReplenishment_bounds
+    (A : FiniteAmortizedResource) {P R : ℕ}
+    (hpotential : A.potential 0 ≤ P)
+    (hreplenishment : ∀ m,
+      ∑ k ∈ Finset.range m, A.replenishment k ≤ R) (m : ℕ) :
+    A.queue m ≤ A.queue 0 + P + R := by
+  have hqueue := A.queue_le_initial_add_potential_add_cumulativeReplenishment m
+  have hrepl := hreplenishment m
+  omega
+
+/-- Compatibility corollary: a uniform potential bound is stronger than the
+initial bound actually used by the telescope. -/
+theorem queue_le_of_potential_and_cumulative_replenishment_bounds
+    (A : FiniteAmortizedResource) {P R : ℕ}
+    (hpotential : ∀ k, A.potential k ≤ P)
+    (hreplenishment : ∀ m,
+      ∑ k ∈ Finset.range m, A.replenishment k ≤ R) (m : ℕ) :
+    A.queue m ≤ A.queue 0 + P + R :=
+  A.queue_le_of_initialPotential_and_cumulativeReplenishment_bounds
+    (hpotential 0) hreplenishment m
+
+end FiniteAmortizedResource
+
+end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmortizedResource.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmortizedResource.lean
index 6a01fbfb..c39e3167 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmortizedResource.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmortizedResource.lean
@@ -4,6 +4,7 @@ Released under MIT license as described in the file LICENSE.
 Authors: D. and Wise Wolf.
 -/

+import DkMath.Collatz.PetalBridge.FloatWindow.FiniteAmortizedResource
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude

 #print "file: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmortizedResource"
@@ -11,109 +12,161 @@ import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude
 namespace DkMath.Collatz

 /-!
-# Transition-based amortized resource interface
-
-This module states the global resource contract without assuming a global
-injection into a pre-existing finite carrier.  A resource state evolves at
-each block.  The only accounting axiom is a one-step conservation inequality.
-
-The replenishment hypothesis below is cumulative.  A merely pointwise bound
-on replenishment would allow linear growth and cannot imply a uniform queue
-bound.  No Collatz instance of this interface is asserted here.
+# Canonical queue audit and the owned-resource frontier
+
+The generic telescope is in `FiniteAmortizedResource`.  This module audits its
+connection to the canonical reflected queue.  The audit proves that an
+arbitrary scalar potential certificate is equivalent, existentially, to the
+desired queue bound: choosing `potential k = C - queue k` makes conservation
+tautological.  Therefore this certificate is useful algebraically but is not a
+noncircular Collatz resource construction.
 -/

-/-- A dynamic resource state with an explicit queue, potential, demand,
-consumption, and derived replenishment stream. -/
-structure CanonicalAmortizedResourceTransition (n : OddNat) where
-  State : ℕ → Type
-  state : (k : ℕ) → State k
-  potential : ℕ → ℕ
-  queue : ℕ → ℕ
-  demand : ℕ → ℕ
-  consumed : ℕ → ℕ
-  replenishment : ℕ → ℕ
-  demand_le_consumed_add_nextQueue :
-    ∀ k, demand k ≤ consumed k + queue (k + 1)
-  step_conservation :
-    ∀ k, queue (k + 1) + potential (k + 1) + consumed k ≤
-      queue k + potential k + replenishment k
-
-namespace CanonicalAmortizedResourceTransition
-
-/-- Iterating one-step conservation gives the exact finite-prefix resource
-ceiling. -/
-theorem queue_add_potential_le_initial_add_sum
-    {n : OddNat} (A : CanonicalAmortizedResourceTransition n) (m : ℕ) :
-    A.queue m + A.potential m ≤
-      A.queue 0 + A.potential 0 + ∑ k ∈ Finset.range m, A.replenishment k := by
-  induction m with
-  | zero => simp
-  | succ m ih =>
-      have hstep := A.step_conservation m
-      rw [Finset.sum_range_succ]
-      omega
-
-/-- A uniform potential ceiling and a cumulative replenishment ceiling imply
-a uniform queue ceiling. -/
-theorem queue_le_of_potential_and_cumulative_replenishment_bounds
-    {n : OddNat} (A : CanonicalAmortizedResourceTransition n)
-    {P R : ℕ} (hpotential : ∀ k, A.potential k ≤ P)
-    (hreplenishment : ∀ m,
-      ∑ k ∈ Finset.range m, A.replenishment k ≤ R) (m : ℕ) :
-    A.queue m ≤ A.queue 0 + P + R := by
-  have hprefix := A.queue_add_potential_le_initial_add_sum m
-  have hp0 := hpotential 0
-  have hr := hreplenishment m
-  omega
-
-end CanonicalAmortizedResourceTransition
-
-/--
-Noncircular conditional interface for the canonical queue.  It asks for a
-transition law whose queue observable is the existing canonical queue, plus
-independently stated potential and cumulative-replenishment ceilings.  It does
-not include the desired queue bound as a field.
--/
-def CanonicalNoncircularGlobalAmortizationLaw
+/-- Deprecated compatibility name for the former phantom-state structure. -/
+abbrev CanonicalAmortizedResourceTransition (_n : OddNat) :=
+  FiniteAmortizedResource
+
+/-- Neutral scalar certificate connecting a finite amortized telescope to the
+canonical reflected queue.  It intentionally makes no ownership claim. -/
+def CanonicalAbstractAmortizationCertificate
     (n : OddNat) (P R : ℕ) : Prop :=
-  ∃ A : CanonicalAmortizedResourceTransition n,
+  ∃ A : FiniteAmortizedResource,
     (∀ m, A.queue m = canonicalOutstandingClaimQueue n m) ∧
-      (∀ k, A.potential k ≤ P) ∧
+      A.potential 0 ≤ P ∧
         ∀ m, ∑ k ∈ Finset.range m, A.replenishment k ≤ R

-/-- The noncircular amortization law yields a named uniform scalar queue
-bound. -/
-theorem CanonicalNoncircularGlobalAmortizationLaw.to_queueUniformUpperBound
+/-- Deprecated compatibility alias.  Despite its historical name, this
+predicate is not noncircular; see
+`exists_abstractAmortizationCertificate_iff_exists_queueUniformUpperBound`. -/
+@[deprecated CanonicalAbstractAmortizationCertificate (since := "2026-07-16")]
+abbrev CanonicalNoncircularGlobalAmortizationLaw :=
+  CanonicalAbstractAmortizationCertificate
+
+/-- A scalar certificate gives the corresponding canonical queue bound. -/
+theorem CanonicalAbstractAmortizationCertificate.to_queueUniformUpperBound
     {n : OddNat} {P R : ℕ}
-    (h : CanonicalNoncircularGlobalAmortizationLaw n P R) :
+    (h : CanonicalAbstractAmortizationCertificate n P R) :
     CanonicalOutstandingClaimQueueUniformUpperBound n
       (canonicalOutstandingClaimQueue n 0 + P + R) := by
   rcases h with ⟨A, hqueue, hpotential, hreplenishment⟩
   intro m
   rw [← hqueue m, ← hqueue 0]
-  exact A.queue_le_of_potential_and_cumulative_replenishment_bounds
+  exact A.queue_le_of_initialPotential_and_cumulativeReplenishment_bounds
     hpotential hreplenishment m

-/-- Conditional challenge-facing chain from amortization to endpoint width. -/
-theorem CanonicalNoncircularGlobalAmortizationLaw.to_endpointWidthUniformUpperBound
+/-- Conditional challenge-facing consequence of the scalar certificate. -/
+theorem CanonicalAbstractAmortizationCertificate.to_endpointWidthUniformUpperBound
     {n : OddNat} {P R : ℕ}
-    (h : CanonicalNoncircularGlobalAmortizationLaw n P R) :
+    (h : CanonicalAbstractAmortizationCertificate n P R) :
     CanonicalEndpointWidthUniformUpperBound n
       (bitWidth n.1 + (canonicalOutstandingClaimQueue n 0 + P + R)) :=
   h.to_queueUniformUpperBound.to_endpointWidthUniformUpperBound

+/-- Reverse construction exposing the circular complement potential. -/
+noncomputable def trivialAmortizedTransitionOfQueueBound
+    {n : OddNat} {C : ℕ}
+    (hC : CanonicalOutstandingClaimQueueUniformUpperBound n C) :
+    FiniteAmortizedResource where
+  queue k := canonicalOutstandingClaimQueue n k
+  potential k := C - canonicalOutstandingClaimQueue n k
+  consumed _ := 0
+  replenishment _ := 0
+  step_conservation k := by
+    have hk := hC k
+    have hks := hC (k + 1)
+    omega
+
+/-- Any assumed canonical queue bound manufactures the neutral certificate. -/
+theorem CanonicalOutstandingClaimQueueUniformUpperBound.to_abstractAmortizationCertificate
+    {n : OddNat} {C : ℕ}
+    (hC : CanonicalOutstandingClaimQueueUniformUpperBound n C) :
+    CanonicalAbstractAmortizationCertificate n C 0 := by
+  refine ⟨trivialAmortizedTransitionOfQueueBound hC, ?_, ?_, ?_⟩
+  · intro m
+    rfl
+  · exact Nat.sub_le _ _
+  · intro m
+    simp [trivialAmortizedTransitionOfQueueBound]
+
+/-- Mandatory semantic regression: existential scalar amortization is exactly
+as strong as an existential uniform queue bound. -/
+theorem exists_abstractAmortizationCertificate_iff_exists_queueUniformUpperBound
+    (n : OddNat) :
+    (∃ P R, CanonicalAbstractAmortizationCertificate n P R) ↔
+      ∃ C, CanonicalOutstandingClaimQueueUniformUpperBound n C := by
+  constructor
+  · rintro ⟨P, R, h⟩
+    exact ⟨canonicalOutstandingClaimQueue n 0 + P + R,
+      h.to_queueUniformUpperBound⟩
+  · rintro ⟨C, hC⟩
+    exact ⟨C, 0, hC.to_abstractAmortizationCertificate⟩
+
+/-! ## Exact canonical reflected-queue observables -/
+
+/-- Queue available immediately before canonical block `k` is served. -/
+noncomputable def canonicalOutstandingClaimQueueBeforeBlock
+    (n : OddNat) : ℕ → ℕ
+  | 0 => 0
+  | k + 1 => canonicalOutstandingClaimQueue n k
+
+/-- Claims arriving at canonical block `k`. -/
+noncomputable def canonicalQueueDemand (n : OddNat) (k : ℕ) : ℕ :=
+  canonicalBlockClaimCount n k
+
+/-- Anonymous capacity offered by canonical block `k`. -/
+noncomputable def canonicalQueueService (n : OddNat) (k : ℕ) : ℕ :=
+  canonicalBlockCapacityCount n k
+
+/-- Service actually consumed is the minimum of available work and capacity. -/
+noncomputable def canonicalQueueConsumed (n : OddNat) (k : ℕ) : ℕ :=
+  min (canonicalOutstandingClaimQueueBeforeBlock n k + canonicalQueueDemand n k)
+    (canonicalQueueService n k)
+
+/-- Exact conservation for one reflected-queue block. -/
+theorem canonicalOutstandingClaimQueue_add_consumed
+    (n : OddNat) (k : ℕ) :
+    canonicalOutstandingClaimQueue n k + canonicalQueueConsumed n k =
+      canonicalOutstandingClaimQueueBeforeBlock n k + canonicalQueueDemand n k := by
+  cases k with
+  | zero =>
+      change (canonicalBlockClaimCount n 0 - canonicalBlockCapacityCount n 0) +
+          min (0 + canonicalBlockClaimCount n 0) (canonicalBlockCapacityCount n 0) =
+        0 + canonicalBlockClaimCount n 0
+      simp only [zero_add]
+      by_cases h : canonicalBlockCapacityCount n 0 ≤ canonicalBlockClaimCount n 0
+      · rw [Nat.min_eq_right h, Nat.sub_add_cancel h]
+      · have hle : canonicalBlockClaimCount n 0 ≤ canonicalBlockCapacityCount n 0 :=
+          Nat.le_of_not_ge h
+        rw [Nat.min_eq_left hle, Nat.sub_eq_zero_of_le hle]
+        simp
+  | succ k =>
+      change ((canonicalOutstandingClaimQueue n k + canonicalBlockClaimCount n (k + 1)) -
+            canonicalBlockCapacityCount n (k + 1)) +
+          min (canonicalOutstandingClaimQueue n k + canonicalBlockClaimCount n (k + 1))
+            (canonicalBlockCapacityCount n (k + 1)) =
+        canonicalOutstandingClaimQueue n k + canonicalBlockClaimCount n (k + 1)
+      by_cases h : canonicalBlockCapacityCount n (k + 1) ≤
+          canonicalOutstandingClaimQueue n k + canonicalBlockClaimCount n (k + 1)
+      · rw [Nat.min_eq_right h, Nat.sub_add_cancel h]
+      · have hle : canonicalOutstandingClaimQueue n k +
+            canonicalBlockClaimCount n (k + 1) ≤
+              canonicalBlockCapacityCount n (k + 1) := Nat.le_of_not_ge h
+        rw [Nat.min_eq_left hle, Nat.sub_eq_zero_of_le hle]
+        simp
+
 /-!
-## Proven frontier
+## Owned-resource frontier
+
+A genuine next layer must define a concrete finite carrier from `n`, together
+with consumed and replenished subcarriers and an equivalence

-Route 1 stops at a concrete obstruction: exact adjacent core-word recurrence
-permits carry alternation, so it supplies no monotone claim-density estimate.
+`Available (k+1) ≃ (Available k \ Consumed k) ⊕ Replenished k`.

-Route 2 is now logically sound but conditional.  The first missing theorem is
-an actual Collatz construction of `CanonicalNoncircularGlobalAmortizationLaw`
-with a cumulative replenishment ceiling.  Current width decreases and negative
-local drift do not yet carry temporal ownership, so the same replenishment
-event could be reused without a proved multiplicity bound.  Replacing this
-missing construction by a queue ceiling would be circular.
+It must also prove disjoint old/new ownership, injective ownership of consumed
+atoms, and temporal nonreuse.  No such carrier has yet been identified, so no
+placeholder existence theorem is asserted.  Consequently
+`CanonicalSaturatedSuccessorAbstractDischarge` is not yet formally connected
+to this global scalar layer.
 -/

 end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean
index 6251f9b2..f3cebe00 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean
@@ -1782,6 +1782,105 @@ theorem coreWordRecurrence_carry_alternation_witness :
             stateUpperCarry 23 = 2 := by
   norm_num [stateUpperCarry, upperCarry3n1, bitWidth]

+/-! ## Canonical carry-alternation regression -/
+
+/-- Odd root whose first canonical block realizes the `53,35,23` profile. -/
+def twentyThreeCarryAlternationOdd : OddNat := ⟨23, by norm_num⟩
+
+private lemma twentyThree_v2_24 : v2 24 = 3 := by
+  have h12 := (DkMath.ABC.padic_val_two_of_even 12).2 (by decide)
+  have h6 := (DkMath.ABC.padic_val_two_of_even 6).2 (by decide)
+  have h3 := (DkMath.ABC.padic_val_two_of_even 3).2 (by decide)
+  have hv3 : v2 3 = 0 := v2_odd 3 (by decide)
+  have hv6 : v2 6 = 1 := by simpa [v2, hv3] using h3
+  have hv12 : v2 12 = 2 := by simpa [v2, hv6] using h6
+  simpa [v2, hv12] using h12
+
+private theorem twentyThree_endpoint_zero :
+    paymentEndpointSeq twentyThreeCarryAlternationOdd 0 = 2 := by
+  norm_num [paymentEndpointSeq, orbitPaymentTarget, orbitExactDepth,
+    ResidualAllOnesDepth, oddOrbitLabel, iterateT,
+    twentyThreeCarryAlternationOdd, mkOddNat, twentyThree_v2_24]
+
+private theorem twentyThree_paymentBlockLength_zero :
+    canonicalPaymentBlockLength twentyThreeCarryAlternationOdd 0 = 3 := by
+  rw [canonicalPaymentBlockLength_eq_endpoint_sub_start_add_one,
+    universalPaymentBlockStart_paymentEndpointSeq_zero,
+    twentyThree_endpoint_zero]
+
+/-- The first canonical block at odd root `23` has length three. -/
+theorem canonicalBlockLength_twentyThree_zero :
+    canonicalBlockLength twentyThreeCarryAlternationOdd 0 = 3 :=
+  twentyThree_paymentBlockLength_zero
+
+private theorem canonicalBlockStartState_twentyThree_zero :
+    canonicalBlockStartState twentyThreeCarryAlternationOdd 0 = 23 := by
+  unfold canonicalBlockStartState canonicalBlockStartTime canonicalEndpointBlockStart
+  rfl
+
+/-- The first canonical block at odd root `23` has odd core three. -/
+theorem canonicalBlockOddCore_twentyThree_zero :
+    canonicalBlockOddCore twentyThreeCarryAlternationOdd 0 = 3 := by
+  rw [canonicalBlockOddCore, canonicalBlockStartState_twentyThree_zero,
+    canonicalBlockLength_twentyThree_zero]
+  norm_num
+
+/-- Exact three-word core profile of the first canonical block at `23`. -/
+theorem canonicalBlockCoreWords_twentyThree_zero :
+    canonicalBlockCoreWordAtDepth twentyThreeCarryAlternationOdd 0 1 = 53 ∧
+      canonicalBlockCoreWordAtDepth twentyThreeCarryAlternationOdd 0 2 = 35 ∧
+        canonicalBlockCoreWordAtDepth twentyThreeCarryAlternationOdd 0 3 = 23 := by
+  simp [canonicalBlockCoreWordAtDepth, canonicalBlockLength_twentyThree_zero,
+    canonicalBlockOddCore_twentyThree_zero]
+
+private lemma twentyThree_v2_70 : v2 70 = 1 := by
+  have h := (DkMath.ABC.padic_val_two_of_even 35).2 (by decide)
+  simpa [v2, v2_odd 35 (by decide)] using h
+
+private lemma twentyThree_v2_106 : v2 106 = 1 := by
+  have h := (DkMath.ABC.padic_val_two_of_even 53).2 (by decide)
+  simpa [v2, v2_odd 53 (by decide)] using h
+
+private theorem twentyThree_carry_zero :
+    CarryTwoDebtAt twentyThreeCarryAlternationOdd 0 := by
+  norm_num [CarryTwoDebtAt, stateUpperCarry, upperCarry3n1, bitWidth,
+    iterateT, twentyThreeCarryAlternationOdd, mkOddNat]
+
+private theorem twentyThree_not_carry_one :
+    ¬ CarryTwoDebtAt twentyThreeCarryAlternationOdd 1 := by
+  norm_num [CarryTwoDebtAt, stateUpperCarry, upperCarry3n1, bitWidth,
+    iterateT, T, twentyThreeCarryAlternationOdd, mkOddNat, threeNPlusOne,
+    pow2, twentyThree_v2_70]
+
+private theorem twentyThree_carry_two :
+    CarryTwoDebtAt twentyThreeCarryAlternationOdd 2 := by
+  norm_num [CarryTwoDebtAt, stateUpperCarry, upperCarry3n1, bitWidth,
+    iterateT, T, twentyThreeCarryAlternationOdd, mkOddNat, threeNPlusOne,
+    pow2, twentyThree_v2_70, twentyThree_v2_106]
+
+/-- The canonical carry profile at `23` claims depths one and three. -/
+theorem canonicalPaymentClaimDepths_twentyThree_zero :
+    canonicalPaymentClaimDepths twentyThreeCarryAlternationOdd 0 = {1, 3} := by
+  classical
+  ext d
+  rw [mem_canonicalPaymentClaimDepths_iff,
+    twentyThree_paymentBlockLength_zero]
+  unfold canonicalPaymentSourceAtDepth
+  rw [twentyThree_endpoint_zero]
+  simp only [Finset.mem_insert, Finset.mem_singleton]
+  constructor
+  · rintro ⟨hd1, hd3, hcarry⟩
+    interval_cases d <;>
+      simp_all [twentyThree_carry_zero, twentyThree_not_carry_one]
+  · rintro (rfl | rfl) <;>
+      simp [twentyThree_carry_zero, twentyThree_carry_two]
+
+/-!
+This canonical regression proves only that adjacent recurrence does not imply
+monotone carry.  It does not rule out bounded-gap or density theorems that use
+the canonical residue class, odd core, or block width.
+-/
+
 /-- Positive depths in the block which do not carry a canonical payment
 claim. -/
 noncomputable def canonicalBlockClaimHoles
@@ -1789,6 +1888,14 @@ noncomputable def canonicalBlockClaimHoles
   Finset.Icc 1 (canonicalBlockLength n k) \
     canonicalPaymentClaimDepths n k

+/-- The unique hole in the canonical carry profile at `23` is depth two. -/
+theorem canonicalBlockClaimHoles_twentyThree_zero :
+    canonicalBlockClaimHoles twentyThreeCarryAlternationOdd 0 = {2} := by
+  classical
+  rw [canonicalBlockClaimHoles, canonicalBlockLength_twentyThree_zero,
+    canonicalPaymentClaimDepths_twentyThree_zero]
+  decide
+
 /-- Claim depths and claim holes are disjoint by construction. -/
 theorem canonicalPaymentClaimDepths_disjoint_claimHoles
     (n : OddNat) (k : ℕ) :
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-329.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-329.md
index 927fec89..8cf6b86d 100644
--- a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-329.md
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-329.md
@@ -59,11 +59,13 @@ The adjacent recurrence does not imply monotone carries.  Lean verifies the
 exact recurrence witness `53, 35, 23`, whose own-width carries are `2, 1, 2`.
 Thus recurrence alone cannot provide the required uniform claim-hole density.

-## Noncircular global interface
+## Abstract global interface (corrected by checkpoint 330)

-`UniversalPaymentAmortizedResource.lean` introduces a transition state with
-queue, potential, demand, consumption, replenishment, and one-step
-conservation.  Finite-prefix conservation is proved by induction.
+The first version of `UniversalPaymentAmortizedResource.lean` introduced a
+scalar transition state and finite-prefix conservation.  Checkpoint 330 found
+that its potential could be chosen as `C - queue`, so the certificate was not
+noncircular.  The generic telescope remains valid, but the interpretation in
+the original checkpoint result is withdrawn.

 A uniform potential ceiling together with a cumulative replenishment ceiling
 implies a uniform queue bound, which then implies the existing endpoint-width
@@ -72,15 +74,16 @@ it permits linear cumulative growth.

 ## Genuine obstruction

-No Collatz instance of `CanonicalNoncircularGlobalAmortizationLaw` is asserted.
-The missing theorem must assign negative drift or width decrease to resource
-transitions with temporal ownership and prove a cumulative replenishment
-ceiling.  Existing scalar facts allow the same event to be reused across
-blocks unless a multiplicity bound is added.
+Checkpoint 330 proves that existence of the former abstract amortization law
+is equivalent to existence of a uniform queue bound.  A genuine replacement
+must assign negative drift or width decrease to concrete resource atoms with
+temporal ownership and prove a cumulative replenishment ceiling.  Existing
+scalar facts allow the same event to be reused across blocks unless a
+multiplicity bound is added.

-Route 1 therefore stops at carry alternation.  Route 2 stops at uncontrolled
-temporal reuse.  Replacing either missing theorem by a uniform queue or width
-bound would only rename the target and is rejected as circular.
+Route 1 therefore does not obtain monotonicity from recurrence alone, although
+additional canonical residue or width data may still support a density bound.
+Route 2 stops at the absence of a concrete owned carrier and temporal nonreuse.

 ## Verification

diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-330.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-330.md
new file mode 100644
index 00000000..4c5b261d
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-330.md
@@ -0,0 +1,115 @@
+# Petal / FloatWindow implementation report - checkpoint 330
+
+## Result
+
+The circularity audit succeeded.  The former scalar “noncircular” law is now
+proved existentially equivalent to the desired uniform queue bound, so it is
+not a reduction of the global problem.  Its valid generic telescope has been
+separated from Collatz, and the canonical reflected queue now has explicit
+demand, service, consumption, and exact one-block conservation observables.
+
+## Circularity regression
+
+Given a queue ceiling `C`, Lean constructs the finite amortized transition
+
+```text
+queue k         = canonicalOutstandingClaimQueue n k
+potential k     = C - queue k
+consumed k      = 0
+replenishment k = 0.
+```
+
+Both `queue k + potential k` and its successor reduce to `C`.  Therefore:
+
+```text
+exists P R, CanonicalAbstractAmortizationCertificate n P R
+  <->
+exists C, CanonicalOutstandingClaimQueueUniformUpperBound n C.
+```
+
+This is a mandatory semantic regression: an arbitrary complement potential
+can encode the target bound rather than explain it.
+
+## Generic telescope
+
+`FiniteAmortizedResource.lean` is Collatz-independent and has no phantom state
+field.  It records only queue, potential, consumed mass, replenishment, and
+one-step conservation.
+
+The sharp finite-prefix theorem is:
+
+```text
+queue m <= queue 0 + potential 0 + cumulativeReplenishment m.
+```
+
+Only the initial potential is needed.  The old uniform-potential version is
+retained as a stronger compatibility corollary.
+
+## Exact canonical queue transition
+
+The canonical observables are now explicit:
+
+```text
+demand k   = canonicalBlockClaimCount n k
+service k  = canonicalBlockCapacityCount n k
+consumed k = min (queueBeforeBlock k + demand k) (service k).
+```
+
+Lean proves exact reflected conservation for every block:
+
+```text
+canonicalOutstandingClaimQueue n k + consumed k
+  = queueBeforeBlock k + demand k.
+```
+
+This handles block zero and successor blocks uniformly through the explicit
+`queueBeforeBlock` observable.
+
+## Canonical carry-alternation regression
+
+The arithmetic witness `53,35,23` is realized by the first canonical block of
+the odd root `23`.  Lean proves:
+
+```text
+block length = 3
+odd core = 3
+core words at depths 1,2,3 = 53,35,23
+claim depths = {1,3}
+claim holes = {2}.
+```
+
+Thus adjacent core-word recurrence alone does not imply monotone carry inside
+canonical blocks.  This does not rule out bounded-gap or density theorems that
+also use canonical residue classes, odd core, or block width.
+
+## Genuine stopping point
+
+No concrete initial upper-resource carrier has yet been identified.  A genuine
+owned transition must define carriers from the initial odd state and prove an
+identity of the form
+
+```text
+Available (k+1) ≃ (Available k \ Consumed k) Sum Replenished k
+```
+
+together with disjoint ownership, injective consumption, unique temporal
+origin, and temporal nonreuse.  Without those data, local saturated-successor
+discharge is not formally connected to global amortization.
+
+The next admissible step is therefore carrier discovery, not another scalar
+potential predicate.  Any proposed owned law must be audited against the same
+reverse construction before it is accepted.
+
+## Verification
+
+All required gates passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude
+lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmortizedResource
+lake build DkMath.Collatz.PetalBridge.FloatWindow
+lake build DkMath
+git diff --check
+```
+
+The changed Lean files contain no `sorry` or local heartbeat override.
````
`````
