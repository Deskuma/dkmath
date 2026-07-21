# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceTimeLag, RawLowSignatureObstruction

gch: cc5456fc1ed25c3ed66cfa7cd9625cbaf98bdae3

## Report

(21m18s)

実装完了です。Checkpoint 333 の全 Stage A-H が `no-sorry` で通過しました。

**確定した事実**

- canonical block demand は、対応する実軌道時間区間内の carry-two source 数と厳密に一致します。
- 一様な source claim age `H` が得られれば、queue bound、endpoint width bound まで直結します。
- 任意の `r ≥ 1` に対し、
  `xᵣ = 2^(r+2) - 1`
  は次状態と同じ固定低位署名を持ちながら、幅が厳密に `+1` 増えます。
- したがって、residue・upper carry・height class・growth flag だけからなる固定低位署名では、全正奇数遷移を覆う bounded-potential certificate は存在しません。
- これは全有限署名の否定ではありません。upper-boundary 座標や減少 rank を含む署名は未決着です。

実装箇所:

- [CanonicalSourceTimeLag.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalSourceTimeLag.lean)
- [RawLowSignatureObstruction.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/RawLowSignatureObstruction.lean)
- [FiniteSignedTransition.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean:294)
- [report-petal-333.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-333.md)

`FloatWindow`、`PetalBridge`、トップレベル `DkMath` の全ビルドと `git diff --check` が通過しています。

## Review

(8m33s)

## cp-333 実装レビュー

## 結論

**実装は全面採用。数学的にも大前進じゃ。**

今回は本当に、

1. 未証明だった source-time accounting を無条件に証明した。
2. 固定低位署名の一族を、有限探索ではなく任意の $r\ge1$ に対する反例族で倒した。

という二つを達成している。

しかも build が通っただけではない。証明内容を追っても、

- 前提が空ではない
- queue bound の言い換えではない
- 有限表の観測結果ではない
- all-ones witness は実際の accelerated Collatz edge
- 不可能性 theorem の主張範囲も適切に限定

されている。

ただし、source-time route の解釈には一つだけ重要な補正がある。

> `CanonicalOutstandingQueueCoveredByRecentSourceClaims` は、現状では actual claim-age theorem ではなく、recent source carrier による **cardinality coverage** じゃ。

この違いを次 checkpoint で actual owned queue によって埋めるべきである。

---

## 1. Finite certificate の循環性監査

今回、

```lean id="3fvech"
endpointAccountingTerm_le_queueBeforeBlock_increment
```

が証明された。

内容は、

$$
D_k\le Q_{k+1}^{\mathrm{before}}-Q_k^{\mathrm{before}}
$$

じゃ。

これは reflected queue の exact conservation、

$$
Q_{k+1}^{\mathrm{before}}+C_k=Q_k^{\mathrm{before}}+A_k
$$

と、

$$
C_k\le S_k
$$

から正しく従う。

そして queue bound $Q_k\le C$ を仮定すると、

```lean id="676nsq"
signature k := queueBeforeBlock k
potential s := s.val
projectedUpperWeight s t := t.val - s.val
```

として、

```lean id="a5531s"
CanonicalFiniteSignedTransitionPotentialCertificate n (Fin (C + 1))
```

が作れる。

従って、

$$
\exists\text{ Fin-indexed certificate}\iff\exists\text{ uniform queue bound}
$$

が Lean 上で固定された。

これは重要な semantic regression じゃ。

> 「有限署名 certificate が存在する」という抽象的存在命題だけでは、問題を簡約しない。

非循環にするには、signature が queue bound から逆算されず、あらかじめ arithmetic data から定義されていなければならない。

### 小さな表現上の注意

現在の同値 theorem は、

```lean id="cwbjez"
∃ C, Nonempty
  (CanonicalFiniteSignedTransitionPotentialCertificate n (Fin (C + 1)))
```

という `Fin` 型に正規化された存在を扱う。

意味上は十分じゃが、doc comment の「unrestricted existential certificate」は少し広く見える。

将来は、

```lean id="vbh223"
ExistsFinIndexedCanonicalCertificate
```

のような名前を置くか、任意の非空有限 signature を `Fin N` へ輸送する wrapper を置くと完全に明瞭になる。

---

## 2. Block index から source time への変換

今回の最初の真の新定理は、

```lean id="z7meyx"
canonicalBlockStartTime_succ
```

じゃ。

$$
b_{k+1}=b_k+L_k
$$

が証明された。

ここから、

$$
\sum_{k<m}L_k=b_m
$$

および、

$$
\sum_{k\in[q,m)}L_k=b_m-b_q
$$

が得られた。

これは単なる index arithmetic ではない。

> canonical block が orbit source time を隙間なく分割している

ことを数値 telescope として公開した theorem じゃ。

---

## 3. Demand は source-time span 以下

既存の、

$$
A_k\le L_k
$$

と block-length telescope を合わせて、

$$
\sum_{k\in[q,m)}A_k\le b_m-b_q
$$

が証明された。

さらに recent block window について、

$$
\operatorname{RecentDemand}(L,m)\le b_m-b_{m-L}
$$

まで閉じた。

これは無条件 theorem じゃ。

cp-332 では、

```text id="y34lyj"
block lag
+
per-block arrival bound
```

が必要だった。

cp-333 は demand を source-time 幅へ戻すことで、

> block が何個あるかではなく、その block 群が実際に何 orbit time を占有したか

を使えるようにした。

この座標変換は正しい。

---

## 4. Coarse inequality より強い exact carrier identity

今回の本当の心臓は、単なる、

$$
A_k\le L_k
$$

ではない。

各 block について、

$$
A_k=\left| \{ i\in[b_k,b_{k+1}) \mid \operatorname{CarryTwoDebtAt}(n,i) \} \right|
$$

が証明された。

さらに任意の block interval で、

$$
\sum_{k\in[q,m)} A_k = \left| \{ i\in[b_q,b_m) \mid \operatorname{CarryTwoDebtAt}(n,i) \} \right|
$$

となる。

これは非常に強い。

canonical demand はもはや匿名の block count ではない。

> **実 orbit source time 上の carry-two event の個数**

として完全に読み直された。

つまり Petal block ledger と raw orbit debt event が、carrier cardinality レベルで正確に一致した。

---

## 5. Recent source carrier

新しい、

```lean id="yptzei"
canonicalRecentSourceClaimCarrier n H m
```

は、

$$
[b_m-H,b_m)
$$

に存在する carry-two source time の集合じゃ。

この carrier は実 source address を保持する。

区間自体の cardinality が高々 $H$ なので、

$$
|\operatorname{RecentSourceClaims}(H,m)|\le H
$$

が証明された。

この部分は完全採用でよい。

source-time 幅 $H$ の窓では、一時刻につき claim は高々一個なので、block arrival 上界を別途要求する必要がない。

---

## 6. 重要な意味境界：cardinality coverage と actual age

現在の predicate は、

```lean id="zdazbp"
def CanonicalOutstandingQueueCoveredByRecentSourceClaims
    (n : OddNat) (H : ℕ) : Prop :=
  ∀ m, queueBeforeBlock n m ≤
    (canonicalRecentSourceClaimCarrier n H m).card
```

じゃ。

これは、

$$
Q_m\le|\operatorname{RecentSourceClaims}(H,m)|
$$

という cardinality inequality である。

従って、

$$
Q_m\le H
$$

および endpoint width bound が正しく従う。

しかし、これはまだ、

> queue 内の各 outstanding claim が、本当にその recent source の一つである

とは言っていない。

現在の scalar queue は匿名なので、各時刻 $m$ ごとに別々の arbitrary injection を選んでも cardinality inequality は成立し得る。

例えば古い claim が残り続けていても、最近の別 claim の個数が十分多ければ、数だけは覆える。

したがって現在証明されたものは、

```text id="596vk1"
recent-source cardinal coverage
→ queue bound
→ width bound
```

じゃ。

まだ証明されていないものは、

```text id="2wkfvm"
actual outstanding claim
→ actual birth source
→ source age ≤ H
```

である。

report の、

> remaining input is exactly a uniform source-age theorem

は攻め筋としては正しい。

ただし現 predicate 自体を「source-age theorem」と呼ぶのは一段強すぎる。

推奨名は、

```lean id="p5lqv9"
CanonicalOutstandingQueueCardCoveredByRecentSourceClaims
```

じゃ。

---

## 7. All-ones witness の算術監査

$r\ge1$ とする。

今回定義された、

$$
x_r=2^{r+2}-1
$$

について、

$$
T(x_r)=3\cdot2^{r+1}-1
$$

$$
T^2(x_r)=9\cdot2^r-1
$$

が証明された。

また、

$$
s(x_r)=1
$$

$$
s(T(x_r))=1
$$

である。

幅は、

$$
\operatorname{bitWidth}(x_r)=r+2
$$

$$
\operatorname{bitWidth}(T(x_r))=r+3
$$

$$
\operatorname{bitWidth}(T^2(x_r))=r+4
$$

となる。

従って最初の二 edge は、ともに厳密な width growth $+1$。

指数境界も正しく処理されている。

---

## 8. Signature equality

source と target は共に、

$$
x_r\equiv T(x_r)\equiv2^r-1\pmod{2^r}
$$

じゃ。

さらに両者は、

- upper carry $2$
- height class `one`
- next width growth `true`

を共有する。

従って、

```lean id="fhm6jp"
fixedLowRawSignature r (T xᵣ)
  =
fixedLowRawSignature r xᵣ
```

が成立する。

一方、実 edge weight は、

$$
\operatorname{bitWidth}(T(x_r))-\operatorname{bitWidth}(x_r)=1
$$

じゃ。

---

## 9. これは Collatz cycle ではない

ここは明確にしておくべきじゃ。

$$
T(x_r)\ne x_r
$$

である。

今回得たのは actual state cycle ではない。

得たのは、有限射影後の、

$$
\sigma(x_r)\xrightarrow{+1}\sigma(x_r)
$$

という **positive signature self-loop** じゃ。

bounded potential certificate では、同じ signature への edge は、

$$
\widehat w(s,s)\le\Phi(s)-\Phi(s)=0
$$

を満たさねばならない。

しかし soundness は、

$$
1\le\widehat w(s,s)
$$

を要求する。

よって矛盾する。

この不可能性証明は完全に正しい。

---

## 10. 不可能性 theorem の正確な射程

今回倒したのは、

```lean id="mz6xhy"
FixedLowRawSignature r
```

である。

その座標は、

```text id="nvpygz"
residue modulo 2^r
upper carry
height one / at least two
one-step width-growth flag
```

じゃ。

従って確定したのは、

> この四座標だけを持つ固定低位署名では、全 accelerated odd edge を覆う bounded-potential certificate は作れない。

という命題である。

これは $r$ を増やしても回避できない。witness 自身が $r$ と共に成長するからじゃ。

ただし、まだ直接は次まで否定していない。

- arbitrary な有限署名
- upper bits を含む署名
- absolute boundary distance
- dynamic decreasing rank
- finite history を含む署名
- `FixedLowRawSignature` より豊かな別の low-coordinate family

report はこの境界を正しく守っている。

---

## 11. Factor-through まで一般化できる

現在の theorem は exact signature 型に固定されている。

しかし、実際にはその任意の coarsening も同じ witness で倒せる。

例えば、

```lean id="0jgouq"
C.signature x = f (fixedLowRawSignature r x)
```

と factor する signature なら、

$$
\operatorname{fixedLowSig}(T(x_r))=\operatorname{fixedLowSig}(x_r)
$$

から、

$$
C.\operatorname{signature}(T(x_r))=C.\operatorname{signature}(x_r)
$$

が従う。

従って、次には、

```lean id="zpf5qn"
not_certificate_of_signature_factorsThrough_fixedLowRawSignature
```

を証明できる。

これにより、

> この四座標から計算されるあらゆる有限ラベル

を一括して排除できる。

---

## 12. All-ones obstruction が教えた missing coordinate

今回の witness は、何が見えていないかも正確に教えている。

$x_r$ の最上位二 bit は、

```text id="18nhbg"
11
```

である。

一方、$T(x_r)$ の最上位二 bit は、

```text id="a8hinp"
10
```

じゃ。

従って normalized top-two-bit coordinate を追加すれば、この particular self-loop は消える。

これは、

> 次の finite signature には upper-boundary coordinate が必要

という report の診断を具体化している。

ただし top-two bits を加えただけで positive projected cycle が全て消えるとは限らない。

消えるのは今回の一 edge obstructionだけじゃ。

---

## 13. 今回、本当に何が進んだか

cp-333 以前は、

```text id="8s0632"
未証明 theorem を置く
→ その theorem なら queue bound
```

という conditional surface が中心だった。

今回は違う。

### 無条件に証明したもの

$$
\sum_{k\in[q,m)}A_k=\left|\left{i\in[b_q,b_m)\mid\operatorname{CarryTwoDebtAt}(n,i)\right}\right|
$$

### 一般反例族として倒したもの

$$
\text{fixed low signature bounded-potential certificate}
$$

この二つはいずれも新しい数学的情報じゃ。

「未証明を証明できるか？！」への答えは、

> **一つは証明できた。もう一つは成立しないことを証明できた。**

じゃ。

これは理想的な checkpoint である。

---

## 14. 最終 Challenge への距離

現在の正確な positive route は、

```text id="dy49m2"
actual source-bearing outstanding queue
→ uniform actual source age
→ recent-source cardinal coverage
→ uniform queue bound
→ endpoint width bound
```

じゃ。

negative routeでは、

```text id="h0uhrf"
fixed low signature
→ all-ones positive projected self-loop
→ bounded potential impossible
```

が閉じた。

残るのは、

1. actual outstanding claim ownership
2. uniform source-age theorem
3. upper-boundaryを含む非循環 finite signature
4. width bound 後の finite-state / cycle elimination

である。

---

## 判定まとめ

### Finite-certificate circularity

**完成。**

### Block start telescope

**完成。**

### Demand/source-time exact identity

**完成。今回の中心成果。**

### Recent source carrier cardinality

**完成。**

### Actual source-age theorem

**未完成。現在は匿名 cardinal coverage。**

### All-ones raw family

**完成。**

### Fixed-low signature obstruction

**完成。任意の $r\ge1$ に対する一般 theorem。**

### 全有限署名の否定

**行っていない。境界は正しい。**

### cp-333 総合判定

**全面採用。source-age という用語だけ一段補正。**

## 次の Codex 指示

```text id="4mgf5h"
Continue the DkMath Collatz / PetalBridge FloatWindow branch after
report-petal-333.

The cp-333 implementation is accepted.

It proved two substantive results:

    exact canonical demand/source-time carrier accounting;

    a parameterized positive closed-signature obstruction for the audited
    fixed low raw signature.

One semantic correction is required:

    `CanonicalOutstandingQueueCoveredByRecentSourceClaims` is currently a
    cardinality-coverage predicate, not an actual claim-age or ownership
    theorem.

The next checkpoint must build the actual source-bearing reflected queue and
connect genuine source age to the cp-333 scalar coverage theorem.

## Stage A — cardinal-coverage terminology

Introduce the precise name:

    CanonicalOutstandingQueueCardCoveredByRecentSourceClaims.

Keep:

    CanonicalOutstandingQueueCoveredByRecentSourceClaims

as a compatibility alias if needed.

Document explicitly:

    the predicate asserts only a cardinality inequality;

    it does not identify the outstanding queue elements with recent sources;

    an actual owned-queue age theorem will imply it.

Preserve the existing queue and endpoint-width consequence theorems.

## Stage B — block claim-source carrier

Define:

    canonicalBlockClaimSourceCarrier n k :=
      carryTwoPositions n
        (Ico
          (canonicalBlockStartTime n k)
          (canonicalBlockStartTime n (k + 1))).

Reuse cp-333 to prove:

    card = canonicalQueueDemand n k;

    every source lies in the exact block interval;

    different block claim-source carriers are disjoint;

    every member satisfies CarryTwoDebtAt.

## Stage C — generic oldest-first finite queue

Create a Collatz-independent finite queue on source times.

For a finite set `s : Finset Nat` and service amount `c`, define an
oldest-first remainder:

    eraseOldestN c s.

A recursive implementation using `Finset.min'` and `erase` is acceptable.

Prove:

    eraseOldestN c s ⊆ s;

    card (eraseOldestN c s) = card s - c;

    consumedOldestN c s := s \ eraseOldestN c s;

    card (consumedOldestN c s) = min c s.card;

    consumed and remainder are disjoint;

    their union is s;

    every consumed source is no later than every remaining source.

The final ordering theorem is the FIFO invariant needed for source age.

## Stage D — recursive canonical owned queue

Define recursively:

    canonicalOwnedOutstandingClaimsBeforeBlock n 0 := empty;

    canonicalOwnedOutstandingClaimsBeforeBlock n (k + 1) :=
      eraseOldestN
        (canonicalQueueService n k)
        (
          canonicalOwnedOutstandingClaimsBeforeBlock n k
            union
          canonicalBlockClaimSourceCarrier n k
        ).

Also define:

    canonicalOwnedConsumedClaimsAtBlock n k

as the corresponding consumed subset.

Do not rematch the complete historical window independently at each endpoint.
The transition must be recursive and temporally coherent.

## Stage E — temporal support invariants

Prove by induction:

    every owned outstanding source before block k is strictly less than
      canonicalBlockStartTime n k;

    every owned outstanding source satisfies CarryTwoDebtAt n;

    old outstanding and new block claims are disjoint;

    consumed and next outstanding claims are disjoint;

    a consumed source never reappears in any later owned queue.

Preserve the original source-time address as the claim identity.

## Stage F — scalar cardinality agreement

Prove:

    card (canonicalOwnedOutstandingClaimsBeforeBlock n k)
      =
    canonicalOutstandingClaimQueueBeforeBlock n k;

    card (canonicalOwnedConsumedClaimsAtBlock n k)
      =
    canonicalQueueConsumed n k.

Use:

    card block claim source carrier = canonicalQueueDemand;

    exact service/min cardinality;

    canonicalOutstandingClaimQueue_add_consumed.

This theorem is mandatory.  Without it, the owned queue is not a realization of
the existing scalar queue.

## Stage G — actual source age

Define:

    CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H

to mean:

    for every block m and every source i in the owned outstanding queue,

      canonicalBlockStartTime n m - i <= H.

Using the temporal support invariant, prove:

    every owned outstanding source lies in
      canonicalRecentSourceClaimCarrier n H m.

Then derive:

    CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H
      ->
    CanonicalOutstandingQueueCardCoveredByRecentSourceClaims n H
      ->
    CanonicalOutstandingClaimQueueUniformUpperBound n H
      ->
    CanonicalEndpointWidthUniformUpperBound n (bitWidth n.1 + H).

This is the genuine ownership/age bridge missing from cp-333.

Do not assert that a uniform H exists.

## Stage H — oldest-first optimality surface

Prove a generic comparison theorem:

    among all policies consuming the same number of claims from one finite
    source set, oldest-first minimizes the maximum source age of the remainder.

A weaker sufficient theorem is acceptable:

    if the oldest-first remainder contains a source older than H, then every
    remainder of the same cardinality contains some source at least as old.

This prevents the chosen ownership policy from hiding a better possible age
bound.

## Stage I — generic positive closed-signature obstruction

Extract the logical core of `RawLowSignatureObstruction`:

    if one realized related edge has
      positive actual weight
    and equal endpoint signatures,
    then no bounded-potential certificate can cover that edge.

Reprove the all-ones theorem as a corollary.

## Stage J — factor-through obstruction

Let `f` be any map from `FixedLowRawSignature r` to another finite signature.

Prove that a certificate whose signature satisfies:

    C.signature x = f (fixedLowRawSignature r x)

and whose step/weight covers all raw odd transitions is impossible.

This upgrades the current theorem from the exact four-coordinate structure to
every coarsening computed solely from those coordinates.

Do not claim the result for a strict refinement containing additional
information.

## Stage K — normalized upper-boundary witness

Define or reuse a normalized top-two-bit observation for positive naturals.

For r >= 1 prove:

    topTwoBits (rawAllOnesWitness r) = binary 11;

    topTwoBits (T (rawAllOnesWitness r)) = binary 10.

Conclude only:

    adding this coordinate distinguishes the cp-333 all-ones edge.

Do not infer that the enriched signature has a bounded potential.

## Stage L — enriched-signature audit

Define the first enriched experimental signature:

    fixed low raw signature
      +
    normalized top-two bits.

Audit in this order:

    edgewise raw signed-width bound;

    realized signature-pair graph;

    positive projected self-loops;

    positive projected cycles.

A projected cycle may combine signature edges realized by different concrete
states; a single concrete orbit cycle is not required for a potential
contradiction.

Record exact witnesses for every rejected cycle.

Do not promote finite numerical search to a global theorem without a symbolic
or exhaustive finite soundness proof.

## Stage M — report boundary

Record separately:

    cp-333 scalar recent-source coverage;

    cp-334 actual owned-queue age semantics;

    fixed-low signature obstruction;

    enriched upper-boundary signature status.

The remaining positive theorem should be stated exactly as:

    existence of a uniform actual source-age bound H
      ->
    uniform queue and endpoint-width bounds.

Stop at the first genuine obstruction among:

    oldest-first finite-set cardinality cannot be proved;

    recursive owned queue loses source identity;

    owned queue cardinality disagrees with the scalar queue;

    actual age does not imply recent-source carrier membership;

    factor-through obstruction fails;

    normalized top bits do not distinguish the all-ones edge;

    the enriched finite graph retains a positive projected cycle.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-334.md
```

今回は期待どおりじゃ。

Codex が慎重になっただけの価値はあった。
**cp-333 は、条件整理ではなく、数学そのものを二方向から前進させた checkpoint** じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
index e56c93e7..aa888a16 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
@@ -30,6 +30,8 @@ import DkMath.Collatz.PetalBridge.FloatWindow.FiniteAmortizedResource
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmortizedResource
 import DkMath.Collatz.PetalBridge.FloatWindow.BoundedRepaymentLag
 import DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition
+import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceTimeLag
+import DkMath.Collatz.PetalBridge.FloatWindow.RawLowSignatureObstruction

 #print "file: DkMath.Collatz.PetalBridge.FloatWindow"

diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalSourceTimeLag.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalSourceTimeLag.lean
new file mode 100644
index 00000000..9f848969
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalSourceTimeLag.lean
@@ -0,0 +1,319 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.BoundedRepaymentLag
+import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlockNormalForm
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceTimeLag"
+
+namespace DkMath.Collatz
+
+/-!
+# Canonical source-time lag
+
+Block indices are not physical time.  This module converts canonical block
+arrival counts back to their actual orbit-source interval.  The resulting
+conditional route asks for a uniform source-age theorem, not a uniform number
+of blocks.
+-/
+
+/-- Consecutive canonical block starts differ by the exact block length. -/
+theorem canonicalBlockStartTime_succ
+    (n : OddNat) (k : ℕ) :
+    canonicalBlockStartTime n (k + 1) =
+      canonicalBlockStartTime n k + canonicalBlockLength n k := by
+  have hend := canonicalBlockStartTime_add_length_sub_one_eq_endpoint n k
+  have hlen := one_le_canonicalBlockLength n k
+  change paymentEndpointSeq n k + 1 =
+    canonicalBlockStartTime n k + canonicalBlockLength n k
+  omega
+
+/-- Canonical block lengths telescope exactly to the next block start. -/
+theorem sum_canonicalBlockLength_range_eq_startTime
+    (n : OddNat) (m : ℕ) :
+    (∑ k ∈ Finset.range m, canonicalBlockLength n k) =
+      canonicalBlockStartTime n m := by
+  induction m with
+  | zero => simp [canonicalBlockStartTime, canonicalEndpointBlockStart]
+  | succ m ih =>
+      rw [Finset.sum_range_succ, ih, canonicalBlockStartTime_succ]
+
+/-- A block-index interval has exactly the corresponding orbit-time span. -/
+theorem sum_canonicalBlockLength_Ico_eq_startTime_sub
+    (n : OddNat) {q m : ℕ} (hqm : q ≤ m) :
+    (∑ k ∈ Finset.Ico q m, canonicalBlockLength n k) =
+      canonicalBlockStartTime n m - canonicalBlockStartTime n q := by
+  have hsplit := Finset.sum_range_add_sum_Ico
+    (fun k => canonicalBlockLength n k) hqm
+  rw [sum_canonicalBlockLength_range_eq_startTime,
+    sum_canonicalBlockLength_range_eq_startTime] at hsplit
+  have hadd :
+      (∑ k ∈ Finset.Ico q m, canonicalBlockLength n k) +
+          canonicalBlockStartTime n q = canonicalBlockStartTime n m := by
+    simpa [Nat.add_comm] using hsplit
+  exact Nat.eq_sub_of_add_eq hadd
+
+/-- Canonical demand over a block interval is bounded by its actual source-time
+span. -/
+theorem sum_canonicalQueueDemand_Ico_le_sourceTimeSpan
+    (n : OddNat) {q m : ℕ} (hqm : q ≤ m) :
+    (∑ k ∈ Finset.Ico q m, canonicalQueueDemand n k) ≤
+      canonicalBlockStartTime n m - canonicalBlockStartTime n q := by
+  calc
+    (∑ k ∈ Finset.Ico q m, canonicalQueueDemand n k) ≤
+        ∑ k ∈ Finset.Ico q m, canonicalBlockLength n k :=
+      Finset.sum_le_sum fun k _ => canonicalBlockClaimCount_le_length n k
+    _ = canonicalBlockStartTime n m - canonicalBlockStartTime n q :=
+      sum_canonicalBlockLength_Ico_eq_startTime_sub n hqm
+
+/-- The corrected recent block-demand window is bounded by the corresponding
+actual orbit-source span. -/
+theorem recentCanonicalDemand_le_sourceTimeSpan
+    (n : OddNat) (L m : ℕ) :
+    recentArrivalMass (canonicalQueueDemand n) L m ≤
+      canonicalBlockStartTime n m - canonicalBlockStartTime n (m - L) := by
+  unfold recentArrivalMass
+  exact sum_canonicalQueueDemand_Ico_le_sourceTimeSpan n (Nat.sub_le m L)
+
+/-! ## Exact block/source carrier identification -/
+
+/-- The claims born in one canonical block are exactly its carry-two source
+addresses in the half-open block interval. -/
+theorem canonicalQueueDemand_eq_carryTwoPositions_block_card
+    (n : OddNat) (k : ℕ) :
+    canonicalQueueDemand n k =
+      (carryTwoPositions n
+        (Finset.Ico (canonicalBlockStartTime n k)
+          (canonicalBlockStartTime n (k + 1)))).card := by
+  classical
+  unfold canonicalQueueDemand canonicalBlockClaimCount
+  rw [carryTwoPaymentClaimFiberAt_eq_filter_universalPaymentBlock_carryTwo n
+    (paymentEndpointSeq n k)
+    (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)]
+  apply congrArg Finset.card
+  ext i
+  rw [mem_carryTwoPositions_iff, mem_carryTwoPositions_iff]
+  have hstart := canonicalBlockStartTime_eq_universalPaymentBlockStart n k
+  have htop : canonicalBlockStartTime n (k + 1) =
+      paymentEndpointSeq n k + 1 := by
+    simp [canonicalBlockStartTime, canonicalEndpointBlockStart]
+  constructor
+  · rintro ⟨hi, hcarry⟩
+    have hlo : canonicalBlockStartTime n k ≤ i := by
+      rw [hstart]
+      exact (Finset.mem_Icc.mp hi).1
+    exact ⟨Finset.mem_Ico.mpr ⟨hlo, by
+      have := (Finset.mem_Icc.mp hi).2
+      omega⟩, hcarry⟩
+  · rintro ⟨hi, hcarry⟩
+    have hlo : universalPaymentBlockStart n (paymentEndpointSeq n k)
+        (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k) ≤ i := by
+      rw [← hstart]
+      exact (Finset.mem_Ico.mp hi).1
+    exact ⟨Finset.mem_Icc.mpr ⟨hlo, by
+      have := (Finset.mem_Ico.mp hi).2
+      omega⟩, hcarry⟩
+
+/-- Block-start time is monotone in the block index. -/
+theorem canonicalBlockStartTime_mono
+    (n : OddNat) {q m : ℕ} (hqm : q ≤ m) :
+    canonicalBlockStartTime n q ≤ canonicalBlockStartTime n m := by
+  have hsplit := Finset.sum_range_add_sum_Ico
+    (fun k => canonicalBlockLength n k) hqm
+  rw [sum_canonicalBlockLength_range_eq_startTime,
+    sum_canonicalBlockLength_range_eq_startTime] at hsplit
+  omega
+
+/-- Prefix demand is exactly the number of carry-two source addresses before
+the corresponding block start. -/
+theorem sum_canonicalQueueDemand_range_eq_sourceClaims_card
+    (n : OddNat) (m : ℕ) :
+    (∑ k ∈ Finset.range m, canonicalQueueDemand n k) =
+      (carryTwoPositions n
+        (Finset.Ico 0 (canonicalBlockStartTime n m))).card := by
+  classical
+  induction m with
+  | zero => simp [canonicalBlockStartTime, canonicalEndpointBlockStart,
+      carryTwoPositions]
+  | succ m ih =>
+      let A := carryTwoPositions n (Finset.Ico 0 (canonicalBlockStartTime n m))
+      let B := carryTwoPositions n
+        (Finset.Ico (canonicalBlockStartTime n m)
+          (canonicalBlockStartTime n (m + 1)))
+      have hdisj : Disjoint A B := by
+        apply Finset.disjoint_left.mpr
+        intro i hiA hiB
+        dsimp [A] at hiA
+        dsimp [B] at hiB
+        have hA := (mem_carryTwoPositions_iff.mp hiA).1
+        have hB := (mem_carryTwoPositions_iff.mp hiB).1
+        have hAI := Finset.mem_Ico.mp hA
+        have hBI := Finset.mem_Ico.mp hB
+        omega
+      have hunion : A ∪ B =
+          carryTwoPositions n
+            (Finset.Ico 0 (canonicalBlockStartTime n (m + 1))) := by
+        ext i
+        have hmono := canonicalBlockStartTime_mono n (Nat.le_succ m)
+        have hnextEq : canonicalBlockStartTime n m.succ =
+            canonicalBlockStartTime n (m + 1) := rfl
+        constructor
+        · intro hi
+          rcases Finset.mem_union.mp hi with hiA | hiB
+          · have hA := mem_carryTwoPositions_iff.mp (by simpa [A] using hiA)
+            have hAI := Finset.mem_range.mp hA.1
+            exact mem_carryTwoPositions_iff.mpr
+              ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hA.2⟩
+          · have hB := mem_carryTwoPositions_iff.mp (by simpa [B] using hiB)
+            have hBI := Finset.mem_Ico.mp hB.1
+            exact mem_carryTwoPositions_iff.mpr
+              ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hB.2⟩
+        · intro hi
+          have hI := mem_carryTwoPositions_iff.mp hi
+          by_cases hleft : i < canonicalBlockStartTime n m
+          · apply Finset.mem_union_left
+            exact (show i ∈ A by
+              apply mem_carryTwoPositions_iff.mpr
+              exact ⟨Finset.mem_Ico.mpr ⟨by omega, hleft⟩, hI.2⟩)
+          · apply Finset.mem_union_right
+            exact (show i ∈ B by
+              apply mem_carryTwoPositions_iff.mpr
+              exact ⟨Finset.mem_Ico.mpr ⟨by omega,
+                (Finset.mem_Ico.mp hI.1).2⟩, hI.2⟩)
+      rw [Finset.sum_range_succ, ih,
+        canonicalQueueDemand_eq_carryTwoPositions_block_card]
+      change A.card + B.card = _
+      rw [← Finset.card_union_of_disjoint hdisj, hunion]
+
+/-- Canonical demand over any block interval is exactly the carry-two source
+count in the corresponding orbit-time interval. -/
+theorem sum_canonicalQueueDemand_Ico_eq_sourceClaims_card
+    (n : OddNat) {q m : ℕ} (hqm : q ≤ m) :
+    (∑ k ∈ Finset.Ico q m, canonicalQueueDemand n k) =
+      (carryTwoPositions n
+        (Finset.Ico (canonicalBlockStartTime n q)
+          (canonicalBlockStartTime n m))).card := by
+  classical
+  let A := carryTwoPositions n (Finset.Ico 0 (canonicalBlockStartTime n q))
+  let B := carryTwoPositions n
+    (Finset.Ico (canonicalBlockStartTime n q) (canonicalBlockStartTime n m))
+  have htime := canonicalBlockStartTime_mono n hqm
+  have hdisj : Disjoint A B := by
+    apply Finset.disjoint_left.mpr
+    intro i hiA hiB
+    dsimp [A] at hiA
+    dsimp [B] at hiB
+    have hA := (mem_carryTwoPositions_iff.mp hiA).1
+    have hB := (mem_carryTwoPositions_iff.mp hiB).1
+    have hAI := Finset.mem_Ico.mp hA
+    have hBI := Finset.mem_Ico.mp hB
+    omega
+  have hunion : A ∪ B =
+      carryTwoPositions n (Finset.Ico 0 (canonicalBlockStartTime n m)) := by
+    ext i
+    constructor
+    · intro hi
+      rcases Finset.mem_union.mp hi with hiA | hiB
+      · have hA := mem_carryTwoPositions_iff.mp (by simpa [A] using hiA)
+        have hAI := Finset.mem_range.mp hA.1
+        exact mem_carryTwoPositions_iff.mpr
+          ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hA.2⟩
+      · have hB := mem_carryTwoPositions_iff.mp (by simpa [B] using hiB)
+        have hBI := Finset.mem_Ico.mp hB.1
+        exact mem_carryTwoPositions_iff.mpr
+          ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hB.2⟩
+    · intro hi
+      have hI := mem_carryTwoPositions_iff.mp hi
+      by_cases hleft : i < canonicalBlockStartTime n q
+      · apply Finset.mem_union_left
+        exact (show i ∈ A by
+          apply mem_carryTwoPositions_iff.mpr
+          exact ⟨Finset.mem_Ico.mpr ⟨by omega, hleft⟩, hI.2⟩)
+      · apply Finset.mem_union_right
+        exact (show i ∈ B by
+          apply mem_carryTwoPositions_iff.mpr
+          exact ⟨Finset.mem_Ico.mpr ⟨by omega,
+            (Finset.mem_Ico.mp hI.1).2⟩, hI.2⟩)
+  have hsum := Finset.sum_range_add_sum_Ico
+    (fun k => canonicalQueueDemand n k) hqm
+  rw [sum_canonicalQueueDemand_range_eq_sourceClaims_card,
+    sum_canonicalQueueDemand_range_eq_sourceClaims_card] at hsum
+  change A.card + (∑ k ∈ Finset.Ico q m, canonicalQueueDemand n k) = _ at hsum
+  have hcard : A.card + B.card =
+      (carryTwoPositions n (Finset.Ico 0 (canonicalBlockStartTime n m))).card := by
+    rw [← Finset.card_union_of_disjoint hdisj, hunion]
+  change (∑ k ∈ Finset.Ico q m, canonicalQueueDemand n k) = B.card
+  omega
+
+/-- Carry-two source addresses in the last `H` units of actual orbit time. -/
+noncomputable def canonicalRecentSourceClaimCarrier
+    (n : OddNat) (H m : ℕ) : Finset ℕ :=
+  carryTwoPositions n
+    (Finset.Ico (canonicalBlockStartTime n m - H)
+      (canonicalBlockStartTime n m))
+
+/-- A source-time interval of width at most `H` contains at most `H` claims. -/
+theorem card_canonicalRecentSourceClaimCarrier_le
+    (n : OddNat) (H m : ℕ) :
+    (canonicalRecentSourceClaimCarrier n H m).card ≤ H := by
+  classical
+  calc
+    (canonicalRecentSourceClaimCarrier n H m).card ≤
+        (Finset.Ico (canonicalBlockStartTime n m - H)
+          (canonicalBlockStartTime n m)).card := by
+      unfold canonicalRecentSourceClaimCarrier carryTwoPositions
+      exact Finset.card_filter_le _ _
+    _ ≤ H := by simp; omega
+
+@[simp] theorem canonicalRecentSourceClaimCarrier_zero_time
+    (n : OddNat) (H : ℕ) :
+    canonicalRecentSourceClaimCarrier n H 0 = ∅ := by
+  simp [canonicalRecentSourceClaimCarrier, canonicalBlockStartTime,
+    canonicalEndpointBlockStart, carryTwoPositions]
+
+@[simp] theorem canonicalRecentSourceClaimCarrier_zero_horizon
+    (n : OddNat) (m : ℕ) :
+    canonicalRecentSourceClaimCarrier n 0 m = ∅ := by
+  simp [canonicalRecentSourceClaimCarrier, carryTwoPositions]
+
+/-- Conditional source-age surface: every outstanding anonymous claim is
+represented by a carry-two source in the preceding `H` orbit times. -/
+def CanonicalOutstandingQueueCoveredByRecentSourceClaims
+    (n : OddNat) (H : ℕ) : Prop :=
+  ∀ m, canonicalOutstandingClaimQueueBeforeBlock n m ≤
+    (canonicalRecentSourceClaimCarrier n H m).card
+
+/-- Uniform source-age coverage immediately bounds every pre-block queue. -/
+theorem canonicalQueueBeforeBlock_le_of_recentSourceClaims
+    {n : OddNat} {H : ℕ}
+    (h : CanonicalOutstandingQueueCoveredByRecentSourceClaims n H) (m : ℕ) :
+    canonicalOutstandingClaimQueueBeforeBlock n m ≤ H :=
+  (h m).trans (card_canonicalRecentSourceClaimCarrier_le n H m)
+
+/-- Uniform source-age coverage gives the public post-block queue bound. -/
+theorem CanonicalOutstandingQueueCoveredByRecentSourceClaims.to_queueUniformUpperBound
+    {n : OddNat} {H : ℕ}
+    (h : CanonicalOutstandingQueueCoveredByRecentSourceClaims n H) :
+    CanonicalOutstandingClaimQueueUniformUpperBound n H := by
+  intro k
+  simpa using canonicalQueueBeforeBlock_le_of_recentSourceClaims h (k + 1)
+
+/-- The refined lag route reaches endpoint width once a uniform source-age
+theorem is supplied. -/
+theorem CanonicalOutstandingQueueCoveredByRecentSourceClaims.to_endpointWidthUniformUpperBound
+    {n : OddNat} {H : ℕ}
+    (h : CanonicalOutstandingQueueCoveredByRecentSourceClaims n H) :
+    CanonicalEndpointWidthUniformUpperBound n (bitWidth n.1 + H) :=
+  h.to_queueUniformUpperBound.to_endpointWidthUniformUpperBound
+
+/-!
+No uniform `H` is asserted here.  The remaining input on this route is exactly
+a theorem that every outstanding canonical claim has source age at most one
+fixed `H`.  The carrier preserves actual source addresses, unlike block-count
+lag alone.
+-/
+
+end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean
index 3f0f8075..bbe77bcf 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean
@@ -5,6 +5,7 @@ Authors: D. and Wise Wolf.
 -/

 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPrimitiveExcursion
+import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmortizedResource

 #print "file: DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition"

@@ -293,6 +294,63 @@ No currently audited low-bit signature has this edgewise theorem yet.

 end CanonicalFiniteSignedTransitionPotentialCertificate

+/-! ## Circular reverse construction audit -/
+
+/-- The signed canonical edge is bounded by the actual reflected-queue
+increment across that edge. -/
+theorem endpointAccountingTerm_le_queueBeforeBlock_increment
+    (n : OddNat) (k : ℕ) :
+    endpointAccountingTerm n k ≤
+      (canonicalOutstandingClaimQueueBeforeBlock n (k + 1) : ℤ) -
+        canonicalOutstandingClaimQueueBeforeBlock n k := by
+  rw [endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount]
+  change (canonicalQueueDemand n k : ℤ) - canonicalQueueService n k ≤ _
+  rw [canonicalOutstandingClaimQueueBeforeBlock_succ]
+  have hbalance := canonicalOutstandingClaimQueue_add_consumed n k
+  have hconsumed := canonicalQueueConsumed_le_service n k
+  omega
+
+/-- A queue bound can manufacture a finite signed certificate by using the
+bounded queue itself as the signature and potential.  This construction is a
+semantic circularity regression, not an arithmetic solution. -/
+noncomputable def canonicalFiniteSignedCertificateOfQueueBound
+    {n : OddNat} {C : ℕ}
+    (hC : CanonicalOutstandingClaimQueueUniformUpperBound n C) :
+    CanonicalFiniteSignedTransitionPotentialCertificate n (Fin (C + 1)) where
+  signature k := ⟨canonicalOutstandingClaimQueueBeforeBlock n k, by
+    cases k with
+    | zero => simp
+    | succ k =>
+        simp only [canonicalOutstandingClaimQueueBeforeBlock_succ]
+        exact Nat.lt_succ_of_le (hC k)⟩
+  projectedUpperWeight s t := (t.val : ℤ) - s.val
+  potential s := s.val
+  bound := C
+  actual_le_projected k := by
+    exact endpointAccountingTerm_le_queueBeforeBlock_increment n k
+  projected_le_potential_diff _ _ := le_rfl
+  potential_nonneg _ := by omega
+  potential_le_bound s := Int.ofNat_le.mpr (Nat.le_of_lt_succ s.isLt)
+
+/-- Unrestricted existential canonical finite-certificate existence is exactly
+as strong as existential queue boundedness. -/
+theorem exists_canonicalFiniteSignedCertificate_iff_exists_queueUniformUpperBound
+    (n : OddNat) :
+    (∃ C, Nonempty
+        (CanonicalFiniteSignedTransitionPotentialCertificate n (Fin (C + 1)))) ↔
+      ∃ C, CanonicalOutstandingClaimQueueUniformUpperBound n C := by
+  constructor
+  · rintro ⟨_C, ⟨P⟩⟩
+    exact ⟨P.bound, P.to_queueUniformUpperBound⟩
+  · rintro ⟨C, hC⟩
+    exact ⟨C, ⟨canonicalFiniteSignedCertificateOfQueueBound hC⟩⟩
+
+/-!
+The reverse construction deliberately chooses its signature from `hC`.
+Therefore only a structurally predefined signature, fixed independently of an
+assumed queue ceiling, can provide a noncircular arithmetic certificate.
+-/
+
 namespace FiniteSignedTransitionPotentialCertificate

 variable {State Signature : Type*} [Fintype Signature]
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/RawLowSignatureObstruction.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/RawLowSignatureObstruction.lean
new file mode 100644
index 00000000..fe2fe960
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/RawLowSignatureObstruction.lean
@@ -0,0 +1,378 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.RawLowSignatureObstruction"
+
+namespace DkMath.Collatz
+
+/-!
+# Fixed low-window obstruction
+
+A fixed low binary window cannot distinguish a sufficiently long finite
+all-ones word from its 2-adic all-ones continuation.  This module turns that
+observation into a parameterized positive closed-signature edge.  It rejects
+only the concrete low signature defined below; it does not reject finite
+signatures carrying an upper boundary or a dynamically decreasing rank.
+-/
+
+/-! ## The all-ones source and its first two successors -/
+
+/-- A positive odd word whose visible low `r` bits are all one. -/
+noncomputable def rawAllOnesWitness (r : ℕ) : OddNat := by
+  refine ⟨2 ^ (r + 2) - 1, ?_⟩
+  rw [show r + 2 = (r + 1) + 1 by omega, pow_succ]
+  have hp : 0 < 2 ^ (r + 1) := pow_pos (by norm_num) _
+  omega
+
+@[simp]
+theorem rawAllOnesWitness_val (r : ℕ) :
+    (rawAllOnesWitness r).1 = 2 ^ (r + 2) - 1 := rfl
+
+/-- First residual odd word after removing the visible factor two. -/
+def rawAllOnesFirstTargetValue (r : ℕ) : ℕ :=
+  3 * 2 ^ (r + 1) - 1
+
+/-- Second residual odd word on the same height-one channel. -/
+def rawAllOnesSecondTargetValue (r : ℕ) : ℕ :=
+  9 * 2 ^ r - 1
+
+private theorem rawAllOnes_three_mul_add_one
+    (r : ℕ) :
+    3 * (rawAllOnesWitness r).1 + 1 =
+      2 * rawAllOnesFirstTargetValue r := by
+  simp only [rawAllOnesWitness_val, rawAllOnesFirstTargetValue]
+  have hp : 0 < 2 ^ (r + 1) := pow_pos (by norm_num) _
+  rw [show r + 2 = (r + 1) + 1 by omega, pow_succ]
+  omega
+
+private theorem rawAllOnes_firstTarget_odd
+    (r : ℕ) : rawAllOnesFirstTargetValue r % 2 = 1 := by
+  unfold rawAllOnesFirstTargetValue
+  rw [show r + 1 = r + 1 by rfl, pow_succ]
+  have hp : 0 < 2 ^ r := pow_pos (by norm_num) _
+  omega
+
+/-- The all-ones source lies on the exact height-one channel. -/
+theorem s_rawAllOnesWitness_eq_one (r : ℕ) :
+    s (rawAllOnesWitness r) = 1 := by
+  have hne : rawAllOnesFirstTargetValue r ≠ 0 := by
+    unfold rawAllOnesFirstTargetValue
+    have hp : 0 < 2 ^ (r + 1) := pow_pos (by norm_num) _
+    omega
+  have hv := (DkMath.ABC.padic_val_two_of_even
+    (rawAllOnesFirstTargetValue r)).2 hne
+  change v2 (3 * (rawAllOnesWitness r).1 + 1) = 1
+  rw [rawAllOnes_three_mul_add_one]
+  simpa [v2,
+    v2_odd _ (rawAllOnes_firstTarget_odd r)] using hv
+
+/-- Exact first accelerated successor of the all-ones source. -/
+theorem T_rawAllOnesWitness_val (r : ℕ) :
+    (T (rawAllOnesWitness r)).1 = rawAllOnesFirstTargetValue r := by
+  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one _
+    (s_rawAllOnesWitness_eq_one r)]
+  rw [rawAllOnes_three_mul_add_one]
+  simp
+
+private theorem rawAllOnes_firstTarget_three_mul_add_one
+    (r : ℕ) :
+    3 * rawAllOnesFirstTargetValue r + 1 =
+      2 * rawAllOnesSecondTargetValue r := by
+  simp only [rawAllOnesFirstTargetValue, rawAllOnesSecondTargetValue]
+  rw [show r + 1 = r + 1 by rfl, pow_succ]
+  have hp : 0 < 2 ^ r := pow_pos (by norm_num) _
+  omega
+
+private theorem rawAllOnes_secondTarget_odd
+    {r : ℕ} (hr : 1 ≤ r) : rawAllOnesSecondTargetValue r % 2 = 1 := by
+  unfold rawAllOnesSecondTargetValue
+  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hr
+  rw [show 1 + q = q + 1 by omega, pow_succ]
+  have hp : 0 < 2 ^ q := pow_pos (by norm_num) _
+  omega
+
+/-- The first successor remains on the exact height-one channel. -/
+theorem s_T_rawAllOnesWitness_eq_one
+    {r : ℕ} (hr : 1 ≤ r) :
+    s (T (rawAllOnesWitness r)) = 1 := by
+  have hne : rawAllOnesSecondTargetValue r ≠ 0 := by
+    unfold rawAllOnesSecondTargetValue
+    have hp : 0 < 2 ^ r := pow_pos (by norm_num) _
+    omega
+  have hv := (DkMath.ABC.padic_val_two_of_even
+    (rawAllOnesSecondTargetValue r)).2 hne
+  change v2 (3 * (T (rawAllOnesWitness r)).1 + 1) = 1
+  rw [T_rawAllOnesWitness_val,
+    rawAllOnes_firstTarget_three_mul_add_one]
+  simpa [v2,
+    v2_odd _ (rawAllOnes_secondTarget_odd hr)] using hv
+
+/-- Exact second accelerated successor, used to audit the target growth flag. -/
+theorem T_T_rawAllOnesWitness_val
+    {r : ℕ} (hr : 1 ≤ r) :
+    (T (T (rawAllOnesWitness r))).1 = rawAllOnesSecondTargetValue r := by
+  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one _
+    (s_T_rawAllOnesWitness_eq_one hr)]
+  rw [T_rawAllOnesWitness_val,
+    rawAllOnes_firstTarget_three_mul_add_one]
+  simp
+
+/-! ## Width, residue, and upper-carry audit -/
+
+/-- Exact width of the finite all-ones source word. -/
+theorem bitWidth_rawAllOnesWitness
+    (r : ℕ) :
+    bitWidth (rawAllOnesWitness r).1 = r + 2 := by
+  have hp : 0 < 2 ^ (r + 1) := pow_pos (by norm_num) _
+  have hlo : 2 ^ (r + 1) ≤ (rawAllOnesWitness r).1 := by
+    rw [rawAllOnesWitness_val,
+      show r + 2 = (r + 1) + 1 by omega, pow_succ]
+    omega
+  have hhi : (rawAllOnesWitness r).1 < 2 ^ ((r + 1) + 1) := by
+    rw [rawAllOnesWitness_val,
+      show (r + 1) + 1 = r + 2 by omega]
+    have hpow : 0 < 2 ^ (r + 2) := pow_pos (by norm_num) _
+    omega
+  have h := bitWidth_eq_add_one_of_pow_le_lt hlo hhi
+  omega
+
+/-- Exact width of the first all-ones successor. -/
+theorem bitWidth_T_rawAllOnesWitness
+    (r : ℕ) :
+    bitWidth (T (rawAllOnesWitness r)).1 = r + 3 := by
+  have hp : 0 < 2 ^ (r + 1) := pow_pos (by norm_num) _
+  have hlo : 2 ^ (r + 2) ≤ (T (rawAllOnesWitness r)).1 := by
+    rw [T_rawAllOnesWitness_val]
+    unfold rawAllOnesFirstTargetValue
+    rw [show r + 2 = (r + 1) + 1 by omega, pow_succ]
+    omega
+  have hhi : (T (rawAllOnesWitness r)).1 < 2 ^ ((r + 2) + 1) := by
+    rw [T_rawAllOnesWitness_val]
+    unfold rawAllOnesFirstTargetValue
+    have hpow : 2 ^ ((r + 2) + 1) = 4 * 2 ^ (r + 1) := by
+      rw [show (r + 2) + 1 = (r + 1) + 2 by omega, pow_add]
+      norm_num [Nat.mul_comm]
+    rw [hpow]
+    omega
+  have h := bitWidth_eq_add_one_of_pow_le_lt hlo hhi
+  omega
+
+/-- Exact width of the second all-ones successor. -/
+theorem bitWidth_T_T_rawAllOnesWitness
+    {r : ℕ} (hr : 1 ≤ r) :
+    bitWidth (T (T (rawAllOnesWitness r))).1 = r + 4 := by
+  have hp : 2 ≤ 2 ^ r := by
+    obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hr
+    rw [show 1 + q = q + 1 by omega, pow_succ]
+    have hq : 0 < 2 ^ q := pow_pos (by norm_num) _
+    omega
+  have hlo : 2 ^ (r + 3) ≤ (T (T (rawAllOnesWitness r))).1 := by
+    rw [T_T_rawAllOnesWitness_val hr]
+    unfold rawAllOnesSecondTargetValue
+    rw [pow_add]
+    norm_num
+    omega
+  have hhi : (T (T (rawAllOnesWitness r))).1 < 2 ^ ((r + 3) + 1) := by
+    rw [T_T_rawAllOnesWitness_val hr]
+    unfold rawAllOnesSecondTargetValue
+    rw [show (r + 3) + 1 = r + 4 by omega, pow_add]
+    norm_num
+    omega
+  have h := bitWidth_eq_add_one_of_pow_le_lt hlo hhi
+  omega
+
+/-- The first edge increases binary width by exactly one. -/
+theorem bitWidth_T_rawAllOnesWitness_eq_add_one
+    (r : ℕ) :
+    bitWidth (T (rawAllOnesWitness r)).1 =
+      bitWidth (rawAllOnesWitness r).1 + 1 := by
+  rw [bitWidth_T_rawAllOnesWitness, bitWidth_rawAllOnesWitness]
+
+/-- The second edge also increases binary width by exactly one. -/
+theorem bitWidth_T_T_rawAllOnesWitness_eq_add_one
+    {r : ℕ} (hr : 1 ≤ r) :
+    bitWidth (T (T (rawAllOnesWitness r))).1 =
+      bitWidth (T (rawAllOnesWitness r)).1 + 1 := by
+  rw [bitWidth_T_T_rawAllOnesWitness hr, bitWidth_T_rawAllOnesWitness]
+
+private theorem mul_add_pred_mod_self
+    {m c : ℕ} (hm : 0 < m) :
+    (c * m + (m - 1)) % m = m - 1 := by
+  have hlt : m - 1 < m := by omega
+  simp [Nat.add_mod, Nat.mod_eq_of_lt hlt]
+
+/-- The source shows an all-ones residue in every fixed lower `r`-window. -/
+theorem rawAllOnesWitness_mod_pow
+    (r : ℕ) :
+    (rawAllOnesWitness r).1 % 2 ^ r = 2 ^ r - 1 := by
+  have hp : 0 < 2 ^ r := pow_pos (by norm_num) _
+  have hval : (rawAllOnesWitness r).1 =
+      3 * 2 ^ r + (2 ^ r - 1) := by
+    rw [rawAllOnesWitness_val,
+      show r + 2 = r + 2 by rfl, pow_add]
+    norm_num
+    omega
+  rw [hval]
+  exact mul_add_pred_mod_self hp
+
+/-- The first target has the same all-ones lower `r`-window. -/
+theorem T_rawAllOnesWitness_mod_pow
+    (r : ℕ) :
+    (T (rawAllOnesWitness r)).1 % 2 ^ r = 2 ^ r - 1 := by
+  have hp : 0 < 2 ^ r := pow_pos (by norm_num) _
+  have hval : (T (rawAllOnesWitness r)).1 =
+      5 * 2 ^ r + (2 ^ r - 1) := by
+    rw [T_rawAllOnesWitness_val]
+    unfold rawAllOnesFirstTargetValue
+    rw [show r + 1 = r + 1 by rfl, pow_add]
+    norm_num
+    omega
+  rw [hval]
+  exact mul_add_pred_mod_self hp
+
+/-- The source own-width raw step crosses the next binary boundary. -/
+theorem stateUpperCarry_rawAllOnesWitness_eq_two
+    (r : ℕ) :
+    stateUpperCarry (rawAllOnesWitness r).1 = 2 := by
+  have hbalance := bitWidth_T_add_height_eq_bitWidth_add_upperCarry
+    (rawAllOnesWitness r)
+  rw [s_rawAllOnesWitness_eq_one,
+    bitWidth_T_rawAllOnesWitness_eq_add_one] at hbalance
+  omega
+
+/-- The first target also has own-width upper carry two. -/
+theorem stateUpperCarry_T_rawAllOnesWitness_eq_two
+    {r : ℕ} (hr : 1 ≤ r) :
+    stateUpperCarry (T (rawAllOnesWitness r)).1 = 2 := by
+  have hbalance := bitWidth_T_add_height_eq_bitWidth_add_upperCarry
+    (T (rawAllOnesWitness r))
+  rw [s_T_rawAllOnesWitness_eq_one hr,
+    bitWidth_T_T_rawAllOnesWitness_eq_add_one hr] at hbalance
+  omega
+
+/-! ## The audited finite low signature -/
+
+/-- Coarse 2-adic height class retained by the low signature. -/
+inductive RawLowHeightClass where
+  | one
+  | atLeastTwo
+  deriving DecidableEq, Fintype
+
+/--
+The deliberately fixed observation under audit.  It contains only a lower
+`r`-bit residue, own-width upper carry, the split `s = 1` versus `s ≥ 2`, and
+whether the next accelerated step increases width.  No absolute width or
+upper-boundary coordinate is retained.
+-/
+structure FixedLowRawSignature (r : ℕ) where
+  residue : Fin (2 ^ r)
+  upperCarry : Fin 3
+  heightClass : RawLowHeightClass
+  widthGrowth : Bool
+  deriving DecidableEq, Fintype
+
+/-- The four-coordinate finite observation of one positive odd state. -/
+noncomputable def fixedLowRawSignature
+    (r : ℕ) (x : OddNat) : FixedLowRawSignature r where
+  residue := ⟨x.1 % 2 ^ r, Nat.mod_lt _ (pow_pos (by norm_num) _)⟩
+  upperCarry := ⟨stateUpperCarry x.1,
+    upperCarry3n1_lt_three_of_lt_pow (lt_pow_bitWidth (by
+      have hodd := x.2
+      omega))⟩
+  heightClass := if s x = 1 then .one else .atLeastTwo
+  widthGrowth := decide (bitWidth (T x).1 = bitWidth x.1 + 1)
+
+/-- The all-ones edge is closed under every coordinate of the audited fixed
+low signature. -/
+theorem fixedLowRawSignature_T_rawAllOnesWitness_eq
+    {r : ℕ} (hr : 1 ≤ r) :
+    fixedLowRawSignature r (T (rawAllOnesWitness r)) =
+      fixedLowRawSignature r (rawAllOnesWitness r) := by
+  unfold fixedLowRawSignature
+  congr 1
+  · apply Fin.ext
+    exact T_rawAllOnesWitness_mod_pow r |>.trans
+      (rawAllOnesWitness_mod_pow r).symm
+  · apply Fin.ext
+    change stateUpperCarry (T (rawAllOnesWitness r)).1 =
+      stateUpperCarry (rawAllOnesWitness r).1
+    rw [stateUpperCarry_T_rawAllOnesWitness_eq_two hr,
+      stateUpperCarry_rawAllOnesWitness_eq_two]
+  · simp [s_T_rawAllOnesWitness_eq_one hr,
+      s_rawAllOnesWitness_eq_one]
+  · simp [bitWidth_T_rawAllOnesWitness_eq_add_one,
+      bitWidth_T_T_rawAllOnesWitness_eq_add_one hr]
+
+/-- Signed binary-width change on an arbitrary concrete edge. -/
+def rawSignedWidthWeight (a b : OddNat) : ℤ :=
+  (bitWidth b.1 : ℤ) - bitWidth a.1
+
+/-- The closed-signature all-ones edge has positive realized weight `+1`. -/
+theorem rawSignedWidthWeight_rawAllOnesWitness_eq_one
+    (r : ℕ) :
+    rawSignedWidthWeight (rawAllOnesWitness r)
+      (T (rawAllOnesWitness r)) = 1 := by
+  unfold rawSignedWidthWeight
+  rw [bitWidth_T_rawAllOnesWitness_eq_add_one]
+  omega
+
+/-!
+`CoversAllRawOddTransitionsWithFixedLowSignature` is intentionally stronger
+than observing a finite table: it requires the certificate relation and its
+actual edge weight to cover every accelerated odd transition, while fixing the
+signature to the arithmetic observation above.  The following obstruction is
+therefore structural and uniform in `r`, not a bounded-search result.
+-/
+
+/-- Coverage contract for the specific audited low signature. -/
+def CoversAllRawOddTransitionsWithFixedLowSignature
+    {r : ℕ}
+    (C : RelationalFiniteSignedTransitionPotentialCertificate
+      OddNat (FixedLowRawSignature r)) : Prop :=
+  (∀ x, C.Step x (T x)) ∧
+    (∀ x, C.signature x = fixedLowRawSignature r x) ∧
+      (∀ x, C.actualWeight x (T x) = rawSignedWidthWeight x (T x))
+
+/--
+No bounded potential certificate on the fixed low signature can soundly cover
+all positive odd transitions.  The all-ones source gives a related edge of
+weight `+1` whose endpoint signatures coincide, whereas the potential axiom
+forces every such projected edge to have weight at most zero.
+
+This does not exclude a finite signature with an absolute upper-boundary
+coordinate or a separately proved decreasing rank.
+-/
+theorem not_coversAllRawOddTransitionsWithFixedLowSignature
+    {r : ℕ} (hr : 1 ≤ r)
+    (C : RelationalFiniteSignedTransitionPotentialCertificate
+      OddNat (FixedLowRawSignature r)) :
+    ¬ CoversAllRawOddTransitionsWithFixedLowSignature C := by
+  rintro ⟨hstep, hsignature, hweight⟩
+  let x := rawAllOnesWitness r
+  have hsig : C.signature (T x) = C.signature x := by
+    rw [hsignature, hsignature]
+    exact fixedLowRawSignature_T_rawAllOnesWitness_eq hr
+  have hactual := C.actual_le_projected x (T x) (hstep x)
+  have hprojected := C.projected_le_potential_diff
+    (C.signature x) (C.signature (T x))
+  rw [hsig] at hactual hprojected
+  simp only [sub_self] at hprojected
+  rw [hweight, rawSignedWidthWeight_rawAllOnesWitness_eq_one] at hactual
+  omega
+
+/-- Existential form: the audited fixed low signature admits no global sound
+bounded-potential certificate. -/
+theorem not_exists_fixedLowRawSignature_globalCertificate
+    {r : ℕ} (hr : 1 ≤ r) :
+    ¬ ∃ C : RelationalFiniteSignedTransitionPotentialCertificate
+        OddNat (FixedLowRawSignature r),
+      CoversAllRawOddTransitionsWithFixedLowSignature C := by
+  rintro ⟨C, hC⟩
+  exact not_coversAllRawOddTransitionsWithFixedLowSignature hr C hC
+
+end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-333.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-333.md
new file mode 100644
index 00000000..0d64c034
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-333.md
@@ -0,0 +1,173 @@
+# Petal / FloatWindow implementation report - checkpoint 333
+
+## Result
+
+This checkpoint closes the requested source-time accounting layer and proves a
+uniform obstruction to the audited fixed low-bit signature family.
+
+The outcome separates two routes sharply:
+
+1. the source-time route remains viable, with one explicit missing theorem:
+   uniform source age for outstanding canonical claims;
+2. the fixed low-bit signature consisting only of residue, upper carry,
+   height class, and width-growth flag is rejected for every fixed depth
+   `r >= 1`.
+
+No claim is made against finite signatures that retain an upper boundary or a
+separately proved decreasing rank.
+
+## Circular finite-certificate regression
+
+`FiniteSignedTransition.lean` now proves
+
+```text
+endpointAccountingTerm n k
+  <= queueBefore (k+1) - queueBefore k.
+```
+
+Any assumed queue bound `C` can therefore manufacture a certificate whose
+signature and potential are the queue value itself in `Fin (C+1)`.  Lean proves
+the semantic equivalence
+
+```text
+exists canonical finite certificate
+  <-> exists canonical queue uniform upper bound.
+```
+
+This is a circularity regression, not an arithmetic solution: the constructed
+signature depends on the queue bound it is meant to prove.  A noncircular
+certificate must start from a structurally predefined arithmetic signature.
+
+## Exact source-time accounting
+
+The new `CanonicalSourceTimeLag.lean` proves the exact recurrence
+
+```text
+startTime (k+1) = startTime k + blockLength k
+```
+
+and its range and `Ico` telescopes.  Consequently canonical demand over blocks
+`[q,m)` is bounded by the actual orbit-time span
+
+```text
+sum demand [q,m) <= startTime m - startTime q.
+```
+
+The stronger carrier identity also closes:
+
+```text
+sum demand [q,m)
+  = card {i in [startTime q,startTime m) | CarryTwoDebtAt n i}.
+```
+
+Thus block demand is not merely bounded by elapsed time; it is exactly the
+number of carry-two source addresses in that time interval.
+
+For the last `H` source-time units, `canonicalRecentSourceClaimCarrier` has
+cardinality at most `H`, with regressions at time zero and horizon zero.  The
+conditional predicate
+
+```text
+CanonicalOutstandingQueueCoveredByRecentSourceClaims n H
+```
+
+therefore yields both a queue bound by `H` and an endpoint-width bound by
+`bitWidth n + H`.  No such uniform `H` is asserted.  The remaining input is
+exactly a uniform source-age theorem for outstanding claims.
+
+## All-ones raw family
+
+`RawLowSignatureObstruction.lean` defines
+
+```text
+x_r = 2^(r+2) - 1.
+```
+
+For every `r >= 1`, Lean proves
+
+```text
+T x_r       = 3 * 2^(r+1) - 1
+T (T x_r)   = 9 * 2^r - 1
+s x_r       = 1
+s (T x_r)   = 1
+width x_r   = r + 2
+width (T x_r)       = r + 3
+width (T (T x_r))   = r + 4.
+```
+
+Both `x_r` and `T x_r` have residue `2^r - 1` modulo `2^r`, upper carry two,
+height class one, and a true one-step width-growth flag.  Their audited fixed
+low signatures are therefore equal, while the realized signed width weight of
+the edge `x_r -> T x_r` is exactly `+1`.
+
+## Fixed low-signature obstruction
+
+The finite type `FixedLowRawSignature r` contains exactly:
+
+```text
+residue modulo 2^r
+upper carry in Fin 3
+height class: one / at least two
+width-growth Boolean
+```
+
+The theorem
+
+```text
+not_exists_fixedLowRawSignature_globalCertificate
+```
+
+states that for every `r >= 1` there is no relational bounded-potential
+certificate using this exact signature that covers all accelerated odd edges
+with their signed width weight.
+
+The proof uses the one-edge all-ones witness.  Equal endpoint signatures force
+the projected potential difference to be zero, but soundness must dominate the
+realized weight `+1`, yielding a contradiction.
+
+This establishes a parameterized obstruction, not a finite search result.  A
+fixed lower window confuses a sufficiently long finite all-ones prefix with
+its 2-adic all-ones continuation.
+
+## Route decision
+
+The audited fixed low-bit route is closed negatively.  Enlarging `r` does not
+repair it, because the witness family grows with `r`.
+
+The source-time claim-age route remains the clean positive route:
+
+```text
+uniform source-time claim age
+  -> recent-source coverage
+  -> queue bound
+  -> endpoint-width bound.
+```
+
+The abstract certificate route remains legitimate only after choosing a
+signature independently of the desired queue bound.  The next plausible
+signature experiment must expose information absent from every fixed lower
+window, such as an upper-boundary/eventually-zero coordinate or a proved
+decreasing rank.
+
+## Additional results
+
+Beyond the minimum request, the implementation records the exact second
+successor, all three exact widths, an existential no-certificate theorem, and
+the exact prefix as well as interval source-carrier cardinality identities.
+
+## Verification
+
+The following gates passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition
+lake build DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceTimeLag
+lake build DkMath.Collatz.PetalBridge.FloatWindow.RawLowSignatureObstruction
+lake build DkMath.Collatz.PetalBridge.FloatWindow
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath
+git diff --check
+```
+
+The three changed implementation modules contain no `sorry` or `admit`, and no
+new heartbeat override was introduced.
````
`````
