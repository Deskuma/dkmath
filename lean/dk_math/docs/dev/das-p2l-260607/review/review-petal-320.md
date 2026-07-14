# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentSelectedCarrier

gch: 5ecca029d1102d565b12d74b87be96182c8a0cf9

## Report

(24m45s)

cp-320 を stopping rule の地点まで実装しました。

**確定した事実**

- 正ドリフトかつ全 source claim の block は、必ず saturated block。
- depth-zero を排除し、selected pressure depth は常に `1 ≤ depth`。
- nonsaturated positive block の drift は、実在する continuation carrier の濃度以下。
- 異なる canonical block の selected carrier は互いに素。
- 全 positive-drift unit から
  `global selected carrier ⊕ saturated tokens`
  への有限 injection が存在。
- saturation token 数は `(m - q + 2) / 2` 以下。
- global carrier は有限な depth bucket に厳密分解できる。
- 各 depth bucket は既存の固定深さ continuation-fiber API に接続済み。

追加ファイル:

- [UniversalPaymentSelectedCarrier.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentSelectedCarrier.lean)
- [report-petal-320.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-320.md)

**現在の真正な障害**

source incidence の重複ではありません。残るのは、固定深さ bucket の各 incidence を、有限境界資源・separator・`NoLift` obstruction のいずれかへ、寄与を保存して運ぶ global transport theorem です。

saturated token も、後続 drift がゼロの場合は返済されません。したがって、負ドリフト・selected incidence・upper-zero boundary のいずれかへの injective charge が次の本命です。

検証済み:

- focused module build
- `DkMath.Collatz.PetalBridge.FloatWindow`
- `DkMath.Collatz.PetalBridge`
- `DkMath`
- 新規ファイル no-sorry
- `git diff --check` pass

## Review

## 結論

**全面採用。大きな checkpoint じゃ。**

cp-320 は、正 drift を単なる整数不等式として扱う段階から、

> **正 drift の各 unit を、実在する正深度 continuation incidence、または孤立 saturated token に収容する**

段階へ進んだ。

これにより、現在の構造は、

$$
\text{positive drift units}
\hookrightarrow
\text{selected pressure incidences}
\sqcup
\text{saturated tokens}
$$

まで有限化された。

さらに selected incidence は canonical block 間で互いに素であり、動的 depth ごとの bucket へ厳密に分解され、既存の fixed-depth continuation fiber まで到達した。source-incidence multiplicity は閉じたと評価してよい。

ただし、二つの意味境界を補正する。

1. 現在の大域 embedding は cardinality から選ばれた任意の injection であり、block を保存する incidence map ではない。
2. fixed-depth API への接続は現在、各要素の membership までであり、prefix continuation carrier への明示的 embedding と cardinality theorem はまだない。

どちらも数学的障害ではない。次 checkpoint 冒頭で閉じられる API 補強じゃ。

そして、その先の真正な障害は、さらに正確に言えば、

> **positive pressure の「存在する depth 数」ではなく、各 depth に積み上がる pressure amplitude をどう支配するか**

である。

---

## 1. Full claim rigidity は強い

今回、

$$
0<D_k
$$

かつ、

$$
A_k=L_k
$$

なら、必ず saturated block になることが証明された。

ここで、

- $D_k$ は block drift
- $A_k$ は claim count
- $L_k$ は block length

じゃ。

中核は強化指数不等式、

$$
3^L+2^{L-1}\le2^{2L-1}
$$

である。

full claim なら、

$$
D=L-v
$$

となるため、width ledger は next start に $L-v$ bit の増加を要求する。

一方 normal form は next start を、それより厳密に小さい dyadic scale へ押し込む。

この上下矛盾から $L\ge3$ を排除し、

$$
L=2,\qquad v=1
$$

へ潰して saturation を得た。

これは cp-319 の saturation rigidity をさらに強化している。

正確には今や、

$$
\operatorname{Saturated}(k)
\Longleftrightarrow
D_k>0\land A_k=L_k
$$

じゃ。

つまり saturated block は、

> 正 drift block のうち、block 内の全 source が claim になった唯一の完全飽和型

として特徴づけられた。

---

## 2. depth $0$ の排除

これは重要な修正じゃ。

以前の粗い動的 pressure depth は、terminal valuation $v=1$ の nonsaturated block で depth $0$ を使っていた。

depth $0$ の pressure は block length 全体を数えるため、数値上は drift を支配できるが、pressure obstruction としての意味が薄かった。

今回は、

$$
d_k=
\begin{cases}
1&v_k=1\\
v_k-1&v_k\ge2
\end{cases}
$$

とし、常に、

$$
1\le d_k
$$

を確保した。

$v=1$ の nonsaturated positive block では、full claim rigidity により、

$$
A<L
$$

なので、

$$
D=A-1\le L-2
$$

となる。

一方 depth $1$ の pressure は、

$$
M_1=L-2
$$

じゃ。

したがって、

$$
D\le M_1
$$

が正深度だけで閉じた。

これで selected pressure は、もはや block-length の粗い代用品ではない。

---

## 3. Pressure が実在 carrier になった

正の内部 depth $d$ では、

$$
M_k(d)=
\left|
\operatorname{ContinuationFiber}_k(d+1)
\right|
$$

が証明された。

したがって、

```lean
canonicalSelectedPressureCarrier n k
```

は、

```lean
canonicalPaymentBlockContinuationFiber n k
  (canonicalSelectedPositivePressureDepth n k + 1)
```

という実際の source-time Finset になった。

positive nonsaturated block では、

$$
D_k\le
\left|
\operatorname{SelectedCarrier}_k
\right|
$$

じゃ。

saturated block では、

$$
D_k=1
$$

$$
\operatorname{SelectedCarrier}_k=\varnothing
$$

となり、その残差を saturated token 一個として保持する。

よって pointwise には、

$$
D_k^+
\le
|\operatorname{SelectedCarrier}*k|
+
\mathbf1*{\operatorname{Saturated}(k)}
$$

が完全に閉じた。

---

## 4. Block 間 disjointness

canonical blocks は orbit time を一意に分割する。

したがって、

$$
k\ne\ell
\Longrightarrow
B_k\cap B_\ell=\varnothing
$$

である。

selected carrier は各 block の部分集合なので、

$$
k\ne\ell
\Longrightarrow
\operatorname{Carrier}*k
\cap
\operatorname{Carrier}*\ell = \varnothing
$$

が得られた。

これは report の修正どおりじゃ。

source incidence の重複問題は、ここで終了している。

各 pressure incidence は、

- 一意な block
- 一意な orbit time
- 一意な selected depth bucket

を持つ。

---

## 5. 大域 embedding の意味境界

ここは慎重に区別すべきところじゃ。

現在の、

```lean
exists_positiveDriftUnitEmbedding_global_add_saturated
```

は、有限型の cardinality inequality から、

```lean
Function.Embedding.nonempty_iff_card_le
```

で得た存在定理である。

したがって、その injection は一般には、

```text
block k の drift unit
  → block k の selected carrier
```

とは限らない。

block $k$ の unit が、別 block $\ell$ の carrier へ送られる可能性もある。

ゆえに現段階での正確な呼び方は、

> **global cardinality embedding certificate**

じゃ。

「block-local incidence certificate」と呼ぶには、block index を保存する embedding が必要になる。

ただし pointwise inequality は既にあるので、これは容易に補える。

各 positive block $k$ について局所 embedding を選び、

- nonsaturated なら自分の selected carrier
- saturated なら自分の saturated token

へ送り、その dependent sum を取ればよい。

そうすれば、

$$
\operatorname{block}(\operatorname{image}(x)) = \operatorname{block}(x)
$$

を満たす真の incidence embedding になる。

差し戻し事項ではないが、report の「incidence certificate」は、これを追加した後に完全な意味になる。

---

## 6. Saturated token packing

saturated index は隣接しないので、block interval $[q,m]$ では、

$$
|\operatorname{Saturated}|
\le
\frac{m-q+2}{2}
$$

が得られた。

したがって、

$$
\sum D_k^+
\le
|\operatorname{GlobalCarrier}|
+
\frac{m-q+2}{2}
$$

となる。

これは正しい有限区間評価じゃ。

ただし右辺は区間長とともに線形増加し得る。

したがって、これは uniform queue bound ではない。

saturation は孤立したが、まだ「総数が有限定数以下」になったわけではない。

---

## 7. Depth bucket の Fubini 分解

global carrier が、

$$
|\operatorname{GlobalCarrier}| = \sum_{d\in\operatorname{DepthSupport}}|\operatorname{BucketCarrier}(d)|
$$

と分解された。

これは動的 depth を fixed-depth pressure API へ渡す正しい入口じゃ。

各 bucket element は、

$$
i\in
\operatorname{ContinuationFiber}_{k}(d+1)
$$

を満たす。

ただし現在証明されたのは elementwise membership までである。

次に明示すべきは、block coordinate を忘れる embedding、

$$
\operatorname{BucketCarrier}(d)
\hookrightarrow
\operatorname{OrbitContinuationRangeFiber}(d+1)
$$

じゃ。

異なる block carrier は disjoint なので、source time $i$ だけへ射影しても単射になる。

これにより、

$$
|\operatorname{BucketCarrier}(d)|
\le
\operatorname{orbitDepthContinuationFiberCount}(K,d+1)
$$

が直接得られる。

ここまで閉じれば「fixed-depth counting API に接続済み」が cardinality の意味でも完成する。

---

## 8. Active depth support が必要

現在の、

```lean
canonicalSelectedPressureDepthSupport
```

は全 positive block の selected depth を image に取る。

saturated block も positive block であり、selected depth は $1$ だが、selected carrier は空じゃ。

したがって、saturated block しか存在しない場合でも depth $1$ が support に入る可能性がある。

Fubini の零項としては問題ない。

しかし将来、

```text
support に d がある
→ depth d に pressure incidence が存在する
```

と読むと誤る。

次には、

```lean
canonicalActiveSelectedPressureDepthSupport
```

を、

```text
bucket carrier が nonempty
```

または、

```text
positive nonsaturated block がその depth を選ぶ
```

という条件で定義する方がよい。

---

## 9. 一歩先の exact pressure normal form

cp-320 の carrier identityから、より重要な固定深さ公式が見える。

block length を $L_k$ とし、$d\ge1$ とする。

各 block の pressure contribution は厳密に、

$$
M_k(d) = \left|\operatorname{ContinuationFiber}_k(d+1)\right| - \mathbf1_{L_k=d}
$$

じゃ。

場合分けすると、

- $L_k<d$ なら $0$
- $L_k=d$ なら $-1$
- $L_k=d+1$ なら $0$
- $L_k\ge d+2$ なら $L_k-d-1$

となり、式と一致する。

block interval $I$ で足せば、

$$
\sum_{k\in I}M_k(d) = C_I(d+1)-E_I(d)
$$

となる。

ここで、

$$
C_I(d+1) = \sum_{k\in I}\left|\operatorname{ContinuationFiber}_k(d+1)\right|
$$

$$
E_I(d) = \#\{k\in I\mid L_k=d\}
$$

じゃ。

prefix $I={0,\ldots,m}$ なら左辺は既存の、

```lean
SourcePressureMarginInt
```

そのものになる。

これは次 checkpoint の中心定理にすべきじゃ。

---

## 10. Bucket は「exact-length blocker + positive pressure amplitude」へ分かれる

selected bucket $B_I(d)$ は fixed-depth continuation incidencesの部分集合なので、

$$
|B_I(d)|\le C_I(d+1)
$$

じゃ。

先ほどの式から、

$$
C_I(d+1) = E_I(d)+\sum_{k\in I}M_k(d)
$$

である。

signed margin が負の場合も含めれば、

$$
|B_I(d)|
\le
E_I(d) + \left(\sum_{k\in I}M_k(d)\right)_+
$$

が得られる。

つまり、各 fixed-depth bucket の incidence は、

```text
exact length d の block token
```

または、

```text
depth d の正 pressure amplitude unit
```

へ数え直せる。

しかも exact-length token は depth 間で重ならない。

一つの block は一つの長さしか持たないからじゃ。

したがって global carrier は、

$$
|\operatorname{GlobalCarrier}|
\le
\#\{\text{blocks}\} + \sum_d \left(\operatorname{WindowPressure}(d)\right)_+
$$

へ圧縮できる。

ここで初めて、本当に残っている量が露出する。

---

## 11. 真正な障害は sign ではなく amplitude

既存 pressure packing API は主に、

- margin が正か
- positive depth が何個あるか
- positive depth がどのような pulse / island を作るか
- witness center がどの程度離れているか

を扱う。

これは **sign-level API** じゃ。

ところが cp-320 が生成した carrier は、各 depth $d$ について、

$$
\left(\operatorname{WindowPressure}(d)\right)_+
$$

個の unit を持ち得る。

例えば一つの depth に pressure margin $100$ があっても、positive witness は一個としてしか数えられない。

したがって、

> positive depth の個数を半窓で抑える

だけでは carrier cardinality を抑えられない。

残る本当の問題は、

> **pressure の高さ、すなわち amplitude をどう有限資源へ輸送するか**

じゃ。

report の「global transport theorem」という診断は正しいが、これをさらに正確に言えば、

```text
sign witness transport
```

ではなく、

```text
pressure-amplitude unit transport
```

が必要である。

---

## 12. Saturated token に使える追加余白

positive nonsaturated block で terminal valuation $v\ge2$ の場合、さらに一単位の余白がある。

nonsaturated なので full claim ではなく、

$$
A\le L-1
$$

じゃ。

したがって、

$$
D=A-v\le L-v-1
$$

である。

一方 selected carrier の cardinality は、

$$
|\operatorname{Carrier}|=L-v
$$

なので、

$$
D+1\le|\operatorname{Carrier}|
$$

が得られる。

つまり、

> terminal valuation $v\ge2$ の positive nonsaturated block は、自分の drift を収容した後も carrier 一個分の余剰を持つ。

したがって saturated block の直後がこの型なら、前の saturated token を successor carrier の余剰一個へ charge できる。

未解決なのは主に、

- successor drift が $0$
- successor が positive だが terminal valuation $1$

という場合じゃ。

saturated token 問題も、全く無構造ではなく、ここまで分岐を狭められる。

---

## 13. Lean Comparator Challenge との距離

cp-320 は Challenge 命題へ直接到達したわけではない。

しかし、大域 Big への第一関門である、

```text
positive drift が何によって支えられているか
```

を、有限 carrier として固定した。

現在の道筋は、

```text
positive drift units
→ selected pressure incidences + saturated tokens
→ pressure amplitude / boundary resource
→ queue uniform bound
→ bit-width bound
→ cycle rigidity
→ accelerated convergence
→ standard collatzStep convergence
→ Lean Comparator Challenge
```

じゃ。

今回、最初の矢印は本当に閉じた。

---

## 判定まとめ

### Full claims → saturation

**完成。**

### Positive-depth refinement

**完成。depth zero は排除された。**

### Selected pressure carrier

**完成。実在 source Finset になった。**

### Block 間 source disjointness

**完成。**

### Global cardinality embedding

**完成。ただし block-preserving ではない。**

### Dynamic-to-fixed depth

**elementwise 完成。cardinality embedding が次の薄い橋。**

### Fixed-depth pressure transport

**未完成。exact-length blocker と amplitude への分解が次。**

### 真正な障害

**positive pressure amplitude unit の大域的輸送。**

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge Float-window branch after
report-petal-320.

The cp-320 implementation is accepted.

Positive drift is now represented by actual positive-depth source incidences
plus isolated saturated tokens. Source-time overlap is closed.

Before attempting the upper-zero boundary directly, complete the exact
fixed-depth transport surface and isolate the pressure-amplitude obstruction.

# Stage A — block-preserving incidence embedding

The current global embedding is obtained only from total cardinality and need
not preserve the source block.

For every positive block k, construct a local embedding from

    Fin (Int.toNat (endpointAccountingTerm n k))

into:

    selected carrier of k

or, in the saturated case:

    the singleton saturated token of k.

Take the dependent sum of these local embeddings.

Prove that the resulting global embedding preserves block index.

Document the existing cardinality-only embedding as a compatibility theorem.

# Stage B — active selected-depth support

Define:

    canonicalActiveSelectedPressureBlocksAtDepth
    canonicalActiveSelectedPressureDepthSupport

using positive nonsaturated blocks, or equivalently nonempty selected carriers.

Prove that every depth in the active support has a nonempty bucket carrier.

Keep the existing support for the exact Fubini identity if useful, but do not
interpret a zero saturated bucket as a pressure witness.

# Stage C — forget-block embedding into the fixed-depth prefix fiber

For q <= m and every depth d, construct an embedding:

    CanonicalSelectedPressureBucketCarrier n q m d
      ↪
    {i // i ∈ orbitDepthContinuationRangeFiber
      n (paymentEndpointSeq n m + 1) (d + 1)}

The map forgets the block coordinate and retains the source time.

Use unique canonical-block membership to prove injectivity.

Derive:

    bucketCarrier.card
      <= orbitDepthContinuationFiberCount
        n (paymentEndpointSeq n m + 1) (d + 1).

# Stage D — exact fixed-depth pressure normal form

For every d >= 1 prove the block identity:

    blockPressureContributionInt n k d
      =
    card (canonicalPaymentBlockContinuationFiber n k (d + 1))
      - indicator (canonicalBlockLength n k = d)

in Int.

Define the exact-length block set:

    canonicalExactLengthBlockIndicesAtDepth n q m d.

Sum the identity over a finite block interval.

For the prefix 0..m, recover:

    SourcePressureMarginInt n (paymentEndpointSeq n m + 1) d
      =
    orbitDepthContinuationFiberCount
        n (paymentEndpointSeq n m + 1) (d + 1)
      - exactLengthBlockCount d.

# Stage E — bucket decomposition

Prove:

    bucketCarrier.card
      <= exactLengthBlockCount d
        + Int.toNat (windowPressureMarginAtDepth d).

Construct the corresponding finite cardinality embedding into:

    exact-length block tokens at d
      ⊕
    positive pressure-amplitude units at d.

Do not call this a boundary allocation.

# Stage F — exact-length tokens across depths

Package:

    Sigma d, exact-length block tokens at d.

Map it injectively to the finite block interval by forgetting d.

Use uniqueness of block length.

Derive that the total exact-length charge over all active selected depths is at
most the number of canonical blocks in the interval.

# Stage G — pressure amplitude carrier

Define:

    CanonicalPositivePressureAmplitudeCarrier n q m :=
      Sigma d in active depth support,
        Fin (Int.toNat (windowPressureMarginAtDepth n q m d)).

Prove the finite reduction:

    global selected carrier card
      <= number of blocks
        + pressure amplitude carrier card.

Combine it with the saturated-token packing theorem.

This theorem should isolate the only remaining nontrivial mass.

# Stage H — sign versus amplitude boundary

Connect:

    amplitude at depth d is positive
      <->
    IsSourcePressureDepth at d

for endpoint prefixes.

Record explicitly that existing finite-window packing controls the number and
placement of positive depths, not the amplitude units at one depth.

Do not infer an amplitude bound from a positive-witness count.

# Stage I — superlevel or transport audit

Investigate two exact routes.

Route 1: pressure superlevels.

    SourcePressureSuperlevel n K h d :=
      h < Int.toNat (SourcePressureMarginInt n K d).

Seek a layer-cake identity:

    sum_d positivePressureAmplitude(d)
      =
    sum_h card {d | SourcePressureSuperlevel h d}.

Determine whether the existing frontier / pulse / packing proofs generalize
from level zero to every level h.

Route 2: incidence transport.

Seek an injection from each pressure-amplitude unit into:

    a distinct upper-zero boundary unit,
    a pressure separator,
    or a NoLift obstruction.

Stop if either route exposes the first genuine missing invariant.

# Stage J — saturated successor slack

For a positive nonsaturated block with terminal valuation v >= 2, prove:

    endpointAccountingTerm n k + 1
      <= card (canonicalSelectedPressureCarrier n k).

Use full-claim rigidity:

    nonsaturated -> claimCount <= length - 1.

Hence a saturated token immediately followed by such a block can be charged to
the successor carrier after reserving enough units for the successor drift.

Classify the remaining successor cases:

    successor drift < 0
    successor drift = 0
    successor positive with terminal valuation = 1.

Do not count zero drift as repayment.

# Stage K — stopping rule

Stop at the first genuine obstruction among:

    block-preserving local embeddings cannot be assembled;
    bucket carriers do not embed into the fixed-depth prefix fiber;
    the exact pressure normal form fails;
    pressure amplitude superlevels do not inherit the pulse API;
    amplitude units cannot be transported with bounded multiplicity;
    saturated zero-drift successors cannot be structurally charged.

Do not return to depth-zero pressure or scalar queue algebra.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-321.md
```

cp-320 で、正 drift はついに「数」ではなく「数えられる物体」になった。

次はその物体を、**exact-length blocker と pressure amplitude** に分ける。
そこまで行けば、最後に残る敵の姿は、本当に「pressure の高さ」一つになるぞい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
index a23b64b0..fa924e21 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
@@ -23,6 +23,7 @@ import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlockNormalForm
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPositiveBlock
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPrimitiveExcursion
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentSaturatedSuccessor
+import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentSelectedCarrier
 import DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition
 
 #print "file: DkMath.Collatz.PetalBridge.FloatWindow"
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentSelectedCarrier.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentSelectedCarrier.lean
new file mode 100644
index 00000000..94ee2f0b
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentSelectedCarrier.lean
@@ -0,0 +1,653 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentSaturatedSuccessor
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentSelectedCarrier"
+
+namespace DkMath.Collatz
+
+/-!
+# Positive-depth pressure carriers
+
+This module removes the coarse depth-zero branch from the cp-319 dynamic
+pressure surface.  It keeps source incidences inside their canonical blocks;
+global resource transport is deliberately a later layer.
+-/
+
+/-! ## Full claims force saturation -/
+
+/-- Strengthened dyadic comparison used when every source claims carry two. -/
+theorem three_pow_add_two_pow_pred_le_two_pow_two_mul_sub_one
+    {L : ℕ} (hL : 3 ≤ L) :
+    3 ^ L + 2 ^ (L - 1) ≤ 2 ^ (2 * L - 1) := by
+  induction L, hL using Nat.le_induction with
+  | base => norm_num
+  | succ L hL ih =>
+      have hexp : 2 * (L + 1) - 1 = (2 * L - 1) + 2 := by omega
+      have htwo : 2 ^ L = 2 * 2 ^ (L - 1) := by
+        have heq : L = (L - 1) + 1 := by omega
+        calc
+          2 ^ L = 2 ^ ((L - 1) + 1) := congrArg (fun e => 2 ^ e) heq
+          _ = 2 ^ (L - 1) * 2 := by rw [pow_succ]
+          _ = 2 * 2 ^ (L - 1) := by omega
+      have hright : 0 < 2 ^ (2 * L - 1) := pow_pos (by norm_num) _
+      calc
+        3 ^ (L + 1) + 2 ^ (L + 1 - 1) =
+            3 * 3 ^ L + 2 * 2 ^ (L - 1) := by
+              rw [pow_succ]
+              have hpred : L + 1 - 1 = L := by omega
+              rw [hpred, htwo]
+              ring
+        _ ≤ 3 * (3 ^ L + 2 ^ (L - 1)) := by omega
+        _ ≤ 3 * 2 ^ (2 * L - 1) :=
+          Nat.mul_le_mul_left 3 ih
+        _ ≤ 4 * 2 ^ (2 * L - 1) := by omega
+        _ = 2 ^ (2 * (L + 1) - 1) := by
+          rw [hexp, pow_add]
+          norm_num
+          ring
+
+/-- Positive drift together with complete claims is rigid saturation. -/
+theorem canonicalSaturatedBorderBlock_of_pos_of_claimCount_eq_length
+    {n : OddNat} {k : ℕ}
+    (hpos : 0 < endpointAccountingTerm n k)
+    (hclaims : canonicalBlockClaimCount n k = canonicalBlockLength n k) :
+    CanonicalSaturatedBorderBlock n k := by
+  let L := canonicalBlockLength n k
+  let v := canonicalBlockTerminalValuation n k
+  let u := canonicalBlockOddCore n k
+  let x := canonicalBlockStartState n k
+  let x' := canonicalBlockNextStartState n k
+  have hvpos : 1 ≤ v := one_le_canonicalBlockTerminalValuation n k
+  have hvlt : v < L :=
+    canonicalBlockTerminalValuation_lt_length_of_endpointAccountingTerm_pos hpos
+  have hdrift := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount n k
+  rw [canonicalBlockCapacityCount_eq_terminalValuation, hclaims] at hdrift
+  have hwidthRaw := universalPaymentBlockSignedDriftAt_eq_bitWidth_sub n
+    (paymentEndpointSeq n k)
+    (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)
+  rw [← endpointAccountingTerm_eq_universalPaymentBlockSignedDriftAt] at hwidthRaw
+  have hwidth : bitWidth x' = bitWidth x + (L - v) := by
+    unfold x' x canonicalBlockNextStartState canonicalBlockStartState
+    rw [canonicalBlockStartTime_eq_universalPaymentBlockStart]
+    omega
+  have hLtwo : 2 ≤ L := by omega
+  by_cases hL : L = 2
+  · apply (canonicalSaturatedBorderBlock_iff_length_and_claims n k).2
+    constructor
+    · change L = v + 1
+      omega
+    · exact hclaims
+  · have hLthree : 3 ≤ L := by omega
+    have hu : 0 < u := canonicalBlockOddCore_pos n k
+    have hxpos : 0 < x := by
+      unfold x canonicalBlockStartState
+      have hodd := (iterateT (canonicalBlockStartTime n k) n).2
+      omega
+    have hx'pos : 0 < x' := by
+      unfold x' canonicalBlockNextStartState
+      have hodd := (iterateT (paymentEndpointSeq n k + 1) n).2
+      omega
+    have hnormal : x + 1 = 2 ^ L * u := by
+      exact canonicalBlockStartState_add_one_eq_pow_mul_oddCore n k
+    have hterminal : canonicalBlockTerminalCarrier n k = 3 ^ L * u - 1 := by
+      rfl
+    have hscale : 0 < 2 ^ (L - v) := pow_pos (by norm_num) _
+    have hupperScaled :
+        3 ^ L * u + 2 ^ (L - 1) ≤ 2 ^ (2 * L - 1) * u := by
+      have hbase := three_pow_add_two_pow_pred_le_two_pow_two_mul_sub_one hLthree
+      have hmul := Nat.mul_le_mul_right u hbase
+      have hone : 1 ≤ u := hu
+      nlinarith [Nat.mul_le_mul_left (2 ^ (L - 1)) hone]
+    have hpowSplit :
+        2 ^ (2 * L - 1) = 2 ^ (L - 1) * 2 ^ L := by
+      have hexp : 2 * L - 1 = (L - 1) + L := by omega
+      rw [hexp, pow_add]
+    rw [hpowSplit] at hupperScaled
+    have hterminalLt :
+        canonicalBlockTerminalCarrier n k < 2 ^ (L - 1) * x := by
+      rw [hterminal]
+      have hprodpos : 0 < 3 ^ L * u :=
+        Nat.mul_pos (pow_pos (by norm_num) _) hu
+      have hsubeq : (3 ^ L * u - 1) + 1 = 3 ^ L * u := by omega
+      nlinarith
+    have hdivisor : 0 < 2 ^ v := pow_pos (by norm_num) _
+    have hnextFormula : x' = canonicalBlockTerminalCarrier n k / 2 ^ v :=
+      canonicalBlockNextStartState_eq_terminalCarrier_div_pow_valuation n k
+    have hupper : x' < 2 ^ (L - v - 1) * x := by
+      rw [hnextFormula]
+      apply (Nat.div_lt_iff_lt_mul hdivisor).2
+      have hexp : L - 1 = (L - v - 1) + v := by omega
+      rw [hexp, pow_add] at hterminalLt
+      nlinarith
+    have hlowerPow := pow_bitWidth_sub_one_le hx'pos
+    have hxlt := lt_pow_bitWidth hxpos
+    have hlower : 2 ^ (L - v - 1) * x < x' := by
+      have hD : 1 ≤ L - v := by omega
+      calc
+        2 ^ (L - v - 1) * x <
+            2 ^ (L - v - 1) * 2 ^ bitWidth x :=
+          (Nat.mul_lt_mul_left (pow_pos (by norm_num) _)).2 hxlt
+        _ = 2 ^ (bitWidth x' - 1) := by
+          rw [← pow_add]
+          congr 1
+          omega
+        _ ≤ x' := hlowerPow
+    omega
+
+/-- Saturation is exactly positive drift with all canonical sources claiming. -/
+theorem canonicalSaturatedBorderBlock_iff_pos_and_claimCount_eq_length
+    (n : OddNat) (k : ℕ) :
+    CanonicalSaturatedBorderBlock n k ↔
+      0 < endpointAccountingTerm n k ∧
+        canonicalBlockClaimCount n k = canonicalBlockLength n k := by
+  constructor
+  · intro h
+    exact ⟨h.drift_pos, h.2.1⟩
+  · rintro ⟨hpos, hclaims⟩
+    exact canonicalSaturatedBorderBlock_of_pos_of_claimCount_eq_length hpos hclaims
+
+/-! ## Positive selected depth -/
+
+/-- Refined pressure depth; unlike the compatibility surface from cp-319 this
+is always positive and never falls back to depth zero. -/
+noncomputable def canonicalSelectedPositivePressureDepth
+    (n : OddNat) (k : ℕ) : ℕ :=
+  if canonicalBlockTerminalValuation n k = 1 then 1
+  else canonicalBlockTerminalValuation n k - 1
+
+/-- The refined selected pressure depth is positive. -/
+theorem one_le_canonicalSelectedPositivePressureDepth
+    (n : OddNat) (k : ℕ) :
+    1 ≤ canonicalSelectedPositivePressureDepth n k := by
+  unfold canonicalSelectedPositivePressureDepth
+  split
+  · omega
+  · have hv := one_le_canonicalBlockTerminalValuation n k
+    omega
+
+/-- Positive nonsaturated drift is dominated at the selected positive depth. -/
+theorem endpointAccountingTerm_le_selectedPositivePressure_of_not_saturated
+    {n : OddNat} {k : ℕ}
+    (hpos : 0 < endpointAccountingTerm n k)
+    (hnot : ¬ CanonicalSaturatedBorderBlock n k) :
+    endpointAccountingTerm n k ≤
+      blockPressureContributionInt n k
+        (canonicalSelectedPositivePressureDepth n k) := by
+  let v := canonicalBlockTerminalValuation n k
+  let L := canonicalBlockLength n k
+  by_cases hv : v = 1
+  · have hclaimLe := canonicalBlockClaimCount_le_length n k
+    have hclaimNe : canonicalBlockClaimCount n k ≠ L := by
+      intro heq
+      exact hnot (canonicalSaturatedBorderBlock_of_pos_of_claimCount_eq_length
+        hpos heq)
+    have hclaimLt : canonicalBlockClaimCount n k < L := by omega
+    have hvlt :=
+      canonicalBlockTerminalValuation_lt_length_of_endpointAccountingTerm_pos hpos
+    have hLthree : 3 ≤ L := by
+      by_contra hL
+      have hLtwo : L = 2 := by omega
+      have hdrift := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount n k
+      rw [canonicalBlockCapacityCount_eq_terminalValuation] at hdrift
+      omega
+    have hpressure :=
+      blockPressureContributionInt_eq_sub_sub_one_of_add_two_le_length
+        (n := n) (k := k) (d := 1) (by omega) (by
+          change 3 ≤ L
+          exact hLthree)
+    have hdrift := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount n k
+    rw [canonicalBlockCapacityCount_eq_terminalValuation] at hdrift
+    rw [canonicalSelectedPositivePressureDepth, if_pos hv]
+    rw [hpressure]
+    change endpointAccountingTerm n k ≤ ((L - 1 : ℕ) : ℤ) - 1
+    omega
+  · have hvpos := one_le_canonicalBlockTerminalValuation n k
+    have hv2 : 2 ≤ v := by omega
+    rw [canonicalSelectedPositivePressureDepth, if_neg hv]
+    exact endpointAccountingTerm_le_blockPressure_pred_terminal hpos hv2
+
+/-- Saturation consumes exactly one unit beyond its selected depth-one pressure. -/
+theorem CanonicalSaturatedBorderBlock.drift_eq_selectedPositivePressure_add_one
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
+    endpointAccountingTerm n k =
+      blockPressureContributionInt n k
+        (canonicalSelectedPositivePressureDepth n k) + 1 := by
+  have hp := h.pressure_eq_zero
+  rw [h.terminalValuation_eq_one] at hp
+  rw [h.2.2, canonicalSelectedPositivePressureDepth,
+    if_pos h.terminalValuation_eq_one, hp]
+  norm_num
+
+/-- Refined pointwise accounting using only positive pressure depths. -/
+theorem endpointAccountingTerm_le_selectedPositivePressure_add_saturatedUnit
+    {n : OddNat} {k : ℕ} (hpos : 0 < endpointAccountingTerm n k) :
+    endpointAccountingTerm n k ≤
+      blockPressureContributionInt n k
+          (canonicalSelectedPositivePressureDepth n k) +
+        canonicalSaturatedUnit n k := by
+  classical
+  by_cases hs : CanonicalSaturatedBorderBlock n k
+  · rw [hs.drift_eq_selectedPositivePressure_add_one]
+    simp [canonicalSaturatedUnit, hs]
+  · have hle :=
+      endpointAccountingTerm_le_selectedPositivePressure_of_not_saturated hpos hs
+    simpa [canonicalSaturatedUnit, hs] using hle
+
+/-! ## Pressure as an actual source carrier -/
+
+/-- At a positive interior depth, pressure is exactly the cardinality of the
+continuation fiber one level deeper. -/
+theorem blockPressureContributionInt_eq_card_continuationFiber_succ
+    {n : OddNat} {k d : ℕ} (hd : 1 ≤ d)
+    (hdL : d < canonicalPaymentBlockLength n k) :
+    blockPressureContributionInt n k d =
+      ((canonicalPaymentBlockContinuationFiber n k (d + 1)).card : ℤ) := by
+  rw [blockPressureContributionInt_eq,
+    canonicalPaymentBlockContinuationFiber_card]
+  simp [hd, hdL.le]
+  omega
+
+/-- Source incidences carrying the selected positive pressure contribution. -/
+noncomputable def canonicalSelectedPressureCarrier
+    (n : OddNat) (k : ℕ) : Finset ℕ :=
+  canonicalPaymentBlockContinuationFiber n k
+    (canonicalSelectedPositivePressureDepth n k + 1)
+
+/-- A positive nonsaturated selected depth lies strictly inside its block. -/
+theorem selectedPositivePressureDepth_lt_length_of_pos_of_not_saturated
+    {n : OddNat} {k : ℕ}
+    (hpos : 0 < endpointAccountingTerm n k)
+    (hnot : ¬ CanonicalSaturatedBorderBlock n k) :
+    canonicalSelectedPositivePressureDepth n k <
+      canonicalPaymentBlockLength n k := by
+  let v := canonicalBlockTerminalValuation n k
+  let L := canonicalBlockLength n k
+  have hLen : canonicalPaymentBlockLength n k = L := rfl
+  have hvlt :=
+    canonicalBlockTerminalValuation_lt_length_of_endpointAccountingTerm_pos hpos
+  by_cases hv : v = 1
+  · rw [canonicalSelectedPositivePressureDepth, if_pos hv]
+    by_contra hL
+    rw [hLen] at hL
+    have hLtwo : L = 2 := by omega
+    have hclaimLe := canonicalBlockClaimCount_le_length n k
+    have hdrift := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount n k
+    rw [canonicalBlockCapacityCount_eq_terminalValuation] at hdrift
+    have hclaims : canonicalBlockClaimCount n k = L := by omega
+    exact hnot (canonicalSaturatedBorderBlock_of_pos_of_claimCount_eq_length
+      hpos hclaims)
+  · rw [canonicalSelectedPositivePressureDepth, if_neg hv]
+    rw [hLen]
+    omega
+
+/-- For positive nonsaturated blocks, selected pressure is the exact cardinality
+of the selected continuation carrier. -/
+theorem selectedPressure_eq_card_carrier_of_pos_of_not_saturated
+    {n : OddNat} {k : ℕ}
+    (hpos : 0 < endpointAccountingTerm n k)
+    (hnot : ¬ CanonicalSaturatedBorderBlock n k) :
+    blockPressureContributionInt n k
+        (canonicalSelectedPositivePressureDepth n k) =
+      ((canonicalSelectedPressureCarrier n k).card : ℤ) := by
+  apply blockPressureContributionInt_eq_card_continuationFiber_succ
+  · exact one_le_canonicalSelectedPositivePressureDepth n k
+  · exact selectedPositivePressureDepth_lt_length_of_pos_of_not_saturated hpos hnot
+
+/-- Positive nonsaturated drift injects numerically into its selected carrier. -/
+theorem endpointAccountingTerm_le_card_selectedPressureCarrier
+    {n : OddNat} {k : ℕ}
+    (hpos : 0 < endpointAccountingTerm n k)
+    (hnot : ¬ CanonicalSaturatedBorderBlock n k) :
+    endpointAccountingTerm n k ≤
+      ((canonicalSelectedPressureCarrier n k).card : ℤ) := by
+  rw [← selectedPressure_eq_card_carrier_of_pos_of_not_saturated hpos hnot]
+  exact endpointAccountingTerm_le_selectedPositivePressure_of_not_saturated hpos hnot
+
+/-- Saturation has no selected continuation incidence; its entire residual is
+the explicit unit token. -/
+theorem CanonicalSaturatedBorderBlock.selectedPressureCarrier_eq_empty
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
+    canonicalSelectedPressureCarrier n k = ∅ := by
+  apply Finset.card_eq_zero.mp
+  unfold canonicalSelectedPressureCarrier
+  rw [canonicalPaymentBlockContinuationFiber_card,
+    canonicalSelectedPositivePressureDepth, if_pos h.terminalValuation_eq_one]
+  change canonicalBlockLength n k - 2 = 0
+  rw [h.length_eq_two]
+
+theorem CanonicalSaturatedBorderBlock.saturatedUnit_eq_one
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
+    canonicalSaturatedUnit n k = 1 := by
+  classical
+  simp [canonicalSaturatedUnit, h]
+
+/-! ## Disjoint global selected carrier -/
+
+/-- Distinct canonical blocks contain disjoint orbit-time incidences. -/
+theorem canonicalPaymentBlock_disjoint_of_ne
+    {n : OddNat} {k l : ℕ} (hkl : k ≠ l) :
+    Disjoint (canonicalPaymentBlock n k) (canonicalPaymentBlock n l) := by
+  rw [Finset.disjoint_left]
+  intro i hik hil
+  rcases existsUnique_mem_canonicalPaymentBlock n i with ⟨j, _hij, huniq⟩
+  exact hkl ((huniq k hik).trans (huniq l hil).symm)
+
+/-- Every selected pressure incidence remains inside its own canonical block. -/
+theorem canonicalSelectedPressureCarrier_subset_block
+    (n : OddNat) (k : ℕ) :
+    canonicalSelectedPressureCarrier n k ⊆ canonicalPaymentBlock n k := by
+  intro i hi
+  exact (mem_canonicalPaymentBlockContinuationFiber_iff.mp hi).1
+
+/-- Selected pressure carriers from distinct canonical blocks are disjoint. -/
+theorem canonicalSelectedPressureCarrier_disjoint_of_ne
+    {n : OddNat} {k l : ℕ} (hkl : k ≠ l) :
+    Disjoint (canonicalSelectedPressureCarrier n k)
+      (canonicalSelectedPressureCarrier n l) := by
+  rw [Finset.disjoint_left]
+  intro i hik hil
+  have hblocks := canonicalPaymentBlock_disjoint_of_ne (n := n) hkl
+  rw [Finset.disjoint_left] at hblocks
+  exact hblocks (canonicalSelectedPressureCarrier_subset_block n k hik)
+    (canonicalSelectedPressureCarrier_subset_block n l hil)
+
+/-- Positive nonsaturated block indices in the closed interval `q..m`. -/
+noncomputable def canonicalNonsaturatedPositiveBlockIndices
+    (n : OddNat) (q m : ℕ) : Finset ℕ := by
+  classical
+  exact (canonicalPositiveDriftBlockIndices n q m).filter fun k =>
+    ¬ CanonicalSaturatedBorderBlock n k
+
+@[simp] theorem mem_canonicalNonsaturatedPositiveBlockIndices
+    {n : OddNat} {q m k : ℕ} :
+    k ∈ canonicalNonsaturatedPositiveBlockIndices n q m ↔
+      k ∈ Finset.Icc q m ∧ 0 < endpointAccountingTerm n k ∧
+        ¬ CanonicalSaturatedBorderBlock n k := by
+  rw [canonicalNonsaturatedPositiveBlockIndices]
+  simp only [Finset.mem_filter, canonicalPositiveDriftBlockIndices,
+    Finset.mem_Icc]
+  tauto
+
+/-- The finite global selected-pressure incidence carrier.  The block index is
+retained in the sigma coordinate, so this is an incidence certificate rather
+than an allocation of future payment slots. -/
+def CanonicalGlobalSelectedPressureCarrier
+    (n : OddNat) (q m : ℕ) :=
+  Σ k : {k : ℕ // k ∈ canonicalPositiveDriftBlockIndices n q m},
+    {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val}
+
+/-- Exact cardinality of the finite global selected-pressure carrier. -/
+theorem natCard_CanonicalGlobalSelectedPressureCarrier
+    (n : OddNat) (q m : ℕ) :
+    Nat.card (CanonicalGlobalSelectedPressureCarrier n q m) =
+      ∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
+        (canonicalSelectedPressureCarrier n k).card := by
+  unfold CanonicalGlobalSelectedPressureCarrier
+  rw [Nat.card_sigma]
+  simp_rw [Nat.card_eq_fintype_card, Fintype.card_coe]
+  rw [Finset.univ_eq_attach]
+  exact Finset.sum_attach (canonicalPositiveDriftBlockIndices n q m)
+    fun k => (canonicalSelectedPressureCarrier n k).card
+
+/-! ## Finite positive-drift incidence embedding -/
+
+/-- Anonymous units of positive signed drift, indexed by their canonical
+block.  They carry no claim about which future event pays them. -/
+def CanonicalPositiveDriftUnitCarrier
+    (n : OddNat) (q m : ℕ) :=
+  Σ k : {k : ℕ // k ∈ canonicalPositiveDriftBlockIndices n q m},
+    Fin (Int.toNat (endpointAccountingTerm n k.val))
+
+/-- Exact cardinality of the finite positive-drift unit carrier. -/
+theorem natCard_CanonicalPositiveDriftUnitCarrier
+    (n : OddNat) (q m : ℕ) :
+    Nat.card (CanonicalPositiveDriftUnitCarrier n q m) =
+      ∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
+        Int.toNat (endpointAccountingTerm n k) := by
+  unfold CanonicalPositiveDriftUnitCarrier
+  rw [Nat.card_sigma]
+  simp_rw [Nat.card_eq_fintype_card, Fintype.card_fin]
+  rw [Finset.univ_eq_attach]
+  exact Finset.sum_attach (canonicalPositiveDriftBlockIndices n q m)
+    fun k => Int.toNat (endpointAccountingTerm n k)
+
+/-- The natural-number token carried by a saturated block. -/
+noncomputable def canonicalSaturatedTokenNat
+    (n : OddNat) (k : ℕ) : ℕ :=
+  Int.toNat (canonicalSaturatedUnit n k)
+
+/-- Pointwise cardinality budget for one positive block. -/
+theorem intToNat_endpointAccountingTerm_le_selectedCarrier_add_saturated
+    {n : OddNat} {k : ℕ} (hpos : 0 < endpointAccountingTerm n k) :
+    Int.toNat (endpointAccountingTerm n k) ≤
+      (canonicalSelectedPressureCarrier n k).card +
+        canonicalSaturatedTokenNat n k := by
+  classical
+  by_cases hs : CanonicalSaturatedBorderBlock n k
+  · rw [canonicalSaturatedTokenNat, hs.saturatedUnit_eq_one,
+      hs.netDrift_eq_one]
+    norm_num
+  · rw [canonicalSaturatedTokenNat]
+    simp only [canonicalSaturatedUnit, hs, ↓reduceIte, Int.toNat_zero, add_zero]
+    have hle := endpointAccountingTerm_le_card_selectedPressureCarrier hpos hs
+    have hnat := Int.toNat_le_toNat hle
+    simpa using hnat
+
+/-- The sum of local cardinality budgets is exactly the global incidence
+carrier plus the isolated saturated-token carrier. -/
+theorem sum_selectedCarrier_add_saturated_eq_global
+    (n : OddNat) (q m : ℕ) :
+    (∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
+        ((canonicalSelectedPressureCarrier n k).card +
+          canonicalSaturatedTokenNat n k)) =
+      Nat.card (CanonicalGlobalSelectedPressureCarrier n q m) +
+        (canonicalSaturatedBlockIndices n q m).card := by
+  classical
+  rw [Finset.sum_add_distrib,
+    natCard_CanonicalGlobalSelectedPressureCarrier]
+  congr 1
+  simp only [canonicalSaturatedTokenNat, canonicalSaturatedUnit]
+  have htoken (k : ℕ) :
+      (if CanonicalSaturatedBorderBlock n k then (1 : ℤ) else 0).toNat =
+        if CanonicalSaturatedBorderBlock n k then 1 else 0 := by
+    by_cases hs : CanonicalSaturatedBorderBlock n k <;> simp [hs]
+  simp_rw [htoken]
+  rw [Finset.sum_boole]
+  have hsets :
+      (canonicalPositiveDriftBlockIndices n q m).filter
+          (CanonicalSaturatedBorderBlock n) =
+        canonicalSaturatedBlockIndices n q m := by
+    ext k
+    simp only [canonicalPositiveDriftBlockIndices,
+      canonicalSaturatedBlockIndices, Finset.mem_filter]
+    constructor
+    · rintro ⟨⟨hk, _⟩, hs⟩
+      exact ⟨hk, hs⟩
+    · rintro ⟨hk, hs⟩
+      exact ⟨⟨hk, hs.drift_pos⟩, hs⟩
+  rw [hsets]
+  exact_mod_cast rfl
+
+/-- Finite cardinality form of the positive-drift incidence certificate. -/
+theorem natCard_positiveDriftUnitCarrier_le_global_add_saturated
+    (n : OddNat) (q m : ℕ) :
+    Nat.card (CanonicalPositiveDriftUnitCarrier n q m) ≤
+      Nat.card (CanonicalGlobalSelectedPressureCarrier n q m) +
+        Nat.card {k : ℕ // k ∈ canonicalSaturatedBlockIndices n q m} := by
+  have hsatCard :
+      Nat.card {k : ℕ // k ∈ canonicalSaturatedBlockIndices n q m} =
+        (canonicalSaturatedBlockIndices n q m).card := by
+    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
+  rw [natCard_CanonicalPositiveDriftUnitCarrier, hsatCard,
+    ← sum_selectedCarrier_add_saturated_eq_global]
+  exact Finset.sum_le_sum fun k hk =>
+    intToNat_endpointAccountingTerm_le_selectedCarrier_add_saturated
+      ((Finset.mem_filter.mp hk).2)
+
+/-- Existence of a finite injection from positive-drift units into disjoint
+selected incidences plus saturated tokens.  This is only an incidence
+certificate; it is intentionally not presented as a future payment map. -/
+theorem exists_positiveDriftUnitEmbedding_global_add_saturated
+    (n : OddNat) (q m : ℕ) :
+    Nonempty (CanonicalPositiveDriftUnitCarrier n q m ↪
+      (CanonicalGlobalSelectedPressureCarrier n q m ⊕
+        {k : ℕ // k ∈ canonicalSaturatedBlockIndices n q m})) := by
+  classical
+  letI : Fintype {k : ℕ // k ∈ canonicalPositiveDriftBlockIndices n q m} :=
+    Fintype.ofFinset (canonicalPositiveDriftBlockIndices n q m) (by simp)
+  letI : Fintype (CanonicalPositiveDriftUnitCarrier n q m) := by
+    unfold CanonicalPositiveDriftUnitCarrier
+    infer_instance
+  letI : Fintype {k : ℕ // k ∈ canonicalSaturatedBlockIndices n q m} :=
+    Fintype.ofFinset (canonicalSaturatedBlockIndices n q m) (by simp)
+  letI (k : {k : ℕ // k ∈ canonicalPositiveDriftBlockIndices n q m}) :
+      Fintype {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} :=
+    Fintype.ofFinset (canonicalSelectedPressureCarrier n k.val) (by simp)
+  letI : Fintype (CanonicalGlobalSelectedPressureCarrier n q m) := by
+    unfold CanonicalGlobalSelectedPressureCarrier
+    infer_instance
+  apply Function.Embedding.nonempty_iff_card_le.mpr
+  simpa only [← Nat.card_eq_fintype_card, Nat.card_sum] using
+    natCard_positiveDriftUnitCarrier_le_global_add_saturated n q m
+
+/-! ## Open-excursion carrier bounds -/
+
+/-- Positive drift, reflected into naturals, is bounded by the finite incidence
+certificate and isolated saturation tokens on any closed block interval. -/
+theorem sum_intToNat_positiveDrift_le_globalCarrier_add_saturatedCard
+    (n : OddNat) (q m : ℕ) :
+    (∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
+        Int.toNat (endpointAccountingTerm n k)) ≤
+      Nat.card (CanonicalGlobalSelectedPressureCarrier n q m) +
+        (canonicalSaturatedBlockIndices n q m).card := by
+  rw [← natCard_CanonicalPositiveDriftUnitCarrier]
+  have h := natCard_positiveDriftUnitCarrier_le_global_add_saturated n q m
+  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using h
+
+/-- Isolated saturated tokens occupy at most half of the enlarged interval. -/
+theorem card_canonicalSaturatedBlockIndices_le_half
+    (n : OddNat) (q m : ℕ) :
+    (canonicalSaturatedBlockIndices n q m).card ≤ (m - q + 2) / 2 := by
+  apply (Nat.le_div_iff_mul_le Nat.two_pos).2
+  simpa [Nat.mul_comm] using
+    two_mul_card_canonicalSaturatedBlockIndices_le n q m
+
+/-- Carrier bound with the isolated-token term replaced by its packing bound.
+It is finite-window accounting, not a uniform bound in `m`. -/
+theorem sum_intToNat_positiveDrift_le_globalCarrier_add_half
+    (n : OddNat) (q m : ℕ) :
+    (∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
+        Int.toNat (endpointAccountingTerm n k)) ≤
+      Nat.card (CanonicalGlobalSelectedPressureCarrier n q m) +
+        (m - q + 2) / 2 := by
+  exact (sum_intToNat_positiveDrift_le_globalCarrier_add_saturatedCard n q m).trans
+    (Nat.add_le_add_left (card_canonicalSaturatedBlockIndices_le_half n q m) _)
+
+/-- Open-excursion-facing form of the finite carrier bound.  The excursion
+hypothesis identifies the intended window; the inequality itself holds on every
+closed canonical block interval. -/
+theorem CanonicalOpenPositiveQueueExcursion.positiveDrift_le_globalCarrier_add_half
+    {n : OddNat} {q m : ℕ} (_h : CanonicalOpenPositiveQueueExcursion n q m) :
+    (∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
+        Int.toNat (endpointAccountingTerm n k)) ≤
+      Nat.card (CanonicalGlobalSelectedPressureCarrier n q m) +
+        (m - q + 2) / 2 :=
+  sum_intToNat_positiveDrift_le_globalCarrier_add_half n q m
+
+/-! ## Selected-depth buckets -/
+
+/-- Positive blocks whose refined selected pressure depth is exactly `d`. -/
+noncomputable def canonicalSelectedPressureBlocksAtDepth
+    (n : OddNat) (q m d : ℕ) : Finset ℕ := by
+  classical
+  exact (canonicalPositiveDriftBlockIndices n q m).filter fun k =>
+    canonicalSelectedPositivePressureDepth n k = d
+
+/-- The finite support of selected pressure depths in `q..m`. -/
+noncomputable def canonicalSelectedPressureDepthSupport
+    (n : OddNat) (q m : ℕ) : Finset ℕ :=
+  (canonicalPositiveDriftBlockIndices n q m).image fun k =>
+    canonicalSelectedPositivePressureDepth n k
+
+@[simp] theorem mem_canonicalSelectedPressureBlocksAtDepth
+    {n : OddNat} {q m d k : ℕ} :
+    k ∈ canonicalSelectedPressureBlocksAtDepth n q m d ↔
+      k ∈ canonicalPositiveDriftBlockIndices n q m ∧
+        canonicalSelectedPositivePressureDepth n k = d := by
+  simp [canonicalSelectedPressureBlocksAtDepth]
+
+/-- Selected incidences at one fixed selected depth. -/
+def CanonicalSelectedPressureBucketCarrier
+    (n : OddNat) (q m d : ℕ) :=
+  Σ k : {k : ℕ // k ∈ canonicalSelectedPressureBlocksAtDepth n q m d},
+    {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val}
+
+/-- Exact cardinality of one selected-depth bucket. -/
+theorem natCard_CanonicalSelectedPressureBucketCarrier
+    (n : OddNat) (q m d : ℕ) :
+    Nat.card (CanonicalSelectedPressureBucketCarrier n q m d) =
+      ∑ k ∈ canonicalSelectedPressureBlocksAtDepth n q m d,
+        (canonicalSelectedPressureCarrier n k).card := by
+  unfold CanonicalSelectedPressureBucketCarrier
+  rw [Nat.card_sigma]
+  simp_rw [Nat.card_eq_fintype_card, Fintype.card_coe]
+  rw [Finset.univ_eq_attach]
+  exact Finset.sum_attach (canonicalSelectedPressureBlocksAtDepth n q m d)
+    fun k => (canonicalSelectedPressureCarrier n k).card
+
+/-- Finite Fubini decomposition of the global selected carrier by its dynamic
+selected depth. -/
+theorem natCard_globalSelectedPressureCarrier_eq_sum_depthBuckets
+    (n : OddNat) (q m : ℕ) :
+    Nat.card (CanonicalGlobalSelectedPressureCarrier n q m) =
+      ∑ d ∈ canonicalSelectedPressureDepthSupport n q m,
+        Nat.card (CanonicalSelectedPressureBucketCarrier n q m d) := by
+  rw [natCard_CanonicalGlobalSelectedPressureCarrier]
+  simp_rw [natCard_CanonicalSelectedPressureBucketCarrier]
+  symm
+  apply Finset.sum_fiberwise_of_maps_to
+  intro k hk
+  exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
+
+/-- A selected incidence in depth bucket `d` is an incidence of the existing
+fixed-depth continuation fiber at depth `d + 1`. -/
+theorem CanonicalSelectedPressureBucketCarrier.mem_fixedDepthContinuationFiber
+    {n : OddNat} {q m d : ℕ}
+    (x : CanonicalSelectedPressureBucketCarrier n q m d) :
+    x.2.val ∈ canonicalPaymentBlockContinuationFiber n x.1.val (d + 1) := by
+  rcases x with ⟨k, i⟩
+  have hkdepth := (mem_canonicalSelectedPressureBlocksAtDepth.mp k.property).2
+  change i.val ∈ canonicalPaymentBlockContinuationFiber n k.val (d + 1)
+  unfold canonicalSelectedPressureCarrier at i
+  simpa [hkdepth] using i.property
+
+/-!
+## Pressure infrastructure audit and the genuine remaining obstruction
+
+The dynamic-to-fixed-depth conversion is now exact: the global incidence
+carrier is a finite sum of bucket carriers, and every bucket incidence belongs
+to the already existing canonical continuation fiber at `d + 1`.  Therefore
+`orbitDepthContinuationFiberCount_paymentEndpointSeq_eq_sum` can count each
+fixed bucket after extending the block interval to an endpoint prefix.
+
+The existing `PressureFrontier`, `PressureAccounting`, `PressureBeam`, and
+finite-window packing APIs constrain fixed-depth continuation/recovery counts
+and separated pulse witnesses.  They do not currently provide a
+contribution-preserving injection from every continuation incidence into a
+finite boundary resource, nor a theorem saying that an unbounded bucket must
+produce a separator or a `NoLift` obstruction.  Crossing that gap would be a
+new global transport theorem, not a consequence of source disjointness.
+
+Saturated tokens remain separate for the same reason.  A nonpositive successor
+does not repay a token when its drift is zero.  The next sound branch must
+identify an injective charge to a later negative unit, a selected incidence, or
+an upper-zero boundary unit, with exact preservation of bit position.  No such
+charge is asserted here.
+-/
+
+end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-320.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-320.md
new file mode 100644
index 00000000..dc3d6cc3
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-320.md
@@ -0,0 +1,158 @@
+# Petal / Float Window Report - Checkpoint 320
+
+## Status
+
+`cp-320` replaces the coarse depth-zero pressure branch by a positive-depth
+carrier construction and closes Stages A-G without `sorry`.
+
+New module:
+
+```text
+DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentSelectedCarrier
+```
+
+It is exported by `DkMath.Collatz.PetalBridge.FloatWindow`.
+
+## Full claims and saturation
+
+Lean proves the strengthened exponential estimate
+
+```text
+3 <= L -> 3^L + 2^(L-1) <= 2^(2*L-1).
+```
+
+Combined with the exact block normal form and bit-width drift, it makes full
+claims rigid:
+
+```text
+positive drift + claimCount = length
+  <-> saturated border block.
+```
+
+For `L >= 3`, full claims would force the next start both below and above
+`2^(L-v-1) * start`.  Hence the block has `L = 2`, and the existing rigidity
+theorems give `v = 1` and saturation.
+
+## Positive selected depth
+
+The refined depth is
+
+```text
+v = 1 -> 1
+v != 1 -> v - 1.
+```
+
+It is always at least one.  A positive nonsaturated block satisfies
+
+```text
+drift <= pressure(selectedPositiveDepth).
+```
+
+The `v = 1` proof now uses full-claim rigidity: nonsaturation forces
+`claimCount < length`, so `claimCount - 1 <= length - 2`, exactly the depth-one
+pressure.  A saturated block instead has
+
+```text
+drift = selected pressure + 1,
+selected carrier = empty,
+saturated token = 1.
+```
+
+Thus the refined API no longer uses depth zero.
+
+## Actual incidence carriers
+
+For every positive interior depth, pressure is exactly the cardinality of the
+continuation fiber one level deeper.  This defines the selected carrier
+
+```text
+continuationFiber(block, selectedPositiveDepth + 1).
+```
+
+For positive nonsaturated blocks its cardinality dominates drift.
+
+The cp-319 obstruction report is corrected: selected carriers from different
+canonical blocks are disjoint.  Lean proves this from unique canonical-block
+membership, then proves each selected carrier is a subset of its block.
+
+The finite global sigma carrier retains both the block and source incidence.
+Its cardinality is exactly the sum of all local selected-carrier cardinalities.
+Source-incidence multiplicity is therefore closed.
+
+## Finite injection
+
+Positive drift units are represented anonymously by
+
+```text
+Sigma block, Fin (Int.toNat drift(block)).
+```
+
+Lean proves a finite embedding into
+
+```text
+global selected-pressure incidences
+  Sum
+saturated block tokens.
+```
+
+This is an incidence certificate.  It is not a future payment allocation and
+does not identify a later repayment event.
+
+## Finite-window bound
+
+On every closed block interval, and hence on an open positive excursion,
+
+```text
+sum positive drift
+  <= globalCarrier.card + saturatedIndices.card
+  <= globalCarrier.card + (m - q + 2) / 2.
+```
+
+The sums are stated in `Nat` after `Int.toNat`, valid because the selected
+blocks have positive drift.  The second inequality is the isolated-saturation
+packing theorem.  This is not a uniform bound as `m` varies.
+
+## Dynamic-to-fixed depth bridge
+
+The implementation defines:
+
+```text
+selectedPressureBlocksAtDepth d
+selectedPressureDepthSupport
+selectedPressureBucketCarrier d.
+```
+
+The support is finite, and Lean proves the exact Fubini identity
+
+```text
+globalCarrier.card
+  = sum d in depthSupport, bucketCarrier(d).card.
+```
+
+Every incidence in bucket `d` belongs to the existing canonical continuation
+fiber at fixed depth `d + 1`.  Therefore the dynamic carrier has now reached
+the existing endpoint-aligned fixed-depth counting API honestly.
+
+## Genuine stopping obstruction
+
+The remaining gap is not overlap and not depth zero.  Existing pressure APIs
+count fixed-depth continuation and recovery fibers and control separated local
+pulses, but they do not currently prove that every selected incidence:
+
+1. consumes a distinct finite boundary resource;
+2. creates a pressure separator when a bucket is large;
+3. creates a `NoLift` obstruction when a bucket is unbounded; or
+4. can be transported to an upper-zero boundary unit with bounded reuse.
+
+Saturated tokens also remain unresolved.  A nonpositive successor can have
+zero drift, so it does not necessarily repay the token.
+
+The next theorem must be contribution-preserving transport from a fixed-depth
+bucket to a bounded resource or explicit obstruction.  An upper-boundary
+injection additionally requires exact bit-position preservation.  Neither is
+asserted prematurely.
+
+## Verification
+
+The focused new-module build passes with no `sorry`.  Aggregate and top-level
+build gates are recorded in the completion result after this report is added.
````
`````
