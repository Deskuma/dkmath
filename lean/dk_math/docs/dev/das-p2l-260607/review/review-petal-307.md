# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock

gch: 040fba82537b8a28c8eab79ee1ba44fbdad9add9

## Report

さらに進めました。

`UniversalPaymentBlock.lean` に追加:

- `orbitPaymentTarget` の monotonicity
- consecutive target が等しいことと height-one の同値
- consecutive target が厳密増加することと extra-height の同値
- source fiber 非空と endpoint extra-height の同値
- universal block card
  `= endpoint - start + 1`
  `= start の orbitExactDepth`

これにより、universal payment block の長さは開始点の exact-depth と厳密に一致します。block length と depth histogram を繋ぐ最初の直接定理です。

stale footer も更新し、universal block geometry が完了済みであることを反映しました。

検証済み:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock
```

レポート: [report-petal-307.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-307.md)

## Review

## 結論

**採用。cp-307 は universal payment target の幾何を完成させた。**

今回の成果は、単なる monotonicity 追加ではない。

`orbitPaymentTarget` が自然数時刻上の **閉包作用**として完成した。

$$
i\le\tau(i),\qquad i\le k\Longrightarrow\tau(i)\le\tau(k),\qquad\tau(\tau(i))=\tau(i)
$$

さらに fixed point は extra-height endpoint と完全に一致する。

$$
\tau(i)=i\Longleftrightarrow2\le h_i
$$

各 fixed point $j$ の fiber は連続区間であり、その長さは block start の exact depth に一致する。

$$
\operatorname{Fiber}(j)=[b,j],\qquad|\operatorname{Fiber}(j)|=j-b+1=A_b
$$

これにより、軌道時刻は「payment endpoint への閉包 fiber」として block 化できる状態になった。

## 1. target dynamics の完全分類

追加された二本は、局所 target 運動を完全に分類している。

```lean
orbitPaymentTarget_succ_eq_iff_orbitWindowHeight_eq_one
orbitPaymentTarget_lt_succ_iff_two_le_orbitWindowHeight
```

数学的には、

$$
\tau(i+1)=\tau(i)\Longleftrightarrow h_i=1
$$

$$
\tau(i)<\tau(i+1)\Longleftrightarrow2\le h_i
$$

じゃ。

つまり target map は、

```text
height = 1:
  現在の payment endpoint へ向かって水平移動

height >= 2:
  現在の block を閉じ、次の payment endpoint へ厳密前進
```

という階段関数になった。

これは Collatz の値そのものを追わず、**payment endpoint の遷移だけで時間軸を圧縮する構造**じゃ。

## 2. `orbitPaymentTarget` は closure operator

現在証明済みの三性質は、順序論における closure operator そのものじゃ。

### Extensive

$$
i\le\tau(i)
$$

### Monotone

$$
i\le k\Longrightarrow\tau(i)\le\tau(k)
$$

### Idempotent

$$
\tau(\tau(i))=\tau(i)
$$

したがって payment endpoint は、外から与えた恣意的な観測点ではない。

> 軌道時刻を閉包したときに得られる canonical fixed point

である。

Mathlib の closure-operator 構造を直接使うかは audit が必要だが、少なくとも DkMath 内ではこの三性質を一つの API として束ねる価値がある。

## 3. source fiber の `range` 制約は冗長になった

現在の定義は、

```lean
orbitPaymentSourceFiberAt n j :=
  (Finset.range (j + 1)).filter fun i =>
    orbitPaymentTarget n i = j
```

じゃ。

しかし、

$$
i\le\tau(i)
$$

が証明されたため、

$$
\tau(i)=j\Longrightarrow i\le j
$$

である。

したがって、数学的には source fiber は単純な関数 fiber じゃ。

$$
i\in\operatorname{Fiber}(j)\Longleftrightarrow\tau(i)=j
$$

次の wrapper は有用じゃ。

```lean
theorem mem_orbitPaymentSourceFiberAt_iff_target_eq
    {n : OddNat} {i j : ℕ} :
    i ∈ orbitPaymentSourceFiberAt n j ↔
      orbitPaymentTarget n i = j
```

これにより、以後の fiber 証明から毎回の `i ≤ j` 条件を消せる。

## 4. nonempty fiber と endpoint の同値

```lean
orbitPaymentSourceFiberAt_nonempty_iff_two_le_orbitWindowHeight
```

により、

$$
\operatorname{Fiber}(j)\ne\varnothing\Longleftrightarrow2\le h_j
$$

が確定した。

これは三つの集合が一致することを意味する。

```text
target map の image
target map の fixed points
extra-height orbit times
```

数式では、

$$
\operatorname{Im}(\tau)=\operatorname{Fix}(\tau)={j\mid2\le h_j}
$$

じゃ。

この時点で `PaymentEndpoint` subtype を導入する条件は完全に揃った。

```lean
def PaymentEndpoint (n : OddNat) :=
  {j : ℕ // 2 ≤ orbitWindowHeight n j}
```

この subtype 上なら、fiber nonempty の証明を毎回引数として持ち回る必要がなくなる。

## 5. block length と exact depth の一致

今回の中心成果は、

```lean
orbitPaymentSourceFiberAt_card_eq_orbitExactDepth_start
```

じゃ。

universal block を $[b,j]$ とすれば、

$$
|\operatorname{Fiber}(j)|=j-b+1=A_b
$$

である。

この式は、三つの異なる量を同一視した。

```text
時間方向:
  payment block の時刻数

残余深度方向:
  block start の exact all-ones depth

射影方向:
  一つの endpoint fiber の cardinality
```

つまり exact depth は単なる residue statistic ではない。

> **次の payment endpoint までに残された時間距離そのもの**

じゃ。

これは Pressure と Float の接続に直結する。

## 6. block 内の depth histogram

cp-306 で既に、block 内の exact depth は、

$$
A_i=j-i+1
$$

と証明されている。

cp-307 の cardinality theorem と合わせると、長さ $L$ の block では exact depth が、

$$
L,L-1,\ldots,3,2,1
$$

と一度ずつ現れる。

したがって、固定 depth $d\ge1$ に対する一 block の寄与は完全に計算できる。

### Recovery contribution

$$
E_d(B)=\begin{cases}1&d\le L\\0&L<d\end{cases}
$$

### Continuation contribution

$$
C_d(B)=L-d
$$

ここで Nat subtraction により $d\ge L$ では自動的に $0$ になる。

### Pressure contribution

整数値では、

$$
M_d(B)=(L-d)-\mathbf{1}_{d\le L}
$$

となる。

つまり長い block は浅い depth で正 pressure を生み、block の最深部付近では非正になる。

これは pressure island の形を、block-length histogram だけで説明する式になる。

## 7. cp-307 の report 評価

report の評価は正しい。

```text
universal block geometry:
  完成

次:
  universal claim filter
  endpoint capacity
  universal ledger
```

stale footer も正しく更新された。

今回の停止地点も妥当じゃ。cp-306 までのような誤った論理障害ではなく、幾何層が閉じ、次に会計層へ移る自然な区切りになっている。

## 8. 次は全 universal block の直接 ledger

次の theorem は debt-supported block を経由せず、全 payment endpoint に対して直接証明すべきじゃ。

universal block を $[b,j]$ とする。

### Complete claim count

$$
Q_j=\#{i\in[b,j]\mid\operatorname{CarryTwoDebtAt}(n,i)}
$$

interior の carry-two は delayed claim。

endpoint の carry-two は immediate claim。

### Endpoint capacity

$$
P_j=h_j-1
$$

interior は全て height oneなので、capacity は endpoint に集中する。

### Universal block ledger

$$
w_{j+1}+P_j=w_b+Q_j
$$

signed form は、

$$
Q_j-P_j=w_{j+1}-w_b
$$

じゃ。

これが全 universal block で成立すれば、delayed debt を持たない下降 block も含めて block 列を合算できる。

## 9. endpoint sequence

次の自然な定義は payment endpoint の列じゃ。

$$
e_0=\tau(0)
$$

$$
e_{k+1}=\tau(e_k+1)
$$

cp-307 の strict target theoremにより、

$$
e_k<e_{k+1}
$$

となる。

さらに、次 block の start は厳密に、

$$
e_k+1
$$

になるはずじゃ。

理由は、$e_k$ は fixed point であり、$\tau(e_k+1)>e_k$。もし次 fiber の start が $e_k$ 以下なら monotonicity に反する。

したがって blocks は、

$$
[0,e_0],\quad[e_0+1,e_1],\quad[e_1+1,e_2],\ldots
$$

と隙間なく並ぶ。

これは arbitrary prefix 分解より先に、endpoint-aligned prefix を証明する最短路じゃ。

## 10. endpoint-aligned telescope を先に作る

いきなり任意 prefix の unfinished suffix を扱うより、まず第 $m$ endpoint までの完全 block family を閉じるべきじゃ。

最初の $m+1$ blocks の和集合は、

$$
[0,e_m]
$$

となる。

各 universal block の signed drift を足せば、内部 width が telescope し、

$$
\sum_{k=0}^{m}(Q_{e_k}-P_{e_k})=w_{e_m+1}-w_0
$$

を得る。

この endpoint-aligned theorem を先に固定すれば、任意 prefix は、

```text
完了 block 群
+
最後の unfinished height-one suffix
```

として一段追加するだけになる。

## 判定まとめ

## 実装

**採用。**

## 数学的到達点

**universal payment target の closure geometry 完成。**

## 新しい本質

**block length と exact all-ones depth が同一量になった。**

## 次の最優先

**全 universal block に対する直接 claim/capacity ledger。**

## その次

**canonical endpoint sequence と endpoint-aligned telescope。**

## Codex 指示

```text
Continue the DkMath Collatz / PetalBridge Float-window branch after
report-petal-307.

The cp-307 implementation is accepted.

The universal payment target is now an extensive, monotone, idempotent map on
orbit time. Its fixed points are exactly extra-height endpoints, and each
nonempty fiber is a contiguous universal payment block whose cardinality is
the exact depth at its start.

The next task is direct accounting on every universal block, including blocks
with no delayed Float-growth debt.

# Stage A — closure and pure fiber API

Add a theorem removing the now-redundant range condition:

    i ∈ orbitPaymentSourceFiberAt n j
      ↔ orbitPaymentTarget n i = j

using:

    le_orbitPaymentTarget

Package the three closure properties:

    extensive
    monotone
    idempotent

Audit whether Mathlib already provides a suitable closure-operator structure.
Use it only if dependency placement remains clean; otherwise expose a small
local theorem bundle.

Prove the image/fixed-point characterization:

    j is in the image of orbitPaymentTarget n
      ↔ orbitPaymentTarget n j = j
      ↔ 2 ≤ orbitWindowHeight n j

# Stage B — endpoint subtype

Introduce when useful:

    def PaymentEndpoint (n : OddNat) :=
      {j : ℕ // 2 ≤ orbitWindowHeight n j}

Provide proof-independent endpoint APIs:

    sourceFiber
    blockStart
    block
    blockLength

Avoid passing arbitrary `Nonempty` proofs through block-family data.

# Stage C — block-length/depth refinements

For a payment endpoint with universal start `b`, prove:

    blockLength = j - b + 1
    blockLength = orbitExactDepth n b

Prove that every depth in:

    Finset.Icc 1 blockLength

occurs exactly once in the block.

Expose exact block-local counts:

    recovery count at depth d
      = if d ≤ blockLength then 1 else 0

    continuation count at depth d
      = blockLength - d

Keep depth-zero behavior explicit.

# Stage D — universal complete-claim fiber

For every nonempty universal source fiber, prove:

    i ∈ carryTwoPaymentClaimFiberAt n j
      ↔
    i ∈ Finset.Icc (universalPaymentBlockStart n j h) j
      ∧ CarryTwoDebtAt n i

Handle:

    i < j:
      universal interior height is one, so carry two gives a delayed claim

    i = j:
      endpoint height is at least two, so carry two gives an immediate claim

Derive the Finset equality and cardinality theorem.

# Stage E — universal endpoint capacity

Prove:

    extraPaymentCapacityOn n
      (Finset.Icc (universalPaymentBlockStart n j h) j)
    =
    extraPaymentCapacityAt n j

All strict interior contributions are zero because their height is one.

# Stage F — direct universal block ledger

Apply the generic shifted ledger from the universal start through `j + 1`.

Prove:

    bitWidth (iterateT (j + 1) n).1
        + extraPaymentCapacityAt n j
      =
    bitWidth
        (iterateT (universalPaymentBlockStart n j h) n).1
        + (carryTwoPaymentClaimFiberAt n j).card

This theorem must not require a nonempty delayed-growth debt fiber.

Add the signed form:

    claim card - capacity
      =
    width after block - width before block

and its positive / zero / negative classification.

# Stage G — compatibility cleanup

Introduce a proof-independent signed drift at endpoint level.

Retain the earlier debt-supported signed drift as a compatibility theorem, not
as the primary universal definition.

For endpoints with delayed-growth debt, prove compatibility between the
universal-start ledger and the earlier debt-supported-start ledger.

# Stage H — canonical endpoint sequence

Define:

    paymentEndpointSeq n 0 =
      orbitPaymentTarget n 0

    paymentEndpointSeq n (k + 1) =
      orbitPaymentTarget n (paymentEndpointSeq n k + 1)

Prove:

    paymentEndpointSeq n k < paymentEndpointSeq n (k + 1)

Prove the exact block starts:

    first block starts at 0

    block k + 1 starts at paymentEndpointSeq n k + 1

and the block intervals:

    Icc 0 (endpoint 0)

    Icc (endpoint k + 1) (endpoint (k + 1))

# Stage I — endpoint-aligned finite partition

Before treating arbitrary prefixes, prove that the first `m + 1` blocks are
pairwise disjoint, adjacent, and have union:

    Finset.Icc 0 (paymentEndpointSeq n m)

# Stage J — endpoint-aligned telescope

Sum universal signed block drifts over the first `m + 1` completed blocks.

Prove:

    sum block drifts
      =
    bitWidth after the final endpoint
      -
    initial bitWidth

This theorem has no unfinished suffix and should be completed before the
arbitrary-prefix version.

# Stage K — arbitrary finite prefix

Only after the endpoint-aligned telescope is complete, decompose an arbitrary
finite prefix into:

    completed endpoint blocks
    plus one explicit unfinished height-one suffix

Do not drop the suffix.

# Stage L — pressure histogram bridge

For each completed block of length `L`, prove its exact contribution to:

    recovery fibers
    continuation fibers
    source pressure margin

Then sum these formulas over an endpoint-aligned block family.

Preserve the unfinished suffix as a separate boundary term in the arbitrary
prefix theorem.

Continue autonomously through every stage that follows from the existing API.
Stop only at a genuine mathematical obstruction or an unresolved dependency
placement conflict.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-308.md
```

cp-307 によって、軌道時刻は closure fiber の列として見えるようになった。

次は各 fiber に会計を載せ、その fiber 列を足し合わせる段階じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlock.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlock.lean
index de423879..68f8525e 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlock.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlock.lean
@@ -328,17 +328,98 @@ theorem orbitExactDepth_eq_endpoint_sub_add_one_of_mem_universalPaymentBlock
     dsimp [b] at hstart hijlt hbtarget hdepthi ⊢
     omega
 
+/-- Canonical payment targets are nondecreasing across one orbit step. -/
+theorem orbitPaymentTarget_le_succ
+    (n : OddNat) (i : ℕ) :
+    orbitPaymentTarget n i ≤ orbitPaymentTarget n (i + 1) := by
+  by_cases hheight : orbitWindowHeight n i = 1
+  · rw [orbitPaymentTarget_succ_eq_of_orbitWindowHeight_eq_one hheight]
+  · have htwo : 2 ≤ orbitWindowHeight n i := by
+      have hone := orbitWindowHeight_one_le n i
+      omega
+    exact (orbitPaymentTarget_lt_succ_of_two_le_orbitWindowHeight htwo).le
+
+/-- The target map is monotone on natural orbit times. -/
+theorem monotone_orbitPaymentTarget (n : OddNat) :
+    Monotone (orbitPaymentTarget n) := by
+  intro a b hab
+  induction b, hab using Nat.le_induction with
+  | base => exact le_rfl
+  | succ b _ ih => exact ih.trans (orbitPaymentTarget_le_succ n b)
+
+/-- Equal successive targets occur exactly at height-one sources. -/
+theorem orbitPaymentTarget_succ_eq_iff_orbitWindowHeight_eq_one
+    (n : OddNat) (i : ℕ) :
+    orbitPaymentTarget n (i + 1) = orbitPaymentTarget n i ↔
+      orbitWindowHeight n i = 1 := by
+  constructor
+  · intro heq
+    by_contra hnot
+    have htwo : 2 ≤ orbitWindowHeight n i := by
+      have hone := orbitWindowHeight_one_le n i
+      omega
+    have hlt := orbitPaymentTarget_lt_succ_of_two_le_orbitWindowHeight htwo
+    omega
+  · exact orbitPaymentTarget_succ_eq_of_orbitWindowHeight_eq_one
+
+/-- Strict target advance occurs exactly at extra-height sources. -/
+theorem orbitPaymentTarget_lt_succ_iff_two_le_orbitWindowHeight
+    (n : OddNat) (i : ℕ) :
+    orbitPaymentTarget n i < orbitPaymentTarget n (i + 1) ↔
+      2 ≤ orbitWindowHeight n i := by
+  constructor
+  · intro hlt
+    by_contra hnot
+    have hone : orbitWindowHeight n i = 1 := by
+      have hpos := orbitWindowHeight_one_le n i
+      omega
+    have heq := orbitPaymentTarget_succ_eq_of_orbitWindowHeight_eq_one hone
+    omega
+  · exact orbitPaymentTarget_lt_succ_of_two_le_orbitWindowHeight
+
+/-- Nonempty universal source fibers are exactly the extra-height endpoints. -/
+theorem orbitPaymentSourceFiberAt_nonempty_iff_two_le_orbitWindowHeight
+    (n : OddNat) (j : ℕ) :
+    (orbitPaymentSourceFiberAt n j).Nonempty ↔ 2 ≤ orbitWindowHeight n j := by
+  constructor
+  · exact two_le_orbitWindowHeight_of_orbitPaymentSourceFiberAt_nonempty
+  · intro htwo
+    refine ⟨j, ?_⟩
+    rw [mem_orbitPaymentSourceFiberAt_iff]
+    exact ⟨le_rfl, orbitPaymentTarget_eq_self_of_two_le_orbitWindowHeight htwo⟩
+
+/-- The cardinality of a universal payment block is its interval length. -/
+theorem orbitPaymentSourceFiberAt_card_eq_endpoint_sub_start_add_one
+    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
+    (orbitPaymentSourceFiberAt n j).card =
+      j - universalPaymentBlockStart n j h + 1 := by
+  rw [orbitPaymentSourceFiberAt_eq_Icc_universalPaymentBlockStart n j h]
+  have hstart := universalPaymentBlockStart_mem_sourceFiber n j h
+  have hle : universalPaymentBlockStart n j h ≤ j :=
+    (mem_orbitPaymentSourceFiberAt_iff.mp hstart).1
+  simp
+  omega
+
+/-- The universal block cardinality is the exact depth of its earliest source. -/
+theorem orbitPaymentSourceFiberAt_card_eq_orbitExactDepth_start
+    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
+    (orbitPaymentSourceFiberAt n j).card =
+      orbitExactDepth n (universalPaymentBlockStart n j h) := by
+  rw [orbitPaymentSourceFiberAt_card_eq_endpoint_sub_start_add_one n j h]
+  have hstart := universalPaymentBlockStart_mem_sourceFiber n j h
+  have hle : universalPaymentBlockStart n j h ≤ j :=
+    (mem_orbitPaymentSourceFiberAt_iff.mp hstart).1
+  exact (orbitExactDepth_eq_endpoint_sub_add_one_of_mem_universalPaymentBlock
+    (Finset.mem_Icc.mpr ⟨le_rfl, hle⟩)).symm
+
 /-!
-## Next closure requirement
-
-To identify a nonempty universal source fiber with the full interval from its
-minimum to its endpoint, the missing direction is not finite-set arithmetic.
-It is an exact-depth staircase *reverse closure*: from a source targeting `j`,
-one must show that every intervening time has the corresponding decremented
-exact depth and therefore the same target.  Until that theorem is supplied,
-this module intentionally exposes membership, minima, endpoint height, and
-the debt-fiber inclusion only; it does not claim interval contiguity or
-prefix-family coverage.
+## Current frontier
+
+Universal payment-block geometry is complete: target fibers are contiguous
+intervals with a descending exact-depth profile.  The remaining work is
+accounting over universal blocks and finite families of them: identify their
+complete claim fibers and endpoint capacity, prove their direct ledger, then
+retain an explicit unfinished suffix in finite-prefix decompositions.
 -/
 
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-307.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-307.md
new file mode 100644
index 00000000..498f8f2e
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-307.md
@@ -0,0 +1,24 @@
+# cp-307 Target Dynamics and Block-Length Bridge
+
+## Implemented
+
+`UniversalPaymentBlock.lean` now has the completed target dynamics API:
+
+- target map monotonicity;
+- equality of consecutive targets exactly at height-one times;
+- strict consecutive target advance exactly at extra-height times;
+- nonempty target fibers exactly at extra-height endpoints.
+
+The stale footer was replaced.  Universal block geometry is now recorded as
+complete.
+
+For a nonempty universal payment block, Lean also proves:
+
+```text
+fiber card = endpoint - start + 1 = exact depth at start
+```
+
+This is the direct bridge from universal block length to the exact-depth
+histogram.  The next layer is the universal complete-claim filter, endpoint
+capacity concentration, and the direct universal ledger; these have not been
+derived through the debt-only suffix.
````
`````
