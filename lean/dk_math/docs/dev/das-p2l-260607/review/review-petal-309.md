# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock

gch: 1e5af93914e45f4b919f89e0bd915b9b0d51a5c4

## Report

universal block の直接 ledger を実装しました。

新定理は delayed Float-growth debt の非空性を必要とせず、任意の非空 universal source fiber に対して

```text
width after endpoint + endpoint capacity
=
width at universal start + complete claim count
```

を与えます。

あわせて proof-independent な

```lean
universalPaymentBlockSignedDriftAt n j
```

を追加し、これは universal block 上の signed width drift と一致します。

これにより、delayed debt を持たない capacity-surplus block も同じ会計に含まれることが確定しました。後続の cumulative ledger で削除してはいけない block です。

レポートを追加しました: [report-petal-309.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-309.md)

`lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock` は成功し、新規 `sorry` / `axiom` はありません。

## Review

## 結論

採用。**universal payment block の局所会計が完成した**

今回の中心定理、

```lean
bitWidth_iterateT_universalPaymentBlock_eq_claimFiber_card
```

は、任意の非空 universal source fiber に対して、

$$
w_{j+1}+P_j=w_b+Q_j
$$

を与える。

ここで、

* $b$ は universal block start
* $j$ は payment endpoint
* $Q_j$ は complete carry-two claim 数
* $P_j=h_j-1$ は endpoint capacity

じゃ。

さらに、

```lean
universalPaymentBlockSignedDriftAt
```

により、

$$
D_j:=Q_j-P_j=w_{j+1}-w_b
$$

が proof-independent な endpoint data として確定した。

これで cp-300 以降追ってきた、

```text
debt
→ first-payment target
→ target multiplicity
→ capacity
→ payment block
→ universal block
→ exact signed width drift
```

の局所幹線が完全に閉じた。

## universal block の直接 ledger

重要なのは、今回の theorem が、

```lean
(floatGrowthDebtFiberAt n j).Nonempty
```

を必要としないことじゃ。

必要なのは、

```lean
(orbitPaymentSourceFiberAt n j).Nonempty
```

だけである。

したがって対象は、全ての extra-height endpoint じゃ。

これには、interior に delayed carry-two debt を一つも持たない block も含まれる。

以前の debt-supported ledger は、

> 借金が発生した block の会計

だった。

今回の universal ledger は、

> 借金の有無に関係なく、全 payment cycle を記録する会計

になった。

ここが本質的な進展じゃ。

## transport chain

今回の証明は既存 API を正しく積み上げている。

### 区間輸送

```lean
universalPaymentBlockStart_add_length_eq_endpoint_succ
universalPaymentBlock_Ico_eq_Icc
```

により、$b$ から長さ $j+1-b$ の shifted interval が、

$$
[b,j]
$$

と一致する。

### Claim 輸送

```lean
shiftedOrbitCarryTwoCount_eq_carryTwoPaymentClaimFiber_card_universal
```

により、

$$
\operatorname{ShiftedCarryTwoCount}(b,j+1-b)=Q_j
$$

となる。

### Capacity 輸送

```lean
shiftedExtraPaymentCapacity_eq_extraPaymentCapacityAt_universal
```

により、

$$
\operatorname{ShiftedExtraCapacity}(b,j+1-b)=P_j
$$

となる。

これらを generic shifted width ledger へ代入して、中心等式を得ている。

新しい帰納や値計算を作らず、既存の幾何・filter・capacity API を合流させた良い証明じゃ。

## signed drift の意味

```lean
universalPaymentBlockSignedDriftAt n j
```

は、任意の時刻 $j$ に対して、

$$
D_j=Q_j-P_j
$$

と定義される。

$j$ が payment endpoint なら、

$$
D_j=w_{j+1}-w_b
$$

じゃ。

したがって universal block は整数値一つで分類できる。

$$
D_j>0\Longleftrightarrow w_b<w_{j+1}
$$

$$
D_j=0\Longleftrightarrow w_b=w_{j+1}
$$

$$
D_j<0\Longleftrightarrow w_{j+1}<w_b
$$

この三本はまだ theorem として追加されていないが、今回の signed equality から直ちに出る。

## delayed debt のない block

ここから非常に強い分類が得られる。

仮に、

```lean
floatGrowthDebtFiberAt n j = ∅
```

とする。

universal block interior $[b,j)$ に carry-two があれば、

* interior なので height は $1$
* carry-two と height-one なので delayed debt
* target は $j$

となり、growth debt fiber に入ってしまう。

したがって、interior は全て carry-one じゃ。

$$
b\le i<j\Longrightarrow c_i=1
$$

よって complete claim fiber に入り得るのは endpoint $j$ だけである。

したがって、

$$
Q_j=\begin{cases}1&c_j=2\\0&c_j=1\end{cases}
$$

一方、endpoint は extra-height なので、

$$
1\le P_j
$$

となる。

ゆえに必ず、

$$
Q_j\le P_j
$$

じゃ。

つまり、

> **delayed debt のない universal block は絶対に width growth を起こさない。**

さらに equality は一つの場合に限られる。

$$
Q_j=P_j\Longleftrightarrow c_j=2\land h_j=2
$$

それ以外では、

$$
Q_j<P_j
$$

なので width は厳密に減少する。

これは次 checkpoint で必ず定理化すべき強い分類じゃ。

## 旧 debt-supported ledger との関係

delayed growth debt が存在する endpoint では、次の二つの ledger が同時に成立する。

### Debt-supported start $a$

$$
w_{j+1}+P_j=w_a+Q_j
$$

### Universal start $b$

$$
w_{j+1}+P_j=w_b+Q_j
$$

したがって直ちに、

$$
w_b=w_a
$$

が得られる。

以前は、$[b,a)$ の全 step が carry-one / height-one であることを一つずつ証明して telescope する方針だった。

もちろんその局所定理にも意味はあるが、width equality だけなら、二つの完成済み ledger を比較するだけで即座に出る。

これは cp-309 によって生じた証明短縮じゃ。

## universal block の四要素

現在、各 universal block は次の四量で完全に記録できる。

```text
L:
  block length

Q:
  complete carry-two claim count

P:
  endpoint capacity

D:
  signed width drift = Q - P
```

数式では、

$$
L_j=|\operatorname{Fiber}(j)|=A_b
$$

$$
Q_j=\#\{i\in[b,j]\mid c_i=2\}
$$

$$
P_j=h_j-1
$$

$$
D_j=Q_j-P_j=w_{j+1}-w_b
$$

ここで、

* Pressure 層は主として $L_j$ の分布を見る
* Float 層は $Q_j$ と $P_j$ の差を見る

という役割分担が明確になった。

## pressure との直接接続

長さ $L$ の universal block では exact depth が、

$$
L,L-1,\ldots,2,1
$$

と一度ずつ現れる。

したがって depth $d$ における block 一個の recovery contribution は、

$$
E_d(L)=\mathbf{1}_{d\le L}
$$

continuation contribution は、

$$
C_d(L)=L-d
$$

となる。Nat subtraction により $L\le d$ では $0$ じゃ。

したがって block 一個の pressure contribution は、

$$
M_d(L)=(L-d)-\mathbf{1}_{d\le L}
$$

場合分けすると、

```text
L < d:
  0

L = d:
  -1

L = d + 1:
  0

d + 2 <= L:
  L - d - 1
```

となる。

つまり positive pressure は、depth $d$ で終わる block よりも、そこからさらに二段以上続く長い block の tail mass から生じる。

cp-309 により、この block-length pressure と block-width drift を同じ block record 上で比較できる段階へ来た。

## 判定

### Direct universal ledger

**完成。**

### Proof-independent signed drift

**完成。**

### Delayed debt のない block

**分類可能。次に定理化すべき。**

### 旧 debt ledger

**universal ledger の restricted compatibility theorem へ移行。**

### 次の本丸

**payment endpoint sequence と block-family telescope。**

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge Float-window branch after
report-petal-309.

The cp-309 direct universal payment-block ledger is accepted.

For every nonempty universal payment source fiber with start `b` and endpoint
`j`, Lean now proves:

    width after endpoint + endpoint capacity
      =
    width at universal start + complete claim count

and the proof-independent endpoint drift:

    universalPaymentBlockSignedDriftAt n j
      =
    claim count - endpoint capacity

equals the signed width change across the universal block.

# Stage A — universal drift sign classification

Prove for every nonempty universal block:

    0 < universalPaymentBlockSignedDriftAt n j
      ↔ width at block start < width after endpoint

    universalPaymentBlockSignedDriftAt n j = 0
      ↔ width at block start = width after endpoint

    universalPaymentBlockSignedDriftAt n j < 0
      ↔ width after endpoint < width at block start

Also expose the equivalent claim/capacity comparisons.

# Stage B — no-delayed-debt block classification

Assume:

    (orbitPaymentSourceFiberAt n j).Nonempty

and:

    floatGrowthDebtFiberAt n j = ∅

Prove that every strict universal-block interior point has:

    orbitWindowHeight n i = 1
    stateUpperCarry (iterateT i n).1 = 1

Then prove the exact claim-fiber shape:

    carryTwoPaymentClaimFiberAt n j
      =
    if CarryTwoDebtAt n j then {j} else ∅

or equivalent membership/cardinality statements.

Derive:

    claim card ≤ 1
    claim card ≤ endpoint capacity
    universalPaymentBlockSignedDriftAt n j ≤ 0
    width after endpoint ≤ width at block start

Classify equality exactly:

    universalPaymentBlockSignedDriftAt n j = 0
      ↔ CarryTwoDebtAt n j
        ∧ orbitWindowHeight n j = 2

All other no-delayed-debt blocks strictly decrease width.

# Stage C — compatibility with the earlier debt-supported ledger

For endpoints with:

    (floatGrowthDebtFiberAt n j).Nonempty

compare:

    bitWidth_iterateT_paymentBlock_eq_claimFiber_card
    bitWidth_iterateT_universalPaymentBlock_eq_claimFiber_card

and prove directly:

    bitWidth at universal start
      =
    bitWidth at debt-supported start

Then separately prove the stronger local geometry:

    for universal start ≤ i < debt start:
      height(i) = 1
      carry(i) = 1

The ledger comparison should provide the short aggregate proof; the local
theorem should explain why.

# Stage D — canonical endpoint sequence

Define:

    paymentEndpointSeq n 0 :=
      orbitPaymentTarget n 0

    paymentEndpointSeq n (k + 1) :=
      orbitPaymentTarget n (paymentEndpointSeq n k + 1)

Prove:

    paymentEndpointSeq n k < paymentEndpointSeq n (k + 1)

The first universal block must start at `0`.

For every successor endpoint prove that its universal block starts exactly at:

    paymentEndpointSeq n k + 1

Use monotonicity and the fact that the previous endpoint is a fixed point.

# Stage E — endpoint-aligned block partition

Prove the exact intervals:

    block 0 = Icc 0 (endpoint 0)

    block (k + 1) =
      Icc (endpoint k + 1) (endpoint (k + 1))

Show that consecutive blocks are adjacent and disjoint.

For the first `m + 1` blocks, prove their union is:

    Icc 0 (paymentEndpointSeq n m)

# Stage F — endpoint-aligned telescope

Sum:

    universalPaymentBlockSignedDriftAt n (paymentEndpointSeq n k)

over the first `m + 1` endpoints.

Prove that the block width differences telescope to:

    bitWidth after paymentEndpointSeq n m
      -
    initial bitWidth

This is the first cumulative universal block ledger.

# Stage G — block data package

Introduce a light endpoint-level package when useful, containing:

    endpoint
    block start
    block length
    claim count
    capacity
    signed drift

Avoid adding abstraction that obstructs rewriting with the existing theorems.

# Stage H — pressure contribution of one block

For a universal block of length `L`, prove:

    exact-depth recovery contribution at d
      = if d ≤ L then 1 else 0

    continuation contribution at d
      = L - d

and the signed pressure contribution:

    (L - d : Int) - if d ≤ L then 1 else 0

Provide the simplified cases:

    L < d
    L = d
    L = d + 1
    d + 2 ≤ L

# Stage I — finite-family pressure ledger

Sum the one-block pressure contributions over the endpoint-aligned block
family.

Only after that, extend to arbitrary finite prefixes by adding one explicit
unfinished height-one suffix.

Continue autonomously through every theorem supported by the existing API.
Stop only at a genuine mathematical obstruction.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-310.md
```

cp-309 によって、block 一個の決算は終わった。

次は、借金のない返済 block を分類し、その決算書を時系列に並べて総勘定へ進む段階じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlock.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlock.lean
index 50d04fee..6c608538 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlock.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlock.lean
@@ -476,6 +476,86 @@ theorem extraPaymentCapacityOn_universalPaymentBlock_eq_endpoint_capacity
     exact False.elim (hj (Finset.mem_Icc.mpr
       ⟨(mem_orbitPaymentSourceFiberAt_iff.mp hstartmem).1, le_rfl⟩))

+/-- Endpoint arithmetic for a nonempty universal payment block. -/
+theorem universalPaymentBlockStart_add_length_eq_endpoint_succ
+    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
+    universalPaymentBlockStart n j h +
+      (j + 1 - universalPaymentBlockStart n j h) = j + 1 := by
+  have hstart := universalPaymentBlockStart_mem_sourceFiber n j h
+  have hle := (mem_orbitPaymentSourceFiberAt_iff.mp hstart).1
+  omega
+
+/-- The shifted universal interval is exactly the endpoint-inclusive universal block. -/
+theorem universalPaymentBlock_Ico_eq_Icc
+    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
+    Finset.Ico (universalPaymentBlockStart n j h)
+      (universalPaymentBlockStart n j h +
+        (j + 1 - universalPaymentBlockStart n j h)) =
+      Finset.Icc (universalPaymentBlockStart n j h) j := by
+  rw [universalPaymentBlockStart_add_length_eq_endpoint_succ]
+  ext i
+  simp
+
+/-- Shifted carry-two count on a universal payment block is its complete claim count. -/
+theorem shiftedOrbitCarryTwoCount_eq_carryTwoPaymentClaimFiber_card_universal
+    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
+    shiftedOrbitCarryTwoCount n (universalPaymentBlockStart n j h)
+      (j + 1 - universalPaymentBlockStart n j h) =
+      (carryTwoPaymentClaimFiberAt n j).card := by
+  let b := universalPaymentBlockStart n j h
+  let len := j + 1 - b
+  calc
+    shiftedOrbitCarryTwoCount n b len = (shiftedCarryTwoOffsets n b len).card :=
+      shiftedOrbitCarryTwoCount_eq_offset_card n b len
+    _ = (carryTwoPositions n (Finset.Ico b (b + len))).card :=
+      shiftedCarryTwoOffsets_card_eq_carryTwoPositions_Ico_card n b len
+    _ = (carryTwoPositions n (Finset.Icc b j)).card := by
+      rw [universalPaymentBlock_Ico_eq_Icc]
+    _ = (carryTwoPaymentClaimFiberAt n j).card :=
+      (carryTwoPaymentClaimFiberAt_card_eq_universalPaymentBlock_carryTwo_card n j h).symm
+
+/-- Shifted extra-height capacity on a universal block is its endpoint capacity. -/
+theorem shiftedExtraPaymentCapacity_eq_extraPaymentCapacityAt_universal
+    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
+    shiftedExtraPaymentCapacity n (universalPaymentBlockStart n j h)
+      (j + 1 - universalPaymentBlockStart n j h) = extraPaymentCapacityAt n j := by
+  let b := universalPaymentBlockStart n j h
+  let len := j + 1 - b
+  calc
+    shiftedExtraPaymentCapacity n b len =
+        extraPaymentCapacityOn n (Finset.Ico b (b + len)) :=
+      shiftedExtraPaymentCapacity_eq_extraPaymentCapacityOn_Ico n b len
+    _ = extraPaymentCapacityOn n (Finset.Icc b j) := by
+      rw [universalPaymentBlock_Ico_eq_Icc]
+    _ = extraPaymentCapacityAt n j :=
+      extraPaymentCapacityOn_universalPaymentBlock_eq_endpoint_capacity n j h
+
+/-- Exact width ledger for every nonempty universal payment block. -/
+theorem bitWidth_iterateT_universalPaymentBlock_eq_claimFiber_card
+    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
+    bitWidth (iterateT (j + 1) n).1 + extraPaymentCapacityAt n j =
+      bitWidth (iterateT (universalPaymentBlockStart n j h) n).1 +
+        (carryTwoPaymentClaimFiberAt n j).card := by
+  have hledger := bitWidth_iterateT_add_shiftedExtraPaymentCapacity_eq_shiftedCarryTwo
+    n (universalPaymentBlockStart n j h) (j + 1 - universalPaymentBlockStart n j h)
+  rw [shiftedExtraPaymentCapacity_eq_extraPaymentCapacityAt_universal,
+    shiftedOrbitCarryTwoCount_eq_carryTwoPaymentClaimFiber_card_universal] at hledger
+  simpa [universalPaymentBlockStart_add_length_eq_endpoint_succ] using hledger
+
+/-- Proof-independent signed drift at a universal payment endpoint. -/
+noncomputable def universalPaymentBlockSignedDriftAt (n : OddNat) (j : ℕ) : ℤ :=
+  (carryTwoPaymentClaimFiberAt n j).card - extraPaymentCapacityAt n j
+
+/-- Universal signed drift equals signed width drift across a nonempty block. -/
+theorem universalPaymentBlockSignedDriftAt_eq_bitWidth_sub
+    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
+    universalPaymentBlockSignedDriftAt n j =
+      (bitWidth (iterateT (j + 1) n).1 : ℤ) -
+        bitWidth (iterateT (universalPaymentBlockStart n j h) n).1 := by
+  unfold universalPaymentBlockSignedDriftAt
+  have hledger := bitWidth_iterateT_universalPaymentBlock_eq_claimFiber_card n j h
+  omega
+
 /-- The cardinality of a universal payment block is its interval length. -/
 theorem orbitPaymentSourceFiberAt_card_eq_endpoint_sub_start_add_one
     (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-309.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-309.md
new file mode 100644
index 00000000..ac709652
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-309.md
@@ -0,0 +1,55 @@
+# cp-309 Direct Universal Payment-Block Ledger
+
+## Main Result
+
+The exact width ledger is now proved directly for every nonempty universal
+payment block.  It does not assume a nonempty delayed Float-growth debt fiber.
+
+For universal start `b` and endpoint `j`, Lean proves:
+
+```text
+bitWidth(iterateT(j + 1)) + extraPaymentCapacityAt(j)
+  =
+bitWidth(iterateT(b)) + card(carryTwoPaymentClaimFiberAt(j))
+```
+
+This is the correct block-local accounting surface for all extra-height
+endpoints, including blocks with no delayed carry-two growth debt.
+
+## Transport Chain
+
+The proof combines three direct universal identities:
+
+1. The shifted interval `[b, b + len)` equals `Icc(b, j)` for
+   `len = j + 1 - b`.
+2. The shifted carry-two count equals the complete carry-two claim-fiber card.
+3. The shifted extra-height capacity equals the endpoint capacity.
+
+The generic shifted width ledger then closes the equality without passing
+through the delayed-growth-debt suffix.
+
+## Signed Form
+
+Added proof-independent endpoint data:
+
+```text
+universalPaymentBlockSignedDriftAt(n, j)
+  = claim card - endpoint capacity
+```
+
+For every nonempty universal source fiber this is exactly the signed width
+change from the universal block start to the state after the endpoint.
+
+## Consequence
+
+Universal payment blocks with no delayed growth debt are now included in the
+same accounting theorem.  They can carry capacity surplus and therefore are
+not removable from any later cumulative/telescoping argument.
+
+## Validation
+
+```text
+lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock
+```
+
+completed successfully.  No new `sorry` or `axiom` was introduced.
````
`````
