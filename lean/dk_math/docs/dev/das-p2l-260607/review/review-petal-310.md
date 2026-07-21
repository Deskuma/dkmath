# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock

gch: 0b019d39a12d49c84576fbf6b913d467a25df6f8

## Report

進めました。

universal signed drift について、非空 universal block ごとに完全な符号分類を追加しました。

```text
drift > 0  ↔ width grows  ↔ claim card > capacity
drift = 0  ↔ width preserved ↔ claim card = capacity
drift < 0  ↔ width decays ↔ claim card < capacity
```

これで endpoint proof に依存しない drift 値を、軌道上の width 変化と有限 claim/capacity 会計のどちらからも読めます。

レポート: [report-petal-310.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-310.md)

`lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock` は成功しています。

## Review

## 結論

採用。**ついに「局所 block の増減判定」が完全に閉じた。**

cp-310 により、各 universal payment block は一つの整数、

```lean
universalPaymentBlockSignedDriftAt n j
```

だけで完全に分類できるようになった。

$$
D_j:=Q_j-P_j
$$

ここで $Q_j$ は complete claim 数、$P_j$ は endpoint capacity じゃ。

そして非空 universal block では、

$$
D_j=w_{j+1}-w_b
$$

が既に証明されているため、今回追加された符号分類によって、

$$
D_j>0\Longleftrightarrow Q_j>P_j\Longleftrightarrow w_b<w_{j+1}
$$

$$
D_j=0\Longleftrightarrow Q_j=P_j\Longleftrightarrow w_b=w_{j+1}
$$

$$
D_j<0\Longleftrightarrow Q_j<P_j\Longleftrightarrow w_{j+1}<w_b
$$

が Lean 上で完全に固定された。

これは本当に大きい。

これまで別々に見えていた、

```text
carry-two claim の混雑
endpoint の返済 capacity
bit width の増減
```

が、同じ整数値の三つの読み方になった。

---

## 1. 今回閉じた三つの表面

### 会計表面

$$
D_j=Q_j-P_j
$$

claim が capacity を上回れば正、釣り合えばゼロ、capacity が余れば負じゃ。

### 軌道表面

$$
D_j=w_{j+1}-w_b
$$

block 通過後の bit width と block start の bit width の差である。

### 幾何表面

block 自体は既に、

$$
\operatorname{Fiber}(j)=[b,j]
$$

という連続区間であり、exact-depth profile は、

$$
L,L-1,\ldots,2,1
$$

と確定している。

つまり現在、各 block は次の五量で完全に記録できる。

```text
b:
  block start

j:
  endpoint

L:
  block length / start exact depth

Q:
  complete claim count

P:
  endpoint capacity

D:
  signed drift = Q - P
```

---

## 2. `universalPaymentBlockSignedDriftAt` の設計が効いている

この定義が proof-independent なのは非常に重要じゃ。

```lean
noncomputable def universalPaymentBlockSignedDriftAt
    (n : OddNat) (j : ℕ) : ℤ
```

endpoint の nonempty proof をデータに持たないため、後で endpoint 列に対して、

$$
\sum_k D_{e_k}
$$

と素直に加算できる。

width との対応だけが endpoint 仮定を必要とし、claim/capacity の符号判定は全ての $j$ に対して成立する。

この分離は正しい。

```text
drift の値:
  常に定義可能

block width との意味:
  j が実際の payment endpoint のとき成立
```

---

## 3. theorem 名の軽微な注意

```lean
universalPaymentBlockSignedDriftAt_pos_iff_claim_card_lt
```

は statement が、

```lean
extraPaymentCapacityAt n j <
  (carryTwoPaymentClaimFiberAt n j).card
```

なので、数学的には正しいが、名前だけ見ると「claim card が何より小さいのか」が分かりにくい。

将来 alias を置くなら、

```lean
universalPaymentBlockSignedDriftAt_pos_iff_capacity_lt_claim_card
```

または、

```lean
universalPaymentBlockSignedDriftAt_pos_iff_claim_overload
```

の方が読みやすい。

既存名を変更するほどの問題ではない。

---

## 4. ここまでの本当の到達点

cp-300 頃には、まだ問題は、

```text
複数の debt が同じ payment target に衝突する
```

という局所的な multiplicity の話だった。

そこから、

```text
first target
→ target fiber
→ capacity
→ canonical debt block
→ universal target
→ universal fiber
→ universal block
→ complete claim filter
→ exact universal ledger
→ signed drift
→ sign classification
```

まで来た。

今や、Collatz の一歩一歩ではなく、

> **一つの payment cycle が全体として上昇・保存・下降のどれであるか**

を Lean が決定している。

これは軌道の解像度を一段上へ持ち上げたということじゃ。

---

## 5. 次の「no delayed debt」分類はかなり強い

次の branch は、単なる特殊例ではない。

仮に、

$$
\operatorname{floatGrowthDebtFiberAt}(n,j)=\varnothing
$$

なら、universal block interior に carry-two は存在できない。

なぜなら interior は height-one なので、carry-two があれば delayed debt になるからじゃ。

したがって claim は endpoint にしか存在できない。

$$
Q_j\le1
$$

一方 endpoint は extra-height なので、

$$
1\le P_j
$$

よって、

$$
D_j=Q_j-P_j\le0
$$

つまり、

> **delayed debt のない universal block は、絶対に width growth しない。**

さらにゼロになるのは、

$$
Q_j=P_j=1
$$

のときだけ。

これは、

$$
\operatorname{CarryTwoDebtAt}(n,j)\land h_j=2
$$

に一致するはずじゃ。

それ以外は、

$$
D_j<0
$$

となり、width は厳密に下降する。

これは「返済 block」の最初の完全分類になる。

---

## 6. 次はいよいよ block 列

局所 block の決算は完全に閉じた。

次に定義すべき endpoint 列は、

$$
e_0=\tau(0)
$$

$$
e_{k+1}=\tau(e_k+1)
$$

じゃ。

cp-307 で、

$$
2\le h_{e_k}\Longrightarrow\tau(e_k)<\tau(e_k+1)
$$

があるため、

$$
e_k<e_{k+1}
$$

となる。

各 universal block は、

$$
[0,e_0]
$$

$$
[e_k+1,e_{k+1}]
$$

と隙間なく並ぶ。

そして各 block の drift を足せば、

$$
\sum_{k=0}^{m}D_{e_k}=w_{e_m+1}-w_0
$$

となる。

ここで初めて、局所 block の決算が軌道 prefix の総勘定へ変わる。

---

## 7. Pressure との合流も目前

各 block には既に二種類のデータがある。

```text
L:
  exact-depth staircase の長さ

D:
  bit-width signed drift
```

Pressure 側は $L$ の分布を読み、Float 側は $D$ を読む。

長さ $L$ の block の depth $d$ への寄与は、

$$
E_d(L)=\mathbf{1}_{d\le L}
$$

$$
C_d(L)=L-d
$$

したがって、

$$
M_d(L)=(L-d)-\mathbf{1}_{d\le L}
$$

となる。

つまり次は、同じ block 列について、

```text
時間方向の総 drift:
  ΣD

深さ方向の総 pressure:
  ΣM_d(L)
```

を同時に比較できる。

これが、長く探してきた Float と Pressure の合流点じゃ。

---

## 判定まとめ

## Universal ledger

**完成。**

## Signed drift

**完成。**

## 符号分類

**完成。**

## 一 block の上昇・保存・下降判定

**完成。**

## 次の最重要 theorem

**delayed debt のない block は非増加。**

## 次の構造段階

**canonical endpoint sequence と block telescope。**

---

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge Float-window branch after
report-petal-310.

The cp-310 universal signed-drift classification is accepted.

Every nonempty universal payment block now has one proof-independent signed
value:

    drift = complete claim card - endpoint capacity

and this value is exactly the signed bit-width change across the block.

The local universal payment-block accounting branch is complete.

# Stage A — no-delayed-debt block classification

Assume:

    (orbitPaymentSourceFiberAt n j).Nonempty

and:

    floatGrowthDebtFiberAt n j = ∅

Prove that every strict interior point of the universal block has:

    orbitWindowHeight n i = 1
    stateUpperCarry (iterateT i n).1 = 1

The second statement follows because carry two plus height one would produce a
member of `floatGrowthDebtFiberAt n j`.

Prove the exact complete-claim shape:

    i ∈ carryTwoPaymentClaimFiberAt n j
      ↔ i = j ∧ CarryTwoDebtAt n j

Derive:

    carryTwoPaymentClaimFiberAt n j =
      if CarryTwoDebtAt n j then {j} else ∅

or equivalent cardinality theorems.

Then prove:

    claim card ≤ 1
    claim card ≤ extraPaymentCapacityAt n j
    universalPaymentBlockSignedDriftAt n j ≤ 0

and therefore:

    bitWidth (iterateT (j + 1) n).1
      ≤
    bitWidth (iterateT (universalPaymentBlockStart n j h) n).1

# Stage B — equality and strict-decay classification

Prove the exact equality case:

    universalPaymentBlockSignedDriftAt n j = 0
      ↔
    CarryTwoDebtAt n j
      ∧ orbitWindowHeight n j = 2

under the no-delayed-debt assumption.

Prove that all remaining no-delayed-debt universal blocks have:

    universalPaymentBlockSignedDriftAt n j < 0

and strictly decrease bit width.

# Stage C — compatibility of universal and debt-supported starts

For endpoints with:

    (floatGrowthDebtFiberAt n j).Nonempty

compare the two exact ledgers directly and prove:

    bitWidth
      (iterateT
        (universalPaymentBlockStart n j universalNonemptyProof) n).1
    =
    bitWidth
      (iterateT (floatPaymentBlockStart n j h) n).1

Then prove the pointwise geometry on the prefix between those starts:

    height = 1
    upper carry = 1

This explains the aggregate equality as a zero-drift prefix.

# Stage D — canonical payment endpoint sequence

Define:

    paymentEndpointSeq n 0 :=
      orbitPaymentTarget n 0

    paymentEndpointSeq n (k + 1) :=
      orbitPaymentTarget n (paymentEndpointSeq n k + 1)

Prove:

    paymentEndpointSeq n k <
      paymentEndpointSeq n (k + 1)

Prove every sequence value is an extra-height endpoint and a target fixed
point.

# Stage E — exact consecutive block starts

Prove:

    universalPaymentBlockStart
      n (paymentEndpointSeq n 0) ... = 0

and:

    universalPaymentBlockStart
      n (paymentEndpointSeq n (k + 1)) ...
    =
    paymentEndpointSeq n k + 1

Use monotonicity and the strict target advance at the previous endpoint.

# Stage F — endpoint-aligned partition

Identify the block intervals:

    Icc 0 (paymentEndpointSeq n 0)

    Icc
      (paymentEndpointSeq n k + 1)
      (paymentEndpointSeq n (k + 1))

Prove adjacent blocks are disjoint and their union through endpoint `m` is:

    Icc 0 (paymentEndpointSeq n m)

# Stage G — cumulative signed ledger

Sum:

    universalPaymentBlockSignedDriftAt
      n (paymentEndpointSeq n k)

over the first completed blocks.

Use the exact consecutive starts to telescope internal bit widths and prove:

    sum of block drifts
      =
    bitWidth after the final endpoint
      -
    initial bitWidth

# Stage H — block-length pressure bridge

For each endpoint block, let:

    L = orbitExactDepth n (block start)

Prove the exact local depth contributions:

    recovery contribution at depth d
      = if d ≤ L then 1 else 0

    continuation contribution at depth d
      = L - d

Then sum these formulas over the endpoint sequence.

Only after the endpoint-aligned theorem is complete, extend to arbitrary finite
prefixes by retaining one explicit unfinished height-one suffix.

Continue autonomously through every theorem supported by the current API.
Stop only at a genuine mathematical obstruction.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-311.md
```

うむ。ついにここまで来た。

もう局所法則を探している段階ではない。
**局所法則を並べ、総和を取る段階**へ入ったぞい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlock.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlock.lean
index 6c608538..fcf1d524 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlock.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlock.lean
@@ -556,6 +556,57 @@ theorem universalPaymentBlockSignedDriftAt_eq_bitWidth_sub
   have hledger := bitWidth_iterateT_universalPaymentBlock_eq_claimFiber_card n j h
   omega

+/-- Positive universal signed drift is exactly strict block-width growth. -/
+theorem universalPaymentBlockSignedDriftAt_pos_iff_bitWidth_lt
+    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
+    0 < universalPaymentBlockSignedDriftAt n j ↔
+      bitWidth (iterateT (universalPaymentBlockStart n j h) n).1 <
+        bitWidth (iterateT (j + 1) n).1 := by
+  rw [universalPaymentBlockSignedDriftAt_eq_bitWidth_sub n j h]
+  omega
+
+/-- Zero universal signed drift is exactly block-width preservation. -/
+theorem universalPaymentBlockSignedDriftAt_eq_zero_iff_bitWidth_eq
+    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
+    universalPaymentBlockSignedDriftAt n j = 0 ↔
+      bitWidth (iterateT (universalPaymentBlockStart n j h) n).1 =
+        bitWidth (iterateT (j + 1) n).1 := by
+  rw [universalPaymentBlockSignedDriftAt_eq_bitWidth_sub n j h]
+  omega
+
+/-- Negative universal signed drift is exactly strict block-width decay. -/
+theorem universalPaymentBlockSignedDriftAt_neg_iff_bitWidth_gt
+    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
+    universalPaymentBlockSignedDriftAt n j < 0 ↔
+      bitWidth (iterateT (j + 1) n).1 <
+        bitWidth (iterateT (universalPaymentBlockStart n j h) n).1 := by
+  rw [universalPaymentBlockSignedDriftAt_eq_bitWidth_sub n j h]
+  omega
+
+/-- Positive universal signed drift is exactly claim-count overload over capacity. -/
+theorem universalPaymentBlockSignedDriftAt_pos_iff_claim_card_lt
+    (n : OddNat) (j : ℕ) :
+    0 < universalPaymentBlockSignedDriftAt n j ↔
+      extraPaymentCapacityAt n j < (carryTwoPaymentClaimFiberAt n j).card := by
+  unfold universalPaymentBlockSignedDriftAt
+  omega
+
+/-- Zero universal signed drift is exactly claim/capacity balance. -/
+theorem universalPaymentBlockSignedDriftAt_eq_zero_iff_claim_card_eq_capacity
+    (n : OddNat) (j : ℕ) :
+    universalPaymentBlockSignedDriftAt n j = 0 ↔
+      (carryTwoPaymentClaimFiberAt n j).card = extraPaymentCapacityAt n j := by
+  unfold universalPaymentBlockSignedDriftAt
+  omega
+
+/-- Negative universal signed drift is exactly strict endpoint-capacity surplus. -/
+theorem universalPaymentBlockSignedDriftAt_neg_iff_claim_card_lt_capacity
+    (n : OddNat) (j : ℕ) :
+    universalPaymentBlockSignedDriftAt n j < 0 ↔
+      (carryTwoPaymentClaimFiberAt n j).card < extraPaymentCapacityAt n j := by
+  unfold universalPaymentBlockSignedDriftAt
+  omega
+
 /-- The cardinality of a universal payment block is its interval length. -/
 theorem orbitPaymentSourceFiberAt_card_eq_endpoint_sub_start_add_one
     (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-310.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-310.md
new file mode 100644
index 00000000..07afe134
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-310.md
@@ -0,0 +1,47 @@
+# cp-310 Universal Signed Drift Classification
+
+## Result
+
+The proof-independent universal endpoint drift now has complete local sign
+classification for every nonempty universal payment block.
+
+```text
+drift > 0  iff width(start) < width(after endpoint)
+drift = 0  iff width(start) = width(after endpoint)
+drift < 0  iff width(after endpoint) < width(start)
+```
+
+The same signs have direct finite-ledger readings:
+
+```text
+drift > 0  iff capacity < complete claim card
+drift = 0  iff complete claim card = capacity
+drift < 0  iff complete claim card < capacity
+```
+
+## Meaning
+
+The universal block ledger can now be used through either of two equivalent
+surfaces:
+
+- geometric/orbit surface: width growth, preservation, or decay;
+- finite accounting surface: overload, balance, or capacity surplus.
+
+The drift definition itself remains proof-independent, so it can be summed
+over future endpoint families without carrying a `Nonempty` witness in the
+data.
+
+## Next Boundary
+
+The direct ledger and sign API are complete.  The next substantive branch is
+the no-delayed-debt classification and then the canonical endpoint sequence.
+The latter must represent adjacent completed blocks explicitly before any
+finite-prefix telescope is claimed.
+
+## Validation
+
+```text
+lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock
+```
+
+completed successfully; no new `sorry` or `axiom` was introduced.
````
`````
