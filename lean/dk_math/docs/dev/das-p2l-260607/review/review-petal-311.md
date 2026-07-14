# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock

gch: 498569e0ff071a30e0440e9b6a9e22541ab555c0

## Report

実装を進め、Stage A/B と Stage D/E を固定しました。

- debt-free universal block の内部 carry は必ず `1`
- complete claim fiber は endpoint singleton または空
- debt-free block は幅非増加
- 幅保存は `endpoint carry-two ∧ height = 2` と同値
- それ以外は厳密に幅減少
- `paymentEndpointSeq` は厳密増加し、各 endpoint は target fixed point
- 最初の block start は `0`、以後の start は前 endpoint の直後

レポートを追加しました: [report-petal-311.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-311.md)

検証済み: `UniversalPaymentBlock`、`DkMath.Collatz.PetalBridge`、`DkMath` の build と `git diff --check`。新規 `sorry` / axiom はありません。

## Review

## 結論

**採用。これは本当に節目じゃ。**

cp-311 は、これまで別々に構築してきた二本の幹線を同時に閉じた。

```text
局所会計側:
  delayed debt のない block は増加できない

時間配列側:
  universal payment blocks は canonical endpoint sequence に沿って
  隙間なく連続して並ぶ
```

とくに重要なのは、次の完全分類じゃ。

$$
\operatorname{DebtFiber}(j)=\varnothing\Longrightarrow D_j\le0
$$

さらに、

$$
D_j=0\Longleftrightarrow c_j=2\land h_j=2
$$

それ以外では、

$$
D_j<0
$$

となる。

つまり、

> **width growth を起こす universal block には、必ず delayed growth debt が存在する。**

一方、`paymentEndpointSeq` によって、これらの universal blocks を軌道時刻順に並べる座標も完成した。

ここから先は「局所 block が何か」を調べる段階ではない。

**全 block を並べて総和を取る段階**じゃ。

## 1. debt-free block の完全分類

今回の分類は非常に強い。

非空 universal block $[b,j]$ において、

$$
\operatorname{floatGrowthDebtFiberAt}(n,j)=\varnothing
$$

とする。

universal block の strict interior はすでに全て height-one じゃ。

$$
b\le i<j\Longrightarrow h_i=1
$$

ここで interior carry が $2$ なら、

```text
carry two
+
height one
+
target j
```

となり、時刻 $i$ は `floatGrowthDebtFiberAt n j` に入る。

これは空仮定に反する。

したがって、

$$
b\le i<j\Longrightarrow c_i=1
$$

が証明された。

これは単なる claim-count 上界ではない。

> **借金のない block の内部は、完全な carry-one staircase である。**

と確定したことになる。

## 2. claim fiber は endpoint だけになる

今回、

```lean
mem_carryTwoPaymentClaimFiberAt_iff_eq_endpoint_and_carryTwo_of_growthDebtFiber_eq_empty
```

により、

$$
i\in\operatorname{ClaimFiber}(j)\Longleftrightarrow i=j\land c_j=2
$$

が証明された。

したがって claim fiber は厳密に二択じゃ。

$$
\operatorname{ClaimFiber}(j)=\begin{cases}{j}&c_j=2\\\varnothing&c_j=1\end{cases}
$$

よって、

$$
Q_j\in{0,1}
$$

となる。

一方、payment endpoint では、

$$
2\le h_j
$$

なので、

$$
1\le P_j=h_j-1
$$

じゃ。

したがって必ず、

$$
Q_j\le P_j
$$

となる。

これで debt-free block の非増加性は構造的に閉じた。

## 3. 保存される唯一の debt-free block

ゼロ drift の完全条件は、

```lean
universalPaymentBlockSignedDriftAt_eq_zero_iff_carryTwo_and_height_eq_two_of_growthDebtFiber_eq_empty
```

じゃ。

$$
D_j=0\Longleftrightarrow c_j=2\land h_j=2
$$

この条件では、

$$
Q_j=1,\qquad P_j=1
$$

であり、一件の immediate claim と一単位の endpoint capacity がちょうど相殺する。

それ以外は必ず、

$$
D_j<0
$$

じゃ。

場合を並べると明快になる。

| Endpoint carry | Endpoint height | Claim | Capacity | Drift |
| -------------- | --------------: | ----: | -------: | ----: |
| $1$            |             $2$ |   $0$ |      $1$ |  $-1$ |
| $1$            |        $3$ 以上 |   $0$ | $2$ 以上 |    負 |
| $2$            |             $2$ |   $1$ |      $1$ |   $0$ |
| $2$            |        $3$ 以上 |   $1$ | $2$ 以上 |    負 |

したがって debt-free block は、

```text
唯一の balance pattern
または
strict repayment pattern
```

のどちらかである。

## 4. 成長 block の必要条件が確定した

今回の定理の対偶から、直ちに次が出る。

$$
D_j>0\Longrightarrow\operatorname{floatGrowthDebtFiberAt}(n,j)\ne\varnothing
$$

さらに width 表面では、

$$
w_b<w_{j+1}\Longrightarrow\operatorname{floatGrowthDebtFiberAt}(n,j)\ne\varnothing
$$

じゃ。

つまり、

> **block width growth は、delayed debt の存在なしには発生できない。**

これで「悪い block」の場所が完全に局在化された。

以前は全 block の carry pattern を警戒する必要があった。

現在は、

```text
debt-free block:
  必ず非増加

growth block:
  必ず delayed debt を含む
```

と二分できる。

これは大域解析に向けて非常に大きい圧縮じゃ。

## 5. 次に欲しい exact claim decomposition

今回の成果から、complete claim fiber は概念的に、

$$
\operatorname{ClaimFiber}(j)=\operatorname{GrowthDebtFiber}(j)\sqcup\operatorname{ImmediateClaim}(j)
$$

と分解できる。

endpoint immediate claim は高々一件なので、

$$
Q_j=R_j+\varepsilon_j
$$

と書ける。

ここで、

$$
R_j=\#\operatorname{floatGrowthDebtFiberAt}(n,j)
$$

$$
\varepsilon_j=\begin{cases}1&c_j=2\\0&c_j=1\end{cases}
$$

じゃ。

したがって signed drift は、

$$
D_j=R_j+\varepsilon_j-P_j
$$

となる。

これは非常に重要な次式じゃ。

block growth の条件が、

$$
R_j+\varepsilon_j>P_j
$$

として、delayed debt 数と endpoint repayment capacity の直接比較になる。

現在の会計を、さらに一段意味のある会計へ分解できる。

## 6. canonical endpoint sequence

新定義、

```lean
paymentEndpointSeq n
```

は、

$$
e_0=\tau(0)
$$

$$
e_{k+1}=\tau(e_k+1)
$$

である。

今回、次が証明された。

$$
e_k<e_{k+1}
$$

$$
2\le h_{e_k}
$$

$$
\tau(e_k)=e_k
$$

つまり、列の各要素は全て genuine payment endpoint であり、strictly increasing じゃ。

## 7. block start が完全に確定した

第一 block について、

$$
b_0=0
$$

後続 block について、

$$
b_{k+1}=e_k+1
$$

が証明された。

したがって block intervals は直ちに、

$$
B_0=[0,e_0]
$$

$$
B_{k+1}=[e_k+1,e_{k+1}]
$$

となる。

これは重要じゃ。

各 block が単に disjoint なのではない。

```text
前 block の endpoint
次 block の start
```

の間に隙間が全くない。

$$
\max B_k+1=\min B_{k+1}
$$

したがって endpoint sequence は、軌道時間を canonical payment blocks に切り分ける分割座標になった。

## 8. endpoint sequence は余終的である

strict increase から、

$$
k\le e_k
$$

が帰納的に従う。

したがって $e_k$ は無界である。

さらに任意の時刻 $i$ に対し、

$$
i\le e_i
$$

なので、時刻 $i$ は最初の $i+1$ block のどこかに必ず含まれる。

つまり、endpoint sequence は有限 prefix だけでなく、自然数時間全体を覆う。

これにより、次が証明可能になった。

> **全軌道時刻は、ただ一つの canonical universal payment block に属する。**

これは payment block 分解の大域的な存在・一意性じゃ。

Collatz の収束ではなく、**軌道時間の完全 block 分割**が見えたという意味である。

## 9. 全 extra-height endpoint も列挙できる

block $B_k$ の strict interior は全て height-one。

endpoint $e_k$ だけが extra-height じゃ。

したがって、

$$
2\le h_j\Longleftrightarrow\exists!k,\ j=e_k
$$

が導ける。

つまり `paymentEndpointSeq` は、単に一部の endpoint を選んだ列ではない。

> **全 extra-height payment endpoints を昇順に列挙する canonical enumeration**

になる。

これは次の Finset family や telescope における indexing を完全に解決する。

## 10. telescope はもう一本道

各 block $B_k=[b_k,e_k]$ について、

$$
D_{e_k}=w_{e_k+1}-w_{b_k}
$$

である。

start formula により、

$$
b_0=0
$$

$$
b_{k+1}=e_k+1
$$

なので、

$$
D_{e_0}=w_{e_0+1}-w_0
$$

$$
D_{e_1}=w_{e_1+1}-w_{e_0+1}
$$

$$
D_{e_2}=w_{e_2+1}-w_{e_1+1}
$$

と続く。

よって総和は完全に telescope する。

$$
\sum_{k=0}^{m}D_{e_k}=w_{e_m+1}-w_0
$$

ここには境界補正も unfinished suffix もない。

endpoint-aligned prefix だからじゃ。

この定理が次の checkpoint の中心になる。

## 11. Stage C を飛ばした判断

report にある通り、universal start と debt-supported start の compatibility はまだ未実装じゃ。

しかしこれは telescope の障害ではない。

今後の主 API は universal block なので、旧 debt-supported block との compatibility は、

```text
既存 theorem の整理
旧 API の意味付け
zero-drift prefix の説明
```

という補助 branch へ下がった。

したがって Stage C を後回しにして endpoint sequence へ進んだ判断は正しい。

主幹線は止めずに先へ進めるべきじゃ。

## 12. 数学的現在地

ここまで来ると、accelerated odd orbit は、値列ではなく次の block data 列として読める。

$$
(L_k,R_k,\varepsilon_k,P_k,D_k)
$$

ここで、

- $L_k$ は block length
- $R_k$ は delayed debt count
- $\varepsilon_k$ は endpoint immediate claim
- $P_k$ は endpoint capacity
- $D_k=R_k+\varepsilon_k-P_k$ は width drift

じゃ。

さらに、

$$
\sum_{k=0}^{m}D_k=w_{e_m+1}-w_0
$$

となる。

つまり Collatz の bit-width 運動は、

> delayed debt と repayment capacity の block-wise 累積収支

へ完全に翻訳される。

ここが大域 Big へ向かう、本当の会計表面じゃ。

## 判定まとめ

### Debt-free block

**完全分類。**

### Growth block の必要条件

**delayed debt の存在が必要。**

### Canonical endpoints

**定義・extra-height 性・strict increase 完成。**

### Consecutive block starts

**完成。**

### 時間軸の block 分割

**必要な材料は完成。**

### Telescope

**次の直結定理。**

### Pressure bridge

**block length 列上で接続可能。**

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge Float-window branch after
report-petal-311.

The cp-311 implementation is accepted.

Two central facts are now established:

1. A universal block with no delayed growth debt is never width-increasing.
   It is width-preserving only at the unique endpoint pattern
   `carry two ∧ height two`; otherwise it strictly decreases width.

2. `paymentEndpointSeq` gives strictly increasing canonical payment endpoints,
   with block zero starting at time zero and every successor block starting
   immediately after the previous endpoint.

The next branch is the exact endpoint-aligned partition and cumulative
telescoping ledger.

# Stage A — growth requires delayed debt

Prove the direct contrapositive consequences:

    0 < universalPaymentBlockSignedDriftAt n j
      ->
    (floatGrowthDebtFiberAt n j).Nonempty

and:

    bitWidth at universal start < bitWidth after endpoint
      ->
    (floatGrowthDebtFiberAt n j).Nonempty

for every nonempty universal source fiber.

# Stage B — complete claim decomposition

For a nonempty universal block, prove the disjoint decomposition:

    carryTwoPaymentClaimFiberAt n j
      =
    floatGrowthDebtFiberAt n j
      ∪ endpointImmediateCarryTwoClaim n j

where the endpoint term is `{j}` when `CarryTwoDebtAt n j`, and empty
otherwise.

Prove disjointness and the exact card formula:

    complete claim card
      =
    delayed growth-debt card
      +
    if CarryTwoDebtAt n j then 1 else 0

Derive the refined signed drift formula:

    universal drift
      =
    delayed debt card
      + endpoint immediate indicator
      - endpoint capacity

# Stage C — endpoint sequence lower bound and cofinality

Prove:

    k <= paymentEndpointSeq n k

and the stronger linear lower bound when convenient:

    paymentEndpointSeq n 0 + k <= paymentEndpointSeq n k

Conclude that the endpoint sequence is unbounded/cofinal in orbit time.

# Stage D — exact block intervals

For each `k`, define or expose the canonical endpoint block:

    block 0 =
      Finset.Icc 0 (paymentEndpointSeq n 0)

    block (k + 1) =
      Finset.Icc
        (paymentEndpointSeq n k + 1)
        (paymentEndpointSeq n (k + 1))

Prove that these are exactly the universal source fibers of their endpoints.

# Stage E — adjacency and disjointness

Prove:

    block k and block (k + 1) are disjoint

and more generally:

    k != l -> Disjoint (block k) (block l)

Use strict endpoint monotonicity and exact start formulas.

# Stage F — endpoint-aligned union

Prove by induction:

    union of blocks indexed by Finset.range (m + 1)
      =
    Finset.Icc 0 (paymentEndpointSeq n m)

A recursive prefix-block Finset definition is acceptable when it simplifies
the theorem.

# Stage G — all endpoints are enumerated

Prove:

    2 <= orbitWindowHeight n j
      <->
    exists! k, paymentEndpointSeq n k = j

Use the endpoint-aligned partition and the fact that every strict block
interior has height one.

Also prove that every orbit time belongs to exactly one canonical endpoint
block.

# Stage H — endpoint-aligned signed telescope

Prove:

    sum k in Finset.range (m + 1),
      universalPaymentBlockSignedDriftAt n (paymentEndpointSeq n k)
    =
    (bitWidth (iterateT (paymentEndpointSeq n m + 1) n).1 : Int)
      - bitWidth n.1

Use:

    universalPaymentBlockSignedDriftAt_eq_bitWidth_sub
    universalPaymentBlockStart_paymentEndpointSeq_zero
    universalPaymentBlockStart_paymentEndpointSeq_succ

The internal bit-width terms must cancel exactly.

# Stage I — debt/capacity cumulative form

Rewrite the telescope as:

    sum delayed debt counts
      + sum endpoint immediate indicators
      - sum endpoint capacities
    =
    final bit width - initial bit width

Keep all quantities integer-valued and subtraction-free until the final
signed statement when useful.

# Stage J — block-length pressure contribution

For the block ending at `paymentEndpointSeq n k`, let:

    L_k =
      orbitPaymentSourceFiberAt n (paymentEndpointSeq n k) |>.card

Prove its exact contribution at depth `d`:

    recovery contribution =
      if d <= L_k then 1 else 0

    continuation contribution =
      L_k - d

Then sum over `Finset.range (m + 1)`.

# Stage K — compatibility branch

After the cumulative mainline is secure, return to endpoints with a nonempty
delayed-growth debt fiber and prove:

    width at universal start = width at debt-supported start

by comparing the two exact block ledgers.

Then expose the intervening carry-one / height-one zero-drift prefix.

Continue autonomously through every theorem supported by the existing API.
Stop only at a genuine mathematical obstruction.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-312.md
```

うむ。

**局所決算書は完成し、勘定日も順番に並んだ。**

次はそれらを一冊の総勘定元帳へ綴じるところじゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlock.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlock.lean
index fcf1d524..7ded9378 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlock.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlock.lean
@@ -10,6 +10,8 @@ import DkMath.Collatz.PetalBridge.FloatWindow.PaymentBlockBridge
 
 namespace DkMath.Collatz
 
+set_option linter.style.longLine false
+
 /-!
 # Universal first-payment coordinates
 
@@ -607,6 +609,313 @@ theorem universalPaymentBlockSignedDriftAt_neg_iff_claim_card_lt_capacity
   unfold universalPaymentBlockSignedDriftAt
   omega
 
+/-!
+## Blocks with no delayed growth debt
+
+The following classification is deliberately local to one universal payment
+block.  Empty delayed-debt support does not assert anything about later
+blocks; it only excludes carry-two events at the height-one interior points of
+this particular canonical target fiber.
+-/
+
+/--
+In a debt-free universal block, every strict interior source has upper carry
+one.  A carry of two together with the already-known height-one interior
+profile would be a delayed growth debt for the same endpoint.
+-/
+theorem stateUpperCarry_eq_one_of_mem_universalPaymentBlockInterior_of_growthDebtFiber_eq_empty
+    {n : OddNat} {j i : ℕ} {h : (orbitPaymentSourceFiberAt n j).Nonempty}
+    (hempty : floatGrowthDebtFiberAt n j = ∅)
+    (hi : i ∈ Finset.Ico (universalPaymentBlockStart n j h) j) :
+    stateUpperCarry (iterateT i n).1 = 1 := by
+  have hheight := orbitWindowHeight_eq_one_of_mem_universalPaymentBlockInterior hi
+  have hnotcarry : ¬ CarryTwoDebtAt n i := by
+    intro hcarry
+    have hdebt : FloatDebtAt n i :=
+      (floatDebtAt_iff_delayedCarryTwoDebtAt n i).mpr ⟨hcarry, hheight⟩
+    rcases Finset.mem_Ico.mp hi with ⟨hstart, hij⟩
+    have htarget : floatDebtPaymentTarget n i = j := by
+      simpa [floatDebtPaymentTarget_eq_orbitPaymentTarget] using
+        orbitPaymentTarget_eq_endpoint_of_universalStart_le_lt hstart hij
+    have hfiber : i ∈ floatGrowthDebtFiberAt n j :=
+      mem_floatGrowthDebtFiberAt_iff.mpr ⟨Nat.lt_succ_of_lt hij, hdebt, htarget⟩
+    simp [hempty] at hfiber
+  have hpos : 0 < (iterateT i n).1 := by
+    have hodd := (iterateT i n).2
+    omega
+  rcases stateUpperCarry_one_or_two hpos with hone | htwo
+  · exact hone
+  · exact False.elim (hnotcarry htwo)
+
+/--
+With no delayed debt in a nonempty universal block, a complete carry-two claim
+can occur only at the endpoint.  Thus the full claim fiber is either the
+endpoint singleton or empty.
+-/
+theorem mem_carryTwoPaymentClaimFiberAt_iff_eq_endpoint_and_carryTwo_of_growthDebtFiber_eq_empty
+    {n : OddNat} {j i : ℕ} {h : (orbitPaymentSourceFiberAt n j).Nonempty}
+    (hempty : floatGrowthDebtFiberAt n j = ∅) :
+    i ∈ carryTwoPaymentClaimFiberAt n j ↔ i = j ∧ CarryTwoDebtAt n j := by
+  constructor
+  · intro hi
+    rcases mem_carryTwoPaymentClaimFiberAt_iff_mem_universalPaymentBlock_and_carryTwo.mp hi with
+      ⟨hblock, hcarry⟩
+    have hijle := (Finset.mem_Icc.mp hblock).2
+    by_cases hijEq : i = j
+    · exact ⟨hijEq, by simpa [hijEq] using hcarry⟩
+    · have hij : i < j := lt_of_le_of_ne hijle hijEq
+      have hinterior : i ∈ Finset.Ico (universalPaymentBlockStart n j h) j := by
+        exact Finset.mem_Ico.mpr ⟨(Finset.mem_Icc.mp hblock).1, hij⟩
+      have hone :=
+        stateUpperCarry_eq_one_of_mem_universalPaymentBlockInterior_of_growthDebtFiber_eq_empty
+          hempty hinterior
+      exfalso
+      unfold CarryTwoDebtAt at hcarry
+      omega
+  · rintro ⟨hi, hcarry⟩
+    subst i
+    apply
+      mem_carryTwoPaymentClaimFiberAt_iff_mem_universalPaymentBlock_and_carryTwo
+        (h := h) |>.mpr
+    have hstartmem := universalPaymentBlockStart_mem_sourceFiber n j h
+    exact ⟨Finset.mem_Icc.mpr
+      ⟨(mem_orbitPaymentSourceFiberAt_iff.mp hstartmem).1, le_rfl⟩, hcarry⟩
+
+/-- The endpoint-only candidate shape for a debt-free universal claim fiber. -/
+noncomputable def endpointCarryTwoClaimShape (n : OddNat) (j : ℕ) : Finset ℕ := by
+  classical
+  exact if CarryTwoDebtAt n j then {j} else ∅
+
+/-- Finset form: debt-free universal blocks have at most their endpoint claim. -/
+theorem carryTwoPaymentClaimFiberAt_eq_endpoint_singleton_or_empty_of_growthDebtFiber_eq_empty
+    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty)
+    (hempty : floatGrowthDebtFiberAt n j = ∅) :
+    carryTwoPaymentClaimFiberAt n j = endpointCarryTwoClaimShape n j := by
+  classical
+  ext i
+  unfold endpointCarryTwoClaimShape
+  rw [mem_carryTwoPaymentClaimFiberAt_iff_eq_endpoint_and_carryTwo_of_growthDebtFiber_eq_empty
+    (h := h) hempty]
+  by_cases hcarry : CarryTwoDebtAt n j <;> simp [hcarry]
+
+/-- A debt-free universal block has at most one complete carry-two claim. -/
+theorem carryTwoPaymentClaimFiberAt_card_le_one_of_growthDebtFiber_eq_empty
+    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty)
+    (hempty : floatGrowthDebtFiberAt n j = ∅) :
+    (carryTwoPaymentClaimFiberAt n j).card ≤ 1 := by
+  rw [carryTwoPaymentClaimFiberAt_eq_endpoint_singleton_or_empty_of_growthDebtFiber_eq_empty
+    n j h hempty]
+  unfold endpointCarryTwoClaimShape
+  classical
+  split <;> simp
+
+/-- Every nonempty universal endpoint has at least one unit of payment capacity. -/
+theorem one_le_extraPaymentCapacityAt_of_orbitPaymentSourceFiberAt_nonempty
+    {n : OddNat} {j : ℕ}
+    (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
+    1 ≤ extraPaymentCapacityAt n j := by
+  unfold extraPaymentCapacityAt
+  have hheight := two_le_orbitWindowHeight_of_orbitPaymentSourceFiberAt_nonempty h
+  omega
+
+/-- In a debt-free universal block, complete claims do not exceed endpoint capacity. -/
+theorem carryTwoPaymentClaimFiberAt_card_le_extraPaymentCapacityAt_of_growthDebtFiber_eq_empty
+    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty)
+    (hempty : floatGrowthDebtFiberAt n j = ∅) :
+    (carryTwoPaymentClaimFiberAt n j).card ≤ extraPaymentCapacityAt n j := by
+  have hclaim := carryTwoPaymentClaimFiberAt_card_le_one_of_growthDebtFiber_eq_empty n j h hempty
+  have hcapacity := one_le_extraPaymentCapacityAt_of_orbitPaymentSourceFiberAt_nonempty h
+  omega
+
+/-- A debt-free universal block has nonpositive signed width drift. -/
+theorem universalPaymentBlockSignedDriftAt_nonpos_of_growthDebtFiber_eq_empty
+    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty)
+    (hempty : floatGrowthDebtFiberAt n j = ∅) :
+    universalPaymentBlockSignedDriftAt n j ≤ 0 := by
+  rw [universalPaymentBlockSignedDriftAt]
+  apply sub_nonpos.mpr
+  exact_mod_cast
+    carryTwoPaymentClaimFiberAt_card_le_extraPaymentCapacityAt_of_growthDebtFiber_eq_empty
+      n j h hempty
+
+/-- Consequently, a debt-free universal block cannot increase bit width. -/
+theorem bitWidth_iterateT_le_of_universalPaymentBlock_growthDebtFiber_eq_empty
+    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty)
+    (hempty : floatGrowthDebtFiberAt n j = ∅) :
+    bitWidth (iterateT (j + 1) n).1 ≤
+      bitWidth (iterateT (universalPaymentBlockStart n j h) n).1 := by
+  have hdrift := universalPaymentBlockSignedDriftAt_nonpos_of_growthDebtFiber_eq_empty n j h hempty
+  rw [universalPaymentBlockSignedDriftAt_eq_bitWidth_sub n j h] at hdrift
+  omega
+
+/-- In a debt-free universal block, the complete claim count is one exactly at a carry-two endpoint. -/
+theorem carryTwoPaymentClaimFiberAt_card_eq_one_iff_carryTwoDebtAt_of_growthDebtFiber_eq_empty
+    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty)
+    (hempty : floatGrowthDebtFiberAt n j = ∅) :
+    (carryTwoPaymentClaimFiberAt n j).card = 1 ↔ CarryTwoDebtAt n j := by
+  rw [carryTwoPaymentClaimFiberAt_eq_endpoint_singleton_or_empty_of_growthDebtFiber_eq_empty
+    n j h hempty]
+  unfold endpointCarryTwoClaimShape
+  classical
+  by_cases hcarry : CarryTwoDebtAt n j <;> simp [hcarry]
+
+/-- At a nonempty universal endpoint, capacity one means exact observed height two. -/
+theorem extraPaymentCapacityAt_eq_one_iff_orbitWindowHeight_eq_two_of_nonempty
+    {n : OddNat} {j : ℕ} (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
+    extraPaymentCapacityAt n j = 1 ↔ orbitWindowHeight n j = 2 := by
+  unfold extraPaymentCapacityAt
+  have hheight := two_le_orbitWindowHeight_of_orbitPaymentSourceFiberAt_nonempty h
+  omega
+
+/--
+For a debt-free universal block, zero drift occurs exactly when the endpoint
+contributes its sole carry-two claim and has exactly one unit of capacity.
+-/
+theorem universalPaymentBlockSignedDriftAt_eq_zero_iff_carryTwo_and_height_eq_two_of_growthDebtFiber_eq_empty
+    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty)
+    (hempty : floatGrowthDebtFiberAt n j = ∅) :
+    universalPaymentBlockSignedDriftAt n j = 0 ↔
+      CarryTwoDebtAt n j ∧ orbitWindowHeight n j = 2 := by
+  constructor
+  · intro hzero
+    have hbalance := (universalPaymentBlockSignedDriftAt_eq_zero_iff_claim_card_eq_capacity n j).mp hzero
+    have hclaim := carryTwoPaymentClaimFiberAt_card_le_one_of_growthDebtFiber_eq_empty n j h hempty
+    have hcapacity := one_le_extraPaymentCapacityAt_of_orbitPaymentSourceFiberAt_nonempty h
+    have hclaimone : (carryTwoPaymentClaimFiberAt n j).card = 1 := by omega
+    have hcapacityone : extraPaymentCapacityAt n j = 1 := by omega
+    exact ⟨(carryTwoPaymentClaimFiberAt_card_eq_one_iff_carryTwoDebtAt_of_growthDebtFiber_eq_empty
+      n j h hempty).mp hclaimone,
+      (extraPaymentCapacityAt_eq_one_iff_orbitWindowHeight_eq_two_of_nonempty h).mp hcapacityone⟩
+  · rintro ⟨hcarry, hheight⟩
+    apply (universalPaymentBlockSignedDriftAt_eq_zero_iff_claim_card_eq_capacity n j).mpr
+    rw [(carryTwoPaymentClaimFiberAt_card_eq_one_iff_carryTwoDebtAt_of_growthDebtFiber_eq_empty
+      n j h hempty).mpr hcarry,
+      (extraPaymentCapacityAt_eq_one_iff_orbitWindowHeight_eq_two_of_nonempty h).mpr hheight]
+
+/--
+Every other debt-free universal block has strictly negative signed drift.
+This is the exact complement of the equality classification, not a global
+statement about blocks with delayed-debt sources.
+-/
+theorem universalPaymentBlockSignedDriftAt_neg_of_not_carryTwo_or_height_ne_two_of_growthDebtFiber_eq_empty
+    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty)
+    (hempty : floatGrowthDebtFiberAt n j = ∅)
+    (hneq : ¬ (CarryTwoDebtAt n j ∧ orbitWindowHeight n j = 2)) :
+    universalPaymentBlockSignedDriftAt n j < 0 := by
+  have hnonpos := universalPaymentBlockSignedDriftAt_nonpos_of_growthDebtFiber_eq_empty n j h hempty
+  have hne : universalPaymentBlockSignedDriftAt n j ≠ 0 := by
+    intro hzero
+    exact hneq ((universalPaymentBlockSignedDriftAt_eq_zero_iff_carryTwo_and_height_eq_two_of_growthDebtFiber_eq_empty
+      n j h hempty).mp hzero)
+  omega
+
+/-- Every non-equality debt-free universal block strictly decreases bit width. -/
+theorem bitWidth_iterateT_lt_of_universalPaymentBlock_not_carryTwo_or_height_ne_two
+    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty)
+    (hempty : floatGrowthDebtFiberAt n j = ∅)
+    (hneq : ¬ (CarryTwoDebtAt n j ∧ orbitWindowHeight n j = 2)) :
+    bitWidth (iterateT (j + 1) n).1 <
+      bitWidth (iterateT (universalPaymentBlockStart n j h) n).1 := by
+  exact (universalPaymentBlockSignedDriftAt_neg_iff_bitWidth_gt n j h).mp
+    (universalPaymentBlockSignedDriftAt_neg_of_not_carryTwo_or_height_ne_two_of_growthDebtFiber_eq_empty
+      n j h hempty hneq)
+
+/-!
+## Canonical endpoint sequence
+
+The sequence records the first payment endpoint, then the target immediately
+after each endpoint.  It is defined without choosing a proof of fiber
+nonemptiness; the target map itself supplies the endpoint property.
+-/
+
+/-- Canonical successive endpoints of universal payment blocks. -/
+noncomputable def paymentEndpointSeq (n : OddNat) : ℕ → ℕ
+  | 0 => orbitPaymentTarget n 0
+  | k + 1 => orbitPaymentTarget n (paymentEndpointSeq n k + 1)
+
+/-- Every canonical sequence entry is an extra-height endpoint. -/
+theorem two_le_orbitWindowHeight_paymentEndpointSeq
+    (n : OddNat) (k : ℕ) :
+    2 ≤ orbitWindowHeight n (paymentEndpointSeq n k) := by
+  cases k with
+  | zero =>
+      simpa [paymentEndpointSeq] using two_le_orbitWindowHeight_orbitPaymentTarget n 0
+  | succ k =>
+      simpa [paymentEndpointSeq] using
+        two_le_orbitWindowHeight_orbitPaymentTarget n (paymentEndpointSeq n k + 1)
+
+/-- Each canonical sequence entry is fixed by the universal target map. -/
+theorem orbitPaymentTarget_paymentEndpointSeq
+    (n : OddNat) (k : ℕ) :
+    orbitPaymentTarget n (paymentEndpointSeq n k) = paymentEndpointSeq n k := by
+  apply orbitPaymentTarget_eq_self_of_two_le_orbitWindowHeight
+  exact two_le_orbitWindowHeight_paymentEndpointSeq n k
+
+/-- Consecutive canonical payment endpoints are strictly increasing. -/
+theorem paymentEndpointSeq_lt_succ
+    (n : OddNat) (k : ℕ) :
+    paymentEndpointSeq n k < paymentEndpointSeq n (k + 1) := by
+  rw [show paymentEndpointSeq n (k + 1) =
+    orbitPaymentTarget n (paymentEndpointSeq n k + 1) by rfl]
+  have hlt := orbitPaymentTarget_lt_succ_of_two_le_orbitWindowHeight
+    (two_le_orbitWindowHeight_paymentEndpointSeq n k)
+  rw [orbitPaymentTarget_paymentEndpointSeq] at hlt
+  exact hlt
+
+/-- Every sequence endpoint has a nonempty universal source fiber. -/
+theorem orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq
+    (n : OddNat) (k : ℕ) :
+    (orbitPaymentSourceFiberAt n (paymentEndpointSeq n k)).Nonempty :=
+  (orbitPaymentSourceFiberAt_nonempty_iff_two_le_orbitWindowHeight n
+    (paymentEndpointSeq n k)).mpr (two_le_orbitWindowHeight_paymentEndpointSeq n k)
+
+/-- The first canonical payment block starts at orbit time zero. -/
+theorem universalPaymentBlockStart_paymentEndpointSeq_zero
+    (n : OddNat) :
+    universalPaymentBlockStart n (paymentEndpointSeq n 0)
+      (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n 0) = 0 := by
+  have hzero : 0 ∈ orbitPaymentSourceFiberAt n (paymentEndpointSeq n 0) := by
+    rw [mem_orbitPaymentSourceFiberAt_iff_target_eq]
+    rfl
+  unfold universalPaymentBlockStart
+  exact Nat.eq_zero_of_le_zero (Finset.min'_le _ _ hzero)
+
+/--
+The next canonical block starts immediately after the previous endpoint.
+Monotonicity rules out an earlier source: every index at most the old endpoint
+still targets at most that old endpoint, whereas the next target is strictly
+larger.
+-/
+theorem universalPaymentBlockStart_paymentEndpointSeq_succ
+    (n : OddNat) (k : ℕ) :
+    universalPaymentBlockStart n (paymentEndpointSeq n (k + 1))
+      (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n (k + 1)) =
+        paymentEndpointSeq n k + 1 := by
+  let e := paymentEndpointSeq n k
+  let e' := paymentEndpointSeq n (k + 1)
+  let h' := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n (k + 1)
+  let b := universalPaymentBlockStart n e' h'
+  have hsource : e + 1 ∈ orbitPaymentSourceFiberAt n e' := by
+    rw [mem_orbitPaymentSourceFiberAt_iff_target_eq]
+    change orbitPaymentTarget n (paymentEndpointSeq n k + 1) = paymentEndpointSeq n (k + 1)
+    rfl
+  have hble : b ≤ e + 1 := Finset.min'_le _ _ hsource
+  have hbtarget : orbitPaymentTarget n b = e' :=
+    (mem_orbitPaymentSourceFiberAt_iff.mp
+      (universalPaymentBlockStart_mem_sourceFiber n e' h')).2
+  by_contra hne
+  have hblt : b < e + 1 := lt_of_le_of_ne hble hne
+  have hbe : b ≤ e := by omega
+  have hmono : orbitPaymentTarget n b ≤ orbitPaymentTarget n e :=
+    monotone_orbitPaymentTarget n hbe
+  have hefix : orbitPaymentTarget n e = e := by
+    dsimp [e]
+    exact orbitPaymentTarget_paymentEndpointSeq n k
+  have hee' : e < e' := by
+    dsimp [e, e']
+    exact paymentEndpointSeq_lt_succ n k
+  omega
+
 /-- The cardinality of a universal payment block is its interval length. -/
 theorem orbitPaymentSourceFiberAt_card_eq_endpoint_sub_start_add_one
     (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-311.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-311.md
new file mode 100644
index 00000000..c7b51c0c
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-311.md
@@ -0,0 +1,67 @@
+# Report: Universal Payment Blocks, cp-311
+
+## Scope
+
+This checkpoint continued `DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock` at finite, exact orbit accounting. No global convergence claim is made.
+
+## Implemented facts
+
+### A. Debt-free universal blocks
+
+For a nonempty universal payment fiber at endpoint `j`, under `floatGrowthDebtFiberAt n j = empty`, Lean now proves:
+
+- each strict interior source has `orbitWindowHeight = 1` and `stateUpperCarry = 1`;
+- `i in carryTwoPaymentClaimFiberAt n j` iff `i = j` and `CarryTwoDebtAt n j`;
+- the complete claim fiber is the endpoint singleton when that carry is two, and is empty otherwise;
+- claim cardinality is at most one and at most endpoint capacity;
+- signed block drift is nonpositive, so the block cannot increase bit width.
+
+The key local contradiction is exact: an interior carry-two event plus the known height-one profile is a delayed debt for this same endpoint.
+
+### B. Equality and strict decay
+
+Under those same assumptions:
+
+```text
+universalPaymentBlockSignedDriftAt n j = 0
+  iff CarryTwoDebtAt n j and orbitWindowHeight n j = 2
+```
+
+All other debt-free universal blocks have negative signed drift and strictly decrease bit width.
+
+### D/E. Canonical endpoint blocks
+
+Added `paymentEndpointSeq`, starting from the target of time zero and then taking the target immediately after each endpoint. Lean proves:
+
+- successive entries are strictly increasing;
+- every entry is an extra-height endpoint fixed by `orbitPaymentTarget`;
+- every entry has a nonempty universal source fiber;
+- the first block starts at zero;
+- block `k + 1` starts at `paymentEndpointSeq n k + 1`.
+
+The last result uses target monotonicity: an earlier source can target at most the old endpoint, but the next endpoint is strictly larger.
+
+## Proven conclusion
+
+Canonical target fibers now have consecutive block starts. Separately, every debt-free block is either width-preserving in its unique endpoint-carry-two/height-two equality case, or strictly width-decreasing. These are local conditional facts; they do not assert that every block is debt-free.
+
+## Remaining frontier
+
+1. Stage C: universal/debt-supported start compatibility and zero-drift prefix.
+2. Stage F/G: endpoint-aligned finite partition and telescoping signed ledger.
+3. Stage H: exact block-depth contribution formulas and pressure sums.
+
+The start formulas added here remove the coordinate mismatch required by the finite telescope.
+
+## Verification
+
+Completed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath
+git diff --check
+```
+
+No `sorry` or axioms were added.
````
`````
