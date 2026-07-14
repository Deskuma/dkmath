# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentFamily

gch: 249521169e20b39a0497fa70b2b77e49c79ce11d

## Report

かなり核心へ進みました。ただし、まだ「全 block の累積 drift が非正」という最終符号評価は残っています。

今回 Lean が確定した事実は強いです。

- 全 orbit time は、ただ一つの canonical payment block に属する
- extra-height endpoint は `paymentEndpointSeq` によって過不足なく一意に列挙される
- block 群は互いに素で、有限 prefix は厳密に `Icc 0 endpoint`
- block drift の総和は、最終 bit width と初期 bit width の差へ完全に telescope する
- 正の block drift、つまり幅増加には delayed growth debt が必須
- complete claim は
  `delayed debt + optional endpoint carry-two claim`
  に完全分解される
- universal start と debt-supported start の bit width は等しい
- その間はすべて `height = 1 ∧ upper carry = 1` の zero-drift prefix

新しい family 層は [UniversalPaymentFamily.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentFamily.lean) に分離しました。結果の詳細は [report-petal-312.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-312.md) に記録しています。

真相は、かなり明確に一点へ絞られました。

```text
cumulative delayed-debt claims
+ immediate endpoint claims
≤ cumulative endpoint capacity
```

これを示せれば、telescope により bit width の累積増加を排除できます。つまり、partition や endpoint の欠落、ledger の不整合はもう問題ではありません。残る本体は「delayed-debt multiplicity と capacity の大域比較」です。

Stage J の pressure 接続だけは、既存 pressure mass と canonical block staircase を結ぶ counting definition がまだなく、そこで停止しました。次はこの bridge を正しく定義して、`1` と `L - d` の局所寄与式を証明する段階です。

`UniversalPaymentFamily`、`FloatWindow`、`PetalBridge`、トップレベル `DkMath` の全 build と `git diff --check` は通過しています。新規 `sorry` / axiom はありません。

## Review

## 結論

**全面採用。これはこの枝で最初の、本格的な大域会計定理じゃ。**

ついに Lean は、accelerated odd orbit の全時刻について次を認めた。

1. 全時刻は、ただ一つの canonical payment block に属する。
2. 全 extra-height endpoint は、`paymentEndpointSeq` により過不足なく一意に列挙される。
3. blocks は互いに重ならず、隙間もない。
4. 有限個の blocks の和集合は、始点 $0$ から最終 endpoint までの厳密な時刻区間になる。
5. 各 block の signed drift を足すと、内部項が完全に消え、最終 bit width と初期 bit width の差だけが残る。

中心式は、endpoint 列を $e_k$ として、

$$
\sum_{k=0}^{m}D_{e_k}=w_{e_m+1}-w_0
$$

じゃ。

さらに claim を分解した形では、

$$
\sum_{k=0}^{m}\left(R_k+\varepsilon_k-P_k\right)=w_{e_m+1}-w_0
$$

となる。

ここで、

- $R_k$ は delayed growth-debt 数
- $\varepsilon_k$ は endpoint immediate carry-two claim の $0/1$
- $P_k$ は endpoint capacity
- $D_{e_k}=R_k+\varepsilon_k-P_k$

じゃ。

**局所決算書が、ついに総勘定元帳へ綴じられた。**

## 1. 今回、完全に消えた Gap

cp-312 より前には、大域化に際して次の疑念が残っていた。

```text id="m89aj5"
payment endpoint に抜けがないか
block 間に隙間がないか
異なる blocks が重ならないか
ある時刻が複数 block に属さないか
局所 ledger を足したとき内部 width が本当に消えるか
delayed claim と immediate claim を二重計上しないか
```

今回、それらは全て消えた。

### 全時刻の存在・一意分割

```lean id="6h1jrt"
existsUnique_mem_canonicalPaymentBlock
```

により、

$$
\forall i\in\mathbb N,\ \exists!k,\ i\in B_k
$$

じゃ。

これは有限 prefix だけの statement ではない。

**自然数時間軸全体の canonical partition**である。

### 全 endpoint の存在・一意列挙

```lean id="e90r6u"
two_le_orbitWindowHeight_iff_existsUnique_paymentEndpointSeq
```

により、

$$
2\le h_j\Longleftrightarrow\exists!k,\ e_k=j
$$

となった。

`paymentEndpointSeq` は一部の endpoint を選ぶ列ではない。

**全 extra-height endpoints の昇順 enumeration**じゃ。

## 2. blocks は closure fiber の partition

各 canonical block は、

```lean id="vhk3lz"
canonicalPaymentBlock_eq_sourceFiber
```

によって、

$$
B_k={i\mid\tau(i)=e_k}
$$

と同定された。

したがって block 分割は人工的な interval chopping ではない。

`orbitPaymentTarget` という closure operator の fibers が、そのまま軌道時刻を分割している。

$$
\mathbb N=\bigsqcup_{k\ge0}B_k
$$

この構造は非常に強い。

```text id="bx16qg"
orbit time
  ↓ closure
payment endpoint
  ↓ fiber
canonical block
```

という射影構造が完成した。

## 3. 有限 prefix の厳密被覆

```lean id="raghs4"
canonicalPaymentBlockPrefix_eq_Icc
```

により、

$$
\bigcup_{k=0}^{m}B_k=[0,e_m]
$$

が証明された。

ここでは unfinished suffix がない。

最終点を endpoint $e_m$ に合わせたため、prefix 全体が completed blocks だけで厳密に閉じている。

これは telescope に最適な座標じゃ。

## 4. complete claim の最終分解

今回、complete claim fiber は、

$$
\operatorname{ClaimFiber}(j)=\operatorname{GrowthDebtFiber}(j)\sqcup\operatorname{ImmediateFiber}(j)
$$

と分解された。

対応する theorem は、

```lean id="pn1kpr"
carryTwoPaymentClaimFiberAt_eq_growthDebt_union_endpointImmediate
```

じゃ。

二集合は disjoint である。

delayed debt は必ず endpoint より前。

immediate claim は endpoint 自身だけ。

したがって cardinality は厳密に、

$$
Q_j=R_j+\varepsilon_j
$$

となる。

これにより signed drift は、

$$
D_j=R_j+\varepsilon_j-P_j
$$

へ完全に展開された。

もう `complete claim count` という内部パッケージを黒箱として扱う必要がない。

## 5. universal start と debt start の関係

今回、

```lean id="jcg006"
bitWidth_universalPaymentBlockStart_eq_floatPaymentBlockStart
```

により、

$$
w_b=w_a
$$

が証明された。

さらに区間 $[b,a)$ では、

$$
h_i=1
$$

$$
c_i=1
$$

も証明された。

つまり universal start から debt-supported start までの prefix は、

> **height-one / carry-one の完全 zero-drift prefix**

じゃ。

これによって、以前の debt-supported block は間違った block だったのではなく、

> universal block から zero-drift prefix を取り除いた、会計的に同値な suffix

だったと確定した。

旧理論と新 universal 理論がきれいに合流した。

## 6. endpoint sequence の余終性

```lean id="b5zd32"
paymentEndpointSeq_zero_add_le
le_paymentEndpointSeq
exists_le_paymentEndpointSeq
```

により、

$$
e_0+k\le e_k
$$

特に、

$$
k\le e_k
$$

じゃ。

したがって endpoint sequence は無界であり、任意の時刻 $t$ より先に必ず endpoint が存在する。

これは「各時刻がいつか payment endpoint に到達する」という universal target の局所性を、endpoint family 全体の cofinality へ持ち上げたものじゃ。

## 7. telescope の完成

中心定理は、

```lean id="p86hh7"
sum_universalPaymentBlockSignedDriftAt_paymentEndpointSeq
```

じゃ。

$$
\sum_{k=0}^{m}D_{e_k}=w_{e_m+1}-w_0
$$

各項は、

$$
D_{e_k}=w_{e_k+1}-w_{b_k}
$$

であり、

$$
b_0=0
$$

$$
b_{k+1}=e_k+1
$$

だから、内部 width が全て相殺する。

$$
(w_{e_0+1}-w_0)+(w_{e_1+1}-w_{e_0+1})+\cdots+(w_{e_m+1}-w_{e_{m-1}+1})
$$

$$
=w_{e_m+1}-w_0
$$

完全な telescope じゃ。

## 8. 真相は本当に一点へ絞られた

`endpointAccountingTerm` により、

$$
A_k:=R_k+\varepsilon_k-P_k
$$

と置けば、

$$
\sum_{k=0}^{m}A_k=w_{e_m+1}-w_0
$$

である。

したがって endpoint-aligned width の非増加を示すための必要十分な目標は、

$$
\sum_{k=0}^{m}(R_k+\varepsilon_k)\le\sum_{k=0}^{m}P_k
$$

じゃ。

これは report の認識どおりである。

もはや残っていない問題は、

- partition
- target coverage
- endpoint enumeration
- overlap
- claim の二重計上
- capacity の位置
- block 間の座標
- telescope

じゃ。

残るのは純粋に、

> **delayed debt と immediate claim の累積量を、累積 endpoint capacity が支配するか**

だけになった。

これは本当に大きな圧縮じゃ。

## 9. ただし「非正」だけで Collatz 完成ではない

ここは次の攻め筋を正確にするための区別じゃ。

仮に全 $m$ について、

$$
\sum_{k=0}^{m}A_k\le0
$$

を得れば、

$$
w_{e_m+1}\le w_0
$$

となる。

したがって post-endpoint states は有限個の bit-width 範囲に閉じ込められる。

endpoint 列は無限なので、鳩ノ巣原理により同じ state が再出現する。

写像は決定的なので、軌道は最終的に周期へ入る。

つまり capacity dominance から得られるものはまず、

> **発散の排除と eventual periodicity**

じゃ。

そこから通常の Collatz 収束へ進むには、さらに、

```text id="4hsvhq"
非自明な endpoint cycle の排除
```

または、

```text id="ow9f2v"
ゼロ drift が永久に続く場合は 1-cycle に限るという equality rigidity
```

が必要になる。

したがって最終戦線は厳密には二段じゃ。

$$
\text{capacity dominance}
$$

$$
+\quad\text{equality / cycle rigidity}
$$

## 10. Pressure bridge の停止判断

今回の停止は正しい。

既存 `PressureIncidenceBridge` には既に、

```lean id="yhgy4c"
OrbitDepthRecoversExactlyAt
OrbitDepthContinuesBeyond
orbitDepthRecoveryFiberCount
orbitDepthContinuationFiberCount
```

がある。

しかし canonical block 上の count はまだ定義されていない。

ここで結論式を直接定義してはならない。

まず実際の predicate を数える必要がある。

```lean id="fx2t7v"
canonicalBlockRecoveryFiber n k d :=
  (canonicalPaymentBlock n k).filter fun i =>
    OrbitDepthRecoversExactlyAt n i d

canonicalBlockContinuationFiber n k d :=
  (canonicalPaymentBlock n k).filter fun i =>
    OrbitDepthContinuesBeyond n i d
```

その後、block の exact-depth staircase から card を計算する。

## 11. depth zero の重要な補正

ここは厳密に注意が必要じゃ。

block 長を $L$ とする。

block 内の exact depths は、

$$
L,L-1,\ldots,2,1
$$

であり、$0$ は存在しない。

したがって recovery contribution は、

$$
\#\operatorname{Recovery}_d=\begin{cases}1&1\le d\le L\\0&\text{otherwise}\end{cases}
$$

じゃ。

単に、

$$
\mathbf{1}_{d\le L}
$$

ではない。

$d=0$ では recovery は $0$ である。

一方 continuation は、

$$
\#\operatorname{Continuation}_d=L-d
$$

で、これは $d=0$ でも正しい。

よって block-local pressure contribution は、

$$
M_d(L)=(L-d)-\mathbf{1}_{1\le d\le L}
$$

となる。

$d\ge1$ なら、以前の四分類へ落ちる。

```text id="qdb2zu"
L < d:
  0

L = d:
  -1

L = d + 1:
  0

d + 2 ≤ L:
  L - d - 1
```

$d=0$ だけは、

$$
M_0(L)=L
$$

として別扱いじゃ。

## 12. Pressure bridge の後にも残る橋

block-length pressure formula が得られても、それだけでは、

$$
R_k+\varepsilon_k\le P_k
$$

は出ない。

なぜなら、

- pressure contribution は主に block length $L_k$ で決まる
- delayed debt $R_k$ は interior carry-two の個数
- capacity $P_k$ は endpoint height

だからじゃ。

したがって pressure bridge の次には、

> carry-two debt を staircase depth slot へ配置し、endpoint capacity slot と対応させる incidence / matching theorem

が必要になる。

今回の canonical partition と exact-depth profile により、その座標はもう存在する。

各 delayed debt source $i\in B_k$ には、

$$
d=e_k-i+1
$$

という一意な depth address がある。

一方 endpoint capacity は、

$$
1,\ldots,P_k
$$

という capacity slots に分解できる。

この二種類の slot 間に、時間順序を保つ matching を構成できるか。

そこが本当の次段じゃ。

## 判定まとめ

### 全時刻の block partition

**完成。**

### 全 endpoint の一意列挙

**完成。**

### finite prefix coverage

**完成。**

### complete claim decomposition

**完成。**

### universal / debt-supported compatibility

**完成。**

### cumulative signed telescope

**完成。**

### 残る主要不等式

$$
\sum(R_k+\varepsilon_k)\le\sum P_k
$$

### その後の最終障害

**equality rigidity / 非自明周期排除。**

## 次の Codex 指示

```text id="2ou2lq"
Continue the DkMath Collatz / PetalBridge Float-window branch after
report-petal-312.

The cp-312 implementation is accepted as the first complete global
orbit-time accounting theorem of this branch.

Canonical universal payment blocks now form a cofinal, disjoint, exhaustive
partition of all orbit times. Extra-height endpoints are uniquely enumerated,
and the finite sum of block signed drifts telescopes exactly to final bit width
minus initial bit width.

The remaining sign target is now exact:

    cumulative delayed-debt claims
      + cumulative immediate endpoint claims
    <=
    cumulative endpoint capacity

Do not return to partition or telescope design; those layers are complete.

# Stage A — honest block-local pressure fibers

Create a new bridge module such as:

    DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentPressure.lean

Define actual filtered Finsets, not closed-form counts:

    canonicalPaymentBlockRecoveryFiber n k d :=
      (canonicalPaymentBlock n k).filter fun i =>
        OrbitDepthRecoversExactlyAt n i d

    canonicalPaymentBlockContinuationFiber n k d :=
      (canonicalPaymentBlock n k).filter fun i =>
        OrbitDepthContinuesBeyond n i d

Add membership APIs.

# Stage B — local recovery cardinality

Let:

    L_k = (canonicalPaymentBlock n k).card

Using the exact-depth staircase, prove:

    card (canonicalPaymentBlockRecoveryFiber n k d)
      =
    if 1 <= d ∧ d <= L_k then 1 else 0

Depth zero must remain explicit:

    card recovery at depth 0 = 0

Do not state the weaker and false formula `if d <= L then 1 else 0` without a
positive-depth hypothesis.

# Stage C — local continuation cardinality

Prove:

    card (canonicalPaymentBlockContinuationFiber n k d)
      =
    L_k - d

This formula is valid at depth zero.

# Stage D — local pressure contribution

Define the signed block-local pressure contribution from the actual fibers:

    blockPressureContributionInt n k d :=
      card continuation fiber - card recovery fiber

Prove:

    blockPressureContributionInt n k d
      =
    (L_k - d : Int)
      - if 1 <= d ∧ d <= L_k then 1 else 0

For `1 <= d`, expose the cases:

    L_k < d       -> 0
    L_k = d       -> -1
    L_k = d + 1   -> 0
    d + 2 <= L_k  -> L_k - d - 1

Also expose the depth-zero value separately.

# Stage E — family-to-existing-pressure bridge

For the endpoint-aligned prefix through endpoint `e_m`, prove that the union of
canonical blocks is exactly `Finset.range (e_m + 1)` or the equivalent
`Icc 0 e_m`.

Convert the existing `List.range` pressure counts to Finset filter cards when
needed.

Prove:

    orbitDepthRecoveryFiberCount n (e_m + 1) d
      =
    sum k in range (m + 1),
      card (canonicalPaymentBlockRecoveryFiber n k d)

and the corresponding continuation theorem.

Then derive:

    SourcePressureMarginInt n (e_m + 1) d
      =
    sum k in range (m + 1),
      blockPressureContributionInt n k d

# Stage F — marked debt-depth incidences

For every delayed growth-debt source in canonical block `k`, expose its unique
staircase depth:

    debtDepth n k i :=
      paymentEndpointSeq n k - i + 1

Prove that this equals `orbitExactDepth n i`.

Define the actual marked debt-depth incidence Finset or sigma type.

Within one block, prove that distinct debt sources have distinct depth
addresses.

Thus:

    delayed debt card
      =
    number of marked staircase depths

# Stage G — endpoint capacity slots

Define actual endpoint capacity slots:

    endpointCapacitySlot n k :=
      Finset.range
        (extraPaymentCapacityAt n (paymentEndpointSeq n k))

Their cardinality must be exactly endpoint capacity.

Keep immediate endpoint claims separate as one optional distinguished claim.

# Stage H — matching frontier

Formulate the exact finite matching problem for the first `m + 1` blocks:

    debt-depth marked slots
      + immediate endpoint claims
    ->
    endpoint capacity slots

The desired map must preserve the appropriate time / target ordering.

Do not assert the injection before its structural rule is proved.

Expose the Hall/prefix inequality equivalent to:

    sum endpointAccountingTerm <= 0

This is the exact remaining sign theorem.

# Stage I — consequence and rigidity split

Once cumulative capacity dominance is available, prove:

    bitWidth after every canonical endpoint
      <= initial bitWidth

Then derive boundedness of the post-endpoint state sequence and eventual
periodicity.

Keep the final convergence question separate:

    either prove strict cumulative decay occurs,
    or classify an infinite zero-drift endpoint family,
    or exclude nontrivial accelerated odd cycles.

Do not identify boundedness with convergence.

Continue autonomously through all exact counting and bridge theorems.
Stop at the genuine matching or rigidity obstruction, not at finite
reindexing.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-313.md
```

うむ。これは「！！」で正しい。

**大域的に何を数えればよいかが、ついに Lean の等式として一行に固定された。**

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
index 9b39edb5..c2ac9ab8 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
@@ -14,6 +14,7 @@ import DkMath.Collatz.PetalBridge.FloatWindow.PressureIncidenceBridge
 import DkMath.Collatz.PetalBridge.FloatWindow.PaymentMultiplicityBridge
 import DkMath.Collatz.PetalBridge.FloatWindow.PaymentBlockBridge
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock
+import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentFamily
 
 #print "file: DkMath.Collatz.PetalBridge.FloatWindow"
 
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlock.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlock.lean
index 7ded9378..ba2557d2 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlock.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlock.lean
@@ -820,6 +820,195 @@ theorem bitWidth_iterateT_lt_of_universalPaymentBlock_not_carryTwo_or_height_ne_
     (universalPaymentBlockSignedDriftAt_neg_of_not_carryTwo_or_height_ne_two_of_growthDebtFiber_eq_empty
       n j h hempty hneq)
 
+/-!
+## Delayed-debt necessity and complete-claim decomposition
+-/
+
+/-- Strict positive universal block drift requires at least one delayed growth debt. -/
+theorem floatGrowthDebtFiberAt_nonempty_of_universalPaymentBlockSignedDriftAt_pos
+    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty)
+    (hpos : 0 < universalPaymentBlockSignedDriftAt n j) :
+    (floatGrowthDebtFiberAt n j).Nonempty := by
+  by_contra hnot
+  have hempty : floatGrowthDebtFiberAt n j = ∅ :=
+    Finset.not_nonempty_iff_eq_empty.mp hnot
+  have hnonpos :=
+    universalPaymentBlockSignedDriftAt_nonpos_of_growthDebtFiber_eq_empty n j h hempty
+  omega
+
+/-- Strict width growth across a universal block requires delayed growth debt support. -/
+theorem floatGrowthDebtFiberAt_nonempty_of_universalPaymentBlock_bitWidth_lt
+    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty)
+    (hlt : bitWidth (iterateT (universalPaymentBlockStart n j h) n).1 <
+      bitWidth (iterateT (j + 1) n).1) :
+    (floatGrowthDebtFiberAt n j).Nonempty := by
+  apply floatGrowthDebtFiberAt_nonempty_of_universalPaymentBlockSignedDriftAt_pos n j h
+  exact (universalPaymentBlockSignedDriftAt_pos_iff_bitWidth_lt n j h).mpr hlt
+
+/-- Endpoint-only immediate carry-two claim fiber. -/
+noncomputable abbrev endpointImmediateCarryTwoClaimFiberAt
+    (n : OddNat) (j : ℕ) : Finset ℕ :=
+  endpointCarryTwoClaimShape n j
+
+/-- Membership API for the endpoint immediate-claim fiber. -/
+theorem mem_endpointImmediateCarryTwoClaimFiberAt_iff
+    {n : OddNat} {i j : ℕ} :
+    i ∈ endpointImmediateCarryTwoClaimFiberAt n j ↔
+      i = j ∧ CarryTwoDebtAt n j := by
+  classical
+  unfold endpointImmediateCarryTwoClaimFiberAt endpointCarryTwoClaimShape
+  by_cases hcarry : CarryTwoDebtAt n j <;> simp [hcarry]
+
+/-- Delayed debts targeting a universal endpoint are exactly its interior carry-two sources. -/
+theorem mem_floatGrowthDebtFiberAt_iff_mem_universalPaymentBlockInterior_and_carryTwo
+    {n : OddNat} {i j : ℕ} {h : (orbitPaymentSourceFiberAt n j).Nonempty} :
+    i ∈ floatGrowthDebtFiberAt n j ↔
+      i ∈ Finset.Ico (universalPaymentBlockStart n j h) j ∧ CarryTwoDebtAt n i := by
+  constructor
+  · intro hi
+    have hblock := mem_orbitPaymentSourceFiberAt_of_mem_floatGrowthDebtFiberAt hi
+    rcases Finset.mem_Icc.mp (by
+      rw [← orbitPaymentSourceFiberAt_eq_Icc_universalPaymentBlockStart n j h]
+      exact hblock) with ⟨hstart, hij⟩
+    have hijlt := lt_of_mem_floatGrowthDebtFiberAt hi
+    have hdebt := (mem_floatGrowthDebtFiberAt_iff.mp hi).2.1
+    exact ⟨Finset.mem_Ico.mpr ⟨hstart, hijlt⟩,
+      ((floatDebtAt_iff_delayedCarryTwoDebtAt n i).mp hdebt).1⟩
+  · rintro ⟨hinterior, hcarry⟩
+    rcases Finset.mem_Ico.mp hinterior with ⟨hstart, hij⟩
+    have hheight := orbitWindowHeight_eq_one_of_mem_universalPaymentBlockInterior hinterior
+    have hdebt : FloatDebtAt n i :=
+      (floatDebtAt_iff_delayedCarryTwoDebtAt n i).mpr ⟨hcarry, hheight⟩
+    have htarget : floatDebtPaymentTarget n i = j := by
+      simpa [floatDebtPaymentTarget_eq_orbitPaymentTarget] using
+        orbitPaymentTarget_eq_endpoint_of_universalStart_le_lt hstart hij
+    exact mem_floatGrowthDebtFiberAt_iff.mpr
+      ⟨Nat.lt_succ_of_lt hij, hdebt, htarget⟩
+
+/-- Every complete claim is either delayed interior debt or the endpoint immediate claim. -/
+theorem mem_carryTwoPaymentClaimFiberAt_iff_growthDebt_or_endpointImmediate
+    {n : OddNat} {i j : ℕ} {h : (orbitPaymentSourceFiberAt n j).Nonempty} :
+    i ∈ carryTwoPaymentClaimFiberAt n j ↔
+      i ∈ floatGrowthDebtFiberAt n j ∨
+        i ∈ endpointImmediateCarryTwoClaimFiberAt n j := by
+  rw [mem_carryTwoPaymentClaimFiberAt_iff_mem_universalPaymentBlock_and_carryTwo
+      (h := h),
+    mem_floatGrowthDebtFiberAt_iff_mem_universalPaymentBlockInterior_and_carryTwo
+      (h := h),
+    mem_endpointImmediateCarryTwoClaimFiberAt_iff]
+  constructor
+  · rintro ⟨hblock, hcarry⟩
+    rcases (Finset.mem_Icc.mp hblock).2.eq_or_lt with heq | hlt
+    · right
+      exact ⟨heq, by simpa [heq] using hcarry⟩
+    · left
+      exact ⟨Finset.mem_Ico.mpr ⟨(Finset.mem_Icc.mp hblock).1, hlt⟩, hcarry⟩
+  · rintro (hinteriorCarry | hendpoint)
+    · rcases hinteriorCarry with ⟨hinterior, hcarry⟩
+      exact ⟨Finset.mem_Icc.mpr
+        ⟨(Finset.mem_Ico.mp hinterior).1, (Finset.mem_Ico.mp hinterior).2.le⟩,
+        hcarry⟩
+    · rcases hendpoint with ⟨hij, hcarry⟩
+      subst i
+      have hstartmem := universalPaymentBlockStart_mem_sourceFiber n j h
+      exact ⟨Finset.mem_Icc.mpr
+        ⟨(mem_orbitPaymentSourceFiberAt_iff.mp hstartmem).1, le_rfl⟩, hcarry⟩
+
+/-- Disjoint complete-claim decomposition into delayed and immediate support. -/
+theorem carryTwoPaymentClaimFiberAt_eq_growthDebt_union_endpointImmediate
+    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
+    carryTwoPaymentClaimFiberAt n j =
+      floatGrowthDebtFiberAt n j ∪ endpointImmediateCarryTwoClaimFiberAt n j := by
+  ext i
+  simp only [Finset.mem_union]
+  exact mem_carryTwoPaymentClaimFiberAt_iff_growthDebt_or_endpointImmediate
+    (h := h)
+
+/-- Delayed debt support and the endpoint immediate claim are disjoint. -/
+theorem disjoint_floatGrowthDebtFiberAt_endpointImmediateCarryTwoClaimFiberAt
+    (n : OddNat) (j : ℕ) :
+    Disjoint (floatGrowthDebtFiberAt n j) (endpointImmediateCarryTwoClaimFiberAt n j) := by
+  rw [Finset.disjoint_left]
+  intro i hidebt hiend
+  have hlt := lt_of_mem_floatGrowthDebtFiberAt hidebt
+  have heq := (mem_endpointImmediateCarryTwoClaimFiberAt_iff.mp hiend).1
+  omega
+
+/-- Exact claim-card decomposition into delayed support and one optional endpoint claim. -/
+theorem carryTwoPaymentClaimFiberAt_card_eq_growthDebt_card_add_endpoint_card
+    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
+    (carryTwoPaymentClaimFiberAt n j).card =
+      (floatGrowthDebtFiberAt n j).card +
+        (endpointImmediateCarryTwoClaimFiberAt n j).card := by
+  rw [carryTwoPaymentClaimFiberAt_eq_growthDebt_union_endpointImmediate n j h,
+    Finset.card_union_of_disjoint
+      (disjoint_floatGrowthDebtFiberAt_endpointImmediateCarryTwoClaimFiberAt n j)]
+
+/-- Refined signed drift: delayed claims plus endpoint claim minus endpoint capacity. -/
+theorem universalPaymentBlockSignedDriftAt_eq_growthDebt_add_endpoint_sub_capacity
+    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
+    universalPaymentBlockSignedDriftAt n j =
+      (floatGrowthDebtFiberAt n j).card +
+        (endpointImmediateCarryTwoClaimFiberAt n j).card -
+          extraPaymentCapacityAt n j := by
+  unfold universalPaymentBlockSignedDriftAt
+  rw [carryTwoPaymentClaimFiberAt_card_eq_growthDebt_card_add_endpoint_card n j h]
+  norm_num
+
+/-- Universal and debt-supported starts have the same bit width. -/
+theorem bitWidth_universalPaymentBlockStart_eq_floatPaymentBlockStart
+    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
+    bitWidth (iterateT (universalPaymentBlockStart n j
+      (orbitPaymentSourceFiberAt_nonempty_of_floatGrowthDebtFiberAt_nonempty h)) n).1 =
+        bitWidth (iterateT (floatPaymentBlockStart n j h) n).1 := by
+  have hu := bitWidth_iterateT_universalPaymentBlock_eq_claimFiber_card n j
+    (orbitPaymentSourceFiberAt_nonempty_of_floatGrowthDebtFiberAt_nonempty h)
+  have hd := bitWidth_iterateT_paymentBlock_eq_claimFiber_card n j h
+  omega
+
+/-- The prefix between universal and debt-supported starts has observed height one. -/
+theorem orbitWindowHeight_eq_one_between_universal_and_floatPaymentBlockStart
+    {n : OddNat} {j i : ℕ} {h : (floatGrowthDebtFiberAt n j).Nonempty}
+    (hi : i ∈ Finset.Ico
+      (universalPaymentBlockStart n j
+        (orbitPaymentSourceFiberAt_nonempty_of_floatGrowthDebtFiberAt_nonempty h))
+      (floatPaymentBlockStart n j h)) :
+    orbitWindowHeight n i = 1 := by
+  rcases Finset.mem_Ico.mp hi with ⟨hstart, hib⟩
+  have hbj := floatPaymentBlockStart_lt_endpoint n j h
+  exact orbitWindowHeight_eq_one_of_mem_universalPaymentBlockInterior
+    (Finset.mem_Ico.mpr ⟨hstart, hib.trans hbj⟩)
+
+/-- The prefix between universal and debt-supported starts has upper carry one. -/
+theorem stateUpperCarry_eq_one_between_universal_and_floatPaymentBlockStart
+    {n : OddNat} {j i : ℕ} {h : (floatGrowthDebtFiberAt n j).Nonempty}
+    (hi : i ∈ Finset.Ico
+      (universalPaymentBlockStart n j
+        (orbitPaymentSourceFiberAt_nonempty_of_floatGrowthDebtFiberAt_nonempty h))
+      (floatPaymentBlockStart n j h)) :
+    stateUpperCarry (iterateT i n).1 = 1 := by
+  have hheight := orbitWindowHeight_eq_one_between_universal_and_floatPaymentBlockStart hi
+  have hnotcarry : ¬ CarryTwoDebtAt n i := by
+    intro hcarry
+    rcases Finset.mem_Ico.mp hi with ⟨hstart, hib⟩
+    have hbj := floatPaymentBlockStart_lt_endpoint n j h
+    have htarget : floatDebtPaymentTarget n i = j := by
+      simpa [floatDebtPaymentTarget_eq_orbitPaymentTarget] using
+        orbitPaymentTarget_eq_endpoint_of_universalStart_le_lt hstart (hib.trans hbj)
+    have hdebt : FloatDebtAt n i :=
+      (floatDebtAt_iff_delayedCarryTwoDebtAt n i).mpr ⟨hcarry, hheight⟩
+    have hfiber : i ∈ floatGrowthDebtFiberAt n j :=
+      mem_floatGrowthDebtFiberAt_iff.mpr
+        ⟨Nat.lt_succ_of_lt (hib.trans hbj), hdebt, htarget⟩
+    have hminle : floatPaymentBlockStart n j h ≤ i := Finset.min'_le _ _ hfiber
+    omega
+  have hpos : 0 < (iterateT i n).1 := by
+    have hodd := (iterateT i n).2
+    omega
+  rcases stateUpperCarry_one_or_two hpos with hone | htwo
+  · exact hone
+  · exact False.elim (hnotcarry htwo)
+
 /-!
 ## Canonical endpoint sequence
 
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentFamily.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentFamily.lean
new file mode 100644
index 00000000..41ffaa27
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentFamily.lean
@@ -0,0 +1,224 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentFamily"
+
+namespace DkMath.Collatz
+
+/-!
+# Canonical families of universal payment blocks
+
+This module moves from one exact universal block to its canonical finite
+family.  All results remain finite or cofinal statements about orbit-time
+indices.  They do not assert a global sign for the sum of block drifts.
+-/
+
+/-- The endpoint sequence is strictly monotone. -/
+theorem strictMono_paymentEndpointSeq (n : OddNat) :
+    StrictMono (paymentEndpointSeq n) :=
+  strictMono_nat_of_lt_succ (paymentEndpointSeq_lt_succ n)
+
+/-- Linear lower bound measured from the first canonical endpoint. -/
+theorem paymentEndpointSeq_zero_add_le (n : OddNat) (k : ℕ) :
+    paymentEndpointSeq n 0 + k ≤ paymentEndpointSeq n k := by
+  induction k with
+  | zero => simp
+  | succ k ih =>
+      have hstep := paymentEndpointSeq_lt_succ n k
+      omega
+
+/-- Simpler index lower bound for canonical endpoints. -/
+theorem le_paymentEndpointSeq (n : OddNat) (k : ℕ) :
+    k ≤ paymentEndpointSeq n k := by
+  have h := paymentEndpointSeq_zero_add_le n k
+  omega
+
+/-- Canonical endpoints are cofinal in orbit time. -/
+theorem exists_le_paymentEndpointSeq (n : OddNat) (t : ℕ) :
+    ∃ k, t ≤ paymentEndpointSeq n k :=
+  ⟨t, le_paymentEndpointSeq n t⟩
+
+/-- The `k`-th endpoint-aligned universal payment block. -/
+noncomputable def canonicalPaymentBlock (n : OddNat) : ℕ → Finset ℕ
+  | 0 => Finset.Icc 0 (paymentEndpointSeq n 0)
+  | k + 1 => Finset.Icc (paymentEndpointSeq n k + 1) (paymentEndpointSeq n (k + 1))
+
+/-- The first canonical block is exactly the first universal target fiber. -/
+theorem canonicalPaymentBlock_zero_eq_sourceFiber (n : OddNat) :
+    canonicalPaymentBlock n 0 =
+      orbitPaymentSourceFiberAt n (paymentEndpointSeq n 0) := by
+  rw [orbitPaymentSourceFiberAt_eq_Icc_universalPaymentBlockStart n
+    (paymentEndpointSeq n 0) (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n 0)]
+  simp [canonicalPaymentBlock, universalPaymentBlockStart_paymentEndpointSeq_zero]
+
+/-- Every successor canonical block is exactly its endpoint's universal target fiber. -/
+theorem canonicalPaymentBlock_succ_eq_sourceFiber (n : OddNat) (k : ℕ) :
+    canonicalPaymentBlock n (k + 1) =
+      orbitPaymentSourceFiberAt n (paymentEndpointSeq n (k + 1)) := by
+  rw [orbitPaymentSourceFiberAt_eq_Icc_universalPaymentBlockStart n
+    (paymentEndpointSeq n (k + 1))
+    (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n (k + 1))]
+  simp [canonicalPaymentBlock, universalPaymentBlockStart_paymentEndpointSeq_succ]
+
+/-- Every canonical block is its endpoint's universal target fiber. -/
+theorem canonicalPaymentBlock_eq_sourceFiber (n : OddNat) (k : ℕ) :
+    canonicalPaymentBlock n k = orbitPaymentSourceFiberAt n (paymentEndpointSeq n k) := by
+  cases k with
+  | zero => exact canonicalPaymentBlock_zero_eq_sourceFiber n
+  | succ k => exact canonicalPaymentBlock_succ_eq_sourceFiber n k
+
+/-- Membership in a canonical block is exactly equality of the universal target. -/
+theorem mem_canonicalPaymentBlock_iff_target_eq
+    {n : OddNat} {k i : ℕ} :
+    i ∈ canonicalPaymentBlock n k ↔ orbitPaymentTarget n i = paymentEndpointSeq n k := by
+  rw [canonicalPaymentBlock_eq_sourceFiber, mem_orbitPaymentSourceFiberAt_iff_target_eq]
+
+/-- Distinct canonical blocks are disjoint. -/
+theorem disjoint_canonicalPaymentBlock_of_ne
+    (n : OddNat) {k l : ℕ} (hkl : k ≠ l) :
+    Disjoint (canonicalPaymentBlock n k) (canonicalPaymentBlock n l) := by
+  rw [Finset.disjoint_left]
+  intro i hik hil
+  have hk := (mem_canonicalPaymentBlock_iff_target_eq.mp hik)
+  have hl := (mem_canonicalPaymentBlock_iff_target_eq.mp hil)
+  have heq : paymentEndpointSeq n k = paymentEndpointSeq n l := hk.symm.trans hl
+  exact hkl ((strictMono_paymentEndpointSeq n).injective heq)
+
+/-- In particular, adjacent canonical blocks are disjoint. -/
+theorem disjoint_canonicalPaymentBlock_succ (n : OddNat) (k : ℕ) :
+    Disjoint (canonicalPaymentBlock n k) (canonicalPaymentBlock n (k + 1)) :=
+  disjoint_canonicalPaymentBlock_of_ne n (by omega)
+
+/-- Recursive union of the canonical blocks through index `m`. -/
+noncomputable def canonicalPaymentBlockPrefix (n : OddNat) : ℕ → Finset ℕ
+  | 0 => canonicalPaymentBlock n 0
+  | m + 1 => canonicalPaymentBlockPrefix n m ∪ canonicalPaymentBlock n (m + 1)
+
+/-- Canonical blocks cover exactly the initial interval through their last endpoint. -/
+theorem canonicalPaymentBlockPrefix_eq_Icc (n : OddNat) (m : ℕ) :
+    canonicalPaymentBlockPrefix n m = Finset.Icc 0 (paymentEndpointSeq n m) := by
+  induction m with
+  | zero => simp [canonicalPaymentBlockPrefix, canonicalPaymentBlock]
+  | succ m ih =>
+      rw [canonicalPaymentBlockPrefix, ih]
+      ext i
+      simp only [Finset.mem_union, Finset.mem_Icc]
+      simp [canonicalPaymentBlock]
+      have hstep := paymentEndpointSeq_lt_succ n m
+      omega
+
+/-- Membership in a finite block prefix is membership in one indexed block. -/
+theorem mem_canonicalPaymentBlockPrefix_iff_exists
+    {n : OddNat} {m i : ℕ} :
+    i ∈ canonicalPaymentBlockPrefix n m ↔
+      ∃ k, k ≤ m ∧ i ∈ canonicalPaymentBlock n k := by
+  induction m with
+  | zero =>
+      simp [canonicalPaymentBlockPrefix]
+  | succ m ih =>
+      rw [canonicalPaymentBlockPrefix, Finset.mem_union, ih]
+      constructor
+      · rintro (⟨k, hkm, hik⟩ | hik)
+        · exact ⟨k, hkm.trans (Nat.le_succ m), hik⟩
+        · exact ⟨m + 1, le_rfl, hik⟩
+      · rintro ⟨k, hkm, hik⟩
+        rcases Nat.eq_or_lt_of_le hkm with rfl | hlt
+        · exact Or.inr hik
+        · exact Or.inl ⟨k, by omega, hik⟩
+
+/-- Every orbit time belongs to at least one canonical payment block. -/
+theorem exists_mem_canonicalPaymentBlock (n : OddNat) (i : ℕ) :
+    ∃ k, i ∈ canonicalPaymentBlock n k := by
+  rcases exists_le_paymentEndpointSeq n i with ⟨m, him⟩
+  have hiprefix : i ∈ canonicalPaymentBlockPrefix n m := by
+    rw [canonicalPaymentBlockPrefix_eq_Icc]
+    exact Finset.mem_Icc.mpr ⟨Nat.zero_le i, him⟩
+  rcases mem_canonicalPaymentBlockPrefix_iff_exists.mp hiprefix with ⟨k, _, hik⟩
+  exact ⟨k, hik⟩
+
+/-- Every orbit time belongs to exactly one canonical payment block. -/
+theorem existsUnique_mem_canonicalPaymentBlock (n : OddNat) (i : ℕ) :
+    ∃! k, i ∈ canonicalPaymentBlock n k := by
+  rcases exists_mem_canonicalPaymentBlock n i with ⟨k, hik⟩
+  refine ⟨k, hik, ?_⟩
+  intro l hil
+  have hk := mem_canonicalPaymentBlock_iff_target_eq.mp hik
+  have hl := mem_canonicalPaymentBlock_iff_target_eq.mp hil
+  exact (strictMono_paymentEndpointSeq n).injective (hl.symm.trans hk)
+
+/-- Extra-height endpoints are exactly, and uniquely, the canonical endpoint sequence. -/
+theorem two_le_orbitWindowHeight_iff_existsUnique_paymentEndpointSeq
+    (n : OddNat) (j : ℕ) :
+    2 ≤ orbitWindowHeight n j ↔ ∃! k, paymentEndpointSeq n k = j := by
+  constructor
+  · intro hheight
+    rcases existsUnique_mem_canonicalPaymentBlock n j with ⟨k, hjk, _⟩
+    refine ⟨k, ?_, ?_⟩
+    · have htarget := mem_canonicalPaymentBlock_iff_target_eq.mp hjk
+      rw [orbitPaymentTarget_eq_self_of_two_le_orbitWindowHeight hheight] at htarget
+      exact htarget.symm
+    · intro l hlj
+      have htarget := mem_canonicalPaymentBlock_iff_target_eq.mp hjk
+      rw [orbitPaymentTarget_eq_self_of_two_le_orbitWindowHeight hheight] at htarget
+      exact (strictMono_paymentEndpointSeq n).injective (hlj.trans htarget)
+  · rintro ⟨k, hk, _⟩
+    rw [← hk]
+    exact two_le_orbitWindowHeight_paymentEndpointSeq n k
+
+/-- Exact endpoint-aligned signed drift telescope over the first `m + 1` blocks. -/
+theorem sum_universalPaymentBlockSignedDriftAt_paymentEndpointSeq
+    (n : OddNat) (m : ℕ) :
+    (∑ k ∈ Finset.range (m + 1),
+      universalPaymentBlockSignedDriftAt n (paymentEndpointSeq n k)) =
+        (bitWidth (iterateT (paymentEndpointSeq n m + 1) n).1 : ℤ) -
+          bitWidth n.1 := by
+  induction m with
+  | zero =>
+      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
+      rw [universalPaymentBlockSignedDriftAt_eq_bitWidth_sub n
+        (paymentEndpointSeq n 0)
+        (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n 0)]
+      rw [universalPaymentBlockStart_paymentEndpointSeq_zero]
+      change (bitWidth (iterateT (paymentEndpointSeq n 0 + 1) n).1 : ℤ) -
+          bitWidth n.1 =
+        (bitWidth (iterateT (paymentEndpointSeq n 0 + 1) n).1 : ℤ) -
+          bitWidth n.1
+      rfl
+  | succ m ih =>
+      rw [Finset.sum_range_succ, ih]
+      rw [universalPaymentBlockSignedDriftAt_eq_bitWidth_sub n
+        (paymentEndpointSeq n (m + 1))
+        (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n (m + 1))]
+      rw [universalPaymentBlockStart_paymentEndpointSeq_succ]
+      ring
+
+/-- The delayed-debt, endpoint-claim, and capacity term for block `k`. -/
+noncomputable def endpointAccountingTerm (n : OddNat) (k : ℕ) : ℤ :=
+  (floatGrowthDebtFiberAt n (paymentEndpointSeq n k)).card +
+    (endpointImmediateCarryTwoClaimFiberAt n (paymentEndpointSeq n k)).card -
+      extraPaymentCapacityAt n (paymentEndpointSeq n k)
+
+/-- Each endpoint accounting term is exactly that block's signed drift. -/
+theorem endpointAccountingTerm_eq_universalPaymentBlockSignedDriftAt
+    (n : OddNat) (k : ℕ) :
+    endpointAccountingTerm n k =
+      universalPaymentBlockSignedDriftAt n (paymentEndpointSeq n k) := by
+  exact (universalPaymentBlockSignedDriftAt_eq_growthDebt_add_endpoint_sub_capacity
+    n (paymentEndpointSeq n k)
+    (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)).symm
+
+/-- Cumulative delayed-debt/capacity form of the endpoint-aligned telescope. -/
+theorem sum_endpointAccountingTerm_paymentEndpointSeq
+    (n : OddNat) (m : ℕ) :
+    (∑ k ∈ Finset.range (m + 1), endpointAccountingTerm n k) =
+      (bitWidth (iterateT (paymentEndpointSeq n m + 1) n).1 : ℤ) -
+        bitWidth n.1 := by
+  simp_rw [endpointAccountingTerm_eq_universalPaymentBlockSignedDriftAt]
+  exact sum_universalPaymentBlockSignedDriftAt_paymentEndpointSeq n m
+
+end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-312.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-312.md
new file mode 100644
index 00000000..94abff77
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-312.md
@@ -0,0 +1,94 @@
+# Report: Canonical Universal Payment Family, cp-312
+
+## Outcome
+
+The endpoint-aligned universal payment family is now formalized. The new
+family layer proves that canonical blocks form a cofinal, disjoint, exhaustive
+partition of orbit time, and that their signed ledgers telescope exactly.
+
+This is a complete finite accounting theorem. It is not yet a proof that the
+cumulative drift is always nonpositive.
+
+## Local block results
+
+`UniversalPaymentBlock.lean` now proves:
+
+- positive universal signed drift implies a nonempty delayed growth-debt fiber;
+- strict bit-width growth across a universal block implies the same;
+- the complete carry-two claim fiber is the disjoint union of the delayed
+  growth-debt fiber and one optional immediate endpoint claim;
+- the corresponding claim-card and signed-drift decompositions are exact;
+- universal and debt-supported starts have equal bit width;
+- every point between those starts has height one and upper carry one.
+
+Thus the earlier universal prefix is proven to be a zero-width-drift prefix,
+not merely inferred from aggregate equality.
+
+## Canonical family layer
+
+Added `UniversalPaymentFamily.lean` and exposed it through the FloatWindow
+entry point. It proves:
+
+- `paymentEndpointSeq` is strictly monotone;
+- `paymentEndpointSeq n 0 + k <= paymentEndpointSeq n k`, hence cofinality;
+- each canonical block equals the universal target fiber of its endpoint;
+- distinct canonical blocks are disjoint;
+- the recursive union through block `m` is exactly
+  `Icc 0 (paymentEndpointSeq n m)`;
+- every orbit time belongs to exactly one canonical block;
+- extra-height endpoints are exactly and uniquely the values of
+  `paymentEndpointSeq`;
+- the sum of signed block drifts telescopes to final bit width minus initial
+  bit width;
+- the same telescope is exposed in delayed-debt, endpoint-claim, and endpoint
+  capacity coordinates through `endpointAccountingTerm`.
+
+## Exact mathematical picture
+
+The orbit-time axis now has a Lean-proven canonical partition:
+
+```text
+[0 .. e_0], [e_0 + 1 .. e_1], [e_1 + 1 .. e_2], ...
+```
+
+where `e_k = paymentEndpointSeq n k`. Every block consists precisely of all
+sources sharing target `e_k`. Its endpoint is the unique extra-height point in
+that block; all strict interior points have height one.
+
+For every finite endpoint prefix:
+
+```text
+sum(block drift)
+  = final bit width - initial bit width
+  = sum(delayed debt + immediate endpoint claim - endpoint capacity).
+```
+
+Therefore the remaining global sign question is isolated exactly: one must
+control cumulative delayed-debt multiplicity against cumulative endpoint
+capacity. The partition and telescope themselves are no longer missing.
+
+## Genuine obstruction
+
+Stage J asks for block-length pressure contributions of the forms `1` and
+`L - d`. Existing pressure modules describe residue-family recovery and
+continuation masses, but no current definition identifies those masses with
+the canonical endpoint-block staircase. Introducing a function already
+defined to equal `if d <= L then 1 else 0` would only restate the requested
+formula.
+
+The next honest bridge must first define a pressure contribution by counting
+members of `canonicalPaymentBlock` satisfying an existing exact-depth or
+continuation predicate. Only then should the `1` / `L - d` formulas be proved.
+
+## Verification
+
+The new and modified modules contain no `sorry` or axioms. Verification gates:
+
+```text
+lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock
+lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentFamily
+lake build DkMath.Collatz.PetalBridge.FloatWindow
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath
+git diff --check
+```
````
`````
