# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock

gch: a62a6fb3682fcfbc96a0ad3d245b2e3e0d928caf

## Report

実装しました。

追加内容:

- generic shifted ledger を前方へ移し、block ledger が直接再利用する形に整理。
- signed block drift を追加。claim card と capacity の差を `ℤ` で保持し、width drift と一致。
- `height = 1 ↔ exact depth ≥ 2`、`height ≥ 2 ↔ exact depth = 1` を証明。
- 新規 [UniversalPaymentBlock.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlock.lean) を追加。
  - 全 orbit time の `orbitPaymentTarget`
  - universal source fiber と最小 source
  - target の extra-height 性
  - debt-supported fiber から universal fiber への包含
  - universal start ≤ debt-block start

確定した事実は、canonical block の signed claim-capacity 差が正確に bit width の signed drift であることです。また universal target はすべて実際の extra-height slot を指します。

一方、universal fiber が開始点から endpoint までの連続区間になる主張は、逆向き exact-depth staircase closure が未証明のため追加していません。必要な補題をソースコメントと [report-petal-305.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-305.md) に明記しました。

検証済み:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.PaymentBlockBridge
lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
lake build DkMath
git diff --check
```

変更した Lean ファイルに `sorry` / `axiom` はありません。

## Review

## 結論

**実装は採用。だが「現在の境界」の判定は修正が必要じゃ。**

cp-305 で追加された次の成果は、いずれも有効である。

- signed payment-block drift
- height と exact all-ones depth の完全対応
- 全軌道時刻に対する `orbitPaymentTarget`
- universal source fiber
- universal start と debt-supported start の順序関係

とくに、

```lean
paymentBlockSignedDrift_eq_bitWidth_sub
```

によって、block の claim-capacity 差が、正確に signed bit-width drift へ一致した。

また、

```lean
two_le_orbitWindowHeight_orbitPaymentTarget
```

によって、全ての軌道時刻が有限未来の genuine extra-height slot を指すことまで確定した。

build、`git diff --check`、no-`sorry` / no-`axiom` も報告上すべて成功している。

ただし report の、

```text
universal fiber の区間連続性には
逆向き exact-depth staircase closure が新たに必要
```

という判断は誤りじゃ。

**既存の `orbitDepthRecoversExactlyAt_prePayment_chain` だけで、区間連続性は既に証明可能である。**

新しい逆向き staircase theorem は要らない。

---

## 1. generic shifted ledger の再配置

```lean
bitWidth_iterateT_add_shiftedExtraPaymentCapacity_eq_shiftedCarryTwo
```

を specialized block theorem より前へ移したのは良い。

これにより、

```lean
bitWidth_iterateT_paymentBlock_eq_claimFiber_card
```

が generic theorem を直接再利用するようになった。

cp-304 で残った局所的な重複が解消され、依存構造は次の順に整理された。

```text
generic shifted ledger
  ↓
finite offset transport
  ↓
canonical block specialization
  ↓
signed block drift
```

これは採用。

---

## 2. signed block drift

新しい定義は、

```lean
paymentBlockSignedDrift
```

じゃ。

数学的には、

$$
D_j=Q_j-P_j
$$

ここで、

$$
Q_j=\#\operatorname{CarryTwoPaymentClaimFiberAt}(n,j)
$$

$$
P_j=\operatorname{extraPaymentCapacityAt}(n,j)
$$

である。

そして、

```lean
paymentBlockSignedDrift_eq_bitWidth_sub
```

により、

$$
D_j=w_{j+1}-w_a
$$

が得られた。

これで Nat 上の三分岐が、整数上の単一量へ統合された。

```text
D_j > 0:
  overload / width growth

D_j = 0:
  balance / width preservation

D_j < 0:
  capacity surplus / width decrease
```

これは block-family telescope に必要な API じゃ。

### 軽微な設計注意

現在の定義は、

```lean
paymentBlockSignedDrift
    (n : OddNat) (j : ℕ)
    (_h : (floatGrowthDebtFiberAt n j).Nonempty) : ℤ
```

と、値の計算には使わない証明 `_h` を引数に持つ。

しかし右辺、

```lean
(carryTwoPaymentClaimFiberAt n j).card - extraPaymentCapacityAt n j
```

は任意の $j$ で定義できる。

したがって本体は、

```lean
noncomputable def paymentBlockSignedDriftAt
    (n : OddNat) (j : ℕ) : ℤ :=
  (carryTwoPaymentClaimFiberAt n j).card -
    extraPaymentCapacityAt n j
```

とし、block theorem 側だけに nonempty 仮定を置く方が自然じゃ。

既存定義を直ちに壊す必要はないが、block-family で証明引数の差に悩む前に整理した方がよい。

---

## 3. height と exact depth の対応

追加された二本は重要じゃ。

```lean
orbitWindowHeight_eq_one_iff_two_le_orbitExactDepth
```

```lean
two_le_orbitWindowHeight_iff_orbitExactDepth_eq_one
```

数学的には、

$$
h_i=1\Longleftrightarrow2\le A_i
$$

$$
2\le h_i\Longleftrightarrow A_i=1
$$

じゃ。

ここで、

$$
A_i=\operatorname{orbitExactDepth}(n,i)
$$

である。

odd orbit label では exact depth は必ず少なくとも $1$ なので、状態は完全に二分される。

```text
A_i = 1:
  immediate payment

A_i >= 2:
  delayed payment staircase
```

これによって `orbitPaymentTarget` は全時刻に対して安全な意味を持つようになった。

---

## 4. universal payment target

```lean
orbitPaymentTarget n i := i + orbitExactDepth n i - 1
```

は、非常に良い定義じゃ。

既存の、

```lean
floatDebtPaymentTarget
```

が strict width-growth debt 専用の名前だったのに対し、同じ数式が全軌道時刻へ拡張された。

次が証明された。

### Height-one source

$$
h_i=1\Longrightarrow i<\tau(i)
$$

### Extra-height source

$$
2\le h_i\Longrightarrow\tau(i)=i
$$

### Target correctness

$$
2\le h_{\tau(i)}
$$

ここで、

$$
\tau(i)=\operatorname{orbitPaymentTarget}(n,i)
$$

じゃ。

これは単なる target function ではない。

> **全軌道時刻を、最初に到達する extra-height payment slot へ射影する関数**

になっている。

---

## 5. universal target は retraction である

cp-305 の定理から、すぐ次が導ける。

$$
\tau(\tau(i))=\tau(i)
$$

理由は、$\tau(i)$ は必ず extra-height slot なので、自分自身を target にするからじゃ。

Lean 候補は、

```lean
theorem orbitPaymentTarget_idempotent
    (n : OddNat) (i : ℕ) :
    orbitPaymentTarget n (orbitPaymentTarget n i) =
      orbitPaymentTarget n i := by
  apply orbitPaymentTarget_eq_self_of_two_le_orbitWindowHeight
  exact two_le_orbitWindowHeight_orbitPaymentTarget n i
```

また fixed point も完全に特徴づけられる。

$$
\tau(i)=i\Longleftrightarrow2\le h_i
$$

これにより、

```text
全軌道時刻
  ↓ orbitPaymentTarget
payment endpoint 集合
```

は retraction になる。

この構造は block-family の主語として非常に強い。

---

## 6. universal source fiber

```lean
orbitPaymentSourceFiberAt n j
```

は、

$$
{i\le j\mid\tau(i)=j}
$$

を有限 `Finset` として定義する。

次も正しく証明された。

- 各時刻 $i$ は自分の target fiber に属する
- target fiber は必ず nonempty
- nonempty fiber の endpoint は extra-height
- endpoint 自身も fiber に属する
- growth-debt fiber は universal fiber に含まれる
- universal start は debt-supported start 以下

とくに、

```lean
universalPaymentBlockStart_le_floatPaymentBlockStart
```

は、

$$
b\le a
$$

を確定した。

ここで、

```text
b:
  universal source fiber の最小時刻

a:
  delayed carry-two debt fiber の最小時刻
```

じゃ。

---

## 7. report の停止理由は誤り

report は、universal fiber の区間連続性を示すには、

```text
reverse exact-depth staircase closure
```

が必要だとしている。

しかし実際には、最小 source $b$ からの **既存 forward chain** だけで十分じゃ。

### 既にある事実

$b$ は universal fiber に属するので、

$$
\tau(b)=j
$$

である。

すなわち、

$$
b+A_b-1=j
$$

じゃ。

$b<j$ の場合、

$$
2\le A_b
$$

となる。

そこで既存の、

```lean
orbitDepthRecoversExactlyAt_prePayment_chain
```

を $b$ と $A_b$ に適用する。

すると、

$$
0\le t<A_b-1\Longrightarrow A_{b+t}=A_b-t
$$

が得られる。

任意の、

$$
b\le i<j
$$

に対し、

$$
t=i-b
$$

と置けば、

$$
t<A_b-1
$$

であり、

$$
A_i=A_b-(i-b)
$$

となる。

したがって、

$$
\tau(i)=i+A_i-1
$$

へ代入すると、

$$
\tau(i)=i+A_b-(i-b)-1=b+A_b-1=j
$$

となる。

endpoint $i=j$ では既に、

$$
\tau(j)=j
$$

が証明済みじゃ。

よって、

$$
b\le i\le j\Longrightarrow\tau(i)=j
$$

が成立する。

逆向きは、fiber membership と最小性から、

$$
i\in\operatorname{Fiber}(j)\Longrightarrow b\le i\le j
$$

である。

以上より、

$$
\operatorname{orbitPaymentSourceFiberAt}(n,j)=\operatorname{Finset.Icc}(b,j)
$$

が得られる。

**新しい数学補題は不要。既存 pre-payment chain の specialization で閉じる。**

---

## 8. さらに短い local recurrence route

target dynamics 自体を一歩定理にすると、構造がより明確になる。

### Height-one step

$$
h_i=1\Longrightarrow\tau(i+1)=\tau(i)
$$

exact depth が $2$ なら次が endpoint。

exact depth が $3$ 以上なら、既存 successor theorem で depth が一つ減る。

どちらでも target は保存される。

候補 theorem は、

```lean
orbitPaymentTarget_succ_eq_of_height_eq_one
```

### Payment step

$$
2\le h_i\Longrightarrow\tau(i)=i<\tau(i+1)
$$

なぜなら、

$$
i+1\le\tau(i+1)
$$

だからじゃ。

この二本から、target sequence は、

```text
height-one step:
  target unchanged

extra-height step:
  target strictly advances
```

となる。

つまり $\tau(i)$ は非減少な階段関数であり、その level set は自動的に連続区間になる。

この API の方が、後の block-family partition に使いやすい。

---

## 9. universal fiber の完全特徴づけ

次 checkpoint で最低限欲しい theorem は次じゃ。

```lean
theorem orbitPaymentSourceFiberAt_eq_Icc_universalStart
    (n : OddNat) (j : ℕ)
    (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
    orbitPaymentSourceFiberAt n j =
      Finset.Icc (universalPaymentBlockStart n j h) j
```

これにより universal block は真に、

```text
[start, endpoint]
```

という連続区間になる。

さらに、

$$
b\le i<j\Longrightarrow h_i=1
$$

$$
2\le h_j
$$

も得られる。

これは cp-305 で既にほぼ揃っている。

---

## 10. debt-supported prefix の carry-one 性

universal start を $b$、debt-supported start を $a$ とする。

既に、

$$
b\le a
$$

じゃ。

区間、

$$
b\le i<a
$$

では universal block interior なので、

$$
h_i=1
$$

である。

もし carry-two なら、

```text
carry two + height one
```

なので `FloatDebtAt n i` になる。

また target は $j$ なので、$i$ は `floatGrowthDebtFiberAt n j` に入る。

しかし $a$ はその最小元だから矛盾。

したがって、

$$
b\le i<a\Longrightarrow c_i=1
$$

である。

よって一歩の width ledger から、

$$
w_{i+1}=w_i
$$

となり、区間全体で telescope して、

$$
w_b=w_a
$$

が得られる。

これにより cp-304 の debt-supported block ledger は、full universal block へ無損失で拡張できる。

---

## 11. block partition への道

universal target が retraction であり、その fiber が連続区間なら、自然数時刻は payment blocks に分割される。

```text
height-one run
  ↓
extra-height endpoint
  ↓
次の height-one run
  ↓
次の endpoint
```

各 block は、

```text
[start, endpoint]
```

であり、次 block は `endpoint + 1` から始まる。

異なる endpoint の fiber は、関数の fiber なので自動的に disjoint じゃ。

有限 prefix $[0,k)$ に対しては、

- 完全に終了した payment blocks
- 最後の未完 height-one suffix

へ分解できる。

この boundary suffix を明示すれば、global prefix ledger へ正しく進める。

---

## 12. 判定

### signed drift

**完成。**

### height / depth interface

**完成。**

### universal target

**完成。**

### target correctness

**完成。**

### universal source fiber

**入口完成。**

### fiber contiguity

**未実装だが、既存 theorem だけで証明可能。**

### report の「substantive closure lemma」

**誤判定。**

新規 reverse theorem は必要ない。

### cp-305 全体

**採用。ただし停止判断は差し戻し。**

---

## 13. 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge Float-window branch after
report-petal-305.

The cp-305 implementation is accepted:

- signed block drift;
- height/exact-depth equivalences;
- universal payment target;
- universal source fibers;
- universal start no later than the debt-supported start.

However, the report's stopping diagnosis must be corrected.

Universal-fiber contiguity does not require a new reverse staircase theorem.
It follows from the existing forward theorem:

    orbitDepthRecoversExactlyAt_prePayment_chain

applied to the minimum source in the universal fiber.

Do not stop at this boundary.

# Primary module

Continue in:

    DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlock.lean

# Stage A — target lower bound and retraction API

Prove:

    i ≤ orbitPaymentTarget n i

for every orbit time.

Then prove:

    orbitPaymentTarget n (orbitPaymentTarget n i)
      = orbitPaymentTarget n i

and:

    orbitPaymentTarget n i = i
      ↔ 2 ≤ orbitWindowHeight n i

Expose the image/fixed-point interpretation of payment endpoints.

# Stage B — local target dynamics

Prove:

    orbitWindowHeight n i = 1
      -> orbitPaymentTarget n (i + 1)
           = orbitPaymentTarget n i

Use the exact-depth cases:

    orbitExactDepth = 2
    orbitExactDepth >= 3

and reuse:

    orbitDepthRecoversExactlyAt_succ_of_three_le
    orbitDepthRecoversExactlyAt_delayed_height_two_le

Also prove:

    2 ≤ orbitWindowHeight n i
      -> orbitPaymentTarget n i < orbitPaymentTarget n (i + 1)

Derive monotonicity:

    Monotone (orbitPaymentTarget n)

or the corresponding pointwise theorem.

# Stage C — universal-fiber interval closure

Let:

    b = universalPaymentBlockStart n j h

From:

    b ∈ orbitPaymentSourceFiberAt n j

obtain:

    orbitPaymentTarget n b = j

For any `i` with:

    b ≤ i ≤ j

handle `i = j` by endpoint self-targeting.

For `i < j`, set:

    t = i - b

Use the equation:

    b + orbitExactDepth n b - 1 = j

and:

    orbitDepthRecoversExactlyAt_prePayment_chain

to prove:

    orbitExactDepth n i =
      orbitExactDepth n b - (i - b)

and therefore:

    orbitPaymentTarget n i = j

Prove the reverse inclusion using the minimum property and fiber membership.

Conclude:

    orbitPaymentSourceFiberAt n j =
      Finset.Icc (universalPaymentBlockStart n j h) j

No new reverse staircase theorem is needed.

# Stage D — maximal universal block geometry

Define, or expose through the fiber theorem, the universal block:

    [b, j]

Prove:

    for b ≤ i < j:
      orbitWindowHeight n i = 1

    2 ≤ orbitWindowHeight n j

Expose the exact-depth profile:

    orbitExactDepth n i = j - i + 1

for `b ≤ i ≤ j`, with the endpoint case giving depth one.

# Stage E — relation to the debt-supported block

For a nonempty delayed growth-debt fiber, let:

    b = universalPaymentBlockStart
    a = floatPaymentBlockStart

The theorem `b ≤ a` already exists.

Prove that for every `i` in `[b, a)`:

    orbitWindowHeight n i = 1
    stateUpperCarry (iterateT i n).1 = 1

The carry-one result follows because carry two plus height one would place `i`
in the delayed growth-debt fiber before its minimum `a`.

Then prove:

    bitWidth (iterateT b n).1 =
      bitWidth (iterateT a n).1

Reuse the exact one-step width balance rather than recomputing values.

# Stage F — universal block ledger

Transport the cp-304 exact payment-block ledger from `a` to `b`.

Prove:

    width after universal block + endpoint capacity
      =
    width at universal start + complete claim card

and the signed drift form.

The zero-drift carry-one prefix must be explicit in the proof.

# Stage G — signed drift API cleanup

The value of `paymentBlockSignedDrift` does not depend on its nonempty proof
argument.

Introduce a proof-independent definition such as:

    paymentBlockSignedDriftAt n j

and provide compatibility theorems for the existing API.

Avoid proof-argument friction before constructing block families.

# Stage H — finite payment-block family

Use the universal target retraction and interval fibers to define successive
payment blocks.

Prove:

    distinct target fibers are disjoint

and a finite-prefix decomposition into:

    completed universal payment blocks
    plus an explicit unfinished height-one suffix

Do not discard the unfinished suffix.

# Stage I — cumulative signed ledger

Sum universal block signed drifts over a finite completed block family.

Prove that internal bit widths telescope.

Recover the orbit-prefix width ledger together with the explicit boundary
suffix contribution.

# Stage J — pressure preparation

Use universal block lengths and exact-depth profiles to connect:

    block length histogram
    exact-depth recovery fibers
    continuation fibers
    source pressure margin

Reuse:

    sourcePressureMarginInt_eq_continuationFiber_sub_recoveryFiber

Do not infer ambient positive pressure without accounting for every block and
the boundary suffix.

# Autonomous continuation

Continue while:

    existing forward staircase theorems are reused
    target fibers remain exact function fibers
    universal and debt-supported starts remain distinct
    proof arguments do not contaminate block-family data
    incomplete boundary suffixes remain explicit
    no sorry or axiom is introduced
    builds remain green

Stop only at a genuine logical obstruction or an unresolved dependency/API
placement conflict.

# Validation

Run:

    lake build DkMath.Collatz.PetalBridge.FloatWindow.PaymentBlockBridge
    lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock
    lake build DkMath.Collatz.PetalBridge.FloatWindow
    lake build DkMath.Collatz.PetalBridge
    lake build DkMath
    git diff --check

Record the autonomous continuation in:

    docs/dev/das-p2l-260607/review/report-petal-306.md
```

cp-305 の実装は良い。

だが、Codex が「新しい逆向き定理が必要」と見た箇所は、既存の前向き staircase を最小 source から走らせれば、そのまま閉じる。

ここは止まる場所ではないぞい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
index 9c081108..9b39edb5 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
@@ -13,6 +13,7 @@ import DkMath.Collatz.PetalBridge.FloatWindow.DriftBridge
 import DkMath.Collatz.PetalBridge.FloatWindow.PressureIncidenceBridge
 import DkMath.Collatz.PetalBridge.FloatWindow.PaymentMultiplicityBridge
 import DkMath.Collatz.PetalBridge.FloatWindow.PaymentBlockBridge
+import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock

 #print "file: DkMath.Collatz.PetalBridge.FloatWindow"

diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/PaymentBlockBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/PaymentBlockBridge.lean
index 9a137152..e5dafafa 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/PaymentBlockBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/PaymentBlockBridge.lean
@@ -341,6 +341,21 @@ theorem shiftedExtraPaymentCapacity_eq_sum_range
             (orbitWindowHeight_eq_s_iterateT n (a + len)).symm
       rw [hheight]

+/--
+Exact shifted width ledger.
+
+This is the existing prefix ledger, based at `iterateT a n`; no new induction
+over a segment is required.
+-/
+theorem bitWidth_iterateT_add_shiftedExtraPaymentCapacity_eq_shiftedCarryTwo
+    (n : OddNat) (a len : ℕ) :
+    bitWidth (iterateT (a + len) n).1 + shiftedExtraPaymentCapacity n a len =
+      bitWidth (iterateT a n).1 + shiftedOrbitCarryTwoCount n a len := by
+  unfold shiftedExtraPaymentCapacity shiftedOrbitCarryTwoCount
+  rw [iterateT_add_eq_iterateT_from_shift]
+  exact bitWidth_iterateT_add_sumExtraHeight_eq_initial_add_countCarryTwo
+    (iterateT a n) len
+
 /-- Membership in the local carry-two offset set. -/
 theorem mem_shiftedCarryTwoOffsets_iff
     {n : OddNat} {a len t : ℕ} :
@@ -485,19 +500,8 @@ theorem bitWidth_iterateT_paymentBlock_eq_claimFiber_card
     bitWidth (iterateT (j + 1) n).1 + extraPaymentCapacityAt n j =
       bitWidth (iterateT (floatPaymentBlockStart n j h) n).1 +
         (carryTwoPaymentClaimFiberAt n j).card := by
-  have hledger :
-      bitWidth (iterateT
-        (floatPaymentBlockStart n j h + (j + 1 - floatPaymentBlockStart n j h)) n).1 +
-          shiftedExtraPaymentCapacity n (floatPaymentBlockStart n j h)
-            (j + 1 - floatPaymentBlockStart n j h) =
-        bitWidth (iterateT (floatPaymentBlockStart n j h) n).1 +
-          shiftedOrbitCarryTwoCount n (floatPaymentBlockStart n j h)
-            (j + 1 - floatPaymentBlockStart n j h) := by
-    unfold shiftedExtraPaymentCapacity shiftedOrbitCarryTwoCount
-    rw [iterateT_add_eq_iterateT_from_shift]
-    exact bitWidth_iterateT_add_sumExtraHeight_eq_initial_add_countCarryTwo
-      (iterateT (floatPaymentBlockStart n j h) n)
-      (j + 1 - floatPaymentBlockStart n j h)
+  have hledger := bitWidth_iterateT_add_shiftedExtraPaymentCapacity_eq_shiftedCarryTwo
+    n (floatPaymentBlockStart n j h) (j + 1 - floatPaymentBlockStart n j h)
   rw [shiftedExtraPaymentCapacity_eq_extraPaymentCapacityAt,
     shiftedOrbitCarryTwoCount_eq_carryTwoPaymentClaimFiber_card] at hledger
   simpa [floatPaymentBlockStart_add_endpointLength_eq_endpoint_succ] using hledger
@@ -530,20 +534,94 @@ theorem carryTwoPaymentClaimFiber_card_lt_capacity_iff_bitWidth_paymentBlock_gt
   have hledger := bitWidth_iterateT_paymentBlock_eq_claimFiber_card n j h
   omega

-/--
-Exact shifted width ledger.
+/-- Signed claim-minus-capacity balance of a canonical payment block. -/
+noncomputable def paymentBlockSignedDrift
+    (n : OddNat) (j : ℕ) (_h : (floatGrowthDebtFiberAt n j).Nonempty) : ℤ :=
+  (carryTwoPaymentClaimFiberAt n j).card - extraPaymentCapacityAt n j

-This is the existing prefix ledger, based at `iterateT a n`; no new induction
-over a segment is required.
--/
-theorem bitWidth_iterateT_add_shiftedExtraPaymentCapacity_eq_shiftedCarryTwo
-    (n : OddNat) (a len : ℕ) :
-    bitWidth (iterateT (a + len) n).1 + shiftedExtraPaymentCapacity n a len =
-      bitWidth (iterateT a n).1 + shiftedOrbitCarryTwoCount n a len := by
-  unfold shiftedExtraPaymentCapacity shiftedOrbitCarryTwoCount
-  rw [iterateT_add_eq_iterateT_from_shift]
-  exact bitWidth_iterateT_add_sumExtraHeight_eq_initial_add_countCarryTwo
-    (iterateT a n) len
+/-- The signed claim balance is exactly the signed width drift across the block. -/
+theorem paymentBlockSignedDrift_eq_bitWidth_sub
+    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
+    paymentBlockSignedDrift n j h =
+      (bitWidth (iterateT (j + 1) n).1 : ℤ) -
+        bitWidth (iterateT (floatPaymentBlockStart n j h) n).1 := by
+  unfold paymentBlockSignedDrift
+  have hledger := bitWidth_iterateT_paymentBlock_eq_claimFiber_card n j h
+  omega
+
+/-- Positive signed block drift is precisely complete-claim overload. -/
+theorem paymentBlockSignedDrift_pos_iff_overload
+    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
+    0 < paymentBlockSignedDrift n j h ↔ CarryTwoPaymentOverloadAt n j := by
+  unfold paymentBlockSignedDrift CarryTwoPaymentOverloadAt
+  omega
+
+/-- Zero signed block drift is precisely claim/capacity balance. -/
+theorem paymentBlockSignedDrift_eq_zero_iff_claim_card_eq_capacity
+    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
+    paymentBlockSignedDrift n j h = 0 ↔
+      (carryTwoPaymentClaimFiberAt n j).card = extraPaymentCapacityAt n j := by
+  unfold paymentBlockSignedDrift
+  omega
+
+/-- Negative signed block drift is precisely strict capacity surplus. -/
+theorem paymentBlockSignedDrift_neg_iff_claim_card_lt_capacity
+    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
+    paymentBlockSignedDrift n j h < 0 ↔
+      (carryTwoPaymentClaimFiberAt n j).card < extraPaymentCapacityAt n j := by
+  unfold paymentBlockSignedDrift
+  omega
+
+/-- Height one is exactly an all-ones exact depth of at least two. -/
+theorem orbitWindowHeight_eq_one_iff_two_le_orbitExactDepth
+    (n : OddNat) (i : ℕ) :
+    orbitWindowHeight n i = 1 ↔ 2 ≤ orbitExactDepth n i := by
+  rw [orbitWindowHeight_eq_one_iff_mod_four_eq_three]
+  unfold orbitExactDepth
+  have h := (le_residualAllOnesDepth_iff_mod_eq_allOnes (oddOrbitLabel n i) 2).symm
+  norm_num at h
+  exact h
+
+/-- An extra-height event is exactly all-ones exact depth one. -/
+theorem two_le_orbitWindowHeight_iff_orbitExactDepth_eq_one
+    (n : OddNat) (i : ℕ) :
+    2 ≤ orbitWindowHeight n i ↔ orbitExactDepth n i = 1 := by
+  rw [orbitWindowHeight_two_le_iff_mod_four_eq_one]
+  unfold orbitExactDepth
+  constructor
+  · intro hmod
+    have hmodTwo : oddOrbitLabel n i % 2 = 1 := by
+      calc
+        oddOrbitLabel n i % 2 = (oddOrbitLabel n i % 4) % 2 := by
+          symm
+          exact Nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 4)
+        _ = 1 := by rw [hmod]
+    have hle : 1 ≤ ResidualAllOnesDepth (oddOrbitLabel n i) :=
+      (le_residualAllOnesDepth_iff_mod_eq_allOnes _ 1).2 (by norm_num; exact hmodTwo)
+    by_contra hne
+    have htwo : 2 ≤ ResidualAllOnesDepth (oddOrbitLabel n i) := by omega
+    have hmodThree :=
+      (le_residualAllOnesDepth_iff_mod_eq_allOnes _ 2).1 htwo
+    norm_num at hmodThree
+    omega
+  · intro hdepth
+    have hle : 1 ≤ ResidualAllOnesDepth (oddOrbitLabel n i) := by omega
+    have hmodTwo : oddOrbitLabel n i % 2 = 1 := by
+      have hmod := (le_residualAllOnesDepth_iff_mod_eq_allOnes _ 1).1 hle
+      norm_num at hmod
+      exact hmod
+    have hnotThree : oddOrbitLabel n i % 4 ≠ 3 := by
+      intro hthree
+      have htwo : 2 ≤ ResidualAllOnesDepth (oddOrbitLabel n i) := by
+        apply (le_residualAllOnesDepth_iff_mod_eq_allOnes _ 2).2
+        norm_num
+        exact hthree
+      omega
+    have hmodLt : oddOrbitLabel n i % 4 < 4 := by omega
+    have hmodTwo' : (oddOrbitLabel n i % 4) % 2 = 1 := by
+      rw [Nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 4)]
+      exact hmodTwo
+    omega

 /-!
 ## Ledger frontier
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlock.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlock.lean
new file mode 100644
index 00000000..c7f45140
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlock.lean
@@ -0,0 +1,173 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.PaymentBlockBridge
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock"
+
+namespace DkMath.Collatz
+
+/-!
+# Universal first-payment coordinates
+
+The earlier `floatDebtPaymentTarget` was introduced for delayed width-growth
+debts.  Exact all-ones depth, however, assigns the same canonical target to
+every orbit time.  This module exposes that total coordinate without turning a
+first-claim relation into a final allocation claim.
+-/
+
+/-- The canonical payment target determined by exact all-ones depth at any orbit time. -/
+noncomputable def orbitPaymentTarget (n : OddNat) (i : ℕ) : ℕ :=
+  i + orbitExactDepth n i - 1
+
+/-- The debt-facing target is definitionally the universal target. -/
+theorem floatDebtPaymentTarget_eq_orbitPaymentTarget
+    (n : OddNat) (i : ℕ) :
+    floatDebtPaymentTarget n i = orbitPaymentTarget n i := rfl
+
+/-- A height-one source has a strictly later canonical payment target. -/
+theorem lt_orbitPaymentTarget_of_orbitWindowHeight_eq_one
+    {n : OddNat} {i : ℕ}
+    (hheight : orbitWindowHeight n i = 1) :
+    i < orbitPaymentTarget n i := by
+  unfold orbitPaymentTarget
+  have hdepth := (orbitWindowHeight_eq_one_iff_two_le_orbitExactDepth n i).1 hheight
+  omega
+
+/-- An extra-height event pays immediately at its own orbit time. -/
+theorem orbitPaymentTarget_eq_self_of_two_le_orbitWindowHeight
+    {n : OddNat} {i : ℕ}
+    (hheight : 2 ≤ orbitWindowHeight n i) :
+    orbitPaymentTarget n i = i := by
+  unfold orbitPaymentTarget
+  have hdepth := (two_le_orbitWindowHeight_iff_orbitExactDepth_eq_one n i).1 hheight
+  omega
+
+/-- Every orbit time targets a genuine extra-height payment slot. -/
+theorem two_le_orbitWindowHeight_orbitPaymentTarget
+    (n : OddNat) (i : ℕ) :
+    2 ≤ orbitWindowHeight n (orbitPaymentTarget n i) := by
+  by_cases hheight : orbitWindowHeight n i = 1
+  · have hdepth := (orbitWindowHeight_eq_one_iff_two_le_orbitExactDepth n i).1 hheight
+    have hexact : OrbitDepthRecoversExactlyAt n i (orbitExactDepth n i) := by rfl
+    simpa [orbitPaymentTarget] using
+      orbitDepthRecoversExactlyAt_delayed_height_two_le n i (orbitExactDepth n i) hdepth hexact
+  · have htwo : 2 ≤ orbitWindowHeight n i := by
+      have hone := orbitWindowHeight_one_le n i
+      omega
+    rw [orbitPaymentTarget_eq_self_of_two_le_orbitWindowHeight htwo]
+    exact htwo
+
+/-- All sources at most `j` whose canonical payment target is `j`. -/
+noncomputable def orbitPaymentSourceFiberAt (n : OddNat) (j : ℕ) : Finset ℕ := by
+  classical
+  exact (Finset.range (j + 1)).filter fun i => orbitPaymentTarget n i = j
+
+/-- Membership API for a universal canonical payment-source fiber. -/
+theorem mem_orbitPaymentSourceFiberAt_iff
+    {n : OddNat} {i j : ℕ} :
+    i ∈ orbitPaymentSourceFiberAt n j ↔ i ≤ j ∧ orbitPaymentTarget n i = j := by
+  classical
+  simp [orbitPaymentSourceFiberAt]
+
+/-- A nonempty universal source fiber has a canonical earliest source. -/
+noncomputable def universalPaymentBlockStart
+    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) : ℕ :=
+  (orbitPaymentSourceFiberAt n j).min' h
+
+/-- The universal block start belongs to its endpoint's source fiber. -/
+theorem universalPaymentBlockStart_mem_sourceFiber
+    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
+    universalPaymentBlockStart n j h ∈ orbitPaymentSourceFiberAt n j :=
+  Finset.min'_mem _ h
+
+/-- Every time belongs to the universal source fiber of its own canonical target. -/
+theorem self_mem_orbitPaymentSourceFiberAt_target
+    (n : OddNat) (i : ℕ) :
+    i ∈ orbitPaymentSourceFiberAt n (orbitPaymentTarget n i) := by
+  rw [mem_orbitPaymentSourceFiberAt_iff]
+  constructor
+  · by_cases hheight : orbitWindowHeight n i = 1
+    · exact (lt_orbitPaymentTarget_of_orbitWindowHeight_eq_one hheight).le
+    · have htwo : 2 ≤ orbitWindowHeight n i := by
+        have hone := orbitWindowHeight_one_le n i
+        omega
+      rw [orbitPaymentTarget_eq_self_of_two_le_orbitWindowHeight htwo]
+  · rfl
+
+/-- Every canonical payment target has a nonempty universal source fiber. -/
+theorem orbitPaymentSourceFiberAt_nonempty_target
+    (n : OddNat) (i : ℕ) :
+    (orbitPaymentSourceFiberAt n (orbitPaymentTarget n i)).Nonempty :=
+  ⟨i, self_mem_orbitPaymentSourceFiberAt_target n i⟩
+
+/-- A nonempty universal source fiber has an actual extra-height endpoint. -/
+theorem two_le_orbitWindowHeight_of_orbitPaymentSourceFiberAt_nonempty
+    {n : OddNat} {j : ℕ}
+    (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
+    2 ≤ orbitWindowHeight n j := by
+  rcases h with ⟨i, hi⟩
+  have htarget := (mem_orbitPaymentSourceFiberAt_iff.mp hi).2
+  rw [← htarget]
+  exact two_le_orbitWindowHeight_orbitPaymentTarget n i
+
+/-- A nonempty universal source fiber contains its endpoint as the immediate source. -/
+theorem endpoint_mem_orbitPaymentSourceFiberAt_of_nonempty
+    {n : OddNat} {j : ℕ}
+    (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
+    j ∈ orbitPaymentSourceFiberAt n j := by
+  rw [mem_orbitPaymentSourceFiberAt_iff]
+  exact ⟨le_rfl,
+    orbitPaymentTarget_eq_self_of_two_le_orbitWindowHeight
+      (two_le_orbitWindowHeight_of_orbitPaymentSourceFiberAt_nonempty h)⟩
+
+/-- Every delayed growth-debt source is a universal source for the same target. -/
+theorem mem_orbitPaymentSourceFiberAt_of_mem_floatGrowthDebtFiberAt
+    {n : OddNat} {i j : ℕ}
+    (hi : i ∈ floatGrowthDebtFiberAt n j) :
+    i ∈ orbitPaymentSourceFiberAt n j := by
+  rcases mem_floatGrowthDebtFiberAt_iff.mp hi with ⟨hij, _, htarget⟩
+  rw [mem_orbitPaymentSourceFiberAt_iff]
+  exact ⟨by omega,
+    by simpa [← floatDebtPaymentTarget_eq_orbitPaymentTarget] using htarget⟩
+
+/-- A nonempty delayed growth-debt fiber induces a nonempty universal source fiber. -/
+theorem orbitPaymentSourceFiberAt_nonempty_of_floatGrowthDebtFiberAt_nonempty
+    {n : OddNat} {j : ℕ}
+    (h : (floatGrowthDebtFiberAt n j).Nonempty) :
+    (orbitPaymentSourceFiberAt n j).Nonempty := by
+  rcases h with ⟨i, hi⟩
+  exact ⟨i, mem_orbitPaymentSourceFiberAt_of_mem_floatGrowthDebtFiberAt hi⟩
+
+/--
+The universal block begins no later than the delayed-growth-debt block.
+
+This is only an inclusion-of-fibers statement.  Equality is not claimed: the
+universal fiber can contain height-one sources that are not Float growth debts.
+-/
+theorem universalPaymentBlockStart_le_floatPaymentBlockStart
+    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
+    universalPaymentBlockStart n j
+      (orbitPaymentSourceFiberAt_nonempty_of_floatGrowthDebtFiberAt_nonempty h) ≤
+      floatPaymentBlockStart n j h := by
+  apply Finset.min'_le
+  exact mem_orbitPaymentSourceFiberAt_of_mem_floatGrowthDebtFiberAt
+    (floatPaymentBlockStart_mem_growthDebtFiber n j h)
+
+/-!
+## Next closure requirement
+
+To identify a nonempty universal source fiber with the full interval from its
+minimum to its endpoint, the missing direction is not finite-set arithmetic.
+It is an exact-depth staircase *reverse closure*: from a source targeting `j`,
+one must show that every intervening time has the corresponding decremented
+exact depth and therefore the same target.  Until that theorem is supplied,
+this module intentionally exposes membership, minima, endpoint height, and
+the debt-fiber inclusion only; it does not claim interval contiguity or
+prefix-family coverage.
+-/
+
+end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-305.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-305.md
new file mode 100644
index 00000000..f1de1fec
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-305.md
@@ -0,0 +1,53 @@
+# cp-305 Universal Payment Coordinates
+
+## Implemented
+
+The accepted cp-304 payment-block ledger was retained and its generic shifted
+ledger theorem was moved before the specialized block theorem, so the latter
+now reuses the public shifted statement directly.
+
+`PaymentBlockBridge.lean` now also provides an integer API:
+
+- `paymentBlockSignedDrift = complete claim card - endpoint capacity`;
+- this equals signed width-after minus width-before;
+- positive, zero, and negative drift characterize overload, balance, and
+  strict capacity surplus respectively.
+
+The height/depth interface is now explicit:
+
+```text
+height = 1   iff exact all-ones depth >= 2
+height >= 2  iff exact all-ones depth = 1
+```
+
+## Universal target layer
+
+Added `DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock`.
+
+`orbitPaymentTarget n i = i + orbitExactDepth n i - 1` is defined for every
+orbit time.  The pre-existing debt-facing target is definitionally equal to
+it.  Lean proves:
+
+- height-one sources target strictly later times;
+- extra-height sources target themselves;
+- every source targets an actual extra-height slot;
+- the finite source fiber at an endpoint has a membership API and a minimum;
+- every target has a nonempty source fiber;
+- a nonempty source fiber has an extra-height endpoint;
+- every delayed growth-debt source lies in the universal source fiber with the
+  same target, so the universal start is no later than the debt-supported
+  block start.
+
+## Boundary Found
+
+The universal fiber has not been claimed to be a contiguous interval yet.
+The remaining mathematical bridge is a reverse exact-depth staircase theorem:
+given a source targeting `j`, every intermediate time must be shown to have
+the decremented exact depth and the same target.  This is a substantive
+closure lemma, not an `Ico` normalization issue.  The source code records this
+boundary beside the new API.
+
+## No overclaim
+
+No final allocation of first claims, universal block-family coverage, pressure
+conclusion, or convergence conclusion has been added.
````
`````
