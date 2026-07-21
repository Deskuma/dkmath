# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.FloatWindow.PaymentBlockBridge

gch: c021a7707c712d79bc61347b8525a9eb1aeb8a3c

## Report

cp-302 は canonical payment block まで到達しました。

新規 [PaymentBlockBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/PaymentBlockBridge.lean) を追加し、`FloatWindow` から export しています。

確定したこと:

- nonempty target fiber の最小 debt を canonical block start とした。
- block interior `[a, j)` は全点で height `1`、endpoint `j` は height `≥ 2`。
- interior の全時刻は first-payment target が同じ `j`。
- delayed debt fiber は interior の carry-two filter と完全一致。
- complete carry-two claim fiber は endpoint を含む block `[a, j]` の carry-two filter と完全一致。
- `iterateT (a + len)` の shift theorem と、そのまま使える exact shifted width ledger を追加。

ここで残る本当の境界は、shifted prefix count を global canonical interval の filtered `Finset` card へ移す再index化です。これが通れば、endpoint capacity と block claim card の正確な balance、さらに overload と block width growth の同値へ進めます。first-payment claim を final allocation と取り違える定理は追加していません。

詳細は [report-petal-302.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-302.md) に記録しました。

`PaymentBlockBridge`、`FloatWindow`、`PetalBridge`、トップレベル `DkMath`、`git diff --check` はすべて通過しています。新規モジュールに `sorry` / `axiom` はありません。

## Review

## 結論

**採用。cp-302 は canonical first-payment debt block を正しく構成し、block 内の claim 集合と shifted Float ledger を接続する直前まで到達した。**

今回確定したのは、

```text
target j を共有する最初の debt source a
  ↓
[a, j) はすべて height = 1
  ↓
j は height >= 2
  ↓
[a, j] の carry-two 点
  =
j を first-payment target とする全 carry-two claim
```

という一つの完全な debt-support block じゃ。

新規モジュール、`FloatWindow`、`PetalBridge`、トップレベル `DkMath` の build と `git diff --check`、no-`sorry` / no-`axiom` が報告されている。

ただし重要な意味上の補正が一つある。

> 現在の `floatPaymentBlockStart` は、同じ target を持つ全 height-one staircase の最左端ではない。
> 同じ target を持つ carry-two debt の最左端である。

したがって現在の block は、

> **canonical payment staircase 全体**

ではなく、

> **canonical debt-supported suffix of a payment staircase**

と読むのが正確じゃ。

block balance の証明には現在の start で十分だが、後で pressure と block-length 分布を結ぶ際には、さらに左側の carry-one / height-one prefix を復元する必要がある。

---

## 1. block start の定義

```lean
floatPaymentBlockStart n j h
```

は、

```lean
(floatGrowthDebtFiberAt n j).min' h
```

として定義された。

つまり target $j$ を持つ delayed growth debt の最小時刻を、

$$
a:=\min{i\mid \operatorname{FloatDebtAt}(i),\ \tau(i)=j}
$$

とする。

当然、

$$
a<j
$$

であり、

$$
\tau(a)=j
$$

じゃ。

この start は claim ledger の開始点として自然である。

---

## 2. interior の全点が height one

```lean
orbitWindowHeight_eq_one_of_mem_floatPaymentBlockInterior
```

は、

$$
a\le t<j\Longrightarrow h_t=1
$$

を証明する。

これは start $a$ の exact-depth pre-payment chain を、そのまま $j$ まで展開したものじゃ。

したがって block interior では extra payment capacity は全く発生しない。

$$
h_t-1=0\qquad(a\le t<j)
$$

endpoint では、

```lean
two_le_orbitWindowHeight_floatPaymentBlock_endpoint
```

により、

$$
2\le h_j
$$

となる。

ゆえに区間 $[a,j]$ の追加 payment capacity は、endpoint $j$ にだけ集中する。

---

## 3. interior 全体が同じ target を持つ

```lean
floatDebtPaymentTarget_eq_endpoint_of_mem_floatPaymentBlockInterior
```

は、

$$
a\le t<j\Longrightarrow\tau(t)=j
$$

を示す。

ここで重要なのは、$t$ が carry-two debt である必要がないことじゃ。

carry-one / height-one の時刻も含め、interior の全点が同じ first-payment target を持つ。

これは exact depth が、

$$
A_t=j-t+1
$$

と一段ずつ減少するためである。

したがって block は、既知の debt source だけを寄せ集めた集合ではなく、間に挟まる carry-one state まで含む連続区間になった。

---

## 4. delayed debt fiber の完全同定

次の同値は非常に良い。

```lean
mem_growthDebtFiber_iff_mem_floatPaymentBlockInterior_and_carryTwo
```

$$
i\in\operatorname{GrowthDebtFiber}(j)
$$

と、

$$
i\in[a,j)\land\operatorname{CarryTwoDebtAt}(i)
$$

が同値になった。

したがって、

```lean
floatGrowthDebtFiberAt_eq_filter_floatPaymentBlockInterior_carryTwo
```

により、

$$
\operatorname{GrowthDebtFiber}(j) = \{i\in[a,j)\mid c_i=2\}
$$

が成立する。

これは diagonal target fiber を contiguous time block 上の carry filter へ変換したものじゃ。

斜め座標が時間区間へ降りてきた。

---

## 5. complete claim fiber の同定

さらに endpoint を含めて、

```lean
mem_carryTwoPaymentClaimFiber_iff_mem_floatPaymentBlockWithEndpoint_and_carryTwo
```

が証明された。

$$
i\in\operatorname{CarryTwoClaimFiber}(j)
$$

と、

$$
i\in[a,j]\land c_i=2
$$

が同値になる。

interior の carry-two は delayed claim。

endpoint の carry-two は immediate self-claim。

したがって、

$$
\operatorname{CarryTwoClaimFiber}(j) = \{i\in[a,j]\mid c_i=2\}
$$

である。

cardinality 版も追加されている。

この theorem によって、claim multiplicity は抽象的 fiber ではなく、

> 一つの連続 block 内で carry-two が何回出たか

という単純な count になった。

---

## 6. shifted orbit ledger

```lean
iterateT_add_eq_iterateT_from_shift
```

は、

$$
T^{a+\ell}(n)=T^\ell(T^a(n))
$$

を固定する。

これを既存の prefix ledger に適用して、

```lean
bitWidth_iterateT_add_shiftedExtraPaymentCapacity_eq_shiftedCarryTwo
```

を得た。

数学形は、

$$
w_{a+\ell}+E(a,\ell)=w_a+C(a,\ell)
$$

じゃ。

ここで、

$$
E(a,\ell):=\sum_{t=a}^{a+\ell-1}(h_t-1)
$$

$$
C(a,\ell):=#{t\in[a,a+\ell)\mid c_t=2}
$$

と読む。

新しい区間帰納を作らず、既存 prefix theorem を shifted state に適用したのは良い設計じゃ。

---

## 7. 現在の停止地点

Codex は次の二つの再index化が残ったとしている。

```text
shifted carry count on [a, j+1)
=
card of carryTwoPaymentClaimFiberAt n j
```

```text
shifted extra-height sum on [a, j+1)
=
extraPaymentCapacityAt n j
```

これは正しい。

ただし、これは本質的な数学障害ではない。

> **有限区間の添字輸送という実装上の薄い橋**

じゃ。

次 checkpoint では自然に閉じる可能性が高い。

---

## 8. 重要な補正――現在の block は maximal staircase ではない

ここは今後の pressure 接続に影響する。

`floatPaymentBlockStart` は最初の debt source であり、最初の height-one source ではない。

実際、次のような軌道断片があり得る。

```text
time 18: state 167, carry 1, height 1, exact depth 3, target 20
time 19: state 251, carry 2, height 1, exact depth 2, target 20
time 20: state 377, carry 2, height 2, endpoint
```

target $20$ を持つ growth debt は時刻 $19$ だけなので、現在の block start は $19$ になる。

しかし、同じ target を持つ height-one staircase 自体は時刻 $18$ から始まっている。

```text
maximal staircase:
  [18, 20)

debt-supported block:
  [19, 20)
```

時刻 $18$ は carry-one / height-one なので、width drift はゼロじゃ。

$$
c_{18}-h_{18}=1-1=0
$$

したがって block width ledger において、時刻 $18$ を省いても値は変わらない。

このため現在の実装は正しい。

だが pressure は exact-depth profile を見るので、時刻 $18$ の depth $3$ を省くと block-length histogram が短くなる。

ゆえに今後、二つの start を分けるべきじゃ。

```text
debtBlockStart:
  最初の carry-two / height-one debt

staircaseStart:
  同じ target を持つ maximal height-one run の最左端
```

現在の `floatPaymentBlockStart` は前者である。

---

## 9. 二つの block の接続

将来欲しい構造はこうじゃ。

```text
maximal payment staircase
[b, j)

  [b, a):
    carry 1
    height 1
    width drift 0

  [a, j):
    debt-supported block
    carry 1 or 2
    height 1

  j:
    height >= 2
```

ここで $a$ は現在の `floatPaymentBlockStart`。

$b$ は将来導入する maximal staircase start じゃ。

前半では常に、

$$
c_t=1,\qquad h_t=1
$$

なので、

$$
w_a=w_b
$$

となる。

したがって overload と block width growth の theorem は、現在の $a$ で証明した後、そのまま maximal staircase start $b$ に輸送できる。

これは Float と pressure を接続する非常にきれいな橋になる。

---

## 10. 次に得られる中心恒等式

区間長を、

$$
\ell=j+1-a
$$

と置く。

shifted ledger により、

$$
w_{j+1}+E(a,\ell)=w_a+C(a,\ell)
$$

となる。

interior は全て height $1$ なので、

$$
E(a,\ell)=h_j-1
$$

じゃ。

claim fiber identification により、

$$
C(a,\ell)=\#\operatorname{CarryTwoClaimFiber}(j)
$$

となる。

よって、

$$
w_{j+1}+(h_j-1) = w_a+\#\operatorname{CarryTwoClaimFiber}(j)
$$

が得られる。

すなわち、

$$
w_{j+1}-w_a = \#\operatorname{CarryTwoClaimFiber}(j)-(h_j-1)
$$

じゃ。

これは payment block の完全会計である。

---

## 11. overload と block growth

上の等式から直ちに、

$$
h_j-1 < \#\operatorname{CarryTwoClaimFiber}(j)
$$

と、

$$
w_a<w_{j+1}
$$

が同値になる。

つまり、

$$
\operatorname{CarryTwoPaymentOverloadAt}(j)
\Longleftrightarrow
w_a < w_{j+1}
$$

じゃ。

同様に、

$$
\#\text{claims}=h_j-1
\Longleftrightarrow
w_a=w_{j+1}
$$

$$
\#\text{claims}<h_j-1
\Longleftrightarrow
w_{j+1}<w_a
$$

も得られる。

この三分岐は、

```text
overload   -> block width growth
balanced   -> block width preservation
credit     -> block width decrease
```

となる。

ここまで閉じれば、一歩単位ではなく payment cycle 単位で軌道を圧縮できる。

---

## 12. pressure への次の接続

block balance を完成させた後、maximal staircase start を導入する。

その maximal block の長さを $L$ とすれば、exact-depth profile は、

$$
L+1,L,\ldots,3,2
$$

になる。

この profile が pressure の、

```text
recovery fiber
continuation fiber
```

を構成する。

一方、現在の debt-supported suffix は、block 内の carry-two 密度を測る。

```text
maximal staircase length:
  下位 pressure の対象

debt-supported suffix carry density:
  上位 Float overload の対象
```

したがって最終的な挟み撃ちは、

> 長い staircase が多ければ pressure が正へ寄る。
> 短い staircase に carry-two が集中すれば block overload が起きる。

という二方向の追い込みになる。

---

## 13. 判定

### canonical debt block

**完成。**

### block interior height-one

**完成。**

### common payment target

**完成。**

### delayed fiber identification

**完成。**

### complete claim fiber identification

**完成。**

### shifted ledger

**完成。**

### endpoint-only block balance

**未完成だが、再index化だけ。**

### overload / block-growth equivalence

**次に直結。**

### pressure block-length bridge

**現在の start では不足。maximal staircase start が別途必要。**

---

## 14. 次の Codex 指示

cp-303 では、まず reindexing と exact block balance を閉じる。

その後、現在の debt start と maximal staircase start を分離し、pressure 接続の土台まで進ませる。

````text
You are continuing the DkMath Collatz / PetalBridge Float-window branch after
report-petal-302.

The current module has completed the canonical debt-supported payment block:

```text
a = minimum delayed growth debt targeting j
[a, j) has height one
j has height at least two
the complete claim fiber at j is the carry-two filter of [a, j]
```

The immediate task is to close the exact endpoint-only block balance.

The checkpoint number is not a stopping boundary. Continue autonomously through
all logically justified stages.

# Primary target

Continue in:

```text
DkMath/Collatz/PetalBridge/FloatWindow/PaymentBlockBridge.lean
```

Create a separate reindexing module only if the lemmas are broadly reusable.

# Stage A — generic segment reindexing

Prove reusable interval forms of the shifted counts.

For carry-two count, target a theorem equivalent to:

```text
shiftedOrbitCarryTwoCount n a len
  =
card { i in Finset.Ico a (a + len) | CarryTwoDebtAt n i }
```

Using the existing helper:

```lean
carryTwoPositions
```

a preferred statement is:

```lean
shiftedOrbitCarryTwoCount n a len =
  (carryTwoPositions n (Finset.Ico a (a + len))).card
```

For extra-height payment, introduce a finite interval sum:

```lean
noncomputable def extraPaymentCapacityOn
    (n : OddNat) (S : Finset ℕ) : ℕ :=
  ∑ i ∈ S, orbitWindowHeight n i - 1
```

or an equivalent clean API.

Prove:

```text
shiftedExtraPaymentCapacity n a len
  =
extraPaymentCapacityOn n (Finset.Ico a (a + len))
```

Prefer induction on `len`, reusing:

```lean
iterateT_add_eq_iterateT_from_shift
orbitWindowHeight_eq_s_iterateT
```

Do not hide the index transport inside a large final proof.

# Stage B — block interval arithmetic

For a nonempty growth-debt fiber at endpoint `j`, let:

```text
a = floatPaymentBlockStart n j h
len = j + 1 - a
```

Prove explicitly:

```text
a + len = j + 1
Finset.Ico a (a + len) = Finset.Icc a j
```

or the corresponding membership equivalence.

# Stage C — count identification

Use the generic reindexing theorem and the existing block theorem:

```lean
carryTwoPaymentClaimFiberAt_eq_filter_floatPaymentBlockWithEndpoint_carryTwo
```

to prove:

```text
shiftedOrbitCarryTwoCount n a (j + 1 - a)
  =
(carryTwoPaymentClaimFiberAt n j).card
```

# Stage D — endpoint capacity identification

Use:

```lean
orbitWindowHeight_eq_one_of_mem_floatPaymentBlockInterior
two_le_orbitWindowHeight_floatPaymentBlock_endpoint
```

to prove:

```text
shiftedExtraPaymentCapacity n a (j + 1 - a)
  =
extraPaymentCapacityAt n j
```

The proof must explicitly show that all contributions in `[a, j)` are zero
and the unique endpoint contribution is `height(j) - 1`.

# Stage E — exact payment-block ledger

Prove the central theorem:

```text
bitWidth (iterateT (j + 1) n).1
  + extraPaymentCapacityAt n j
=
bitWidth (iterateT a n).1
  + (carryTwoPaymentClaimFiberAt n j).card
```

where:

```text
a = floatPaymentBlockStart n j h
```

Provide both the subtraction-free natural-number equality and, if useful, an
integer drift form.

# Stage F — overload / balance / credit trichotomy

Derive:

```text
CarryTwoPaymentOverloadAt n j
  <->
bitWidth (iterateT a n).1 <
  bitWidth (iterateT (j + 1) n).1
```

Also prove:

```text
claim card = capacity
  <->
block width preserved

claim card < capacity
  <->
block width decreases
```

Expose a single trichotomy theorem if it produces a cleaner API.

# Stage G — semantic distinction between debt block and maximal staircase

The current:

```lean
floatPaymentBlockStart
```

is the minimum carry-two/height-one debt targeting `j`.

It need not be the earliest height-one source with target `j`.

Do not claim that it is the maximal payment staircase start.

Document the current object as the:

```text
debt-supported payment block
```

or equivalent.

Search numerically or symbolically for the possibility:

```text
carry one / height one / same target
```

before the first debt. The implementation must allow this prefix.

# Stage H — maximal payment staircase

After the debt-block balance is complete, introduce a separate canonical
maximal staircase start.

A suitable semantic target is the earliest `b <= j` such that:

```text
for every t in [b, j):
  orbitWindowHeight n t = 1

at j:
  2 <= orbitWindowHeight n j
```

Alternatively define it through all height-one times whose canonical target is
`j`, provided contiguity is proved.

Prove:

```text
b <= a
for every t in [b, a):
  height(t) = 1
  carry(t) = 1

bitWidth (iterateT b n).1 =
  bitWidth (iterateT a n).1
```

The carry-one fact follows because `a` is the first delayed carry-two debt in
the target fiber.

# Stage I — prepare the pressure bridge

Use the maximal staircase, not merely the debt-supported suffix, for
block-length / exact-depth statements.

Expose its exact-depth profile:

```text
at time b + t:
  exact depth = j - (b + t) + 1
```

for the pre-payment interval.

Investigate count identities connecting maximal staircase lengths to:

```lean
orbitDepthRecoveryFiberCount
orbitDepthContinuationFiberCount
sourcePressureMarginInt_eq_continuationFiber_sub_recoveryFiber
```

Do not infer ambient positive pressure by dropping unrelated blocks.

# Autonomous continuation

Continue while:

```text
theorems follow from current Lean facts
debt-block and maximal-staircase starts remain distinct
reindexing preserves every interval endpoint
first-payment claims are not treated as final allocation
multiplicity and capacity remain explicit
no sorry or axiom is introduced
builds remain green
```

Continue into maximal-staircase and pressure-profile consequences when they
close naturally.

Stop only at a genuine mathematical obstruction or an API placement conflict.

# Validation

Build at least:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.PaymentBlockBridge
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
lake build DkMath
git diff --check
```

Record all autonomous progress and the exact remaining obstruction in:

```text
docs/dev/das-p2l-260607/review/report-petal-303.md
```
````

cp-302 は、block の内部構造を正しく捕まえた。

次は、この block 一個を通過したときの width 変化を完全に閉じ、その後に debt block の左側へ隠れている zero-drift prefix を掘り出す段階じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
index 2c03783b..9c081108 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
@@ -12,6 +12,7 @@ import DkMath.Collatz.PetalBridge.FloatWindow.PatternLedger
 import DkMath.Collatz.PetalBridge.FloatWindow.DriftBridge
 import DkMath.Collatz.PetalBridge.FloatWindow.PressureIncidenceBridge
 import DkMath.Collatz.PetalBridge.FloatWindow.PaymentMultiplicityBridge
+import DkMath.Collatz.PetalBridge.FloatWindow.PaymentBlockBridge

 #print "file: DkMath.Collatz.PetalBridge.FloatWindow"

diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/PaymentBlockBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/PaymentBlockBridge.lean
new file mode 100644
index 00000000..dbc3a8ef
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/PaymentBlockBridge.lean
@@ -0,0 +1,285 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.PaymentMultiplicityBridge
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.PaymentBlockBridge"
+
+namespace DkMath.Collatz
+
+/-!
+# Canonical first-payment blocks
+
+`FloatDebtPaymentDischarge` is retained as a proof-carrying name for backward
+compatibility.  The target it proves is a canonical *first payment claim*, not
+an allocation statement: a target fiber can be larger than that endpoint's
+extra-height capacity.  This module makes the entire first-claim block visible
+before any final allocation or transport theorem is attempted.
+-/
+
+/-- The canonical first source of a nonempty delayed-growth target fiber. -/
+noncomputable def floatPaymentBlockStart
+    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) : ℕ :=
+  (floatGrowthDebtFiberAt n j).min' h
+
+/-- The height-one part of a canonical payment block. -/
+noncomputable def floatPaymentBlockInterior
+    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) : Finset ℕ :=
+  Finset.Ico (floatPaymentBlockStart n j h) j
+
+/-- The complete canonical payment block, including its payment endpoint. -/
+noncomputable def floatPaymentBlockWithEndpoint
+    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) : Finset ℕ :=
+  Finset.Icc (floatPaymentBlockStart n j h) j
+
+/-- The carry-two subfamily of a finite collection of orbit times. -/
+noncomputable def carryTwoPositions (n : OddNat) (S : Finset ℕ) : Finset ℕ := by
+  classical
+  exact S.filter (CarryTwoDebtAt n)
+
+/-- Membership in a finite carry-two subfamily. -/
+theorem mem_carryTwoPositions_iff
+    {n : OddNat} {S : Finset ℕ} {i : ℕ} :
+    i ∈ carryTwoPositions n S ↔ i ∈ S ∧ CarryTwoDebtAt n i := by
+  classical
+  simp [carryTwoPositions]
+
+/-- The canonical block start is a delayed-growth debt targeting its endpoint. -/
+theorem floatPaymentBlockStart_mem_growthDebtFiber
+    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
+    floatPaymentBlockStart n j h ∈ floatGrowthDebtFiberAt n j :=
+  Finset.min'_mem _ h
+
+/-- The canonical block start carries the endpoint as its first-payment target. -/
+theorem floatPaymentBlockStart_target_eq
+    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
+    floatDebtPaymentTarget n (floatPaymentBlockStart n j h) = j :=
+  (mem_floatGrowthDebtFiberAt_iff.mp
+    (floatPaymentBlockStart_mem_growthDebtFiber n j h)).2.2
+
+/-- The canonical block start is strictly before its payment endpoint. -/
+theorem floatPaymentBlockStart_lt_endpoint
+    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
+    floatPaymentBlockStart n j h < j :=
+  lt_of_mem_floatGrowthDebtFiberAt (floatPaymentBlockStart_mem_growthDebtFiber n j h)
+
+/-- The canonical block has exact height one on every interior time. -/
+theorem orbitWindowHeight_eq_one_of_mem_floatPaymentBlockInterior
+    {n : OddNat} {j t : ℕ} {h : (floatGrowthDebtFiberAt n j).Nonempty}
+    (ht : t ∈ floatPaymentBlockInterior n j h) :
+    orbitWindowHeight n t = 1 := by
+  rcases Finset.mem_Ico.mp ht with ⟨hstart, htj⟩
+  let a := floatPaymentBlockStart n j h
+  have ha := floatPaymentBlockStart_mem_growthDebtFiber n j h
+  have hdebt : FloatDebtAt n a := (mem_floatGrowthDebtFiberAt_iff.mp ha).2.1
+  have htarget : floatDebtPaymentTarget n a = j :=
+    floatPaymentBlockStart_target_eq n j h
+  have hdepth := two_le_orbitExactDepth_of_floatDebtAt hdebt
+  have hexact : OrbitDepthRecoversExactlyAt n a (orbitExactDepth n a) := by rfl
+  rcases orbitDepthRecoversExactlyAt_prePayment_chain n a (orbitExactDepth n a)
+      hdepth hexact with ⟨hchain, _⟩
+  have hoff : t - a < orbitExactDepth n a - 1 := by
+    unfold floatDebtPaymentTarget at htarget
+    dsimp [a] at hstart htj htarget ⊢
+    omega
+  have hheight := (hchain (t - a) hoff).2
+  simpa [show a + (t - a) = t by omega] using hheight
+
+/-- The endpoint of a nonempty canonical block has an extra-height payment. -/
+theorem two_le_orbitWindowHeight_floatPaymentBlock_endpoint
+    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
+    2 ≤ orbitWindowHeight n j := by
+  let a := floatPaymentBlockStart n j h
+  have ha := floatPaymentBlockStart_mem_growthDebtFiber n j h
+  have hdebt : FloatDebtAt n a := (mem_floatGrowthDebtFiberAt_iff.mp ha).2.1
+  have htarget : floatDebtPaymentTarget n a = j :=
+    floatPaymentBlockStart_target_eq n j h
+  have hpay := floatDebtAt_paymentTarget hdebt
+  unfold PetalPaymentAt at hpay
+  rwa [htarget] at hpay
+
+/-- Every interior point of a canonical block has the same first-payment target. -/
+theorem floatDebtPaymentTarget_eq_endpoint_of_mem_floatPaymentBlockInterior
+    {n : OddNat} {j t : ℕ} {h : (floatGrowthDebtFiberAt n j).Nonempty}
+    (ht : t ∈ floatPaymentBlockInterior n j h) :
+    floatDebtPaymentTarget n t = j := by
+  rcases Finset.mem_Ico.mp ht with ⟨hstart, htj⟩
+  let a := floatPaymentBlockStart n j h
+  have ha := floatPaymentBlockStart_mem_growthDebtFiber n j h
+  have hdebt : FloatDebtAt n a := (mem_floatGrowthDebtFiberAt_iff.mp ha).2.1
+  have htarget : floatDebtPaymentTarget n a = j :=
+    floatPaymentBlockStart_target_eq n j h
+  have hdepth := two_le_orbitExactDepth_of_floatDebtAt hdebt
+  have hexact : OrbitDepthRecoversExactlyAt n a (orbitExactDepth n a) := by rfl
+  rcases orbitDepthRecoversExactlyAt_prePayment_chain n a (orbitExactDepth n a)
+      hdepth hexact with ⟨hchain, _⟩
+  have hoff : t - a < orbitExactDepth n a - 1 := by
+    unfold floatDebtPaymentTarget at htarget
+    dsimp [a] at hstart htj htarget ⊢
+    omega
+  have hrec := (hchain (t - a) hoff).1
+  have hdeptht : orbitExactDepth n t = orbitExactDepth n a - (t - a) := by
+    simpa [OrbitDepthRecoversExactlyAt, orbitExactDepth,
+      show a + (t - a) = t by omega] using hrec
+  unfold floatDebtPaymentTarget at htarget ⊢
+  dsimp [a] at hstart htj htarget hdeptht ⊢
+  omega
+
+/-- Every delayed debt with target `j` lies in the canonical interior block. -/
+theorem mem_floatPaymentBlockInterior_of_mem_growthDebtFiber
+    {n : OddNat} {i j : ℕ} {h : (floatGrowthDebtFiberAt n j).Nonempty}
+    (hi : i ∈ floatGrowthDebtFiberAt n j) :
+    i ∈ floatPaymentBlockInterior n j h := by
+  apply Finset.mem_Ico.mpr
+  constructor
+  · exact Finset.min'_le _ _ hi
+  · exact lt_of_mem_floatGrowthDebtFiberAt hi
+
+/-- Delayed debts targeting `j` are exactly carry-two positions in its full interior block. -/
+theorem mem_growthDebtFiber_iff_mem_floatPaymentBlockInterior_and_carryTwo
+    {n : OddNat} {i j : ℕ} {h : (floatGrowthDebtFiberAt n j).Nonempty} :
+    i ∈ floatGrowthDebtFiberAt n j ↔
+      i ∈ floatPaymentBlockInterior n j h ∧ CarryTwoDebtAt n i := by
+  constructor
+  · intro hi
+    refine ⟨mem_floatPaymentBlockInterior_of_mem_growthDebtFiber hi, ?_⟩
+    have hdebt := (mem_floatGrowthDebtFiberAt_iff.mp hi).2.1
+    exact ((floatDebtAt_iff_delayedCarryTwoDebtAt n i).mp hdebt).1
+  · rintro ⟨hblock, hcarry⟩
+    have hheight := orbitWindowHeight_eq_one_of_mem_floatPaymentBlockInterior hblock
+    have hdelayed : DelayedCarryTwoDebtAt n i := ⟨hcarry, hheight⟩
+    have hdebt : FloatDebtAt n i :=
+      (floatDebtAt_iff_delayedCarryTwoDebtAt n i).mpr hdelayed
+    apply mem_floatGrowthDebtFiberAt_iff.mpr
+    rcases Finset.mem_Ico.mp hblock with ⟨_, hij⟩
+    exact ⟨Nat.lt_succ_of_lt hij, hdebt,
+      floatDebtPaymentTarget_eq_endpoint_of_mem_floatPaymentBlockInterior hblock⟩
+
+/-- The delayed-growth fiber is the carry-two filter of the full height-one interior. -/
+theorem floatGrowthDebtFiberAt_eq_filter_floatPaymentBlockInterior_carryTwo
+    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
+    floatGrowthDebtFiberAt n j =
+      carryTwoPositions n (floatPaymentBlockInterior n j h) := by
+  ext i
+  rw [mem_carryTwoPositions_iff]
+  exact mem_growthDebtFiber_iff_mem_floatPaymentBlockInterior_and_carryTwo
+
+/-- A complete claim arriving at `j` is a carry-two position in the full block. -/
+theorem mem_carryTwoPaymentClaimFiber_iff_mem_floatPaymentBlockWithEndpoint_and_carryTwo
+    {n : OddNat} {i j : ℕ} {h : (floatGrowthDebtFiberAt n j).Nonempty} :
+    i ∈ carryTwoPaymentClaimFiberAt n j ↔
+      i ∈ floatPaymentBlockWithEndpoint n j h ∧ CarryTwoDebtAt n i := by
+  constructor
+  · intro hi
+    have hclaim := (mem_carryTwoPaymentClaimFiberAt_iff.mp hi).2
+    rcases hclaim with hdelayed | himmediate
+    · rcases hdelayed with ⟨hdelayed, htarget⟩
+      have hdebt : FloatDebtAt n i :=
+        (floatDebtAt_iff_delayedCarryTwoDebtAt n i).mpr hdelayed
+      have hfiber : i ∈ floatGrowthDebtFiberAt n j :=
+        (mem_floatGrowthDebtFiberAt_iff.mpr
+          ⟨by rw [htarget]; exact Nat.lt_succ_of_lt (floatDebtAt_lt_paymentTarget hdebt),
+            hdebt, htarget.symm⟩)
+      exact ⟨Finset.mem_Icc.mpr
+        ⟨Finset.min'_le _ _ hfiber, (lt_of_mem_floatGrowthDebtFiberAt hfiber).le⟩,
+        hdelayed.1⟩
+    · rcases himmediate with ⟨himmediate, hself⟩
+      subst j
+      exact ⟨Finset.mem_Icc.mpr
+        ⟨(floatPaymentBlockStart_lt_endpoint n i h).le, le_rfl⟩, himmediate.1⟩
+  · rintro ⟨hblock, hcarry⟩
+    rcases Finset.mem_Icc.mp hblock with ⟨hstart, hij⟩
+    rcases hij.eq_or_lt with heq | hij
+    · subst i
+      exact mem_carryTwoPaymentClaimFiberAt_of_claim
+        (Or.inr ⟨⟨hcarry, two_le_orbitWindowHeight_floatPaymentBlock_endpoint n j h⟩, rfl⟩)
+    · have hinterior : i ∈ floatPaymentBlockInterior n j h :=
+        Finset.mem_Ico.mpr ⟨hstart, hij⟩
+      have hheight := orbitWindowHeight_eq_one_of_mem_floatPaymentBlockInterior hinterior
+      have htarget :=
+        floatDebtPaymentTarget_eq_endpoint_of_mem_floatPaymentBlockInterior hinterior
+      exact mem_carryTwoPaymentClaimFiberAt_of_claim
+        (Or.inl ⟨⟨hcarry, hheight⟩, htarget.symm⟩)
+
+/-- The complete claim fiber is exactly the carry-two filter of the full block. -/
+theorem carryTwoPaymentClaimFiberAt_eq_filter_floatPaymentBlockWithEndpoint_carryTwo
+    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
+    carryTwoPaymentClaimFiberAt n j =
+      carryTwoPositions n (floatPaymentBlockWithEndpoint n j h) := by
+  ext i
+  rw [mem_carryTwoPositions_iff]
+  exact mem_carryTwoPaymentClaimFiber_iff_mem_floatPaymentBlockWithEndpoint_and_carryTwo
+
+/-- Cardinality form of the complete claim-fiber/block-filter identification. -/
+theorem carryTwoPaymentClaimFiberAt_card_eq_floatPaymentBlockWithEndpoint_carryTwo_card
+    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
+    (carryTwoPaymentClaimFiberAt n j).card =
+      (carryTwoPositions n (floatPaymentBlockWithEndpoint n j h)).card := by
+  exact congrArg Finset.card
+    (carryTwoPaymentClaimFiberAt_eq_filter_floatPaymentBlockWithEndpoint_carryTwo n j h)
+
+/-- Applying `T` commutes with a finite accelerated orbit prefix. -/
+theorem T_iterateT_eq_iterateT_T
+    (n : OddNat) (k : ℕ) :
+    T (iterateT k n) = iterateT k (T n) := by
+  rw [← iterateT_succ_eq_T_iterateT n k]
+  rfl
+
+/-- Iteration over a shifted orbit starts from the corresponding accelerated state. -/
+theorem iterateT_add_eq_iterateT_from_shift
+    (n : OddNat) (a len : ℕ) :
+    iterateT (a + len) n = iterateT len (iterateT a n) := by
+  induction a generalizing n with
+  | zero => simp [iterateT]
+  | succ a ih =>
+      calc
+        iterateT (a + 1 + len) n = T (iterateT (a + len) n) := by
+          rw [show a + 1 + len = a + len + 1 by omega,
+            iterateT_succ_eq_T_iterateT]
+        _ = T (iterateT len (iterateT a n)) := by rw [ih]
+        _ = iterateT len (T (iterateT a n)) := T_iterateT_eq_iterateT_T _ _
+        _ = iterateT len (iterateT (a + 1) n) := by
+          rw [iterateT_succ_eq_T_iterateT]
+
+/-- Carry-two count on the half-open orbit segment `[a, a + len)`. -/
+noncomputable def shiftedOrbitCarryTwoCount
+    (n : OddNat) (a len : ℕ) : ℕ :=
+  orbitWindowUpperCarryCountEqTwo (iterateT a n) len
+
+/-- Extra-height capacity on the half-open orbit segment `[a, a + len)`. -/
+noncomputable def shiftedExtraPaymentCapacity
+    (n : OddNat) (a len : ℕ) : ℕ :=
+  sumExtraHeight (iterateT a n) len
+
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
+/-!
+## Ledger frontier
+
+The block and its complete first-claim fiber are now canonical, and the
+existing prefix ledger has been repackaged as a shifted segment ledger.
+To obtain the proposed endpoint-only block identity, the remaining task is a
+reindexing theorem: identify the shifted carry count on `[a, j + 1)` with the
+canonical claim fiber, and identify its shifted extra-height sum with the
+single endpoint capacity.  The latter needs a finite-sum transport lemma from
+the interior height-one theorem.  No claim allocation or ambient pressure
+conclusion is inferred before those two exact identifications are proved.
+-/
+
+end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-302.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-302.md
new file mode 100644
index 00000000..a17c96da
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-302.md
@@ -0,0 +1,96 @@
+# cp-302: Canonical payment blocks
+
+## Result
+
+Added `DkMath.Collatz.PetalBridge.FloatWindow.PaymentBlockBridge` and exported
+it through `DkMath.Collatz.PetalBridge.FloatWindow`.
+
+The module corrects the semantic reading of the old `PaymentDischarge` name:
+it provides a proof of a canonical first-payment claim and target, not a final
+capacity allocation for every source in a colliding fiber.
+
+## Established block geometry
+
+For a nonempty delayed-growth target fiber at endpoint `j`, the canonical block
+start is its least source index:
+
+```text
+a = min (floatGrowthDebtFiberAt n j)
+```
+
+The canonical block is split into:
+
+```text
+interior: [a, j)   -- exact height one
+endpoint: j        -- height at least two
+full block: [a, j]
+```
+
+The following are now formal facts.
+
+- Every interior time has `orbitWindowHeight = 1`.
+- The endpoint has `orbitWindowHeight >= 2`.
+- Every interior time has first-payment target `j`.
+- Every delayed Float debt targeting `j` lies in the interior.
+- The delayed debt fiber is exactly the carry-two filter of the interior.
+- The complete carry-two claim fiber at `j` is exactly the carry-two filter of
+  the full block, including a carry-two endpoint precisely as an immediate
+  self-claim.
+
+Thus the block includes every intervening height-one state, including
+carry-one states.  It is not merely the set of already-selected debts.
+
+## Shifted ledger
+
+Added the iterate transport theorem:
+
+```text
+iterateT (a + len) n = iterateT len (iterateT a n)
+```
+
+and the exact segment ledger:
+
+```text
+width(a + len) + shiftedExtraPaymentCapacity(a, len)
+  = width(a) + shiftedOrbitCarryTwoCount(a, len)
+```
+
+This is obtained by applying the established prefix ledger to `iterateT a n`;
+no duplicate induction over a segment was introduced.
+
+## Remaining boundary
+
+The intended endpoint-only payment-block identity still needs two explicit
+reindexing theorems:
+
+```text
+shifted carry-two count on [a, j + 1)
+  = card of the full canonical claim fiber
+
+shifted extra-height sum on [a, j + 1)
+  = extraPaymentCapacityAt j
+```
+
+The second equality uses the block fact that all interior heights are one.
+The first equality transports the recursive count, based at `iterateT a n`,
+to global interval coordinates.  Neither transport should be hidden in a
+rewrite; they are reusable finite-orbit reindexing lemmas and deserve a small
+separate API.
+
+No theorem claiming `overload <-> block width growth` is made until both
+identities are proven.  In particular, no first-payment claim is treated as a
+final allocation.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.FloatWindow.PaymentBlockBridge
+lake build DkMath.Collatz.PetalBridge.FloatWindow
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath
+git diff --check
+```
+
+No `sorry` or `axiom` was introduced in `PaymentBlockBridge.lean`.
````
`````
