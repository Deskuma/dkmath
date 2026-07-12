# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.FloatWindow.PaymentMultiplicityBridge

gch: 0a0812d18b607d3e98e4c67afa27cf76fe702b46

## Report

cp-301 を、実証可能な行き止まりまで進めました。

新規 [PaymentMultiplicityBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/PaymentMultiplicityBridge.lean) を公開入口へ export しました。

確定した事実:

- delayed payment は canonical target `i + A_i - 1` に一意に定まる。
- `FloatDebtPaymentDischarge` はその target map の graph と同値。
- 同一 target の debt collision は、有限 debt fiber の card が `2` 以上であることと同値。
- `extraPaymentCapacityAt = height - 1` を定義し、overload は collision を含意する。ただし collision の逆は主張していない。
- carry-two 全体を delayed と immediate self-paid に分解し、完全 claim fiber とその overload/collision を定義した。
- 同一 target の二つの順序付き Float debt は、前者から後者まで exact-height-one の descending staircase 上に並ぶ。

行き止まりも明確です。diagonal target fiber と既存の `List.range k` 上の horizontal pressure を結ぶ局所 source-set API がまだありません。従って `overload -> positive pressure` は証明していません。これは欠落ではなく、無関係な recovery source を勝手に捨てないための正しい境界です。

結果は [report-petal-301.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-301.md) に記録しました。

検証済み: 新規モジュール、`FloatWindow`、`PetalBridge`、トップレベル `DkMath`、`git diff --check`。新規モジュールに `sorry` / `axiom` はありません。

## Review

## 結論

**採用。cp-301 は、上位 debt と下位 payment を「点」ではなく「有限 fiber」として扱える段階まで進めた。**

特に重要なのは次の四点じゃ。

- delayed debt の支払候補時刻が canonical target として一意になった
- 同一 target に集まる debt multiplicity が `Finset.card` になった
- target coincidence と capacity overload を分離した
- carry-two 全体を delayed / immediate の二枝に分け、完全 claim fiber を作った

同一 target の debt が一つの exact-depth staircase 上に並ぶことまで Lean で固定されたのも強い。添付 report では、新規モジュールからトップレベル `DkMath` までの build、`git diff --check`、no-`sorry` / no-`axiom` が報告されている。

ただし、今回の成果によって一段先が見えた。

> 次に必要なのは、直ちに任意 `Finset` 上の localized pressure を作ることではない。
> まず canonical payment target を中心とした **payment block の完全な幅会計** を作るべきじゃ。

そして、現在 `Discharge` と呼んでいるものは、multiplicity が発生した場合には「完全な返済」ではなく、

> **最初の支払機会・最初の claim target**

と読むのが正確じゃ。

---

## 1. pre-payment staircase は完成

追加された、

```lean
orbitDepthRecoversExactlyAt_prePayment_chain
```

は前回残っていた firstness をきれいに閉じた。

exact all-ones depth が $d\ge2$ なら、支払時刻より前では、

$$
0\le t<d-1\Longrightarrow A_{i+t}=d-t
$$

かつ、

$$
0\le t<d-1\Longrightarrow h_{i+t}=1
$$

そして endpoint で、

$$
2\le h_{i+d-1}
$$

となる。

したがって、

$$
\tau(i):=i+A_i-1
$$

は単に「どこか将来の payment」ではない。

> **途中に extra-height capacity が一つも存在しない、最初の強制 payment 時刻**

である。

これはかなり重要じゃ。

---

## 2. canonical target と graph theorem

```lean
floatDebtPaymentTarget
```

が、

$$
\tau(i)=i+A_i-1
$$

として定義された。

さらに、

```lean
floatDebtPaymentDischarge_iff_target
```

により、

$$
\operatorname{FloatDebtPaymentDischarge}(i,j)
$$

が、

$$
\operatorname{FloatDebtAt}(i)\land j=\tau(i)
$$

と同値になった。

これで relation と function が両方揃った。

- function は target fiber を作れる
- relation は payment の存在証明を保持する

前回指摘した設計が正しく実装されている。

---

## 3. debt fiber は正しい

```lean
floatGrowthDebtFiberAt n j
```

は、target $j$ を持つ strict width-growth debt の有限集合じゃ。

各 member は必ず、

$$
i<j
$$

を満たす。

これは delayed debt の target が真に未来であることを示している。

そして、

```lean
floatPaymentCollisionAt_iff_two_le_growthDebtFiberCard
```

により、

$$
\operatorname{FloatPaymentCollisionAt}(j)
\Longleftrightarrow
2\le\#\operatorname{GrowthDebtFiber}(j)
$$

が確定した。

collision predicate が存在量から cardinality へ移ったので、これ以降は本格的な有限会計ができる。

---

## 4. collision と overload の分離

capacity は、

```lean
extraPaymentCapacityAt n j
```

として、

$$
P_j:=h_j-1
$$

と定義された。

delayed debt load を、

$$
D_j:=\#\operatorname{GrowthDebtFiber}(j)
$$

とすれば、overload は、

$$
P_j<D_j
$$

じゃ。

実装は、

```lean
FloatPaymentOverloadAt
```

としてこれを固定し、

$$
\operatorname{Overload}(j)\Longrightarrow\operatorname{Collision}(j)
$$

だけを証明した。

逆を証明しなかったのは正しい。

二つの debt が同じ target に集まっても、

$$
P_j\ge2
$$

なら capacity 内に収まるからじゃ。

ここは cp-301 の最も良い判断の一つである。

---

## 5. 同一 target の diagonal geometry

同じ target を持つ $i_1<i_2$ に対して、

$$
A_{i_1}=A_{i_2}+(i_2-i_1)
$$

が証明された。

さらに、

```lean
floatDebtAt_same_paymentTarget_staircase_to_later_source
```

は、$i_1$ から $i_2$ までの全時刻が、同じ下降 staircase 上にあることを示す。

すなわち、

$$
A_{i_1+t}=A_{i_1}-t
$$

であり、その区間の height は全て $1$ じゃ。

これは非常に強い。

同一 target fiber は、散らばった無関係な debt の集合ではない。

> **一つの連続する height-one block の中に存在する carry-two 点群**

だった。

ここで pressure と Float が、初めて幾何学的に同じ図へ載った。

---

## 6. carry-two 全体の claim ledger

carry-two event は、

```lean
CarryTwoDebtAt
```

として定義され、

```text
DelayedCarryTwoDebtAt
ImmediateCarryTwoDebtAt
```

へ分解された。

数学的には、

```text
carry 2 ∧ height 1
  -> width-growth debt
  -> future target を claim

carry 2 ∧ height >= 2
  -> 同じ時刻に extra capacity がある
  -> current time を claim
```

じゃ。

そして、

```lean
CarryTwoPaymentClaim
carryTwoPaymentClaimFiberAt
CarryTwoPaymentClaimCollisionAt
CarryTwoPaymentOverloadAt
```

が追加された。

これは前段の exact ledger、

$$
w_k+\operatorname{ExtraHeight}_k = w_0+\operatorname{CarryTwoCount}_k
$$

と対応する完全な claim vocabulary になっている。

---

## 7. 重要な意味補正――`Discharge` はまだ完全返済ではない

コードの論理は正しい。

だが `FloatDebtPaymentDischarge` という名前は、現段階では少し強く聞こえる。

target に payment capacity が存在することは証明されている。

しかし fiber が overload していれば、その target で全 debt を同時に返済することはできない。

具体例を挙げよう。

加速 odd 軌道、

$$
7\longmapsto11\longmapsto17\longmapsto13\longmapsto5
$$

を見る。

### 時刻 0

$$
A_0=v_2(7+1)=3
$$

したがって、

$$
\tau(0)=0+3-1=2
$$

さらに $7$ は carry-two / height-one なので debt じゃ。

### 時刻 1

$$
A_1=v_2(11+1)=2
$$

したがって、

$$
\tau(1)=1+2-1=2
$$

$11$ も carry-two / height-one debt じゃ。

よって target $j=2$ には二つの claim が集まる。

$$
D_2=2
$$

target state は $17$ で、

$$
h_2=v_2(3\cdot17+1)=v_2(52)=2
$$

したがって capacity は、

$$
P_2=h_2-1=1
$$

ゆえに、

$$
D_2-P_2=1
$$

の overload が残る。

次の $13$ では、

$$
h_3=v_2(40)=3
$$

なので capacity は $2$ ある。

しかも $13$ 自身は carry-two なので、そのうち一単位を immediate claim が使い、残る一単位が前 block の余剰 debt を吸収できる。

つまり target $2$ は、

> 二 debt に共通する最初の payment opportunity

ではあるが、二 debt 全ての final discharge ではない。

したがって今後は意味上、

```text
FloatDebtPaymentDischarge
```

を、

```text
first payment claim
first payment opportunity
canonical first-payment target
```

として読むのが正確じゃ。

既存名を今すぐ大量 rename する必要はないが、docstring と report には補足した方がよい。

---

## 8. `complete claim fiber` も「最初の claim ledger」

`CarryTwoPaymentClaim` は、全 carry-two event を一度ずつ target へ送っている。

したがって **source debt の完全列挙**としては正しい。

しかし overload で余った claim を、次の payment slot へ移送する機構はまだない。

よって現在の complete claim fiber は、

> **各 debt の first claim target の完全 ledger**

じゃ。

まだ、

> 実際にどの capacity unit がどの debt を消すか

という allocation / carry-over ledger ではない。

ここを区別すると次の攻め筋がはっきりする。

---

## 9. report の次手を修正

report は次に、

```text
generic finite-source-set pressure API
```

が必要だとしている。

これは将来的には有用じゃ。

だが、いきなり任意 `Finset` へ一般化するのは危険がある。

任意の source set から都合の悪い recovery source を除けば、localized pressure を人工的に正へできてしまう。

例えば exact depth が全て $2$ 以上の debt source だけを選べば、depth $1$ の recovery はゼロで continuation だけが残る。

それは正しい局所数値ではあるが、ambient pressure の正性を意味しない。

したがって次の source set は、恣意的な `Finset` ではなく、

> **一つの canonical payment block**

でなければならない。

---

## 10. 次の中心――Payment Block

同じ target $j$ へ向かう source は、一つの descending staircase 上に並ぶ。

その staircase の開始を $a$ とする。

区間、

$$
[a,j)
$$

では全 height が $1$。

endpoint $j$ で初めて、

$$
2\le h_j
$$

となる。

この block 内では、各 step の exact width balance が、

$$
w_{t+1} - w_t = \mathbf 1_{\operatorname{carryTwo}(t)}-(h_t-1)
$$

となる。

途中では $h_t-1=0$ なので、block 全体を足すと、

$$
w_{j+1} - w_a = \#\{\text{carry-two claims in the block}\}-(h_j-1)
$$

となる。

complete claim fiber の cardinality を $Q_j$ とすれば、狙うべき中心等式は、

$$
w_{j+1}-w_a=Q_j-P_j
$$

じゃ。

したがって、

$$
P_j<Q_j
\Longleftrightarrow
w_a<w_{j+1}
$$

となる。

つまり、

> **payment overload とは、一つの完全な height-one / payment cycle を通過した後にも bit width が純増していること**

である。

これは pressure へ行く前に必ず固定すべき theorem じゃ。

---

## 11. $7$ の例も block identity で閉じる

最初の block は、

```text
7 -> 11 -> 17 -> 13
```

であり、source $a=0$、payment endpoint $j=2$。

claim は $7,11$ の二つ。

capacity は $17$ の一つ。

したがって、

$$
w(13)-w(7)=2-1=1
$$

実際に、

$$
4-3=1
$$

じゃ。

次の block は $13$ 単体の immediate claim を含み、

$$
w(5)-w(13)=1-2=-1
$$

実際に、

$$
3-4=-1
$$

となる。

二 block を合わせると width は元へ戻る。

これが、余剰 debt の持ち越しと後続 capacity の吸収を、値そのものを追わずに示す会計じゃ。

---

## 12. pressure は block-length histogram になる

payment block の height-one 部分の長さを $L$ とする。

その block 内の exact depths は、

$$
L+1,L,\ldots,3,2
$$

と一段ずつ減る。

したがって、exact-depth recovery fiber は、

> 長さが少なくとも $d-1$ ある payment block の個数

として読める。

一方、continuation fiber は、

> その depth を越えてまだ残り距離を持つ block position の総数

じゃ。

ゆえに pressure、

$$
M_d=C_d-E_d
$$

は、

> 支払までの残り距離が長い block の tail mass と、そこで終了する block 数との差

となる。

これは非常に大きな再解釈じゃ。

```text
Float target fiber:
  一つの block 内の carry-two 密度

Pressure depth fiber:
  payment block 長の分布
```

上位 Float は block 内の debt 密度を測る。

下位 pressure は block の長さ分布を測る。

これこそ本来の挟み撃ちじゃ。

---

## 13. 判定

## pre-payment chain

**完成。**

first payment であることまで固定された。

## canonical target

**完成。**

relation が target function の graph になった。

## multiplicity

**完成。**

collision と fiber cardinality が同値になった。

## capacity

**完成。**

collision と overload が正しく分離された。

## diagonal geometry

**完成。**

同一 target source は一つの staircase 上に並ぶ。

## complete carry-two claim

**source debt の完全列挙として完成。**

ただし actual allocation / overflow transport は未完成。

## localized pressure

**まだ着手しなくてよい。**

先に canonical payment block と block width balance を固定すべきじゃ。

---

## 14. 次の Codex 指示

次は `PaymentBlockBridge.lean` が本線になる。

任意 `Finset` pressure を先に作らず、canonical payment block、block drift、overflow transport を先に閉じる。

````text
You are continuing the DkMath Collatz / PetalBridge Float-window branch after
report-petal-301.

The current implementation has completed:

```text
exact pre-payment staircases
canonical first-payment targets
finite target fibers
collision versus capacity overload
complete first-claim fibers for all carry-two events
same-target diagonal geometry
```

The next task is to convert one target fiber into an exact finite payment-block
width ledger.

The historical checkpoint number is not a stopping boundary. Continue
autonomously through all logically justified stages.

# Primary target module

Create:

```text
DkMath/Collatz/PetalBridge/FloatWindow/PaymentBlockBridge.lean
```

Export it through:

```text
DkMath.Collatz.PetalBridge.FloatWindow
```

# Semantic correction

The existing declarations named with `PaymentDischarge` are logically sound,
but they currently prove a canonical first payment opportunity/claim.

When several debts target one slot and capacity is insufficient, not every
debt is completely discharged there.

Do not perform a disruptive rename unless it is clearly beneficial. Add
documentation or compatibility aliases making the intended meaning explicit:

```text
canonical first-payment target
first payment claim
not yet a capacity allocation
```

# Stage A — canonical height-one payment block

A payment block ending at `j` consists of:

```text
a consecutive height-one run before j
followed by height at least two at j
```

Reuse:

```lean
orbitDepthRecoversExactlyAt_prePayment_chain
floatDebtAt_same_paymentTarget_staircase_to_later_source
floatDebtPaymentTarget
```

Do not use an arbitrary source Finset as the primary object.

Develop either:

1. a proof-carrying `PaymentBlock` structure; or
2. a canonical interval derived from the target fiber / exact-depth staircase.

The block API must expose:

```text
start time a
payment endpoint j
for a <= t < j: height(t) = 1
at j: 2 <= height(j)
```

When a block is maximal on the left, expose that fact separately.

# Stage B — all height-one sources in one block have one target

Prove that every height-one source in the canonical block has:

```text
floatDebtPaymentTarget n t = j
```

Conversely, every delayed debt targeting `j` lies inside that block.

Show that the delayed-growth debt fiber is exactly the carry-two filter of the
height-one part of the block.

Do not count only the already-known debt sources while ignoring intervening
carry-one / height-one states.

# Stage C — complete claim fiber on one block

At the endpoint `j`, include the immediate carry-two claim exactly when:

```text
stateUpperCarry (iterateT j n).1 = 2
```

Prove that:

```text
carryTwoPaymentClaimFiberAt n j
```

is exactly:

```text
carry-two positions in the full block [a, j]
```

where the endpoint is included and the pre-payment interval is height one.

Expose a cardinality theorem.

# Stage D — shifted finite width ledger

Prove a segment form of the exact Float ledger.

For arbitrary start `a` and length `len`, derive an integer or subtraction-free
identity equivalent to:

```text
width at a + len
  - width at a
=
carry-two count on [a, a + len)
  - extra-height capacity on [a, a + len)
```

Prefer applying the existing orbit ledger to:

```lean
iterateT a n
```

rather than duplicating the induction.

Add any missing iterate-shift lemmas cleanly.

# Stage E — exact payment-block balance

For a canonical block from `a` through endpoint `j`, all pre-endpoint
extra-height capacities are zero.

Therefore prove the central identity:

```text
width after processing j
  + extraPaymentCapacityAt n j
=
width at block start
  + (carryTwoPaymentClaimFiberAt n j).card
```

Equivalently in integers:

```text
width after block - width before block
  =
claim fiber card - endpoint capacity
```

# Stage F — overload iff block width growth

Derive:

```text
CarryTwoPaymentOverloadAt n j
  <->
bitWidth (iterateT a n).1 <
  bitWidth (iterateT (j + 1) n).1
```

for the canonical block start `a`.

Also derive the equality and decrease branches:

```text
claims = capacity -> block width preserved
claims < capacity -> block width decreases
claims > capacity -> block width increases
```

This theorem is the direct upper/lower squeeze result for one complete payment
cycle.

# Stage G — overflow transport / prefix balance

A first target can be overloaded, and the excess may be absorbed by a later
payment block.

Define an exact signed block balance or prefix balance rather than pretending
that every first claim is fully discharged.

Useful quantities include:

```text
block load
block capacity
block net drift
prefix carry-two debt
prefix extra-height payment
signed outstanding balance
```

Prove that summing block net drifts reproduces the existing orbit-width ledger.

Investigate a canonical pending-debt or signed-credit API. Preserve negative
surplus rather than truncating it silently.

# Stage H — payment-block length and pressure fibers

Only after the block ledger is stable, connect pressure.

A height-one block of length `L` has exact-depth profile:

```text
L + 1, L, ..., 3, 2
```

Formalize this profile and investigate count identities of the form:

```text
exact-depth recovery count at d
  = number of relevant payment blocks with length at least d - 1
```

and:

```text
continuation fiber at d
  = tail mass of remaining block lengths beyond d
```

Use:

```lean
sourcePressureMarginInt_eq_continuationFiber_sub_recoveryFiber
```

to interpret pressure as a payment-block-length tail imbalance.

# Stage I — localized pressure restrictions

Do not introduce arbitrary source-set pressure merely to manufacture a positive
margin.

When a localized pressure API becomes necessary, prefer canonical contiguous
orbit intervals or canonical payment blocks.

If a generic Finset API is introduced, it must additionally provide:

```text
specialization to canonical payment blocks
decomposition into the ambient orbit window
explicit complement contribution
```

No theorem may infer ambient positive pressure after silently discarding
unrelated recovery sources.

# Autonomous continuation

Continue while:

```text
theorems follow from current Lean facts
first payment opportunity is not confused with final allocation
all intermediate height-one states are retained
multiplicity and capacity remain explicit
block boundaries are canonical
time, depth, and target coordinates remain distinct
no sorry or axiom is introduced
builds remain green
```

Continue into pressure/block-length consequences when they close naturally.

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
docs/dev/das-p2l-260607/review/report-petal-302.md
```
````

cp-301 によって、魚が同じ網目へ集まったことは数えられるようになった。

次は、その網目一つが **どれだけの debt を受け、どれだけの capacity で返し、通過後に width が増えたか**を完全に測る段階じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
index 947d19a8..2c03783b 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
@@ -11,6 +11,7 @@ import DkMath.Collatz.PetalBridge.FloatWindow.OrbitBalance
 import DkMath.Collatz.PetalBridge.FloatWindow.PatternLedger
 import DkMath.Collatz.PetalBridge.FloatWindow.DriftBridge
 import DkMath.Collatz.PetalBridge.FloatWindow.PressureIncidenceBridge
+import DkMath.Collatz.PetalBridge.FloatWindow.PaymentMultiplicityBridge
 
 #print "file: DkMath.Collatz.PetalBridge.FloatWindow"
 
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/PaymentMultiplicityBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/PaymentMultiplicityBridge.lean
new file mode 100644
index 00000000..afb04796
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/PaymentMultiplicityBridge.lean
@@ -0,0 +1,481 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.PressureIncidenceBridge
+import DkMath.Collatz.PetalBridge.FloatWindow.OrbitBalance
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.PaymentMultiplicityBridge"
+
+namespace DkMath.Collatz
+
+/-!
+# Delayed-payment multiplicity
+
+This module separates three different coordinates which must not be identified:
+
+* source time `i`;
+* exact all-ones depth `A_i`;
+* payment time `i + A_i - 1`.
+
+The target map is deliberately allowed to be noninjective.  Its fibers record
+the multiplicity that a later capacity theorem must compare with the extra
+height available at the target slot.
+-/
+
+/-- The exact all-ones depth at an orbit time. -/
+noncomputable def orbitExactDepth (n : OddNat) (i : ℕ) : ℕ :=
+  ResidualAllOnesDepth (oddOrbitLabel n i)
+
+/-- The deterministic delayed-payment target of a Float width-growth debt. -/
+noncomputable def floatDebtPaymentTarget (n : OddNat) (i : ℕ) : ℕ :=
+  i + orbitExactDepth n i - 1
+
+/-- Exact recovery at depth at least two is an exact-height-one source event. -/
+theorem orbitDepthRecoversExactlyAt_height_eq_one
+    (n : OddNat) (i d : ℕ)
+    (hd : 2 ≤ d)
+    (h : OrbitDepthRecoversExactlyAt n i d) :
+    orbitWindowHeight n i = 1 := by
+  have hrec := (orbitDepthRecoversExactlyAt_iff_recoverySibling n i d).1 h
+  apply (orbitWindowHeight_eq_one_iff_mod_four_eq_three n i).2
+  have hfour : 4 ∣ 2 ^ (d + 1) := by
+    rcases exists_add_of_le hd with ⟨e, he⟩
+    rw [he, show (2 + e + 1 : ℕ) = 2 + (e + 1) by omega, pow_add]
+    norm_num
+  rw [mod_eq_mod_of_dvd_modulus hfour, hrec]
+  rcases exists_add_of_le hd with ⟨e, he⟩
+  rw [he, pow_add]
+  have hpow : 0 < 2 ^ e := pow_pos (by norm_num) e
+  have hsplit : 4 * 2 ^ e - 1 = 3 + (2 ^ e - 1) * 4 := by omega
+  norm_num
+  rw [hsplit, Nat.add_mul_mod_self_right]
+
+/--
+The complete exact-depth staircase before its forced extra-height payment.
+
+For every proper pre-payment offset, the remaining depth is exact and the
+observed height is exactly one.  The endpoint is separately known to have
+height at least two.
+-/
+theorem orbitDepthRecoversExactlyAt_prePayment_chain
+    (n : OddNat) (i d : ℕ)
+    (hd : 2 ≤ d)
+    (hexact : OrbitDepthRecoversExactlyAt n i d) :
+    (∀ t, t < d - 1 →
+      OrbitDepthRecoversExactlyAt n (i + t) (d - t) ∧
+        orbitWindowHeight n (i + t) = 1) ∧
+      2 ≤ orbitWindowHeight n (i + d - 1) := by
+  have hstair : ∀ t, t ≤ d - 2 →
+      OrbitDepthRecoversExactlyAt n (i + t) (d - t) := by
+    intro t ht
+    induction t with
+    | zero => simpa using hexact
+    | succ t iht =>
+      have ht' : t ≤ d - 2 := by omega
+      have hprev := iht ht'
+      have hdepth : 3 ≤ d - t := by omega
+      have hnext := orbitDepthRecoversExactlyAt_succ_of_three_le
+        n (i + t) (d - t) hdepth hprev
+      simpa [show i + (t + 1) = i + t + 1 by omega,
+        show d - (t + 1) = (d - t) - 1 by omega] using hnext
+  constructor
+  · intro t ht
+    have ht' : t ≤ d - 2 := by omega
+    have hrec := hstair t ht'
+    refine ⟨hrec, orbitDepthRecoversExactlyAt_height_eq_one n (i + t) (d - t) ?_ hrec⟩
+    omega
+  · exact orbitDepthRecoversExactlyAt_delayed_height_two_le n i d hd hexact
+
+/-- The discharge relation has the unique canonical target fixed by exact depth. -/
+theorem floatDebtPaymentDischarge_target_eq
+    {n : OddNat} {i j : ℕ}
+    (h : FloatDebtPaymentDischarge n i j) :
+    j = floatDebtPaymentTarget n i := by
+  rcases h with ⟨_, depth, _, hexact, hj, _⟩
+  have hdepth : depth = orbitExactDepth n i := by
+    simpa [OrbitDepthRecoversExactlyAt, orbitExactDepth] using hexact.symm
+  rw [hdepth] at hj
+  simpa [floatDebtPaymentTarget] using hj
+
+/-- Every Float growth debt reaches its canonical delayed-payment target. -/
+theorem floatDebtAt_paymentDischarge_target
+    {n : OddNat} {i : ℕ}
+    (h : FloatDebtAt n i) :
+    FloatDebtPaymentDischarge n i (floatDebtPaymentTarget n i) := by
+  rcases floatDebtAt_exists_paymentDischarge n i h with ⟨j, hj⟩
+  rw [floatDebtPaymentDischarge_target_eq hj] at hj
+  exact hj
+
+/-- The proof-carrying delayed discharge relation is the graph of the target map. -/
+theorem floatDebtPaymentDischarge_iff_target
+    {n : OddNat} {i j : ℕ} :
+    FloatDebtPaymentDischarge n i j ↔
+      FloatDebtAt n i ∧ j = floatDebtPaymentTarget n i := by
+  constructor
+  · intro h
+    exact ⟨h.1, floatDebtPaymentDischarge_target_eq h⟩
+  · rintro ⟨hdebt, htarget⟩
+    rw [htarget]
+    exact floatDebtAt_paymentDischarge_target hdebt
+
+/-- The canonical target is an actual extra-height payment for every Float debt. -/
+theorem floatDebtAt_paymentTarget
+    {n : OddNat} {i : ℕ}
+    (h : FloatDebtAt n i) :
+    PetalPaymentAt n (floatDebtPaymentTarget n i) := by
+  rcases floatDebtAt_paymentDischarge_target h with ⟨_, _, _, _, _, hpay⟩
+  exact hpay
+
+/-- A Float growth debt is strictly before its delayed payment target. -/
+theorem floatDebtAt_lt_paymentTarget
+    {n : OddNat} {i : ℕ}
+    (h : FloatDebtAt n i) :
+    i < floatDebtPaymentTarget n i := by
+  rcases floatDebtAt_paymentDischarge_target h with ⟨_, depth, hdepth, _, htarget, _⟩
+  rw [htarget]
+  omega
+
+/-- Finite fiber of Float debts having canonical delayed payment target `j`. -/
+noncomputable def floatGrowthDebtFiberAt
+    (n : OddNat) (j : ℕ) : Finset ℕ := by
+  classical
+  exact (Finset.range (j + 1)).filter fun i =>
+    FloatDebtAt n i ∧ floatDebtPaymentTarget n i = j
+
+/-- Membership in a delayed-growth debt fiber. -/
+theorem mem_floatGrowthDebtFiberAt_iff
+    {n : OddNat} {i j : ℕ} :
+    i ∈ floatGrowthDebtFiberAt n j ↔
+      i < j + 1 ∧ FloatDebtAt n i ∧ floatDebtPaymentTarget n i = j := by
+  simp [floatGrowthDebtFiberAt]
+
+/-- Every debt in the fiber is strictly earlier than its payment slot. -/
+theorem lt_of_mem_floatGrowthDebtFiberAt
+    {n : OddNat} {i j : ℕ}
+    (h : i ∈ floatGrowthDebtFiberAt n j) :
+    i < j := by
+  rcases (mem_floatGrowthDebtFiberAt_iff.mp h) with ⟨_, hdebt, htarget⟩
+  rw [← htarget]
+  exact floatDebtAt_lt_paymentTarget hdebt
+
+/-- A canonical debt belongs to the fiber over its own payment target. -/
+theorem mem_floatGrowthDebtFiberAt_paymentTarget
+    {n : OddNat} {i : ℕ}
+    (h : FloatDebtAt n i) :
+    i ∈ floatGrowthDebtFiberAt n (floatDebtPaymentTarget n i) := by
+  apply mem_floatGrowthDebtFiberAt_iff.mpr
+  exact ⟨Nat.lt_succ_of_lt (floatDebtAt_lt_paymentTarget h), h, rfl⟩
+
+/-- A target collision gives two distinct elements of its canonical debt fiber. -/
+theorem FloatPaymentCollisionAt.exists_distinct_mem_growthDebtFiber
+    {n : OddNat} {j : ℕ}
+    (h : FloatPaymentCollisionAt n j) :
+    ∃ i₁ i₂, i₁ ≠ i₂ ∧
+      i₁ ∈ floatGrowthDebtFiberAt n j ∧ i₂ ∈ floatGrowthDebtFiberAt n j := by
+  rcases h with ⟨i₁, i₂, hne, h₁, h₂⟩
+  refine ⟨i₁, i₂, hne, ?_, ?_⟩
+  · apply mem_floatGrowthDebtFiberAt_iff.mpr
+    rcases h₁ with ⟨hdebt, depth, _, _, htarget, _⟩
+    exact ⟨by omega, hdebt,
+      (floatDebtPaymentDischarge_target_eq
+        ⟨hdebt, depth, by omega, by assumption, htarget, by assumption⟩).symm⟩
+  · apply mem_floatGrowthDebtFiberAt_iff.mpr
+    rcases h₂ with ⟨hdebt, depth, _, _, htarget, _⟩
+    exact ⟨by omega, hdebt,
+      (floatDebtPaymentDischarge_target_eq
+        ⟨hdebt, depth, by omega, by assumption, htarget, by assumption⟩).symm⟩
+
+/-- A target collision is exactly a delayed-growth debt fiber of size at least two. -/
+theorem floatPaymentCollisionAt_iff_two_le_growthDebtFiberCard
+    {n : OddNat} {j : ℕ} :
+    FloatPaymentCollisionAt n j ↔ 2 ≤ (floatGrowthDebtFiberAt n j).card := by
+  constructor
+  · intro h
+    rcases h.exists_distinct_mem_growthDebtFiber with ⟨i₁, i₂, hne, hi₁, hi₂⟩
+    have hcard : 1 < (floatGrowthDebtFiberAt n j).card :=
+      Finset.one_lt_card.mpr ⟨i₁, hi₁, i₂, hi₂, hne⟩
+    omega
+  · intro hcard
+    rcases Finset.one_lt_card.mp (by omega : 1 < (floatGrowthDebtFiberAt n j).card)
+      with ⟨i₁, hi₁, i₂, hi₂, hne⟩
+    rcases mem_floatGrowthDebtFiberAt_iff.mp hi₁ with ⟨_, hdebt₁, htarget₁⟩
+    rcases mem_floatGrowthDebtFiberAt_iff.mp hi₂ with ⟨_, hdebt₂, htarget₂⟩
+    refine ⟨i₁, i₂, hne, ?_, ?_⟩
+    · have hdischarge := floatDebtAt_paymentDischarge_target hdebt₁
+      rwa [htarget₁] at hdischarge
+    · have hdischarge := floatDebtAt_paymentDischarge_target hdebt₂
+      rwa [htarget₂] at hdischarge
+
+/-- The number of extra height units available at a payment time. -/
+noncomputable def extraPaymentCapacityAt (n : OddNat) (j : ℕ) : ℕ :=
+  orbitWindowHeight n j - 1
+
+/-- More delayed growth-debt claims than available extra-height capacity. -/
+def FloatPaymentOverloadAt (n : OddNat) (j : ℕ) : Prop :=
+  extraPaymentCapacityAt n j < (floatGrowthDebtFiberAt n j).card
+
+/-- A payment slot with a nonempty delayed-debt fiber has at least one extra unit. -/
+theorem one_le_extraPaymentCapacityAt_of_growthDebtFiber_nonempty
+    {n : OddNat} {j : ℕ}
+    (h : (floatGrowthDebtFiberAt n j).Nonempty) :
+    1 ≤ extraPaymentCapacityAt n j := by
+  rcases h with ⟨i, hi⟩
+  rcases (mem_floatGrowthDebtFiberAt_iff.mp hi) with ⟨_, hdebt, htarget⟩
+  have hpay := floatDebtAt_paymentTarget hdebt
+  rw [htarget] at hpay
+  unfold extraPaymentCapacityAt PetalPaymentAt at *
+  omega
+
+/-- A genuine delayed-payment overload forces a target collision. -/
+theorem floatPaymentOverloadAt_implies_collision
+    {n : OddNat} {j : ℕ}
+    (h : FloatPaymentOverloadAt n j) :
+    FloatPaymentCollisionAt n j := by
+  have hcard_pos : 0 < (floatGrowthDebtFiberAt n j).card := by
+    unfold FloatPaymentOverloadAt at h
+    omega
+  have hnonempty : (floatGrowthDebtFiberAt n j).Nonempty :=
+    Finset.card_pos.mp hcard_pos
+  have hcap : 1 ≤ extraPaymentCapacityAt n j :=
+    one_le_extraPaymentCapacityAt_of_growthDebtFiber_nonempty hnonempty
+  have htwo : 2 ≤ (floatGrowthDebtFiberAt n j).card := by
+    unfold FloatPaymentOverloadAt at h
+    omega
+  exact floatPaymentCollisionAt_iff_two_le_growthDebtFiberCard.mpr htwo
+
+/-- Every Float debt has all-ones depth at least two. -/
+theorem two_le_orbitExactDepth_of_floatDebtAt
+    {n : OddNat} {i : ℕ}
+    (h : FloatDebtAt n i) :
+    2 ≤ orbitExactDepth n i := by
+  rcases floatDebtAt_paymentDischarge_target h with ⟨_, depth, hdepth, hexact, _, _⟩
+  have heq : depth = orbitExactDepth n i := by
+    simpa [OrbitDepthRecoversExactlyAt, orbitExactDepth] using hexact.symm
+  omega
+
+/-- Equal canonical targets form one descending exact-depth diagonal. -/
+theorem orbitExactDepth_eq_add_gap_of_lt_paymentTarget_eq
+    {n : OddNat} {i₁ i₂ : ℕ}
+    (hlt : i₁ < i₂)
+    (hdepth₁ : 1 ≤ orbitExactDepth n i₁)
+    (hdepth₂ : 1 ≤ orbitExactDepth n i₂)
+    (htarget : floatDebtPaymentTarget n i₁ = floatDebtPaymentTarget n i₂) :
+    orbitExactDepth n i₁ = orbitExactDepth n i₂ + (i₂ - i₁) := by
+  unfold floatDebtPaymentTarget at htarget
+  omega
+
+/-- Two ordered Float debts with one target lie on one descending depth diagonal. -/
+theorem floatDebtAt_orbitExactDepth_eq_add_gap_of_lt_same_paymentTarget
+    {n : OddNat} {i₁ i₂ : ℕ}
+    (hi₁ : FloatDebtAt n i₁)
+    (hi₂ : FloatDebtAt n i₂)
+    (hlt : i₁ < i₂)
+    (htarget : floatDebtPaymentTarget n i₁ = floatDebtPaymentTarget n i₂) :
+    orbitExactDepth n i₁ = orbitExactDepth n i₂ + (i₂ - i₁) := by
+  apply orbitExactDepth_eq_add_gap_of_lt_paymentTarget_eq hlt
+  · have hdepth := two_le_orbitExactDepth_of_floatDebtAt hi₁
+    omega
+  · have hdepth := two_le_orbitExactDepth_of_floatDebtAt hi₂
+    omega
+  · exact htarget
+
+/--
+Two ordered Float debts with a common target occupy one exact-depth staircase.
+
+Every intermediate time from the earlier source to the later source remains in
+the pre-payment height-one chain; at the later source the remaining depth is
+exactly its own all-ones depth.
+-/
+theorem floatDebtAt_same_paymentTarget_staircase_to_later_source
+    {n : OddNat} {i₁ i₂ : ℕ}
+    (hi₁ : FloatDebtAt n i₁)
+    (hi₂ : FloatDebtAt n i₂)
+    (hlt : i₁ < i₂)
+    (htarget : floatDebtPaymentTarget n i₁ = floatDebtPaymentTarget n i₂) :
+    (∀ t, t ≤ i₂ - i₁ →
+      OrbitDepthRecoversExactlyAt n (i₁ + t) (orbitExactDepth n i₁ - t) ∧
+        orbitWindowHeight n (i₁ + t) = 1) ∧
+      OrbitDepthRecoversExactlyAt n i₂ (orbitExactDepth n i₂) := by
+  have hdepth₁ := two_le_orbitExactDepth_of_floatDebtAt hi₁
+  have hdepth₂ := two_le_orbitExactDepth_of_floatDebtAt hi₂
+  have hdiag := floatDebtAt_orbitExactDepth_eq_add_gap_of_lt_same_paymentTarget
+    hi₁ hi₂ hlt htarget
+  have hgap : i₂ - i₁ < orbitExactDepth n i₁ - 1 := by
+    omega
+  have hexact₁ : OrbitDepthRecoversExactlyAt n i₁ (orbitExactDepth n i₁) := by
+    rfl
+  rcases orbitDepthRecoversExactlyAt_prePayment_chain n i₁ (orbitExactDepth n i₁)
+      hdepth₁ hexact₁ with ⟨hchain, _⟩
+  constructor
+  · intro t ht
+    have hlt' : t < orbitExactDepth n i₁ - 1 := lt_of_le_of_lt ht hgap
+    exact hchain t hlt'
+  · have hlater := (hchain (i₂ - i₁) hgap).1
+    simpa [show i₁ + (i₂ - i₁) = i₂ by omega, hdiag] using hlater
+
+/-- A carry-two event is every upper binary carry requiring one extra unit. -/
+def CarryTwoDebtAt (n : OddNat) (i : ℕ) : Prop :=
+  stateUpperCarry (iterateT i n).1 = 2
+
+/-- A carry-two event is delayed precisely when its observed height is one. -/
+def DelayedCarryTwoDebtAt (n : OddNat) (i : ℕ) : Prop :=
+  CarryTwoDebtAt n i ∧ orbitWindowHeight n i = 1
+
+/-- A carry-two event self-pays immediately when its height is already extra. -/
+def ImmediateCarryTwoDebtAt (n : OddNat) (i : ℕ) : Prop :=
+  CarryTwoDebtAt n i ∧ 2 ≤ orbitWindowHeight n i
+
+/-- Float width growth is exactly the delayed carry-two branch. -/
+theorem floatDebtAt_iff_delayedCarryTwoDebtAt
+    (n : OddNat) (i : ℕ) :
+    FloatDebtAt n i ↔ DelayedCarryTwoDebtAt n i := by
+  unfold FloatDebtAt DelayedCarryTwoDebtAt CarryTwoDebtAt
+  rw [iterateT_succ_eq_T_iterateT]
+  rw [bitWidth_growth_iff_carryTwo_and_heightOne]
+  simp only [orbitWindowHeight_eq_s_iterateT]
+
+/-- Every carry-two event is either delayed or immediately self-paid. -/
+theorem carryTwoDebtAt_delayed_or_immediate
+    {n : OddNat} {i : ℕ}
+    (h : CarryTwoDebtAt n i) :
+    DelayedCarryTwoDebtAt n i ∨ ImmediateCarryTwoDebtAt n i := by
+  by_cases hone : orbitWindowHeight n i = 1
+  · exact Or.inl ⟨h, hone⟩
+  · right
+    refine ⟨h, ?_⟩
+    have hpos := orbitWindowHeight_one_le n i
+    omega
+
+/-- Complete claim relation for the carry-two ledger. -/
+noncomputable def CarryTwoPaymentClaim
+    (n : OddNat) (i j : ℕ) : Prop :=
+  DelayedCarryTwoDebtAt n i ∧ j = floatDebtPaymentTarget n i ∨
+    ImmediateCarryTwoDebtAt n i ∧ j = i
+
+/-- Every carry-two event makes one explicit payment claim. -/
+theorem carryTwoDebtAt_exists_paymentClaim
+    {n : OddNat} {i : ℕ}
+    (h : CarryTwoDebtAt n i) :
+    ∃ j, CarryTwoPaymentClaim n i j := by
+  rcases carryTwoDebtAt_delayed_or_immediate h with hdelayed | himmediate
+  · refine ⟨floatDebtPaymentTarget n i, Or.inl ⟨hdelayed, rfl⟩⟩
+  · exact ⟨i, Or.inr ⟨himmediate, rfl⟩⟩
+
+/-- Finite fiber of all carry-two claims arriving at one payment slot. -/
+noncomputable def carryTwoPaymentClaimFiberAt
+    (n : OddNat) (j : ℕ) : Finset ℕ := by
+  classical
+  exact (Finset.range (j + 1)).filter fun i => CarryTwoPaymentClaim n i j
+
+/-- Membership in the finite complete carry-two claim fiber. -/
+theorem mem_carryTwoPaymentClaimFiberAt_iff
+    {n : OddNat} {i j : ℕ} :
+    i ∈ carryTwoPaymentClaimFiberAt n j ↔
+      i < j + 1 ∧ CarryTwoPaymentClaim n i j := by
+  simp [carryTwoPaymentClaimFiberAt]
+
+/-- Every complete carry-two claim reaches an actual extra-height payment slot. -/
+theorem carryTwoPaymentClaim_payment
+    {n : OddNat} {i j : ℕ}
+    (h : CarryTwoPaymentClaim n i j) :
+    PetalPaymentAt n j := by
+  rcases h with hdelayed | himmediate
+  · rcases hdelayed with ⟨hdelayed, htarget⟩
+    have hdebt : FloatDebtAt n i :=
+      (floatDebtAt_iff_delayedCarryTwoDebtAt n i).mpr hdelayed
+    rw [htarget]
+    exact floatDebtAt_paymentTarget hdebt
+  · rcases himmediate with ⟨⟨_, hheight⟩, hself⟩
+    rw [hself]
+    exact hheight
+
+/-- Every complete carry-two claim is present in the finite fiber of its target. -/
+theorem mem_carryTwoPaymentClaimFiberAt_of_claim
+    {n : OddNat} {i j : ℕ}
+    (h : CarryTwoPaymentClaim n i j) :
+    i ∈ carryTwoPaymentClaimFiberAt n j := by
+  apply mem_carryTwoPaymentClaimFiberAt_iff.mpr
+  constructor
+  · rcases h with hdelayed | himmediate
+    · rcases hdelayed with ⟨hdelayed, htarget⟩
+      have hdebt : FloatDebtAt n i :=
+        (floatDebtAt_iff_delayedCarryTwoDebtAt n i).mpr hdelayed
+      rw [htarget]
+      exact Nat.lt_succ_of_lt (floatDebtAt_lt_paymentTarget hdebt)
+    · rcases himmediate with ⟨_, hself⟩
+      rw [hself]
+      exact Nat.lt_succ_self i
+  · exact h
+
+/-- A nonempty complete claim fiber has at least one extra-height unit available. -/
+theorem one_le_extraPaymentCapacityAt_of_carryTwoClaimFiber_nonempty
+    {n : OddNat} {j : ℕ}
+    (h : (carryTwoPaymentClaimFiberAt n j).Nonempty) :
+    1 ≤ extraPaymentCapacityAt n j := by
+  rcases h with ⟨i, hi⟩
+  have hclaim := (mem_carryTwoPaymentClaimFiberAt_iff.mp hi).2
+  have hpay := carryTwoPaymentClaim_payment hclaim
+  unfold extraPaymentCapacityAt PetalPaymentAt at *
+  omega
+
+/-- Two distinct carry-two sources claim the same payment slot. -/
+def CarryTwoPaymentClaimCollisionAt (n : OddNat) (j : ℕ) : Prop :=
+  ∃ i₁ i₂, i₁ ≠ i₂ ∧
+    CarryTwoPaymentClaim n i₁ j ∧ CarryTwoPaymentClaim n i₂ j
+
+/-- Complete-claim collision is exactly a complete claim fiber of size at least two. -/
+theorem carryTwoPaymentClaimCollisionAt_iff_two_le_fiberCard
+    {n : OddNat} {j : ℕ} :
+    CarryTwoPaymentClaimCollisionAt n j ↔
+      2 ≤ (carryTwoPaymentClaimFiberAt n j).card := by
+  constructor
+  · rintro ⟨i₁, i₂, hne, h₁, h₂⟩
+    have hi₁ := mem_carryTwoPaymentClaimFiberAt_of_claim h₁
+    have hi₂ := mem_carryTwoPaymentClaimFiberAt_of_claim h₂
+    have hcard : 1 < (carryTwoPaymentClaimFiberAt n j).card :=
+      Finset.one_lt_card.mpr ⟨i₁, hi₁, i₂, hi₂, hne⟩
+    omega
+  · intro hcard
+    rcases Finset.one_lt_card.mp
+        (by omega : 1 < (carryTwoPaymentClaimFiberAt n j).card)
+      with ⟨i₁, hi₁, i₂, hi₂, hne⟩
+    refine ⟨i₁, i₂, hne,
+      (mem_carryTwoPaymentClaimFiberAt_iff.mp hi₁).2,
+      (mem_carryTwoPaymentClaimFiberAt_iff.mp hi₂).2⟩
+
+/-- Capacity overload for the complete carry-two claim ledger. -/
+def CarryTwoPaymentOverloadAt (n : OddNat) (j : ℕ) : Prop :=
+  extraPaymentCapacityAt n j < (carryTwoPaymentClaimFiberAt n j).card
+
+/-- A complete carry-two payment overload forces a complete-claim collision. -/
+theorem carryTwoPaymentOverloadAt_implies_collision
+    {n : OddNat} {j : ℕ}
+    (h : CarryTwoPaymentOverloadAt n j) :
+    CarryTwoPaymentClaimCollisionAt n j := by
+  have hcard_pos : 0 < (carryTwoPaymentClaimFiberAt n j).card := by
+    unfold CarryTwoPaymentOverloadAt at h
+    omega
+  have hnonempty : (carryTwoPaymentClaimFiberAt n j).Nonempty :=
+    Finset.card_pos.mp hcard_pos
+  have hcap : 1 ≤ extraPaymentCapacityAt n j :=
+    one_le_extraPaymentCapacityAt_of_carryTwoClaimFiber_nonempty hnonempty
+  have htwo : 2 ≤ (carryTwoPaymentClaimFiberAt n j).card := by
+    unfold CarryTwoPaymentOverloadAt at h
+    omega
+  exact carryTwoPaymentClaimCollisionAt_iff_two_le_fiberCard.mpr htwo
+
+/-!
+## Current boundary
+
+The finite debt and complete carry-two claim fibers are now explicit.  The
+remaining bridge is genuinely combinatorial: compare a target fiber's
+multiplicity with `extraPaymentCapacityAt`, then relate an overload to a
+localized horizontal continuation/recovery imbalance.  Target coincidence is
+not itself an overload, because one payment slot can have several extra height
+units.
+-/
+
+end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-301.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-301.md
new file mode 100644
index 00000000..362618c5
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-301.md
@@ -0,0 +1,141 @@
+# cp-301: Payment multiplicity and capacity
+
+## Result
+
+Added `DkMath.Collatz.PetalBridge.FloatWindow.PaymentMultiplicityBridge` and
+exported it from `DkMath.Collatz.PetalBridge.FloatWindow`.
+
+The module makes the delayed-payment geometry finite and explicit.  It does
+not identify target coincidence with pressure or with an unpaid debt.
+
+## Fixed facts
+
+### 1. Pre-payment staircase
+
+`orbitDepthRecoversExactlyAt_prePayment_chain` proves that an exact all-ones
+depth `d >= 2` produces:
+
+```text
+for t < d - 1:
+  exact depth at i + t is d - t
+  observed height at i + t is exactly 1
+
+at i + d - 1:
+  observed height is at least 2
+```
+
+Thus the delayed endpoint is the first forced extra-height payment, rather
+than merely an endpoint known to have enough height.
+
+### 2. Canonical target
+
+`floatDebtPaymentTarget n i` is defined as:
+
+```text
+i + ResidualAllOnesDepth (oddOrbitLabel n i) - 1
+```
+
+The old proof-carrying relation is now proved to be exactly the graph of this
+target map:
+
+```text
+FloatDebtPaymentDischarge n i j
+  <-> FloatDebtAt n i and j = floatDebtPaymentTarget n i
+```
+
+The relation is retained because it carries the exact-depth payment proof;
+the deterministic target is used for finite fibers.
+
+### 3. Collision versus overload
+
+`floatGrowthDebtFiberAt n j` is the finite set of Float growth debts targeting
+`j`.  It satisfies:
+
+```text
+FloatPaymentCollisionAt n j
+  <-> 2 <= (floatGrowthDebtFiberAt n j).card
+```
+
+The actual capacity is:
+
+```text
+extraPaymentCapacityAt n j = orbitWindowHeight n j - 1
+```
+
+and the genuine overload predicate compares capacity with the fiber card.
+
+```text
+FloatPaymentOverloadAt n j -> FloatPaymentCollisionAt n j
+```
+
+The converse is intentionally absent.  Two debts sharing a target are not an
+overload if that target carries at least two extra-height units.
+
+### 4. Complete carry-two ledger
+
+The ledger now includes both branches of every carry-two event:
+
+```text
+DelayedCarryTwoDebtAt:   carry two and height one
+ImmediateCarryTwoDebtAt: carry two and height at least two
+```
+
+`CarryTwoPaymentClaim` gives delayed debts their canonical target and immediate
+debts their own time.  Its finite target fiber, collision predicate, and
+capacity-overload predicate are all explicit.  The complete overload also
+forces a complete-claim collision.
+
+### 5. Diagonal geometry
+
+For ordered Float debts with a common payment target:
+
+```text
+A_i1 = A_i2 + (i2 - i1)
+```
+
+where `A_i = orbitExactDepth n i`.  More strongly,
+`floatDebtAt_same_paymentTarget_staircase_to_later_source` shows that every
+intermediate time is on the earlier source's exact-depth, height-one staircase.
+The later debt is therefore a later point on that same descending diagonal.
+
+## Honest stopping point
+
+The requested Stage G bridge is not an index equality.  It must compare a
+diagonal target fiber with a *localized horizontal* continuation/recovery
+fiber.  The existing `SourcePressureMarginInt` counts over `List.range k`.
+Those global entries can contain recovery sources unrelated to one target
+fiber, and no existing theorem maps a diagonal fiber to such a restricted
+horizontal source set.
+
+Consequently, no theorem of either form below was claimed:
+
+```text
+target collision -> positive source pressure
+payment overload -> positive source pressure
+```
+
+The next legitimate layer is a generic finite-source-set pressure API:
+
+```text
+retention / continuation / recovery over Finset source indices
+localized margin = continuation card - recovery card
+List.range k specialization = existing source pressure
+```
+
+Only after mapping a payment diagonal into one such source set can overload be
+compared to local horizontal pressure without silently discarding unrelated
+recoveries.
+
+## Verification
+
+Passed during this checkpoint:
+
+```text
+lake build DkMath.Collatz.PetalBridge.FloatWindow.PaymentMultiplicityBridge
+lake build DkMath.Collatz.PetalBridge.FloatWindow
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath
+git diff --check
+```
+
+No `sorry` or `axiom` was introduced in the new FloatWindow module.
````
`````
