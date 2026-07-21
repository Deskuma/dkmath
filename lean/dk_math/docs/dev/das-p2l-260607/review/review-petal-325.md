# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.FloatWindow.*

gch: 488b9a80273391b80eda1a14b4e53cd1f47247e9

## Report

(14m5s)

cp-325 の実装と修正が完了しました。

**確定した事実**

- 空区間を正しく `0` とする total queue API を追加。
- 全深度 residual から causal queue への深度保存 embedding を構築。
- selected carrier を drift image と実在する spare incidence に分解。
- terminal valuation `≥ 2` なら spare incidence が存在。
- valuation-one の no-spare は `claimCount = length - 1` と同値。
- zero drift の no-spare 条件を valuation 別に分類。
- saturated successor は、当初の五分類では不足していました。
  - `positive + valuation-one + nonempty spare`
  - これを含む六分岐が、現時点で証明可能な完全分類です。
- dyadic potential を証明：

  ```text
  Int.toNat drift ≤ L - d - 1
  Int.toNat drift * 2^d ≤ 2^(L - 1)
  ```

重要な境界として、最後の不等式は数値容量です。異なる深度間の causal matching や、同じ incidence の再利用は主張していません。次の本質的課題は、時間順序と非重複を同時に保存する conversion semantics です。

レポートは [report-petal-325.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-325.md) に記録しました。

検証結果：

- `lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude` 成功
- `lake build DkMath.Collatz.PetalBridge` 成功
- `lake build DkMath` 成功、8641 jobs
- `git diff --check` 成功
- 対象ファイルに新規 `sorry` なし
- 旧 `maxHeartbeats 800000` / 重い embedding は除去済み

## Review

## 結論

**全面採用。no-spare 境界が正確に露出した。**

cp-325 では、次の三つが閉じた。

- selected carrier が、実 drift image と実 spare incidence に分解された。
- positive / zero drift における no-spare 条件が exact に分類された。
- depth を重み $2^d$ として読む局所 dyadic potential が証明された。

特に、当初の五分岐では漏れていた、

```text
positive nonsaturated
terminal valuation = 1
spare carrier nonempty
```

を発見して六分岐へ修正した判断は正しい。Lean が分類漏れを露出させ、無理に五分類へ押し込まなかった点を高く評価する。

ただし、さらに一段整理できる。

この第六分岐は **新しい障害ではない**。`spare carrier nonempty` を仮定に持つため、既に saturated token を受け取れる実 source incidence が存在する。

したがって、source-incidence の意味で本当に残る no-spare successor は二種類だけじゃ。

```text
CanonicalZeroCarrierBalancedBorderBlock
CanonicalTightValuationOnePositiveBlock
```

そして、この二種類は claim-depth の「穴」の個数で統一的に記述できる可能性が高い。

---

## 1. Total queue API

```lean
finiteReflectedQueueOnIcc
```

の追加は正しい。

従来の `finiteReflectedQueueOn` は $m<q$ でも block $q$ を一件処理していたが、新 API は空区間を正しく $0$ とする。

$$
m<q\Longrightarrow Q_{[q,m]}=0
$$

suffix 条件も空集合上で自明に成立するため、total API として整合している。

既存 Collatz specialization は $q\le m$ を持つため、旧 API を互換面として残した構成もよい。

---

## 2. Depth-preserving all-depth embedding

cp-324 の all-depth embedding は総 cardinality から選ばれていたため、depth coordinate を保存する保証がなかった。

今回、

```lean
allDepthActualResidualCausalQueueEmbedding
```

を `sigmaMap` で構築し、

```lean
allDepthActualResidualCausalQueueEmbedding_fst
```

によって depth が定義的に保存された。

これで、

$$
\operatorname{Residual}(d)\hookrightarrow\operatorname{Queue}(d)
$$

が depth ごとに独立に成立し、そのまま全 depth へ持ち上がった。

この層では token の cross-depth 再利用は一切ない。安全な conservative upper bound になっている。

---

## 3. 実 spare carrier

```lean
canonicalSelectedDriftSpareCarrier
```

は selected carrier から、classically chosen drift image を除いた実 Finset じゃ。

$$
|\operatorname{SelectedCarrier}|=|\operatorname{DriftImage}|+|\operatorname{SpareCarrier}|
$$

が exact に証明された。

terminal valuation $v\ge2$ の positive nonsaturated block では、

$$
D+1\le|\operatorname{SelectedCarrier}|
$$

なので、

$$
1\le|\operatorname{SpareCarrier}|
$$

となる。

さらに、

```lean
oneEmbedding_canonicalSelectedDriftSpareCarrier
```

によって、単なる cardinality slack ではなく、実 source incidence 一個への embedding まで得られた。

これは saturated predecessor の unit token を charge するための正しい carrier じゃ。

---

## 4. Valuation-one tight block

$v=1$ では selected depth は $1$ で、selected carrier の大きさは、

$$
|\operatorname{SelectedCarrier}|=L-2
$$

になる。

positive drift は、

$$
D=A-1
$$

じゃ。

したがって spare cardinality は、

$$
|\operatorname{SpareCarrier}|=(L-2)-(A-1)=L-A-1
$$

となる。

よって no-spare 条件は、

$$
|\operatorname{SpareCarrier}|=0\iff A=L-1
$$

である。

今回の、

```lean
CanonicalTightValuationOnePositiveBlock
```

はこの exact border を正しく固定している。

また positive nonsaturated $v=1$ なら $L\ge3$ も従う。

$L=2$ なら positive drift により $A=2=L$ となり、full-claim positive block、すなわち saturation になってしまうからじゃ。

---

## 5. Zero-carrier balanced block はさらに剛直化できる

zero drift なら、

$$
A=v
$$

じゃ。

今回得た carrier-empty 条件と合わせると、`CanonicalZeroCarrierBalancedBorderBlock` は次の二種類に完全に潰せる。

$$
\operatorname{ZeroCarrierBalanced}\iff(L=v\land A=L)\lor(v=1\land L=2\land A=1)
$$

第一分岐は、

```text
length = terminal valuation
all depths claim
drift = 0
selected carrier empty
```

という full-claim balanced block。

$v=1,L=1,A=1$ もここに含まれる。

第二分岐だけが例外で、

```text
length = 2
terminal valuation = 1
claim count = 1
```

という一穴の短い balanced blockじゃ。

現在の二つの `selectedPressureCarrier_eq_empty_iff...` theorem は正しいが、最終 API としては、この exact normal form までまとめた方がよい。

---

## 6. Claim-hole accounting が見えている

ここで新しい保存核が露出した。

block 内の全 depth から、claim depth を除いた集合を定義する。

```lean
noncomputable def canonicalBlockClaimHoles
    (n : OddNat) (k : ℕ) : Finset ℕ :=
  Finset.Icc 1 (canonicalBlockLength n k) \
    canonicalPaymentClaimDepths n k
```

hole 数を $H$ とすれば、

$$
A+H=L
$$

じゃ。

したがって block drift は、

$$
D=L-v-H
$$

となる。

これは現在の分類を一つの式へ統合する。

### Saturated block

$$
L-v=1,\qquad H=0,\qquad D=1
$$

### Full-claim balanced block

$$
L-v=0,\qquad H=0,\qquad D=0
$$

### Tight valuation-one positive block

$$
v=1,\qquad H=1,\qquad D=L-2
$$

### Exceptional length-two balanced block

$$
v=1,\qquad L=2,\qquad H=1,\qquad D=0
$$

つまり、本当に難しい no-spare 構造は、

> **claim-depth の穴が 0 個または 1 個しかない極端に密な block**

として統一できる。

これは六分岐の論理分類より、さらに構造的な grammar じゃ。

---

## 7. Spare cardinality も hole 数で書ける

positive nonsaturated block について、hole 数を $H$ とする。

terminal valuation $v\ge2$ では、

$$
|\operatorname{SpareCarrier}|=H
$$

terminal valuation $v=1$ では、

$$
|\operatorname{SpareCarrier}|=H-1
$$

となる。

したがって、

- $v\ge2$ では positive nonsaturated なら必ず $H\ge1$ で spare がある。
- $v=1$ では $H=1$ のときだけ no-spare。
- $v=1$ で $H\ge2$ なら spare がある。

今回追加された第六分岐、

```text
positive valuation-one + spare nonempty
```

は、claim-hole 言語では単に、

$$
v=1,\qquad H\ge2
$$

じゃ。

これは障害ではなく、明確な source-available branch である。

---

## 8. 六分岐は四分岐へ圧縮できる

現在の六分岐 theorem は論理的に完全であり、そのまま保持してよい。

ただし公開される意味論としては、次の四分岐が鋭い。

```text
successor drift < 0

successor spare carrier nonempty

CanonicalZeroCarrierBalancedBorderBlock

CanonicalTightValuationOnePositiveBlock
```

zero drift かつ selected carrier nonempty の場合、drift image は空なので、selected carrier 全体が spare になる。

positive $v\ge2$ では今回の theorem により spare が存在する。

positive $v=1$ の第六分岐も、定義上 spare が存在する。

したがって、source-incidence の意味で解けていないのは最後の二種類だけじゃ。

---

## 9. Saturated predecessor の即時処理

saturated predecessor の drift は $1$。

successor drift が負なら、整数なので、

$$
D_{k+1}\le-1
$$

ゆえに、

$$
D_k+D_{k+1}\le0
$$

となり、二 block scalar ledger で即時返済される。

successor spare carrier が nonempty なら、

$$
\operatorname{Fin}(1)\hookrightarrow\operatorname{SpareCarrier}_{k+1}
$$

を構成できる。

したがって saturated block の successor は、次まで圧縮できる。

```text
scalar repayment
or
actual spare-source charge
or
zero-carrier balanced border
or
tight valuation-one positive block
```

report にある「valuation-one spare branch を調査する」は少し修正すべきじゃ。

その branch は既に charge 可能であり、存在頻度を調べる必要はあっても、構造的障害ではない。

---

## 10. Dyadic potential の評価

今回証明された、

$$
D,2^d\le2^{L-1}
$$

は正しい。

ただし証明は、

$$
D\le L-d-1\le2^{L-d-1}
$$

という一般的な指数上界を使っており、まだかなり余裕がある。

positive nonsaturated block では $d+2\le L$ なので、

$$
g=L-d-1\ge1
$$

じゃ。

$g\ge1$ なら、さらに強く、

$$
g\le2^{g-1}
$$

が成立する。

したがって、

$$
D,2^d\le2^{L-2}
$$

まで強化できる。

これは現在の theorem より一 factor $2$ 強い。

---

## 11. Half-budget の意味

positive nonsaturated block では $L\ge3$ なので、

$$
2\le2^{L-2}
$$

じゃ。

よって saturated predecessor の dyadic mass $2$ と、successor 自身の positive drift massを合わせても、

$$
2+D_{k+1}2^{d_{k+1}}\le2^{L_{k+1}-1}
$$

となる。

つまり数値 potential の世界では、

> positive nonsaturated successor は、自分自身の drift と直前の saturated unit を、一つの block-width denomination 内へ同時に収められる。

これは tight valuation-one no-spare blockにも適用される。

したがって、source-incidence carrier では tight block が障害でも、dyadic potential では既に半分以下しか使っていない。

---

## 12. Zero successor の dyadic 境界

zero-drift successor では自分自身の positive demand は $0$。

block length $L\ge2$ なら、

$$
2\le2^{L-1}
$$

なので saturated predecessor の dyadic mass $2$ を数値的には収容できる。

したがって dyadic potential 上で唯一容量不足になり得るのは、

```text
zero drift
zero carrier
block length = 1
terminal valuation = 1
claim count = 1
```

という最小 full-claim balanced blockじゃ。

これは先ほどの zero-carrier exact normal form の最小ケースである。

よって dyadic route の真正な局所特異点は、二種類ではなく最終的にこの一種類まで縮む可能性がある。

ただし、まだ **数値容量上の話** であり、actual bit resource への変換は未証明じゃ。

---

## 13. Conversion semantics の注意

`2^(L-1)` を block ごとに新しく発生する service と解釈すると、全 block が自分自身を容易に払えてしまう。

それでは大域 Big にはならない。

必要なのは、

> 各 block の dyadic budget が、有限開始値のどの既存 upper-bit resource を使用しているか

を示す bridge じゃ。

同じ上位 bit boundary を複数 block が再利用しているなら、数値 potential を足しても意味がない。

したがって、binary refinement tree や weighted Hall を作る前に、次を区別する必要がある。

```text
abstract dyadic leaf capacity

actual bit-position resource

timeをまたいだ resource reuse
```

まず abstract carrier で非重複 conversion を作り、その後 actual bit boundary へ単射できるかを問うのが安全じゃ。

---

## 判定まとめ

### Total queue

**完成。**

### Depth-preserving all-depth embedding

**完成。**

### Actual spare carrier

**完成。**

### Positive valuation-one no-spare

**完成。near-full claim と同値。**

### Zero-drift no-spare

**完成。さらに二種類の exact normal form へ圧縮可能。**

### Saturated successor six-way classification

**完成。ただし source semantics では四分岐へ圧縮可能。**

### Dyadic potential

**完成。さらに half-budget へ強化可能。**

### 真の次戦線

**claim-hole grammar、二つの rigid class の圧縮、abstract dyadic conversion と actual upper-bit resource の橋。**

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge FloatWindow branch after
report-petal-325.

The cp-325 implementation is accepted.

The six-way saturated-successor theorem is logically complete, but the new
valuation-one nonempty-spare branch is not an obstruction: it already contains
an actual chargeable source incidence.

Before implementing a global cross-depth matcher, compress the remaining
structure through claim-depth holes and strengthen the dyadic potential.

# Stage A — claim-hole carrier

Define:

    canonicalBlockClaimHoles n k :=
      Icc 1 (canonicalBlockLength n k)
        \ canonicalPaymentClaimDepths n k.

Prove:

    claim depths and claim holes are disjoint;
    their union is Icc 1 blockLength;
    claimCount + claimHoles.card = blockLength.

Derive the exact signed formula:

    endpointAccountingTerm n k
      =
    (canonicalBlockLength n k : Int)
      - canonicalBlockTerminalValuation n k
      - canonicalBlockClaimHoles.card.

This theorem should become the primary block accounting normal form.

# Stage B — exact spare formulas through holes

For every positive nonsaturated block prove:

    terminal valuation = 1 ->
      spare carrier card = claimHoles.card - 1;

    terminal valuation >= 2 ->
      spare carrier card = claimHoles.card.

Derive:

    tight valuation-one positive
      <->
    positive nonsaturated
      and terminal valuation = 1
      and claimHoles.card = 1;

    positive valuation-one with nonempty spare
      <->
    positive nonsaturated
      and terminal valuation = 1
      and 2 <= claimHoles.card.

For terminal valuation at least two, recover spare nonemptiness from
`claimHoles.card >= 1`.

# Stage C — exact zero-carrier balanced normal form

Prove:

    CanonicalZeroCarrierBalancedBorderBlock n k
      <->
    (
      canonicalBlockLength n k
        = canonicalBlockTerminalValuation n k
      and
      canonicalBlockClaimCount n k
        = canonicalBlockLength n k
    )
    or
    (
      canonicalBlockTerminalValuation n k = 1
      and
      canonicalBlockLength n k = 2
      and
      canonicalBlockClaimCount n k = 1
    ).

Derive the hole forms:

    full balanced branch -> holes.card = 0;
    exceptional length-two branch -> holes.card = 1.

Expose that the `length = valuation = 1` case belongs to the full balanced
branch.

# Stage D — unique missing claim depth

For every block whose claim-hole cardinality is one, define or choose the unique
missing depth.

Prove:

    canonicalPaymentClaimDepths
      =
    Icc 1 blockLength erase missingDepth.

Instantiate this for:

    CanonicalTightValuationOnePositiveBlock;
    exceptional length-two zero-balanced block.

Split the missing depth into:

    missing depth = 1;
    missing depth > 1.

Audit whether either branch is excluded by existing carry-two or endpoint
theorems.

# Stage E — compress saturated-successor classification

Define a simple source-availability predicate:

    CanonicalSuccessorSpareAvailable n j :=
      (canonicalSelectedDriftSpareCarrier n j).Nonempty.

Prove that zero drift plus nonempty selected carrier implies spare availability,
because the drift image is empty.

Prove the four-way theorem for a saturated predecessor:

    successor drift < 0
      or
    successor spare carrier is nonempty
      or
    CanonicalZeroCarrierBalancedBorderBlock successor
      or
    CanonicalTightValuationOnePositiveBlock successor.

Keep the six-way theorem as the detailed compatibility surface.

# Stage F — actual saturated-token discharge

For the negative-successor branch prove:

    endpointAccountingTerm n k
      + endpointAccountingTerm n (k + 1) <= 0.

For the spare-available branch construct:

    Fin 1
      ↪
    successor spare selected-incidence carrier.

Conclude that only the two rigid predicates remain unresolved at the
source-incidence level.

Do not describe the valuation-one nonempty-spare branch as unresolved.

# Stage G — stronger nonsaturated dyadic half-budget

First prove for every positive nonsaturated block:

    3 <= canonicalBlockLength n k.

Let:

    gap = blockLength - selectedDepth - 1.

Prove the elementary inequality:

    1 <= gap -> gap <= 2^(gap - 1).

Strengthen the current dyadic theorem to:

    Int.toNat drift * 2^selectedDepth
      <=
    2^(blockLength - 2).

Keep the existing `2^(L - 1)` theorem as a coarse corollary.

# Stage H — two-block saturated dyadic budget

For a saturated block followed by a positive nonsaturated block prove:

    2
      + Int.toNat successorDrift * 2^successorSelectedDepth
      <=
    2^(successorLength - 1).

For a zero-drift successor with length at least two prove:

    2 <= 2^(successorLength - 1).

Thus isolate the only locally insufficient dyadic successor candidate:

    zero drift;
    zero carrier;
    length = 1;
    terminal valuation = 1;
    claim count = 1.

State this only as a numerical potential classification.

# Stage I — focused arithmetic audit of the length-one balanced successor

Let `u` be the saturated predecessor odd core.

Use the existing saturated successor normal form to prove:

    successor length = 1 -> u % 8 = 3.

Refine the residue calculation for successor terminal valuation one.  Check the
candidate implication:

    successor length = 1
      and successor terminal valuation = 1
      ->
    u % 16 = 11.

Then express the sole claim condition as the carry-two condition at the
successor start state.

Audit whether this exact state can occur and whether it can repeat after later
saturated blocks.

Do not use broad random statistics until the residue grammar is formalized.

# Stage J — abstract nonduplicating dyadic carrier

In an experimental section, define an abstract block budget carrier:

    Fin (2^(blockLength - 1)).

Represent positive drift demand at selected depth `d` by a carrier of
cardinality:

    Int.toNat drift * 2^d.

Use the strengthened half-budget to embed the block's own demand into one half
of the budget and, when applicable, a preceding saturated unit of mass two
into the other half.

The two images must be explicitly disjoint.

This is an abstract potential carrier only.  Do not call it a bit-position or
payment carrier.

# Stage K — actual upper-boundary bridge audit

Search the existing upper-window and eventually-zero boundary APIs for an
actual finite carrier of bit positions.

Determine whether the abstract dyadic budget carrier can inject into:

    distinct upper-zero bit positions;
    a finite binary refinement tree rooted at one boundary position;
    or another nonreusable initial-state resource.

Stop if block budgets can reuse the same boundary resource without a uniform
multiplicity bound.

# Stage L — report boundary

Record:

    claim-hole accounting unifies saturation, balanced blocks, and tight
    valuation-one blocks;

    source-incidence discharge leaves exactly two rigid classes;

    dyadic numerical discharge may reduce the local obstruction to the
    length-one balanced case;

    no global repayment follows until abstract dyadic leaves are connected to
    a finite nonreusable upper-boundary resource.

Stop at the first genuine obstruction among:

    claim holes do not partition the depth interval;
    spare cardinality is not controlled by hole count;
    zero-carrier balanced blocks have another normal form;
    the four-way successor theorem fails;
    the half-budget inequality fails;
    the length-one balanced successor has no finite residue grammar;
    abstract dyadic images cannot be made disjoint;
    actual upper-boundary resources are reused without control.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-326.md
```

cp-325 で no-spare の姿は見えた。

次はその姿を、**claim-depth の穴**として一つの式にまとめる番じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteReflectedQueue.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteReflectedQueue.lean
index eac49dd0..f4416a3c 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteReflectedQueue.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteReflectedQueue.lean
@@ -35,6 +35,26 @@ def finiteReflectedQueueOn
     (arrivals service : ℕ → ℕ) (q m : ℕ) : ℕ :=
   finiteReflectedQueueFrom arrivals service q (m - q + 1)

+/-- Total closed-interval queue.  Unlike `finiteReflectedQueueOn`, this wrapper
+treats `m < q` as the empty window and therefore processes no index. -/
+def finiteReflectedQueueOnIcc
+    (arrivals service : ℕ → ℕ) (q m : ℕ) : ℕ :=
+  if q ≤ m then finiteReflectedQueueOn arrivals service q m else 0
+
+/-- On a nonempty closed interval, the total wrapper is the compatibility
+queue. -/
+theorem finiteReflectedQueueOnIcc_eq_reflectedQueueOn
+    (arrivals service : ℕ → ℕ) {q m : ℕ} (hqm : q ≤ m) :
+    finiteReflectedQueueOnIcc arrivals service q m =
+      finiteReflectedQueueOn arrivals service q m := by
+  simp [finiteReflectedQueueOnIcc, hqm]
+
+/-- A reversed closed interval is an empty queue window. -/
+theorem finiteReflectedQueueOnIcc_eq_zero_of_lt
+    (arrivals service : ℕ → ℕ) {q m : ℕ} (hmq : m < q) :
+    finiteReflectedQueueOnIcc arrivals service q m = 0 := by
+  simp [finiteReflectedQueueOnIcc, Nat.not_le.mpr hmq]
+
 /-- Signed arrivals-minus-service balance on a closed finite window. -/
 def finiteSignedWindowBalance
     (arrivals service : ℕ → ℕ) (t m : ℕ) : ℤ :=
@@ -244,6 +264,20 @@ theorem finiteReflectedQueueOn_eq_zero_iff_all_suffix_nonpos
     intro t ht
     rw [Int.toNat_of_nonpos (hall t ht)]

+/-- Total zero characterization, including the empty closed interval. -/
+theorem finiteReflectedQueueOnIcc_eq_zero_iff_all_suffix_nonpos
+    (arrivals service : ℕ → ℕ) (q m : ℕ) :
+    finiteReflectedQueueOnIcc arrivals service q m = 0 ↔
+      ∀ t ∈ Finset.Icc q m,
+        finiteSignedWindowBalance arrivals service t m ≤ 0 := by
+  by_cases hqm : q ≤ m
+  · rw [finiteReflectedQueueOnIcc_eq_reflectedQueueOn arrivals service hqm]
+    exact finiteReflectedQueueOn_eq_zero_iff_all_suffix_nonpos
+      arrivals service hqm
+  · have hempty : Finset.Icc q m = ∅ := by
+      exact Finset.Icc_eq_empty hqm
+    simp [finiteReflectedQueueOnIcc, hqm, hempty]
+
 /-- Unordered positive part of total balance on the whole window. -/
 def finiteUnorderedResidual
     (arrivals service : ℕ → ℕ) (q m : ℕ) : ℕ :=
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean
index dec50be0..23b4b59f 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean
@@ -1021,6 +1021,35 @@ theorem canonicalSelectedDriftImageCarrier_eq_empty_of_not_active
   classical
   simp [canonicalSelectedDriftImageCarrier, h]

+/-! ## Actual spare selected incidences -/
+
+/-- Selected source incidences not used by the chosen same-block drift image. -/
+noncomputable def canonicalSelectedDriftSpareCarrier
+    (n : OddNat) (k : ℕ) :
+    Finset {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} := by
+  classical
+  letI : Fintype {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} :=
+    Fintype.ofFinset (canonicalSelectedPressureCarrier n k) (by simp)
+  exact Finset.univ \ canonicalSelectedDriftImageCarrier n k
+
+/-- The selected source carrier splits exactly into drift image and spare
+incidences. -/
+theorem card_selectedPressureCarrier_eq_driftImage_add_spare
+    (n : OddNat) (k : ℕ) :
+    (canonicalSelectedPressureCarrier n k).card =
+      (canonicalSelectedDriftImageCarrier n k).card +
+        (canonicalSelectedDriftSpareCarrier n k).card := by
+  classical
+  letI : Fintype {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} :=
+    Fintype.ofFinset (canonicalSelectedPressureCarrier n k) (by simp)
+  have hsplit := Finset.card_sdiff_add_card_eq_card
+    (show canonicalSelectedDriftImageCarrier n k ⊆
+      (Finset.univ : Finset {i : ℕ //
+        i ∈ canonicalSelectedPressureCarrier n k}) from Finset.subset_univ _)
+  rw [Finset.card_univ, Fintype.card_coe] at hsplit
+  unfold canonicalSelectedDriftSpareCarrier
+  omega
+
 /-- Actual positive-drift images bucketed by selected depth.  The sigma keeps
 the block index, while the inner subtype keeps the source time. -/
 def CanonicalSelectedDriftBucketCarrier
@@ -1470,6 +1499,38 @@ theorem natCard_allDepthActualResidual_le_causalQueueCarrier
   rw [natCard_actualSelectedDriftResidualCarrier, Nat.card_fin]
   exact canonicalUnorderedSelectedDriftResidualCount_le_depthQueue n hqm

+/-- Explicit depthwise embedding of actual residual incidences into the
+corresponding causal queue fiber. -/
+noncomputable def actualSelectedDriftResidualDepthEmbedding
+    (n : OddNat) {q m : ℕ} (d : ℕ) (hqm : q ≤ m) :
+    CanonicalActualSelectedDriftResidualCarrier n q m d ↪
+      Fin (canonicalSelectedDriftDepthQueue n q m d) := by
+  classical
+  letI : Fintype (CanonicalActualSelectedDriftResidualCarrier n q m d) :=
+    Fintype.ofFinset (canonicalActualSelectedDriftResidualFinset n q m d) (by simp)
+  apply Classical.choice
+  apply Function.Embedding.nonempty_iff_card_le.mpr
+  rw [Fintype.card_fin, ← Nat.card_eq_fintype_card,
+    natCard_actualSelectedDriftResidualCarrier]
+  exact canonicalUnorderedSelectedDriftResidualCount_le_depthQueue n hqm
+
+/-- Depth-preserving all-depth embedding.  No service token is converted or
+shared between depth fibers. -/
+noncomputable def allDepthActualResidualCausalQueueEmbedding
+    (n : OddNat) {q m : ℕ} (hqm : q ≤ m) :
+    CanonicalAllDepthActualSelectedDriftResidualCarrier n q m ↪
+      CanonicalAllDepthSelectedDriftCausalQueueCarrier n q m :=
+  (Function.Embedding.refl _).sigmaMap fun d => by
+    exact actualSelectedDriftResidualDepthEmbedding n d.val hqm
+
+/-- The explicit all-depth embedding preserves the depth coordinate
+definitionally. -/
+@[simp] theorem allDepthActualResidualCausalQueueEmbedding_fst
+    {n : OddNat} {q m : ℕ} (hqm : q ≤ m)
+    (x : CanonicalAllDepthActualSelectedDriftResidualCarrier n q m) :
+    (allDepthActualResidualCausalQueueEmbedding n hqm x).1 = x.1 :=
+  rfl
+
 /-- Noncanonical finite embedding witnessing the all-depth cardinal
 comparison.  Its target fibers remain depth-separated. -/
 theorem exists_allDepthActualResidualEmbedding_causalQueueCarrier
@@ -1533,6 +1594,317 @@ theorem intToNat_endpointAccountingTerm_add_one_le_selectedPressureCarrier_card
     canonicalBlockTerminalValuation_lt_length_of_endpointAccountingTerm_pos hpos
   omega

+/-- Terminal valuation at least two forces an actual spare selected source
+incidence on every positive nonsaturated block. -/
+theorem canonicalSelectedDriftSpareCarrier_nonempty
+    {n : OddNat} {k : ℕ}
+    (hpos : 0 < endpointAccountingTerm n k)
+    (hnot : ¬ CanonicalSaturatedBorderBlock n k)
+    (hv : 2 ≤ canonicalBlockTerminalValuation n k) :
+    (canonicalSelectedDriftSpareCarrier n k).Nonempty := by
+  apply Finset.card_pos.mp
+  have hsplit := card_selectedPressureCarrier_eq_driftImage_add_spare n k
+  have himage := card_canonicalSelectedDriftImageCarrier hpos hnot
+  have hslack :=
+    intToNat_endpointAccountingTerm_add_one_le_selectedPressureCarrier_card
+      hpos hnot hv
+  omega
+
+/-- One explicit unit embeds into the actual spare selected-incidence subtype. -/
+noncomputable def oneEmbedding_canonicalSelectedDriftSpareCarrier
+    {n : OddNat} {k : ℕ}
+    (hpos : 0 < endpointAccountingTerm n k)
+    (hnot : ¬ CanonicalSaturatedBorderBlock n k)
+    (hv : 2 ≤ canonicalBlockTerminalValuation n k) :
+    Fin 1 ↪ {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} //
+      i ∈ canonicalSelectedDriftSpareCarrier n k} := by
+  classical
+  letI : Fintype {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} :=
+    Fintype.ofFinset (canonicalSelectedPressureCarrier n k) (by simp)
+  letI : Fintype
+      {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} //
+        i ∈ canonicalSelectedDriftSpareCarrier n k} :=
+    Fintype.ofFinset (canonicalSelectedDriftSpareCarrier n k) (by simp)
+  apply Classical.choice
+  apply Function.Embedding.nonempty_iff_card_le.mpr
+  rw [Fintype.card_fin, Fintype.card_coe]
+  exact Finset.one_le_card.mpr
+    (canonicalSelectedDriftSpareCarrier_nonempty hpos hnot hv)
+
+/-! ## Exact no-spare classes -/
+
+/-- At terminal valuation one the selected depth is exactly one. -/
+theorem canonicalSelectedPositivePressureDepth_eq_one_of_terminalValuation_eq_one
+    {n : OddNat} {k : ℕ}
+    (hv : canonicalBlockTerminalValuation n k = 1) :
+    canonicalSelectedPositivePressureDepth n k = 1 := by
+  simp [canonicalSelectedPositivePressureDepth, hv]
+
+/-- At terminal valuation one the selected carrier has cardinality `L - 2`. -/
+theorem card_selectedPressureCarrier_of_terminalValuation_eq_one
+    {n : OddNat} {k : ℕ}
+    (hv : canonicalBlockTerminalValuation n k = 1) :
+    (canonicalSelectedPressureCarrier n k).card =
+      canonicalBlockLength n k - 2 := by
+  unfold canonicalSelectedPressureCarrier
+  rw [canonicalPaymentBlockContinuationFiber_card]
+  simp only [canonicalSelectedPositivePressureDepth, hv, ↓reduceIte, Nat.reduceAdd]
+  change canonicalBlockLength n k - 2 = canonicalBlockLength n k - 2
+  rfl
+
+/-- Tight positive valuation-one blocks are precisely the candidate class in
+which selected drift consumes every selected incidence. -/
+def CanonicalTightValuationOnePositiveBlock
+    (n : OddNat) (k : ℕ) : Prop :=
+  0 < endpointAccountingTerm n k ∧
+    ¬ CanonicalSaturatedBorderBlock n k ∧
+      canonicalBlockTerminalValuation n k = 1 ∧
+        canonicalBlockClaimCount n k = canonicalBlockLength n k - 1
+
+/-- Under the positive nonsaturated valuation-one hypotheses, no spare source
+incidence is exactly the near-full-claims condition. -/
+theorem selectedDriftSpareCarrier_eq_empty_iff_claimCount_eq_length_sub_one
+    {n : OddNat} {k : ℕ}
+    (hpos : 0 < endpointAccountingTerm n k)
+    (hnot : ¬ CanonicalSaturatedBorderBlock n k)
+    (hv : canonicalBlockTerminalValuation n k = 1) :
+    canonicalSelectedDriftSpareCarrier n k = ∅ ↔
+      canonicalBlockClaimCount n k = canonicalBlockLength n k - 1 := by
+  have hclaimsLe := canonicalBlockClaimCount_le_length n k
+  have hvlt :=
+    canonicalBlockTerminalValuation_lt_length_of_endpointAccountingTerm_pos hpos
+  have hdrift := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount n k
+  rw [canonicalBlockCapacityCount_eq_terminalValuation, hv] at hdrift
+  have htoNat : Int.toNat (endpointAccountingTerm n k) =
+      canonicalBlockClaimCount n k - 1 := by
+    have hcast : ((Int.toNat (endpointAccountingTerm n k) : ℕ) : ℤ) =
+        endpointAccountingTerm n k := Int.toNat_of_nonneg hpos.le
+    exact_mod_cast (show (Int.toNat (endpointAccountingTerm n k) : ℤ) =
+      (canonicalBlockClaimCount n k - 1 : ℕ) by omega)
+  have himage := card_canonicalSelectedDriftImageCarrier hpos hnot
+  have hselected := card_selectedPressureCarrier_of_terminalValuation_eq_one hv
+  have hsplit := card_selectedPressureCarrier_eq_driftImage_add_spare n k
+  constructor
+  · intro hempty
+    have hspare : (canonicalSelectedDriftSpareCarrier n k).card = 0 := by
+      rw [hempty]
+      rfl
+    omega
+  · intro hclaims
+    apply Finset.card_eq_zero.mp
+    omega
+
+/-- Tight valuation-one blocks expose all exact no-spare data. -/
+theorem CanonicalTightValuationOnePositiveBlock.exact_data
+    {n : OddNat} {k : ℕ}
+    (h : CanonicalTightValuationOnePositiveBlock n k) :
+    canonicalBlockTerminalValuation n k = 1 ∧
+      canonicalSelectedPositivePressureDepth n k = 1 ∧
+        endpointAccountingTerm n k =
+          (canonicalBlockLength n k - 2 : ℕ) ∧
+          (canonicalSelectedPressureCarrier n k).card =
+            canonicalBlockLength n k - 2 ∧
+            canonicalSelectedDriftSpareCarrier n k = ∅ := by
+  rcases h with ⟨hpos, hnot, hv, hclaims⟩
+  have hdrift := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount n k
+  rw [canonicalBlockCapacityCount_eq_terminalValuation, hv, hclaims] at hdrift
+  have hvlt :=
+    canonicalBlockTerminalValuation_lt_length_of_endpointAccountingTerm_pos hpos
+  exact ⟨hv,
+    canonicalSelectedPositivePressureDepth_eq_one_of_terminalValuation_eq_one hv,
+    by exact_mod_cast (show endpointAccountingTerm n k =
+      (canonicalBlockLength n k - 2 : ℕ) by omega),
+    card_selectedPressureCarrier_of_terminalValuation_eq_one hv,
+    (selectedDriftSpareCarrier_eq_empty_iff_claimCount_eq_length_sub_one
+      hpos hnot hv).2 hclaims⟩
+
+/-- Zero drift forces exact equality between claims and terminal capacity. -/
+theorem claimCount_eq_terminalValuation_of_endpointAccountingTerm_eq_zero
+    {n : OddNat} {k : ℕ} (hzero : endpointAccountingTerm n k = 0) :
+    canonicalBlockClaimCount n k = canonicalBlockTerminalValuation n k := by
+  have hdrift := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount n k
+  rw [canonicalBlockCapacityCount_eq_terminalValuation, hzero] at hdrift
+  omega
+
+/-- Zero-drift valuation-one blocks have empty selected carrier exactly at
+length at most two. -/
+theorem selectedPressureCarrier_eq_empty_iff_length_le_two_of_zero_val_one
+    {n : OddNat} {k : ℕ}
+    (_hzero : endpointAccountingTerm n k = 0)
+    (hv : canonicalBlockTerminalValuation n k = 1) :
+    canonicalSelectedPressureCarrier n k = ∅ ↔
+      canonicalBlockLength n k ≤ 2 := by
+  rw [← Finset.card_eq_zero, card_selectedPressureCarrier_of_terminalValuation_eq_one hv]
+  omega
+
+/-- For terminal valuation at least two, the zero-drift selected carrier is
+empty exactly when block length does not exceed terminal valuation. -/
+theorem selectedPressureCarrier_eq_empty_iff_length_le_terminalValuation_of_zero
+    {n : OddNat} {k : ℕ}
+    (_hzero : endpointAccountingTerm n k = 0)
+    (hv : 2 ≤ canonicalBlockTerminalValuation n k) :
+    canonicalSelectedPressureCarrier n k = ∅ ↔
+      canonicalBlockLength n k ≤ canonicalBlockTerminalValuation n k := by
+  rw [← Finset.card_eq_zero]
+  unfold canonicalSelectedPressureCarrier
+  rw [canonicalPaymentBlockContinuationFiber_card]
+  rw [canonicalSelectedPositivePressureDepth, if_neg (by omega)]
+  change canonicalBlockLength n k -
+      (canonicalBlockTerminalValuation n k - 1 + 1) = 0 ↔
+    canonicalBlockLength n k ≤ canonicalBlockTerminalValuation n k
+  omega
+
+/-- Rigid balanced border: zero drift and no selected source incidence. -/
+def CanonicalZeroCarrierBalancedBorderBlock
+    (n : OddNat) (k : ℕ) : Prop :=
+  endpointAccountingTerm n k = 0 ∧
+    canonicalSelectedPressureCarrier n k = ∅
+
+/-! ## Saturated-successor source classification
+
+The five-way classification proposed at cp-325 omitted a logically possible
+positive valuation-one branch: the spare carrier need not be empty.  The
+six-way theorem below is therefore the exhaustive surface justified by the
+current API.  Collapsing it to five branches requires a new theorem saying
+that every positive nonsaturated valuation-one successor of a saturated block
+is tight; no such theorem is currently available.
+-/
+
+/-- A zero-drift block with a nonempty selected carrier supplies an actual
+source incidence, independently of the (empty) drift image. -/
+theorem exists_selectedPressureSource_of_zero_of_nonempty
+    {n : OddNat} {k : ℕ}
+    (_hzero : endpointAccountingTerm n k = 0)
+    (hcarrier : (canonicalSelectedPressureCarrier n k).Nonempty) :
+    ∃ i, i ∈ canonicalSelectedPressureCarrier n k :=
+  hcarrier
+
+/-- A positive nonsaturated block of terminal valuation at least two supplies
+an actual spare selected source incidence. -/
+theorem exists_spareSelectedPressureSource_of_pos_of_two_le_terminalValuation
+    {n : OddNat} {k : ℕ}
+    (hpos : 0 < endpointAccountingTerm n k)
+    (hnot : ¬ CanonicalSaturatedBorderBlock n k)
+    (hv : 2 ≤ canonicalBlockTerminalValuation n k) :
+    ∃ i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k},
+      i ∈ canonicalSelectedDriftSpareCarrier n k :=
+  canonicalSelectedDriftSpareCarrier_nonempty hpos hnot hv
+
+/-- Exhaustive successor classification currently justified for a saturated
+predecessor.  The final disjunct is the valuation-one spare branch missing
+from the proposed five-way split. -/
+theorem CanonicalSaturatedBorderBlock.successor_source_classification
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
+    endpointAccountingTerm n (k + 1) < 0 ∨
+      (endpointAccountingTerm n (k + 1) = 0 ∧
+        (canonicalSelectedPressureCarrier n (k + 1)).Nonempty) ∨
+      CanonicalZeroCarrierBalancedBorderBlock n (k + 1) ∨
+      (0 < endpointAccountingTerm n (k + 1) ∧
+        ¬ CanonicalSaturatedBorderBlock n (k + 1) ∧
+        2 ≤ canonicalBlockTerminalValuation n (k + 1)) ∨
+      CanonicalTightValuationOnePositiveBlock n (k + 1) ∨
+      (0 < endpointAccountingTerm n (k + 1) ∧
+        ¬ CanonicalSaturatedBorderBlock n (k + 1) ∧
+        canonicalBlockTerminalValuation n (k + 1) = 1 ∧
+        (canonicalSelectedDriftSpareCarrier n (k + 1)).Nonempty) := by
+  classical
+  let j := k + 1
+  have hnotsat : ¬ CanonicalSaturatedBorderBlock n j := by
+    simpa [j] using h.not_succ
+  by_cases hneg : endpointAccountingTerm n j < 0
+  · exact Or.inl hneg
+  · have hnonneg : 0 ≤ endpointAccountingTerm n j := by omega
+    by_cases hzero : endpointAccountingTerm n j = 0
+    · by_cases hempty : canonicalSelectedPressureCarrier n j = ∅
+      · exact Or.inr (Or.inr (Or.inl ⟨hzero, hempty⟩))
+      · exact Or.inr (Or.inl ⟨hzero, Finset.nonempty_iff_ne_empty.mpr hempty⟩)
+    · have hpos : 0 < endpointAccountingTerm n j := by omega
+      by_cases hv : canonicalBlockTerminalValuation n j = 1
+      · by_cases hspare : canonicalSelectedDriftSpareCarrier n j = ∅
+        · have hclaims :=
+            (selectedDriftSpareCarrier_eq_empty_iff_claimCount_eq_length_sub_one
+              hpos hnotsat hv).1 hspare
+          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
+            ⟨hpos, hnotsat, hv, hclaims⟩))))
+        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
+            ⟨hpos, hnotsat, hv, Finset.nonempty_iff_ne_empty.mpr hspare⟩))))
+      · have hvpos := one_le_canonicalBlockTerminalValuation n j
+        have hv2 : 2 ≤ canonicalBlockTerminalValuation n j := by omega
+        have hbranch : 0 < endpointAccountingTerm n j ∧
+            ¬ CanonicalSaturatedBorderBlock n j ∧
+            2 ≤ canonicalBlockTerminalValuation n j := ⟨hpos, hnotsat, hv2⟩
+        exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa [j] using hbranch))))
+
+/-! ## Experimental dyadic depth-transfer potential
+
+These inequalities compare numerical denominations only.  They do not define
+a cross-depth map, do not permit one source incidence to be reused at several
+depths, and do not establish causal repayment.  A later conversion layer must
+carry an explicit nonduplication invariant before these bounds can be used as
+matching capacity.
+-/
+
+/-- Positive nonsaturated drift fits in the selected continuation width after
+removing its selected depth and the endpoint. -/
+theorem intToNat_endpointAccountingTerm_le_length_sub_depth_sub_one
+    {n : OddNat} {k : ℕ}
+    (hpos : 0 < endpointAccountingTerm n k)
+    (hnot : ¬ CanonicalSaturatedBorderBlock n k) :
+    Int.toNat (endpointAccountingTerm n k) ≤
+      canonicalBlockLength n k -
+        canonicalSelectedPositivePressureDepth n k - 1 := by
+  let d := canonicalSelectedPositivePressureDepth n k
+  let L := canonicalBlockLength n k
+  have hdL := selectedPositivePressureDepth_lt_length_of_pos_of_not_saturated
+    hpos hnot
+  have hle := endpointAccountingTerm_le_card_selectedPressureCarrier hpos hnot
+  have hcard : (canonicalSelectedPressureCarrier n k).card = L - (d + 1) := by
+    unfold canonicalSelectedPressureCarrier
+    rw [canonicalPaymentBlockContinuationFiber_card]
+    rfl
+  have hcast : ((Int.toNat (endpointAccountingTerm n k) : ℕ) : ℤ) =
+      endpointAccountingTerm n k := Int.toNat_of_nonneg hpos.le
+  rw [hcard] at hle
+  change d < L at hdL
+  change Int.toNat (endpointAccountingTerm n k) ≤ L - d - 1
+  exact_mod_cast (show ((Int.toNat (endpointAccountingTerm n k) : ℕ) : ℤ) ≤
+    (L - d - 1 : ℕ) by omega)
+
+/-- Local dyadic potential: the selected positive drift, denominated at depth
+`d`, is bounded by one block-width denomination `2^(L-1)`. -/
+theorem intToNat_endpointAccountingTerm_mul_two_pow_depth_le_two_pow_length_sub_one
+    {n : OddNat} {k : ℕ}
+    (hpos : 0 < endpointAccountingTerm n k)
+    (hnot : ¬ CanonicalSaturatedBorderBlock n k) :
+    Int.toNat (endpointAccountingTerm n k) *
+        2 ^ canonicalSelectedPositivePressureDepth n k ≤
+      2 ^ (canonicalBlockLength n k - 1) := by
+  let a := Int.toNat (endpointAccountingTerm n k)
+  let d := canonicalSelectedPositivePressureDepth n k
+  let L := canonicalBlockLength n k
+  let gap := L - d - 1
+  have hdL := selectedPositivePressureDepth_lt_length_of_pos_of_not_saturated
+    hpos hnot
+  have ha : a ≤ gap :=
+    intToNat_endpointAccountingTerm_le_length_sub_depth_sub_one hpos hnot
+  have hagap : a ≤ 2 ^ gap :=
+    ha.trans (Nat.le_of_lt gap.lt_two_pow_self)
+  have hsum : gap + d = L - 1 := by
+    change d < L at hdL
+    dsimp [gap]
+    omega
+  calc
+    a * 2 ^ d ≤ 2 ^ gap * 2 ^ d := Nat.mul_le_mul_right _ hagap
+    _ = 2 ^ (gap + d) := by rw [pow_add]
+    _ = 2 ^ (L - 1) := by rw [hsum]
+
+/-- The explicit saturated unit has exactly the same dyadic mass as its fixed
+length-two block-width denomination. -/
+theorem CanonicalSaturatedBorderBlock.dyadic_unit_budget
+    {n : OddNat} {k : ℕ} (_h : CanonicalSaturatedBorderBlock n k) :
+    (1 : ℕ) * 2 ^ 1 = 2 ^ (2 - 1) := by
+  norm_num
+
 /-!
 ## Current boundary after the causal depth queue

diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-325.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-325.md
new file mode 100644
index 00000000..d4a4e5fb
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-325.md
@@ -0,0 +1,99 @@
+# Petal / FloatWindow Report - Checkpoint 325
+
+## Status
+
+Accepted implementation target completed through the first honest conversion
+boundary.  All new declarations in the touched FloatWindow files are
+`no-sorry`.
+
+## Implemented
+
+### Total closed-window queue
+
+`FiniteReflectedQueue.lean` now provides `finiteReflectedQueueOnIcc`.  It
+agrees with the compatibility queue on nonempty closed intervals and is zero
+when the interval is empty.  Its zero characterization quantifies over every
+suffix of the possibly-empty window.
+
+### Explicit all-depth embedding
+
+`UniversalPaymentAmplitude.lean` now contains an explicit depth-preserving
+embedding from the all-depth actual residual carrier into the all-depth causal
+queue carrier.  The depth coordinate is preserved definitionally.  The old
+cardinality-only existence theorem remains available.
+
+### Spare selected incidences
+
+The selected pressure carrier is split into the chosen drift image and its
+finite complement, `canonicalSelectedDriftSpareCarrier`.  Positive
+nonsaturated blocks with terminal valuation at least two have a concrete spare
+incidence, including an explicit `Fin 1` embedding.
+
+### Exact no-spare classes
+
+For positive nonsaturated valuation-one blocks, spare emptiness is equivalent
+to `claimCount = length - 1`.  The named tight predicate exposes valuation,
+depth, drift, carrier cardinality, and no-spare data.
+
+For zero drift, claims equal terminal valuation.  Empty selected carriers are
+classified separately at valuation one and valuation at least two.  The rigid
+zero-carrier balanced predicate records the remaining no-source case.
+
+### Saturated-successor correction
+
+The requested five-way successor split is not derivable from the current API.
+It omitted a possible branch:
+
+```text
+positive nonsaturated + terminal valuation one + nonempty spare carrier
+```
+
+Lean validates an exhaustive six-way classification including this branch.
+The two easy source-bearing cases expose actual source incidences:
+
+1. zero drift with nonempty selected carrier;
+2. positive nonsaturated drift with terminal valuation at least two.
+
+The five-way theorem must not be introduced unless a future theorem proves
+that every positive valuation-one successor of a saturated block is tight.
+
+### Dyadic potential
+
+For positive nonsaturated blocks with selected depth `d` and length `L`:
+
+```text
+Int.toNat drift <= L - d - 1
+Int.toNat drift * 2^d <= 2^(L - 1)
+```
+
+The saturated length-two unit satisfies the corresponding exact identity.
+
+## Proven Facts
+
+1. Fixed-depth queue accounting is total, exact, causal, and explicitly
+   embeddable without changing depth.
+2. The all-depth construction is conservative: no source token is shared
+   across depths.
+3. Spare incidence is a concrete finite source carrier, not merely a cardinal
+   slack inequality.
+4. Terminal valuation at least two guarantees spare incidence in the positive
+   nonsaturated branch.
+5. Valuation-one no-spare is exactly the near-full claim condition.
+6. Zero drift alone is not an incidence; a nonempty selected carrier is the
+   required source witness.
+7. A block-width dyadic denomination numerically dominates its selected drift
+   mass.
+
+## Boundary and Next Work
+
+The dyadic inequality is not a cross-depth matching theorem.  A valid
+conversion layer must represent one high-depth token by lower-depth units
+while preserving both temporal order and nonduplication.  Candidate models
+remain a finite binary refinement tree, weighted Hall capacity, or a monotone
+potential certificate.
+
+The immediate focused audit should examine the two rigid no-spare classes and
+the newly exposed valuation-one spare branch.  In particular, determine
+whether saturated successors can enter the valuation-one spare branch and
+whether either rigid class can persist indefinitely.  No global repayment or
+convergence conclusion is claimed at this checkpoint.
````
`````
