# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude

gch: 883f6be223f2a41551f244131b06b3a40a545c0f

## Report

(17m21s)

cp-326 を実装し、最初の真正な障害まで到達しました。

主な確定事項:

- claim depths と claim holes は完全に分割される。
- drift は `length - terminalValuation - holes.card` で正規化できる。
- spare cardinality を hole 数から正確に計算できる。
- saturated successor は negative / actual spare / 2つの rigid class に圧縮できる。
- positive nonsaturated demand は dyadic budget の上半分へ埋め込める。
- saturated mass 2 は下側へ埋め込め、両者の像は明示的に非交差。
- saturated predecessor の successor length が `1` なら、predecessor odd core は `3 mod 8`。
- length-one block の唯一の claim 条件は endpoint の carry-two 条件と同値。

現在の真正な障害は、抽象 dyadic carrier を実際の「再利用されない upper-zero bit-position carrier」へ移す API が存在しないことです。したがって、現時点で global repayment を主張することはできません。`mod 16 = 11` の強化には successor terminal carrier の代数的な置換公式がもう一つ必要です。

実装は [UniversalPaymentAmplitude.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean)、詳細な成果と次の境界は [report-petal-326.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-326.md) に記録しました。

検証済み:

- targeted module build
- `lake build DkMath.Collatz.PetalBridge`
- `lake build DkMath`
- `git diff --check`
- 変更コードに `sorry`、`maxHeartbeats` なし

トップレベルビルドには既存研究モジュール由来の `sorry` 警告がありますが、今回の変更とは無関係です。

## Review

# cp-326 実装レビュー

## 結論

**全面採用。局所 no-spare 解析と abstract dyadic budget は完成じゃ。**

cp-326 の最大成果は、block accounting を claim-hole 数 $H$ によって、

$$D = L - v - H$$

という一式へ圧縮したことじゃ。

これにより、

- saturation
- zero-carrier balanced block
- tight valuation-one positive block
- spare incidence の有無
- positive drift の dyadic demand

が、同じ有限構造から読めるようになった。

さらに、positive nonsaturated successor の demand と、直前 saturated unit の質量 $2$ を、同じ abstract dyadic budget 内の互いに素な領域へ実際に埋め込んだ。これは単なる数値不等式から一段進んだ成果じゃ。

ただし、停止診断は次のように精密化すべきである。

> 足りないのは「upper-zero bit-position carrier」という定義だけではない。
> 真に欠けているのは、各 block の局所 budget がどの大域資源から生じ、その資源が時間を越えて新生・重複利用されないことを示す **global conservation transport** である。

単に bit position の集合を定義するだけでは、まだ global repayment にはならぬ。

---

## 1. Claim-hole accounting normal form

```lean
canonicalBlockClaimHoles
```

は、正 depth 全体から claim depths を除いた有限集合じゃ。

$$\operatorname{Claims}\sqcup\operatorname{Holes}=\operatorname{Icc}(1,L)$$

したがって、

$$A+H=L$$

となる。

ここで、

- $L$ は block length
- $A$ は claim count
- $H$ は claim-hole count
- $v$ は terminal valuation

じゃ。

既存 drift 式、

$$D=A-v$$

と合わせることで、

$$D=L-v-H$$

が得られた。

これは今後の primary normal form として正しい。

以前は claim count、capacity、selected depth、carrier cardinality を個別に追っていた。今後はまず $L,v,H$ を見るだけで、主要な局所状態を分類できる。

---

## 2. Spare carrier の exact formula

positive nonsaturated block について、spare cardinality が hole 数と直接結びついた。

terminal valuation が $1$ なら、

$$|\operatorname{Spare}|=H-1$$

terminal valuation が $2$ 以上なら、

$$|\operatorname{Spare}|=H$$

じゃ。

これにより、valuation-one の特殊性が明確になった。

$v\ge2$ では一つでも claim hole があれば、その hole はそのまま一つの spare incidence になる。

$v=1$ では最初の hole 一個が selected carrier の境界補正に消費され、二個目以降が spare になる。

したがって、

$$v=1\land|\operatorname{Spare}|=0\iff H=1$$

である。

`CanonicalTightValuationOnePositiveBlock` は、まさに claim hole が一個だけの極限密度 block じゃ。

---

## 3. Zero-carrier balanced block

今回、zero drift かつ selected carrier が空となる状態が、二種類へ完全に分類された。

### Full balanced branch

$$L=v,\qquad A=L,\qquad H=0$$

全 depth が claim であり、block length と terminal capacity が完全に一致する。

### Exceptional length-two branch

$$L=2,\qquad v=1,\qquad A=1,\qquad H=1$$

二つの depth のうち一つだけが claim になる。

したがって、

```lean
CanonicalZeroCarrierBalancedBorderBlock
```

は曖昧な残余 predicate ではなくなった。

特に $L=v=1,A=1$ は full balanced branch に含まれる。

---

## 4. Unique missing claim depth

hole cardinality が一なら、唯一の missing depth が選べる。

$$\operatorname{Claims}=\operatorname{Icc}(1,L)\setminus{d_{\mathrm{miss}}}$$

これは tight valuation-one positive block と exceptional length-two balanced block の両方に適用される。

今回の、

```lean
canonicalBlockMissingClaimDepth_eq_one_or_gt_one
```

は入口として正しい。

ただし、次には単なる、

```text
missing depth = 1
missing depth > 1
```

だけでなく、次も分ける価値がある。

```text
missing depth = 1
1 < missing depth < L
missing depth = L
```

depth $1$ は endpoint claim、depth $L$ は最深 claim という異なる意味を持つ可能性があるためじゃ。

---

## 5. Saturated successor の四分岐

詳細な六分岐を source-level に圧縮し、

```text
negative successor drift
actual spare source available
zero-carrier balanced block
tight valuation-one positive block
```

の四分岐が得られた。

これは正しい圧縮じゃ。

negative branch では saturated predecessor の drift が $1$ なので、

$$1+D_{k+1}\le0$$

となり、二 block scalar ledger で即座に返済される。

spare branch では、

$$\operatorname{Fin}(1)\hookrightarrow\operatorname{SpareCarrier}_{k+1}$$

が実 source incidence として構成された。

したがって source-incidence の層で未解決なのは、本当に次の二種類だけじゃ。

```text
CanonicalZeroCarrierBalancedBorderBlock
CanonicalTightValuationOnePositiveBlock
```

valuation-one positive かつ spare nonempty の分岐は、もはや障害ではない。

---

## 6. Dyadic half-budget

positive nonsaturated blockについて、

$$D\le L-d-1$$

に加え、

$$D,2^d\le2^{L-2}$$

が証明された。

これは以前の、

$$D,2^d\le2^{L-1}$$

より一 factor $2$ 強い。

さらに saturated predecessor の mass $2$ を lower region、successor demand を upper half へ埋め込み、二つの像が交わらないことまで証明した。

$$\operatorname{Fin}(2)\hookrightarrow[0,2^{L-2})$$

$$\operatorname{Demand}\hookrightarrow[2^{L-2},2^{L-1})$$

したがって、

$$2+D_{k+1}2^{d_{k+1}}\le2^{L_{k+1}-1}$$

が、単なる inequality ではなく非重複 finite embedding として実現された。

これは非常に良い。

---

## 7. Zero-drift successor の abstract embedding

zero-drift successor については、

$$L\ge2\Longrightarrow2\le2^{L-1}$$

まで証明されている。

ただし、positive successor と異なり、まだ abstract carrier への明示的 embedding は追加されていない。

次の定義は直ちに構成できる。

```lean
noncomputable def abstractSaturatedUnitEmbeddingZeroSuccessor
    {n : OddNat} {k : ℕ}
    (hL : 2 ≤ canonicalBlockLength n (k + 1)) :
    Fin 2 ↪ CanonicalAbstractDyadicBudgetCarrier n (k + 1)
```

写像は単に `i ↦ i` でよい。

これを追加すると、abstract dyadic 層で未処理になるのは、

$$L=1,\qquad v=1,\qquad A=1,\qquad D=0$$

という最小 full-balanced successor だけになる。

つまり source-level では rigid class が二種類残るが、abstract dyadic capacity の層では一種類まで縮む。

---

## 8. Length-one residue grammar

saturated predecessor の odd core を $u$ とする。

既存 normal form では、

$$x_{k+1}=\frac{9u-1}{2}$$

じゃ。

successor length が $1$ なら、

$$u\equiv3\pmod8$$

が証明された。

ここから `% 16 = 11` 候補も、算術的には正しい形が見えている。

successor length が $1$ なら successor odd core は、

$$u'=\frac{9u+1}{4}$$

となる。

その terminal carrier は、

$$3u'-1=\frac{27u-1}{4}$$

じゃ。

successor terminal valuation が $1$ である条件は、

$$\frac{27u-1}{4}\equiv2\pmod4$$

すなわち、

$$27u-1\equiv8\pmod{16}$$

である。

$27\equiv11\pmod{16}$ かつ $11^{-1}\equiv3\pmod{16}$ なので、

$$u\equiv11\pmod{16}$$

を得る。

したがって report の `% 16 = 11` は単なる実験予想ではない。必要なのは、この計算を Lean が利用できる successor odd-core / terminal-carrier substitution theorem として固定することだけじゃ。

---

## 9. 唯一の length-one claim 条件

length-one block では claim depth は $1$ しか存在しない。

今回、

$$A=1\iff\operatorname{CarryTwoDebtAt}(e_k)$$

が証明された。

したがって abstract dyadic capacity が不足する唯一の局所候補は、次まで圧縮された。

```text
saturated predecessor
successor length = 1
successor terminal valuation = 1
successor endpoint CarryTwoDebtAt
```

predecessor core では、

```text
u ≡ 11 mod 16
```

が必要になる。

この状態が本当に発生可能か、また繰り返し発生できるかが次の局所 arithmetic branch じゃ。

---

## 10. Abstract carrier の評価

```lean
CanonicalAbstractDyadicBudgetCarrier
```

は `Fin (2^(L-1))` である。

これは **bit position の集合ではない**。

一つの自然数が持つ bit position 数はおよそ $L$ 個だが、abstract carrier は $2^{L-1}$ 個の leaf を持つ。

したがって、次のような単純な injection は一般に不可能じゃ。

```text
Fin (2^(L-1))
  ↪
bit positions of one L-bit number
```

必要なのは bit position 自体ではなく、例えば、

```text
root bit position
+
その位置が表す有限 binary refinement leaves
```

という weighted resource である。

候補は、

```lean
Σ root : UpperBoundaryRoot, Fin (2 ^ root.rank)
```

または有限 binary tree の leaf carrier じゃ。

よって「upper-zero bit-position carrier がない」という停止理由は、より正確には、

> **bit position に付随する dyadic leaf capacity と、その leaf が block 間で重複消費されないことを表す保存 API がない**

ということになる。

---

## 11. 真正な global obstruction

局所 block ごとに、

$$2^{L-1}$$

の budget を新しく発行してよいなら、全 block は容易に自分の demand を払えてしまう。

しかし、それでは有限開始値から生まれた資源ではなく、時間ごとに無限に新しい通貨を発行しているだけじゃ。

必要なのは次の theorem である。

```text
各 block-local budget root は、
有限開始値の global upper-boundary forest の部分木へ割り当てられる。

異なる block に割り当てられた leaves は、
互いに素であるか、少なくとも再利用回数が一様有界である。
```

したがって、現在の真正な障害は carrier の「定義不足」ではなく、

> **block-local budget の非生成・非重複・大域保存則**

じゃ。

これは report の停止判断を否定しない。むしろ、その数学的中身をより正確にしたものじゃ。

---

## 12. Lean Comparator Challenge への現在地

最終出口は、

```lean
theorem collatz_conjecture (n : ℕ) (hn : n > 0) :
  ∃ m, collatzStep^[m] n = 1
```

じゃ。

cp-326 では局所 positive drift が次まで処理された。

```text
negative successor
  -> scalar repayment

spare successor
  -> actual source incidence

positive rigid successor
  -> abstract dyadic half-budget

zero rigid successor with length >= 2
  -> numerical dyadic capacity

length-one full-balanced successor
  -> mod-16 / carry-two arithmetic candidate
```

残る大域問題は、これらの abstract budget を有限開始値の一回限りの資源へ接続することじゃ。

---

## 判定まとめ

### Claim-hole normal form

**完成。今後の primary accounting API。**

### Spare cardinality through holes

**完成。**

### Zero-carrier balanced normal form

**完成。**

### Unique missing depth

**完成。内部位置の追加分類余地あり。**

### Saturated successor source discharge

**negative / spare branches は完成。**

### Dyadic half-budget

**完成。非重複 abstract embedding まで到達。**

### Zero-successor abstract embedding

**数値上完成。明示 carrier embedding が薄く未実装。**

### `% 16 = 11` residue

**数学的には導出可能。Lean substitution bridge が未実装。**

### 真正な障害

**block-local dyadic budget を有限 global resource へ非重複輸送する保存則。**

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge FloatWindow branch after
report-petal-326.

The cp-326 implementation is accepted.

Claim-hole accounting and the abstract dyadic half-budget are complete.

Refine the stopping diagnosis:

    the missing object is not merely a finite set of upper-zero bit positions;

    the real missing theorem is a conserved, nonduplicating transport from
    block-local dyadic budget leaves to a finite global upper-boundary resource.

Before starting that global layer, close the remaining local arithmetic and
carrier details.

## Stage A — zero-successor abstract carrier

For a saturated predecessor whose successor has zero drift and length at least
two, construct explicitly:

    Fin 2
      ↪
    CanonicalAbstractDyadicBudgetCarrier n (k + 1).

Use the low two slots.

Prove that all zero-drift successors of length at least two are discharged at
the abstract dyadic level.

Conclude that the only locally insufficient abstract successor candidate is:

    successor length = 1;
    terminal valuation = 1;
    claim count = 1;
    endpoint CarryTwoDebtAt.

Do not call this an actual bit repayment.

## Stage B — exact successor core substitution

For a saturated block with predecessor odd core `u`, expose the existing exact
successor data as public theorems:

    successor start = (9 * u - 1) / 2;

    if successor length = 1 then
      successor odd core = (9 * u + 1) / 4;

    successor terminal carrier
      = 3 * successor odd core - 1
      = (27 * u - 1) / 4.

Avoid repeatedly unfolding the whole canonical normal form.

## Stage C — modulo-sixteen theorem

Under:

    saturated predecessor;
    successor length = 1;

prove:

    successor terminal valuation = 1
      <->
    predecessor odd core % 16 = 11.

A convenient intermediate form is:

    successor terminal carrier % 4 = 2
      <->
    predecessor odd core % 16 = 11.

Retain the existing modulo-eight theorem as a coarse corollary.

## Stage D — unique length-one obstruction predicate

Define:

    CanonicalLengthOneBalancedCarrySuccessor n k

for a saturated predecessor `k`, requiring on `k + 1`:

    block length = 1;
    terminal valuation = 1;
    claim count = 1.

Prove equivalent presentations using:

    predecessor odd core % 16 = 11;
    endpoint CarryTwoDebtAt.

Separate the arithmetic residue condition from the carry-two condition; neither
should be silently inferred from the other.

## Stage E — persistence grammar

For a `CanonicalLengthOneBalancedCarrySuccessor`, compute:

    successor start;
    successor odd core;
    following block start;
    following block length lower bounds;
    following drift or spare conditions.

Determine whether another saturated block can occur immediately or after one
additional block.

Seek an exact finite residue grammar modulo 32 or 64 only after the modulo-16
normal form is proved.

Do not substitute broad statistical enumeration for the grammar.

## Stage F — claim-hole position refinement

For one-hole blocks, split the unique missing depth into:

    missing depth = 1;
    1 < missing depth < block length;
    missing depth = block length.

For each case expose which existing claim/carry theorem is violated or
satisfied.

Apply the split to:

    tight valuation-one positive blocks;
    exceptional length-two balanced blocks.

Investigate whether the rigid successor grammar forces the missing depth to a
specific endpoint.

## Stage G — abstract dyadic forest API

Create an experimental Collatz-independent finite binary resource module.

Define a full binary leaf carrier of rank `r`:

    DyadicLeafCarrier r := Fin (2^r).

Provide exact disjoint splitting equivalences:

    DyadicLeafCarrier (r + 1)
      ≃
    DyadicLeafCarrier r ⊕ DyadicLeafCarrier r.

Define subtree addresses as finite bit words or `Fin (2^r)` intervals.

Prove:

    left and right subtree leaf images are disjoint;
    repeated refinement preserves cardinality;
    a leaf is owned by exactly one subtree at a fixed partition.

This module is abstract.  Do not mention orbit bits yet.

## Stage H — block-local budget package

Package for every block:

    block rank = blockLength - 1;
    abstract leaf budget;
    own positive-drift demand image;
    optional preceding saturated-unit image.

For a positive nonsaturated successor, reuse the cp-326 lower/upper embeddings.

For a zero-drift successor of length at least two, use only the saturated-unit
image.

Prove all local demand images are pairwise disjoint inside one block budget.

## Stage I — global root-resource specification

Before constructing any global matcher, define the exact interface that a real
upper-boundary resource must satisfy.

A candidate structure should contain:

    a finite root carrier determined only by the initial natural number;
    a rank for each root;
    a map assigning each block-local budget to a root subtree;
    temporal monotonicity;
    pairwise disjoint leaf ownership, or a uniform reuse bound;
    no creation of new roots during the orbit.

Do not assert that this structure exists.

Prove that existence of such a structure would bound the total abstract demand.

This should be a conditional theorem.

## Stage J — audit actual upper-window APIs

Inspect the existing fixed-width upper-carry, bit-width, eventually-zero, and
canonical block APIs.

For each, record whether it supplies:

    root identity;
    root rank;
    subtree refinement;
    temporal ownership;
    nonreuse.

Scalar inequalities alone do not satisfy the interface.

Attempt the weakest bridge:

    one actual upper-zero boundary interval
      ->
    one abstract dyadic root.

Stop immediately if the same interval can be assigned to arbitrarily many
blocks without a multiplicity theorem.

## Stage K — challenge-facing consequence surface

Keep the final route visible.

Prove a conditional theorem of the form:

    finite global upper-resource structure
      ->
    uniform bound on all-depth causal demand
      ->
    uniform bit-width bound.

Do not yet claim cycle rigidity or Collatz convergence.

This theorem should show exactly which missing hypothesis stands between the
current local theory and the Lean Comparator challenge.

## Stopping rule

Stop at the first genuine obstruction among:

    zero-successor abstract embedding fails;
    successor terminal-carrier substitution cannot be exposed;
    modulo-sixteen equivalence fails;
    length-one obstruction has no finite continuation grammar;
    one-hole position cannot be connected to carry structure;
    abstract dyadic forest cannot preserve unique leaf ownership;
    global root-resource interface cannot imply a finite demand bound;
    existing upper-window intervals admit uncontrolled reuse.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-327.md
```

cp-326 で局所通貨の額面と分割法はできた。

次は、その通貨が **有限開始値から本当に発行されたものか**を証明する段階じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean
index 23b4b59f..d97bbc01 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean
@@ -1633,6 +1633,68 @@ noncomputable def oneEmbedding_canonicalSelectedDriftSpareCarrier
 
 /-! ## Exact no-spare classes -/
 
+/-! ### Claim-hole accounting normal form -/
+
+/-- Positive depths in the block which do not carry a canonical payment
+claim. -/
+noncomputable def canonicalBlockClaimHoles
+    (n : OddNat) (k : ℕ) : Finset ℕ :=
+  Finset.Icc 1 (canonicalBlockLength n k) \
+    canonicalPaymentClaimDepths n k
+
+/-- Claim depths and claim holes are disjoint by construction. -/
+theorem canonicalPaymentClaimDepths_disjoint_claimHoles
+    (n : OddNat) (k : ℕ) :
+    Disjoint (canonicalPaymentClaimDepths n k)
+      (canonicalBlockClaimHoles n k) := by
+  classical
+  rw [Finset.disjoint_left]
+  intro d hdClaim hdHole
+  exact (Finset.mem_sdiff.mp hdHole).2 hdClaim
+
+/-- Claims and holes partition the complete positive depth interval. -/
+theorem canonicalPaymentClaimDepths_union_claimHoles
+    (n : OddNat) (k : ℕ) :
+    canonicalPaymentClaimDepths n k ∪ canonicalBlockClaimHoles n k =
+      Finset.Icc 1 (canonicalBlockLength n k) := by
+  classical
+  ext d
+  rw [Finset.mem_union, Finset.mem_Icc]
+  constructor
+  · rintro (hd | hd)
+    · rcases mem_canonicalPaymentClaimDepths_iff.mp hd with ⟨hd1, hdL, _⟩
+      exact ⟨hd1, hdL⟩
+    · exact (Finset.mem_sdiff.mp hd).1 |> Finset.mem_Icc.mp
+  · intro hd
+    by_cases hclaim : d ∈ canonicalPaymentClaimDepths n k
+    · exact Or.inl hclaim
+    · exact Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr hd, hclaim⟩)
+
+/-- Claim count plus missing-depth count is exactly block length. -/
+theorem canonicalBlockClaimCount_add_claimHoles_card
+    (n : OddNat) (k : ℕ) :
+    canonicalBlockClaimCount n k + (canonicalBlockClaimHoles n k).card =
+      canonicalBlockLength n k := by
+  have hcard := Finset.card_union_of_disjoint
+    (canonicalPaymentClaimDepths_disjoint_claimHoles n k)
+  rw [canonicalPaymentClaimDepths_union_claimHoles,
+    ← canonicalBlockClaimCount_eq_claimDepths_card, Nat.card_Icc] at hcard
+  have hL := one_le_canonicalBlockLength n k
+  omega
+
+/-- Primary signed block-accounting normal form: drift is block length minus
+terminal capacity minus the missing claim depths. -/
+theorem endpointAccountingTerm_eq_length_sub_terminalValuation_sub_claimHoles
+    (n : OddNat) (k : ℕ) :
+    endpointAccountingTerm n k =
+      (canonicalBlockLength n k : ℤ) -
+        canonicalBlockTerminalValuation n k -
+          (canonicalBlockClaimHoles n k).card := by
+  have hdrift := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount n k
+  rw [canonicalBlockCapacityCount_eq_terminalValuation] at hdrift
+  have hpartition := canonicalBlockClaimCount_add_claimHoles_card n k
+  omega
+
 /-- At terminal valuation one the selected depth is exactly one. -/
 theorem canonicalSelectedPositivePressureDepth_eq_one_of_terminalValuation_eq_one
     {n : OddNat} {k : ℕ}
@@ -1652,6 +1714,64 @@ theorem card_selectedPressureCarrier_of_terminalValuation_eq_one
   change canonicalBlockLength n k - 2 = canonicalBlockLength n k - 2
   rfl
 
+/-- At valuation one, every hole after the first one is exactly one spare
+selected incidence. -/
+theorem card_selectedDriftSpareCarrier_eq_claimHoles_card_sub_one
+    {n : OddNat} {k : ℕ}
+    (hpos : 0 < endpointAccountingTerm n k)
+    (hnot : ¬ CanonicalSaturatedBorderBlock n k)
+    (hv : canonicalBlockTerminalValuation n k = 1) :
+    (canonicalSelectedDriftSpareCarrier n k).card =
+      (canonicalBlockClaimHoles n k).card - 1 := by
+  have himage := card_canonicalSelectedDriftImageCarrier hpos hnot
+  have hselected := card_selectedPressureCarrier_of_terminalValuation_eq_one hv
+  have hsplit := card_selectedPressureCarrier_eq_driftImage_add_spare n k
+  have hpartition := canonicalBlockClaimCount_add_claimHoles_card n k
+  have hdrift := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount n k
+  rw [canonicalBlockCapacityCount_eq_terminalValuation, hv] at hdrift
+  have hcast : ((Int.toNat (endpointAccountingTerm n k) : ℕ) : ℤ) =
+      endpointAccountingTerm n k := Int.toNat_of_nonneg hpos.le
+  omega
+
+/-- At terminal valuation at least two, claim holes and spare selected
+incidences have exactly the same cardinality. -/
+theorem card_selectedDriftSpareCarrier_eq_claimHoles_card
+    {n : OddNat} {k : ℕ}
+    (hpos : 0 < endpointAccountingTerm n k)
+    (hnot : ¬ CanonicalSaturatedBorderBlock n k)
+    (hv : 2 ≤ canonicalBlockTerminalValuation n k) :
+    (canonicalSelectedDriftSpareCarrier n k).card =
+      (canonicalBlockClaimHoles n k).card := by
+  have himage := card_canonicalSelectedDriftImageCarrier hpos hnot
+  have hsplit := card_selectedPressureCarrier_eq_driftImage_add_spare n k
+  have hpartition := canonicalBlockClaimCount_add_claimHoles_card n k
+  have hdrift := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount n k
+  rw [canonicalBlockCapacityCount_eq_terminalValuation] at hdrift
+  have hcast : ((Int.toNat (endpointAccountingTerm n k) : ℕ) : ℤ) =
+      endpointAccountingTerm n k := Int.toNat_of_nonneg hpos.le
+  have hselected : (canonicalSelectedPressureCarrier n k).card =
+      canonicalBlockLength n k - canonicalBlockTerminalValuation n k := by
+    unfold canonicalSelectedPressureCarrier
+    rw [canonicalPaymentBlockContinuationFiber_card,
+      canonicalSelectedPositivePressureDepth, if_neg (by omega)]
+    change canonicalBlockLength n k -
+      (canonicalBlockTerminalValuation n k - 1 + 1) =
+        canonicalBlockLength n k - canonicalBlockTerminalValuation n k
+    omega
+  omega
+
+/-- At terminal valuation at least two, a spare incidence exists exactly when
+there is a missing claim depth. -/
+theorem selectedDriftSpareCarrier_nonempty_iff_claimHoles_nonempty_of_val_ge_two
+    {n : OddNat} {k : ℕ}
+    (hpos : 0 < endpointAccountingTerm n k)
+    (hnot : ¬ CanonicalSaturatedBorderBlock n k)
+    (hv : 2 ≤ canonicalBlockTerminalValuation n k) :
+    (canonicalSelectedDriftSpareCarrier n k).Nonempty ↔
+      (canonicalBlockClaimHoles n k).Nonempty := by
+  rw [← Finset.card_pos, ← Finset.card_pos,
+    card_selectedDriftSpareCarrier_eq_claimHoles_card hpos hnot hv]
+
 /-- Tight positive valuation-one blocks are precisely the candidate class in
 which selected drift consumes every selected incidence. -/
 def CanonicalTightValuationOnePositiveBlock
@@ -1661,6 +1781,34 @@ def CanonicalTightValuationOnePositiveBlock
       canonicalBlockTerminalValuation n k = 1 ∧
         canonicalBlockClaimCount n k = canonicalBlockLength n k - 1
 
+/-- Hole normal form of the tight valuation-one class. -/
+theorem canonicalTightValuationOnePositiveBlock_iff_claimHoles_card_eq_one
+    (n : OddNat) (k : ℕ) :
+    CanonicalTightValuationOnePositiveBlock n k ↔
+      0 < endpointAccountingTerm n k ∧
+        ¬ CanonicalSaturatedBorderBlock n k ∧
+          canonicalBlockTerminalValuation n k = 1 ∧
+            (canonicalBlockClaimHoles n k).card = 1 := by
+  unfold CanonicalTightValuationOnePositiveBlock
+  have hpartition := canonicalBlockClaimCount_add_claimHoles_card n k
+  have hL := one_le_canonicalBlockLength n k
+  constructor <;> rintro ⟨hpos, hnot, hv, hcount⟩
+  · exact ⟨hpos, hnot, hv, by omega⟩
+  · exact ⟨hpos, hnot, hv, by omega⟩
+
+/-- A positive nonsaturated valuation-one block has a spare incidence exactly
+when it has at least two claim holes. -/
+theorem selectedDriftSpareCarrier_nonempty_iff_two_le_claimHoles_card_of_val_one
+    {n : OddNat} {k : ℕ}
+    (hpos : 0 < endpointAccountingTerm n k)
+    (hnot : ¬ CanonicalSaturatedBorderBlock n k)
+    (hv : canonicalBlockTerminalValuation n k = 1) :
+    (canonicalSelectedDriftSpareCarrier n k).Nonempty ↔
+      2 ≤ (canonicalBlockClaimHoles n k).card := by
+  rw [← Finset.card_pos,
+    card_selectedDriftSpareCarrier_eq_claimHoles_card_sub_one hpos hnot hv]
+  omega
+
 /-- Under the positive nonsaturated valuation-one hypotheses, no spare source
 incidence is exactly the near-full-claims condition. -/
 theorem selectedDriftSpareCarrier_eq_empty_iff_claimCount_eq_length_sub_one
@@ -1760,6 +1908,157 @@ def CanonicalZeroCarrierBalancedBorderBlock
   endpointAccountingTerm n k = 0 ∧
     canonicalSelectedPressureCarrier n k = ∅
 
+/-- Exact arithmetic normal form of a zero-drift block with no selected source
+incidence. -/
+theorem canonicalZeroCarrierBalancedBorderBlock_iff
+    (n : OddNat) (k : ℕ) :
+    CanonicalZeroCarrierBalancedBorderBlock n k ↔
+      (canonicalBlockLength n k = canonicalBlockTerminalValuation n k ∧
+        canonicalBlockClaimCount n k = canonicalBlockLength n k) ∨
+      (canonicalBlockTerminalValuation n k = 1 ∧
+        canonicalBlockLength n k = 2 ∧
+        canonicalBlockClaimCount n k = 1) := by
+  constructor
+  · rintro ⟨hzero, hempty⟩
+    have hclaim := claimCount_eq_terminalValuation_of_endpointAccountingTerm_eq_zero hzero
+    have hclaimLe := canonicalBlockClaimCount_le_length n k
+    have hvpos := one_le_canonicalBlockTerminalValuation n k
+    by_cases hv : canonicalBlockTerminalValuation n k = 1
+    · have hL :=
+        (selectedPressureCarrier_eq_empty_iff_length_le_two_of_zero_val_one
+          hzero hv).1 hempty
+      by_cases hLen : canonicalBlockLength n k = 1
+      · exact Or.inl ⟨by omega, by omega⟩
+      · exact Or.inr ⟨hv, by omega, by omega⟩
+    · have hv2 : 2 ≤ canonicalBlockTerminalValuation n k := by omega
+      have hL :=
+        (selectedPressureCarrier_eq_empty_iff_length_le_terminalValuation_of_zero
+          hzero hv2).1 hempty
+      exact Or.inl ⟨by omega, by omega⟩
+  · rintro (hfull | hexceptional)
+    · rcases hfull with ⟨hLv, hclaimL⟩
+      have hzero := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount n k
+      rw [canonicalBlockCapacityCount_eq_terminalValuation, hclaimL, hLv] at hzero
+      have hvpos := one_le_canonicalBlockTerminalValuation n k
+      by_cases hv : canonicalBlockTerminalValuation n k = 1
+      · refine ⟨by omega,
+          (selectedPressureCarrier_eq_empty_iff_length_le_two_of_zero_val_one
+            (by omega) hv).2 (by omega)⟩
+      · refine ⟨by omega,
+          (selectedPressureCarrier_eq_empty_iff_length_le_terminalValuation_of_zero
+            (by omega) (by omega)).2 (by omega)⟩
+    · rcases hexceptional with ⟨hv, hL, hclaim⟩
+      have hzero := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount n k
+      rw [canonicalBlockCapacityCount_eq_terminalValuation, hv, hclaim] at hzero
+      exact ⟨by omega,
+        (selectedPressureCarrier_eq_empty_iff_length_le_two_of_zero_val_one
+          (by omega) hv).2 (by omega)⟩
+
+/-- The full balanced no-carrier branch has no claim holes. -/
+theorem claimHoles_card_eq_zero_of_full_balanced
+    {n : OddNat} {k : ℕ}
+    (hL : canonicalBlockLength n k = canonicalBlockTerminalValuation n k)
+    (hclaim : canonicalBlockClaimCount n k = canonicalBlockLength n k) :
+    (canonicalBlockClaimHoles n k).card = 0 := by
+  have hpartition := canonicalBlockClaimCount_add_claimHoles_card n k
+  omega
+
+/-- The exceptional length-two balanced branch has one missing claim depth. -/
+theorem claimHoles_card_eq_one_of_exceptional_length_two_balanced
+    {n : OddNat} {k : ℕ}
+    (hL : canonicalBlockLength n k = 2)
+    (hclaim : canonicalBlockClaimCount n k = 1) :
+    (canonicalBlockClaimHoles n k).card = 1 := by
+  have hpartition := canonicalBlockClaimCount_add_claimHoles_card n k
+  omega
+
+/-! ### Unique missing claim depth -/
+
+/-- The unique missing depth of a block whose claim-hole carrier has
+cardinality one. -/
+noncomputable def canonicalBlockMissingClaimDepth
+    {n : OddNat} {k : ℕ}
+    (h : (canonicalBlockClaimHoles n k).card = 1) : ℕ :=
+  (Finset.card_eq_one.mp h).choose
+
+/-- The one-hole carrier is the singleton containing its chosen missing
+depth. -/
+theorem canonicalBlockClaimHoles_eq_singleton_missingDepth
+    {n : OddNat} {k : ℕ}
+    (h : (canonicalBlockClaimHoles n k).card = 1) :
+    canonicalBlockClaimHoles n k = {canonicalBlockMissingClaimDepth h} := by
+  exact (Finset.card_eq_one.mp h).choose_spec
+
+/-- With one missing depth, the claim-depth carrier is exactly the complete
+positive interval with that depth erased. -/
+theorem canonicalPaymentClaimDepths_eq_Icc_erase_missingDepth
+    {n : OddNat} {k : ℕ}
+    (h : (canonicalBlockClaimHoles n k).card = 1) :
+    canonicalPaymentClaimDepths n k =
+      (Finset.Icc 1 (canonicalBlockLength n k)).erase
+        (canonicalBlockMissingClaimDepth h) := by
+  classical
+  let missing := canonicalBlockMissingClaimDepth h
+  have hholes : canonicalBlockClaimHoles n k = {missing} :=
+    canonicalBlockClaimHoles_eq_singleton_missingDepth h
+  ext d
+  rw [Finset.mem_erase, Finset.mem_Icc]
+  constructor
+  · intro hdClaim
+    rcases mem_canonicalPaymentClaimDepths_iff.mp hdClaim with
+      ⟨hd1, hdL, _⟩
+    refine ⟨?_, hd1, hdL⟩
+    intro hdm
+    have hmHole : missing ∈ canonicalBlockClaimHoles n k := by
+      rw [hholes]
+      simp
+    exact (Finset.mem_sdiff.mp hmHole).2 (by simpa [hdm] using hdClaim)
+  · rintro ⟨hdm, hd1, hdL⟩
+    by_contra hdClaim
+    have hdHole : d ∈ canonicalBlockClaimHoles n k :=
+      Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨hd1, hdL⟩, hdClaim⟩
+    have : d = missing := by
+      rw [hholes] at hdHole
+      simpa using hdHole
+    exact hdm this
+
+/-- The unique missing depth is either the endpoint depth or a delayed depth. -/
+theorem canonicalBlockMissingClaimDepth_eq_one_or_gt_one
+    {n : OddNat} {k : ℕ}
+    (h : (canonicalBlockClaimHoles n k).card = 1) :
+    canonicalBlockMissingClaimDepth h = 1 ∨
+      1 < canonicalBlockMissingClaimDepth h := by
+  have hmem : canonicalBlockMissingClaimDepth h ∈ canonicalBlockClaimHoles n k := by
+    rw [canonicalBlockClaimHoles_eq_singleton_missingDepth h]
+    simp
+  have hIcc := (Finset.mem_sdiff.mp hmem).1
+  have hone := (Finset.mem_Icc.mp hIcc).1
+  omega
+
+/-- Tight valuation-one positive blocks have a unique missing claim depth. -/
+theorem CanonicalTightValuationOnePositiveBlock.claimDepths_eq_erase_missing
+    {n : OddNat} {k : ℕ} (h : CanonicalTightValuationOnePositiveBlock n k) :
+    canonicalPaymentClaimDepths n k =
+      (Finset.Icc 1 (canonicalBlockLength n k)).erase
+        (canonicalBlockMissingClaimDepth
+          ((canonicalTightValuationOnePositiveBlock_iff_claimHoles_card_eq_one
+            n k).1 h).2.2.2) :=
+  canonicalPaymentClaimDepths_eq_Icc_erase_missingDepth
+    ((canonicalTightValuationOnePositiveBlock_iff_claimHoles_card_eq_one n k).1 h).2.2.2
+
+/-- The exceptional length-two balanced branch also has a unique missing claim
+depth. -/
+theorem exceptionalLengthTwoBalanced_claimDepths_eq_erase_missing
+    {n : OddNat} {k : ℕ}
+    (hL : canonicalBlockLength n k = 2)
+    (hclaim : canonicalBlockClaimCount n k = 1) :
+    canonicalPaymentClaimDepths n k =
+      (Finset.Icc 1 (canonicalBlockLength n k)).erase
+        (canonicalBlockMissingClaimDepth
+          (claimHoles_card_eq_one_of_exceptional_length_two_balanced hL hclaim)) :=
+  canonicalPaymentClaimDepths_eq_Icc_erase_missingDepth
+    (claimHoles_card_eq_one_of_exceptional_length_two_balanced hL hclaim)
+
 /-! ## Saturated-successor source classification
 
 The five-way classification proposed at cp-325 omitted a logically possible
@@ -1790,6 +2089,29 @@ theorem exists_spareSelectedPressureSource_of_pos_of_two_le_terminalValuation
       i ∈ canonicalSelectedDriftSpareCarrier n k :=
   canonicalSelectedDriftSpareCarrier_nonempty hpos hnot hv
 
+/-- A successor has an immediately chargeable spare selected incidence. -/
+def CanonicalSuccessorSpareAvailable (n : OddNat) (j : ℕ) : Prop :=
+  (canonicalSelectedDriftSpareCarrier n j).Nonempty
+
+/-- With zero drift the chosen drift image is empty, so every selected source
+incidence is spare. -/
+theorem successorSpareAvailable_of_zero_of_selectedPressureCarrier_nonempty
+    {n : OddNat} {j : ℕ}
+    (hzero : endpointAccountingTerm n j = 0)
+    (hcarrier : (canonicalSelectedPressureCarrier n j).Nonempty) :
+    CanonicalSuccessorSpareAvailable n j := by
+  have himage : canonicalSelectedDriftImageCarrier n j = ∅ :=
+    canonicalSelectedDriftImageCarrier_eq_empty_of_not_active (by
+      intro hactive
+      omega)
+  have hsplit := card_selectedPressureCarrier_eq_driftImage_add_spare n j
+  rw [himage] at hsplit
+  simp only [Finset.card_empty, zero_add] at hsplit
+  apply Finset.card_pos.mp
+  have hcard : 0 < (canonicalSelectedPressureCarrier n j).card :=
+    Finset.card_pos.mpr hcarrier
+  omega
+
 /-- Exhaustive successor classification currently justified for a saturated
 predecessor.  The final disjunct is the valuation-one spare branch missing
 from the proposed five-way split. -/
@@ -1835,6 +2157,50 @@ theorem CanonicalSaturatedBorderBlock.successor_source_classification
             2 ≤ canonicalBlockTerminalValuation n j := ⟨hpos, hnotsat, hv2⟩
         exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa [j] using hbranch))))
 
+/-- Source-level compression of the detailed six-way successor theorem. -/
+theorem CanonicalSaturatedBorderBlock.successor_negative_or_spare_or_rigid
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
+    endpointAccountingTerm n (k + 1) < 0 ∨
+      CanonicalSuccessorSpareAvailable n (k + 1) ∨
+      CanonicalZeroCarrierBalancedBorderBlock n (k + 1) ∨
+      CanonicalTightValuationOnePositiveBlock n (k + 1) := by
+  rcases h.successor_source_classification with
+    hneg | hzeroSpare | hzeroRigid | hpos2 | htight | hpos1Spare
+  · exact Or.inl hneg
+  · exact Or.inr (Or.inl
+      (successorSpareAvailable_of_zero_of_selectedPressureCarrier_nonempty
+        hzeroSpare.1 hzeroSpare.2))
+  · exact Or.inr (Or.inr (Or.inl hzeroRigid))
+  · exact Or.inr (Or.inl
+      (canonicalSelectedDriftSpareCarrier_nonempty hpos2.1 hpos2.2.1 hpos2.2.2))
+  · exact Or.inr (Or.inr (Or.inr htight))
+  · exact Or.inr (Or.inl hpos1Spare.2.2.2)
+
+/-- A negative successor cancels the saturated predecessor's exact unit
+drift numerically. -/
+theorem CanonicalSaturatedBorderBlock.drift_add_successor_drift_nonpos_of_negative
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
+    (hneg : endpointAccountingTerm n (k + 1) < 0) :
+    endpointAccountingTerm n k + endpointAccountingTerm n (k + 1) ≤ 0 := by
+  rw [h.netDrift_eq_one]
+  omega
+
+/-- Every spare-available successor supplies an explicit singleton embedding
+into its actual spare source carrier. -/
+noncomputable def oneEmbedding_successorSpareCarrier
+    {n : OddNat} {j : ℕ} (h : CanonicalSuccessorSpareAvailable n j) :
+    Fin 1 ↪ {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n j} //
+      i ∈ canonicalSelectedDriftSpareCarrier n j} := by
+  classical
+  letI : Fintype
+      {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n j} //
+        i ∈ canonicalSelectedDriftSpareCarrier n j} :=
+    Fintype.ofFinset (canonicalSelectedDriftSpareCarrier n j) (by simp)
+  apply Classical.choice
+  apply Function.Embedding.nonempty_iff_card_le.mpr
+  rw [Fintype.card_fin, Fintype.card_coe]
+  exact Finset.one_le_card.mpr h
+
 /-! ## Experimental dyadic depth-transfer potential
 
 These inequalities compare numerical denominations only.  They do not define
@@ -1870,6 +2236,97 @@ theorem intToNat_endpointAccountingTerm_le_length_sub_depth_sub_one
   exact_mod_cast (show ((Int.toNat (endpointAccountingTerm n k) : ℕ) : ℤ) ≤
     (L - d - 1 : ℕ) by omega)
 
+/-- Positive nonsaturated blocks have room for a positive selected depth, a
+positive gap, and an endpoint, hence length at least three. -/
+theorem three_le_canonicalBlockLength_of_endpointAccountingTerm_pos_of_not_saturated
+    {n : OddNat} {k : ℕ}
+    (hpos : 0 < endpointAccountingTerm n k)
+    (hnot : ¬ CanonicalSaturatedBorderBlock n k) :
+    3 ≤ canonicalBlockLength n k := by
+  have hbound :=
+    intToNat_endpointAccountingTerm_le_length_sub_depth_sub_one hpos hnot
+  have hcast : ((Int.toNat (endpointAccountingTerm n k) : ℕ) : ℤ) =
+      endpointAccountingTerm n k := Int.toNat_of_nonneg hpos.le
+  have ha : 0 < Int.toNat (endpointAccountingTerm n k) := by omega
+  have hd := one_le_canonicalSelectedPositivePressureDepth n k
+  omega
+
+/-- Elementary half-budget inequality used by the dyadic denomination. -/
+theorem nat_le_two_pow_pred {gap : ℕ} (hgap : 1 ≤ gap) :
+    gap ≤ 2 ^ (gap - 1) := by
+  rcases gap with _ | gap
+  · omega
+  · rcases gap with _ | gap
+    · norm_num
+    · have hpow := (gap + 1).lt_two_pow_self
+      simpa only [Nat.add_sub_cancel, Nat.succ_eq_add_one] using hpow
+
+/-- Strengthened local dyadic potential: positive nonsaturated demand fits in
+one half of the block-width budget. -/
+theorem intToNat_endpointAccountingTerm_mul_two_pow_depth_le_two_pow_length_sub_two
+    {n : OddNat} {k : ℕ}
+    (hpos : 0 < endpointAccountingTerm n k)
+    (hnot : ¬ CanonicalSaturatedBorderBlock n k) :
+    Int.toNat (endpointAccountingTerm n k) *
+        2 ^ canonicalSelectedPositivePressureDepth n k ≤
+      2 ^ (canonicalBlockLength n k - 2) := by
+  let a := Int.toNat (endpointAccountingTerm n k)
+  let d := canonicalSelectedPositivePressureDepth n k
+  let L := canonicalBlockLength n k
+  let gap := L - d - 1
+  have ha : a ≤ gap :=
+    intToNat_endpointAccountingTerm_le_length_sub_depth_sub_one hpos hnot
+  have hcast : ((a : ℕ) : ℤ) = endpointAccountingTerm n k :=
+    Int.toNat_of_nonneg hpos.le
+  have hapos : 0 < a := by omega
+  have hgap : 1 ≤ gap := by omega
+  have hgapPow : gap ≤ 2 ^ (gap - 1) := nat_le_two_pow_pred hgap
+  have hsum : (gap - 1) + d = L - 2 := by
+    have hdL := selectedPositivePressureDepth_lt_length_of_pos_of_not_saturated
+      hpos hnot
+    change d < L at hdL
+    dsimp [gap]
+    omega
+  calc
+    a * 2 ^ d ≤ gap * 2 ^ d := Nat.mul_le_mul_right _ ha
+    _ ≤ 2 ^ (gap - 1) * 2 ^ d := Nat.mul_le_mul_right _ hgapPow
+    _ = 2 ^ ((gap - 1) + d) := by rw [pow_add]
+    _ = 2 ^ (L - 2) := by rw [hsum]
+
+/-- A saturated unit and the positive demand of its nonsaturated successor fit
+in the successor's full local dyadic budget. -/
+theorem CanonicalSaturatedBorderBlock.two_add_successor_dyadic_demand_le
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
+    (hpos : 0 < endpointAccountingTerm n (k + 1)) :
+    2 + Int.toNat (endpointAccountingTerm n (k + 1)) *
+        2 ^ canonicalSelectedPositivePressureDepth n (k + 1) ≤
+      2 ^ (canonicalBlockLength n (k + 1) - 1) := by
+  have hnot := h.not_succ
+  have hdemand :=
+    intToNat_endpointAccountingTerm_mul_two_pow_depth_le_two_pow_length_sub_two
+      hpos hnot
+  have hL :=
+    three_le_canonicalBlockLength_of_endpointAccountingTerm_pos_of_not_saturated
+      hpos hnot
+  have htwo : 2 ≤ 2 ^ (canonicalBlockLength n (k + 1) - 2) := by
+    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (show 1 ≤
+      canonicalBlockLength n (k + 1) - 2 by omega)
+    simpa using this
+  rw [show canonicalBlockLength n (k + 1) - 1 =
+      (canonicalBlockLength n (k + 1) - 2) + 1 by omega, pow_succ]
+  omega
+
+/-- A zero-drift successor of length at least two has enough numerical dyadic
+budget for the preceding saturated unit. -/
+theorem two_le_successor_dyadic_budget_of_two_le_length
+    {n : OddNat} {k : ℕ}
+    (_hzero : endpointAccountingTerm n (k + 1) = 0)
+    (hL : 2 ≤ canonicalBlockLength n (k + 1)) :
+    2 ≤ 2 ^ (canonicalBlockLength n (k + 1) - 1) := by
+  have := Nat.pow_le_pow_right (by norm_num : 0 < 2)
+    (show 1 ≤ canonicalBlockLength n (k + 1) - 1 by omega)
+  simpa using this
+
 /-- Local dyadic potential: the selected positive drift, denominated at depth
 `d`, is bounded by one block-width denomination `2^(L-1)`. -/
 theorem intToNat_endpointAccountingTerm_mul_two_pow_depth_le_two_pow_length_sub_one
@@ -1905,6 +2362,170 @@ theorem CanonicalSaturatedBorderBlock.dyadic_unit_budget
     (1 : ℕ) * 2 ^ 1 = 2 ^ (2 - 1) := by
   norm_num
 
+/-! ## Length-one successor residue audit
+
+The saturated predecessor has odd core congruent to either three or seven
+modulo eight.  A successor of length one excludes the seven class, because the
+existing successor normal form forces length at least two there.  This is the
+finite residue grammar needed before attempting a modulo-sixteen refinement.
+
+The stronger candidate
+
+`successor length = 1` and `successor terminal valuation = 1`
+`-> predecessor odd core % 16 = 11`
+
+requires an explicit normal form connecting the successor odd core (or its
+terminal carrier) to the predecessor odd core.  The current API exposes the
+successor start and successor length, but not that substituted terminal-carrier
+identity.  Do not replace this missing algebraic bridge by computation or a
+statistical residue table.
+-/
+
+/-- A length-one successor of a saturated block selects the class three
+modulo eight for the predecessor odd core. -/
+theorem CanonicalSaturatedBorderBlock.oddCore_mod_eight_eq_three_of_next_length_one
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
+    (hL : canonicalBlockLength n (k + 1) = 1) :
+    canonicalBlockOddCore n k % 8 = 3 := by
+  rcases h.oddCore_mod_eight_eq_three_or_seven with hthree | hseven
+  · exact hthree
+  · have htwo := h.two_le_nextBlockLength_of_core_mod_eight_eq_seven hseven
+    omega
+
+/-- For a length-one block, the sole claim-count condition is exactly the
+carry-two condition at its endpoint source. -/
+theorem canonicalBlockClaimCount_eq_one_iff_endpoint_carryTwo_of_length_one
+    {n : OddNat} {k : ℕ} (hL : canonicalBlockLength n k = 1) :
+    canonicalBlockClaimCount n k = 1 ↔
+      CarryTwoDebtAt n (paymentEndpointSeq n k) := by
+  constructor
+  · intro hcount
+    have hcard : (canonicalPaymentClaimDepths n k).card = 1 := by
+      simpa [canonicalBlockClaimCount_eq_claimDepths_card] using hcount
+    obtain ⟨d, hd⟩ := Finset.card_pos.mp (by omega :
+      0 < (canonicalPaymentClaimDepths n k).card)
+    have hdepth := mem_canonicalPaymentClaimDepths_iff.mp hd
+    have hLen : canonicalPaymentBlockLength n k = canonicalBlockLength n k := rfl
+    have hdOne : d = 1 := by
+      rw [hLen, hL] at hdepth
+      omega
+    subst d
+    exact (one_mem_canonicalPaymentClaimDepths_iff n k).mp hd
+  · intro hcarry
+    have hone : 1 ∈ canonicalPaymentClaimDepths n k :=
+      (one_mem_canonicalPaymentClaimDepths_iff n k).mpr hcarry
+    have hpos : 0 < canonicalBlockClaimCount n k := by
+      rw [canonicalBlockClaimCount_eq_claimDepths_card]
+      exact Finset.card_pos.mpr ⟨1, hone⟩
+    have hle := canonicalBlockClaimCount_le_length n k
+    omega
+
+/-! ## Abstract nonduplicating dyadic carrier
+
+This section realizes the numerical half-budget as two disjoint `Fin` images.
+The low two points carry the preceding saturated unit; the positive successor
+demand is shifted into the upper half.  These are abstract potential slots.
+They are not orbit indices, binary bit positions, or upper-boundary resources.
+-/
+
+/-- Abstract block-width dyadic budget. -/
+abbrev CanonicalAbstractDyadicBudgetCarrier
+    (n : OddNat) (k : ℕ) :=
+  Fin (2 ^ (canonicalBlockLength n k - 1))
+
+/-- Abstract selected positive-drift demand at its dyadic depth. -/
+abbrev CanonicalAbstractDyadicDemandCarrier
+    (n : OddNat) (k : ℕ) :=
+  Fin (Int.toNat (endpointAccountingTerm n k) *
+    2 ^ canonicalSelectedPositivePressureDepth n k)
+
+/-- The positive nonsaturated demand embeds into the upper half of its abstract
+block budget. -/
+noncomputable def abstractDyadicDemandEmbeddingUpperHalf
+    {n : OddNat} {k : ℕ}
+    (hpos : 0 < endpointAccountingTerm n k)
+    (hnot : ¬ CanonicalSaturatedBorderBlock n k) :
+    CanonicalAbstractDyadicDemandCarrier n k ↪
+      CanonicalAbstractDyadicBudgetCarrier n k where
+  toFun i := by
+    let half := 2 ^ (canonicalBlockLength n k - 2)
+    have hdemand :=
+      intToNat_endpointAccountingTerm_mul_two_pow_depth_le_two_pow_length_sub_two
+        hpos hnot
+    have hL :=
+      three_le_canonicalBlockLength_of_endpointAccountingTerm_pos_of_not_saturated
+        hpos hnot
+    refine ⟨half + i.val, ?_⟩
+    rw [show canonicalBlockLength n k - 1 =
+        (canonicalBlockLength n k - 2) + 1 by omega, pow_succ]
+    omega
+  inj' := by
+    intro i j hij
+    have hval := congrArg Fin.val hij
+    change 2 ^ (canonicalBlockLength n k - 2) + i.val =
+      2 ^ (canonicalBlockLength n k - 2) + j.val at hval
+    exact Fin.ext (Nat.add_left_cancel hval)
+
+/-- The preceding saturated mass-two unit occupies the first two abstract
+slots of a positive nonsaturated successor budget. -/
+noncomputable def abstractSaturatedUnitEmbeddingLowerHalf
+    {n : OddNat} {k : ℕ}
+    (hpos : 0 < endpointAccountingTerm n (k + 1))
+    (hnot : ¬ CanonicalSaturatedBorderBlock n (k + 1)) :
+    Fin 2 ↪ CanonicalAbstractDyadicBudgetCarrier n (k + 1) where
+  toFun i := by
+    have hL :=
+      three_le_canonicalBlockLength_of_endpointAccountingTerm_pos_of_not_saturated
+        hpos hnot
+    refine ⟨i.val, ?_⟩
+    have hfour : 4 ≤ 2 ^ (canonicalBlockLength n (k + 1) - 1) := by
+      have := Nat.pow_le_pow_right (by norm_num : 0 < 2)
+        (show 2 ≤ canonicalBlockLength n (k + 1) - 1 by omega)
+      simpa using this
+    omega
+  inj' := by
+    intro i j hij
+    have hval := congrArg Fin.val hij
+    change i.val = j.val at hval
+    exact Fin.ext hval
+
+/-- The saturated-unit image and successor-demand image are explicitly
+disjoint in the abstract successor budget. -/
+theorem abstractSaturatedUnitEmbeddingLowerHalf_ne_demandEmbeddingUpperHalf
+    {n : OddNat} {k : ℕ}
+    (hpos : 0 < endpointAccountingTerm n (k + 1))
+    (hnot : ¬ CanonicalSaturatedBorderBlock n (k + 1))
+    (i : Fin 2) (j : CanonicalAbstractDyadicDemandCarrier n (k + 1)) :
+    abstractSaturatedUnitEmbeddingLowerHalf hpos hnot i ≠
+      abstractDyadicDemandEmbeddingUpperHalf hpos hnot j := by
+  intro heq
+  have hL :=
+    three_le_canonicalBlockLength_of_endpointAccountingTerm_pos_of_not_saturated
+      hpos hnot
+  have hhalf : 2 ≤ 2 ^ (canonicalBlockLength n (k + 1) - 2) := by
+    have := Nat.pow_le_pow_right (by norm_num : 0 < 2)
+      (show 1 ≤ canonicalBlockLength n (k + 1) - 2 by omega)
+    simpa using this
+  have hval := congrArg Fin.val heq
+  dsimp [abstractSaturatedUnitEmbeddingLowerHalf,
+    abstractDyadicDemandEmbeddingUpperHalf] at hval
+  omega
+
+/-!
+## Actual upper-boundary audit
+
+The existing upper-window API records scalar carries, widths, and eventually
+zero statements.  It does not expose a finite carrier of distinct upper-zero
+bit positions, nor a finite binary refinement tree whose leaves are consumed
+at most once.  Consequently the abstract embeddings above cannot yet be
+transported into a nonreusable initial-state resource.  Reusing one scalar
+upper-boundary fact for several block budgets would invalidate the accounting.
+
+This is the genuine boundary of the present branch: a future theorem must
+define an actual finite upper resource and prove a uniform nonreuse or
+multiplicity bound before any global repayment conclusion is sound.
+-/
+
 /-!
 ## Current boundary after the causal depth queue
 
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-326.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-326.md
new file mode 100644
index 00000000..e57428e8
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-326.md
@@ -0,0 +1,141 @@
+# Petal / FloatWindow Report cp-326
+
+## Status
+
+`cp-326` closes the local claim-hole, successor-source, and abstract dyadic
+budget program without `sorry`.  The branch stops at the first genuine global
+resource obstruction: the current upper-window API has no finite,
+nonreusable carrier of upper-boundary bit positions.
+
+## Implemented results
+
+### Claim-hole accounting
+
+`canonicalBlockClaimHoles` is the complement of the payment claim depths in
+the complete depth interval.  Lean now proves disjointness, exact union, and
+
+```text
+claimCount + claimHoles.card = blockLength.
+```
+
+The primary signed normal form is therefore
+
+```text
+endpointAccountingTerm
+  = blockLength - terminalValuation - claimHoles.card.
+```
+
+This one formula controls saturation, balanced blocks, positive spare
+cardinality, and tight valuation-one blocks.
+
+### Exact rigid and spare classes
+
+The selected spare carrier has exact cardinality:
+
+```text
+terminal valuation = 1  -> holes.card - 1
+terminal valuation >= 2 -> holes.card.
+```
+
+The zero-carrier balanced class has exactly two normal forms:
+
+1. `length = terminal valuation` and every depth is claimed;
+2. `terminal valuation = 1`, `length = 2`, and exactly one depth is claimed.
+
+A singleton claim hole has a chosen unique missing depth, and the claim set is
+the complete interval with precisely that depth erased.
+
+### Saturated successor compression
+
+The detailed six-way successor theorem compresses to four source-level cases:
+
+```text
+negative drift
+or actual spare source
+or zero-carrier balanced block
+or tight valuation-one positive block.
+```
+
+The negative successor numerically cancels the saturated unit.  The spare
+branch supplies an actual `Fin 1` embedding into the selected spare incidence
+carrier.  Thus the valuation-one nonempty-spare branch is discharged and is
+not an obstruction.
+
+### Dyadic half-budget
+
+Every positive nonsaturated block has length at least three.  Its selected
+dyadic demand satisfies the stronger bound
+
+```text
+toNat drift * 2^selectedDepth <= 2^(blockLength - 2).
+```
+
+Consequently a saturated mass-two unit and a positive nonsaturated successor
+demand fit into the successor budget `2^(blockLength - 1)`.
+
+The numerical statement was strengthened to an explicit abstract carrier:
+
+- `Fin 2` embeds into the low slots;
+- the successor demand embeds into the upper half;
+- Lean proves every point in the two images is distinct.
+
+This is an abstract potential carrier only.  It is not a carrier of orbit
+indices or physical bit positions.
+
+### Length-one residue grammar
+
+For a saturated predecessor, a successor of length one forces
+
+```text
+canonicalBlockOddCore n k % 8 = 3.
+```
+
+The `% 16 = 11` candidate needs one additional algebraic bridge: an explicit
+formula transporting the predecessor odd core through the successor odd core
+into the successor terminal carrier.  Existing APIs expose the successor
+start and length separately but not this substituted terminal-carrier normal
+form.  No empirical residue claim was substituted for that missing theorem.
+
+## Genuine obstruction
+
+The upper-window modules currently expose scalar width/carry and eventual-zero
+facts.  They do not expose any of the following:
+
+- a finite carrier of distinct upper-zero bit positions;
+- a finite binary refinement tree rooted at a boundary position;
+- a uniform multiplicity theorem preventing reuse of one boundary resource by
+  several block budgets.
+
+Therefore the abstract dyadic leaves cannot yet be transported to a finite
+nonreusable initial-state resource.  A global repayment or convergence claim
+does not follow from the present local bounds.
+
+## Next implementation
+
+The next sound layer should first define a concrete upper-boundary resource
+carrier and prove its nonreuse invariant.  Separately, the local arithmetic
+branch can add the successor odd-core/terminal-carrier substitution theorem
+needed to decide the candidate `% 16 = 11` residue implication.
+
+Do not begin a global matcher until at least one of those two interfaces is
+available.
+
+## Verification
+
+The targeted module build passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude
+```
+
+The complete gates passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath
+git diff --check
+```
+
+The top-level build replays known `sorry` warnings in unrelated research
+modules.  This checkpoint adds no `sorry` and no `maxHeartbeats` override.
````
`````
