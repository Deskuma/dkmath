# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock

gch: b69af71d02e4a6dfb7bad11edf5d5cf1a327e985

## Report

実装を進めました。

今回確定した内容:

- universal source fiber の membership は、範囲条件なしに
  `orbitPaymentTarget n i = j`
  と同値。
- universal endpoint の complete carry-two claim fiber は、
  universal block 上の carry-two filter と厳密に一致。
- その card equality を追加。
- universal block の extra-height capacity は、内部の height-one 項が消えるため endpoint capacity に集中。

これで、debt-supported suffix を仮定せずに universal block の claim 側と capacity 側を直接扱える土台が揃いました。次は generic shifted ledger とこの二つの直接同一視を合成し、universal block ledger を閉じる段階です。

`lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock` は成功しています。

# report を書き忘れる by GPT-5.6 Terra light

その通りです。cp-308 の指示に report 作成があり、実装事実の整理を優先して失念しました。

[report-petal-308.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-308.md) を追加しました。

特に、universal block 全体の carry-two filter が complete claim fiber と一致し、capacity が endpoint に集中することを、direct universal ledger への接続として記録しています。

## Review

## 結論

**採用。進展はかなり重要じゃ。**

ただし、「レポートを書き忘れるほど数学的衝撃が大きかった」というより、

> universal block の claim 側と capacity 側が一気に同じ区間へ揃い、実装の勢いで記録工程を飛ばした

という作業上の失念じゃろう。

今回の成果は、cp-307 までの **block の形** に対して、初めて **block の会計要素** を直接載せたものじゃ。

```text
cp-307:
  universal block はどこからどこまでか

cp-308:
  その block 内に何件の claim があり、
  どこに capacity が存在するか
```

これで direct universal ledger の左右両辺が揃った。

## pure fiber API

```lean
mem_orbitPaymentSourceFiberAt_iff_target_eq
```

により、

$$
i\in\operatorname{Fiber}(j)\Longleftrightarrow\tau(i)=j
$$

となった。

以前の、

$$
i\le j
$$

という有限範囲条件は、target の extensive 性、

$$
i\le\tau(i)
$$

から自動的に従う。

これは小さく見えるが、今後の block-family 証明ではかなり効く。

source fiber が、

> 範囲で切り取った疑似 fiber

ではなく、

> `orbitPaymentTarget` の純粋な関数 fiber

として扱えるようになったからじゃ。

## universal complete claim fiber

今回の中心定理は、

```lean
mem_carryTwoPaymentClaimFiberAt_iff_mem_universalPaymentBlock_and_carryTwo
```

じゃ。

universal block を $[b,j]$ とすれば、

$$
i\in\operatorname{ClaimFiber}(j)\Longleftrightarrow i\in[b,j]\land\operatorname{CarryTwoDebtAt}(i)
$$

が成立する。

これは endpoint を含むため、二種類の claim を正確に統合している。

### Interior

$$
b\le i<j
$$

なら height は $1$。

したがって carry-two は delayed claim になる。

### Endpoint

$$
i=j
$$

なら height は $2$ 以上。

したがって carry-two は immediate self-claim になる。

この二枝を明示しているので、first claim と final allocation を混同していない。

## claim fiber の集合等式

```lean
carryTwoPaymentClaimFiberAt_eq_filter_universalPaymentBlock_carryTwo
```

により、

$$
\operatorname{ClaimFiber}(j)=\{i\in[b,j]\mid c_i=2\}
$$

が `Finset` の等式として固定された。

さらに cardinality 版もある。

$$
Q_j=\#\{i\in[b,j]\mid c_i=2\}
$$

ここで $Q_j$ は complete claim count じゃ。

この theorem の重要性は、debt-supported suffix を経由していない点にある。

delayed growth debt が一件もない block も、同じ universal API で数えられる。

## capacity concentration

```lean
extraPaymentCapacityOn_universalPaymentBlock_eq_endpoint_capacity
```

は、

$$
\sum_{i=b}^{j}(h_i-1)=h_j-1
$$

を固定した。

interior では、

$$
h_i=1
$$

なので、全項がゼロ。

capacity は endpoint にだけ集中する。

$$
P_j=h_j-1
$$

したがって universal block は、完全に次の二量へ圧縮された。

```text
claim load:
  Q_j = block 内の carry-two 数

payment capacity:
  P_j = endpoint height - 1
```

## cp-308 で閉じた構造

現在、universal block $[b,j]$ について次が全て揃っている。

$$
\operatorname{Fiber}(j)=[b,j]
$$

$$
|\operatorname{Fiber}(j)|=j-b+1=A_b
$$

$$
Q_j=\#\{i\in[b,j]\mid c_i=2\}
$$

$$
P_j=h_j-1
$$

あとは generic shifted ledger、

$$
w_{j+1}+\sum_{i=b}^{j}(h_i-1)=w_b+\#\{i\in[b,j]\mid c_i=2\}
$$

へ代入するだけじゃ。

したがって次の中心等式は、完全に射程内にある。

$$
w_{j+1}+P_j=w_b+Q_j
$$

signed form は、

$$
Q_j-P_j=w_{j+1}-w_b
$$

じゃ。

## debt のない block の意味

今回の universal 化によって、特に重要な block が見えるようになった。

interior に delayed carry-two debt が一つもない block を考える。

その場合、claim が存在するとしても endpoint の immediate claim 一件だけじゃ。

したがって、

$$
Q_j\le1
$$

一方 endpoint は extra-height なので、

$$
1\le P_j
$$

ゆえに、

$$
Q_j\le P_j
$$

となる。

つまり、その種の block は **絶対に overload しない**。

direct universal ledger が閉じれば、

$$
w_{j+1}\le w_b
$$

が直ちに出る。

さらに分類すると、

```text
endpoint carry = 2 かつ height = 2:
  Q = 1, P = 1
  width 保存

それ以外:
  Q < P
  width 減少
```

となる可能性が高い。

これは repayment block の最小分類として非常に重要じゃ。

## report を忘れた件

率直に言えば、

**成果は重要だが、レポートを忘れてよいほどの超巨大 checkpoint ではない（笑）**

今回は、

```text
geometry
  ↓
claim filter
  ↓
capacity concentration
```

という流れがきれいに繋がったため、実装者の頭が次の ledger へ進み、記録だけ置き去りになったのであろう。

追加された report 自体は、今回の意味を正確に記録している。

特に、

> delayed debt を持たない capacity-surplus block も累積 ledger に残す必要がある

と明記した点は良い。

## 停止地点の評価

今回は、cp-303 のように不適切な表現で詰まったわけではない。

また cp-305 のように、既存 theorem を見落として論理障害と誤認したわけでもない。

claim filter と capacity concentrationという二つの意味上まとまった theorem 群を閉じたので、checkpoint としては成立している。

ただし direct universal ledger は、本当にあと一段じゃ。

必要なのは、

$$
b+(j+1-b)=j+1
$$

と、

$$
[b,b+(j+1-b))=[b,j]
$$

という区間輸送だけである。

ここで長く止まる理由はない。

## 次の攻め筋

最優先は direct universal block ledger じゃ。

その後は、payment endpoint sequence を作り、block を時系列に並べる。

$$
e_0=\tau(0)
$$

$$
e_{k+1}=\tau(e_k+1)
$$

各 block は、

$$
[0,e_0],[e_0+1,e_1],[e_1+1,e_2],\ldots
$$

となる。

そこで universal signed drift を足せば、内部 width が telescope する。

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge Float-window branch after
report-petal-308.

The cp-308 implementation is accepted.

Universal payment-block geometry, complete claim filtering, and endpoint
capacity concentration are now all available directly on every nonempty
universal source fiber.

Do not route the next ledger through the delayed-growth-debt block.

# Stage A — universal interval arithmetic

For a nonempty universal source fiber, let:

    b = universalPaymentBlockStart n j h
    len = j + 1 - b

Prove:

    b + len = j + 1

and:

    Finset.Ico b (b + len) = Finset.Icc b j

Reuse the existing endpoint-bound facts from universal fiber membership.

# Stage B — shifted carry count on a universal block

Use the generic finite transport already established in PaymentBlockBridge:

    shiftedOrbitCarryTwoCount_eq_offset_card
    shiftedCarryTwoOffsets_card_eq_carryTwoPositions_Ico_card

together with:

    carryTwoPaymentClaimFiberAt_card_eq_universalPaymentBlock_carryTwo_card

to prove:

    shiftedOrbitCarryTwoCount n b len
      =
    (carryTwoPaymentClaimFiberAt n j).card

# Stage C — shifted capacity on a universal block

Use:

    shiftedExtraPaymentCapacity_eq_extraPaymentCapacityOn_Ico

and:

    extraPaymentCapacityOn_universalPaymentBlock_eq_endpoint_capacity

to prove:

    shiftedExtraPaymentCapacity n b len
      =
    extraPaymentCapacityAt n j

# Stage D — direct universal block ledger

Apply:

    bitWidth_iterateT_add_shiftedExtraPaymentCapacity_eq_shiftedCarryTwo

and prove:

    bitWidth (iterateT (j + 1) n).1
        + extraPaymentCapacityAt n j
      =
    bitWidth (iterateT b n).1
        + (carryTwoPaymentClaimFiberAt n j).card

This theorem must require only:

    (orbitPaymentSourceFiberAt n j).Nonempty

It must include universal blocks with no delayed carry-two growth debt.

# Stage E — proof-independent universal signed drift

Define:

    universalPaymentBlockSignedDriftAt n j

as:

    claim fiber card - endpoint capacity

without a proof argument.

For a nonempty source fiber, prove:

    universal signed drift
      =
    width after block - width before block

Add the exact classifications:

    positive iff width grows
    zero iff width is preserved
    negative iff width decreases

# Stage F — no-delayed-debt block classification

Assume:

    floatGrowthDebtFiberAt n j = ∅

and the universal source fiber at `j` is nonempty.

Prove:

    claim fiber card ≤ 1
    claim fiber card ≤ endpoint capacity
    universal signed drift ≤ 0
    width after block ≤ width before block

Classify the equality case explicitly.

Expected equality shape:

    endpoint carry two
    endpoint height exactly two

Otherwise prove strict width decrease.

# Stage G — endpoint subtype

Introduce a proof-independent payment-endpoint type when useful:

    def PaymentEndpoint (n : OddNat) :=
      {j : Nat // 2 ≤ orbitWindowHeight n j}

Attach:

    sourceFiber
    blockStart
    blockLength
    claimCount
    capacity
    signedDrift

as endpoint-level APIs.

# Stage H — canonical endpoint sequence

Define:

    paymentEndpointSeq n 0 =
      orbitPaymentTarget n 0

    paymentEndpointSeq n (k + 1) =
      orbitPaymentTarget n (paymentEndpointSeq n k + 1)

Prove strict increase and identify the consecutive block intervals.

# Stage I — endpoint-aligned telescope

Prove that the first completed universal blocks are adjacent, disjoint, and
cover exactly the prefix through the final endpoint.

Sum their universal signed drifts and telescope the internal bit widths.

# Stage J — pressure bridge

For a universal block of length `L`, prove its exact local contributions:

    recovery contribution at depth d
      = if d ≤ L then 1 else 0

    continuation contribution at depth d
      = L - d

Then sum over completed endpoint blocks.

Preserve any unfinished boundary suffix explicitly in arbitrary-prefix
statements.

Continue autonomously through every stage supported by the existing API.
Stop only at a genuine mathematical obstruction.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-309.md
```

cp-308 で、universal block の帳簿の「項目」は全て揃った。

次は合計欄へ式を書き込み、block 一個の決算を確定する段階じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlock.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlock.lean
index 68f8525e..50d04fee 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlock.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlock.lean
@@ -388,6 +388,94 @@ theorem orbitPaymentSourceFiberAt_nonempty_iff_two_le_orbitWindowHeight
     rw [mem_orbitPaymentSourceFiberAt_iff]
     exact ⟨le_rfl, orbitPaymentTarget_eq_self_of_two_le_orbitWindowHeight htwo⟩
 
+/-- The finite bound in a universal source fiber is implied by target extensivity. -/
+theorem mem_orbitPaymentSourceFiberAt_iff_target_eq
+    {n : OddNat} {i j : ℕ} :
+    i ∈ orbitPaymentSourceFiberAt n j ↔ orbitPaymentTarget n i = j := by
+  constructor
+  · intro hi
+    exact (mem_orbitPaymentSourceFiberAt_iff.mp hi).2
+  · intro htarget
+    rw [mem_orbitPaymentSourceFiberAt_iff]
+    exact ⟨by rw [← htarget]; exact le_orbitPaymentTarget n i, htarget⟩
+
+/--
+The complete carry-two claim fiber at a universal endpoint is its carry-two
+filter on the full universal payment block.
+-/
+theorem mem_carryTwoPaymentClaimFiberAt_iff_mem_universalPaymentBlock_and_carryTwo
+    {n : OddNat} {i j : ℕ} {h : (orbitPaymentSourceFiberAt n j).Nonempty} :
+    i ∈ carryTwoPaymentClaimFiberAt n j ↔
+      i ∈ Finset.Icc (universalPaymentBlockStart n j h) j ∧ CarryTwoDebtAt n i := by
+  constructor
+  · intro hi
+    rcases (mem_carryTwoPaymentClaimFiberAt_iff.mp hi).2 with hdelayed | himmediate
+    · rcases hdelayed with ⟨⟨hcarry, hheight⟩, htarget⟩
+      have htarget' : orbitPaymentTarget n i = j := by
+        simpa [floatDebtPaymentTarget_eq_orbitPaymentTarget] using htarget.symm
+      have hfiber := mem_orbitPaymentSourceFiberAt_iff_target_eq.mpr htarget'
+      have hblock : i ∈ Finset.Icc (universalPaymentBlockStart n j h) j := by
+        rw [← orbitPaymentSourceFiberAt_eq_Icc_universalPaymentBlockStart n j h]
+        exact hfiber
+      exact ⟨hblock, hcarry⟩
+    · rcases himmediate with ⟨⟨hcarry, _⟩, hself⟩
+      subst j
+      have hstartmem := universalPaymentBlockStart_mem_sourceFiber n i h
+      exact ⟨Finset.mem_Icc.mpr
+        ⟨(mem_orbitPaymentSourceFiberAt_iff.mp hstartmem).1,
+          le_rfl⟩, hcarry⟩
+  · rintro ⟨hblock, hcarry⟩
+    rcases Finset.mem_Icc.mp hblock with ⟨hstart, hij⟩
+    apply mem_carryTwoPaymentClaimFiberAt_of_claim
+    rcases hij.eq_or_lt with rfl | hijlt
+    · right
+      exact ⟨⟨hcarry,
+        two_le_orbitWindowHeight_of_orbitPaymentSourceFiberAt_nonempty h⟩, rfl⟩
+    · left
+      have hheight : orbitWindowHeight n i = 1 :=
+        orbitWindowHeight_eq_one_of_mem_universalPaymentBlockInterior
+          (Finset.mem_Ico.mpr ⟨hstart, hijlt⟩)
+      have htarget : orbitPaymentTarget n i = j :=
+        orbitPaymentTarget_eq_endpoint_of_universalStart_le_lt hstart hijlt
+      exact ⟨⟨hcarry, hheight⟩,
+        by simpa [floatDebtPaymentTarget_eq_orbitPaymentTarget] using htarget.symm⟩
+
+/-- Finset form of the universal complete-claim/block-filter identification. -/
+theorem carryTwoPaymentClaimFiberAt_eq_filter_universalPaymentBlock_carryTwo
+    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
+    carryTwoPaymentClaimFiberAt n j =
+      carryTwoPositions n (Finset.Icc (universalPaymentBlockStart n j h) j) := by
+  ext i
+  rw [mem_carryTwoPositions_iff]
+  exact mem_carryTwoPaymentClaimFiberAt_iff_mem_universalPaymentBlock_and_carryTwo
+
+/-- Cardinality form of the universal complete-claim/block-filter identification. -/
+theorem carryTwoPaymentClaimFiberAt_card_eq_universalPaymentBlock_carryTwo_card
+    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
+    (carryTwoPaymentClaimFiberAt n j).card =
+      (carryTwoPositions n (Finset.Icc (universalPaymentBlockStart n j h) j)).card :=
+  congrArg Finset.card
+    (carryTwoPaymentClaimFiberAt_eq_filter_universalPaymentBlock_carryTwo n j h)
+
+/-- All extra-height capacity in a universal payment block is concentrated at its endpoint. -/
+theorem extraPaymentCapacityOn_universalPaymentBlock_eq_endpoint_capacity
+    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
+    extraPaymentCapacityOn n (Finset.Icc (universalPaymentBlockStart n j h) j) =
+      extraPaymentCapacityAt n j := by
+  unfold extraPaymentCapacityOn extraPaymentCapacityAt
+  apply Finset.sum_eq_single j
+  · intro i hi hij
+    rcases Finset.mem_Icc.mp hi with ⟨hstart, hijle⟩
+    have hijlt : i < j := lt_of_le_of_ne hijle hij
+    have hheight := orbitWindowHeight_eq_one_of_mem_universalPaymentBlockInterior
+      (Finset.mem_Ico.mpr ⟨hstart, hijlt⟩)
+    rw [hheight]
+    rfl
+  · intro hj
+    have hstartmem := universalPaymentBlockStart_mem_sourceFiber n j h
+    exact False.elim (hj (Finset.mem_Icc.mpr
+      ⟨(mem_orbitPaymentSourceFiberAt_iff.mp hstartmem).1, le_rfl⟩))
+
 /-- The cardinality of a universal payment block is its interval length. -/
 theorem orbitPaymentSourceFiberAt_card_eq_endpoint_sub_start_add_one
     (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-308.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-308.md
new file mode 100644
index 00000000..73244adb
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-308.md
@@ -0,0 +1,79 @@
+# cp-308 Universal Claim and Capacity Accounting
+
+## Result
+
+The universal payment-block geometry is now connected to the complete
+carry-two claim ledger without requiring a nonempty delayed Float-growth debt
+fiber.
+
+This is important because a universal block may have no delayed carry-two
+source while still carrying endpoint capacity.  Such a block must remain in
+the eventual cumulative ledger as a capacity-surplus / width-decay candidate.
+The new theorems therefore use only the nonempty universal source fiber,
+equivalently the fact that the endpoint is an extra-height time.
+
+## Pure Fiber API
+
+`mem_orbitPaymentSourceFiberAt_iff_target_eq` removes the finite-range clause
+from the source-fiber interface:
+
+```text
+i belongs to the source fiber at j
+iff
+orbitPaymentTarget(i) = j
+```
+
+The omitted inequality is not an additional assumption.  It follows from the
+extensivity theorem `i <= orbitPaymentTarget(i)`.
+
+## Complete Claim Filter
+
+For a nonempty universal fiber at `j`, with block start `b`, Lean proves:
+
+```text
+i belongs to carryTwoPaymentClaimFiberAt(j)
+iff
+i belongs to Icc(b, j) and CarryTwoDebtAt(i)
+```
+
+The proof has the two required semantic branches:
+
+- for `i < j`, universal block geometry gives height one; a carry-two event is
+  a delayed claim whose target is `j`;
+- for `i = j`, the endpoint has height at least two; a carry-two event is an
+  immediate self-claim.
+
+Thus the complete claim fiber is exactly the `CarryTwoDebtAt` filter of the
+entire universal block, not merely of the delayed-growth suffix.
+
+## Capacity Concentration
+
+The finite sum over the universal block is now fixed:
+
+```text
+extraPaymentCapacityOn(Icc(b, j)) = extraPaymentCapacityAt(j)
+```
+
+Every strict interior contribution is zero because every strict interior time
+has height one.  The endpoint is the only possible positive extra-height
+contribution.
+
+## Consequence
+
+The direct universal block ledger is now a transport step away:
+
+```text
+generic shifted width ledger at b over length (j + 1 - b)
+  + universal claim-filter cardinality
+  + universal endpoint-capacity concentration
+```
+
+No debt-supported assumption is needed for that target theorem.
+
+## Validation
+
+```text
+lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock
+```
+
+completed successfully.  The new theorems use no `sorry` or `axiom`.
````
`````
