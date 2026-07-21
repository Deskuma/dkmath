# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.FloatWindow.PaymentBlockBridge

gch: f06a3f650d70b592eb0ee92433688f3a7ffdc219

## Report

実装を完了しました。

`PaymentBlockBridge.lean` に局所 offset 表現から canonical payment block への有限輸送を追加し、次を no-sorry で証明しています。

- shifted carry-two count = complete claim fiber の card
- shifted extra capacity = endpoint capacity
- exact block ledger
- overload / balance / surplus と bit width の増加 / 保存 / 減少の同値

局所 block に限定した主張であり、全軌道の被覆や収束は導いていません。

レポートを追加しました: [report-petal-304.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-304.md)

検証済み:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.PaymentBlockBridge
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
lake build DkMath
git diff --check
```

すべて成功しています。今回変更した `PaymentBlockBridge.lean` に `sorry` / `axiom` はありません。

## Review

## 結論

**採用。payment-block 会計の局所幹線は完成した。**

cp-304 は、前回問題になった `Finset.Ico` の successor 正規化を正面突破せず、

```text
再帰 count
→ local offset
→ global position
→ canonical block
```

という正しい座標変換へ切り替えた。

その結果、次が全て no-sorry で閉じた。

- shifted carry-two count と complete claim fiber card の一致
- shifted extra-height sum と endpoint capacity の一致
- exact payment-block ledger
- overload / balance / capacity surplus と width 増減の完全同値

添付 report では対象モジュールからトップレベル `DkMath` までの build と `git diff --check` が全て成功したと報告されている。

わっちの側でも、

- 指定 snapshot の SHA-256 一致
- cp-304 patch が snapshot へ clean apply 可能
- 変更後 `PaymentBlockBridge.lean` 内に `sorry` / `axiom` がないこと

を直接確認した。

この環境には `lake` / `lean` 実行系がないため、build 自体の独立再実行だけは行えていない。

## 1. offset route への変更

今回の最重要修正は、

```lean
shiftedCarryTwoOffsets
```

じゃ。

局所 offset を、

```text
t ∈ Finset.range len
```

とし、global time を、

```text
a + t
```

としている。

これにより再帰定義、

```lean
orbitWindowUpperCarryCountEqTwo
```

と `Finset.range` の再帰構造が一致した。

```lean
shiftedOrbitCarryTwoCount_eq_offset_card
```

は、

$$
\operatorname{ShiftedCarryCount}(n,a,\ell)=\#\{t<\ell\mid\operatorname{CarryTwoDebtAt}(n,a+t)\}
$$

を証明する。

successor step では `Finset.range_add_one` を使用し、最後の offset `len` だけを追加している。

これは Lean の正規形に合った証明じゃ。

## 2. extra-height sum の offset 表現

```lean
shiftedExtraPaymentCapacity_eq_sum_range
```

は、

$$
\operatorname{ShiftedExtraCapacity}(n,a,\ell)=\sum_{t<\ell}\bigl(h_{a+t}-1\bigr)
$$

を証明した。

ここでも、

```lean
Finset.sum_range_succ
```

と、

```lean
orbitWindowHeight_shift_eq
```

を使っており、再帰定義と有限和の構造が完全に一致している。

前回のように、最初から global `Ico` の sum へ合わせなかったのが正解じゃ。

## 3. local offset から global block への輸送

```lean
shiftedCarryTwoPositions
```

は、写像、

$$
t\longmapsto a+t
$$

によって local offsets を global positions へ送る。

`Finset.map` を使い、単射性を `Nat.add_left_cancel` で明示している。

さらに、

```lean
shiftedCarryTwoPositions_eq_carryTwoPositions_Ico
```

により、

$$
\{a+t\mid t<\ell,\ c_{a+t}=2\}=\{i\in[a,a+\ell)\mid c_i=2\}
$$

を証明した。

逆写像は、

$$
i\longmapsto i-a
$$

じゃ。

この実装は非常に良い。

interval の successor 正規化ではなく、有限集合間の全単射として transport を実装している。

## 4. complete claim fiber との一致

canonical block では、

```lean
shiftedOrbitCarryTwoCount_eq_carryTwoPaymentClaimFiber_card
```

が成立した。

block start を $a$、endpoint を $j$ とすれば、

$$
\operatorname{ShiftedCarryCount}(n,a,j+1-a)=\#\operatorname{CarryTwoPaymentClaimFiberAt}(n,j)
$$

じゃ。

既存の、

```lean
carryTwoPaymentClaimFiberAt_card_eq_floatPaymentBlockWithEndpoint_carryTwo_card
```

を再利用し、

```text
local offsets
→ global Ico
→ canonical Icc block
→ complete claim fiber
```

と段階的に接続している。

証明の依存構造もきれいじゃ。

## 5. capacity の endpoint 集中

```lean
extraPaymentCapacityOn_floatPaymentBlockWithEndpoint_eq_endpoint_extra
```

は、

$$
\sum_{i\in[a,j]}(h_i-1)=h_j-1
$$

を証明した。

理由は既に確定している通り、

$$
a\le i<j\Longrightarrow h_i=1
$$

だからじゃ。

したがって interior contribution は全てゼロ。

endpoint $j$ だけが extra capacity を持つ。

`Finset.sum_eq_single j` を使った実装も自然である。

さらに、

```lean
shiftedExtraPaymentCapacity_eq_extraPaymentCapacityAt
```

によって、

$$
\operatorname{ShiftedExtraCapacity}(n,a,j+1-a)=\operatorname{extraPaymentCapacityAt}(n,j)
$$

まで閉じた。

## 6. exact payment-block ledger

今回の中心定理は、

```lean
bitWidth_iterateT_paymentBlock_eq_claimFiber_card
```

じゃ。

数学形は、

$$
w_{j+1}+P_j=w_a+Q_j
$$

ここで、

$$
P_j=h_j-1,\qquad Q_j=\#\operatorname{CarryTwoPaymentClaimFiberAt}(n,j)
$$

である。

これは一つの canonical first-payment block 全体を、

```text
block 開始時の width
claim 数
endpoint capacity
block 通過後の width
```

という四値だけへ圧縮した完全会計じゃ。

途中の個々の Collatz 値を追う必要がなくなった。

## 7. overload / balance / surplus の完全分類

中心等式から、三分岐が Lean 上で完全に閉じた。

### Overload

$$
P_j<Q_j\Longleftrightarrow w_a<w_{j+1}
$$

### Balance

$$
P_j=Q_j\Longleftrightarrow w_a=w_{j+1}
$$

### Capacity surplus

$$
Q_j<P_j\Longleftrightarrow w_{j+1}<w_a
$$

対応する theorem は、

```lean
carryTwoPaymentOverloadAt_iff_bitWidth_paymentBlock_lt

carryTwoPaymentClaimFiber_card_eq_capacity_iff_bitWidth_paymentBlock_eq

carryTwoPaymentClaimFiber_card_lt_capacity_iff_bitWidth_paymentBlock_gt
```

じゃ。

これで payment block は、

```text
overload
balanced
surplus
```

の三状態へ完全分類できる。

## 8. 数学的意味

今回の成果を一言で言えば、

> **payment overload は、block width growth と完全に同じ現象である。**

じゃ。

これは重要な確定だが、同時に注意点でもある。

`CarryTwoPaymentOverloadAt` が width growth を外部から阻止する新しい条件になったわけではない。

現段階では、

```text
overload
```

と、

```text
block width growth
```

が同じ事実の二つの表示になった。

したがって次に必要なのは、

```text
overload block が発生しない
```

と単独で示すことではなく、

```text
overload block が後続 surplus block により回収される
```

または、

```text
overload block を長期に維持する block 配列は不可能
```

と示すことじゃ。

## 9. 現在の block が表す範囲

主定理には、

```lean
h : (floatGrowthDebtFiberAt n j).Nonempty
```

が必要である。

したがって対象は、

> 少なくとも一つの delayed growth debt を持つ endpoint

じゃ。

次はまだ含まれていない。

- delayed carry-two debt を一つも持たない payment endpoint
- carry-one / height-one のみで構成された staircase
- immediate payment だけの単点 block
- 全軌道時刻を被覆する block partition

これは report の境界説明とも一致している。

## 10. debt-supported block と maximal staircase

現在の start は、

```lean
floatPaymentBlockStart
```

であり、同じ target を持つ最初の **carry-two debt** じゃ。

同じ target を持つ height-one staircase の真の最左端とは限らない。

左側に、

```text
carry one
height one
same payment target
```

の zero-drift prefix が存在し得る。

ただし、その prefix では各 step が、

$$
c_i=1,\qquad h_i=1
$$

なので width は変化しない。

したがって今回の block ledger は正しい。

しかし pressure の depth profile を完全に数える際には、その左側 prefix を含む maximal staircase が必要になる。

## 11. 軽微な実装改善点

### shifted ledger の再利用

```lean
bitWidth_iterateT_paymentBlock_eq_claimFiber_card
```

の内部では、既に存在する、

```lean
bitWidth_iterateT_add_shiftedExtraPaymentCapacity_eq_shiftedCarryTwo
```

を直接使わず、同内容の `hledger` を局所的に再構築している。

理由は宣言順で、新しい specialized theorem 群が generic shifted ledger より前に挿入されたためじゃ。

論理的問題はない。

ただし将来リファクタリングするなら、generic shifted ledger を transport theorem 群より前へ移し、specialized block ledger から直接呼ぶ方が構造は明瞭になる。

これは採用を妨げる問題ではない。

## 12. 次に必要な signed block drift

三分岐は完成したが、大域的に block を足し合わせるには整数値 drift が便利じゃ。

例えば、

```lean
def paymentBlockDriftInt
    (n : OddNat) (j : ℕ)
    (h : (floatGrowthDebtFiberAt n j).Nonempty) : ℤ :=
  (carryTwoPaymentClaimFiberAt n j).card -
    extraPaymentCapacityAt n j
```

型変換を明示すれば、中心定理から、

$$
\operatorname{paymentBlockDriftInt}(n,j)=w_{j+1}-w_a
$$

を得られる。

これにより block 列の総和が telescope する。

Nat の三分岐だけより、後続の cumulative ledger に適している。

## 13. 本当の次の本丸

次は universal payment target じゃ。

現在の target 式、

$$
\tau(i)=i+A_i-1
$$

は debt source だけでなく、全 orbit time に意味を持つ。

ここで、

$$
A_i=\operatorname{ResidualAllOnesDepth}(\operatorname{oddOrbitLabel}(n,i))
$$

じゃ。

既存 residue API から、次が狙える。

$$
h_i=1\Longleftrightarrow2\le A_i
$$

$$
2\le h_i\Longleftrightarrow A_i=1
$$

したがって、

```text
height one:
  target は未来

height at least two:
  target は現在時刻
```

となる。

全時刻を target fiber に分類できれば、軌道は maximal payment blocks へ分割される。

その block family 上で今回の ledger を足し合わせれば、

```text
局所 block ledger
→ finite block-family ledger
→ global prefix width ledger
```

へ進める。

## 判定

### 実装

**採用。**

### 証明強度

**適正。**

局所 block より外へ飛躍していない。

### cp-304 の到達点

**payment-block accounting branch の局所核は完成。**

### 残る Gap

```text
signed block drift
universal payment target
maximal payment block
finite block partition
block-family telescope
pressure block-length profile
```

じゃ。

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge Float-window branch after
report-petal-304.

The cp-304 payment-block ledger is accepted.

The local result is now exact:

    width after block + endpoint capacity
      =
    width before block + complete claim count

and overload / balance / capacity surplus are exactly width growth /
preservation / decay.

The next objective is to lift this local accounting into a canonical family of
payment blocks without confusing first claims with final debt allocation.

The checkpoint number is not a stopping boundary. Continue autonomously while
the statements remain justified.

# Primary files

Continue in:

    DkMath/Collatz/PetalBridge/FloatWindow/PaymentBlockBridge.lean

Create a new module such as:

    DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlock.lean

when the universal-target and block-family API becomes large enough.

# Stage A — minor ledger refactor

Move or expose the generic theorem:

    bitWidth_iterateT_add_shiftedExtraPaymentCapacity_eq_shiftedCarryTwo

before the specialized block-ledger declarations when this permits:

    bitWidth_iterateT_paymentBlock_eq_claimFiber_card

to reuse it directly.

Do not change theorem statements merely for cosmetic reasons.

# Stage B — signed block drift

Define an integer-valued block balance:

    claim card - endpoint capacity

and prove that it equals:

    width after block - width before block

Provide sign characterizations compatible with the existing Nat trichotomy.

The signed API must preserve capacity surplus as a negative value rather than
truncate it.

# Stage C — height / exact-depth equivalences

Prove the pointwise equivalences:

    orbitWindowHeight n i = 1
      ↔ 2 ≤ orbitExactDepth n i

    2 ≤ orbitWindowHeight n i
      ↔ orbitExactDepth n i = 1

Reuse:

    orbitWindowHeight_eq_one_iff_mod_four_eq_three
    orbitWindowHeight_two_le_iff_mod_four_eq_one
    le_residualAllOnesDepth_iff_mod_eq_allOnes

Do not duplicate modular arithmetic unnecessarily.

# Stage D — universal payment target

Introduce a semantic target defined for every orbit time:

    orbitPaymentTarget n i :=
      i + orbitExactDepth n i - 1

Keep:

    floatDebtPaymentTarget

as an alias or compatibility theorem.

Prove:

    height = 1 -> i < orbitPaymentTarget n i

    height >= 2 -> orbitPaymentTarget n i = i

    every time targets an actual height >= 2 payment slot

For height-one sources, reuse the generic delayed-horizon theorem.
For height-at-least-two sources, the target is immediate.

# Stage E — universal source fibers

Define:

    orbitPaymentSourceFiberAt n j :=
      {i in Finset.range (j + 1) |
        orbitPaymentTarget n i = j}

Prove the membership API and that a nonempty fiber has a minimum.

Show that every source in one fiber lies on the same descending exact-depth
staircase.

# Stage F — maximal payment block

For an endpoint `j` with nonempty universal source fiber, define:

    universalPaymentBlockStart n j

as the minimum source in that fiber.

Prove that the fiber is exactly the contiguous interval:

    Finset.Icc start j

Equivalently prove:

    start <= i <= j
      ↔ orbitPaymentTarget n i = j

Expose:

    for start <= i < j:
      orbitWindowHeight n i = 1

    at j:
      2 <= orbitWindowHeight n j

This is the maximal payment staircase.

# Stage G — relation to the debt-supported block

For an endpoint with a nonempty delayed-growth debt fiber, let:

    b = universalPaymentBlockStart
    a = floatPaymentBlockStart

Prove:

    b <= a

and for every `i` in `[b, a)`:

    height(i) = 1
    carry(i) = 1

Therefore prove:

    bitWidth (iterateT b n).1 =
      bitWidth (iterateT a n).1

Transport the cp-304 exact block ledger from the debt-supported suffix to the
full maximal payment block.

# Stage H — block-family structure

Investigate finite families of successive universal payment blocks.

Prove disjointness of distinct target fibers.

Prove the appropriate finite-prefix coverage statement, including any final
unfinished height-one suffix as an explicit boundary remainder.

Do not claim complete coverage without representing that remainder.

# Stage I — cumulative block ledger

Sum the signed block drifts over a finite block family.

Prove that internal widths telescope and recover the existing orbit-prefix
width ledger, plus any explicit boundary remainder.

This is the first block-level global accounting theorem.

# Stage J — pressure preparation

Relate maximal block lengths to exact-depth fibers.

A maximal block of pre-payment length `L` has depth profile:

    L + 1, L, ..., 3, 2

Use this to connect block-length histograms to:

    orbitDepthRecoveryFiberCount
    orbitDepthContinuationFiberCount
    sourcePressureMarginInt_eq_continuationFiber_sub_recoveryFiber

Do not infer ambient positive pressure by deleting unrelated blocks.

# Autonomous continuation

Continue while:

    theorem statements follow from existing Lean facts
    local and universal block starts remain distinct
    signed debt and capacity are not truncated
    unfinished prefix/suffix boundaries remain explicit
    no sorry or axiom is introduced
    builds remain green

Stop only at a genuine logical obstruction or an unresolved dependency/API
placement conflict.

# Validation

Run:

    lake build DkMath.Collatz.PetalBridge.FloatWindow.PaymentBlockBridge
    lake build DkMath.Collatz.PetalBridge.FloatWindow
    lake build DkMath.Collatz.PetalBridge
    lake build DkMath
    git diff --check

Record the autonomous continuation in:

    docs/dev/das-p2l-260607/review/report-petal-305.md
```

cp-304 で、一個の block 内の会計は完全に閉じた。

次は block を点列として並べ、局所等式を telescope させる段階じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/PaymentBlockBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/PaymentBlockBridge.lean
index 964ca9c3..9a137152 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/PaymentBlockBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/PaymentBlockBridge.lean
@@ -253,7 +253,7 @@ theorem orbitWindowHeight_shift_eq

 /-- Total extra-height capacity over an explicit finite source set. -/
 noncomputable def extraPaymentCapacityOn (n : OddNat) (S : Finset ℕ) : ℕ :=
-  ∑ i ∈ S, orbitWindowHeight n i - 1
+  S.sum fun i => orbitWindowHeight n i - 1

 /-- Endpoint arithmetic for a nonempty debt-supported payment block. -/
 theorem floatPaymentBlockStart_add_endpointLength_eq_endpoint_succ
@@ -283,6 +283,253 @@ noncomputable def shiftedExtraPaymentCapacity
     (n : OddNat) (a len : ℕ) : ℕ :=
   sumExtraHeight (iterateT a n) len

+/-- Local offsets of carry-two sources in the shifted segment `[a, a + len)`. -/
+noncomputable def shiftedCarryTwoOffsets
+    (n : OddNat) (a len : ℕ) : Finset ℕ := by
+  classical
+  exact (Finset.range len).filter fun t => CarryTwoDebtAt n (a + t)
+
+/-- The recursive shifted carry-two count is the card of its local offset set. -/
+theorem shiftedOrbitCarryTwoCount_eq_offset_card
+    (n : OddNat) (a len : ℕ) :
+    shiftedOrbitCarryTwoCount n a len = (shiftedCarryTwoOffsets n a len).card := by
+  classical
+  induction len with
+  | zero =>
+      simp [shiftedOrbitCarryTwoCount, shiftedCarryTwoOffsets,
+        orbitWindowUpperCarryCountEqTwo]
+  | succ len ih =>
+      change orbitWindowUpperCarryCountEqTwo (iterateT a n) (len + 1) =
+        ((Finset.range (len + 1)).filter fun t => CarryTwoDebtAt n (a + t)).card
+      rw [orbitWindowUpperCarryCountEqTwo]
+      change shiftedOrbitCarryTwoCount n a len +
+          (if stateUpperCarry (iterateT len (iterateT a n)).1 = 2 then 1 else 0) = _
+      rw [ih, Finset.range_add_one]
+      change ((Finset.range len).filter fun t => CarryTwoDebtAt n (a + t)).card +
+          (if stateUpperCarry (iterateT len (iterateT a n)).1 = 2 then 1 else 0) =
+        ((insert len (Finset.range len)).filter fun t => CarryTwoDebtAt n (a + t)).card
+      by_cases hcarry : CarryTwoDebtAt n (a + len)
+      · have hstate : stateUpperCarry (iterateT len (iterateT a n)).1 = 2 := by
+          simpa [CarryTwoDebtAt, ← iterateT_add_eq_iterateT_from_shift] using hcarry
+        rw [Finset.filter_insert]
+        simp [hcarry, hstate]
+      · have hstate : stateUpperCarry (iterateT len (iterateT a n)).1 ≠ 2 := by
+          simpa [CarryTwoDebtAt, ← iterateT_add_eq_iterateT_from_shift] using hcarry
+        rw [Finset.filter_insert]
+        simp [hcarry, hstate]
+
+/-- Shifted extra-height capacity is the finite sum over local offsets. -/
+theorem shiftedExtraPaymentCapacity_eq_sum_range
+    (n : OddNat) (a len : ℕ) :
+    shiftedExtraPaymentCapacity n a len =
+      (Finset.range len).sum fun t => orbitWindowHeight n (a + t) - 1 := by
+  induction len with
+  | zero => simp [shiftedExtraPaymentCapacity, sumExtraHeight]
+  | succ len ih =>
+      change sumExtraHeight (iterateT a n) (len + 1) =
+        (Finset.range (len + 1)).sum fun t => orbitWindowHeight n (a + t) - 1
+      rw [sumExtraHeight]
+      change shiftedExtraPaymentCapacity n a len +
+          (s (iterateT len (iterateT a n)) - 1) = _
+      rw [ih, Finset.sum_range_succ]
+      have hheight : s (iterateT len (iterateT a n)) =
+          orbitWindowHeight n (a + len) := by
+        calc
+          s (iterateT len (iterateT a n)) = s (iterateT (a + len) n) := by
+            rw [iterateT_add_eq_iterateT_from_shift]
+          _ = orbitWindowHeight n (a + len) :=
+            (orbitWindowHeight_eq_s_iterateT n (a + len)).symm
+      rw [hheight]
+
+/-- Membership in the local carry-two offset set. -/
+theorem mem_shiftedCarryTwoOffsets_iff
+    {n : OddNat} {a len t : ℕ} :
+    t ∈ shiftedCarryTwoOffsets n a len ↔ t < len ∧ CarryTwoDebtAt n (a + t) := by
+  classical
+  simp [shiftedCarryTwoOffsets]
+
+/--
+The global positions represented by local carry-two offsets.
+
+The map is deliberately stated through `Finset.map`: its injectivity proof
+makes the finite transport and its cardinal preservation explicit.
+-/
+noncomputable def shiftedCarryTwoPositions
+    (n : OddNat) (a len : ℕ) : Finset ℕ := by
+  classical
+  exact (shiftedCarryTwoOffsets n a len).map
+    ⟨fun t => a + t, by
+      intro x y hxy
+      exact Nat.add_left_cancel hxy⟩
+
+/-- Local carry-two offsets are exactly the carry-two positions of the shifted interval. -/
+theorem shiftedCarryTwoPositions_eq_carryTwoPositions_Ico
+    (n : OddNat) (a len : ℕ) :
+    shiftedCarryTwoPositions n a len =
+      carryTwoPositions n (Finset.Ico a (a + len)) := by
+  classical
+  ext i
+  constructor
+  · intro hi
+    rcases Finset.mem_map.mp hi with ⟨t, ht, hti⟩
+    rw [mem_carryTwoPositions_iff]
+    rcases mem_shiftedCarryTwoOffsets_iff.mp ht with ⟨htlen, htcarry⟩
+    rw [← hti]
+    change a + t ∈ Finset.Ico a (a + len) ∧ CarryTwoDebtAt n (a + t)
+    exact ⟨Finset.mem_Ico.mpr ⟨Nat.le_add_right _ _, by omega⟩, htcarry⟩
+  · intro hi
+    rw [mem_carryTwoPositions_iff] at hi
+    rcases hi with ⟨hiIco, hcarry⟩
+    rcases Finset.mem_Ico.mp hiIco with ⟨hai, hiend⟩
+    apply Finset.mem_map.mpr
+    refine ⟨i - a, ?_, ?_⟩
+    · apply mem_shiftedCarryTwoOffsets_iff.mpr
+      constructor
+      · omega
+      · simpa [Nat.add_sub_of_le hai] using hcarry
+    · exact Nat.add_sub_of_le hai
+
+/-- Cardinality is preserved when local carry-two offsets are shifted globally. -/
+theorem shiftedCarryTwoOffsets_card_eq_carryTwoPositions_Ico_card
+    (n : OddNat) (a len : ℕ) :
+    (shiftedCarryTwoOffsets n a len).card =
+      (carryTwoPositions n (Finset.Ico a (a + len))).card := by
+  calc
+    (shiftedCarryTwoOffsets n a len).card = (shiftedCarryTwoPositions n a len).card := by
+      simp [shiftedCarryTwoPositions]
+    _ = (carryTwoPositions n (Finset.Ico a (a + len))).card :=
+      congrArg Finset.card (shiftedCarryTwoPositions_eq_carryTwoPositions_Ico n a len)
+
+/--
+On a canonical block, the shifted carry-two count is exactly the complete
+first-payment claim-fiber cardinality at its endpoint.
+-/
+theorem shiftedOrbitCarryTwoCount_eq_carryTwoPaymentClaimFiber_card
+    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
+    shiftedOrbitCarryTwoCount n (floatPaymentBlockStart n j h)
+      (j + 1 - floatPaymentBlockStart n j h) =
+      (carryTwoPaymentClaimFiberAt n j).card := by
+  let a := floatPaymentBlockStart n j h
+  let len := j + 1 - a
+  calc
+    shiftedOrbitCarryTwoCount n a len = (shiftedCarryTwoOffsets n a len).card :=
+      shiftedOrbitCarryTwoCount_eq_offset_card n a len
+    _ = (carryTwoPositions n (Finset.Ico a (a + len))).card :=
+      shiftedCarryTwoOffsets_card_eq_carryTwoPositions_Ico_card n a len
+    _ = (carryTwoPositions n (floatPaymentBlockWithEndpoint n j h)).card := by
+      rw [floatPaymentBlock_Ico_eq_withEndpoint]
+    _ = (carryTwoPaymentClaimFiberAt n j).card :=
+      (carryTwoPaymentClaimFiberAt_card_eq_floatPaymentBlockWithEndpoint_carryTwo_card n j h).symm
+
+/--
+All extra-height capacity in a canonical block is concentrated at its endpoint.
+
+Every earlier point is in the height-one interior, hence contributes zero to
+`orbitWindowHeight - 1`.
+-/
+theorem extraPaymentCapacityOn_floatPaymentBlockWithEndpoint_eq_endpoint_extra
+    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
+    extraPaymentCapacityOn n (floatPaymentBlockWithEndpoint n j h) =
+      orbitWindowHeight n j - 1 := by
+  classical
+  unfold extraPaymentCapacityOn
+  apply Finset.sum_eq_single j
+  · intro i hi hij
+    have hii := Finset.mem_Icc.mp hi
+    have hijlt : i < j := lt_of_le_of_ne hii.2 hij
+    have hinterior : i ∈ floatPaymentBlockInterior n j h :=
+      Finset.mem_Ico.mpr ⟨hii.1, hijlt⟩
+    rw [orbitWindowHeight_eq_one_of_mem_floatPaymentBlockInterior hinterior]
+    rfl
+  · intro hj
+    exact False.elim (hj (Finset.mem_Icc.mpr
+      ⟨(floatPaymentBlockStart_lt_endpoint n j h).le, le_rfl⟩))
+
+/-- The shifted local extra-height sum is the capacity of its global half-open interval. -/
+theorem shiftedExtraPaymentCapacity_eq_extraPaymentCapacityOn_Ico
+    (n : OddNat) (a len : ℕ) :
+    shiftedExtraPaymentCapacity n a len =
+      extraPaymentCapacityOn n (Finset.Ico a (a + len)) := by
+  unfold extraPaymentCapacityOn
+  rw [shiftedExtraPaymentCapacity_eq_sum_range]
+  symm
+  rw [Finset.sum_Ico_eq_sum_range]
+  simp
+
+/-- The shifted extra-height capacity of a canonical block is its endpoint capacity. -/
+theorem shiftedExtraPaymentCapacity_eq_extraPaymentCapacityAt
+    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
+    shiftedExtraPaymentCapacity n (floatPaymentBlockStart n j h)
+      (j + 1 - floatPaymentBlockStart n j h) = extraPaymentCapacityAt n j := by
+  calc
+    shiftedExtraPaymentCapacity n (floatPaymentBlockStart n j h)
+        (j + 1 - floatPaymentBlockStart n j h) =
+        extraPaymentCapacityOn n (Finset.Ico (floatPaymentBlockStart n j h)
+          (floatPaymentBlockStart n j h + (j + 1 - floatPaymentBlockStart n j h))) :=
+      shiftedExtraPaymentCapacity_eq_extraPaymentCapacityOn_Ico n
+        (floatPaymentBlockStart n j h) (j + 1 - floatPaymentBlockStart n j h)
+    _ = extraPaymentCapacityOn n (floatPaymentBlockWithEndpoint n j h) := by
+      rw [floatPaymentBlock_Ico_eq_withEndpoint]
+    _ = orbitWindowHeight n j - 1 :=
+      extraPaymentCapacityOn_floatPaymentBlockWithEndpoint_eq_endpoint_extra n j h
+    _ = extraPaymentCapacityAt n j := rfl
+
+/--
+Exact width ledger on a canonical first-payment block.
+
+The right side counts complete carry-two claims; the left side records the
+single endpoint's available extra-height capacity.
+-/
+theorem bitWidth_iterateT_paymentBlock_eq_claimFiber_card
+    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
+    bitWidth (iterateT (j + 1) n).1 + extraPaymentCapacityAt n j =
+      bitWidth (iterateT (floatPaymentBlockStart n j h) n).1 +
+        (carryTwoPaymentClaimFiberAt n j).card := by
+  have hledger :
+      bitWidth (iterateT
+        (floatPaymentBlockStart n j h + (j + 1 - floatPaymentBlockStart n j h)) n).1 +
+          shiftedExtraPaymentCapacity n (floatPaymentBlockStart n j h)
+            (j + 1 - floatPaymentBlockStart n j h) =
+        bitWidth (iterateT (floatPaymentBlockStart n j h) n).1 +
+          shiftedOrbitCarryTwoCount n (floatPaymentBlockStart n j h)
+            (j + 1 - floatPaymentBlockStart n j h) := by
+    unfold shiftedExtraPaymentCapacity shiftedOrbitCarryTwoCount
+    rw [iterateT_add_eq_iterateT_from_shift]
+    exact bitWidth_iterateT_add_sumExtraHeight_eq_initial_add_countCarryTwo
+      (iterateT (floatPaymentBlockStart n j h) n)
+      (j + 1 - floatPaymentBlockStart n j h)
+  rw [shiftedExtraPaymentCapacity_eq_extraPaymentCapacityAt,
+    shiftedOrbitCarryTwoCount_eq_carryTwoPaymentClaimFiber_card] at hledger
+  simpa [floatPaymentBlockStart_add_endpointLength_eq_endpoint_succ] using hledger
+
+/-- A canonical block overload is exactly a strict width increase across the block. -/
+theorem carryTwoPaymentOverloadAt_iff_bitWidth_paymentBlock_lt
+    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
+    CarryTwoPaymentOverloadAt n j ↔
+      bitWidth (iterateT (floatPaymentBlockStart n j h) n).1 <
+        bitWidth (iterateT (j + 1) n).1 := by
+  unfold CarryTwoPaymentOverloadAt
+  have hledger := bitWidth_iterateT_paymentBlock_eq_claimFiber_card n j h
+  omega
+
+/-- Claim capacity is balanced exactly when the canonical block preserves width. -/
+theorem carryTwoPaymentClaimFiber_card_eq_capacity_iff_bitWidth_paymentBlock_eq
+    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
+    (carryTwoPaymentClaimFiberAt n j).card = extraPaymentCapacityAt n j ↔
+      bitWidth (iterateT (floatPaymentBlockStart n j h) n).1 =
+        bitWidth (iterateT (j + 1) n).1 := by
+  have hledger := bitWidth_iterateT_paymentBlock_eq_claimFiber_card n j h
+  omega
+
+/-- Claim capacity is surplus exactly when the canonical block strictly decreases width. -/
+theorem carryTwoPaymentClaimFiber_card_lt_capacity_iff_bitWidth_paymentBlock_gt
+    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
+    (carryTwoPaymentClaimFiberAt n j).card < extraPaymentCapacityAt n j ↔
+      bitWidth (iterateT (j + 1) n).1 <
+        bitWidth (iterateT (floatPaymentBlockStart n j h) n).1 := by
+  have hledger := bitWidth_iterateT_paymentBlock_eq_claimFiber_card n j h
+  omega
+
 /--
 Exact shifted width ledger.

@@ -301,14 +548,15 @@ theorem bitWidth_iterateT_add_shiftedExtraPaymentCapacity_eq_shiftedCarryTwo
 /-!
 ## Ledger frontier

-The block and its complete first-claim fiber are now canonical, and the
-existing prefix ledger has been repackaged as a shifted segment ledger.
-To obtain the proposed endpoint-only block identity, the remaining task is a
-reindexing theorem: identify the shifted carry count on `[a, j + 1)` with the
-canonical claim fiber, and identify its shifted extra-height sum with the
-single endpoint capacity.  The latter needs a finite-sum transport lemma from
-the interior height-one theorem.  No claim allocation or ambient pressure
-conclusion is inferred before those two exact identifications are proved.
+The local-offset transport is now complete.  On a nonempty canonical block,
+the shifted carry-two count is the complete claim-fiber cardinality and the
+shifted extra-height sum is the endpoint capacity.  Their exact ledger gives a
+three-way arithmetic classification: overload, equality, and surplus are
+respectively strict width growth, width preservation, and strict width decay.
+
+This remains a block-local accounting theorem.  It does not allocate claims to
+individual height units, assert coverage of arbitrary orbit intervals, or
+derive an ambient pressure conclusion without further hypotheses.
 -/

 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-304.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-304.md
new file mode 100644
index 00000000..ce1fb1af
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-304.md
@@ -0,0 +1,62 @@
+# cp-304 Payment Block Ledger
+
+## Result
+
+The payment-block accounting branch is now closed without `sorry` or new
+axioms in `PaymentBlockBridge.lean`.
+
+The implementation avoids successor normalization of `Finset.Ico` during the
+recursive proofs.  It first works over local offsets `t ∈ range len`, with
+global time `a + t`, then transports that finite carrier to the canonical
+global block.
+
+## Proven finite transport
+
+- `shiftedCarryTwoOffsets` represents carry-two sources in `[a, a + len)`.
+- `shiftedOrbitCarryTwoCount_eq_offset_card` identifies the recursive count
+  with the offset-set cardinality.
+- `shiftedExtraPaymentCapacity_eq_sum_range` identifies the recursive
+  capacity with the corresponding local finite sum.
+- `shiftedCarryTwoPositions_eq_carryTwoPositions_Ico` proves that offset
+  translation `t ↦ a + t` gives precisely the carry-two positions of the
+  global half-open interval.
+- `shiftedOrbitCarryTwoCount_eq_carryTwoPaymentClaimFiber_card` specializes
+  this transport to a canonical block and its complete claim fiber.
+
+## Endpoint concentration
+
+`extraPaymentCapacityOn_floatPaymentBlockWithEndpoint_eq_endpoint_extra`
+proves that every non-endpoint term contributes zero: the block interior has
+height one, so all extra-height capacity is concentrated at its endpoint.
+Consequently,
+`shiftedExtraPaymentCapacity_eq_extraPaymentCapacityAt` specializes the
+shifted segment sum to `extraPaymentCapacityAt n j`.
+
+## Exact block classification
+
+For a nonempty growth-debt fiber at endpoint `j`, with canonical start `a`, the
+new ledger is:
+
+```text
+bitWidth (iterateT (j + 1) n) + extraPaymentCapacityAt n j
+  = bitWidth (iterateT a n) + card (carryTwoPaymentClaimFiberAt n j)
+```
+
+Lean now proves three exact equivalences:
+
+```text
+claim card > capacity  iff width strictly grows
+claim card = capacity  iff width is preserved
+claim card < capacity  iff width strictly decreases
+```
+
+These are local block-accounting facts only.  They do not assign individual
+claims to individual capacity units, claim global interval coverage, or infer
+an ambient pressure/convergence conclusion.
+
+## Next work
+
+The immediate target in the current branch is complete.  A later universal
+payment-target layer may quantify this ledger over endpoint families, but it
+needs new hypotheses that connect local canonical blocks; it should not be
+inferred merely from the finite transport proven here.
````
`````
