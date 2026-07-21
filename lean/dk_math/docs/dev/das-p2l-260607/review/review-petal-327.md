# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude

gch: d29d33af3ec201f25c0b110e9d0057c6e1e85986

## Report

(7m58s)

cp-327 の局所登頂を完了しました。

**Lean で確定した事実**

- zero-drift successor でも長さ `≥ 2` なら、`Fin 2` を抽象 dyadic budget に埋め込める。
- saturated predecessor の odd core を `u` とし、successor length が `1` なら:
  - successor odd core = `(9*u + 1) / 4`
  - successor terminal carrier = `(27*u - 1) / 4`
- 次の同値が成立:

  ```text
  successor terminal valuation = 1
    ↔ u % 16 = 11
  ```

- 唯一の局所不足候補を `CanonicalLengthOneBalancedCarrySuccessor` として固定。
- その条件は次の独立した二条件に分離できる:

  ```text
  u % 16 = 11
  successor endpoint is CarryTwoDebtAt
  ```

- 一段先の start は `(27*u - 1) / 8`。
- persistence は `mod 32` で分岐:
  - `u % 32 = 11` → following block length = `1`、したがって saturated ではない。
  - `u % 32 = 27` → following block length `≥ 2`。

**真正な停止点**

`u % 32 = 27` の分岐では、following block が saturated かを residue だけでは決定できません。必要なのは、そのブロックの terminal valuation と claim count を前段から運ぶ **claim-transport theorem** です。

したがって `mod 64` へ進むだけでは不十分です。指示の stopping rule に従い、abstract forest や global matcher へ迂回せず、この地点で止めました。

実装: [UniversalPaymentAmplitude.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean)
レポート: [report-petal-327.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-327.md)

検証済み:

- 対象モジュール
- `DkMath.Collatz.PetalBridge`
- トップレベル `DkMath`
- `git diff --check`
- 変更ファイルに `sorry` / `maxHeartbeats` なし

## Review

## 結論

**条件付き採用。Lean 実装は採用、停止診断は差し戻しじゃ。**

次の成果は有効であり、そのまま残してよい。

- zero-drift successor の abstract `Fin 2` embedding
- successor odd core と terminal carrier の置換公式
- terminal valuation $1$ と predecessor core の $11\bmod16$ 同値
- $32$ を法とする following block length の分岐

しかし、

```lean
CanonicalLengthOneBalancedCarrySuccessor
```

は、実は **空の predicate** である可能性が極めて高い。より強く、saturated block の直後の start state は、successor length に関係なく carry two にならない。

したがって、cp-327 が genuine obstruction とした、

> `% 32 = 27` 分岐で following block の claim count を輸送できない

という地点は、本枝の最初の障害ではない。例外候補そのものを、その一段手前で消せる。

---

## 1. cp-327 の有効な成果

saturated predecessor の odd core を $u$ とする。

successor length が $1$ なら、

$$\operatorname{nextOddCore}=\frac{9u+1}{4}$$

$$\operatorname{nextTerminalCarrier}=\frac{27u-1}{4}$$

が証明された。

さらに、

$$v_{\mathrm{next}}=1\iff u\equiv11\pmod{16}$$

も正しい。

この residue theorem は非自明であり、今後も使える。

ただし、この条件が意味する successor は、

```text
length = 1
terminal valuation = 1
claim count = 0
drift = -1
```

であって、`claim count = 1` の balanced block ではないと見える。

---

## 2. 見落としていた width obstruction

saturated block $k$ の、

- start state を $x$
- odd core を $u$
- next start state を $y$

とする。

既存 theorem により、

$$x=4u-1$$

$$y=\frac{9u-1}{2}$$

である。

また saturation から、

$$u\equiv3\pmod4$$

なので、

$$u\ge3$$

じゃ。

ここで直接計算すると、

$$2(3y+1)=27u-1$$

$$2(4x)=32u-8$$

であり、$u\ge3$ より、

$$27u-1<32u-8$$

したがって、

$$3y+1<4x$$

となる。

一方、saturated unit drift の width theorem は、

$$\operatorname{bitWidth}(y)=\operatorname{bitWidth}(x)+1$$

を既に与えている。

また、

$$x<2^{\operatorname{bitWidth}(x)}$$

なので、

$$4x<2^{\operatorname{bitWidth}(x)+2}=2^{\operatorname{bitWidth}(y)+1}$$

じゃ。

以上から、

$$3y+1<2^{\operatorname{bitWidth}(y)+1}$$

となる。

しかし upper carry が $2$ であるための exact threshold は、

$$\operatorname{stateUpperCarry}(y)=2\iff2^{\operatorname{bitWidth}(y)+1}\le3y+1$$

だった。

よって、

$$\operatorname{stateUpperCarry}(y)\ne2$$

となる。

positive state の upper carry は $1$ または $2$ なので、結論は、

$$\operatorname{stateUpperCarry}(y)=1$$

じゃ。

---

## 3. 最優先で追加すべき theorem

```lean
theorem CanonicalSaturatedBorderBlock.nextStart_stateUpperCarry_eq_one
    {n : OddNat} {k : ℕ}
    (h : CanonicalSaturatedBorderBlock n k) :
    stateUpperCarry (canonicalBlockStartState n (k + 1)) = 1 := by
  ...
```

または claim 語彙で、

```lean
theorem CanonicalSaturatedBorderBlock.not_carryTwo_nextBlockStart
    {n : OddNat} {k : ℕ}
    (h : CanonicalSaturatedBorderBlock n k) :
    ¬ CarryTwoDebtAt n (canonicalBlockStartTime n (k + 1)) := by
  ...
```

これは successor length を仮定しない。

cp-327 の residue grammar より強い、saturated-successor 全体に対する theorem じゃ。

---

## 4. Successor の最深 depth は必ず claim hole

block $j$ の length を $L_j$ とする。

canonical source 座標では、

$$\operatorname{SourceAtDepth}(L_j)=\operatorname{BlockStartTime}(j)$$

となる。

したがって saturated block の successor $j=k+1$ では、

$$L_j\notin\operatorname{PaymentClaimDepths}(j)$$

である。

つまり、

$$L_j\in\operatorname{ClaimHoles}(j)$$

じゃ。

Lean API としては次を置くべきである。

```lean
theorem canonicalPaymentSourceAtDepth_length_eq_startTime
    (n : OddNat) (k : ℕ) :
    canonicalPaymentSourceAtDepth n k (canonicalBlockLength n k) =
      canonicalBlockStartTime n k := by
  ...
```

```lean
theorem CanonicalSaturatedBorderBlock.nextBlockLength_mem_claimHoles
    {n : OddNat} {k : ℕ}
    (h : CanonicalSaturatedBorderBlock n k) :
    canonicalBlockLength n (k + 1) ∈
      canonicalBlockClaimHoles n (k + 1) := by
  ...
```

これにより、

$$H_{k+1}\ge1$$

$$A_{k+1}\le L_{k+1}-1$$

が得られる。

これは、求めていた claim-transport theorem そのものじゃ。

---

## 5. Length-one successor の claim count はゼロ

successor length が $1$ なら、唯一の depth は block start と endpoint の両方を兼ねる。

その唯一の source が carry two ではないので、

$$A_{k+1}=0$$

となる。

```lean
theorem CanonicalSaturatedBorderBlock.nextClaimCount_eq_zero_of_length_one
    {n : OddNat} {k : ℕ}
    (h : CanonicalSaturatedBorderBlock n k)
    (hL : canonicalBlockLength n (k + 1) = 1) :
    canonicalBlockClaimCount n (k + 1) = 0 := by
  ...
```

従って、

```lean
CanonicalLengthOneBalancedCarrySuccessor n k
```

は成立しない。

```lean
theorem not_canonicalLengthOneBalancedCarrySuccessor
    (n : OddNat) (k : ℕ) :
    ¬ CanonicalLengthOneBalancedCarrySuccessor n k := by
  ...
```

これが cp-327 に対する決定的な補正じゃ。

---

## 6. `% 16 = 11` の正しい意味

successor length が $1$ のとき claim count は $0$。

したがって drift は、

$$D_{k+1}=0-v_{k+1}=-v_{k+1}$$

となる。

### $u\equiv11\pmod{16}$

cp-327 の theorem により、

$$v_{k+1}=1$$

なので、

$$D_{k+1}=-1$$

じゃ。

saturated predecessor は $D_k=1$ なので、

$$D_k+D_{k+1}=0$$

となる。

これは exact two-block repayment じゃ。

### $u\equiv3\pmod{16}$

next length $1$ の coarse residue は $u\equiv3$ または $11\bmod16$。

$11$ でなければ terminal valuation は $1$ ではなく、かつ valuation は正なので、

$$v_{k+1}\ge2$$

となる。

したがって、

$$D_{k+1}\le-2$$

であり、

$$D_k+D_{k+1}<0$$

じゃ。

つまり、

> saturated block の successor length が $1$ なら、必ず即時 scalar repayment が成立する。

---

## 7. cp-327 の persistence namespace は現在 vacuous

現在の、

```lean
namespace CanonicalLengthOneBalancedCarrySuccessor
```

以下の、

- following start formula
- mod $32$ 分岐
- following block length theorem

は、前提 predicate が空なら全て vacuous theorem になる。

式そのものは算術的に正しいが、数学的対象を一件も持たない。

有効な形で残すなら、predicate を次へ変更する方がよい。

```lean
def CanonicalLengthOneTerminalOneSuccessor
    (n : OddNat) (k : ℕ) : Prop :=
  CanonicalSaturatedBorderBlock n k ∧
    canonicalBlockLength n (k + 1) = 1 ∧
      canonicalBlockTerminalValuation n (k + 1) = 1
```

これは、

$$u\equiv11\pmod{16}$$

と同値であり、実在し得る。

この predicate の下では、

- following start $=(27u-1)/8$
- $u\bmod32$ の分岐

は意味を持つ。

ただし、この successor は balanced carry ではなく、drift $-1$ の repayment block じゃ。

---

## 8. Zero-carrier balanced successor も圧縮される

cp-326 では zero-carrier balanced block に、

### Full balanced branch

$$L=v,\qquad A=L,\qquad H=0$$

### Exceptional length-two branch

$$L=2,\qquad v=1,\qquad A=1,\qquad H=1$$

の二種類があった。

しかし saturated successor では最深 depth が必ず hole なので、

$$H\ge1$$

じゃ。

したがって full balanced branch は successor として不可能。

saturated successor の zero-carrier balanced branchは、必ず、

$$L=2,\qquad v=1,\qquad A=1$$

へ潰れる。

さらに唯一の hole は最深 depth $2$ なので、

$$\operatorname{Claims}={1}$$

となる。

---

## 9. Tight valuation-one successor の missing depth

tight valuation-one positive block は hole 数が一。

saturated successor では最深 depthが hole であるため、唯一の missing depth は必ず、

$$d_{\mathrm{miss}}=L$$

じゃ。

従って claim set は、

$$\operatorname{Claims}=\operatorname{Icc}(1,L-1)$$

となる。

これはかなり強い grammar じゃ。

```lean
theorem CanonicalTightValuationOnePositiveBlock.missingDepth_eq_length_of_prev_saturated
```

を置ける。

これにより、「どこか一箇所が欠ける」という曖昧さが消え、欠けるのは必ず block start であると固定される。

---

## 10. Saturated successor の局所処理は全て閉じる

saturated block の successor は次のように処理できる。

### Negative drift

scalar repayment。

### Zero drift

length $1$ は不可能。よって length $2$ 以上であり、cp-327 の、

```lean
abstractZeroSuccessorUnitEmbedding
```

が使える。

### Positive drift

successor は nonsaturated で length $3$ 以上。

cp-326 の、

- lower `Fin 2`
- upper demand carrier

の disjoint embedding が使える。

したがって abstract dyadic 層では、

> saturated predecessor の unit は、全 successor branch で局所的に処理可能

となる。

局所不足候補は消滅する。

---

## 11. 真正な障害は global resource transport

cp-327 が止まった claim-transport は、上記 width theorem で閉じられる。

本当に残る障害は、cp-326 で既に露出していたこちらじゃ。

```text
block ごとの abstract dyadic budget を、
有限開始値に由来する global resource へどう割り当てるか
```

必要なのは、

- block-local budget の root
- root の有限性
- leaf の非重複
- 時間方向の所有権
- 新規 root を勝手に発行しないこと
- 同じ upper boundary を無制限に再利用しないこと

である。

つまり局所 arithmetic ではなく、global conservation transport が次の本丸じゃ。

---

## 判定まとめ

### Zero-successor abstract embedding

**完成。**

### Successor odd-core / terminal substitution

**完成。**

### Modulo-sixteen theorem

**完成。有効な非自明成果。**

### `CanonicalLengthOneBalancedCarrySuccessor`

**空 predicate と見られる。解釈差し戻し。**

### Modulo-thirty-two persistence grammar

**現 predicate 下では vacuous。非空 predicate へ一般化すれば再利用可能。**

### Claim-transport obstruction

**真正な障害ではない。successor start carry-one theorem で閉じられる。**

### 真の次戦線

**saturated-successor deepest-hole theorem と、global nonduplicating dyadic resource transport。**

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge FloatWindow branch after
report-petal-327.

The cp-327 arithmetic substitutions and modulo-sixteen theorem are accepted.

However, the stopping diagnosis must be revised.

The predicate

    CanonicalLengthOneBalancedCarrySuccessor

should be impossible.  A saturated block's next start has upper carry one,
independently of the successor block length.

Do not continue the modulo-32 persistence branch before proving or refuting
this stronger width obstruction.

# Stage A — next-start carry obstruction

Let:

    u = canonicalBlockOddCore n k
    x = canonicalBlockStartState n k
    y = canonicalBlockStartState n (k + 1).

For a saturated block prove:

    x = 4*u - 1;
    y = (9*u - 1)/2;
    3 <= u;
    bitWidth y = bitWidth x + 1.

Then prove:

    3*y + 1 < 4*x.

Use:

    x < 2^(bitWidth x)

to derive:

    3*y + 1 < 2^(bitWidth y + 1).

Apply:

    stateUpperCarry_eq_two_iff_pow_succ_le_threeNPlusOne

and conclude:

    stateUpperCarry y = 1.

Target theorem:

    CanonicalSaturatedBorderBlock.nextStart_stateUpperCarry_eq_one.

# Stage B — deepest successor claim hole

Prove the general coordinate identity:

    canonicalPaymentSourceAtDepth n j
        (canonicalBlockLength n j)
      =
    canonicalBlockStartTime n j.

Use Stage A to prove for a saturated predecessor:

    canonicalBlockLength n (k + 1)
      ∈
    canonicalBlockClaimHoles n (k + 1).

Derive:

    1 <= claimHoles.card;
    successor claimCount <= successor length - 1.

This is the missing claim-transport theorem.

# Stage C — eliminate the length-one balanced-carry predicate

For successor length one prove:

    canonicalBlockClaimCount n (k + 1) = 0.

Then prove:

    not_canonicalLengthOneBalancedCarrySuccessor.

Update the cp-327 report: the former exceptional predicate is empty, and all
theorems under its namespace are vacuous.

Do not delete useful arithmetic formulas until they are generalized to a
nonempty predicate.

# Stage D — salvage the modulo grammar

Define the nonvacuous predicate:

    CanonicalLengthOneTerminalOneSuccessor n k :=
      CanonicalSaturatedBorderBlock n k
      and canonicalBlockLength n (k + 1) = 1
      and canonicalBlockTerminalValuation n (k + 1) = 1.

Prove:

    CanonicalLengthOneTerminalOneSuccessor n k
      <->
    CanonicalSaturatedBorderBlock n k
      and canonicalBlockLength n (k + 1) = 1
      and canonicalBlockOddCore n k % 16 = 11.

Move or generalize the following-start and modulo-32 theorems to this
nonvacuous predicate.

Also prove:

    successor claimCount = 0;
    successor drift = -1;
    predecessor drift + successor drift = 0.

For the alternative residue class modulo sixteen, prove successor drift <= -2.

# Stage E — refine rigid successor classes

Use the deepest-hole theorem to prove:

    a zero-carrier balanced successor of a saturated block
      must be the exceptional length-two branch;

    its claim depths are exactly {1};

    a tight valuation-one positive successor has unique missing depth equal to
      its block length;

    its claim depths are Icc 1 (length - 1).

Eliminate the full-balanced zero-carrier branch from saturated successors.

# Stage F — complete local saturated discharge

Prove a single local classification:

    successor drift < 0
    or successor drift = 0 with successor length >= 2
    or successor drift > 0 and successor is nonsaturated.

Then attach the already proved discharge:

    negative -> scalar repayment;
    zero and length >= 2 -> abstract Fin 2 embedding;
    positive nonsaturated -> disjoint lower saturated-unit and upper demand
      embeddings.

Conclude conditionally at the abstract level:

    every saturated predecessor unit is locally discharged by its successor.

Do not call this actual bit repayment.

# Stage G — remove the false local obstruction

Record explicitly:

    there is no locally insufficient length-one balanced-carry successor;

    modulo-32 claim persistence is not needed to discharge a saturated unit;

    the local successor grammar is closed at the abstract dyadic level.

# Stage H — block-internal carry-profile normal form

Expose the general exact source-state formula.

For valid depth d in a block of length L and odd core u, prove:

    iterateT (canonicalPaymentSourceAtDepth n k d) n + 1
      =
    2^d * 3^(L - d) * u.

Derive:

    d belongs to canonicalPaymentClaimDepths
      <->
    stateUpperCarry
      (2^d * 3^(L - d) * u - 1)
      = 2.

This theorem should become the generic claim-profile transport API for future
block arithmetic.

# Stage I — return to the genuine global obstruction

Resume the abstract dyadic forest / global root-resource program.

Define a conditional global resource interface containing:

    finite roots determined by the initial natural number;
    dyadic rank per root;
    assignment of each block-local budget to one subtree;
    temporal ownership;
    pairwise disjoint leaves or a uniform reuse bound;
    no creation of new roots.

Prove only the conditional consequence:

    such a resource structure
      ->
    finite total abstract demand bound.

Do not assert that the structure exists.

# Stage J — upper-boundary audit

Audit whether current bit-width, upper-carry, and eventually-zero APIs provide:

    root identity;
    root rank;
    subtree ownership;
    temporal nonreuse.

Scalar width inequalities alone are insufficient.

Stop when an actual resource is reused without a proved multiplicity bound.

# Stopping rule

Stop at the first genuine obstruction among:

    next-start carry one theorem fails;
    deepest source coordinate is not the block start;
    length-one successor can carry two;
    nonvacuous modulo predicate cannot recover the arithmetic formulas;
    generic source-state formula cannot be proved;
    block-local budgets cannot be assigned to finite global roots;
    actual upper-boundary roots admit uncontrolled temporal reuse.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-328.md
```

cp-327 は claim transport を求めて一段先へ進んだ。

しかし答えは、次 block の内部ではなく、**saturated block が作った一 bit の width shift** の中に既にあったぞい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean
index d97bbc01..4d41fe3e 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean
@@ -2327,6 +2327,35 @@ theorem two_le_successor_dyadic_budget_of_two_le_length
     (show 1 ≤ canonicalBlockLength n (k + 1) - 1 by omega)
   simpa using this

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
+/-- A zero-drift successor of length at least two carries the preceding
+saturated mass-two unit in the low two slots of its abstract budget. -/
+noncomputable def abstractZeroSuccessorUnitEmbedding
+    {n : OddNat} {k : ℕ}
+    (_hzero : endpointAccountingTerm n (k + 1) = 0)
+    (hL : 2 ≤ canonicalBlockLength n (k + 1)) :
+    Fin 2 ↪ CanonicalAbstractDyadicBudgetCarrier n (k + 1) where
+  toFun i := by
+    refine ⟨i.val, ?_⟩
+    have htwo : 2 ≤ 2 ^ (canonicalBlockLength n (k + 1) - 1) :=
+      two_le_successor_dyadic_budget_of_two_le_length _hzero hL
+    omega
+  inj' := by
+    intro i j hij
+    have hval := congrArg Fin.val hij
+    change i.val = j.val at hval
+    exact Fin.ext hval
+
 /-- Local dyadic potential: the selected positive drift, denominated at depth
 `d`, is bounded by one block-width denomination `2^(L-1)`. -/
 theorem intToNat_endpointAccountingTerm_mul_two_pow_depth_le_two_pow_length_sub_one
@@ -2374,11 +2403,10 @@ The stronger candidate
 `successor length = 1` and `successor terminal valuation = 1`
 `-> predecessor odd core % 16 = 11`

-requires an explicit normal form connecting the successor odd core (or its
-terminal carrier) to the predecessor odd core.  The current API exposes the
-successor start and successor length, but not that substituted terminal-carrier
-identity.  Do not replace this missing algebraic bridge by computation or a
-statistical residue table.
+is proved below by first exposing the successor odd-core and terminal-carrier
+substitutions.  The resulting modulo-thirty-two continuation grammar also
+records the next genuine boundary: predecessor residue alone does not
+transport the following block's claim count.
 -/

 /-- A length-one successor of a saturated block selects the class three
@@ -2392,6 +2420,94 @@ theorem CanonicalSaturatedBorderBlock.oddCore_mod_eight_eq_three_of_next_length_
   · have htwo := h.two_le_nextBlockLength_of_core_mod_eight_eq_seven hseven
     omega

+/-- Exact odd-core substitution for a length-one successor. -/
+theorem CanonicalSaturatedBorderBlock.nextOddCore_eq_quarter_nine_core_add_one
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
+    (hL : canonicalBlockLength n (k + 1) = 1) :
+    canonicalBlockOddCore n (k + 1) =
+      (9 * canonicalBlockOddCore n k + 1) / 4 := by
+  let u := canonicalBlockOddCore n k
+  let u' := canonicalBlockOddCore n (k + 1)
+  have hstart := canonicalBlockStartState_add_one_eq_pow_mul_oddCore n (k + 1)
+  have hnext := h.nextStartState_add_one_eq
+  have hsucc := canonicalBlockStartState_succ_eq_nextStartState n k
+  have hu8 := h.oddCore_mod_eight_eq_three_of_next_length_one hL
+  have hu : u = 8 * (u / 8) + 3 := by
+    have := Nat.mod_add_div u 8
+    omega
+  rw [hL] at hstart
+  norm_num at hstart
+  have hhalf : (9 * u + 1) / 2 = 36 * (u / 8) + 14 := by
+    omega
+  have hquarter : (9 * u + 1) / 4 = 18 * (u / 8) + 7 := by
+    omega
+  dsimp [u] at hu hhalf hquarter
+  rw [hhalf] at hnext
+  rw [hquarter]
+  omega
+
+/-- The terminal carrier of a length-one successor is the exact substituted
+quarter-word `(27*u-1)/4`. -/
+theorem CanonicalSaturatedBorderBlock.nextTerminalCarrier_eq_quarter_twentySeven_core_sub_one
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
+    (hL : canonicalBlockLength n (k + 1) = 1) :
+    canonicalBlockTerminalCarrier n (k + 1) =
+      (27 * canonicalBlockOddCore n k - 1) / 4 := by
+  let u := canonicalBlockOddCore n k
+  have hu8 := h.oddCore_mod_eight_eq_three_of_next_length_one hL
+  have hu : u = 8 * (u / 8) + 3 := by
+    have := Nat.mod_add_div u 8
+    omega
+  rw [canonicalBlockTerminalCarrier, hL]
+  norm_num
+  rw [h.nextOddCore_eq_quarter_nine_core_add_one hL]
+  dsimp [u] at hu ⊢
+  omega
+
+/-- For the length-one successor, terminal valuation one is exactly the
+predecessor residue class eleven modulo sixteen. -/
+theorem CanonicalSaturatedBorderBlock.nextTerminalValuation_eq_one_iff_core_mod_sixteen_eq_eleven
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
+    (hL : canonicalBlockLength n (k + 1) = 1) :
+    canonicalBlockTerminalValuation n (k + 1) = 1 ↔
+      canonicalBlockOddCore n k % 16 = 11 := by
+  let u := canonicalBlockOddCore n k
+  let c := canonicalBlockTerminalCarrier n (k + 1)
+  have hcpos := canonicalBlockTerminalCarrier_pos n (k + 1)
+  have hc := h.nextTerminalCarrier_eq_quarter_twentySeven_core_sub_one hL
+  have hu8 := h.oddCore_mod_eight_eq_three_of_next_length_one hL
+  constructor
+  · intro hv
+    have hnot4 : ¬ 4 ∣ c := by
+      intro hfour
+      have htwo := (two_le_v2_iff_four_dvd hcpos.ne').2 hfour
+      unfold canonicalBlockTerminalValuation at hv
+      omega
+    have hrem : u % 16 = 3 ∨ u % 16 = 11 := by
+      omega
+    rcases hrem with h3 | h11
+    · have hu : u = 16 * (u / 16) + 3 := by
+        have := Nat.mod_add_div u 16
+        omega
+      have hcFour : 4 ∣ c := by
+        refine ⟨27 * (u / 16) + 5, ?_⟩
+        dsimp [c, u] at hc hu ⊢
+        omega
+      exact (hnot4 hcFour).elim
+    · exact h11
+  · intro hu16
+    have hu : u = 16 * (u / 16) + 11 := by
+      have := Nat.mod_add_div u 16
+      omega
+    have hcform : c = 108 * (u / 16) + 74 := by
+      dsimp [c, u] at hc hu ⊢
+      omega
+    have hceven : c % 2 = 0 := by rw [hcform]; omega
+    have hchalfodd : (c / 2) % 2 = 1 := by rw [hcform]; omega
+    unfold canonicalBlockTerminalValuation
+    change v2 c = 1
+    rw [v2_step_of_even c hceven hcpos, v2_odd _ hchalfodd]
+
 /-- For a length-one block, the sole claim-count condition is exactly the
 carry-two condition at its endpoint source. -/
 theorem canonicalBlockClaimCount_eq_one_iff_endpoint_carryTwo_of_length_one
@@ -2420,6 +2536,136 @@ theorem canonicalBlockClaimCount_eq_one_iff_endpoint_carryTwo_of_length_one
     have hle := canonicalBlockClaimCount_le_length n k
     omega

+/-- The sole locally insufficient successor class after abstract dyadic
+discharge.  Saturation is a predecessor condition; residue and endpoint claim
+remain separate data. -/
+def CanonicalLengthOneBalancedCarrySuccessor
+    (n : OddNat) (k : ℕ) : Prop :=
+  CanonicalSaturatedBorderBlock n k ∧
+    canonicalBlockLength n (k + 1) = 1 ∧
+      canonicalBlockTerminalValuation n (k + 1) = 1 ∧
+        canonicalBlockClaimCount n (k + 1) = 1
+
+/-- Residue/carry presentation of the length-one balanced successor. -/
+theorem canonicalLengthOneBalancedCarrySuccessor_iff_residue_and_endpoint_carry
+    (n : OddNat) (k : ℕ) :
+    CanonicalLengthOneBalancedCarrySuccessor n k ↔
+      CanonicalSaturatedBorderBlock n k ∧
+        canonicalBlockLength n (k + 1) = 1 ∧
+          canonicalBlockOddCore n k % 16 = 11 ∧
+            CarryTwoDebtAt n (paymentEndpointSeq n (k + 1)) := by
+  constructor
+  · rintro ⟨hsat, hL, hv, hclaim⟩
+    exact ⟨hsat, hL,
+      (hsat.nextTerminalValuation_eq_one_iff_core_mod_sixteen_eq_eleven hL).1 hv,
+      (canonicalBlockClaimCount_eq_one_iff_endpoint_carryTwo_of_length_one hL).1
+        hclaim⟩
+  · rintro ⟨hsat, hL, hres, hcarry⟩
+    exact ⟨hsat, hL,
+      (hsat.nextTerminalValuation_eq_one_iff_core_mod_sixteen_eq_eleven hL).2 hres,
+      (canonicalBlockClaimCount_eq_one_iff_endpoint_carryTwo_of_length_one hL).2
+        hcarry⟩
+
+namespace CanonicalLengthOneBalancedCarrySuccessor
+
+/-- The start after the exceptional length-one successor is the exact
+eighth-word `(27*u-1)/8`. -/
+theorem followingStartState_eq
+    {n : OddNat} {k : ℕ} (h : CanonicalLengthOneBalancedCarrySuccessor n k) :
+    canonicalBlockStartState n (k + 2) =
+      (27 * canonicalBlockOddCore n k - 1) / 8 := by
+  rcases h with ⟨hsat, hL, hv, _⟩
+  have hnext := canonicalBlockNextStartState_eq_terminalCarrier_div_pow_valuation
+    n (k + 1)
+  have hsucc := canonicalBlockStartState_succ_eq_nextStartState n (k + 1)
+  have hc := hsat.nextTerminalCarrier_eq_quarter_twentySeven_core_sub_one hL
+  have hres :=
+    (hsat.nextTerminalValuation_eq_one_iff_core_mod_sixteen_eq_eleven hL).1 hv
+  let u := canonicalBlockOddCore n k
+  have hu : u = 16 * (u / 16) + 11 := by
+    have := Nat.mod_add_div u 16
+    omega
+  rw [show k + 2 = k + 1 + 1 by omega, hsucc, hnext, hv]
+  norm_num
+  dsimp [u] at hu hres ⊢
+  rw [hc]
+  omega
+
+/-- The modulo-sixteen obstruction splits into the two possible modulo-thirty-
+two continuation classes. -/
+theorem core_mod_thirtyTwo_eq_eleven_or_twentySeven
+    {n : OddNat} {k : ℕ} (h : CanonicalLengthOneBalancedCarrySuccessor n k) :
+    canonicalBlockOddCore n k % 32 = 11 ∨
+      canonicalBlockOddCore n k % 32 = 27 := by
+  have hres :=
+    (canonicalLengthOneBalancedCarrySuccessor_iff_residue_and_endpoint_carry
+      n k).1 h |>.2.2.1
+  omega
+
+/-- In residue class eleven modulo thirty-two, the following block again has
+length one. -/
+theorem followingBlockLength_eq_one_of_core_mod_thirtyTwo_eq_eleven
+    {n : OddNat} {k : ℕ} (h : CanonicalLengthOneBalancedCarrySuccessor n k)
+    (hres : canonicalBlockOddCore n k % 32 = 11) :
+    canonicalBlockLength n (k + 2) = 1 := by
+  let u := canonicalBlockOddCore n k
+  have hu : u = 32 * (u / 32) + 11 := by
+    have := Nat.mod_add_div u 32
+    omega
+  rw [canonicalBlockLength_eq_v2_startState_add_one, h.followingStartState_eq]
+  have hstart : (27 * u - 1) / 8 + 1 = 108 * (u / 32) + 38 := by
+    omega
+  dsimp [u] at hu hstart hres ⊢
+  rw [hstart]
+  have heven : (108 * (canonicalBlockOddCore n k / 32) + 38) % 2 = 0 := by
+    omega
+  have hpos : 0 < 108 * (canonicalBlockOddCore n k / 32) + 38 := by omega
+  have hhalfodd :
+      ((108 * (canonicalBlockOddCore n k / 32) + 38) / 2) % 2 = 1 := by
+    omega
+  rw [v2_step_of_even _ heven hpos, v2_odd _ hhalfodd]
+
+/-- In residue class twenty-seven modulo thirty-two, the following block has
+length at least two.  This is the first persistence branch not settled by the
+local length-one grammar. -/
+theorem two_le_followingBlockLength_of_core_mod_thirtyTwo_eq_twentySeven
+    {n : OddNat} {k : ℕ} (h : CanonicalLengthOneBalancedCarrySuccessor n k)
+    (hres : canonicalBlockOddCore n k % 32 = 27) :
+    2 ≤ canonicalBlockLength n (k + 2) := by
+  let u := canonicalBlockOddCore n k
+  have hu : u = 32 * (u / 32) + 27 := by
+    have := Nat.mod_add_div u 32
+    omega
+  rw [canonicalBlockLength_eq_v2_startState_add_one, h.followingStartState_eq]
+  have hstart : (27 * u - 1) / 8 + 1 = 108 * (u / 32) + 92 := by
+    omega
+  dsimp [u] at hu hstart hres ⊢
+  rw [hstart]
+  apply (two_le_v2_iff_four_dvd (by omega)).2
+  exact ⟨27 * (canonicalBlockOddCore n k / 32) + 23, by ring⟩
+
+/-- The length-one modulo-thirty-two continuation cannot itself be saturated,
+because saturation requires canonical length two. -/
+theorem not_following_saturated_of_core_mod_thirtyTwo_eq_eleven
+    {n : OddNat} {k : ℕ} (h : CanonicalLengthOneBalancedCarrySuccessor n k)
+    (hres : canonicalBlockOddCore n k % 32 = 11) :
+    ¬ CanonicalSaturatedBorderBlock n (k + 2) := by
+  intro hsaturated
+  have hOne := h.followingBlockLength_eq_one_of_core_mod_thirtyTwo_eq_eleven hres
+  rw [hsaturated.length_eq_two] at hOne
+  omega
+
+end CanonicalLengthOneBalancedCarrySuccessor
+
+/-!
+The modulo-thirty-two grammar is exact for one further block.  The class
+`u % 32 = 27` only yields following length at least two; deciding whether that
+block is saturated also requires its claim count and terminal valuation.
+Those are not determined by the predecessor residue currently exposed by the
+API.  A modulo-64 arithmetic split alone therefore cannot establish or exclude
+persistence without a new claim-transport theorem.
+-/
+
 /-! ## Abstract nonduplicating dyadic carrier

 This section realizes the numerical half-budget as two disjoint `Fin` images.
@@ -2428,17 +2674,6 @@ demand is shifted into the upper half.  These are abstract potential slots.
 They are not orbit indices, binary bit positions, or upper-boundary resources.
 -/

-/-- Abstract block-width dyadic budget. -/
-abbrev CanonicalAbstractDyadicBudgetCarrier
-    (n : OddNat) (k : ℕ) :=
-  Fin (2 ^ (canonicalBlockLength n k - 1))
-
-/-- Abstract selected positive-drift demand at its dyadic depth. -/
-abbrev CanonicalAbstractDyadicDemandCarrier
-    (n : OddNat) (k : ℕ) :=
-  Fin (Int.toNat (endpointAccountingTerm n k) *
-    2 ^ canonicalSelectedPositivePressureDepth n k)
-
 /-- The positive nonsaturated demand embeds into the upper half of its abstract
 block budget. -/
 noncomputable def abstractDyadicDemandEmbeddingUpperHalf
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-327.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-327.md
new file mode 100644
index 00000000..ff76568f
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-327.md
@@ -0,0 +1,123 @@
+# Petal / FloatWindow Report cp-327
+
+## Status
+
+The local zero-successor carrier, exact successor substitution, modulo-sixteen
+classification, and one-step persistence grammar are complete without
+`sorry`.  Work stops at the persistence-grammar condition named by the
+checkpoint: residue data does not determine the following block's claim
+count.
+
+## Zero-successor discharge
+
+A zero-drift successor of length at least two now has an explicit embedding
+
+```text
+Fin 2 -> CanonicalAbstractDyadicBudgetCarrier n (k + 1).
+```
+
+It uses the low two abstract slots.  Therefore every such successor is paid at
+the abstract dyadic level.  This remains a potential statement, not an actual
+bit repayment.
+
+The sole locally insufficient successor candidate is exactly:
+
+```text
+successor length = 1
+successor terminal valuation = 1
+successor claim count = 1
+successor endpoint is CarryTwoDebtAt
+```
+
+## Exact arithmetic substitution
+
+For a saturated predecessor with odd core `u` and a length-one successor, Lean
+proves:
+
+```text
+successor start         = (9*u - 1) / 2
+successor odd core      = (9*u + 1) / 4
+successor terminal word = (27*u - 1) / 4
+```
+
+The first equality was already public.  The latter two are now public bridge
+theorems, avoiding repeated unfolding of the canonical block normal form.
+
+## Modulo-sixteen classification
+
+The candidate implication strengthens to an equivalence:
+
+```text
+successor terminal valuation = 1
+  <-> predecessor odd core % 16 = 11
+```
+
+This is proved arithmetically from the exact terminal word.  No numerical
+enumeration is used.
+
+`CanonicalLengthOneBalancedCarrySuccessor` packages the exceptional local
+class.  Its caller-facing equivalent form keeps two independent requirements:
+
+```text
+predecessor odd core % 16 = 11
+and
+CarryTwoDebtAt at the successor endpoint.
+```
+
+The residue condition does not imply the claim condition, and the API does not
+silently identify them.
+
+## One-step persistence grammar
+
+For the exceptional class, the following block starts at
+
+```text
+(27*u - 1) / 8.
+```
+
+The modulo-sixteen class splits exactly modulo thirty-two:
+
+```text
+u % 32 = 11 or u % 32 = 27.
+```
+
+Lean proves:
+
+- `u % 32 = 11` gives following block length `1`, hence that following block
+  is not saturated;
+- `u % 32 = 27` gives following block length at least `2`.
+
+## Genuine obstruction
+
+The `% 32 = 27` branch is not decided by arithmetic length data.  Saturation
+of the following block additionally needs its terminal valuation and claim
+count.  No existing theorem transports those claim facts from the predecessor
+residue or from the exceptional successor endpoint.
+
+Consequently a modulo-64 split by itself would not close persistence.  The
+next required theorem is a claim-transport bridge connecting the successor
+endpoint/carry structure to the claim carrier of block `k + 2`.
+
+Per the checkpoint stopping rule, the later independent tasks were not used to
+bypass this obstruction:
+
+- one-hole position refinement;
+- abstract dyadic forest module;
+- global root-resource specification;
+- challenge-facing conditional width theorem.
+
+These remain valid future tasks after the local claim-transport interface is
+designed or the persistence branch is explicitly separated from them.
+
+## Verification
+
+The following gates passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath
+git diff --check
+```
+
+The changed Lean file contains no `sorry` and no `maxHeartbeats` override.
````
`````
