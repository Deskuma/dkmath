# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentSaturatedSuccessor

gch: a3b77dd6a734109ba742fd6e25ece889b5e3ee08

## Report

cp-319 の登頂作業を完了しました。

**Lean で確定した事実**

- 飽和ブロックの長さは必ず `2`
- 終端 valuation は必ず `1`
- 飽和ブロックは連続しない
- 飽和後続は「非正ドリフト」または「正圧力」
- 飽和 core は `mod 8 = 3` または `7`
- `mod 8 = 3` なら次ブロック長は `1`
- `mod 8 = 7` なら次ブロック長は `2` 以上
- 飽和 index の packing bound:
  `2 * saturated.card ≤ intervalLength + 1`
- 正ドリフトは `positive pressure` と `saturated` に厳密分割
- 動的深さ圧力による有限総和評価:

  ```text
  sum positive drift
    ≤ sum selected dynamic-depth pressure
      + saturatedIndices.card
  ```

実装は [UniversalPaymentSaturatedSuccessor.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentSaturatedSuccessor.lean)、結果は [report-petal-319.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-319.md) に記録しました。

検証結果:

- `lake build DkMath.Collatz.PetalBridge.FloatWindow` 成功
- `lake build DkMath.Collatz.PetalBridge` 成功
- `lake build DkMath` 成功
- 新規ファイルに `sorry` なし
- `git diff --check` 成功

次の本当の障害は、異なる `(block, depth)` の局所圧力が同じ支払資源を重複計上しないことを示す incidence 定理です。動的圧力総和そのものは、今回すでに閉じました。

## Review

# cp-319 実装レビュー

## 結論

**全面採用。cp-319 は saturated branch を本当に閉じた。**

前 checkpoint で有限観測だったものが、今回は全て exact theorem へ昇格した。

- saturated block は必ず長さ $2$
- terminal valuation は必ず $1$
- endpoint height は必ず $2$
- saturated block は連続しない
- saturated successor が正 drift なら、必ず pressure branch
- saturated core は $u\equiv3\pmod4$
- よって $u\bmod8$ は $3$ または $7$
- saturated index は有限区間の高々半分
- 正 drift は pressure / saturation に排他的に分割される

さらに、

$$
\sum D_k^+\le\sum \text{selected pressure}_k+|\text{saturated indices}|
$$

という有限総和評価まで到達した。

これは大躍進じゃ。

ただし、report の「次の障害」には重要な補正がある。

> 異なる block の pressure incidence が同じ source resource を重複計上する

という問題は、canonical block partition により、source-time 側では既に起こらない。

本当に未証明なのは、

> **disjoint な pressure incidence を、queue を減らす将来 capacity・境界資源・NoLift obstruction のどれへ輸送するか**

じゃ。

そして、その前に `canonicalDynamicPressureDepth` の depth $0$ 分岐を除去するべきである。

---

## 1. Saturated length $2$ の証明

今回の証明は非常に良い。

saturated block では、

$$
D=1
$$

なので、block start を $x$、next start を $x'$ とすれば、

$$
\operatorname{bitWidth}(x') = \operatorname{bitWidth}(x) + 1
$$

である。

一方、normal form は、

$$
x+1=2^Lu
$$

$$
x'=\frac{3^Lu-1}{2^{L-1}}
$$

を与える。

$L\ge3$ なら、

$$
3^L<2^{2L-1}
$$

なので、

$$
x'<x+1
$$

となり、自然数性から、

$$
x'\le x
$$

じゃ。

これは一 bit の厳密増加と矛盾する。

よって、

$$
L=2
$$

しかない。

この証明の強みは、carry pattern を個別に分類せず、

```text
arithmetic normal form
+
exact signed width ledger
```

だけで saturation を潰した点じゃ。

---

## 2. No consecutive saturation

二つの saturated block を続けると、最初の odd core $u$ から、

$$
x_0=4u-1
$$

$$
x_1=\frac{9u-1}{2}
$$

$$
x_2=\frac{81u+1}{16}
$$

が得られる。

二回の unit drift は、

$$
\operatorname{bitWidth}(x_2) = \operatorname{bitWidth}(x_0)+2
$$

を要求するので、

$$
2x_0<x_2
$$

でなければならない。

しかし exact arithmetic から、

$$
x_2<2x_0
$$

となる。

完全な矛盾じゃ。

したがって、

$$
\operatorname{Saturated}(k)
\Longrightarrow
\neg\operatorname{Saturated}(k+1)
$$

が確定した。

これによって saturated は pumpable cycle の構成要素ではなく、

> **隣接配置できない孤立 $+1$ token**

となった。

---

## 3. Saturated successor の正しい定理

有限監査で偽だったのは、

$$
\operatorname{Saturated}(k)
\Longrightarrow
D_{k+1}\le0
$$

じゃ。

今回得た正しい theorem は、

$$
\operatorname{Saturated}(k)
\Longrightarrow
D_{k+1}\le0
\ \lor
M_{k+1}(v_{k+1})>0
$$

である。

これは十分強い。

正 successor の 1,785 例は、例外の連鎖ではない。

全て、

```text
saturated
→ nonsaturated positive
→ positive pressure
```

へ落ちる。

したがって saturated branch 自体は閉じたと見てよい。

---

## 4. Packing bound の意味

有限区間 $[q,m]$ の saturated indices を $S$ とすると、

$$
2|S|\le m-q+2
$$

が証明された。

閉区間の block 数を、

$$
N=m-q+1
$$

とすれば、

$$
2|S|\le N+1
$$

じゃ。

これは孤立点集合に対する正確な packing bound である。

ただし、これだけでは saturated surcharge の総量は一様有界にならない。

最大でも半密度というだけなので、区間長が増えれば、

$$
|S|=O(N)
$$

は許される。

よって saturated の孤立性は重要だが、それだけで queue bound にはならない。

---

## 5. 動的 pressure 深度の問題点

現在の定義は、non-saturated かつ terminal valuation $v=1$ の場合に、

$$
d=0
$$

を選んでいる。

depth $0$ では、

$$
\#\operatorname{Recovery}(0)=0
$$

$$
\#\operatorname{Continuation}(0)=L
$$

なので、

$$
M_0=L
$$

となる。

確かに、

$$
D\le L
$$

なので数値上の domination は成立する。

しかし depth $0$ は、

> 全 source が自動的に continuation になる基底層

であり、実質的な pressure obstruction ではない。

これは既存の `PressureFrontier`・`PressureBeam`・NoLift 層へ渡すには粗すぎる。

現在の総和 theorem は正しいが、その $v=1$ branch は、

> pressure theorem というより block-length upper bound

になっている。

したがって `dynamic pressure sum is closed` という表現には、

> depth-zero を許した粗い scalar upper bound として閉じた

という限定が必要じゃ。

---

## 6. 一歩先の重要定理：positive full-claim は saturated だけ

現在の theorem 群から、さらに次が証明できると見える。

$$
0<D_k \land A_k=L_k \Longleftrightarrow \operatorname{Saturated}(k)
$$

逆向きは既に自明じゃ。

問題は、

$$
0<D,\qquad A=L
$$

から saturated を出す方向。

この場合、

$$
D=L-v
$$

である。

exact ledger より、

$$
\operatorname{bitWidth}(x') = \operatorname{bitWidth}(x)+(L-v)
$$

となる。

したがって、

$$
2^{L-v-1}x<x'
$$

でなければならない。

一方、normal form は、

$$
x=2^Lu-1
$$

$$
x'=\frac{3^Lu-1}{2^v}
$$

じゃ。

$L\ge3$ について、少し強い指数不等式、

$$
3^L+2^{L-1}\le2^{2L-1}
$$

を使うと、

$$
x'<2^{L-v-1}x
$$

が得られる。

矛盾じゃ。

よって $L\le2$。

正 drift と $1\le v<L$ より、

$$
L=2,\qquad v=1
$$

となり、full claim と合わせて saturated になる。

この theorem は極めて重要じゃ。

---

## 7. depth $0$ を完全に除去できる

前節が閉じれば、positive non-saturated block では、

$$
A<L
$$

である。

terminal valuation $v=1$ の場合、

$$
D=A-1
$$

じゃ。

$A<L$ より、

$$
A\le L-1
$$

だから、

$$
D\le L-2
$$

となる。

一方、depth $1$ の pressure は、

$$
M_1=L-2
$$

じゃ。

したがって、

$$
D\le M_1
$$

が得られる。

よって refined dynamic depth は、

$$
d_k=
\begin{cases}
1&v_k=1\\
v_k-1&2\le v_k
\end{cases}
$$

でよい。

saturated の場合だけ、

$$
D=1,\qquad M_1=0
$$

なので unit surcharge を足す。

最終的に、全 positive block について、

$$
D_k \le M_k(d_k)+\mathbf1_{\operatorname{Saturated}(k)}
$$

となる。

しかも常に、

$$
1\le d_k
$$

じゃ。

これで dynamic pressure は、本物の正 depth pressure だけになる。

---

## 8. Pressure contribution は実際の carrier にできる

正 depth $d$ かつ $d<L$ なら、

$$
M_d=L-d-1
$$

である。

一方、

$$
\left|\operatorname{ContinuationFiber}(d+1)\right|=\#L-(d+1)=L-d-1
$$

じゃ。

したがって、

$$
\boxed{M_d = \left|\operatorname{ContinuationFiber}(d+1)\right|}
$$

となる。

つまり pressure contribution を signed difference のまま持つ必要はない。

実際の有限集合、

```lean
canonicalSelectedPressureCarrier n k :=
  canonicalPaymentBlockContinuationFiber n k
    (canonicalSelectedPositivePressureDepth n k + 1)
```

として持てる。

- saturated なら carrier は空で unit surcharge が一件
- non-saturated positive なら carrier cardinality が drift を支配

となる。

---

## 9. 異なる block の pressure carrier は重ならない

各 selected pressure carrier は、

$$
\operatorname{Carrier}_k\subseteq B_k
$$

である。

canonical blocks は全時刻を一意分割するので、

$$
k\ne\ell \Longrightarrow B_k\cap B_\ell=\varnothing
$$

じゃ。

よって、

$$
\operatorname{Carrier}*k \cap \operatorname{Carrier}*\ell = \varnothing
$$

となる。

したがって report の、

> different `(block, depth)` pressure witnesses may overlap the same continuation resources

という懸念は、**source-time continuation incidence の意味では既に解消可能**じゃ。

有限区間では、

$$
\left|\bigsqcup_k\operatorname{Carrier}_k\right| = \sum_k|\operatorname{Carrier}_k|
$$

を証明できる。

ここには multiplicity correction は不要である。

---

## 10. 本当の未証明事項

重複が問題になる可能性があるのは、その先じゃ。

selected pressure carrier の source incidence を、

```text
future endpoint capacity slot
upper-zero boundary unit
NoLift obstruction
pressure separator
```

へ写すとき、その像が重なるかもしれない。

現在は、そもそもその輸送写像が存在しない。

したがって真の障害は、

> pressure carrier の disjointness

ではなく、

> **pressure carrier から大域有限資源への寄与保存輸送**

じゃ。

pressure は「支払い資源」そのものでもない。

むしろ、

> positive drift が存在するために消費された bad-structure incidence

と読む方が正確である。

---

## 11. cp-319 の最終的な位置

現在、positive drift は次まで圧縮された。

```text
positive block
  ├─ genuine positive-depth pressure carrier
  └─ isolated saturated unit
```

さらに pressure carriers は block 間で disjoint にできる。

よって open excursion の正 drift 全体は、

$$
\text{disjoint pressure incidences} + \text{isolated saturated tokens}
$$

へ落ちる。

ここまで来れば次の問いは一つじゃ。

> この異なる incidence を、有限開始値のどの有限資源が支えているのか。

最有力候補は、以前から見えている eventually-zero upper-bit boundary じゃ。

---

## 判定まとめ

### Saturated length / valuation / residue

**完成。**

### No consecutive saturation

**完成。**

### Saturated successor grammar

**完成。**

### Positive/saturated finite partition

**完成。**

### Dynamic numerical aggregation

**完成。ただし depth $0$ branch は粗い。**

### Pressure incidence disjointness

**未実装だが canonical block partition から閉じられる。**

### 真の障害

**disjoint pressure incidence を有限大域資源へ輸送する theorem。**

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge Float-window branch after
report-petal-319.

The cp-319 implementation is accepted.

Saturation is now completely rigid:

    length = 2
    terminal valuation = 1
    no consecutive saturated blocks
    saturated successor = nonpositive or positive pressure

However, revise the reported obstruction.

Selected pressure source incidences from different canonical blocks do not
overlap: every local continuation fiber is contained in its unique canonical
block, and canonical blocks partition orbit time.

The genuine missing theorem is not source-incidence disjointness. It is a
contribution-preserving transport from those disjoint incidences to a globally
bounded resource or obstruction.

Before attacking that transport, eliminate the current depth-zero branch.

# Stage A — positive full claims imply saturation

Prove the strengthened exponential inequality:

    3 <= L ->
    3^L + 2^(L - 1) <= 2^(2*L - 1)

Use induction from:

    27 + 4 <= 32.

Then prove:

    0 < endpointAccountingTerm n k
      ->
    canonicalBlockClaimCount n k = canonicalBlockLength n k
      ->
    CanonicalSaturatedBorderBlock n k

Suggested proof:

    D = L - v
    bitWidth(nextStart) = bitWidth(start) + D

For `3 <= L`, the normal form and the strengthened exponential inequality
give:

    nextStart < 2^(D - 1) * start

while the bit-width increase gives:

    2^(D - 1) * start < nextStart.

Conclude `L = 2`, then `v = 1`, hence saturation.

Export the clean equivalence:

    CanonicalSaturatedBorderBlock n k
      <->
    0 < endpointAccountingTerm n k
      ∧
    canonicalBlockClaimCount n k = canonicalBlockLength n k

# Stage B — eliminate depth zero

Define a refined positive pressure depth:

    canonicalSelectedPositivePressureDepth n k :=
      if canonicalBlockTerminalValuation n k = 1 then
        1
      else
        canonicalBlockTerminalValuation n k - 1

Prove:

    1 <= canonicalSelectedPositivePressureDepth n k

For a positive nonsaturated block prove:

    endpointAccountingTerm n k
      <=
    blockPressureContributionInt n k
      (canonicalSelectedPositivePressureDepth n k)

The `v >= 2` branch already exists.

For `v = 1`, use Stage A:

    nonsaturated -> claimCount < length

and derive:

    drift = claimCount - 1
      <= length - 2
      = pressure at depth 1.

For saturated blocks retain the exact unit surcharge:

    drift = pressure at depth 1 + 1.

Then prove the refined pointwise theorem:

    positive drift
      <=
    selected positive-depth pressure
      + saturated unit.

Do not use pressure depth zero in this refined API.

Keep the old depth-zero definition only as a deprecated coarse compatibility
surface if existing code depends on it.

# Stage C — pressure as an actual carrier

For `1 <= d` and `d < blockLength`, prove:

    blockPressureContributionInt n k d
      =
    card (canonicalPaymentBlockContinuationFiber n k (d + 1))

with the appropriate `Int` cast.

Define:

    canonicalSelectedPressureCarrier n k :=
      canonicalPaymentBlockContinuationFiber n k
        (canonicalSelectedPositivePressureDepth n k + 1)

For every positive nonsaturated block prove:

    card selectedPressureCarrier
      =
    selected pressure contribution

and:

    endpointAccountingTerm
      <=
    card selectedPressureCarrier.

For saturated blocks prove that the selected carrier is empty and the
saturated unit is exactly one.

# Stage D — pairwise disjoint source incidence

Prove canonical block disjointness explicitly:

    k != l ->
    Disjoint (canonicalPaymentBlock n k)
      (canonicalPaymentBlock n l)

Use `existsUnique_mem_canonicalPaymentBlock`.

Then derive:

    k != l ->
    Disjoint (canonicalSelectedPressureCarrier n k)
      (canonicalSelectedPressureCarrier n l).

Define the finite global carrier over `q..m` as a sigma type or disjoint union.

Prove its cardinality is exactly the sum of the selected local carrier cards.

This closes source-incidence multiplicity completely.

# Stage E — finite positive-drift unit embedding

Define anonymous positive-drift unit carriers:

    Fin (Int.toNat (endpointAccountingTerm n k))

for positive blocks.

Construct a finite injection from all positive-drift units in `q..m` into:

    global selected pressure carrier
      ⊕
    saturated block indices.

This may use finite-cardinality existence after the exact inequalities are
proved.

Document carefully:

    this is an incidence certificate,
    not a future payment allocation.

# Stage F — open-excursion carrier theorem

For an open positive excursion `q..m`, prove:

    sum positive drift
      <=
    card global selected pressure carrier
      + card saturated indices.

Then combine the existing saturation packing theorem to expose:

    sum positive drift
      <=
    card global selected pressure carrier
      + (excursion length + 1) / 2

in a convenient Nat/Int form.

Do not interpret this as a uniform bound.

# Stage G — depth buckets

Define the selected blocks at a fixed selected depth:

    canonicalSelectedPressureBlocksAtDepth n q m d.

Partition the global carrier by depth and prove a finite Fubini identity:

    global carrier card
      =
    sum d in finiteDepthSupport,
      card carrier bucket at d.

For each fixed `d`, show that the bucket carrier is a subset of the union of
the canonical continuation fibers at depth `d + 1`.

Connect this to the existing endpoint-aligned continuation-count theorem.

This is the honest bridge from dynamic depths to the fixed-depth pressure API.

# Stage H — existing pressure infrastructure audit

For each fixed depth bucket, inspect whether the existing:

    PressureFrontier
    PressureAccounting
    PressureBeam
    PressureState.FiniteWindowPacking
    PressureLocalWitnessObstruction

can bound:

    number of carrier incidences,
    number of positive blocks,
    or number of separated pressure pulses.

Do not treat a positive pressure contribution as a payment slot.

The target is one of:

    every carrier incidence consumes a distinct finite boundary resource;

    every sufficiently large bucket creates a pressure separator;

    every unbounded bucket creates a NoLift obstruction;

    every long open excursion forces a fixed-depth pulse family violating
      finite-window packing.

# Stage I — saturated token transport

Keep saturated tokens separate.

Audit the exact successor branches:

    core mod 8 = 3 -> next block length 1
    core mod 8 = 7 -> next block length >= 2.

Seek a theorem that charges each isolated saturated token to exactly one of:

    a later negative drift unit,
    a distinct selected pressure incidence,
    a distinct upper-zero boundary unit.

Do not infer repayment merely from nonpositive successor drift; zero drift
does not repay the saturated unit.

# Stage J — upper-boundary resource candidate

Define an experimental finite carrier for the eventually-zero upper-bit
boundary of the initial natural number.

Investigate whether every selected pressure incidence or saturated token can be
assigned to a distinct boundary unit, or whether a boundary unit can be reused
with a uniformly bounded multiplicity.

Do not assert the global injection before exact bit-position preservation is
proved.

# Stage K — stopping rule

Stop at the first genuine obstruction among:

    positive full-claim blocks do not reduce to saturation
    positive-depth refinement fails
    selected pressure carriers are not block-disjoint
    fixed-depth pressure buckets cannot enter existing pressure APIs
    saturated tokens have no structurally identifiable charge
    upper-boundary units can be reused without a uniform multiplicity bound.

Do not return to scalar queue algebra or coarse depth-zero pressure.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-320.md
```

うむ。

cp-319 で saturated は退治された。

次は pressure を数値ではなく、**重ならない実在 incidence** に変える番じゃ。
そこまで閉じれば、最後に問うべきものは「その incidence が有限開始境界を何個消費するか」だけになる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
index 5913925e..a23b64b0 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
@@ -22,6 +22,7 @@ import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentScalarQueue
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlockNormalForm
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPositiveBlock
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPrimitiveExcursion
+import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentSaturatedSuccessor
 import DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition

 #print "file: DkMath.Collatz.PetalBridge.FloatWindow"
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentPositiveBlock.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentPositiveBlock.lean
index 19e4df13..f1f0d6ad 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentPositiveBlock.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentPositiveBlock.lean
@@ -436,17 +436,13 @@ does **not** export

 `saturated block -> next block has nonpositive drift`.

-The length-two and no-consecutive-saturation patterns remain finite evidence,
-not theorems.  The exact facts proved above stop at the normal form
-
-`x + 1 = 2^L * u` and `v2 (3^L * u - 1) = L - 1`.
-
-To pass this stopping point, a new arithmetic theorem must constrain the next
-canonical block from that normal form, or rule out `L > 2` by combining all
-carry-two inequalities across the exact recurrence.  Existing tail-grammar,
-drift-budget, and delayed-reservoir APIs do not currently accept enough of this
-block-local data to prove either statement.  Adding a successor theorem from
-the finite pattern alone would therefore be an unsound strengthening.
+The former stopping point has since been crossed in
+`UniversalPaymentSaturatedSuccessor`.  The exact normal form and signed width
+ledger prove that saturation has length two and that saturated blocks cannot
+be consecutive.  That module also replaces the false unconditional successor
+rule by the exact disjunction: the successor has nonpositive drift or positive
+terminal-depth pressure.  The audit remains useful as evidence, but these two
+structural facts no longer depend on it.
 -/

 /-- The non-saturated positive branch carries its dynamic terminal pressure depth. -/
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentSaturatedSuccessor.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentSaturatedSuccessor.lean
new file mode 100644
index 00000000..94626a32
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentSaturatedSuccessor.lean
@@ -0,0 +1,706 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPrimitiveExcursion
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentSaturatedSuccessor"
+
+namespace DkMath.Collatz
+
+/-!
+# Saturated canonical blocks and their successors
+
+This module replaces the finite cp-318 saturation observations by exact
+arithmetic wherever possible.  The key input is not the audit: it is the
+combination of the canonical block normal form with the signed width ledger.
+-/
+
+/-! ## Minimal saturation surface -/
+
+/-- The unit-drift field of saturation follows from length and complete claims. -/
+theorem canonicalSaturatedBorderBlock_iff_length_and_claims
+    (n : OddNat) (k : ℕ) :
+    CanonicalSaturatedBorderBlock n k ↔
+      canonicalBlockLength n k = canonicalBlockTerminalValuation n k + 1 ∧
+        canonicalBlockClaimCount n k = canonicalBlockLength n k := by
+  constructor
+  · intro h
+    exact ⟨h.1, h.2.1⟩
+  · rintro ⟨hlength, hclaims⟩
+    refine ⟨hlength, hclaims, ?_⟩
+    rw [endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount,
+      canonicalBlockCapacityCount_eq_terminalValuation, hclaims, hlength]
+    norm_num
+
+/-- Saturated pressure is exactly zero at the terminal valuation depth. -/
+theorem CanonicalSaturatedBorderBlock.pressure_eq_zero
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
+    blockPressureContributionInt n k (canonicalBlockTerminalValuation n k) = 0 := by
+  have hvpos : 1 ≤ canonicalBlockTerminalValuation n k := by
+    have hheight := two_le_orbitWindowHeight_paymentEndpointSeq n k
+    rw [canonicalBlock_endpointHeight_eq_terminalValuation_add_one] at hheight
+    omega
+  apply blockPressureContributionInt_eq_zero_of_length_eq_succ hvpos
+  simpa [canonicalBlockLength] using h.1
+
+/-! ## Exponential comparison -/
+
+/-- From length three onward, `3^L` lies below the relevant dyadic scale. -/
+theorem three_pow_lt_two_pow_two_mul_sub_one {L : ℕ} (hL : 3 ≤ L) :
+    3 ^ L < 2 ^ (2 * L - 1) := by
+  induction L, hL using Nat.le_induction with
+  | base => norm_num
+  | succ L hL ih =>
+      have hexp : 2 * (L + 1) - 1 = (2 * L - 1) + 2 := by omega
+      rw [pow_succ, hexp, pow_add]
+      have hpos : 0 < 2 ^ (2 * L - 1) := pow_pos (by norm_num) _
+      nlinarith
+
+/-- Multiplication by a positive core preserves the exponential comparison. -/
+theorem three_pow_mul_lt_two_pow_two_mul_sub_one_mul
+    {L u : ℕ} (hL : 3 ≤ L) (hu : 0 < u) :
+    3 ^ L * u < 2 ^ (2 * L - 1) * u := by
+  exact (Nat.mul_lt_mul_right hu).2 (three_pow_lt_two_pow_two_mul_sub_one hL)
+
+/-- Binary width is monotone on positive natural words. -/
+private theorem bitWidth_mono_of_pos {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
+    bitWidth a ≤ bitWidth b := by
+  have hb : 0 < b := ha.trans_le hab
+  rw [bitWidth_eq_log_two_add_one ha.ne', bitWidth_eq_log_two_add_one hb.ne']
+  exact Nat.add_le_add_right (Nat.log_mono_right hab) 1
+
+/-! ## Saturated length -/
+
+/-- Unit saturated drift is exact one-bit growth from block start to next start. -/
+theorem CanonicalSaturatedBorderBlock.nextStart_bitWidth_eq_start_add_one
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
+    bitWidth (canonicalBlockNextStartState n k) =
+      bitWidth (canonicalBlockStartState n k) + 1 := by
+  have hdrift := universalPaymentBlockSignedDriftAt_eq_bitWidth_sub n
+    (paymentEndpointSeq n k)
+    (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)
+  rw [← endpointAccountingTerm_eq_universalPaymentBlockSignedDriftAt, h.2.2] at hdrift
+  unfold canonicalBlockNextStartState canonicalBlockStartState
+  rw [canonicalBlockStartTime_eq_universalPaymentBlockStart]
+  omega
+
+/-- Length at least three would make the next start no larger than the old start. -/
+theorem CanonicalSaturatedBorderBlock.nextStart_lt_start_add_one_of_three_le_length
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
+    (hL : 3 ≤ canonicalBlockLength n k) :
+    canonicalBlockNextStartState n k < canonicalBlockStartState n k + 1 := by
+  have hcore := canonicalBlockOddCore_pos n k
+  have hpow := three_pow_mul_lt_two_pow_two_mul_sub_one_mul hL hcore
+  rw [canonicalBlockNextStartState_eq_terminalCarrier_div_pow_valuation,
+    h.terminalValuation_eq_length_sub_one]
+  apply (Nat.div_lt_iff_lt_mul (pow_pos (by norm_num)
+    (canonicalBlockLength n k - 1))).2
+  rw [h.normalForm.1]
+  calc
+    canonicalBlockTerminalCarrier n k
+        ≤ 3 ^ canonicalBlockLength n k * canonicalBlockOddCore n k := by
+          unfold canonicalBlockTerminalCarrier
+          omega
+    _ < 2 ^ (2 * canonicalBlockLength n k - 1) *
+          canonicalBlockOddCore n k := hpow
+    _ = (2 ^ canonicalBlockLength n k * canonicalBlockOddCore n k) *
+          2 ^ (canonicalBlockLength n k - 1) := by
+          have hexp : 2 * canonicalBlockLength n k - 1 =
+              canonicalBlockLength n k + (canonicalBlockLength n k - 1) := by
+            omega
+          rw [hexp, pow_add]
+          ring
+
+/-- Every saturated canonical block has length exactly two. -/
+theorem CanonicalSaturatedBorderBlock.length_eq_two
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
+    canonicalBlockLength n k = 2 := by
+  have hvpos : 1 ≤ canonicalBlockTerminalValuation n k := by
+    have hheight := two_le_orbitWindowHeight_paymentEndpointSeq n k
+    rw [canonicalBlock_endpointHeight_eq_terminalValuation_add_one] at hheight
+    omega
+  have hLtwo : 2 ≤ canonicalBlockLength n k := by
+    rw [h.1]
+    omega
+  by_contra hne
+  have hLthree : 3 ≤ canonicalBlockLength n k := by omega
+  have hnextLe : canonicalBlockNextStartState n k ≤ canonicalBlockStartState n k := by
+    have := h.nextStart_lt_start_add_one_of_three_le_length hLthree
+    omega
+  have hnextPos : 0 < canonicalBlockNextStartState n k := by
+    unfold canonicalBlockNextStartState
+    have hodd := (iterateT (paymentEndpointSeq n k + 1) n).2
+    omega
+  have hwidthLe : bitWidth (canonicalBlockNextStartState n k) ≤
+      bitWidth (canonicalBlockStartState n k) :=
+    bitWidth_mono_of_pos hnextPos hnextLe
+  rw [h.nextStart_bitWidth_eq_start_add_one] at hwidthLe
+  omega
+
+/-- Saturated terminal valuation is one. -/
+theorem CanonicalSaturatedBorderBlock.terminalValuation_eq_one
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
+    canonicalBlockTerminalValuation n k = 1 := by
+  have hval := h.terminalValuation_eq_length_sub_one
+  rw [h.length_eq_two] at hval
+  exact hval
+
+/-- Saturated endpoint height is two. -/
+theorem CanonicalSaturatedBorderBlock.endpointHeight_eq_two
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
+    orbitWindowHeight n (paymentEndpointSeq n k) = 2 := by
+  rw [h.endpointHeight_eq_length, h.length_eq_two]
+
+/-! ## Exact length-two normal form -/
+
+/-- Saturated start state is one below four times its odd core. -/
+theorem CanonicalSaturatedBorderBlock.startState_eq_four_mul_core_sub_one
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
+    canonicalBlockStartState n k = 4 * canonicalBlockOddCore n k - 1 := by
+  have hnormal := h.normalForm.1
+  rw [h.length_eq_two] at hnormal
+  norm_num at hnormal ⊢
+  omega
+
+/-- Saturated next start has the exact length-two quotient form. -/
+theorem CanonicalSaturatedBorderBlock.nextStartState_eq
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
+    canonicalBlockNextStartState n k =
+      (9 * canonicalBlockOddCore n k - 1) / 2 := by
+  rw [canonicalBlockNextStartState_eq_terminalCarrier_div_pow_valuation,
+    h.terminalValuation_eq_one]
+  unfold canonicalBlockTerminalCarrier
+  rw [h.length_eq_two]
+  norm_num
+
+/-- The length-two terminal carrier has exact two-adic valuation one. -/
+theorem CanonicalSaturatedBorderBlock.v2_nine_mul_core_sub_one_eq_one
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
+    v2 (9 * canonicalBlockOddCore n k - 1) = 1 := by
+  have hnormal := h.normalForm.2
+  rw [h.length_eq_two] at hnormal
+  norm_num at hnormal ⊢
+  exact hnormal
+
+/-- A saturated odd core is exactly in residue class three modulo four. -/
+theorem CanonicalSaturatedBorderBlock.oddCore_mod_four_eq_three
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
+    canonicalBlockOddCore n k % 4 = 3 := by
+  have hnot : ¬ 4 ∣ 9 * canonicalBlockOddCore n k - 1 := by
+    have hraw := h.not_pow_length_dvd_terminalCarrier
+    rw [h.length_eq_two] at hraw
+    simpa [canonicalBlockTerminalCarrier, h.length_eq_two] using hraw
+  rcases odd_mod_four_eq_one_or_three
+      (canonicalBlockOddCore_mod_two_eq_one n k) with hone | hthree
+  · exfalso
+    apply hnot
+    rw [Nat.dvd_iff_mod_eq_zero]
+    omega
+  · exact hthree
+
+/-- The mod-eight refinement leaves exactly the observed classes three and seven. -/
+theorem CanonicalSaturatedBorderBlock.oddCore_mod_eight_eq_three_or_seven
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
+    canonicalBlockOddCore n k % 8 = 3 ∨
+      canonicalBlockOddCore n k % 8 = 7 := by
+  rcases odd_mod_eight_eq_one_or_three_or_five_or_seven
+      (canonicalBlockOddCore_mod_two_eq_one n k) with
+    hone | hthree | hfive | hseven
+  · have := h.oddCore_mod_four_eq_three
+    omega
+  · exact Or.inl hthree
+  · have := h.oddCore_mod_four_eq_three
+    omega
+  · exact Or.inr hseven
+
+/-! ## No consecutive saturated blocks -/
+
+/-- The next canonical block starts at the state produced by the current block. -/
+theorem canonicalBlockStartState_succ_eq_nextStartState
+    (n : OddNat) (k : ℕ) :
+    canonicalBlockStartState n (k + 1) = canonicalBlockNextStartState n k := by
+  unfold canonicalBlockStartState canonicalBlockNextStartState
+  rw [canonicalBlockStartTime_eq_universalPaymentBlockStart,
+    universalPaymentBlockStart_paymentEndpointSeq_succ]
+
+/-- A two-bit width increase forces more than a doubling of positive words. -/
+private theorem two_mul_lt_of_bitWidth_eq_add_two
+    {x y : ℕ} (hx : 0 < x) (hy : 0 < y)
+    (hwidth : bitWidth y = bitWidth x + 2) :
+    2 * x < y := by
+  have hxlt := lt_pow_bitWidth hx
+  have hylead := pow_bitWidth_sub_one_le hy
+  have hpow : 2 ^ (bitWidth x + 1) ≤ y := by
+    rw [hwidth] at hylead
+    simpa using hylead
+  calc
+    2 * x < 2 * 2 ^ bitWidth x :=
+      (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).2 hxlt
+    _ = 2 ^ (bitWidth x + 1) := by rw [pow_succ]; ring
+    _ ≤ y := hpow
+
+/-- Saturated blocks cannot occur at consecutive canonical indices. -/
+theorem CanonicalSaturatedBorderBlock.not_succ
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
+    ¬ CanonicalSaturatedBorderBlock n (k + 1) := by
+  intro hnext
+  let u := canonicalBlockOddCore n k
+  let u' := canonicalBlockOddCore n (k + 1)
+  let x₀ := canonicalBlockStartState n k
+  let x₁ := canonicalBlockNextStartState n k
+  let x₂ := canonicalBlockNextStartState n (k + 1)
+  have hu : 0 < u := canonicalBlockOddCore_pos n k
+  have hx₀ : x₀ = 4 * u - 1 := h.startState_eq_four_mul_core_sub_one
+  have hx₁ : x₁ = (9 * u - 1) / 2 := h.nextStartState_eq
+  have hstart₁ : canonicalBlockStartState n (k + 1) = x₁ :=
+    canonicalBlockStartState_succ_eq_nextStartState n k
+  have hstart₁core : canonicalBlockStartState n (k + 1) = 4 * u' - 1 :=
+    hnext.startState_eq_four_mul_core_sub_one
+  have hx₂ : x₂ = (9 * u' - 1) / 2 := hnext.nextStartState_eq
+  have hdvd₁ : 2 ∣ 9 * u - 1 := by
+    have hdvd := h.pow_length_sub_one_dvd_terminalCarrier
+    simpa [u, canonicalBlockTerminalCarrier, h.length_eq_two] using hdvd
+  have hdvd₂ : 2 ∣ 9 * u' - 1 := by
+    have hdvd := hnext.pow_length_sub_one_dvd_terminalCarrier
+    simpa [u', canonicalBlockTerminalCarrier, hnext.length_eq_two] using hdvd
+  have hdouble₁ : 2 * x₁ = 9 * u - 1 := by
+    rw [hx₁]
+    have := Nat.div_mul_cancel hdvd₁
+    omega
+  have hdouble₂ : 2 * x₂ = 9 * u' - 1 := by
+    rw [hx₂]
+    have := Nat.div_mul_cancel hdvd₂
+    omega
+  have hu' : 8 * u' = 9 * u + 1 := by
+    omega
+  have hx₂closed : 16 * x₂ = 81 * u + 1 := by
+    omega
+  have hx₂lt : x₂ < 2 * x₀ := by
+    omega
+  have hx₀pos : 0 < x₀ := by omega
+  have hx₂pos : 0 < x₂ := by
+    unfold x₂ canonicalBlockNextStartState
+    have hodd := (iterateT (paymentEndpointSeq n (k + 1) + 1) n).2
+    omega
+  have hwidth₁ := h.nextStart_bitWidth_eq_start_add_one
+  have hwidth₂ := hnext.nextStart_bitWidth_eq_start_add_one
+  have hwidth : bitWidth x₂ = bitWidth x₀ + 2 := by
+    change bitWidth x₁ = bitWidth x₀ + 1 at hwidth₁
+    change bitWidth x₂ = bitWidth (canonicalBlockStartState n (k + 1)) + 1 at hwidth₂
+    rw [hstart₁] at hwidth₂
+    omega
+  have hx₂gt : 2 * x₀ < x₂ :=
+    two_mul_lt_of_bitWidth_eq_add_two hx₀pos hx₂pos hwidth
+  omega
+
+/-! ## Correct saturated-successor pressure theorem -/
+
+/-- A saturated block is followed by nonpositive drift or positive pressure. -/
+theorem CanonicalSaturatedBorderBlock.successor_nonpos_or_pressure_pos
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
+    endpointAccountingTerm n (k + 1) ≤ 0 ∨
+      0 < blockPressureContributionInt n (k + 1)
+        (canonicalBlockTerminalValuation n (k + 1)) := by
+  by_cases hpos : 0 < endpointAccountingTerm n (k + 1)
+  · right
+    rcases positive_blockPressure_or_saturatedBorder_of_endpointAccountingTerm_pos
+      hpos with hpressure | hsaturated
+    · exact hpressure
+    · exact (h.not_succ hsaturated).elim
+  · exact Or.inl (by omega)
+
+/-! ## Sharper pressure depth -/
+
+/-- Positive drift is dominated by pressure one level before a terminal
+valuation of at least two.  At that depth the pressure is exactly `L - v`,
+the same universal upper bound supplied by the endpoint ledger. -/
+theorem endpointAccountingTerm_le_blockPressure_pred_terminal
+    {n : OddNat} {k : ℕ}
+    (hpos : 0 < endpointAccountingTerm n k)
+    (hv : 2 ≤ canonicalBlockTerminalValuation n k) :
+    endpointAccountingTerm n k ≤
+      blockPressureContributionInt n k
+        (canonicalBlockTerminalValuation n k - 1) := by
+  let v := canonicalBlockTerminalValuation n k
+  let L := canonicalBlockLength n k
+  have hvlt : v < L :=
+    canonicalBlockTerminalValuation_lt_length_of_endpointAccountingTerm_pos hpos
+  have hdrift := endpointAccountingTerm_le_length_sub_capacity n k
+  rw [canonicalBlockCapacityCount_eq_terminalValuation] at hdrift
+  have hpressure :=
+    blockPressureContributionInt_eq_sub_sub_one_of_add_two_le_length
+      (n := n) (k := k) (d := v - 1) (by omega) (by
+        change v - 1 + 2 ≤ L
+        omega)
+  have hpressureExact :
+      blockPressureContributionInt n k (v - 1) = (L : ℤ) - v := by
+    rw [hpressure]
+    change ((L - (v - 1) : ℕ) : ℤ) - 1 = (L : ℤ) - v
+    omega
+  rw [hpressureExact]
+  exact hdrift
+
+/-- At terminal valuation one, positive length-two blocks are precisely the
+saturated border blocks; every nonsaturated alternative has length at least
+three and positive pressure at depth one. -/
+theorem positive_terminalValuation_one_saturated_or_length_three_pressure
+    {n : OddNat} {k : ℕ}
+    (hpos : 0 < endpointAccountingTerm n k)
+    (hv : canonicalBlockTerminalValuation n k = 1) :
+    CanonicalSaturatedBorderBlock n k ∨
+      (3 ≤ canonicalBlockLength n k ∧
+        0 < blockPressureContributionInt n k 1) := by
+  rcases positive_blockPressure_or_saturatedBorder_of_endpointAccountingTerm_pos
+      hpos with hpressure | hsaturated
+  · right
+    constructor
+    · have hvlt :=
+        canonicalBlockTerminalValuation_lt_length_of_endpointAccountingTerm_pos hpos
+      by_contra hL
+      have hLtwo : canonicalBlockLength n k = 2 := by omega
+      have hclaimLe := canonicalBlockClaimCount_le_length n k
+      have hdrift := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount n k
+      rw [canonicalBlockCapacityCount_eq_terminalValuation, hv] at hdrift
+      rw [hLtwo] at hclaimLe
+      have hclaims : canonicalBlockClaimCount n k = 2 := by omega
+      have hsaturated : CanonicalSaturatedBorderBlock n k :=
+        (canonicalSaturatedBorderBlock_iff_length_and_claims n k).2
+          ⟨by omega, by simpa [hLtwo] using hclaims⟩
+      rw [hsaturated.pressure_eq_zero] at hpressure
+      omega
+    · simpa [hv] using hpressure
+  · exact Or.inl hsaturated
+
+/-! ## Finite saturated sets and open-excursion decomposition -/
+
+/-- Actual saturated canonical indices in the closed block interval `q..m`. -/
+noncomputable def canonicalSaturatedBlockIndices
+    (n : OddNat) (q m : ℕ) : Finset ℕ := by
+  classical
+  exact (Finset.Icc q m).filter (CanonicalSaturatedBorderBlock n)
+
+/-- Positive-pressure canonical indices in the closed block interval `q..m`. -/
+noncomputable def canonicalPositivePressureBlockIndices
+    (n : OddNat) (q m : ℕ) : Finset ℕ :=
+  (Finset.Icc q m).filter fun k =>
+    0 < endpointAccountingTerm n k ∧
+      0 < blockPressureContributionInt n k
+        (canonicalBlockTerminalValuation n k)
+
+/-- Nonpositive-drift canonical indices in the closed block interval `q..m`. -/
+noncomputable def canonicalNonpositiveBlockIndices
+    (n : OddNat) (q m : ℕ) : Finset ℕ :=
+  (Finset.Icc q m).filter fun k => endpointAccountingTerm n k ≤ 0
+
+@[simp] theorem mem_canonicalSaturatedBlockIndices
+    {n : OddNat} {q m k : ℕ} :
+    k ∈ canonicalSaturatedBlockIndices n q m ↔
+      k ∈ Finset.Icc q m ∧ CanonicalSaturatedBorderBlock n k := by
+  simp [canonicalSaturatedBlockIndices]
+
+@[simp] theorem mem_canonicalPositivePressureBlockIndices
+    {n : OddNat} {q m k : ℕ} :
+    k ∈ canonicalPositivePressureBlockIndices n q m ↔
+      k ∈ Finset.Icc q m ∧ 0 < endpointAccountingTerm n k ∧
+        0 < blockPressureContributionInt n k
+          (canonicalBlockTerminalValuation n k) := by
+  simp [canonicalPositivePressureBlockIndices]
+
+@[simp] theorem mem_canonicalNonpositiveBlockIndices
+    {n : OddNat} {q m k : ℕ} :
+    k ∈ canonicalNonpositiveBlockIndices n q m ↔
+      k ∈ Finset.Icc q m ∧ endpointAccountingTerm n k ≤ 0 := by
+  simp [canonicalNonpositiveBlockIndices]
+
+/-- Saturated membership excludes membership of the immediate successor. -/
+theorem canonicalSaturatedBlockIndices_not_succ_mem
+    {n : OddNat} {q m k : ℕ}
+    (hk : k ∈ canonicalSaturatedBlockIndices n q m) :
+    k + 1 ∉ canonicalSaturatedBlockIndices n q m := by
+  intro hsucc
+  exact (mem_canonicalSaturatedBlockIndices.mp hk).2.not_succ
+    (mem_canonicalSaturatedBlockIndices.mp hsucc).2
+
+/-- Isolated saturation occupies at most every other slot of a finite interval. -/
+theorem two_mul_card_canonicalSaturatedBlockIndices_le
+    (n : OddNat) (q m : ℕ) :
+    2 * (canonicalSaturatedBlockIndices n q m).card ≤ m - q + 2 := by
+  classical
+  let S := canonicalSaturatedBlockIndices n q m
+  let T := S.image fun k => k + 1
+  have hdisjoint : Disjoint S T := by
+    rw [Finset.disjoint_left]
+    intro x hxS hxT
+    rcases Finset.mem_image.mp hxT with ⟨k, hkS, hkx⟩
+    subst x
+    exact canonicalSaturatedBlockIndices_not_succ_mem hkS hxS
+  have hsubset : S ∪ T ⊆ Finset.Icc q (m + 1) := by
+    intro x hx
+    rcases Finset.mem_union.mp hx with hxS | hxT
+    · change x ∈ canonicalSaturatedBlockIndices n q m at hxS
+      have hxIcc := (mem_canonicalSaturatedBlockIndices.mp hxS).1
+      simp only [Finset.mem_Icc] at hxIcc
+      rcases hxIcc with ⟨hqx, hxm⟩
+      exact Finset.mem_Icc.mpr ⟨hqx, by omega⟩
+    · rcases Finset.mem_image.mp hxT with ⟨k, hkS, rfl⟩
+      change k ∈ canonicalSaturatedBlockIndices n q m at hkS
+      have hkIcc := (mem_canonicalSaturatedBlockIndices.mp hkS).1
+      simp only [Finset.mem_Icc] at hkIcc
+      rcases hkIcc with ⟨hqk, hkm⟩
+      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
+  have hcardT : T.card = S.card := by
+    exact Finset.card_image_iff.mpr (fun _ _ _ _ h => by omega)
+  have hcardUnion : (S ∪ T).card = S.card + T.card :=
+    Finset.card_union_of_disjoint hdisjoint
+  have hle := Finset.card_le_card hsubset
+  rw [hcardUnion, hcardT] at hle
+  change 2 * S.card ≤ m - q + 2
+  calc
+    2 * S.card = S.card + S.card := by omega
+    _ ≤ (Finset.Icc q (m + 1)).card := hle
+    _ = m + 2 - q := by rw [Nat.card_Icc]
+    _ ≤ m - q + 2 := by omega
+
+/-- The same packing bound applies to the observed interval of an open excursion. -/
+theorem CanonicalOpenPositiveQueueExcursion.two_mul_card_saturated_le
+    {n : OddNat} {q m : ℕ}
+    (_hopen : CanonicalOpenPositiveQueueExcursion n q m) :
+    2 * (canonicalSaturatedBlockIndices n q m).card ≤ m - q + 2 :=
+  two_mul_card_canonicalSaturatedBlockIndices_le n q m
+
+/-- A positive-drift block in a finite interval belongs to exactly one of the
+positive-pressure and saturated families. -/
+theorem canonicalPositiveDrift_mem_pressure_xor_saturated
+    {n : OddNat} {q m k : ℕ} (hk : k ∈ Finset.Icc q m)
+    (hpos : 0 < endpointAccountingTerm n k) :
+    (k ∈ canonicalPositivePressureBlockIndices n q m ∧
+        k ∉ canonicalSaturatedBlockIndices n q m) ∨
+      (k ∈ canonicalSaturatedBlockIndices n q m ∧
+        k ∉ canonicalPositivePressureBlockIndices n q m) := by
+  rcases positive_blockPressure_or_saturatedBorder_of_endpointAccountingTerm_pos
+      hpos with hpressure | hsaturated
+  · left
+    refine ⟨mem_canonicalPositivePressureBlockIndices.mpr
+      ⟨hk, hpos, hpressure⟩, ?_⟩
+    intro hs
+    have hsaturated := (mem_canonicalSaturatedBlockIndices.mp hs).2
+    rw [hsaturated.pressure_eq_zero] at hpressure
+    omega
+  · right
+    refine ⟨mem_canonicalSaturatedBlockIndices.mpr ⟨hk, hsaturated⟩, ?_⟩
+    intro hp
+    have hpressure := (mem_canonicalPositivePressureBlockIndices.mp hp).2.2
+    rw [hsaturated.pressure_eq_zero] at hpressure
+    omega
+
+/-- On an open observed excursion, every positive-drift block still has the
+exact pressure/saturation split; no future repayment endpoint is used. -/
+theorem CanonicalOpenPositiveQueueExcursion.positive_mem_pressure_xor_saturated
+    {n : OddNat} {q m k : ℕ}
+    (_hopen : CanonicalOpenPositiveQueueExcursion n q m)
+    (hk : k ∈ Finset.Icc q m)
+    (hpos : 0 < endpointAccountingTerm n k) :
+    (k ∈ canonicalPositivePressureBlockIndices n q m ∧
+        k ∉ canonicalSaturatedBlockIndices n q m) ∨
+      (k ∈ canonicalSaturatedBlockIndices n q m ∧
+        k ∉ canonicalPositivePressureBlockIndices n q m) :=
+  canonicalPositiveDrift_mem_pressure_xor_saturated hk hpos
+
+/-- Saturated indices remain isolated inside every open observed excursion. -/
+theorem CanonicalOpenPositiveQueueExcursion.saturated_not_succ_mem
+    {n : OddNat} {q m k : ℕ}
+    (_hopen : CanonicalOpenPositiveQueueExcursion n q m)
+    (hk : k ∈ canonicalSaturatedBlockIndices n q m) :
+    k + 1 ∉ canonicalSaturatedBlockIndices n q m :=
+  canonicalSaturatedBlockIndices_not_succ_mem hk
+
+/-! ## Dynamic-depth pressure accounting -/
+
+/-- Every canonical endpoint has positive terminal two-adic valuation. -/
+theorem one_le_canonicalBlockTerminalValuation (n : OddNat) (k : ℕ) :
+    1 ≤ canonicalBlockTerminalValuation n k := by
+  have hheight := two_le_orbitWindowHeight_paymentEndpointSeq n k
+  rw [canonicalBlock_endpointHeight_eq_terminalValuation_add_one] at hheight
+  omega
+
+/-- A block-dependent pressure depth.  Saturation remains at its zero-pressure
+terminal depth so that its exceptional unit is visible; ordinary blocks use
+the quantitatively stronger predecessor depth whenever available. -/
+noncomputable def canonicalDynamicPressureDepth
+    (n : OddNat) (k : ℕ) : ℕ := by
+  classical
+  exact if CanonicalSaturatedBorderBlock n k then
+      canonicalBlockTerminalValuation n k
+    else if 2 ≤ canonicalBlockTerminalValuation n k then
+      canonicalBlockTerminalValuation n k - 1
+    else 0
+
+/-- Dependent-pair presentation of a block and its selected pressure depth. -/
+noncomputable def canonicalDynamicPressureWitness
+    (n : OddNat) (k : ℕ) : Σ _block : ℕ, ℕ :=
+  ⟨k, canonicalDynamicPressureDepth n k⟩
+
+/-- Indicator charge carried by a saturated canonical block. -/
+noncomputable def canonicalSaturatedUnit (n : OddNat) (k : ℕ) : ℤ := by
+  classical
+  exact if CanonicalSaturatedBorderBlock n k then 1 else 0
+
+/-- Pointwise dynamic-depth domination.  Exactly saturated blocks consume the
+explicit unit surcharge; every nonsaturated positive block is paid by its
+selected local pressure contribution. -/
+theorem endpointAccountingTerm_le_dynamicPressure_add_saturatedUnit
+    {n : OddNat} {k : ℕ} (hpos : 0 < endpointAccountingTerm n k) :
+    endpointAccountingTerm n k ≤
+      blockPressureContributionInt n k (canonicalDynamicPressureDepth n k) +
+        canonicalSaturatedUnit n k := by
+  classical
+  by_cases hs : CanonicalSaturatedBorderBlock n k
+  · simp only [canonicalDynamicPressureDepth, hs, ↓reduceIte, canonicalSaturatedUnit]
+    rw [hs.pressure_eq_zero, hs.2.2]
+    norm_num
+  · simp only [canonicalDynamicPressureDepth, canonicalSaturatedUnit, if_neg hs,
+      add_zero]
+    by_cases hv : 2 ≤ canonicalBlockTerminalValuation n k
+    · rw [if_pos hv]
+      exact endpointAccountingTerm_le_blockPressure_pred_terminal hpos hv
+    · rw [if_neg hv]
+      rw [blockPressureContributionInt_zero]
+      have hdrift := endpointAccountingTerm_le_length_sub_capacity n k
+      rw [canonicalBlockCapacityCount_eq_terminalValuation] at hdrift
+      have hvone := one_le_canonicalBlockTerminalValuation n k
+      have hLen : canonicalPaymentBlockLength n k = canonicalBlockLength n k := rfl
+      rw [hLen]
+      omega
+
+/-- Actual positive-drift indices in a closed finite interval. -/
+noncomputable def canonicalPositiveDriftBlockIndices
+    (n : OddNat) (q m : ℕ) : Finset ℕ :=
+  (Finset.Icc q m).filter fun k => 0 < endpointAccountingTerm n k
+
+/-- Finite dynamic-depth aggregation with isolated saturation retained as an
+explicit unit charge. -/
+theorem sum_positiveDrift_le_dynamicPressure_add_saturatedUnits
+    (n : OddNat) (q m : ℕ) :
+    (∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
+        endpointAccountingTerm n k) ≤
+      (∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
+        (blockPressureContributionInt n k (canonicalDynamicPressureDepth n k) +
+          canonicalSaturatedUnit n k)) := by
+  classical
+  refine Finset.sum_le_sum
+    (s := canonicalPositiveDriftBlockIndices n q m)
+    (f := fun k => endpointAccountingTerm n k)
+    (g := fun k => blockPressureContributionInt n k
+      (canonicalDynamicPressureDepth n k) + canonicalSaturatedUnit n k)
+    (fun k hk => ?_)
+  have hpos : 0 < endpointAccountingTerm n k := by
+    change k ∈ (Finset.Icc q m).filter
+      (fun j => 0 < endpointAccountingTerm n j) at hk
+    exact (Finset.mem_filter.mp hk).2
+  exact endpointAccountingTerm_le_dynamicPressure_add_saturatedUnit hpos
+
+/-- The finite surcharge sum is exactly the number of saturated indices. -/
+theorem sum_saturatedUnit_positiveIndices_eq_card
+    (n : OddNat) (q m : ℕ) :
+    (∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
+      canonicalSaturatedUnit n k) =
+      (canonicalSaturatedBlockIndices n q m).card := by
+  classical
+  simp only [canonicalPositiveDriftBlockIndices, canonicalSaturatedUnit, Finset.sum_boole,
+    canonicalSaturatedBlockIndices, Nat.cast_inj]
+  congr 1
+  ext k
+  simp only [Finset.mem_filter]
+  constructor
+  · rintro ⟨⟨hk, _hpos⟩, hs⟩
+    exact ⟨hk, hs⟩
+  · rintro ⟨hk, hs⟩
+    exact ⟨⟨hk, hs.drift_pos⟩, hs⟩
+
+/-- Accounting shape with dynamic pressure mass and the cardinality of the
+isolated saturated family displayed as separate terms. -/
+theorem sum_positiveDrift_le_dynamicPressureMass_add_saturatedCard
+    (n : OddNat) (q m : ℕ) :
+    (∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
+        endpointAccountingTerm n k) ≤
+      (∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
+        blockPressureContributionInt n k (canonicalDynamicPressureDepth n k)) +
+          (canonicalSaturatedBlockIndices n q m).card := by
+  have h := sum_positiveDrift_le_dynamicPressure_add_saturatedUnits n q m
+  rw [Finset.sum_add_distrib,
+    sum_saturatedUnit_positiveIndices_eq_card] at h
+  exact h
+
+/-! ## Exact successor grammar -/
+
+/-- After a saturated block, the next start plus one is half of `9*u+1`. -/
+theorem CanonicalSaturatedBorderBlock.nextStartState_add_one_eq
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
+    canonicalBlockNextStartState n k + 1 =
+      (9 * canonicalBlockOddCore n k + 1) / 2 := by
+  let u := canonicalBlockOddCore n k
+  have huodd := canonicalBlockOddCore_mod_two_eq_one n k
+  have hdvdMinus : 2 ∣ 9 * u - 1 := by
+    rw [Nat.dvd_iff_mod_eq_zero]
+    omega
+  have hdvdPlus : 2 ∣ 9 * u + 1 := by
+    rw [Nat.dvd_iff_mod_eq_zero]
+    omega
+  rw [h.nextStartState_eq]
+  have hminus := Nat.div_mul_cancel hdvdMinus
+  have hplus := Nat.div_mul_cancel hdvdPlus
+  omega
+
+/-- The next canonical length is the valuation of the exact successor word. -/
+theorem CanonicalSaturatedBorderBlock.nextBlockLength_eq_v2_half_nine_core_add_one
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
+    canonicalBlockLength n (k + 1) =
+      v2 ((9 * canonicalBlockOddCore n k + 1) / 2) := by
+  rw [canonicalBlockLength_eq_v2_startState_add_one,
+    canonicalBlockStartState_succ_eq_nextStartState, h.nextStartState_add_one_eq]
+
+/-- Residue class three modulo eight produces a next block of length one. -/
+theorem CanonicalSaturatedBorderBlock.nextBlockLength_eq_one_of_core_mod_eight_eq_three
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
+    (hu : canonicalBlockOddCore n k % 8 = 3) :
+    canonicalBlockLength n (k + 1) = 1 := by
+  let u := canonicalBlockOddCore n k
+  let y := (9 * u + 1) / 2
+  have hdecomp : u = 8 * (u / 8) + 3 := by
+    have := Nat.mod_add_div u 8
+    omega
+  have hy : y = 36 * (u / 8) + 14 := by
+    dsimp [y]
+    omega
+  have hyeven : y % 2 = 0 := by rw [hy]; omega
+  have hypos : 0 < y := by rw [hy]; omega
+  have hyhalfodd : (y / 2) % 2 = 1 := by rw [hy]; omega
+  rw [h.nextBlockLength_eq_v2_half_nine_core_add_one]
+  change v2 y = 1
+  rw [v2_step_of_even y hyeven hypos, v2_odd _ hyhalfodd]
+
+/-- Residue class seven modulo eight produces a next block of length at least two. -/
+theorem CanonicalSaturatedBorderBlock.two_le_nextBlockLength_of_core_mod_eight_eq_seven
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
+    (hu : canonicalBlockOddCore n k % 8 = 7) :
+    2 ≤ canonicalBlockLength n (k + 1) := by
+  let u := canonicalBlockOddCore n k
+  let y := (9 * u + 1) / 2
+  have hdecomp : u = 8 * (u / 8) + 7 := by
+    have := Nat.mod_add_div u 8
+    omega
+  have hy : y = 36 * (u / 8) + 32 := by
+    dsimp [y]
+    omega
+  have hypos : 0 < y := by rw [hy]; omega
+  have hfour : 4 ∣ y := by
+    rw [hy]
+    exact ⟨9 * (u / 8) + 8, by ring⟩
+  rw [h.nextBlockLength_eq_v2_half_nine_core_add_one]
+  change 2 ≤ v2 y
+  exact (two_le_v2_iff_four_dvd hypos.ne').2 hfour
+
+end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-319.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-319.md
new file mode 100644
index 00000000..c346aa5b
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-319.md
@@ -0,0 +1,146 @@
+# Petal / Float Window Report - Checkpoint 319
+
+## Status
+
+`cp-319` closes the saturated canonical-block branch through the requested
+finite dynamic-pressure aggregation surface.  All new Lean declarations are
+proved without `sorry`.
+
+## Implemented module
+
+New module:
+
+```text
+DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentSaturatedSuccessor
+```
+
+It is exported by `DkMath.Collatz.PetalBridge.FloatWindow`.
+
+## Exact facts now proved
+
+Saturation is equivalent to the two structural conditions
+
+```text
+L = v + 1
+claimCount = L.
+```
+
+Its terminal-depth pressure is exactly zero.  The exponential comparison
+`3^L < 2^(2L-1)` for `L >= 3`, combined with the exact normal form and unit
+bit-width drift, proves that every saturated block has
+
+```text
+L = 2
+v = 1
+endpoint height = 2.
+```
+
+Writing `u` for the odd core gives
+
+```text
+x0 = 4*u - 1
+x1 = (9*u - 1) / 2
+v2(9*u - 1) = 1
+u mod 4 = 3
+u mod 8 = 3 or 7.
+```
+
+Two consecutive saturated blocks are impossible.  This is an exact arithmetic
+theorem and no longer a finite-audit observation.  Consequently the correct
+successor theorem is
+
+```text
+saturated(k)
+  -> drift(k+1) <= 0
+     or terminal-pressure(k+1) > 0.
+```
+
+The false unconditional statement `saturated -> next drift <= 0` remains
+rejected.  The positive successors seen in the cp-318 audit inhabit the
+positive-pressure branch.
+
+## Pressure depth and finite decomposition
+
+For positive drift with terminal valuation `v >= 2`, pressure at depth `v-1`
+equals the ledger upper bound `L-v` and therefore dominates the drift.
+
+At `v = 1`, a positive length-two block is saturated; a nonsaturated positive
+block has length at least three and positive terminal-depth pressure.
+
+The implementation now exposes actual finite index sets for:
+
+```text
+positive drift
+positive terminal pressure
+saturation
+nonpositive drift.
+```
+
+Every positive block belongs to exactly one of the pressure and saturation
+families.  Saturated indices are isolated, and the exact packing bound is
+
+```text
+2 * saturated.card <= intervalLength + 1.
+```
+
+This remains valid for an open observed excursion and assumes no future
+repayment endpoint.
+
+## Dynamic-depth aggregation
+
+The selected pressure coordinate remains a dependent pair `(block, depth)`:
+
+```text
+saturated       -> terminal depth
+nonsaturated,
+  v >= 2        -> v - 1
+nonsaturated,
+  v = 1         -> 0.
+```
+
+The finite theorem now has the requested form:
+
+```text
+sum positive drift
+  <= sum selected dynamic-depth pressure
+       + saturatedIndices.card.
+```
+
+Thus the dynamic-depth sum itself was not an obstruction.
+
+## Successor grammar
+
+For a saturated core `u`, Lean proves
+
+```text
+nextStart + 1 = (9*u + 1) / 2
+nextLength = v2 ((9*u + 1) / 2)
+u mod 8 = 3 -> nextLength = 1
+u mod 8 = 7 -> 2 <= nextLength.
+```
+
+This is the exact two-branch successor grammar requested at this checkpoint.
+
+## First remaining obstruction
+
+The next global step cannot simply reinterpret the finite pressure sum as
+repaid mass.  Pressure witnesses selected at different block-dependent depths
+may refer to overlapping continuation resources.  The current theorem is a
+correct sum of local numerical contributions; it does not yet prove that those
+contributions are disjoint physical payments.
+
+The next required bridge is therefore one of:
+
+1. an injection from selected `(block, depth)` pressure units to distinct
+   payment resources; or
+2. a uniform multiplicity bound for reuse of a payment resource, followed by
+   the corresponding corrected charging inequality.
+
+Until such an incidence theorem is proved, replacing dynamic local pressure by
+a globally available repayment mass would overstate the current result.
+
+## Verification
+
+The focused module build passed.  The public aggregate and top-level build
+gates are run after this report is created and are recorded in the completion
+message.
````
`````
