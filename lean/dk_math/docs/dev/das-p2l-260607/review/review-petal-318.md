# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPositiveBlock

gch: 126aaae7fa3d0d8c0f18a920082852115f4a3fac

## Report

(22m15s)

cp-318 を最初の真正な阻害点まで完了しました。

- 正 drift は「動的深度で正 pressure」または `CanonicalSaturatedBorderBlock` に必ず分岐。
- saturated block は `x + 1 = 2^L * u`、`v2 (3^L * u - 1) = L - 1` という厳密な正規形を持つ。
- 正 queue 位置には一意な open excursion 開始点が存在。
- 遷移関係付き有限 potential certificate を実装。
- 全時刻 bit-width の条件付き評価も canonical block 被覆から確立。

一方、33,435 個の saturated block の監査により、

```text
saturated block -> next block drift <= 0
```

は 1,785 件の反例があり、偽と判明しました。後続規則は無理に定理化せず、正確な停止理由をコードコメントへ記録しています。

主要成果は [UniversalPaymentPositiveBlock.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentPositiveBlock.lean)、全記録は [report-petal-318.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-318.md) にあります。

`lake build DkMath`、各対象モジュール、`git diff --check` はすべて成功。今回の Lean 変更に `sorry` はありません。

## Review

## 結論

**実装は全面採用。だが、停止点の診断は修正じゃ。**

cp-318 は、正 drift block を

$$
\text{positive pressure branch}\quad\lor\quad\text{saturated border branch}
$$

へ厳密に分離し、high claim depth を continuation fiber へ実際に単射で送った。さらに saturated block の全 source が carry-two であること、open excursion の一意な開始点、遷移関係つき finite potential certificate、全 orbit time の条件付き bit-width 上界まで閉じている。ここまでは非常に強い。

しかし、report が有限観測に留めた次の二項目は、**現在の exact normal form と drift theorem だけで定理化できる可能性が極めて高い**。

```text
全 saturated block の長さは 2
saturated block は連続しない
```

したがって、

> saturated successor behavior が真正な停止点

という診断は一手早い。

さらに、監査で見つかった「saturated の次も正 drift」である 1,785 件は、反例ではあるが障害ではない。

**連続 saturation が不可能なら、その正 successor は必ず pressure branch になる。**

ここが今回の詰将棋の王手筋じゃ。

---

## 1. cp-318 の実装評価

## Low / high claim-depth 分解

terminal valuation を $v$ とし、claim depth 集合を

$$
C=C_{\le v}\sqcup C_{>v}
$$

へ分けた。

そして、

$$
A=|C_{\le v}|+|C_{>v}|
$$

$$
|C_{\le v}|\le v
$$

$$
D=|C_{>v}|-\left(v-|C_{\le v}|\right)
$$

を得た。

ここから、

$$
D\le|C_{>v}|
$$

および、

$$
0<D\Longrightarrow C_{>v}\ne\varnothing
$$

が出る。

これは正確じゃ。

positive drift は必ず、terminal capacity より深い claim を持つ。

## High claim から continuation への単射

$d>v$ の claim source は exact depth $d$ を持つので、depth $v$ ではまだ continuation 中である。

したがって、

$$
C_{>v}\hookrightarrow\operatorname{ContinuationFiber}(v)
$$

が成立し、

$$
|C_{>v}|
\le
|\operatorname{ContinuationFiber}(v)|
$$

となる。

これは、cp-317 で不足していた「Float claim を pressure incidence へ送る局所写像」を、正しい block-local 形式で実現している。

## Positive pressure / saturation 分岐

block length を $L$ とすると、正 depth $v$ における block pressure は、

$$
M_v=L-v-1
$$

じゃ。

positive drift なら $v<L$。

そこで、

- $L\ge v+2$ なら $M_v>0$
- $L=v+1$ なら pressure は境界値 $0$

となる。

後者で正 drift を維持するには、

$$
A=L
$$

すなわち全 depth が claim でなければならない。

このため、

$$
0<D
\Longrightarrow
M_v>0\lor\operatorname{Saturated}
$$

という cp-318 の二分は正確じゃ。

なお saturated branch の pressure は「非正」より強く、

$$
M_v=0
$$

じゃ。

`pressure_eq_zero` を公開すると意味がさらに明瞭になる。

---

## 2. Saturated 定義の最小化

現在の定義は、

```lean
L = v + 1
claimCount = L
endpointAccountingTerm = 1
```

の三条件を持つ。

しかし第三条件は最初の二条件から従う。

$$
D=A-v=L-(L-1)=1
$$

したがって次の iff を追加するとよい。

```lean
CanonicalSaturatedBorderBlock n k ↔
  canonicalBlockLength n k =
      canonicalBlockTerminalValuation n k + 1
  ∧ canonicalBlockClaimCount n k =
      canonicalBlockLength n k
```

既存定義を変更する必要はない。minimal characterization を別 theorem として置けばよい。

---

## 3. 決定的推論：saturated block は必ず $L=2$

saturated block の start state を $x$、length を $L$、odd core を $u$ とする。

cp-317 / cp-318 から、

$$
x+1=2^Lu
$$

$$
v=L-1
$$

$$
x'=\frac{3^Lu-1}{2^{L-1}}
$$

が成立する。ここで $x'$ は次 block の start state じゃ。

また saturated drift は $1$ なので、exact block ledger より、

$$
\operatorname{bitWidth}(x') = \operatorname{bitWidth}(x)+1
$$

となる。

したがって、数値としても、

$$
x<x'
$$

でなければならない。

ところが $L\ge3$ と仮定する。

このとき、

$$
3^L<2^{2L-1}
$$

じゃ。

初期値 $L=3$ では、

$$
27<32
$$

であり、以後は左辺が $3$ 倍、右辺が $4$ 倍になるので帰納的に成立する。

ゆえに、

$$
3^Lu-1<2^{2L-1}u
$$

となる。

両辺を $2^{L-1}$ で割れば、

$$
x' = \frac{3^Lu-1}{2^{L-1}} < 2^Lu = x+1
$$

である。

自然数なので、

$$
x'\le x
$$

となる。

しかし saturated drift $1$ は bit width の厳密増加を要求している。

$$
\operatorname{bitWidth}(x') = \operatorname{bitWidth}(x)+1
$$

これは $x'\le x$ と両立しない。

したがって、

$$
L<3
$$

じゃ。

一方、canonical endpoint の height は少なくとも $2$ なので terminal valuation は少なくとも $1$。

saturated では $L=v+1$ だから、

$$
2\le L
$$

である。

よって、

$$
\boxed{L=2}
$$

じゃ。

これは有限監査ではない。現在の exact theorem 群から出る普遍定理である。

---

## 4. Saturated normal form は一気に簡約される

$L=2$ が確定すると、全 saturated block は、

$$
x+1=4u
$$

$$
x=4u-1
$$

$$
v_2(9u-1)=1
$$

$$
x'=\frac{9u-1}{2}
$$

となる。

さらに、

$$
v_2(9u-1)=1
$$

は、

$$
9u-1\equiv2\pmod4
$$

を意味する。

$9\equiv1\pmod4$ だから、

$$
u-1\equiv2\pmod4
$$

すなわち、

$$
\boxed{u\equiv3\pmod4}
$$

じゃ。

監査で saturated odd core が mod $8$ で $3$ または $7$ だけだったのは、偶然ではない。

$$
u\equiv3\pmod4
\Longleftrightarrow
u\equiv3\text{ or }7\pmod8
$$

で完全に説明される。

したがって audit の、

```text
saturated odd-core residues mod 8: {3, 7}
```

も theorem 側へ引き上げられる。

---

## 5. 二つの saturated block は連続できない

これはさらに重要じゃ。

block $k$ と block $k+1$ が両方 saturated と仮定する。

第一 saturated block の odd core を $u$ とする。

第一 block の start と次 start は、

$$
x_0=4u-1
$$

$$
x_1=\frac{9u-1}{2}
$$

じゃ。

第二 block も length $2$ なので、ある odd core $u_1$ に対して、

$$
x_1+1=4u_1
$$

である。

よって、

$$
u_1=\frac{9u+1}{8}
$$

じゃ。

第二 block 後の state は、

$$
x_2=\frac{9u_1-1}{2}
$$

だから、

$$
x_2
===

\frac{81u+1}{16}
$$

となる。

二つの saturated block はそれぞれ drift $1$ なので、

$$
\operatorname{bitWidth}(x_2) = \operatorname{bitWidth}(x_0)+2
$$

となる。

bit width が $2$ 増えれば、

$$
2x_0<x_2
$$

でなければならない。

しかし arithmetic normal form では、

$$
16x_2=81u+1
$$

$$
16(2x_0)=32(4u-1)=128u-32
$$

である。

$u\ge1$ より、

$$
81u+1<128u-32
$$

なので、

$$
x_2<2x_0
$$

となる。

矛盾じゃ。

したがって、

$$
\boxed{
\operatorname{Saturated}(k)
\Longrightarrow
\neg\operatorname{Saturated}(k+1)
}
$$

である。

監査で saturated の最大連続長が $1$ だった事実も、Lean theorem へ引き上げられる。

---

## 6. 1,785 件の「正 successor」の意味が逆転する

監査では、

```text
saturated block
  -> next block drift <= 0
```

が 1,785 件の反例により否定された。

これは正しい否定結果じゃ。

しかし no-consecutive-saturation が証明されれば、正 successor は必ず non-saturated になる。

したがって既存の二分定理から、

$$
\operatorname{Saturated}(k)
\land 0<D_{k+1}
\Longrightarrow
0<M_{v_{k+1}}(k+1)
$$

が直ちに従う。

つまり 1,785 件は、

> saturated exception の後に、さらに別の exception が続いた

例ではない。

> saturated unit drift の後に、positive pressure block が続いた

例じゃ。

これは障害ではなく、pressure branch への合流例である。

正しい successor theorem は、

$$
\boxed{
\operatorname{Saturated}(k)
\Longrightarrow
D_{k+1}\le0
\ \lor
0<M_{v_{k+1}}(k+1)
}
$$

じゃ。

この theorem は監査結果の全行と整合する。

---

## 7. pressure depth はもう一段鋭く選べる

positive block では、

$$
D=A-v
$$

$$
A\le L
$$

なので、

$$
D\le L-v
$$

じゃ。

$v\ge2$ の場合、pressure depth を terminal valuation $v$ ではなく、その一段手前、

$$
d=v-1
$$

に置く。

すると、

$$
M_{v-1}=L-(v-1)-1=L-v
$$

だから、

$$
\boxed{D\le M_{v-1}}
$$

となる。

しかも $D>0$ なら、

$$
M_{v-1}>0
$$

じゃ。

したがって $v\ge2$ の positive block は、単なる positive pressure witness より強く、

> **block drift 全量を支配する pressure margin**

を一段手前の depth に持つ。

残る境界は $v=1$ だけになる。

$v=1$ かつ $L=2$ の positive block は saturated。

$v=1$ かつ non-saturated positive なら $L\ge3$ なので、既存 terminal depth $1$ でも、

$$
M_1=L-2>0
$$

じゃ。

よって positive block は、より鋭く次に分類できる。

```text
v >= 2:
  depth v - 1 の pressure が block drift 全量を支配

v = 1, L >= 3:
  depth 1 で正 pressure

v = 1, L = 2:
  isolated saturated unit block
```

敵は本当に最後の一種類まで圧縮された。

---

## 8. Open excursion の意味

open excursion の存在・開始点一意性は正しい。

ただし、

```lean
CanonicalOpenPositiveQueueExcursion.positiveBlock_pressure_or_saturated
```

では `_hopen` と `_hk` が証明に使われていない。

定理自体は正しいが、実質は global dichotomy の namespace alias じゃ。

今後は open excursion 上で本当に必要な theorem を置くべきである。

例えば、

```lean
theorem CanonicalOpenPositiveQueueExcursion.no_adjacent_saturated
```

および、

```lean
theorem CanonicalOpenPositiveQueueExcursion.positive_successor_of_saturated_has_pressure
```

じゃ。

さらに saturated index は隣接しないので、有限 interval 内で、

$$
2\,|\operatorname{SaturatedIndices}|
\le
\operatorname{length}+1
$$

型の packing bound が得られる。

---

## 9. Relational potential certificate

`Step` relation を持つ版への修正は正しい。

これで soundness は arbitrary state pair ではなく、実際の transition edge だけに要求される。

また diagnostics の意味分離も正しい。

- drift collision は exact deterministic drift recovery を否定
- nondeterministic successor は deterministic automaton だけを否定
- positive closed-signature path は bounded potential certificate を否定

ここは完成と見てよい。

もう finite certificate の抽象層を増やす必要はない。

---

## 10. 真の停止点

cp-318 report の停止点は、

```text
saturated successor behavior
```

ではない。

現在の exact theorem から、

```text
saturated length = 2
no consecutive saturation
positive successor after saturation = pressure branch
```

まで進める。

その後に残る真正な問題は、

> **動的 depth に現れる positive pressure witness 群を、open excursion 全体でどう集約するか**

じゃ。

また、isolated saturated block の $+1$ を、

- 前後の pressure witness
- 後続の nonpositive drift
- 既存 pressure separator

のどこへ charge するかが残る。

つまり敵の最終形は、

```text
dynamic-depth pressure mass
+
isolated unit surcharge
```

じゃ。

これは cp-318 よりさらに狭い。

---

## 判定まとめ

### Positive block dichotomy

**完成。**

### High claim → continuation injection

**完成。**

### Saturated arithmetic normal form

**完成。ただしさらに $L=2$ まで閉じられる。**

### Saturated length $2$

**未実装だが、現 API から証明可能。**

### Consecutive saturation

**未実装だが、二 block normal form と width drift から否定可能。**

### 1,785 positive successors

**障害ではない。全て pressure branch へ再分類される。**

### 真の次戦線

**dynamic pressure aggregation と isolated saturated unit の charge。**

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge Float-window branch after
report-petal-318.

The cp-318 implementation is accepted, but its reported stopping point must be
revised.

The exact normal form and signed width ledger already appear sufficient to
prove that every saturated border block has length exactly two, and that two
saturated blocks cannot be consecutive.

Do not begin another broad saturated-successor audit before attempting these
exact theorems.

# Stage A — minimal saturated characterization

Add:

    CanonicalSaturatedBorderBlock n k
      <->
    canonicalBlockLength n k
        = canonicalBlockTerminalValuation n k + 1
      ∧
    canonicalBlockClaimCount n k
        = canonicalBlockLength n k

Derive the existing `endpointAccountingTerm = 1` field from these two
conditions.

Also strengthen:

    saturated pressure <= 0

to:

    saturated pressure = 0

at terminal valuation depth.

# Stage B — exponential comparison lemma

Prove the arithmetic lemma:

    3 <= L -> 3^L < 2^(2*L - 1)

Use induction from `27 < 32`; each successor multiplies the left side by three
and the right side by four.

Expose a form convenient for multiplication by a positive odd core.

# Stage C — saturated length is exactly two

For a saturated block, write:

    x = canonicalBlockStartState n k
    L = canonicalBlockLength n k
    u = canonicalBlockOddCore n k
    x' = canonicalBlockNextStartState n k

Use the exact normal form:

    x + 1 = 2^L * u
    x' = (3^L * u - 1) / 2^(L - 1)

and the exact unit drift:

    bitWidth x' = bitWidth x + 1

Assume `3 <= L`.  From Stage B prove:

    x' < x + 1

hence:

    x' <= x.

This contradicts the strict bit-width increase.

Since endpoint terminal valuation is positive and `L = v + 1`, conclude:

    CanonicalSaturatedBorderBlock n k
      ->
    canonicalBlockLength n k = 2

Then derive:

    canonicalBlockTerminalValuation n k = 1
    orbitWindowHeight n (paymentEndpointSeq n k) = 2

# Stage D — exact length-two normal form

For every saturated block prove:

    canonicalBlockStartState n k
      = 4 * canonicalBlockOddCore n k - 1

    canonicalBlockNextStartState n k
      = (9 * canonicalBlockOddCore n k - 1) / 2

    v2 (9 * canonicalBlockOddCore n k - 1) = 1

Derive the residue theorem:

    canonicalBlockOddCore n k % 4 = 3

and therefore:

    core % 8 = 3 or core % 8 = 7.

This promotes the cp-318 residue audit to exact arithmetic.

# Stage E — no consecutive saturated blocks

Assume blocks `k` and `k + 1` are both saturated.

Let `u` be the odd core of block `k`.

Using Stage D twice, derive:

    x0 = 4*u - 1
    x1 = (9*u - 1) / 2

    u1 = (9*u + 1) / 8
    x2 = (81*u + 1) / 16

Two saturated unit drifts imply:

    bitWidth x2 = bitWidth x0 + 2

and hence:

    2*x0 < x2.

But the exact arithmetic formulas and `0 < u` imply:

    x2 < 2*x0.

Conclude:

    CanonicalSaturatedBorderBlock n k
      ->
    not CanonicalSaturatedBorderBlock n (k + 1)

Do not use the finite audit in this proof.

# Stage F — correct saturated-successor theorem

Prove:

    CanonicalSaturatedBorderBlock n k
      ->
    endpointAccountingTerm n (k + 1) <= 0
      or
    0 < blockPressureContributionInt n (k + 1)
      (canonicalBlockTerminalValuation n (k + 1))

If the successor drift is positive, use Stage E to exclude saturation and then
apply the existing positive-pressure/saturated dichotomy.

Document that the 1,785 positive successors in the cp-318 audit are examples
of the pressure branch, not unresolved saturated exceptions.

# Stage G — sharper pressure depth

For every positive block with terminal valuation `v >= 2`, prove:

    endpointAccountingTerm n k
      <=
    blockPressureContributionInt n k (v - 1)

Use:

    endpointAccountingTerm <= L - v

and:

    blockPressureContributionInt at depth (v - 1) = L - v.

Thus positive drift at `v >= 2` is quantitatively dominated by pressure one
depth before the terminal valuation.

For `v = 1`, prove the exact split:

    positive and L = 2 -> saturated
    positive and not saturated -> 3 <= L and pressure at depth 1 is positive.

# Stage H — isolated saturated indices

For a finite block interval define the actual Finset of saturated indices.

Prove:

    no two members are consecutive.

Derive a finite packing bound such as:

    2 * saturatedIndices.card
      <= intervalLength + 1.

Add the corresponding theorem for indices inside an open positive excursion.

# Stage I — open-excursion decomposition

For an open positive excursion, define:

    positivePressureBlockIndices
    saturatedBlockIndices
    nonpositiveBlockIndices

Prove that every positive-drift block belongs to exactly one of the first two
families and that saturated indices are isolated.

Do not assume a future repayment endpoint.

# Stage J — dynamic pressure aggregation frontier

Package the quantitative pressure witnesses as dependent pairs:

    (block index, pressure depth)

Do not force all witnesses to one fixed depth.

Seek an exact finite sum theorem that bounds the positive drift of all
non-saturated positive blocks by the sum of their selected pressure
contributions, using depth `v - 1` when `v >= 2`.

Keep isolated saturated blocks as explicit unit surcharge terms.

The target accounting shape is:

    positive drift over an interval
      <=
    selected dynamic-depth pressure mass
      + number of isolated saturated blocks.

# Stage K — successor grammar

After length-two and no-consecutive-saturation are theorems, expose the exact
next-block coordinates:

    current saturated core = u
    next start = (9*u - 1) / 2
    next block length = v2 (9*u + 1) - 1
    next odd core = oddPart (9*u + 1)

Derive at least:

    u % 8 = 3 -> next block length = 1
    u % 8 = 7 -> 2 <= next block length.

Use higher residues only after these exact branches are formalized.

# Stage L — report correction

Update the cp-318 stopping interpretation:

    saturated length two
    and
    no consecutive saturation

are no longer finite observations once Stages C and E are complete.

The false theorem remains correctly rejected:

    saturated -> next drift <= 0.

The surviving exact theorem is:

    saturated -> next nonpositive or next positive-pressure.

Stop only at the first obstruction to the dynamic-depth pressure sum or to
charging the isolated saturated unit terms.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-319.md
```

うむ。

cp-318 は「例外が残った」checkpoint ではなかった。

**例外は長さ $2$ に潰れ、しかも二回続けて置けない。**

盤上に残った saturated 駒は、連鎖する敵ではなく、pressure block の間に一枚ずつしか現れない孤立駒じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
index 63c219c6..5913925e 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
@@ -20,6 +20,7 @@ import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentRepayment
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentDepthLedger
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentScalarQueue
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlockNormalForm
+import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPositiveBlock
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPrimitiveExcursion
 import DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition
 
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean
index 4aca983b..e46e2e80 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean
@@ -19,6 +19,20 @@ standard stronger form of the nonpositive-cycle condition.  It deliberately
 does not instantiate the certificate with the experimental low-bit block
 signatures: the cp-317 audit found drift collisions and nondeterministic
 successors in those projections.
+
+The exact interpretation of those diagnostics is deliberately asymmetric:
+
+* a drift collision disproves exact deterministic recovery of drift from the
+  selected signature;
+* two realized successors of one signature disprove a deterministic automaton,
+  but do not disprove a nondeterministic graph or a sound over-approximation;
+* a realized related path with equal endpoint signatures and positive total
+  weight contradicts any bounded potential certificate on that signature, by
+  `pathWeight_nonpos_of_signature_eq` below.
+
+Thus nondeterminism alone is not a potential obstruction.  The obstruction is
+a positive closed-signature path whose adjacent transitions all satisfy the
+certificate's `Step` relation.
 -/
 
 /--
@@ -40,10 +54,135 @@ structure FiniteSignedTransitionPotentialCertificate
   potential_nonneg : ∀ s, 0 ≤ potential s
   potential_le_bound : ∀ s, potential s ≤ bound
 
+/--
+A finite signed abstraction whose soundness obligation is restricted to actual
+transitions.  This is the appropriate surface for a nondeterministic finite
+graph: arbitrary pairs of concrete states need not be comparable.
+-/
+structure RelationalFiniteSignedTransitionPotentialCertificate
+    (State Signature : Type*) [Fintype Signature] where
+  Step : State → State → Prop
+  signature : State → Signature
+  actualWeight : State → State → ℤ
+  projectedUpperWeight : Signature → Signature → ℤ
+  potential : Signature → ℤ
+  bound : ℕ
+  actual_le_projected : ∀ a b, Step a b →
+    actualWeight a b ≤ projectedUpperWeight (signature a) (signature b)
+  projected_le_potential_diff : ∀ s t,
+    projectedUpperWeight s t ≤ potential t - potential s
+  potential_nonneg : ∀ s, 0 ≤ potential s
+  potential_le_bound : ∀ s, potential s ≤ bound
+
+namespace RelationalFiniteSignedTransitionPotentialCertificate
+
+variable {State Signature : Type*} [Fintype Signature]
+
+/-- Concrete signed weight along a finite sequence of related transitions. -/
+def pathWeight
+    (C : RelationalFiniteSignedTransitionPotentialCertificate State Signature)
+    (stateAt : ℕ → State) (start length : ℕ) : ℤ :=
+  ∑ i ∈ Finset.range length,
+    C.actualWeight (stateAt (start + i)) (stateAt (start + i + 1))
+
+/-- Projected upper weight along the same finite transition path. -/
+def projectedPathWeight
+    (C : RelationalFiniteSignedTransitionPotentialCertificate State Signature)
+    (stateAt : ℕ → State) (start length : ℕ) : ℤ :=
+  ∑ i ∈ Finset.range length,
+    C.projectedUpperWeight
+      (C.signature (stateAt (start + i)))
+      (C.signature (stateAt (start + i + 1)))
+
+/-- A path satisfies the certificate relation at each adjacent pair. -/
+def IsPath
+    (C : RelationalFiniteSignedTransitionPotentialCertificate State Signature)
+    (stateAt : ℕ → State) (start length : ℕ) : Prop :=
+  ∀ i, i < length → C.Step (stateAt (start + i)) (stateAt (start + i + 1))
+
+/-- Relation soundness bounds every concrete weight along a certified path. -/
+theorem pathWeight_le_projectedPathWeight
+    (C : RelationalFiniteSignedTransitionPotentialCertificate State Signature)
+    (stateAt : ℕ → State) (start length : ℕ)
+    (hpath : C.IsPath stateAt start length) :
+    C.pathWeight stateAt start length ≤ C.projectedPathWeight stateAt start length := by
+  unfold pathWeight projectedPathWeight
+  exact Finset.sum_le_sum fun i hi =>
+    C.actual_le_projected _ _ (hpath i (Finset.mem_range.mp hi))
+
+/-- Projected weights telescope below the endpoint potential difference. -/
+theorem projectedPathWeight_le_potential_sub
+    (C : RelationalFiniteSignedTransitionPotentialCertificate State Signature)
+    (stateAt : ℕ → State) (start length : ℕ) :
+    C.projectedPathWeight stateAt start length ≤
+      C.potential (C.signature (stateAt (start + length))) -
+        C.potential (C.signature (stateAt start)) := by
+  induction length with
+  | zero => simp [projectedPathWeight]
+  | succ length ih =>
+      rw [projectedPathWeight, Finset.sum_range_succ]
+      unfold projectedPathWeight at ih
+      change
+        (∑ i ∈ Finset.range length,
+          C.projectedUpperWeight
+            (C.signature (stateAt (start + i)))
+            (C.signature (stateAt (start + i + 1)))) +
+            C.projectedUpperWeight
+              (C.signature (stateAt (start + length)))
+              (C.signature (stateAt (start + length + 1))) ≤ _
+      have hedge := C.projected_le_potential_diff
+        (C.signature (stateAt (start + length)))
+        (C.signature (stateAt (start + length + 1)))
+      have hend : start + (length + 1) = start + length + 1 := by omega
+      rw [hend]
+      linarith
+
+/-- Every related concrete path has weight at most the finite potential bound. -/
+theorem pathWeight_le_bound
+    (C : RelationalFiniteSignedTransitionPotentialCertificate State Signature)
+    (stateAt : ℕ → State) (start length : ℕ)
+    (hpath : C.IsPath stateAt start length) :
+    C.pathWeight stateAt start length ≤ C.bound := by
+  have hweight := (C.pathWeight_le_projectedPathWeight stateAt start length hpath).trans
+    (C.projectedPathWeight_le_potential_sub stateAt start length)
+  have hnonneg := C.potential_nonneg (C.signature (stateAt start))
+  have hbound := C.potential_le_bound (C.signature (stateAt (start + length)))
+  omega
+
+/-- A related closed-signature path cannot have positive concrete weight. -/
+theorem pathWeight_nonpos_of_signature_eq
+    (C : RelationalFiniteSignedTransitionPotentialCertificate State Signature)
+    (stateAt : ℕ → State) (start length : ℕ)
+    (hpath : C.IsPath stateAt start length)
+    (hclosed : C.signature (stateAt (start + length)) =
+      C.signature (stateAt start)) :
+    C.pathWeight stateAt start length ≤ 0 := by
+  have hweight := (C.pathWeight_le_projectedPathWeight stateAt start length hpath).trans
+    (C.projectedPathWeight_le_potential_sub stateAt start length)
+  rw [hclosed, sub_self] at hweight
+  exact hweight
+
+end RelationalFiniteSignedTransitionPotentialCertificate
+
 namespace FiniteSignedTransitionPotentialCertificate
 
 variable {State Signature : Type*} [Fintype Signature]
 
+/-- The legacy all-pairs certificate is the relational certificate with universal steps. -/
+def toRelational
+    (C : FiniteSignedTransitionPotentialCertificate State Signature) :
+    RelationalFiniteSignedTransitionPotentialCertificate State Signature where
+  Step := fun _ _ => True
+  signature := C.signature
+  actualWeight := C.actualWeight
+  projectedUpperWeight := C.projectedUpperWeight
+  potential := C.potential
+  bound := C.bound
+  actual_le_projected := fun a b _ => C.actual_le_projected a b
+  projected_le_potential_diff := C.projected_le_potential_diff
+  potential_nonneg := C.potential_nonneg
+  potential_le_bound := C.potential_le_bound
+
 /-- Concrete signed weight along `length` successive transitions from `start`. -/
 def pathWeight
     (C : FiniteSignedTransitionPotentialCertificate State Signature)
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlockNormalForm.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlockNormalForm.lean
index 0aebdb5e..6e0135f4 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlockNormalForm.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlockNormalForm.lean
@@ -338,6 +338,15 @@ theorem canonicalBlockNextStartState_eq_terminalCarrier_div_pow_valuation
       2 ^ v2 (canonicalBlockTerminalCarrier n k)
   exact Nat.mul_div_mul_left _ _ (by omega)
 
+/-- If the next canonical block starts at state one, the completed block has no
+outstanding claims.  This names the endpoint-state audit interpretation in the
+canonical-block vocabulary. -/
+theorem canonicalOutstandingClaimQueue_eq_zero_of_canonicalBlockNextStartState_eq_one
+    {n : OddNat} {k : ℕ} (hstate : canonicalBlockNextStartState n k = 1) :
+    canonicalOutstandingClaimQueue n k = 0 := by
+  apply canonicalOutstandingClaimQueue_eq_zero_of_endpointState_eq_one
+  simpa [canonicalBlockNextStartState] using hstate
+
 /-! ## Exact block-drift consequences -/
 
 /-- Complete carry-two claims form a subfamily of the canonical block. -/
@@ -554,11 +563,43 @@ theorem canonicalBlock_bitWidth_le_of_queue_and_burst_bounds
   omega
 
 /-!
-This is the precise two-coordinate conditional bound available at this layer.
-It ranges over every state *inside a named canonical block*.  Promoting it to
-an unqualified all-time orbit theorem requires a separate coverage theorem
-showing that the canonical block family covers every natural orbit index; that
-coverage statement is intentionally not smuggled into the burst argument.
+The canonical blocks form a proved partition of all orbit times.  Therefore
+the preceding block-local estimate is already sufficient for an all-time
+conditional bound; no additional coverage hypothesis belongs in the public
+statement.
+-/
+
+/-- Queue drawup and block burst bounds control the bit width at every orbit time. -/
+theorem orbit_bitWidth_le_of_queue_and_canonicalBlockBurst_bounds
+    {n : OddNat} {C D : ℕ}
+    (hqueue : CanonicalOutstandingClaimQueueUniformUpperBound n C)
+    (hburst : CanonicalBlockBurstUniformUpperBound n D)
+    (i : ℕ) :
+    bitWidth (iterateT i n).1 ≤ bitWidth n.1 + C + D := by
+  rcases existsUnique_mem_canonicalPaymentBlock n i with ⟨k, hik, _⟩
+  have hiIcc : i ∈ Finset.Icc
+      (canonicalBlockStartTime n k) (paymentEndpointSeq n k) := by
+    rw [canonicalPaymentBlock_eq_Icc_universalPaymentBlockStart] at hik
+    simpa [canonicalBlockStartTime_eq_universalPaymentBlockStart] using hik
+  rcases Finset.mem_Icc.mp hiIcc with ⟨hstart, hend⟩
+  let t := i - canonicalBlockStartTime n k
+  have hindex : canonicalBlockStartTime n k + t = i := by
+    simp [t, Nat.add_sub_of_le hstart]
+  have ht : t < canonicalBlockLength n k := by
+    rw [canonicalBlockLength,
+      canonicalPaymentBlockLength_eq_endpoint_sub_start_add_one,
+      ← canonicalBlockStartTime_eq_universalPaymentBlockStart]
+    dsimp [t]
+    omega
+  simpa [hindex] using
+    canonicalBlock_bitWidth_le_of_queue_and_burst_bounds hqueue hburst ht
+
+/-!
+The local theorem remains useful when a caller already has block coordinates.
+The all-time theorem is justified by `existsUnique_mem_canonicalPaymentBlock`:
+every natural orbit index lies in exactly one canonical block.  The result is
+still conditional on two explicit uniform bounds; it does not assert either
+bound unconditionally.
 -/
 
 /-!
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentPositiveBlock.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentPositiveBlock.lean
new file mode 100644
index 00000000..19e4df13
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentPositiveBlock.lean
@@ -0,0 +1,469 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlockNormalForm
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPositiveBlock"
+
+namespace DkMath.Collatz
+
+/-!
+# Positive canonical blocks: pressure or saturation
+
+Claim depths are split at the terminal valuation `v`.  Claims above `v` are
+not merely counted: their exact source times continue beyond depth `v`, giving
+an explicit injection into the local continuation fiber.  The resulting
+cardinality arithmetic isolates one rigid exception to positive pressure.
+-/
+
+/-- Marked claim depths at or below the terminal valuation. -/
+noncomputable def canonicalBlockLowClaimDepths
+    (n : OddNat) (k : ℕ) : Finset ℕ := by
+  classical
+  exact (canonicalPaymentClaimDepths n k).filter fun d =>
+    d ≤ canonicalBlockTerminalValuation n k
+
+/-- Marked claim depths strictly above the terminal valuation. -/
+noncomputable def canonicalBlockHighClaimDepths
+    (n : OddNat) (k : ℕ) : Finset ℕ := by
+  classical
+  exact (canonicalPaymentClaimDepths n k).filter fun d =>
+    canonicalBlockTerminalValuation n k < d
+
+/-- Membership API for low claim depths. -/
+theorem mem_canonicalBlockLowClaimDepths_iff
+    {n : OddNat} {k d : ℕ} :
+    d ∈ canonicalBlockLowClaimDepths n k ↔
+      d ∈ canonicalPaymentClaimDepths n k ∧
+        d ≤ canonicalBlockTerminalValuation n k := by
+  classical
+  simp [canonicalBlockLowClaimDepths]
+
+/-- Membership API for high claim depths. -/
+theorem mem_canonicalBlockHighClaimDepths_iff
+    {n : OddNat} {k d : ℕ} :
+    d ∈ canonicalBlockHighClaimDepths n k ↔
+      d ∈ canonicalPaymentClaimDepths n k ∧
+        canonicalBlockTerminalValuation n k < d := by
+  classical
+  simp [canonicalBlockHighClaimDepths]
+
+/-- Low and high depths partition all marked claim depths. -/
+theorem canonicalPaymentClaimDepths_eq_low_union_high
+    (n : OddNat) (k : ℕ) :
+    canonicalPaymentClaimDepths n k =
+      canonicalBlockLowClaimDepths n k ∪ canonicalBlockHighClaimDepths n k := by
+  classical
+  ext d
+  simp only [Finset.mem_union, mem_canonicalBlockLowClaimDepths_iff,
+    mem_canonicalBlockHighClaimDepths_iff]
+  constructor
+  · intro hd
+    by_cases hdv : d ≤ canonicalBlockTerminalValuation n k
+    · exact Or.inl ⟨hd, hdv⟩
+    · exact Or.inr ⟨hd, by omega⟩
+  · rintro (⟨hd, _⟩ | ⟨hd, _⟩) <;> exact hd
+
+/-- The valuation cut makes the low and high depth families disjoint. -/
+theorem canonicalBlockLowClaimDepths_disjoint_high
+    (n : OddNat) (k : ℕ) :
+    Disjoint (canonicalBlockLowClaimDepths n k)
+      (canonicalBlockHighClaimDepths n k) := by
+  classical
+  apply Finset.disjoint_left.mpr
+  intro d hdLow hdHigh
+  have hlow := (mem_canonicalBlockLowClaimDepths_iff.mp hdLow).2
+  have hhigh := (mem_canonicalBlockHighClaimDepths_iff.mp hdHigh).2
+  omega
+
+/-- Complete scalar claim count is the marked claim-depth cardinality. -/
+theorem canonicalBlockClaimCount_eq_claimDepths_card
+    (n : OddNat) (k : ℕ) :
+    canonicalBlockClaimCount n k = (canonicalPaymentClaimDepths n k).card := by
+  have hdepth := canonicalPaymentClaimDepths_card n k
+  have hclaim := carryTwoPaymentClaimFiberAt_card_eq_growthDebt_card_add_endpoint_card
+    n (paymentEndpointSeq n k)
+      (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)
+  unfold canonicalBlockClaimCount
+  omega
+
+/-- Claim count splits exactly across the terminal-valuation cut. -/
+theorem canonicalBlockClaimCount_eq_low_card_add_high_card
+    (n : OddNat) (k : ℕ) :
+    canonicalBlockClaimCount n k =
+      (canonicalBlockLowClaimDepths n k).card +
+        (canonicalBlockHighClaimDepths n k).card := by
+  rw [canonicalBlockClaimCount_eq_claimDepths_card,
+    canonicalPaymentClaimDepths_eq_low_union_high]
+  exact Finset.card_union_of_disjoint
+    (canonicalBlockLowClaimDepths_disjoint_high n k)
+
+/-- There are at most `v` distinct positive claim depths at or below `v`. -/
+theorem canonicalBlockLowClaimDepths_card_le_terminalValuation
+    (n : OddNat) (k : ℕ) :
+    (canonicalBlockLowClaimDepths n k).card ≤
+      canonicalBlockTerminalValuation n k := by
+  classical
+  have hsubset : canonicalBlockLowClaimDepths n k ⊆
+      Finset.Icc 1 (canonicalBlockTerminalValuation n k) := by
+    intro d hd
+    rcases mem_canonicalBlockLowClaimDepths_iff.mp hd with ⟨hdClaim, hdle⟩
+    exact Finset.mem_Icc.mpr
+      ⟨(mem_canonicalPaymentClaimDepths_iff.mp hdClaim).1, hdle⟩
+  have hcard := Finset.card_le_card hsubset
+  rw [Nat.card_Icc] at hcard
+  omega
+
+/-- Exact signed drift after splitting marked depths at the terminal valuation. -/
+theorem endpointAccountingTerm_eq_high_card_sub_terminalValuation_sub_low_card
+    (n : OddNat) (k : ℕ) :
+    endpointAccountingTerm n k =
+      ((canonicalBlockHighClaimDepths n k).card : ℤ) -
+        (canonicalBlockTerminalValuation n k -
+          (canonicalBlockLowClaimDepths n k).card : ℕ) := by
+  rw [endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount,
+    canonicalBlockCapacityCount_eq_terminalValuation,
+    canonicalBlockClaimCount_eq_low_card_add_high_card]
+  have hlow := canonicalBlockLowClaimDepths_card_le_terminalValuation n k
+  push_cast
+  omega
+
+/-- Positive low-depth cancellation can never make drift exceed the high count. -/
+theorem endpointAccountingTerm_le_highClaimDepths_card
+    (n : OddNat) (k : ℕ) :
+    endpointAccountingTerm n k ≤
+      (canonicalBlockHighClaimDepths n k).card := by
+  rw [endpointAccountingTerm_eq_high_card_sub_terminalValuation_sub_low_card]
+  exact sub_le_self _ (Int.natCast_nonneg _)
+
+/-- A positive block must contain a marked depth above terminal capacity. -/
+theorem canonicalBlockHighClaimDepths_nonempty_of_endpointAccountingTerm_pos
+    {n : OddNat} {k : ℕ} (hpos : 0 < endpointAccountingTerm n k) :
+    (canonicalBlockHighClaimDepths n k).Nonempty := by
+  have hle := endpointAccountingTerm_le_highClaimDepths_card n k
+  apply Finset.card_pos.mp
+  omega
+
+/-! ## High-depth claims inject into continuation pressure -/
+
+/-- A high marked depth's exact source continues beyond terminal valuation. -/
+theorem canonicalPaymentSourceAtDepth_mem_terminalContinuation_of_mem_high
+    {n : OddNat} {k d : ℕ} (hd : d ∈ canonicalBlockHighClaimDepths n k) :
+    canonicalPaymentSourceAtDepth n k d ∈
+      canonicalPaymentBlockContinuationFiber n k
+        (canonicalBlockTerminalValuation n k) := by
+  rcases mem_canonicalBlockHighClaimDepths_iff.mp hd with ⟨hdClaim, hvd⟩
+  rcases mem_canonicalPaymentClaimDepths_iff.mp hdClaim with
+    ⟨hdpos, hdle, _⟩
+  have hrecover : canonicalPaymentSourceAtDepth n k d ∈
+      canonicalPaymentBlockRecoveryFiber n k d :=
+    (mem_canonicalPaymentBlockRecoveryFiber_iff_eq_sourceAtDepth hdpos hdle).2 rfl
+  rcases mem_canonicalPaymentBlockRecoveryFiber_iff.mp hrecover with
+    ⟨hblock, hexact⟩
+  apply mem_canonicalPaymentBlockContinuationFiber_iff.mpr
+  refine ⟨hblock, ?_⟩
+  have hdepth : orbitExactDepth n (canonicalPaymentSourceAtDepth n k d) = d := by
+    simpa [OrbitDepthRecoversExactlyAt, orbitExactDepth] using hexact
+  change canonicalBlockTerminalValuation n k + 1 ≤
+    orbitExactDepth n (canonicalPaymentSourceAtDepth n k d)
+  rw [hdepth]
+  omega
+
+/-- Source-at-depth is injective on valid marked canonical depths. -/
+theorem canonicalPaymentSourceAtDepth_injective_on_claimDepths
+    {n : OddNat} {k d e : ℕ}
+    (hd : d ∈ canonicalPaymentClaimDepths n k)
+    (he : e ∈ canonicalPaymentClaimDepths n k)
+    (hsource : canonicalPaymentSourceAtDepth n k d =
+      canonicalPaymentSourceAtDepth n k e) :
+    d = e := by
+  rcases mem_canonicalPaymentClaimDepths_iff.mp hd with ⟨hdpos, hdle, _⟩
+  rcases mem_canonicalPaymentClaimDepths_iff.mp he with ⟨hepos, hele, _⟩
+  have hdepthD := canonicalPaymentDebtDepth_sourceAtDepth n k d hdpos hdle
+  have hdepthE := canonicalPaymentDebtDepth_sourceAtDepth n k e hepos hele
+  rw [hsource] at hdepthD
+  omega
+
+/-- High-depth claims inject into the continuation fiber at terminal valuation. -/
+theorem canonicalBlockHighClaimDepths_card_le_terminalContinuationFiber_card
+    (n : OddNat) (k : ℕ) :
+    (canonicalBlockHighClaimDepths n k).card ≤
+      (canonicalPaymentBlockContinuationFiber n k
+        (canonicalBlockTerminalValuation n k)).card := by
+  classical
+  apply Finset.card_le_card_of_injOn (canonicalPaymentSourceAtDepth n k)
+  · intro d hd
+    exact canonicalPaymentSourceAtDepth_mem_terminalContinuation_of_mem_high hd
+  · intro d hd e he hsource
+    exact canonicalPaymentSourceAtDepth_injective_on_claimDepths
+      (mem_canonicalBlockHighClaimDepths_iff.mp hd).1
+      (mem_canonicalBlockHighClaimDepths_iff.mp he).1 hsource
+
+/-! ## Exact positive-pressure/saturated-border dichotomy -/
+
+/-- The rigid border case: length just exceeds valuation and every source claims. -/
+def CanonicalSaturatedBorderBlock (n : OddNat) (k : ℕ) : Prop :=
+  canonicalBlockLength n k = canonicalBlockTerminalValuation n k + 1 ∧
+    canonicalBlockClaimCount n k = canonicalBlockLength n k ∧
+      endpointAccountingTerm n k = 1
+
+/-- Saturation gives positive unit drift. -/
+theorem CanonicalSaturatedBorderBlock.drift_pos
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
+    0 < endpointAccountingTerm n k := by
+  rw [h.2.2]
+  norm_num
+
+/-- Saturation lies exactly on the nonpositive-pressure border. -/
+theorem CanonicalSaturatedBorderBlock.pressure_nonpos
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
+    blockPressureContributionInt n k (canonicalBlockTerminalValuation n k) ≤ 0 := by
+  have hvpos : 1 ≤ canonicalBlockTerminalValuation n k := by
+    have hheight := two_le_orbitWindowHeight_paymentEndpointSeq n k
+    rw [canonicalBlock_endpointHeight_eq_terminalValuation_add_one] at hheight
+    omega
+  rw [blockPressureContributionInt_eq]
+  have hLen : canonicalPaymentBlockLength n k =
+      canonicalBlockTerminalValuation n k + 1 := by
+    simpa [canonicalBlockLength] using h.1
+  simp [hvpos, hLen]
+
+/-- Positive drift has either positive terminal-depth pressure or rigid saturation. -/
+theorem positive_blockPressure_or_saturatedBorder_of_endpointAccountingTerm_pos
+    {n : OddNat} {k : ℕ} (hpos : 0 < endpointAccountingTerm n k) :
+    0 < blockPressureContributionInt n k (canonicalBlockTerminalValuation n k) ∨
+      CanonicalSaturatedBorderBlock n k := by
+  by_cases hp : 0 < blockPressureContributionInt n k
+      (canonicalBlockTerminalValuation n k)
+  · exact Or.inl hp
+  · right
+    have hvlt :=
+      canonicalBlockTerminalValuation_lt_length_of_endpointAccountingTerm_pos hpos
+    have hvpos : 1 ≤ canonicalBlockTerminalValuation n k := by
+      by_contra hv
+      have hvzero : canonicalBlockTerminalValuation n k = 0 := by omega
+      rw [hvzero] at hp
+      rw [blockPressureContributionInt_zero] at hp
+      have hL := one_le_canonicalBlockLength n k
+      have hLen : canonicalPaymentBlockLength n k = canonicalBlockLength n k := rfl
+      rw [hLen] at hp
+      omega
+    have hpressure := blockPressureContributionInt_eq n k
+      (canonicalBlockTerminalValuation n k)
+    have hclaimLe := canonicalBlockClaimCount_le_length n k
+    have hdrift := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount n k
+    rw [canonicalBlockCapacityCount_eq_terminalValuation] at hdrift
+    have hL : canonicalBlockLength n k = canonicalBlockTerminalValuation n k + 1 := by
+      have hLen : canonicalPaymentBlockLength n k = canonicalBlockLength n k := rfl
+      rw [hLen] at hpressure
+      simp [hvpos, hvlt.le] at hpressure
+      omega
+    have hclaim : canonicalBlockClaimCount n k = canonicalBlockLength n k := by
+      omega
+    have hone : endpointAccountingTerm n k = 1 := by omega
+    exact ⟨hL, hclaim, hone⟩
+
+/-- Saturation is exactly the positive-drift, nonpositive-pressure branch. -/
+theorem canonicalSaturatedBorderBlock_iff_positive_drift_and_pressure_nonpos
+    (n : OddNat) (k : ℕ) :
+    CanonicalSaturatedBorderBlock n k ↔
+      0 < endpointAccountingTerm n k ∧
+        blockPressureContributionInt n k
+          (canonicalBlockTerminalValuation n k) ≤ 0 := by
+  constructor
+  · intro h
+    exact ⟨h.drift_pos, h.pressure_nonpos⟩
+  · rintro ⟨hpos, hpressure⟩
+    rcases positive_blockPressure_or_saturatedBorder_of_endpointAccountingTerm_pos hpos with
+      hp | hsaturated
+    · omega
+    · exact hsaturated
+
+/-- In a saturated block every positive staircase depth is marked. -/
+theorem CanonicalSaturatedBorderBlock.claimDepths_eq_Icc
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
+    canonicalPaymentClaimDepths n k =
+      Finset.Icc 1 (canonicalBlockLength n k) := by
+  classical
+  apply Finset.eq_of_subset_of_card_le
+  · intro d hd
+    rcases mem_canonicalPaymentClaimDepths_iff.mp hd with ⟨hdpos, hdle, _⟩
+    exact Finset.mem_Icc.mpr ⟨hdpos, hdle⟩
+  · rw [← canonicalBlockClaimCount_eq_claimDepths_card, h.2.1, Nat.card_Icc]
+    have hL := one_le_canonicalBlockLength n k
+    omega
+
+/-! ## Saturated arithmetic normal form -/
+
+/-- Saturated terminal valuation is exactly one below block length. -/
+theorem CanonicalSaturatedBorderBlock.terminalValuation_eq_length_sub_one
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
+    canonicalBlockTerminalValuation n k = canonicalBlockLength n k - 1 := by
+  have hL := one_le_canonicalBlockLength n k
+  have hEq := h.1
+  omega
+
+/-- A saturated endpoint has height exactly equal to its block length. -/
+theorem CanonicalSaturatedBorderBlock.endpointHeight_eq_length
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
+    orbitWindowHeight n (paymentEndpointSeq n k) = canonicalBlockLength n k := by
+  rw [canonicalBlock_endpointHeight_eq_terminalValuation_add_one,
+    h.terminalValuation_eq_length_sub_one]
+  have hL := one_le_canonicalBlockLength n k
+  omega
+
+/-- Every source in a saturated canonical block has upper carry two. -/
+theorem CanonicalSaturatedBorderBlock.carryTwo_of_mem
+    {n : OddNat} {k i : ℕ} (h : CanonicalSaturatedBorderBlock n k)
+    (hi : i ∈ canonicalPaymentBlock n k) :
+    CarryTwoDebtAt n i := by
+  let d := orbitExactDepth n i
+  have hiRecovery : i ∈ canonicalPaymentBlockRecoveryFiber n k d := by
+    apply mem_canonicalPaymentBlockRecoveryFiber_iff.mpr
+    refine ⟨hi, ?_⟩
+    change orbitExactDepth n i = d
+    rfl
+  have hvalid := (canonicalPaymentBlockRecoveryFiber_nonempty_iff n k d).mp
+    ⟨i, hiRecovery⟩
+  have hdClaim : d ∈ canonicalPaymentClaimDepths n k := by
+    rw [h.claimDepths_eq_Icc]
+    exact Finset.mem_Icc.mpr hvalid
+  have hsource : i = canonicalPaymentSourceAtDepth n k d :=
+    (mem_canonicalPaymentBlockRecoveryFiber_iff_eq_sourceAtDepth
+      hvalid.1 hvalid.2).mp hiRecovery
+  have hcarry := (mem_canonicalPaymentClaimDepths_iff.mp hdClaim).2.2
+  simpa [← hsource] using hcarry
+
+/-- Every strict canonical interior has the universal height-one staircase. -/
+theorem CanonicalSaturatedBorderBlock.interior_height_eq_one
+    {n : OddNat} {k i : ℕ} (_h : CanonicalSaturatedBorderBlock n k)
+    (hi : i ∈ Finset.Ico (canonicalBlockStartTime n k)
+      (paymentEndpointSeq n k)) :
+    orbitWindowHeight n i = 1 := by
+  apply orbitWindowHeight_eq_one_of_mem_universalPaymentBlockInterior
+  simpa [canonicalBlockStartTime_eq_universalPaymentBlockStart] using hi
+
+/-- Every strict saturated interior step increases bit width by exactly one. -/
+theorem CanonicalSaturatedBorderBlock.interior_bitWidth_succ_eq_add_one
+    {n : OddNat} {k i : ℕ} (h : CanonicalSaturatedBorderBlock n k)
+    (hi : i ∈ Finset.Ico (canonicalBlockStartTime n k)
+      (paymentEndpointSeq n k)) :
+    bitWidth (iterateT (i + 1) n).1 = bitWidth (iterateT i n).1 + 1 := by
+  have hheight := h.interior_height_eq_one hi
+  have hs : s (iterateT i n) = 1 := by
+    simpa [orbitWindowHeight_eq_s_iterateT] using hheight
+  have hcarry : stateUpperCarry (iterateT i n).1 = 2 := by
+    exact h.carryTwo_of_mem (by
+      rw [canonicalPaymentBlock_eq_Icc_universalPaymentBlockStart]
+      exact Finset.mem_Icc.mpr ⟨
+        (Finset.mem_Ico.mp (by simpa
+          [canonicalBlockStartTime_eq_universalPaymentBlockStart] using hi)).1,
+        (Finset.mem_Ico.mp hi).2.le⟩)
+  have hbalance := bitWidth_T_add_height_eq_bitWidth_add_upperCarry (iterateT i n)
+  rw [iterateT_succ_eq_T_iterateT]
+  rw [hs, hcarry] at hbalance
+  omega
+
+/-- Saturated blocks have exact unit net drift. -/
+theorem CanonicalSaturatedBorderBlock.netDrift_eq_one
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
+    endpointAccountingTerm n k = 1 := h.2.2
+
+/-- Saturated block start and terminal carrier satisfy the exact power normal form. -/
+theorem CanonicalSaturatedBorderBlock.normalForm
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
+    canonicalBlockStartState n k + 1 =
+        2 ^ canonicalBlockLength n k * canonicalBlockOddCore n k ∧
+      v2 (3 ^ canonicalBlockLength n k * canonicalBlockOddCore n k - 1) =
+        canonicalBlockLength n k - 1 := by
+  exact ⟨canonicalBlockStartState_add_one_eq_pow_mul_oddCore n k, by
+    change canonicalBlockTerminalValuation n k = canonicalBlockLength n k - 1
+    exact h.terminalValuation_eq_length_sub_one⟩
+
+/-- The exact saturated terminal two-power divides the terminal carrier. -/
+theorem CanonicalSaturatedBorderBlock.pow_length_sub_one_dvd_terminalCarrier
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
+    2 ^ (canonicalBlockLength n k - 1) ∣ canonicalBlockTerminalCarrier n k := by
+  rw [← h.terminalValuation_eq_length_sub_one]
+  simpa [v2] using
+    (pow_padicValNat_dvd (p := 2) (n := canonicalBlockTerminalCarrier n k))
+
+/-- Saturation is exact: the next power of two does not divide the carrier. -/
+theorem CanonicalSaturatedBorderBlock.not_pow_length_dvd_terminalCarrier
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
+    ¬ 2 ^ canonicalBlockLength n k ∣ canonicalBlockTerminalCarrier n k := by
+  have hL := one_le_canonicalBlockLength n k
+  have hnot := pow_succ_padicValNat_not_dvd
+    (p := 2) (n := canonicalBlockTerminalCarrier n k)
+  have hnot' := hnot (canonicalBlockTerminalCarrier_pos n k).ne'
+  have hval : padicValNat 2 (canonicalBlockTerminalCarrier n k) =
+      canonicalBlockLength n k - 1 := by
+    simpa [canonicalBlockTerminalValuation, v2] using
+      h.terminalValuation_eq_length_sub_one
+  rw [hval] at hnot'
+  simpa [show canonicalBlockLength n k - 1 + 1 = canonicalBlockLength n k by omega]
+    using hnot'
+
+/-- Modulo `2^(L-1)`, the saturated terminal carrier is exactly zero. -/
+theorem CanonicalSaturatedBorderBlock.terminalCarrier_mod_pow_length_sub_one_eq_zero
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
+    canonicalBlockTerminalCarrier n k % 2 ^ (canonicalBlockLength n k - 1) = 0 :=
+  Nat.dvd_iff_mod_eq_zero.mp h.pow_length_sub_one_dvd_terminalCarrier
+
+/-- Modulo `2^L`, the saturated terminal carrier remains nonzero. -/
+theorem CanonicalSaturatedBorderBlock.terminalCarrier_mod_pow_length_ne_zero
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
+    canonicalBlockTerminalCarrier n k % 2 ^ canonicalBlockLength n k ≠ 0 := by
+  exact fun hzero => h.not_pow_length_dvd_terminalCarrier
+    (Nat.dvd_iff_mod_eq_zero.mpr hzero)
+
+/-!
+## Saturated-successor audit and exact stopping point (cp-318)
+
+The dedicated finite audit in
+`python/Collatz/PetalBridge/saturated_block_audit.py` examined 65,536
+consecutive odd roots and 1,280 deterministic random roots up to 1024 bits.
+It found 33,435 saturated blocks.  All observed saturated blocks had length
+two, no two observed saturated blocks were consecutive, and every observed
+saturated run reached a later nonpositive-drift block within five blocks.
+
+The simplest proposed successor rule is false: 1,785 saturated blocks had an
+immediately following block with positive drift.  Consequently this module
+does **not** export
+
+`saturated block -> next block has nonpositive drift`.
+
+The length-two and no-consecutive-saturation patterns remain finite evidence,
+not theorems.  The exact facts proved above stop at the normal form
+
+`x + 1 = 2^L * u` and `v2 (3^L * u - 1) = L - 1`.
+
+To pass this stopping point, a new arithmetic theorem must constrain the next
+canonical block from that normal form, or rule out `L > 2` by combining all
+carry-two inequalities across the exact recurrence.  Existing tail-grammar,
+drift-budget, and delayed-reservoir APIs do not currently accept enough of this
+block-local data to prove either statement.  Adding a successor theorem from
+the finite pattern alone would therefore be an unsound strengthening.
+-/
+
+/-- The non-saturated positive branch carries its dynamic terminal pressure depth. -/
+structure CanonicalPositiveBlockPressureWitness (n : OddNat) where
+  block : ℕ
+  depth : ℕ := canonicalBlockTerminalValuation n block
+  depth_eq : depth = canonicalBlockTerminalValuation n block := by rfl
+  pressure_pos : 0 < blockPressureContributionInt n block depth
+
+/-- A positive non-saturated block produces a block-local pressure witness. -/
+theorem exists_positiveBlockPressureWitness_of_pos_of_not_saturated
+    {n : OddNat} {k : ℕ} (hpos : 0 < endpointAccountingTerm n k)
+    (hnot : ¬ CanonicalSaturatedBorderBlock n k) :
+    ∃ W : CanonicalPositiveBlockPressureWitness n, W.block = k := by
+  rcases positive_blockPressure_or_saturatedBorder_of_endpointAccountingTerm_pos hpos with
+    hp | hsaturated
+  · exact ⟨⟨k, canonicalBlockTerminalValuation n k, rfl, hp⟩, rfl⟩
+  · exact (hnot hsaturated).elim
+
+end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentPrimitiveExcursion.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentPrimitiveExcursion.lean
index 777b48d5..c5cbd429 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentPrimitiveExcursion.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentPrimitiveExcursion.lean
@@ -4,7 +4,7 @@ Released under MIT license as described in the file LICENSE.
 Authors: D. and Wise Wolf.
 -/
 
-import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlockNormalForm
+import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPositiveBlock
 
 #print "file: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPrimitiveExcursion"
 
@@ -44,6 +44,16 @@ def CanonicalPrimitivePositiveDriftExcursion
       (∀ m ∈ Finset.Ico q r, 0 < canonicalWindowDriftInt n q m) ∧
         canonicalWindowDriftInt n q r ≤ 0
 
+/--
+An open positive excursion starts from an empty queue and remains positive
+through the observed block `m`; no future repayment endpoint is assumed.
+-/
+def CanonicalOpenPositiveQueueExcursion
+    (n : OddNat) (q m : ℕ) : Prop :=
+  q ≤ m ∧
+    canonicalOutstandingClaimQueueBefore n q = 0 ∧
+      ∀ t ∈ Finset.Icc q m, 0 < canonicalOutstandingClaimQueue n t
+
 /-- Number of canonical blocks in the closed excursion interval `q..r`. -/
 def canonicalPrimitiveQueueExcursionLength (q r : ℕ) : ℕ :=
   r - q + 1
@@ -218,6 +228,85 @@ theorem canonicalPrimitivePositiveQueueExcursion_right_unique
   · exact (h.2.2.1 r' (Finset.mem_Ico.mpr ⟨Nat.le_of_lt h'.1, hgt⟩)).ne'
       h'.2.2.2
 
+/-! ## Open positive excursions -/
+
+/-- Every positive queue position has an open excursion start. -/
+theorem exists_canonicalOpenPositiveQueueExcursion_of_queue_pos
+    {n : OddNat} {m : ℕ} (hm : 0 < canonicalOutstandingClaimQueue n m) :
+    ∃ q, CanonicalOpenPositiveQueueExcursion n q m := by
+  induction m with
+  | zero =>
+      exact ⟨0, by
+        refine ⟨le_rfl, rfl, ?_⟩
+        intro t ht
+        have : t = 0 := by simpa using ht
+        simpa [this] using hm⟩
+  | succ m ih =>
+      by_cases hzero : canonicalOutstandingClaimQueue n m = 0
+      · refine ⟨m + 1, le_rfl, ?_, ?_⟩
+        · simpa [canonicalOutstandingClaimQueueBefore_succ] using hzero
+        · intro t ht
+          have htEq : t = m + 1 := by
+            rcases Finset.mem_Icc.mp ht with ⟨hlo, hhi⟩
+            omega
+          simpa [htEq] using hm
+      · have hmPos : 0 < canonicalOutstandingClaimQueue n m :=
+          Nat.pos_of_ne_zero hzero
+        rcases ih hmPos with ⟨q, hqle, hbefore, hpositive⟩
+        refine ⟨q, hqle.trans (by omega), hbefore, ?_⟩
+        intro t ht
+        rcases Finset.mem_Icc.mp ht with ⟨hqt, htm⟩
+        rcases htm.eq_or_lt with rfl | hlt
+        · exact hm
+        · exact hpositive t (Finset.mem_Icc.mpr ⟨hqt, by omega⟩)
+
+/-- Two open excursions ending at the same positive position have the same start. -/
+theorem canonicalOpenPositiveQueueExcursion_left_unique
+    {n : OddNat} {q q' m : ℕ}
+    (h : CanonicalOpenPositiveQueueExcursion n q m)
+    (h' : CanonicalOpenPositiveQueueExcursion n q' m) :
+    q = q' := by
+  have hqm := h.1
+  have hq'm := h'.1
+  by_contra hne
+  rcases lt_or_gt_of_ne hne with hlt | hgt
+  · cases q' with
+    | zero => omega
+    | succ q' =>
+        have hpos : 0 < canonicalOutstandingClaimQueue n q' :=
+          h.2.2 q' (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
+        have hzero : canonicalOutstandingClaimQueue n q' = 0 := by
+          simpa [canonicalOutstandingClaimQueueBefore_succ] using h'.2.1
+        omega
+  · cases q with
+    | zero => omega
+    | succ q =>
+        have hpos : 0 < canonicalOutstandingClaimQueue n q :=
+          h'.2.2 q (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
+        have hzero : canonicalOutstandingClaimQueue n q = 0 := by
+          simpa [canonicalOutstandingClaimQueueBefore_succ] using h.2.1
+        omega
+
+/-- Every positive queue position has a unique last-zero open-excursion start. -/
+theorem existsUnique_canonicalOpenPositiveQueueExcursion_of_queue_pos
+    {n : OddNat} {m : ℕ} (hm : 0 < canonicalOutstandingClaimQueue n m) :
+    ∃! q, CanonicalOpenPositiveQueueExcursion n q m := by
+  rcases exists_canonicalOpenPositiveQueueExcursion_of_queue_pos hm with ⟨q, hq⟩
+  exact ⟨q, hq, fun q' hq' => canonicalOpenPositiveQueueExcursion_left_unique hq' hq⟩
+
+/--
+Every positive-drift block observed inside an open excursion is either a
+dynamic-depth pressure block or the rigid saturated border exception.
+-/
+theorem CanonicalOpenPositiveQueueExcursion.positiveBlock_pressure_or_saturated
+    {n : OddNat} {q m k : ℕ}
+    (_hopen : CanonicalOpenPositiveQueueExcursion n q m)
+    (_hk : k ∈ Finset.Icc q m)
+    (hpos : 0 < endpointAccountingTerm n k) :
+    0 < blockPressureContributionInt n k (canonicalBlockTerminalValuation n k) ∨
+      CanonicalSaturatedBorderBlock n k :=
+  positive_blockPressure_or_saturatedBorder_of_endpointAccountingTerm_pos hpos
+
 /-!
 ## Exact remaining obstruction
 
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-318.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-318.md
new file mode 100644
index 00000000..8671943f
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-318.md
@@ -0,0 +1,290 @@
+# cp-318 Implementation Report
+
+## Status
+
+**Completed through the first genuine Stage L obstruction.**
+
+The exact positive-block dichotomy, its saturated arithmetic normal form,
+open positive excursions, and a relational finite-transition certificate are
+now formalized without `sorry`.  A dedicated finite audit also falsified the
+simplest saturated-successor rule.  No universal successor claim was inferred
+from the remaining finite pattern.
+
+## 1. Integration closure
+
+`UniversalPaymentBlockNormalForm.lean` now uses the existing unique canonical
+block coverage theorem to lift two conditional bounds to every orbit time:
+
+```text
+uniform queue bound C
++ uniform canonical-block burst bound D
+-> bitWidth (iterateT i n) <= bitWidth n + C + D
+```
+
+The theorem is conditional only on the two named uniform bounds.  No extra
+coverage assumption is needed because `existsUnique_mem_canonicalPaymentBlock`
+already partitions all natural orbit indices.
+
+The endpoint audit also has a canonical-block-facing public theorem:
+
+```text
+canonicalBlockNextStartState n k = 1
+-> canonicalOutstandingClaimQueue n k = 0
+```
+
+## 2. Low/high claim-depth split
+
+New module:
+
+```text
+DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPositiveBlock
+```
+
+For a canonical block, claim depths are split at terminal valuation `v` into
+the finite sets:
+
+```text
+low  = {d in claims | d <= v}
+high = {d in claims | v < d}
+```
+
+Lean proves that they are disjoint and partition all claim depths, with exact
+cardinality accounting:
+
+```text
+claimCount = low.card + high.card
+low.card <= v
+
+endpointAccountingTerm
+  = high.card - (v - low.card)       -- in Int
+endpointAccountingTerm <= high.card
+```
+
+Therefore positive block drift forces a nonempty high-depth claim family.
+
+## 3. High claims enter continuation fibers
+
+Every high claim depth has a unique canonical source.  Its exact-depth theorem
+places that source in the continuation fiber at terminal depth `v`.
+
+The implementation constructs the explicit finite injection from high claim
+depths into that continuation fiber and proves:
+
+```text
+high.card <= (continuationFiber at v).card
+```
+
+This is block-local and contribution-preserving.  It does not introduce a
+global orbit-time/source-depth identification.
+
+## 4. Exact positive-block dichotomy
+
+`CanonicalSaturatedBorderBlock n k` records exactly:
+
+```text
+L = v + 1
+claimCount = L
+endpointAccountingTerm = 1
+```
+
+The main theorem is now proved:
+
+```text
+0 < endpointAccountingTerm n k
+->
+  0 < blockPressureContributionInt n k v
+  or CanonicalSaturatedBorderBlock n k
+```
+
+The exceptional branch is also characterized bidirectionally:
+
+```text
+CanonicalSaturatedBorderBlock n k
+<->
+  0 < endpointAccountingTerm n k
+  and blockPressureContributionInt n k v <= 0
+```
+
+In a saturated block, all depths in `Finset.Icc 1 L` are claims.  Thus the
+exception is not an unspecified failure case; its finite claim structure is
+fully determined.
+
+## 5. Saturated arithmetic normal form
+
+For every saturated block, Lean proves:
+
+```text
+terminal valuation = L - 1
+endpoint height = L
+every block source has upper carry two
+every strict interior source has height one
+every strict interior step raises bit width by one
+net block drift = 1
+```
+
+The exact arithmetic normal form is:
+
+```text
+x + 1 = 2^L * u
+v2 (3^L * u - 1) = L - 1
+```
+
+The residue boundary is exact as well:
+
+```text
+2^(L-1) divides the terminal carrier
+2^L does not divide the terminal carrier
+```
+
+No logarithmic estimate or asymptotic substitution is used.
+
+## 6. Open positive excursions
+
+`UniversalPaymentPrimitiveExcursion.lean` now defines an open excursion ending
+at an observed positive queue position.  It requires a preceding queue zero
+and positivity through the observed interval, but makes no future repayment
+assumption.
+
+Lean proves:
+
+```text
+positive queue at m
+-> exists unique q, CanonicalOpenPositiveQueueExcursion n q m
+```
+
+The start is the block immediately after the last preceding zero.  Every
+positive-drift block inside such an observed excursion is then decomposed by
+the pressure-or-saturated theorem.  This avoids assuming the still-unproved
+future-zero statement.
+
+## 7. Dynamic pressure witness
+
+`CanonicalPositiveBlockPressureWitness` packages the non-saturated branch with:
+
+- canonical block index;
+- that block's terminal valuation as a dynamic depth;
+- positive pressure at precisely that depth.
+
+The witness is intentionally not converted into one fixed global pressure
+depth.  Existing pressure-separator APIs do not yet provide a proved map that
+preserves these block-local contributions across changing depths.
+
+## 8. Relational finite-transition certificate
+
+`FiniteSignedTransition.lean` now defines
+`RelationalFiniteSignedTransitionPotentialCertificate` with an explicit
+transition relation `Step`.
+
+Only realized edges must satisfy concrete-to-projected soundness.  For every
+finite related path, Lean proves:
+
+```text
+actual path weight <= projected path weight
+projected path weight <= endpoint potential difference
+actual path weight <= finite potential bound
+equal endpoint signatures -> actual path weight <= 0
+```
+
+The former all-pairs certificate remains available and maps to the relational
+one by taking `Step := True`.
+
+The cp-317 signature diagnostics now have a precise interpretation:
+
+- drift collision refutes exact deterministic drift recovery;
+- nondeterministic successors refute a deterministic automaton but not a
+  graph abstraction or sound over-approximation;
+- a realized related positive closed-signature path refutes a bounded
+  potential certificate for that signature.
+
+## 9. Saturated-chain audit
+
+New executable audit and recorded outputs:
+
+```text
+python/Collatz/PetalBridge/saturated_block_audit.py
+python/Collatz/PetalBridge/results/saturated_block_audit_318.json
+python/Collatz/PetalBridge/results/saturated_block_audit_318.md
+```
+
+Range:
+
+- all 65,536 odd roots through `131071`;
+- 1,280 deterministic random odd roots of widths 64, 128, 256, 512, and 1024;
+- random seed `54039`.
+
+Observed results:
+
+| Observation | Result |
+| --- | ---: |
+| saturated blocks | 33,435 |
+| maximum consecutive saturated length | 1 |
+| consecutive saturated pairs | 0 |
+| saturated blocks of length 2 | 33,435 |
+| immediate successor drift nonpositive | 31,650 |
+| immediate successor drift positive | 1,785 |
+| runs lacking a later observed nonpositive block | 0 |
+| maximum blocks to first later nonpositive drift | 5 |
+
+The 1,785 positive immediate successors are counterexamples to the proposed
+rule:
+
+```text
+saturated block -> next block has nonpositive drift
+```
+
+The observed length-two and no-consecutive-saturation patterns are not Lean
+theorems and are not exposed as API claims.
+
+## 10. Exact stopping point
+
+The first genuine Stage L obstruction is saturated successor behavior.
+
+The exact normal form determines the current block, but no existing theorem
+currently turns
+
+```text
+x + 1 = 2^L * u
+v2 (3^L * u - 1) = L - 1
+```
+
+into a stable successor grammar.  In particular, the audit disproves the
+strongest one-step repayment candidate.  Proving either `L = 2`, exclusion of
+consecutive saturation, or a bounded later repayment requires a new arithmetic
+argument controlling the next canonical block from this normal form.
+
+This is the safe endpoint of cp-318.  Returning to queue algebra or enlarging
+the failed low-bit signatures would not address this obstruction.
+
+## 11. Next implementation direction
+
+The next productive experiment should start from the exact saturated normal
+form rather than from another finite signature.  Candidate proof obligations,
+in order, are:
+
+1. derive a next-block normal form directly from `(L,u)`;
+2. test whether simultaneous carry-two inequalities can prove `L = 2`;
+3. if not, seek an exact residue descent that excludes consecutive saturation;
+4. separately design a contribution-preserving aggregator for pressure
+   witnesses whose terminal depths vary by block.
+
+Any new successor theorem must first survive both the exact recurrence and the
+recorded positive-successor counterexamples.
+
+## 12. Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlockNormalForm
+lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPositiveBlock
+lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPrimitiveExcursion
+lake build DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition
+lake build DkMath.Collatz.PetalBridge.FloatWindow
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath
+git diff --check
+```
+
+The four modified/new theorem modules contain no `sorry`.  The top-level build
+continues to report pre-existing `sorry` declarations in unrelated research
+modules; cp-318 introduces none.
diff --git a/python/Collatz/PetalBridge/results/saturated_block_audit_318.md b/python/Collatz/PetalBridge/results/saturated_block_audit_318.md
new file mode 100644
index 00000000..483a2fe9
--- /dev/null
+++ b/python/Collatz/PetalBridge/results/saturated_block_audit_318.md
@@ -0,0 +1,25 @@
+# Saturated Canonical Block Audit (cp-318)
+
+Finite computational evidence only; no universal successor theorem is inferred.
+
+## Range
+
+- exhaustive odd roots: `65536` through `131071`
+- deterministic random roots: `1280` over `(64, 128, 256, 512, 1024)`
+- random seed: `54039`
+
+## Saturated runs
+
+- saturated blocks: `33435`
+- maximum consecutive saturated length: `1`
+- consecutive saturated pairs: `0`
+- saturated length counts: `{2: 33435}`
+- saturated odd-core residues mod 8: `{3: 14619, 7: 18816}`
+- immediate successor drift nonpositive: `31650`
+- immediate successor drift positive: `1785`
+- runs without a later observed nonpositive drift: `0`
+- maximum blocks to first later nonpositive drift: `5`
+
+A positive successor or a consecutive saturated pair refutes the simplest
+`saturated -> next drift <= 0` candidate.  Even a clean finite row would
+remain evidence rather than a Lean theorem.
diff --git a/python/Collatz/PetalBridge/saturated_block_audit.py b/python/Collatz/PetalBridge/saturated_block_audit.py
new file mode 100644
index 00000000..c291e6d5
--- /dev/null
+++ b/python/Collatz/PetalBridge/saturated_block_audit.py
@@ -0,0 +1,184 @@
+#!/usr/bin/env python3
+"""cp-318 finite audit of consecutive saturated canonical blocks.
+
+This script tests the rigid exception isolated by Lean:
+
+    L = v + 1, claims = L, drift = 1.
+
+It records successor data and repayment behavior over the same exhaustive and
+deterministic random root families as the cp-317 normal-form audit.  Results
+are computational evidence only; they do not establish a universal successor
+grammar.
+"""
+
+from __future__ import annotations
+
+import json
+import random
+from collections import Counter
+from pathlib import Path
+
+from canonical_block_normal_form_audit import (
+    EXHAUSTIVE_MAX,
+    RANDOM_PER_WIDTH,
+    RANDOM_SEED,
+    RANDOM_WIDTHS,
+    block_trace,
+    odd_with_exact_width,
+)
+
+
+def saturated(block: dict[str, int]) -> bool:
+    return (
+        block["length"] == block["terminal_valuation"] + 1
+        and block["claims"] == block["length"]
+        and block["drift"] == 1
+    )
+
+
+def audit_traces(traces: list[list[dict[str, int]]]) -> dict[str, object]:
+    saturated_count = 0
+    maximum_run = 0
+    transition_counter: Counter[tuple[int, ...]] = Counter()
+    successor_positive = 0
+    successor_nonpositive = 0
+    consecutive_pairs = 0
+    runs_without_later_nonpositive = 0
+    maximum_blocks_to_nonpositive = 0
+    first_two_consecutive = None
+    saturated_lengths: Counter[int] = Counter()
+    saturated_core_mod_8: Counter[int] = Counter()
+
+    for blocks in traces:
+        i = 0
+        while i < len(blocks):
+            if not saturated(blocks[i]):
+                i += 1
+                continue
+            start = i
+            while i < len(blocks) and saturated(blocks[i]):
+                saturated_count += 1
+                saturated_lengths[blocks[i]["length"]] += 1
+                saturated_core_mod_8[blocks[i]["core"] % 8] += 1
+                if i + 1 < len(blocks):
+                    nxt = blocks[i + 1]
+                    transition_counter[
+                        (
+                            blocks[i]["length"],
+                            blocks[i]["core"] % 256,
+                            nxt["length"],
+                            nxt["terminal_valuation"],
+                            nxt["drift"],
+                        )
+                    ] += 1
+                    if nxt["drift"] <= 0:
+                        successor_nonpositive += 1
+                    else:
+                        successor_positive += 1
+                    if saturated(nxt):
+                        consecutive_pairs += 1
+                        if first_two_consecutive is None:
+                            first_two_consecutive = {
+                                "root_start_state": blocks[0]["start_state"],
+                                "left_block": blocks[i],
+                                "right_block": nxt,
+                            }
+                i += 1
+
+            run_length = i - start
+            maximum_run = max(maximum_run, run_length)
+            repayment = next(
+                (j for j in range(i, len(blocks)) if blocks[j]["drift"] <= 0),
+                None,
+            )
+            if repayment is None:
+                runs_without_later_nonpositive += 1
+            else:
+                maximum_blocks_to_nonpositive = max(
+                    maximum_blocks_to_nonpositive, repayment - i + 1
+                )
+
+    most_common = [
+        {
+            "length": key[0],
+            "core_mod_256": key[1],
+            "next_length": key[2],
+            "next_terminal_valuation": key[3],
+            "next_drift": key[4],
+            "count": count,
+        }
+        for key, count in transition_counter.most_common(40)
+    ]
+    return {
+        "saturated_blocks": saturated_count,
+        "maximum_consecutive_saturated_length": maximum_run,
+        "consecutive_saturated_pairs": consecutive_pairs,
+        "saturated_successor_nonpositive_drift": successor_nonpositive,
+        "saturated_successor_positive_drift": successor_positive,
+        "runs_without_observed_later_nonpositive_drift": runs_without_later_nonpositive,
+        "maximum_blocks_to_first_nonpositive_drift_after_run": maximum_blocks_to_nonpositive,
+        "first_two_consecutive_saturated": first_two_consecutive,
+        "saturated_length_counts": dict(sorted(saturated_lengths.items())),
+        "saturated_core_mod_8_counts": dict(sorted(saturated_core_mod_8.items())),
+        "most_common_transitions": most_common,
+    }
+
+
+def main() -> None:
+    exhaustive_roots = list(range(1, EXHAUSTIVE_MAX + 1, 2))
+    rng = random.Random(RANDOM_SEED)
+    random_roots = [
+        odd_with_exact_width(rng, width)
+        for width in RANDOM_WIDTHS
+        for _ in range(RANDOM_PER_WIDTH)
+    ]
+    traces = [block_trace(root) for root in exhaustive_roots + random_roots]
+    result = {
+        "checkpoint": 318,
+        "exhaustive_odd_roots": len(exhaustive_roots),
+        "exhaustive_max": EXHAUSTIVE_MAX,
+        "random_seed": RANDOM_SEED,
+        "random_roots": len(random_roots),
+        "random_widths": list(RANDOM_WIDTHS),
+        **audit_traces(traces),
+    }
+
+    output_dir = Path(__file__).with_name("results")
+    output_dir.mkdir(parents=True, exist_ok=True)
+    json_path = output_dir / "saturated_block_audit_318.json"
+    md_path = output_dir / "saturated_block_audit_318.md"
+    json_path.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
+
+    lines = [
+        "# Saturated Canonical Block Audit (cp-318)",
+        "",
+        "Finite computational evidence only; no universal successor theorem is inferred.",
+        "",
+        "## Range",
+        "",
+        f"- exhaustive odd roots: `{len(exhaustive_roots)}` through `{EXHAUSTIVE_MAX}`",
+        f"- deterministic random roots: `{len(random_roots)}` over `{RANDOM_WIDTHS}`",
+        f"- random seed: `{RANDOM_SEED}`",
+        "",
+        "## Saturated runs",
+        "",
+        f"- saturated blocks: `{result['saturated_blocks']}`",
+        f"- maximum consecutive saturated length: `{result['maximum_consecutive_saturated_length']}`",
+        f"- consecutive saturated pairs: `{result['consecutive_saturated_pairs']}`",
+        f"- saturated length counts: `{result['saturated_length_counts']}`",
+        f"- saturated odd-core residues mod 8: `{result['saturated_core_mod_8_counts']}`",
+        f"- immediate successor drift nonpositive: `{result['saturated_successor_nonpositive_drift']}`",
+        f"- immediate successor drift positive: `{result['saturated_successor_positive_drift']}`",
+        f"- runs without a later observed nonpositive drift: `{result['runs_without_observed_later_nonpositive_drift']}`",
+        f"- maximum blocks to first later nonpositive drift: `{result['maximum_blocks_to_first_nonpositive_drift_after_run']}`",
+        "",
+        "A positive successor or a consecutive saturated pair refutes the simplest",
+        "`saturated -> next drift <= 0` candidate.  Even a clean finite row would",
+        "remain evidence rather than a Lean theorem.",
+    ]
+    md_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
+    print(json.dumps(result, indent=2))
+
+
+if __name__ == "__main__":
+    main()
````
`````
