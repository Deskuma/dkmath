# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.FloatWindow.FiniteReflectedQueue

gch: 9541640cb829973b216f10c000931a4ca9107fd3

## Report

### take-1

(23m17s)

cp-324 を完了しました。レポートは [report-petal-324.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-324.md) にあります。

主な確定事項:

- 汎用 Nat 反射キューと有限 Lindley 恒等式を新設
- unordered residual は causal queue 以下
- 早すぎる service は未来の arrival を支払えない反例を固定
- queue zero と suffix Hall 条件、forward matching が同値
- 固定深さの drift arrival と exact-length service を実装
- actual source time を保持した forward matching と queue zero が同値
- 全深さ residual carrier は、深さごとに独立な causal queue carrier へ埋め込み可能
- 正・非飽和かつ terminal valuation ≥ 2 なら、drift に加えて最低一つの selected incidence が余る

正直な停止境界も明確です。未解決なのは zero-drift successor、terminal valuation 1、深さをまたぐ service 共有です。今回の結果から cross-depth repayment はまだ導けません。

検証済み:

- `lake build DkMath.Collatz.PetalBridge.FloatWindow.FiniteReflectedQueue`
- `lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentScalarQueue`
- `lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude`
- `lake build DkMath.Collatz.PetalBridge.FloatWindow`
- `lake build DkMath.Collatz.PetalBridge`
- `git diff --check`
- 変更した Lean ファイルに `sorry` なし

### take-2

エラー修正

(5m19s)

修正完了です。

- `selectedPressureBucketWindowEmbedding` と `maxHeartbeats 800000` を削除
- 同じ cardinality 上界を blockwise sum と `Finset.sum_le_sum_of_subset` で証明
- `UniversalPaymentAmplitude` のビルド時間を約70秒から約10秒へ短縮
- `card_canonicalSelectedDriftImageCarrierAtDepth` の inactive branch を明示的な矛盾除去で修正
- all-depth carrier の `Fintype` 問題を修正
- `Int.toNat` と spare-incidence 証明の型不一致を修正

検証結果:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude  OK
lake build DkMath.Collatz.PetalBridge.FloatWindow                           OK
lake build DkMath.Collatz.PetalBridge                                       OK
lake build DkMath                                                           OK
git diff --check                                                            OK
```

変更対象の Lean ファイルには `sorry` がなく、重い embedding も残っていません。

現在、一部ファイルが `MM` / `AM`、つまりステージ後に追加修正された状態です。コミット前に改めて `git add` が必要です。

## Review

## 結論

**全面採用。causal queue 層は完成じゃ。**

cp-324 は、これまで別々だった、

- unordered residual
- scalar outstanding queue
- fixed-depth selected arrivals
- exact-length service
- source-bearing forward matching

を、汎用有限 Lindley queue の上で統一した。

中心成果は次の同値である。

$$
Q_{q,m}=0 \iff \forall t\in[q,m],\ \sum_{k=t}^{m}a_k\le\sum_{k=t}^{m}s_k \iff \text{forward temporal matching exists}
$$

さらに固定深さへ特殊化し、

$$
\text{depth queue}=0 \iff \text{実 source incidence を保持する未来向き matching が存在}
$$

まで閉じた。

これにより、cp-323 の unordered residual と causal outstanding debt の差は、完全に Lean 上で固定された。

ただし、次の三点を補強すべきじゃ。

1. `q > m` における generic queue の定義が、空区間ではなく block `q` を一件処理してしまう。
2. all-depth embedding は cardinality から選ばれたため、depth coordinate を保存しない。
3. 次の問題は「cross-depth sharing」ではなく、**一個の高 depth service を重複なく低 depth 資源へ変換できるか**という depth-denomination conversion である。

---

## 1. Generic reflected queue

新しい、

```lean
finiteReflectedQueueFrom
finiteReflectedQueueOn
finiteSignedWindowBalance
```

は、Collatz 固有語彙を含まない汎用 API として正しく切り出されている。

反射キューの再帰は、

$$
Q_{t+1}=(Q_t+a_t)\mathbin{\stackrel{.}{-}}s_t\qquad (\text{dot minus:}\stackrel{.}{-})
$$

じゃ。

そして有限窓では、

$$
Q_{q,m}=\max_{q\le t\le m}\left(\sum_{k=t}^{m}(a_k-s_k)\right)_+
$$

が証明された。

この形は正確な Lindley reflection であり、cp-316 の scalar queue で得ていた内容が、任意の `arrivals` / `service` 列へ一般化された。

特に、

```lean
finiteReflectedQueueOn_eq_zero_or_exists_suffix
```

により、queue が正なら、その値を実現する suffix が実際に存在する。

単なる上界ではなく、最大悪区間が witness を持つところまで閉じている。

---

## 2. Early-service regression

今回の意味論上、最も重要な regression はこれじゃ。

```text
block 0:
  arrival = 0
  service = 1

block 1:
  arrival = 1
  service = 0
```

全体の unordered balance は、

$$
(0-1)+(1-0)=0
$$

なので unordered residual は $0$。

しかし causal queue は、

$$
Q_0=0,\qquad Q_1=1
$$

となる。

したがって、

$$
R^{\mathrm{unordered}}=0<1=Q^{\mathrm{causal}}
$$

じゃ。

この regression によって、

> 過去の余った service を、未来の arrival へ勝手に回してはならない

という意味境界がコードに固定された。

これは今後も残すべき重要な反例じゃ。

---

## 3. Generic Hall theorem

```lean
FiniteArrivalWindowCarrier
FiniteServiceWindowCarrier
FiniteForwardWindowMatching
```

により、arrival と service が block address を保持する有限 carrier になった。

eligibility は、

$$
\operatorname{claimBlock}\le\operatorname{serviceBlock}
$$

である。

そして、

```lean
finiteForwardWindowMatching_iff_suffix_sum_le
finiteReflectedQueueOn_eq_zero_iff_forwardWindowMatching
```

によって、

- 全 suffix Hall 条件
- forward injection
- queue zero

が完全に同値になった。

Hall の逆向き証明も正しい。

任意の claim subset から最小 release block $t$ を選び、その subset 全体を suffix $t,\ldots,m$ の claims へ入れ、suffix service 全体を近傍へ入れる。

interval-order 特有の nested neighborhood を使った、鋭い有限 Hall reductionじゃ。

---

## 4. 空区間 API の注意

ここだけは早めに補強した方がよい。

現在、

```lean
def finiteReflectedQueueOn
    (arrivals service : ℕ → ℕ) (q m : ℕ) : ℕ :=
  finiteReflectedQueueFrom arrivals service q (m - q + 1)
```

なので、$q>m$ のときにも、

$$
m-q=0
$$

となり、長さ $1$ として block $q$ を一件処理する。

一方、

```lean
finiteSignedWindowBalance arrivals service q m
```

は `Finset.Icc q m` が空なので $0$ になる。

したがって $q>m$ では、

```text
queue:
  block q を一件処理

signed window:
  空区間
```

という意味の不一致がある。

現在の主 theorem は全て `q ≤ m` を仮定しているため数学的誤りはない。

しかし generic API としては危険じゃ。

次のいずれかを早めに行うべきである。

```lean
def finiteReflectedQueueOnIcc
    (arrivals service : ℕ → ℕ) (q m : ℕ) : ℕ :=
  if q ≤ m then
    finiteReflectedQueueFrom arrivals service q (m - q + 1)
  else
    0
```

または現在の定義を、

```text
finiteReflectedQueueOnNonempty
```

相当の内部 API として位置づけ、空区間を正しく扱う public wrapper を置く。

---

## 5. Scalar queue との統合

既存の、

```lean
canonicalLocalOutstandingClaimQueue
```

が、

```lean
finiteReflectedQueueOn
    (canonicalBlockClaimCount n)
    (canonicalBlockCapacityCount n)
```

と一致することが証明された。

これは良い refactor じゃ。

既存 theorem 名を壊さず、generic API の instance として読み直している。

つまり scalar queue は独立した特別理論ではなく、

> claim count を arrivals、capacity count を service とした Lindley queue

であったことが正式に確定した。

---

## 6. Proof-independent fixed-depth arrivals

固定深さ $d$ の arrival 数は、

```lean
canonicalSelectedDriftArrivalCountAtDepth n k d
```

として、

- positive drift
- nonsaturated
- selected depth が $d$

の場合だけ `Int.toNat drift` を返す。

重要なのは、この数値定義が classically chosen source image を参照していないことじゃ。

$$
a_k(d)=
\begin{cases}
D_k&\text{positive nonsaturated かつ selectedDepth}=d\
0&\text{otherwise}
\end{cases}
$$

その後、

```lean
card_canonicalSelectedDriftImageCarrierAtDepth
```

によって、実 source image の cardinality がこの proof-independent arrival 数に一致すると示している。

この順序は正しい。

```text
数値 queue:
  choice 非依存

source-bearing matching:
  choice により実在 source を代表
```

と層が分離されている。

---

## 7. Exact-length service

固定深さ $d$ の service は、

```lean
canonicalExactLengthServiceAtDepth n k d :=
  if canonicalPaymentBlockLength n k = d then 1 else 0
```

じゃ。

したがって block $k$ は、その length $L_k$ においてだけ一個の service を持つ。

$$
s_k(d)=\mathbf1_{L_k=d}
$$

全 block window で足すと、既存の exact-length index carrier の cardinalityに一致する。

これにより cp-321 の exact-length token が、causal service 列へ正しく昇格した。

---

## 8. Fixed-depth causal queue

新しい、

```lean
canonicalSelectedDriftDepthQueue n q m d
```

は、

$$
Q_{q,m}(d)=\max_{q\le t\le m}\left(\sum_{k=t}^{m}a_k(d)-\sum_{k=t}^{m}s_k(d)\right)_+
$$

を表す。

そして、

$$
R_{q,m}^{\mathrm{unordered}}(d)\le Q_{q,m}(d)
$$

が証明された。

これは cp-323 の実 residual carrierを causal queue と同一視せず、cardinality だけ比較している。

意味境界は完全に正しい。

---

## 9. Source-bearing temporal matching

```lean
CanonicalSelectedDriftArrivalWindowCarrier
```

は、

- release block
- selected source time
- selected depth

を保持する。

これを proof-independent な `Fin arrivalCount` carrierへ block-preserving に同値変換し、generic Hall theoremを引き戻している。

その結果、

$$
Q_{q,m}(d)=0 \iff \text{固定深さ }d\text{ の全 source claims に未来向き matching が存在}
$$

となった。

ここで service 側は exact-length block token だが、claim 側は実際の source time を失っていない。

これで fixed-depth causal repayment 層は完成と見てよい。

---

## 10. All-depth carrier の補正

現在の cardinality theorem、

```lean
natCard_allDepthActualResidual_le_causalQueueCarrier
```

は正しい。

各 depth について、

$$
|\operatorname{Residual}(d)|\le Q(d)
$$

を足しているからじゃ。

ただし、

```lean
exists_allDepthActualResidualEmbedding_causalQueueCarrier
```

は総 cardinality inequality から一個の arbitrary embedding を選んでいる。

したがって、その embedding は、

$$
\operatorname{depth}(\operatorname{image}(x))=\operatorname{depth}(x)
$$

を保証しない。

target 自体は depth-indexed sigma だが、写像が depth を保存するとは限らない。

これは次のように、depthwise embedding を `sigmaMap` で組み立てれば直せる。

```lean
noncomputable def allDepthActualResidualCausalQueueEmbedding
    (n : OddNat) {q m : ℕ} (hqm : q ≤ m) :
    CanonicalAllDepthActualSelectedDriftResidualCarrier n q m ↪
      CanonicalAllDepthSelectedDriftCausalQueueCarrier n q m :=
  (Function.Embedding.refl _).sigmaMap fun d =>
    Classical.choice
      (Function.Embedding.nonempty_iff_card_le.mpr <|
        by
          rw [natCard_actualSelectedDriftResidualCarrier]
          exact canonicalUnorderedSelectedDriftResidualCount_le_depthQueue
            n hqm)
```

さらに、

```lean
@[simp] theorem allDepthActualResidualCausalQueueEmbedding_fst ... :
    (... x).1 = x.1 := rfl
```

を置くべきじゃ。

既存の存在 theorem は compatibility surface として残せばよい。

---

## 11. 「Cross-depth sharing」ではなく「depth conversion」

現在の all-depth queue は、

$$
\bigsqcup_d Q(d)
$$

という独立 queue の束である。

一つの exact-length block $k$ は、

$$
d=L_k
$$

にだけ service を一件供給する。

したがって、同一 service が複数 depth で重複計上されているわけではない。

未証明なのは sharing ではなく、

> depth $L$ の一個の service を、保存則を守って低い depth の複数 unit へ変換できるか

という **denomination conversion** じゃ。

ここは用語を修正した方がよい。

```text
cross-depth sharing:
  同じ token を複数回使うように聞こえるため不適切

cross-depth conversion:
  一個の高 depth 資源を、保存則つきで低 depth 資源へ変換する
```

現在の matching theorem は conversion を一切許していない。

したがって、独立 depth queue の和は安全な上界だが、実際より大きい可能性がある。

---

## 12. Spare-incidence theorem

今回、

```lean
intToNat_endpointAccountingTerm_add_one_le_selectedPressureCarrier_card
```

によって、positive nonsaturated block かつ terminal valuation $v\ge2$ なら、

$$
D_k+1\le|\operatorname{SelectedCarrier}_k|
$$

が証明された。

つまり successor 自身の drift image を確保しても、一件以上の source incidence が余る。

これは saturated predecessor の $+1$ token を charge する候補になる。

ただし現状は cardinality inequality だけじゃ。

次には実 source carrier として、

```lean
canonicalSelectedDriftSpareCarrier n k :=
  selected carrier \ selected drift image
```

を定義し、

$$
1\le|\operatorname{SpareCarrier}_k|
$$

を示すべきじゃ。

そうすれば saturated token を actual source incidence へ送る局所 embedding を作れる。

---

## 13. 未解決枝はさらに狭められる

report では、

- zero-drift successor
- positive successor with terminal valuation $1$

が未解決とされている。

しかし、真の no-spare case はさらに狭い。

### Positive、nonsaturated、$v=1$

このとき selected depth は $1$ で、

$$
|\operatorname{SelectedCarrier}|=L-2
$$

また、

$$
D=A-1
$$

じゃ。

したがって spare が存在しないのは、

$$
D=|\operatorname{SelectedCarrier}|
$$

すなわち、

$$
A=L-1
$$

の場合だけである。

よって unresolved branch は単なる $v=1$ ではなく、

> terminal valuation $1$ かつ claim count が length より一だけ小さい、near-saturated tight block

じゃ。

### Zero drift

zero drift なら、

$$
A=v
$$

じゃ。

drift image は空なので selected carrier が一件でもあれば、その全てが spare になる。

したがって unresolved なのは、

$$
|\operatorname{SelectedCarrier}|=0
$$

の場合だけじゃ。

これも length / valuation の境界条件へ落とせる。

次 checkpoint では broad な `zero drift` 全体ではなく、この **zero-carrier balanced border** だけを解剖すべきである。

---

## 14. 一歩先の depth-transfer 不等式

cp-324 から、興味深い新しい保存候補が見える。

positive nonsaturated block の、

- selected depth を $d$
- block length を $L$
- positive drift を $D$

とする。

既に、

$$
d+2\le L
$$

および、

$$
D\le L-d-1
$$

がある。

$g=L-d\ge2$ と置けば、

$$
D\le g-1\le2^{g-1}
$$

なので、

$$
D,2^d\le2^{L-1}
$$

が得られる。

saturated block では、

$$
L=2,\qquad D=1
$$

であり、token を depth $1$ と読めば、

$$
1\cdot2^1=2^{2-1}
$$

となる。

したがって全 positive block に対し、概念的には、

$$
\text{lower-depth drift mass}\le\text{one block-length dyadic budget}
$$

が成り立つ可能性がある。

これはまだ causal conversion theorem ではない。

しかし、

> 高い depth の一単位を、低い depth の複数 unit へ非重複で分解する

ための potential inequality として非常に有望じゃ。

pressure の `Pow2` 層、eventually-zero upper boundary、bit-width budget へ接続する候補になる。

---

## 15. Challenge 命題への現在地

最終出口は、

```lean
theorem collatz_conjecture (n : ℕ) (hn : n > 0) :
  ∃ m, collatzStep^[m] n = 1
```

じゃ。

cp-324 は収束そのものではない。

しかし positive drift の会計は、ここまで進んだ。

```text
positive drift
  ↓
actual same-block source incidence
  ↓
fixed-depth arrivals
  ↓
causal reflected queue
  ↓
suffix Hall condition
  ↓
source-bearing future matching
```

つまり、局所 pressure の借金について、

> 何個残っているか
> なぜ過去の service では払えないか
> いつ全て未来 service へ割り当てられるか

が完全に形式化された。

---

## 判定まとめ

### Generic Lindley queue

**完成。**

### Early-service obstruction

**完成。意味論上の重要 regression。**

### Generic temporal Hall theorem

**完成。**

### Scalar queue specialization

**完成。既存 API を維持。**

### Fixed-depth causal queue

**完成。**

### Source-bearing forward matching

**完成。**

### All-depth cardinal comparison

**完成。**

### All-depth depth-preserving embedding

**未実装。現在の存在 embedding は depth を保存しない。**

### Saturated successor charge

**$v\ge2$ の spare cardinality まで完成。actual spare carrier は未実装。**

### 真の次戦線

**tight no-spare successor と sound な depth conversion。**

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge FloatWindow branch after
report-petal-324.

The cp-324 implementation is accepted.

The causal layer is complete:

    generic finite Lindley reflection;
    suffix-maximum identity;
    early-service obstruction;
    interval-order Hall equivalence;
    fixed-depth selected-drift queue;
    source-bearing forward matching.

The next checkpoint must first repair two API boundaries, then isolate the
exact no-spare successor classes.  Do not treat cross-depth conversion as
token sharing.

# Stage A — total empty-window semantics

The current definition

    finiteReflectedQueueOn arrivals service q m

processes one index when `m < q`, while `Finset.Icc q m` is empty.

Add a total closed-interval wrapper:

    finiteReflectedQueueOnIcc arrivals service q m :=
      if q <= m then
        finiteReflectedQueueFrom arrivals service q (m - q + 1)
      else
        0.

Prove:

    q <= m ->
      finiteReflectedQueueOnIcc = finiteReflectedQueueOn;

    m < q ->
      finiteReflectedQueueOnIcc = 0;

    finiteReflectedQueueOnIcc = 0
      <->
    every suffix in the possibly-empty window is nonpositive.

Keep the existing nonempty-window definition for compatibility.

Document that all current Collatz specializations use `q <= m`.

# Stage B — depth-preserving all-depth embedding

Construct an explicit sigma-map embedding:

    allDepthActualResidualCausalQueueEmbedding

from:

    CanonicalAllDepthActualSelectedDriftResidualCarrier

to:

    CanonicalAllDepthSelectedDriftCausalQueueCarrier.

Build it depthwise from:

    natCard_actualSelectedDriftResidualCarrier
    canonicalUnorderedSelectedDriftResidualCount_le_depthQueue.

Prove definitionally:

    image depth = source depth.

Keep the existing cardinality-only existence theorem as a compatibility
surface.

# Stage C — actual spare selected carrier

Define:

    canonicalSelectedDriftSpareCarrier n k

as the complement of:

    canonicalSelectedDriftImageCarrier n k

inside:

    canonicalSelectedPressureCarrier n k.

Prove on every positive nonsaturated block:

    selected carrier card
      =
    drift image card + spare carrier card.

For terminal valuation at least two prove:

    spare carrier is nonempty.

Construct an explicit embedding:

    Fin 1 -> spare carrier.

Do not yet call this a repayment slot; call it a spare selected incidence.

# Stage D — exact positive valuation-one no-spare classification

Assume:

    positive drift;
    nonsaturated;
    terminal valuation = 1.

Prove:

    spare carrier is empty
      <->
    canonicalBlockClaimCount n k
      = canonicalBlockLength n k - 1.

Equivalently isolate the tight class:

    CanonicalTightValuationOnePositiveBlock n k.

Expose its exact data:

    terminal valuation = 1;
    selected depth = 1;
    claim count = length - 1;
    drift = length - 2;
    selected carrier card = length - 2;
    no spare incidence.

# Stage E — exact zero-drift no-spare classification

Assume:

    endpointAccountingTerm n k = 0.

Then:

    claim count = terminal valuation.

Classify exactly when:

    canonicalSelectedPressureCarrier n k = empty.

Separate at least:

    terminal valuation = 1;
    terminal valuation >= 2.

Define a rigid predicate for the remaining zero-carrier balanced border.

Do not leave all zero-drift blocks unresolved: any zero-drift block with a
nonempty selected carrier already supplies a spare incidence because its drift
image is empty.

# Stage F — saturated successor refinement

For a saturated block k, classify successor k + 1 into:

    negative drift;
    zero drift with nonempty spare;
    zero-carrier balanced border;
    positive nonsaturated with terminal valuation >= 2;
    tight positive terminal-valuation-one block.

Prove a source-bearing saturated-token charge in the two easy branches:

    zero drift with nonempty selected carrier;
    positive nonsaturated terminal valuation >= 2.

The target must be an actual successor source incidence.

Do not count a nonpositive integer drift alone as an incidence.

# Stage G — focused successor audit

Audit only the two rigid no-spare successor classes:

    zero-carrier balanced border;
    tight valuation-one positive block.

Record:

    predecessor saturated core residue;
    successor block length;
    successor terminal valuation;
    claim count;
    following block length and drift;
    first later spare incidence or negative repayment.

Seek a finite exact grammar, not a broad statistical bound.

# Stage H — dyadic depth-transfer potential

Add an experimental, clearly separated section.

For a positive nonsaturated block with selected depth d and length L, prove:

    Int.toNat drift <= L - d - 1

and then:

    Int.toNat drift * 2^d <= 2^(L - 1).

For a saturated block prove:

    1 * 2^1 = 2^(2 - 1).

Package these as a local dyadic budget theorem.

Interpretation:

    one block-length denomination has enough numerical mass to dominate the
    lower-depth positive-drift units generated by that block.

This is a potential inequality only.  It is not yet a cross-depth matching or
causal repayment theorem.

# Stage I — conversion, not sharing

Design a candidate cross-depth conversion relation in which:

    one service token at depth L

may be converted into lower-depth units subject to one conserved dyadic budget.

The same token must never be reused at two depths.

Before implementing a global matcher, determine whether the conversion should
be represented by:

    a finite binary refinement tree;
    weighted Hall capacity;
    or a monotone potential certificate.

Stop if no representation preserves both:

    temporal order;
    nonduplication.

# Stage J — pressure and upper-boundary bridge

Compare the dyadic budget with existing:

    orbitWindowRetentionMassPow2;
    continuation/recovery sibling layers;
    eventually-zero upper-bit boundary;
    fixed-width upper-carry budget.

Seek an exact theorem connecting depth denomination `2^d` to an actual bit
position or finite boundary resource.

Do not infer this connection from the notation `Pow2` alone; those existing
mass definitions count residue incidences rather than weighted mass.

# Stage K — report boundary

Record explicitly:

    all current fixed-depth queues are exact and causal;

    the all-depth sum is conservative because no depth conversion is allowed;

    cross-depth conversion may lower the total outstanding queue, but requires
    a new nonduplicating resource semantics;

    the only immediate saturated-successor obstructions are the rigid no-spare
    classes isolated above.

Stop at the first genuine obstruction among:

    empty-window totalization breaks compatibility;
    depth-preserving sigma embedding cannot be assembled;
    spare source complement cannot be made finite;
    valuation-one no-spare is not equivalent to near-full claims;
    zero-drift no-spare has no rigid characterization;
    saturated successors can remain indefinitely inside no-spare classes;
    dyadic conversion cannot preserve temporal order and nonduplication.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-325.md
```

cp-324 で、時間の矢は入った。

次は depth を越えるときにも、**一個の資源を二度使わない保存則**を見つける番じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
index 3276dcc0..bc18ca77 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
@@ -18,6 +18,7 @@ import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentFamily
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPressure
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentRepayment
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentDepthLedger
+import DkMath.Collatz.PetalBridge.FloatWindow.FiniteReflectedQueue
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentScalarQueue
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlockNormalForm
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPositiveBlock
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteReflectedQueue.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteReflectedQueue.lean
new file mode 100644
index 00000000..eac49dd0
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteReflectedQueue.lean
@@ -0,0 +1,499 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import Mathlib.Combinatorics.Hall.Basic
+import Mathlib.Algebra.BigOperators.Group.Finset.Basic
+import Mathlib.Data.Finset.Interval
+import Mathlib.Tactic
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.FiniteReflectedQueue"
+
+namespace DkMath.Collatz
+
+/-!
+# Generic finite reflected queue
+
+This module is independent of orbit and Collatz definitions.  It separates a
+causal, recursively reflected queue from the unordered positive part of total
+signed balance.  Arrivals and service are anonymous natural-number counts.
+-/
+
+/-- Reflected queue started immediately before absolute index `q`. -/
+def finiteReflectedQueueFrom
+    (arrivals service : ℕ → ℕ) (q : ℕ) : ℕ → ℕ
+  | 0 => 0
+  | t + 1 =>
+      (finiteReflectedQueueFrom arrivals service q t + arrivals (q + t)) -
+        service (q + t)
+
+/-- Terminal queue after processing every index in the closed window `q..m`.
+The intended public use supplies `q ≤ m`. -/
+def finiteReflectedQueueOn
+    (arrivals service : ℕ → ℕ) (q m : ℕ) : ℕ :=
+  finiteReflectedQueueFrom arrivals service q (m - q + 1)
+
+/-- Signed arrivals-minus-service balance on a closed finite window. -/
+def finiteSignedWindowBalance
+    (arrivals service : ℕ → ℕ) (t m : ℕ) : ℤ :=
+  ∑ k ∈ Finset.Icc t m, ((arrivals k : ℤ) - service k)
+
+@[simp] theorem finiteReflectedQueueFrom_zero
+    (arrivals service : ℕ → ℕ) (q : ℕ) :
+    finiteReflectedQueueFrom arrivals service q 0 = 0 :=
+  rfl
+
+/-- Causal successor equation in local time. -/
+theorem finiteReflectedQueueFrom_succ
+    (arrivals service : ℕ → ℕ) (q t : ℕ) :
+    finiteReflectedQueueFrom arrivals service q (t + 1) =
+      (finiteReflectedQueueFrom arrivals service q t + arrivals (q + t)) -
+        service (q + t) :=
+  rfl
+
+/-- Nat reflection is the nonnegative part of the corresponding signed step. -/
+theorem finiteReflectedQueueFrom_succ_eq_intToNat
+    (arrivals service : ℕ → ℕ) (q t : ℕ) :
+    finiteReflectedQueueFrom arrivals service q (t + 1) =
+      Int.toNat ((finiteReflectedQueueFrom arrivals service q t : ℤ) +
+        arrivals (q + t) - service (q + t)) := by
+  rw [finiteReflectedQueueFrom_succ]
+  omega
+
+/-- A singleton signed window is one arrivals-minus-service term. -/
+theorem finiteSignedWindowBalance_self
+    (arrivals service : ℕ → ℕ) (m : ℕ) :
+    finiteSignedWindowBalance arrivals service m m =
+      (arrivals m : ℤ) - service m := by
+  simp [finiteSignedWindowBalance]
+
+/-- Extending a nonempty-right window appends its terminal term. -/
+theorem finiteSignedWindowBalance_succ
+    (arrivals service : ℕ → ℕ) {t m : ℕ} (ht : t ≤ m + 1) :
+    finiteSignedWindowBalance arrivals service t (m + 1) =
+      (if t ≤ m then finiteSignedWindowBalance arrivals service t m else 0) +
+        ((arrivals (m + 1) : ℤ) - service (m + 1)) := by
+  by_cases htm : t ≤ m
+  · rw [if_pos htm]
+    unfold finiteSignedWindowBalance
+    have hIcc : Finset.Icc t (m + 1) = insert (m + 1) (Finset.Icc t m) := by
+      ext x
+      simp only [Finset.mem_Icc, Finset.mem_insert]
+      omega
+    rw [hIcc, Finset.sum_insert (by simp)]
+    ring
+  · have hteq : t = m + 1 := by omega
+    subst t
+    simp [finiteSignedWindowBalance]
+
+/-- Right extension equation for a nonempty terminal queue window. -/
+theorem finiteReflectedQueueOn_succ
+    (arrivals service : ℕ → ℕ) {q m : ℕ} (hqm : q ≤ m) :
+    finiteReflectedQueueOn arrivals service q (m + 1) =
+      (finiteReflectedQueueOn arrivals service q m + arrivals (m + 1)) -
+        service (m + 1) := by
+  unfold finiteReflectedQueueOn
+  have hstep : m + 1 - q + 1 = (m - q + 1) + 1 := by omega
+  have hindex : q + (m - q + 1) = m + 1 := by omega
+  rw [hstep, finiteReflectedQueueFrom_succ]
+  rw [hindex]
+
+/-- Integer-positive-part form of right extension. -/
+theorem finiteReflectedQueueOn_succ_eq_intToNat
+    (arrivals service : ℕ → ℕ) {q m : ℕ} (hqm : q ≤ m) :
+    finiteReflectedQueueOn arrivals service q (m + 1) =
+      Int.toNat ((finiteReflectedQueueOn arrivals service q m : ℤ) +
+        arrivals (m + 1) - service (m + 1)) := by
+  rw [finiteReflectedQueueOn_succ arrivals service hqm]
+  omega
+
+/-- A singleton terminal window is one reflected arrivals/service step. -/
+theorem finiteReflectedQueueOn_self
+    (arrivals service : ℕ → ℕ) (q : ℕ) :
+    finiteReflectedQueueOn arrivals service q q =
+      arrivals q - service q := by
+  simp [finiteReflectedQueueOn, finiteReflectedQueueFrom]
+
+/-- Every suffix positive balance is bounded by the causal terminal queue. -/
+theorem intToNat_finiteSignedWindowBalance_le_reflectedQueueOn
+    (arrivals service : ℕ → ℕ) {q t m : ℕ}
+    (hqt : q ≤ t) (htm : t ≤ m) :
+    Int.toNat (finiteSignedWindowBalance arrivals service t m) ≤
+      finiteReflectedQueueOn arrivals service q m := by
+  induction m generalizing q t with
+  | zero =>
+      have hq : q = 0 := by omega
+      have ht : t = 0 := by omega
+      subst q
+      subst t
+      rw [finiteSignedWindowBalance_self, finiteReflectedQueueOn_self]
+      omega
+  | succ m ih =>
+      by_cases htm' : t ≤ m
+      · rw [finiteSignedWindowBalance_succ arrivals service (by omega), if_pos htm']
+        rw [finiteReflectedQueueOn_succ arrivals service (by omega)]
+        have hprev := ih hqt htm'
+        have hself := Int.self_le_toNat
+          (finiteSignedWindowBalance arrivals service t m)
+        omega
+      · have ht : t = m + 1 := by omega
+        subst t
+        rw [finiteSignedWindowBalance_self]
+        by_cases hqeq : q = m + 1
+        · subst q
+          rw [finiteReflectedQueueOn_self]
+          omega
+        · rw [finiteReflectedQueueOn_succ arrivals service (by omega)]
+          omega
+
+/-- A positive terminal queue is attained by one suffix positive balance. -/
+theorem finiteReflectedQueueOn_eq_zero_or_exists_suffix
+    (arrivals service : ℕ → ℕ) {q m : ℕ} (hqm : q ≤ m) :
+    finiteReflectedQueueOn arrivals service q m = 0 ∨
+      (0 < finiteReflectedQueueOn arrivals service q m ∧
+        ∃ t ∈ Finset.Icc q m,
+          finiteReflectedQueueOn arrivals service q m =
+            Int.toNat (finiteSignedWindowBalance arrivals service t m)) := by
+  induction m generalizing q with
+  | zero =>
+      have hq : q = 0 := by omega
+      subst q
+      by_cases hzero : finiteReflectedQueueOn arrivals service 0 0 = 0
+      · exact Or.inl hzero
+      · exact Or.inr ⟨Nat.pos_of_ne_zero hzero, 0, by simp,
+          by rw [finiteSignedWindowBalance_self, finiteReflectedQueueOn_self]; omega⟩
+  | succ m ih =>
+      by_cases hqeq : q = m + 1
+      · subst q
+        by_cases hzero : finiteReflectedQueueOn arrivals service (m + 1) (m + 1) = 0
+        · exact Or.inl hzero
+        · exact Or.inr ⟨Nat.pos_of_ne_zero hzero, m + 1, by simp,
+            by rw [finiteSignedWindowBalance_self, finiteReflectedQueueOn_self]; omega⟩
+      · have hqm' : q ≤ m := by omega
+        by_cases hzero : finiteReflectedQueueOn arrivals service q (m + 1) = 0
+        · exact Or.inl hzero
+        · refine Or.inr ⟨Nat.pos_of_ne_zero hzero, ?_⟩
+          rcases ih hqm' with hold | ⟨holdPos, t, ht, holdWitness⟩
+          · refine ⟨m + 1, by simp [hqm], ?_⟩
+            rw [finiteSignedWindowBalance_self,
+              finiteReflectedQueueOn_succ arrivals service hqm', hold]
+            omega
+          · have htBounds := Finset.mem_Icc.mp ht
+            refine ⟨t, Finset.mem_Icc.mpr ⟨htBounds.1, by omega⟩, ?_⟩
+            rw [finiteReflectedQueueOn_succ_eq_intToNat arrivals service hqm',
+              finiteSignedWindowBalance_succ arrivals service (by omega),
+              if_pos htBounds.2]
+            have hnonneg : 0 ≤ finiteSignedWindowBalance arrivals service t m := by
+              by_contra hneg
+              have hz : Int.toNat
+                  (finiteSignedWindowBalance arrivals service t m) = 0 :=
+                Int.toNat_of_nonpos (by omega)
+              omega
+            have hcast : (finiteReflectedQueueOn arrivals service q m : ℤ) =
+                finiteSignedWindowBalance arrivals service t m := by
+              rw [holdWitness, Int.ofNat_toNat, max_eq_left hnonneg]
+            rw [hcast]
+            congr 1
+            ring
+
+/-- Maximum positive suffix balance in a finite closed window. -/
+def finiteReflectedWindowMaximum
+    (arrivals service : ℕ → ℕ) (q m : ℕ) : ℕ :=
+  (Finset.Icc q m).sup fun t =>
+    Int.toNat (finiteSignedWindowBalance arrivals service t m)
+
+/-- Lindley reflection identity on a finite closed window. -/
+theorem finiteReflectedQueueOn_eq_windowMaximum
+    (arrivals service : ℕ → ℕ) {q m : ℕ} (hqm : q ≤ m) :
+    finiteReflectedQueueOn arrivals service q m =
+      finiteReflectedWindowMaximum arrivals service q m := by
+  apply le_antisymm
+  · rcases finiteReflectedQueueOn_eq_zero_or_exists_suffix
+      arrivals service hqm with hzero | ⟨_, t, ht, hqueue⟩
+    · simp [hzero]
+    · rw [hqueue]
+      exact Finset.le_sup (f := fun t =>
+        Int.toNat (finiteSignedWindowBalance arrivals service t m)) ht
+  · unfold finiteReflectedWindowMaximum
+    apply Finset.sup_le
+    intro t ht
+    exact intToNat_finiteSignedWindowBalance_le_reflectedQueueOn
+      arrivals service (Finset.mem_Icc.mp ht).1 (Finset.mem_Icc.mp ht).2
+
+/-- Queue zero is exactly nonpositivity of every release-time suffix. -/
+theorem finiteReflectedQueueOn_eq_zero_iff_all_suffix_nonpos
+    (arrivals service : ℕ → ℕ) {q m : ℕ} (hqm : q ≤ m) :
+    finiteReflectedQueueOn arrivals service q m = 0 ↔
+      ∀ t ∈ Finset.Icc q m,
+        finiteSignedWindowBalance arrivals service t m ≤ 0 := by
+  rw [finiteReflectedQueueOn_eq_windowMaximum arrivals service hqm]
+  constructor
+  · intro hzero t ht
+    have hle : Int.toNat (finiteSignedWindowBalance arrivals service t m) ≤ 0 := by
+      rw [← hzero]
+      unfold finiteReflectedWindowMaximum
+      exact Finset.le_sup (f := fun t =>
+        Int.toNat (finiteSignedWindowBalance arrivals service t m)) ht
+    exact Int.toNat_eq_zero.mp (Nat.eq_zero_of_le_zero hle)
+  · intro hall
+    apply Nat.eq_zero_of_le_zero
+    unfold finiteReflectedWindowMaximum
+    apply Finset.sup_le
+    intro t ht
+    rw [Int.toNat_of_nonpos (hall t ht)]
+
+/-- Unordered positive part of total balance on the whole window. -/
+def finiteUnorderedResidual
+    (arrivals service : ℕ → ℕ) (q m : ℕ) : ℕ :=
+  Int.toNat (finiteSignedWindowBalance arrivals service q m)
+
+/-- Unordered residual never exceeds the causal reflected queue. -/
+theorem finiteUnorderedResidual_le_reflectedQueueOn
+    (arrivals service : ℕ → ℕ) {q m : ℕ} (hqm : q ≤ m) :
+    finiteUnorderedResidual arrivals service q m ≤
+      finiteReflectedQueueOn arrivals service q m := by
+  exact intToNat_finiteSignedWindowBalance_le_reflectedQueueOn
+    arrivals service le_rfl hqm
+
+/-! ## Semantic regression: early service cannot repay future arrivals -/
+
+private def earlyServiceArrival : ℕ → ℕ
+  | 1 => 1
+  | _ => 0
+
+private def earlyServiceCapacity : ℕ → ℕ
+  | 0 => 1
+  | _ => 0
+
+theorem earlyService_unorderedResidual_zero :
+    finiteUnorderedResidual earlyServiceArrival earlyServiceCapacity 0 1 = 0 := by
+  have hIcc : Finset.Icc 0 1 = {0, 1} := by decide
+  rw [show finiteUnorderedResidual earlyServiceArrival earlyServiceCapacity 0 1 =
+      Int.toNat (finiteSignedWindowBalance earlyServiceArrival
+        earlyServiceCapacity 0 1) by rfl]
+  unfold finiteSignedWindowBalance
+  rw [hIcc]
+  norm_num [finiteUnorderedResidual, finiteSignedWindowBalance,
+    earlyServiceArrival, earlyServiceCapacity]
+
+theorem earlyService_causalQueue_one :
+    finiteReflectedQueueOn earlyServiceArrival earlyServiceCapacity 0 1 = 1 := by
+  norm_num [finiteReflectedQueueOn, finiteReflectedQueueFrom,
+    earlyServiceArrival, earlyServiceCapacity]
+
+/-! ## Generic finite interval-order Hall layer -/
+
+/-- Arrival units retaining their release block. -/
+def FiniteArrivalWindowCarrier
+    (arrivals : ℕ → ℕ) (q m : ℕ) :=
+  Σ k : {k : ℕ // k ∈ Finset.Icc q m}, Fin (arrivals k.val)
+
+/-- Service units retaining their availability block. -/
+def FiniteServiceWindowCarrier
+    (service : ℕ → ℕ) (q m : ℕ) :=
+  Σ k : {k : ℕ // k ∈ Finset.Icc q m}, Fin (service k.val)
+
+/-- A causal matching sends every claim to a distinct service slot at its own
+block or a later block. -/
+def FiniteForwardWindowMatching
+    (arrivals service : ℕ → ℕ) (q m : ℕ) : Prop :=
+  q ≤ m ∧ ∃ pay : FiniteArrivalWindowCarrier arrivals q m →
+      FiniteServiceWindowCarrier service q m,
+    Function.Injective pay ∧ ∀ claim, claim.1.val ≤ (pay claim).1.val
+
+/-- Cardinality of the generic arrival carrier. -/
+theorem natCard_finiteArrivalWindowCarrier
+    (arrivals : ℕ → ℕ) (q m : ℕ) :
+    Nat.card (FiniteArrivalWindowCarrier arrivals q m) =
+      ∑ k ∈ Finset.Icc q m, arrivals k := by
+  unfold FiniteArrivalWindowCarrier
+  rw [Nat.card_sigma, Finset.univ_eq_attach]
+  simp_rw [Nat.card_eq_fintype_card, Fintype.card_fin]
+  exact Finset.sum_attach (Finset.Icc q m) arrivals
+
+/-- Cardinality of the generic service carrier. -/
+theorem natCard_finiteServiceWindowCarrier
+    (service : ℕ → ℕ) (q m : ℕ) :
+    Nat.card (FiniteServiceWindowCarrier service q m) =
+      ∑ k ∈ Finset.Icc q m, service k := by
+  unfold FiniteServiceWindowCarrier
+  rw [Nat.card_sigma, Finset.univ_eq_attach]
+  simp_rw [Nat.card_eq_fintype_card, Fintype.card_fin]
+  exact Finset.sum_attach (Finset.Icc q m) service
+
+/-- Forward matching forces every release-time suffix Hall inequality. -/
+theorem FiniteForwardWindowMatching.to_suffix_sum_le
+    {arrivals service : ℕ → ℕ} {q m : ℕ}
+    (h : FiniteForwardWindowMatching arrivals service q m) :
+    ∀ t ∈ Finset.Icc q m,
+      (∑ k ∈ Finset.Icc t m, arrivals k) ≤
+        ∑ k ∈ Finset.Icc t m, service k := by
+  classical
+  rcases h with ⟨_, pay, hpayInjective, hpayForward⟩
+  intro t ht
+  have hqt := (Finset.mem_Icc.mp ht).1
+  let includeClaim : FiniteArrivalWindowCarrier arrivals t m →
+      FiniteArrivalWindowCarrier arrivals q m := fun claim =>
+    ⟨⟨claim.1.val, Finset.mem_Icc.mpr
+      ⟨hqt.trans (Finset.mem_Icc.mp claim.1.property).1,
+        (Finset.mem_Icc.mp claim.1.property).2⟩⟩, claim.2⟩
+  have includeClaim_injective : Function.Injective includeClaim := by
+    intro a b hab
+    apply Sigma.ext_iff.mpr
+    exact ⟨Subtype.ext (congrArg (fun x => x.1.val) hab),
+      (Sigma.ext_iff.mp hab).2⟩
+  let suffixPay : FiniteArrivalWindowCarrier arrivals t m →
+      FiniteServiceWindowCarrier service t m := fun claim =>
+    ⟨⟨(pay (includeClaim claim)).1.val, Finset.mem_Icc.mpr
+      ⟨(Finset.mem_Icc.mp claim.1.property).1.trans
+          (hpayForward (includeClaim claim)),
+        (Finset.mem_Icc.mp (pay (includeClaim claim)).1.property).2⟩⟩,
+      (pay (includeClaim claim)).2⟩
+  have suffixPay_injective : Function.Injective suffixPay := by
+    intro a b hab
+    apply includeClaim_injective
+    apply hpayInjective
+    apply Sigma.ext_iff.mpr
+    exact ⟨Subtype.ext (congrArg (fun x => x.1.val) hab),
+      (Sigma.ext_iff.mp hab).2⟩
+  letI : Finite (FiniteArrivalWindowCarrier arrivals t m) := by
+    unfold FiniteArrivalWindowCarrier
+    infer_instance
+  letI : Finite (FiniteServiceWindowCarrier service t m) := by
+    unfold FiniteServiceWindowCarrier
+    infer_instance
+  have hcard := Nat.card_le_card_of_injective suffixPay suffixPay_injective
+  rw [natCard_finiteArrivalWindowCarrier,
+    natCard_finiteServiceWindowCarrier] at hcard
+  exact hcard
+
+/-- Nested suffix Hall inequalities construct a causal forward matching. -/
+theorem finiteForwardWindowMatching_of_suffix_sum_le
+    {arrivals service : ℕ → ℕ} {q m : ℕ} (hqm : q ≤ m)
+    (hall : ∀ t ∈ Finset.Icc q m,
+      (∑ k ∈ Finset.Icc t m, arrivals k) ≤
+        ∑ k ∈ Finset.Icc t m, service k) :
+    FiniteForwardWindowMatching arrivals service q m := by
+  classical
+  let Claim := FiniteArrivalWindowCarrier arrivals q m
+  let Slot := FiniteServiceWindowCarrier service q m
+  letI : Finite Claim := by
+    dsimp [Claim]
+    unfold FiniteArrivalWindowCarrier
+    infer_instance
+  letI : Finite Slot := by
+    dsimp [Slot]
+    unfold FiniteServiceWindowCarrier
+    infer_instance
+  letI : Fintype Claim := Fintype.ofFinite Claim
+  letI : Fintype Slot := Fintype.ofFinite Slot
+  let eligible : Claim → Slot → Prop := fun claim slot =>
+    claim.1.val ≤ slot.1.val
+  have hallSubsets : ∀ A : Finset Claim,
+      A.card ≤ ({slot : Slot | ∃ claim ∈ A, eligible claim slot} : Finset Slot).card := by
+    intro A
+    by_cases hA : A.Nonempty
+    · let blocks : Finset ℕ := A.image fun claim => claim.1.val
+      have hblocks : blocks.Nonempty := hA.image _
+      let t := blocks.min' hblocks
+      have htBlocks : t ∈ blocks := Finset.min'_mem blocks hblocks
+      rcases Finset.mem_image.mp htBlocks with ⟨minClaim, hminClaimA, hminBlock⟩
+      have htIcc : t ∈ Finset.Icc q m := by
+        rw [← hminBlock]
+        exact minClaim.1.property
+      have ht_le_claim : ∀ claim ∈ A, t ≤ claim.1.val := by
+        intro claim hclaim
+        exact Finset.min'_le blocks _
+          (Finset.mem_image.mpr ⟨claim, hclaim, rfl⟩)
+      let claimsFromT : ↥A → FiniteArrivalWindowCarrier arrivals t m := fun claim =>
+        ⟨⟨claim.val.1.val, Finset.mem_Icc.mpr
+          ⟨ht_le_claim claim.val claim.property,
+            (Finset.mem_Icc.mp claim.val.1.property).2⟩⟩, claim.val.2⟩
+      have claimsFromT_injective : Function.Injective claimsFromT := by
+        intro a b hab
+        apply Subtype.ext
+        apply Sigma.ext_iff.mpr
+        exact ⟨Subtype.ext (congrArg (fun x => x.1.val) hab),
+          (Sigma.ext_iff.mp hab).2⟩
+      have hAClaims : A.card ≤ ∑ k ∈ Finset.Icc t m, arrivals k := by
+        letI : Finite (FiniteArrivalWindowCarrier arrivals t m) := by
+          unfold FiniteArrivalWindowCarrier
+          infer_instance
+        letI : Fintype (FiniteArrivalWindowCarrier arrivals t m) :=
+          Fintype.ofFinite _
+        have hcard := Fintype.card_le_of_injective claimsFromT
+          claimsFromT_injective
+        rw [← natCard_finiteArrivalWindowCarrier arrivals t m]
+        simpa only [Fintype.card_coe, Nat.card_eq_fintype_card] using hcard
+      let slotsToEligible : FiniteServiceWindowCarrier service t m →
+          {slot : Slot // ∃ claim ∈ A, eligible claim slot} := fun slot =>
+        ⟨⟨⟨slot.1.val, Finset.mem_Icc.mpr
+          ⟨(Finset.mem_Icc.mp htIcc).1.trans
+              (Finset.mem_Icc.mp slot.1.property).1,
+            (Finset.mem_Icc.mp slot.1.property).2⟩⟩, slot.2⟩,
+          ⟨minClaim, hminClaimA, by
+            change minClaim.1.val ≤ slot.1.val
+            rw [hminBlock]
+            exact (Finset.mem_Icc.mp slot.1.property).1⟩⟩
+      have slotsToEligible_injective : Function.Injective slotsToEligible := by
+        intro a b hab
+        apply Sigma.ext_iff.mpr
+        constructor
+        · exact Subtype.ext (congrArg (fun x => x.val.1.val) hab)
+        · exact (Sigma.ext_iff.mp (congrArg Subtype.val hab)).2
+      have hSlotsEligible : (∑ k ∈ Finset.Icc t m, service k) ≤
+          ({slot : Slot | ∃ claim ∈ A, eligible claim slot} : Finset Slot).card := by
+        letI : Finite (FiniteServiceWindowCarrier service t m) := by
+          unfold FiniteServiceWindowCarrier
+          infer_instance
+        letI : Fintype (FiniteServiceWindowCarrier service t m) :=
+          Fintype.ofFinite _
+        have hcard := Fintype.card_le_of_injective slotsToEligible
+          slotsToEligible_injective
+        rw [← natCard_finiteServiceWindowCarrier service t m]
+        rw [Nat.card_eq_fintype_card]
+        rw [Fintype.card_subtype] at hcard
+        exact hcard
+      exact hAClaims.trans ((hall t htIcc).trans hSlotsEligible)
+    · rw [Finset.not_nonempty_iff_eq_empty.mp hA]
+      simp
+  rcases (Fintype.all_card_le_filter_rel_iff_exists_injective eligible).1
+      hallSubsets with ⟨pay, hpay, heligible⟩
+  exact ⟨hqm, pay, hpay, heligible⟩
+
+/-- Generic interval-order Hall theorem. -/
+theorem finiteForwardWindowMatching_iff_suffix_sum_le
+    (arrivals service : ℕ → ℕ) {q m : ℕ} (hqm : q ≤ m) :
+    FiniteForwardWindowMatching arrivals service q m ↔
+      ∀ t ∈ Finset.Icc q m,
+        (∑ k ∈ Finset.Icc t m, arrivals k) ≤
+          ∑ k ∈ Finset.Icc t m, service k := by
+  constructor
+  · exact FiniteForwardWindowMatching.to_suffix_sum_le
+  · exact finiteForwardWindowMatching_of_suffix_sum_le hqm
+
+/-- Signed nonpositivity is equivalent to the natural suffix Hall inequality. -/
+theorem finiteSignedWindowBalance_nonpos_iff_sum_le
+    (arrivals service : ℕ → ℕ) (t m : ℕ) :
+    finiteSignedWindowBalance arrivals service t m ≤ 0 ↔
+      (∑ k ∈ Finset.Icc t m, arrivals k) ≤
+        ∑ k ∈ Finset.Icc t m, service k := by
+  unfold finiteSignedWindowBalance
+  rw [Finset.sum_sub_distrib]
+  rw [← Nat.cast_sum, ← Nat.cast_sum]
+  omega
+
+/-- Queue zero, all suffix Hall inequalities, and temporal matchability are
+the same finite condition. -/
+theorem finiteReflectedQueueOn_eq_zero_iff_forwardWindowMatching
+    (arrivals service : ℕ → ℕ) {q m : ℕ} (hqm : q ≤ m) :
+    finiteReflectedQueueOn arrivals service q m = 0 ↔
+      FiniteForwardWindowMatching arrivals service q m := by
+  rw [finiteForwardWindowMatching_iff_suffix_sum_le arrivals service hqm,
+    finiteReflectedQueueOn_eq_zero_iff_all_suffix_nonpos arrivals service hqm]
+  exact forall_congr' fun t => forall_congr' fun _ =>
+    finiteSignedWindowBalance_nonpos_iff_sum_le arrivals service t m
+
+end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean
index af59922b..dec50be0 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean
@@ -5,6 +5,7 @@ Authors: D. and Wise Wolf.
 -/
 
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentSelectedCarrier
+import DkMath.Collatz.PetalBridge.FloatWindow.FiniteReflectedQueue
 
 #print "file: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude"
 
@@ -394,51 +395,6 @@ theorem canonicalWindowPressureMarginAtDepth_eq
 
 /-! ## Bucket charge versus pressure amplitude -/
 
-/-- All continuation incidences at depth `d + 1` in the closed block window. -/
-def CanonicalWindowContinuationCarrierAtDepth
-    (n : OddNat) (q m d : ℕ) :=
-  Σ k : {k : ℕ // k ∈ Finset.Icc q m},
-    {i : ℕ // i ∈ canonicalPaymentBlockContinuationFiber n k.val (d + 1)}
-
-set_option maxHeartbeats 800000 in
--- Elaborating this dependent sigma embedding requires deeper type reduction.
-/-- Retaining the block coordinate embeds a selected bucket into the complete
-window continuation carrier at the same fixed depth. -/
-noncomputable def selectedPressureBucketWindowEmbedding
-    (n : OddNat) (q m d : ℕ) :
-    CanonicalSelectedPressureBucketCarrier n q m d ↪
-      CanonicalWindowContinuationCarrierAtDepth n q m d := by
-  let ek : {k : ℕ // k ∈ canonicalSelectedPressureBlocksAtDepth n q m d} ↪
-      {k : ℕ // k ∈ Finset.Icc q m} :=
-    { toFun := fun k => ⟨k.val,
-        (Finset.mem_filter.mp (Finset.mem_filter.mp k.property).1).1⟩
-      inj' := by
-        intro x y h
-        apply Subtype.ext
-        exact congrArg (fun z : {k : ℕ // k ∈ Finset.Icc q m} => z.val) h }
-  exact ek.sigmaMap fun k =>
-    { toFun := fun i => ⟨i.val,
-        CanonicalSelectedPressureBucketCarrier.mem_fixedDepthContinuationFiber
-          ⟨k, i⟩⟩
-      inj' := by
-        intro x y h
-        apply Subtype.ext
-        exact congrArg (fun z : {i : ℕ // i ∈
-          canonicalPaymentBlockContinuationFiber n k.val (d + 1)} => z.val) h }
-
-/-- The window continuation carrier has the expected finite Fubini count. -/
-theorem natCard_windowContinuationCarrierAtDepth
-    (n : OddNat) (q m d : ℕ) :
-    Nat.card (CanonicalWindowContinuationCarrierAtDepth n q m d) =
-      ∑ k ∈ Finset.Icc q m,
-        (canonicalPaymentBlockContinuationFiber n k (d + 1)).card := by
-  unfold CanonicalWindowContinuationCarrierAtDepth
-  rw [Nat.card_sigma]
-  simp_rw [Nat.card_eq_fintype_card, Fintype.card_coe]
-  rw [Finset.univ_eq_attach]
-  exact Finset.sum_attach (Finset.Icc q m) fun k =>
-    (canonicalPaymentBlockContinuationFiber n k (d + 1)).card
-
 /-- A selected bucket is bounded by exact-length recovery charge plus the
 positive part of the fixed-depth pressure margin.  This is finite accounting,
 not an allocation to a future boundary. -/
@@ -448,20 +404,26 @@ theorem natCard_selectedPressureBucket_le_exactLength_add_pressureAmplitude
       (canonicalExactLengthBlockIndicesAtDepth n q m d).card +
         Int.toNat (canonicalWindowPressureMarginAtDepth n q m d) := by
   classical
-  letI : Fintype {k : ℕ // k ∈ Finset.Icc q m} :=
-    Fintype.ofFinset (Finset.Icc q m) (by simp)
-  letI (k : {k : ℕ // k ∈ Finset.Icc q m}) :
-      Fintype {i : ℕ // i ∈ canonicalPaymentBlockContinuationFiber n k.val (d + 1)} :=
-    Fintype.ofFinset (canonicalPaymentBlockContinuationFiber n k.val (d + 1)) (by simp)
-  letI : Fintype (CanonicalWindowContinuationCarrierAtDepth n q m d) := by
-    unfold CanonicalWindowContinuationCarrierAtDepth
-    infer_instance
   have hbucket :
       Nat.card (CanonicalSelectedPressureBucketCarrier n q m d) ≤
-        Nat.card (CanonicalWindowContinuationCarrierAtDepth n q m d) :=
-    Nat.card_le_card_of_injective (selectedPressureBucketWindowEmbedding n q m d)
-      (selectedPressureBucketWindowEmbedding n q m d).injective
-  rw [natCard_windowContinuationCarrierAtDepth] at hbucket
+        ∑ k ∈ Finset.Icc q m,
+          (canonicalPaymentBlockContinuationFiber n k (d + 1)).card := by
+    rw [natCard_CanonicalSelectedPressureBucketCarrier]
+    calc
+      (∑ k ∈ canonicalSelectedPressureBlocksAtDepth n q m d,
+          (canonicalSelectedPressureCarrier n k).card) =
+          ∑ k ∈ canonicalSelectedPressureBlocksAtDepth n q m d,
+            (canonicalPaymentBlockContinuationFiber n k (d + 1)).card := by
+        apply Finset.sum_congr rfl
+        intro k hk
+        have hdepth := (mem_canonicalSelectedPressureBlocksAtDepth.mp hk).2
+        simp [canonicalSelectedPressureCarrier, hdepth]
+      _ ≤ ∑ k ∈ Finset.Icc q m,
+          (canonicalPaymentBlockContinuationFiber n k (d + 1)).card := by
+        apply Finset.sum_le_sum_of_subset
+        intro k hk
+        exact (Finset.mem_filter.mp
+          (mem_canonicalSelectedPressureBlocksAtDepth.mp hk).1).1
   let C := ∑ k ∈ Finset.Icc q m,
     (canonicalPaymentBlockContinuationFiber n k (d + 1)).card
   let E := (canonicalExactLengthBlockIndicesAtDepth n q m d).card
@@ -1067,6 +1029,216 @@ def CanonicalSelectedDriftBucketCarrier
     {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} //
       i ∈ canonicalSelectedDriftImageCarrier n k.val}
 
+/-! ## Proof-independent fixed-depth arrivals and service -/
+
+/-- Numeric selected-drift arrivals at block `k` and depth `d`.
+
+This definition deliberately does not inspect the classically chosen drift
+image.  Choice is used only to realize a source-bearing carrier whose
+cardinality is proved below to equal this proof-independent count. -/
+noncomputable def canonicalSelectedDriftArrivalCountAtDepth
+    (n : OddNat) (k d : ℕ) : ℕ := by
+  classical
+  exact if 0 < endpointAccountingTerm n k ∧
+      ¬ CanonicalSaturatedBorderBlock n k ∧
+      canonicalSelectedPositivePressureDepth n k = d
+  then Int.toNat (endpointAccountingTerm n k)
+  else 0
+
+/-- Local source-bearing drift image restricted to one selected depth. -/
+noncomputable def canonicalSelectedDriftImageCarrierAtDepth
+    (n : OddNat) (k d : ℕ) :
+    Finset {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} :=
+  if canonicalSelectedPositivePressureDepth n k = d then
+    canonicalSelectedDriftImageCarrier n k
+  else ∅
+
+/-- The local depth image realizes exactly the proof-independent arrival
+count. -/
+theorem card_canonicalSelectedDriftImageCarrierAtDepth
+    (n : OddNat) (k d : ℕ) :
+    (canonicalSelectedDriftImageCarrierAtDepth n k d).card =
+      canonicalSelectedDriftArrivalCountAtDepth n k d := by
+  classical
+  by_cases hactive : 0 < endpointAccountingTerm n k ∧
+      ¬ CanonicalSaturatedBorderBlock n k
+  · by_cases hdepth : canonicalSelectedPositivePressureDepth n k = d
+    · simp [canonicalSelectedDriftImageCarrierAtDepth,
+        canonicalSelectedDriftArrivalCountAtDepth, hactive, hdepth,
+        card_canonicalSelectedDriftImageCarrier]
+    · simp [canonicalSelectedDriftImageCarrierAtDepth,
+        canonicalSelectedDriftArrivalCountAtDepth, hdepth]
+  · have hempty := canonicalSelectedDriftImageCarrier_eq_empty_of_not_active hactive
+    by_cases hdepth : canonicalSelectedPositivePressureDepth n k = d
+    · rw [show canonicalSelectedDriftImageCarrierAtDepth n k d =
+          canonicalSelectedDriftImageCarrier n k by
+          simp [canonicalSelectedDriftImageCarrierAtDepth, hdepth], hempty]
+      rw [Finset.card_empty]
+      unfold canonicalSelectedDriftArrivalCountAtDepth
+      split_ifs with hfull
+      · exact (hactive ⟨hfull.1, hfull.2.1⟩).elim
+      · rfl
+    · simp [canonicalSelectedDriftImageCarrierAtDepth,
+        canonicalSelectedDriftArrivalCountAtDepth, hdepth]
+
+/-- Cardinality of the selected drift bucket is the sum of its
+proof-independent per-block arrivals over the closed block window. -/
+theorem natCard_CanonicalSelectedDriftBucketCarrier_eq_sum_arrivals
+    (n : OddNat) (q m d : ℕ) :
+    Nat.card (CanonicalSelectedDriftBucketCarrier n q m d) =
+      ∑ k ∈ Finset.Icc q m,
+        canonicalSelectedDriftArrivalCountAtDepth n k d := by
+  classical
+  unfold CanonicalSelectedDriftBucketCarrier
+  rw [Nat.card_sigma, Finset.univ_eq_attach]
+  simp_rw [Nat.card_eq_fintype_card, Fintype.card_coe]
+  rw [Finset.sum_attach
+    (canonicalActiveSelectedPressureBlocksAtDepth n q m d)
+    (fun k => (canonicalSelectedDriftImageCarrier n k).card)]
+  calc
+    (∑ k ∈ canonicalActiveSelectedPressureBlocksAtDepth n q m d,
+        (canonicalSelectedDriftImageCarrier n k).card) =
+        ∑ k ∈ canonicalActiveSelectedPressureBlocksAtDepth n q m d,
+          canonicalSelectedDriftArrivalCountAtDepth n k d := by
+      apply Finset.sum_congr rfl
+      intro k hk
+      have hdata := mem_canonicalActiveSelectedPressureBlocksAtDepth.mp hk
+      have hnonsat := mem_canonicalNonsaturatedPositiveBlockIndices.mp hdata.1
+      rw [card_canonicalSelectedDriftImageCarrier hnonsat.2.1 hnonsat.2.2]
+      simp [canonicalSelectedDriftArrivalCountAtDepth, hnonsat.2.1,
+        hnonsat.2.2, hdata.2]
+    _ = ∑ k ∈ Finset.Icc q m,
+          canonicalSelectedDriftArrivalCountAtDepth n k d := by
+      apply Finset.sum_subset
+      · intro k hk
+        exact (mem_canonicalNonsaturatedPositiveBlockIndices.mp
+          (mem_canonicalActiveSelectedPressureBlocksAtDepth.mp hk).1).1
+      · intro k hkIcc hkNotActive
+        have hinactive : ¬ (0 < endpointAccountingTerm n k ∧
+            ¬ CanonicalSaturatedBorderBlock n k ∧
+            canonicalSelectedPositivePressureDepth n k = d) := by
+          intro h
+          exact hkNotActive (mem_canonicalActiveSelectedPressureBlocksAtDepth.mpr
+            ⟨mem_canonicalNonsaturatedPositiveBlockIndices.mpr
+              ⟨hkIcc, h.1, h.2.1⟩, h.2.2⟩)
+        simp [canonicalSelectedDriftArrivalCountAtDepth, hinactive]
+
+/-- One exact-length service token is available precisely at a block whose
+canonical length equals `d`. -/
+noncomputable def canonicalExactLengthServiceAtDepth
+    (n : OddNat) (k d : ℕ) : ℕ :=
+  if canonicalPaymentBlockLength n k = d then 1 else 0
+
+/-- Total exact-length service is the cardinality of the existing exact-length
+block index carrier. -/
+theorem sum_canonicalExactLengthServiceAtDepth_eq_card
+    (n : OddNat) (q m d : ℕ) :
+    (∑ k ∈ Finset.Icc q m, canonicalExactLengthServiceAtDepth n k d) =
+      (canonicalExactLengthBlockIndicesAtDepth n q m d).card := by
+  classical
+  simp [canonicalExactLengthServiceAtDepth,
+    canonicalExactLengthBlockIndicesAtDepth, Finset.sum_boole]
+
+/-! ## Fixed-depth causal queue -/
+
+/-- Causal reflected queue for actual selected-drift arrivals at depth `d`
+against one exact-length service token per qualifying block. -/
+noncomputable def canonicalSelectedDriftDepthQueue
+    (n : OddNat) (q m d : ℕ) : ℕ :=
+  finiteReflectedQueueOn
+    (fun k => canonicalSelectedDriftArrivalCountAtDepth n k d)
+    (fun k => canonicalExactLengthServiceAtDepth n k d) q m
+
+/-- Lindley maximum form of the fixed-depth causal queue. -/
+theorem canonicalSelectedDriftDepthQueue_eq_windowMaximum
+    (n : OddNat) {q m d : ℕ} (hqm : q ≤ m) :
+    canonicalSelectedDriftDepthQueue n q m d =
+      finiteReflectedWindowMaximum
+        (fun k => canonicalSelectedDriftArrivalCountAtDepth n k d)
+        (fun k => canonicalExactLengthServiceAtDepth n k d) q m := by
+  exact finiteReflectedQueueOn_eq_windowMaximum _ _ hqm
+
+/-! ## Source-bearing temporal matching -/
+
+/-- Actual selected drift-image incidences in the full block window.  The
+outer coordinate is the release block and the inner subtype retains the
+original source time.  Inactive fibers are empty. -/
+def CanonicalSelectedDriftArrivalWindowCarrier
+    (n : OddNat) (q m d : ℕ) :=
+  Σ k : {k : ℕ // k ∈ Finset.Icc q m},
+    {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} //
+      i ∈ canonicalSelectedDriftImageCarrierAtDepth n k.val d}
+
+/-- A source-bearing causal matching sends every actual selected-drift
+incidence to a distinct exact-length service token at its release block or a
+later block. -/
+def CanonicalSelectedDriftForwardWindowMatching
+    (n : OddNat) (q m d : ℕ) : Prop :=
+  q ≤ m ∧ ∃ pay : CanonicalSelectedDriftArrivalWindowCarrier n q m d →
+      FiniteServiceWindowCarrier
+        (fun k => canonicalExactLengthServiceAtDepth n k d) q m,
+    Function.Injective pay ∧ ∀ claim, claim.1.val ≤ (pay claim).1.val
+
+/-- Each source-bearing local drift-image fiber is block-preservingly
+equivalent to the proof-independent numeric arrival fiber. -/
+noncomputable def canonicalSelectedDriftArrivalFiberEquiv
+    (n : OddNat) (k d : ℕ) :
+    {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} //
+      i ∈ canonicalSelectedDriftImageCarrierAtDepth n k d} ≃
+      Fin (canonicalSelectedDriftArrivalCountAtDepth n k d) := by
+  classical
+  letI : Fintype {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} :=
+    Fintype.ofFinset (canonicalSelectedPressureCarrier n k) (by simp)
+  letI : Fintype
+      {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} //
+        i ∈ canonicalSelectedDriftImageCarrierAtDepth n k d} :=
+    Fintype.ofFinset (canonicalSelectedDriftImageCarrierAtDepth n k d) (by simp)
+  apply Fintype.equivOfCardEq
+  rw [Fintype.card_coe, Fintype.card_fin,
+    card_canonicalSelectedDriftImageCarrierAtDepth]
+
+/-- Block-preserving equivalence between actual source arrivals and the
+generic numeric arrival carrier. -/
+noncomputable def canonicalSelectedDriftArrivalWindowEquiv
+    (n : OddNat) (q m d : ℕ) :
+    CanonicalSelectedDriftArrivalWindowCarrier n q m d ≃
+      FiniteArrivalWindowCarrier
+        (fun k => canonicalSelectedDriftArrivalCountAtDepth n k d) q m :=
+  Equiv.sigmaCongrRight fun k =>
+    canonicalSelectedDriftArrivalFiberEquiv n k.val d
+
+/-- The source-bearing temporal matching is exactly the generic interval-order
+matching after a block-preserving change of arrival fiber coordinates. -/
+theorem canonicalSelectedDriftForwardWindowMatching_iff_finiteForward
+    (n : OddNat) (q m d : ℕ) :
+    CanonicalSelectedDriftForwardWindowMatching n q m d ↔
+      FiniteForwardWindowMatching
+        (fun k => canonicalSelectedDriftArrivalCountAtDepth n k d)
+        (fun k => canonicalExactLengthServiceAtDepth n k d) q m := by
+  classical
+  let e := canonicalSelectedDriftArrivalWindowEquiv n q m d
+  constructor
+  · rintro ⟨hqm, pay, hinj, hforward⟩
+    refine ⟨hqm, fun claim => pay (e.symm claim), ?_, ?_⟩
+    · exact hinj.comp e.symm.injective
+    · intro claim
+      simpa [e, canonicalSelectedDriftArrivalWindowEquiv] using
+        hforward (e.symm claim)
+  · rintro ⟨hqm, pay, hinj, hforward⟩
+    refine ⟨hqm, fun claim => pay (e claim), ?_, ?_⟩
+    · exact hinj.comp e.injective
+    · intro claim
+      simpa [e, canonicalSelectedDriftArrivalWindowEquiv] using hforward (e claim)
+
+/-- Fixed-depth queue zero is equivalent to a forward matching that retains
+the actual claim source coordinate. -/
+theorem canonicalSelectedDriftDepthQueue_eq_zero_iff_sourceMatching
+    (n : OddNat) {q m d : ℕ} (hqm : q ≤ m) :
+    canonicalSelectedDriftDepthQueue n q m d = 0 ↔
+      CanonicalSelectedDriftForwardWindowMatching n q m d := by
+  rw [canonicalSelectedDriftForwardWindowMatching_iff_finiteForward]
+  exact finiteReflectedQueueOn_eq_zero_iff_forwardWindowMatching _ _ hqm
+
 /-- Forgetting image membership embeds the actual drift bucket into the full
 active selected bucket without changing block or source coordinates. -/
 def selectedDriftBucketActiveSelectedEmbedding
@@ -1084,6 +1256,32 @@ noncomputable def canonicalUnorderedSelectedDriftResidualCount
   Nat.card (CanonicalSelectedDriftBucketCarrier n q m d) -
     (canonicalExactLengthBlockIndicesAtDepth n q m d).card
 
+/-- The old unordered cardinal subtraction is exactly the generic positive
+part of total fixed-depth signed balance. -/
+theorem canonicalUnorderedSelectedDriftResidualCount_eq_finiteUnorderedResidual
+    (n : OddNat) (q m d : ℕ) :
+    canonicalUnorderedSelectedDriftResidualCount n q m d =
+      finiteUnorderedResidual
+        (fun k => canonicalSelectedDriftArrivalCountAtDepth n k d)
+        (fun k => canonicalExactLengthServiceAtDepth n k d) q m := by
+  rw [canonicalUnorderedSelectedDriftResidualCount,
+    natCard_CanonicalSelectedDriftBucketCarrier_eq_sum_arrivals,
+    ← sum_canonicalExactLengthServiceAtDepth_eq_card]
+  unfold finiteUnorderedResidual finiteSignedWindowBalance
+  rw [Finset.sum_sub_distrib]
+  rw [← Nat.cast_sum, ← Nat.cast_sum]
+  omega
+
+/-- The unordered actual drift residual is bounded by the causal reflected
+queue.  This compares cardinalities only and does not reinterpret the chosen
+unordered residual carrier as a causal state. -/
+theorem canonicalUnorderedSelectedDriftResidualCount_le_depthQueue
+    (n : OddNat) {q m d : ℕ} (hqm : q ≤ m) :
+    canonicalUnorderedSelectedDriftResidualCount n q m d ≤
+      canonicalSelectedDriftDepthQueue n q m d := by
+  rw [canonicalUnorderedSelectedDriftResidualCount_eq_finiteUnorderedResidual]
+  exact finiteUnorderedResidual_le_reflectedQueueOn _ _ hqm
+
 /-- The actual drift residual is bounded by the cp-322 selected-carrier
 residual.  The difference is precisely unused selected-carrier slack. -/
 theorem unorderedSelectedDriftResidualCount_le_selectedCarrierResidualCount
@@ -1234,23 +1432,126 @@ theorem natCard_actualSelectedDriftResidualCarrier
   · simp only [Finset.card_empty, canonicalUnorderedSelectedDriftResidualCount]
     omega
 
+/-! ## All-depth causal carrier -/
+
+/-- All actual unordered residual incidences, separated by active selected
+depth.  This is only a disjoint depthwise package; it does not share service
+tokens across depths. -/
+def CanonicalAllDepthActualSelectedDriftResidualCarrier
+    (n : OddNat) (q m : ℕ) :=
+  Σ d : {d : ℕ // d ∈ canonicalActiveSelectedPressureDepthSupport n q m},
+    CanonicalActualSelectedDriftResidualCarrier n q m d.val
+
+/-- Abstract causal outstanding capacity at every active selected depth. -/
+def CanonicalAllDepthSelectedDriftCausalQueueCarrier
+    (n : OddNat) (q m : ℕ) :=
+  Σ d : {d : ℕ // d ∈ canonicalActiveSelectedPressureDepthSupport n q m},
+    Fin (canonicalSelectedDriftDepthQueue n q m d.val)
+
+/-- Every depthwise unordered residual cardinality is bounded by its causal
+queue, hence the same is true after taking their disjoint sigma sum. -/
+theorem natCard_allDepthActualResidual_le_causalQueueCarrier
+    (n : OddNat) {q m : ℕ} (hqm : q ≤ m) :
+    Nat.card (CanonicalAllDepthActualSelectedDriftResidualCarrier n q m) ≤
+      Nat.card (CanonicalAllDepthSelectedDriftCausalQueueCarrier n q m) := by
+  classical
+  letI : Fintype
+      {d : ℕ // d ∈ canonicalActiveSelectedPressureDepthSupport n q m} :=
+    Fintype.ofFinset (canonicalActiveSelectedPressureDepthSupport n q m) (by simp)
+  letI (d : {d : ℕ // d ∈
+      canonicalActiveSelectedPressureDepthSupport n q m}) :
+      Fintype (CanonicalActualSelectedDriftResidualCarrier n q m d.val) :=
+    Fintype.ofFinset (canonicalActualSelectedDriftResidualFinset n q m d.val) (by simp)
+  unfold CanonicalAllDepthActualSelectedDriftResidualCarrier
+  unfold CanonicalAllDepthSelectedDriftCausalQueueCarrier
+  rw [Nat.card_sigma, Nat.card_sigma]
+  apply Finset.sum_le_sum
+  intro d hd
+  rw [natCard_actualSelectedDriftResidualCarrier, Nat.card_fin]
+  exact canonicalUnorderedSelectedDriftResidualCount_le_depthQueue n hqm
+
+/-- Noncanonical finite embedding witnessing the all-depth cardinal
+comparison.  Its target fibers remain depth-separated. -/
+theorem exists_allDepthActualResidualEmbedding_causalQueueCarrier
+    (n : OddNat) {q m : ℕ} (hqm : q ≤ m) :
+    Nonempty (CanonicalAllDepthActualSelectedDriftResidualCarrier n q m ↪
+      CanonicalAllDepthSelectedDriftCausalQueueCarrier n q m) := by
+  classical
+  letI : Fintype
+      {d : ℕ // d ∈ canonicalActiveSelectedPressureDepthSupport n q m} :=
+    Fintype.ofFinset (canonicalActiveSelectedPressureDepthSupport n q m) (by simp)
+  letI (d : {d : ℕ // d ∈
+      canonicalActiveSelectedPressureDepthSupport n q m}) :
+      Fintype (CanonicalActualSelectedDriftResidualCarrier n q m d.val) :=
+    Fintype.ofFinset (canonicalActualSelectedDriftResidualFinset n q m d.val) (by simp)
+  letI : Fintype (CanonicalAllDepthActualSelectedDriftResidualCarrier n q m) := by
+    unfold CanonicalAllDepthActualSelectedDriftResidualCarrier
+    infer_instance
+  letI : Fintype (CanonicalAllDepthSelectedDriftCausalQueueCarrier n q m) := by
+    unfold CanonicalAllDepthSelectedDriftCausalQueueCarrier
+    infer_instance
+  apply Function.Embedding.nonempty_iff_card_le.mpr
+  simpa only [Nat.card_eq_fintype_card] using
+    natCard_allDepthActualResidual_le_causalQueueCarrier n hqm
+
+/-! ## Spare selected incidence on nonsaturated blocks -/
+
+/-- A positive nonsaturated block of terminal valuation at least two has one
+selected incidence beyond its positive drift image.  This is the local slack
+needed for a future charge of an immediately preceding saturated token; no
+such cross-block charge is asserted here. -/
+theorem intToNat_endpointAccountingTerm_add_one_le_selectedPressureCarrier_card
+    {n : OddNat} {k : ℕ}
+    (hpos : 0 < endpointAccountingTerm n k)
+    (hnot : ¬ CanonicalSaturatedBorderBlock n k)
+    (hv : 2 ≤ canonicalBlockTerminalValuation n k) :
+    Int.toNat (endpointAccountingTerm n k) + 1 ≤
+      (canonicalSelectedPressureCarrier n k).card := by
+  have hclaimsLe := canonicalBlockClaimCount_le_length n k
+  have hclaimsLt : canonicalBlockClaimCount n k < canonicalBlockLength n k := by
+    by_contra h
+    have heq : canonicalBlockClaimCount n k = canonicalBlockLength n k := by omega
+    exact hnot (canonicalSaturatedBorderBlock_of_pos_of_claimCount_eq_length hpos heq)
+  have hdrift := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount n k
+  rw [canonicalBlockCapacityCount_eq_terminalValuation] at hdrift
+  have htoNat : Int.toNat (endpointAccountingTerm n k) =
+      canonicalBlockClaimCount n k - canonicalBlockTerminalValuation n k := by
+    have hnonneg : 0 ≤ endpointAccountingTerm n k := hpos.le
+    have hcast : ((Int.toNat (endpointAccountingTerm n k) : ℕ) : ℤ) =
+        endpointAccountingTerm n k := Int.toNat_of_nonneg hnonneg
+    exact_mod_cast (show (Int.toNat (endpointAccountingTerm n k) : ℤ) =
+      (canonicalBlockClaimCount n k -
+        canonicalBlockTerminalValuation n k : ℕ) by omega)
+  unfold canonicalSelectedPressureCarrier
+  rw [canonicalPaymentBlockContinuationFiber_card]
+  rw [canonicalSelectedPositivePressureDepth, if_neg (by omega)]
+  rw [htoNat]
+  change canonicalBlockClaimCount n k - canonicalBlockTerminalValuation n k + 1 ≤
+    canonicalBlockLength n k -
+      (canonicalBlockTerminalValuation n k - 1 + 1)
+  have hvlt :=
+    canonicalBlockTerminalValuation_lt_length_of_endpointAccountingTerm_pos hpos
+  omega
+
 /-!
-## Next boundary: causal depth queue
-
-The unordered layer now ends with an actual source-bearing residual subtype.
-The next theorem cannot be obtained by reinterpreting this complement: the
-chosen injection deliberately ignores block order.
-
-Stage H must instead introduce per-block arrivals from
-`canonicalSelectedDriftImageCarrier`, per-block exact-length service, and a
-fresh reflected queue initialized immediately before block `q`.  The existing
-`canonicalOutstandingClaimQueue` proves the required Lindley pattern only for
-the scalar claim/capacity process fixed in `UniversalPaymentScalarQueue`; it is
-not polymorphic in arrivals and service.  The safe next implementation is
-therefore to extract a generic finite Nat-valued Lindley queue API (or prove a
-parallel fixed-depth specialization) in a lower module, then instantiate it
-here.  Until that exists, neither this unordered residual nor its chosen
-matching may be called causal repayment.
+## Current boundary after the causal depth queue
+
+The fixed-depth causal layer is now stable: proof-independent arrivals and
+exact-length service instantiate the generic Lindley queue; queue zero is
+equivalent to a source-bearing forward matching; and depthwise unordered
+residuals embed by cardinality into the all-depth causal carrier.
+
+The next unresolved resource question is not queue causality.  It is whether
+successor slack can charge saturated tokens in the branches excluded by
+`intToNat_endpointAccountingTerm_add_one_le_selectedPressureCarrier_card`:
+
+* a zero-drift successor supplies no positive drift image;
+* a positive successor of terminal valuation one does not satisfy the
+  valuation-at-least-two spare-incidence theorem.
+
+No cross-depth sharing or cross-block repayment theorem follows from the
+present carriers.  Those branches require new local structure and must not be
+filled by reusing the unordered classical complement.
 -/
 
 /-- Endpoint-prefix pressure is continuation mass one level deeper minus the
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentScalarQueue.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentScalarQueue.lean
index 007a0541..f31811fc 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentScalarQueue.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentScalarQueue.lean
@@ -5,6 +5,7 @@ Authors: D. and Wise Wolf.
 -/
 
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentDepthLedger
+import DkMath.Collatz.PetalBridge.FloatWindow.FiniteReflectedQueue
 
 #print "file: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentScalarQueue"
 
@@ -503,6 +504,15 @@ theorem canonicalOutstandingClaimQueue_eq_zero_iff_all_excursions_repaid
 
 /-! ## Window-local causal queue -/
 
+/-- Canonical signed drift is the generic arrivals-minus-service balance. -/
+theorem finiteSignedWindowBalance_claimCount_capacityCount_eq
+    (n : OddNat) (q m : ℕ) :
+    finiteSignedWindowBalance (canonicalBlockClaimCount n)
+        (canonicalBlockCapacityCount n) q m =
+      canonicalWindowDriftInt n q m := by
+  unfold finiteSignedWindowBalance canonicalWindowDriftInt
+  simp_rw [endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount]
+
 /--
 Outstanding queue generated only by blocks `q..r`, initialized at zero before
 block `q`.  The reflected suffix form is chosen as the public terminal value;
@@ -512,6 +522,18 @@ noncomputable def canonicalLocalOutstandingClaimQueue
     (n : OddNat) (q r : ℕ) : ℕ :=
   (Finset.Icc q r).sup fun t => Int.toNat (canonicalWindowDriftInt n t r)
 
+/-- The existing local scalar queue is exactly the generic reflected queue
+specialized to canonical claim arrivals and capacity service. -/
+theorem canonicalLocalOutstandingClaimQueue_eq_finiteReflectedQueueOn
+    (n : OddNat) {q m : ℕ} (hqm : q ≤ m) :
+    canonicalLocalOutstandingClaimQueue n q m =
+      finiteReflectedQueueOn (canonicalBlockClaimCount n)
+        (canonicalBlockCapacityCount n) q m := by
+  rw [finiteReflectedQueueOn_eq_windowMaximum _ _ hqm]
+  unfold canonicalLocalOutstandingClaimQueue
+  unfold finiteReflectedWindowMaximum
+  simp_rw [finiteSignedWindowBalance_claimCount_capacityCount_eq]
+
 /-- The local causal queue is zero exactly when every release-time suffix is nonpositive. -/
 theorem canonicalLocalOutstandingClaimQueue_eq_zero_iff_all_suffixDrift_nonpos
     (n : OddNat) (q r : ℕ) :
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-324.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-324.md
new file mode 100644
index 00000000..f07d8a56
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-324.md
@@ -0,0 +1,117 @@
+# Petal / FloatWindow implementation report - checkpoint 324
+
+## Scope
+
+This checkpoint separates causal queue semantics from the unordered residual
+carrier introduced at cp-323.  It completes the generic finite queue, the
+fixed-depth specialization, source-bearing temporal matching, and the first
+all-depth causal carrier.  No unordered classical complement is reinterpreted
+as a recursively updated queue.
+
+## Implemented modules
+
+### `FiniteReflectedQueue.lean`
+
+The new Collatz-independent module provides:
+
+- a Nat-valued reflected queue on a finite closed interval;
+- signed arrivals-minus-service window balances;
+- the finite Lindley suffix-maximum identity;
+- queue-zero iff all suffix balances are nonpositive;
+- unordered total residual bounded by the causal queue;
+- an early-service regression where unordered residual is `0` but the causal
+  queue is `1`;
+- finite arrival and service carriers retaining block coordinates;
+- the interval-order Hall equivalence between suffix inequalities and a
+  forward injective matching.
+
+The regression is the semantic guardrail: service before a claim cannot pay
+that future claim, even when total arrivals and total service are equal.
+
+### `UniversalPaymentScalarQueue.lean`
+
+The existing scalar queue API is preserved.  Two compatibility theorems show
+that canonical claim count and capacity count instantiate the generic signed
+balance and reflected queue.
+
+### `UniversalPaymentAmplitude.lean`
+
+The fixed-depth layer now contains:
+
+- proof-independent selected-drift arrival counts;
+- a depth-restricted actual source-image carrier;
+- equality between local image cardinality and numeric arrival count;
+- equality between bucket cardinality and the blockwise arrival sum;
+- exact-length service counts and their finite-set cardinality theorem;
+- the fixed-depth causal queue and Lindley maximum form;
+- equality between the old unordered drift residual count and the generic
+  whole-window positive balance;
+- the theorem that unordered residual count is at most causal queue size;
+- a block-preserving equivalence from actual source-bearing arrival fibers to
+  numeric `Fin` fibers;
+- queue-zero iff an actual source-bearing forward matching exists;
+- an all-depth sigma carrier and cardinal/embedding comparison from unordered
+  residual incidences to independent causal queue fibers;
+- one-unit spare selected-incidence slack for positive nonsaturated blocks
+  whose terminal valuation is at least two.
+
+The former dependent-sigma definition
+`selectedPressureBucketWindowEmbedding` was removed.  Its only use was a
+cardinality bound that follows directly from the existing blockwise bucket
+sum and `Finset.sum_le_sum_of_subset`.  This replacement preserves the theorem
+surface while reducing a clean `UniversalPaymentAmplitude` rebuild from about
+70 seconds to about 10 seconds on this workspace.
+
+## Facts established
+
+1. The causal queue is not an alternate presentation of the cp-323 unordered
+   complement.  It is the maximum positive suffix imbalance.
+2. The unordered residual can underestimate causal outstanding work; the
+   early-service example proves strict inequality can occur.
+3. At fixed depth, queue zero has an exact finite Hall interpretation: every
+   actual source incidence can be injected into a service token at the same or
+   a later block.
+4. Classical choice is confined to realizing finite source images and
+   equivalences.  Numeric arrivals are defined solely from drift positivity,
+   nonsaturation, selected depth, and `Int.toNat endpointAccountingTerm`.
+5. Summing independent depthwise inequalities gives an all-depth finite
+   incidence certificate.  It does not authorize token sharing across depths.
+6. For positive nonsaturated terminal valuation at least two, selected
+   pressure contains the drift image plus at least one extra incidence.
+
+## Honest stopping boundary
+
+The next unresolved branches are:
+
+- a saturated block followed by a zero-drift successor;
+- a positive successor whose terminal valuation is one;
+- any theorem sharing exact-length service across distinct depths;
+- a canonical causal residual subset obtained from a maximal forward
+  matching.
+
+The current theorems do not supply these claims.  The all-depth object is a
+disjoint package of independent queues, not a global repayment allocation.
+
+## Verification
+
+Completed targeted builds during implementation:
+
+```text
+lake build DkMath.Collatz.PetalBridge.FloatWindow.FiniteReflectedQueue
+lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentScalarQueue
+lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude
+lake build DkMath.Collatz.PetalBridge.FloatWindow
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath
+git diff --check
+```
+
+All commands passed.  The changed Lean files contain no `sorry`.
+
+## Suggested next checkpoint
+
+Investigate the two excluded successor branches before adding any cross-block
+charge.  A useful next theorem must produce a local source incidence or an
+explicit obstruction in the zero-drift and valuation-one cases.  If neither
+exists, record a negative theorem or counterexample rather than weakening the
+causal matching contract.
````
`````
