# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude

gch: 347816107c2552376231c01f99e24c0906732e20

## Report

(22m33s)

cp-321 の Stage A-E を実装しました。

主な確定事項:

- 正の drift unit を、同一 block の selected incidence または saturated token へ埋め込める。
- Active depth は positive nonsaturated block のみで構成され、各 bucket は非空。
- Selected bucket は固定深さ continuation fiber の部分 carrier である。
- 固定深さ pressure の正規形:

  ```text
  continuation mass at d+1 - exact-length recovery count at d
  ```

- Bucket carrier は有限 embedding として

  ```text
  exact-length tokens ⊕ positive pressure-amplitude units
  ```

  に分解できる。

したがって、source overlap や positive-depth の個数ではなく、**一つの深さに複数存在し得る pressure amplitude units** が次の本質的な残余だと確定しました。これはまだ未来境界への repayment allocation ではありません。

追加ファイル:

- [UniversalPaymentAmplitude.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean)
- [report-petal-321.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-321.md)

検証済み:

- `lake build DkMath.Collatz.PetalBridge.FloatWindow`
- `lake build DkMath.Collatz.PetalBridge`
- `git diff --check`

すべて成功し、新規コードに `sorry` はありません。次は Stage F/G の全深さ集約、その後に amplitude superlevel または bounded-multiplicity transport が本当の登頂点になります。

## Review

## 結論

**全面採用。Stage A–E は要求どおり閉じた。**

cp-321 は、正 drift の会計を次の三段階へ引き上げた。

$$
\text{positive drift unit}\hookrightarrow\text{same-block selected incidence}\sqcup\text{saturated token}
$$

$$
\text{selected incidence at depth }d\hookrightarrow\text{fixed-depth continuation incidence at }d+1
$$

$$
\text{selected bucket}\hookrightarrow\text{exact-length token}\sqcup\text{positive pressure-amplitude unit}
$$

これにより、これまでの候補だった障害、

- source incidence の block 間重複
- depth $0$ の粗い upper bound
- 動的 depth から fixed-depth API への接続不足
- global cardinality embedding が block を忘れる問題

は全て解消された。

残った主語が **pressure amplitude** であるという診断も正しい。

ただし、次の攻め方には二つの重要な補正が必要じゃ。

1. 現在の amplitude は、selected incidence の真の残余より粗い上界である。
2. 任意の excursion window $q,\ldots,m$ の pressure は、既存 prefix pressure profile そのものではなく、二つの prefix profile の差である。

したがって Stage F/G の直後に既存 pulse packing へ飛ぶのではなく、まず **minimal selected residual** と **sliding pressure profile** を固定すべきじゃ。

---

## 1. Block-preserving embedding

新しい、

```lean
canonicalBlockPreservingPositiveDriftEmbedding
```

は、前 checkpoint の弱点を正しく修正している。

以前の embedding は総 cardinality だけから構成されていたため、block $k$ の drift unit が別 block の carrier へ入る可能性があった。

今回は各 block ごとに、

```lean
canonicalLocalPositiveDriftEmbedding
```

を選び、それを dependent sum で組み立てた。

そのため、

```lean
canonicalBlockPreservingPositiveDriftEmbedding_fst
```

によって block coordinate が定義的に保存される。

これは重要じゃ。

現在の証明書は、

```text
block k の正 drift
  ↓
block k 自身の selected source incidence
または
block k 自身の saturated token
```

という局所帰属を守っている。

局所 embedding 自体は cardinality から非計算的に選ばれた任意の写像であり、各 drift unit に固有の数論的意味があるわけではない。

しかし drift units はもともと匿名 unit なので、この抽象度で問題ない。

---

## 2. Active depth support

```lean
canonicalActiveSelectedPressureDepthSupport
```

は positive nonsaturated block のみから作られた。

これにより saturated block の空 carrier が、見かけだけ depth support に残る問題が消えた。

さらに、

```lean
mem_activeSelectedPressureDepthSupport_iff_nonempty
activeSelectedPressureDepthSupport_bucketCarrier_nonempty
```

によって、

$$
d\in\operatorname{ActiveSupport}\Longrightarrow\operatorname{Bucket}(d)\ne\varnothing
$$

が確定した。

したがって今後、active depth を、

> 実際に selected pressure incidence が存在する depth

として安全に読める。

一点だけ API 上の補強候補がある。

現在 nonempty とされた型は既存の、

```lean
CanonicalSelectedPressureBucketCarrier
```

であり、index 側には全 positive block が使われている。

saturated fiber は空なので実質的には同じだが、将来の可読性のため、

```lean
CanonicalActiveSelectedPressureBucketCarrier
```

を定義し、既存 bucket との `Equiv` を置いてもよい。

数学的内容には影響しない。

---

## 3. Fixed-depth prefix への実在 transport

```lean
selectedPressureBucketPrefixEmbedding
```

は非常に良い。

selected bucket の要素、

$$
(k,i)
$$

から block coordinate を忘れ、source time $i$ を、

$$
\operatorname{orbitDepthContinuationRangeFiber}(e_m+1,d+1)
$$

へ送っている。

injectivity は、

> orbit time $i$ は一意な canonical block に属する

という既存 partition theorem によって回収される。

したがって、これは単なる cardinality comparison ではない。

**実際の source incidence を保った embedding** じゃ。

結果として、

$$
|\operatorname{SelectedBucket}(d)|
\le
\operatorname{ContinuationCount}(e_m+1,d+1)
$$

が得られた。

dynamic selected depth は、ここで初めて既存 fixed-depth source pressure 層へ実体を保ったまま到達した。

---

## 4. Fixed-depth pressure の正規形

今回の中心 theorem は、

```lean
blockPressureContributionInt_eq_succCarrier_sub_exactLengthIndicator
```

じゃ。

正 depth $d\ge1$ について、

$$
M_k(d)=|\operatorname{ContinuationFiber}*k(d+1)|-\mathbf1*{L_k=d}
$$

が証明された。

これは以前の piecewise formula を、一つの構造式へまとめている。

### $L_k<d$

continuation も exact recovery もなく、寄与は $0$。

### $L_k=d$

continuation はなく、exact recovery 一件だけなので $-1$。

### $L_k=d+1$

両方なく、寄与は $0$。

### $L_k\ge d+2$

depth $d+1$ を越えて継続する source が $L_k-d-1$ 件あり、そのまま正 pressure になる。

有限 window で足すと、

$$
W_{q,m}(d)=C_{q,m}(d+1)-E_{q,m}(d)
$$

となる。

ここで、

- $C_{q,m}(d+1)$ は continuation incidence 総数
- $E_{q,m}(d)$ は長さがちょうど $d$ の block 数

じゃ。

これは pressure amplitude の正体を、完全に有限 combinatorics へ落とした theorem である。

---

## 5. Exact-length charge と amplitude

selected bucket の大きさを $B_{q,m}(d)$ とする。

cp-321 は、

$$
B_{q,m}(d)\le C_{q,m}(d+1)
$$

および、

$$
W_{q,m}(d)=C_{q,m}(d+1)-E_{q,m}(d)
$$

から、

$$
B_{q,m}(d)\le E_{q,m}(d)+\max(W_{q,m}(d),0)
$$

を得た。

Lean では、

```lean
natCard_selectedPressureBucket_le_exactLength_add_pressureAmplitude
```

として固定されている。

さらに、

```lean
exists_selectedPressureBucketEmbedding_exactLength_add_amplitude
```

により有限 embedding が存在する。

これは正しい。

ただし、この embedding は再び cardinality から選ばれたものじゃ。

したがって、

```text
ある selected source が、
この exact-length block によって回収された
```

という物理的・時間的意味はない。

exact-length token は現段階では、

> continuation mass から差し引かれる recovery-count の会計 token

である。

report が「future boundary allocation ではない」と明記したのは正確じゃ。

---

## 6. Prefix theorem の完成

```lean
sourcePressureMarginInt_paymentEndpointSeq_eq_continuation_succ_sub_exactLength
```

によって、endpoint prefix では、

$$
\operatorname{SourcePressureMargin}(e_m+1,d)=C_{0,m}(d+1)-E_{0,m}(d)
$$

が証明された。

これで fixed-depth pressure profile が、

```text
successor-depth continuation mass
-
exact-length block histogram
```

として読める。

これは非常に大きい。

pressure は抽象的な `2 * continuation - retention` だけではなく、

> 長い block から供給される continuation の累積と、長さ $d$ で閉じる block の回収一件との収支

になった。

---

## 7. 重要な補正：prefix pressure と window pressure

ここが次 checkpoint で最優先となる点じゃ。

既存の、

```lean
SourcePressureMarginInt n K d
```

は orbit time $0,\ldots,K-1$ の **prefix pressure** である。

一方 cp-321 の、

```lean
canonicalWindowPressureMarginAtDepth n q m d
```

は block $q,\ldots,m$ だけの **sliding-window pressure** じゃ。

$q=0$ なら両者は一致する。

しかし $q>0$ では、window pressure は絶対 pressure ではなく増分になる。

block $q$ の start time を $b_q$ とすれば、次の形が期待される。

$$
W_{q,m}(d)=\operatorname{SourcePressureMargin}(e_m+1,d)-\operatorname{SourcePressureMargin}(b_q,d)
$$

したがって、

$$
0<W_{q,m}(d)
$$

は、

```text
endpoint m の absolute pressure が正
```

を意味しない。

意味するのは、

```text
block q の開始時点から endpoint m までに、
depth d の pressure が正味で増えた
```

ということじゃ。

よって既存の、

```lean
IsSourcePressureDepth
SourcePressureFrontier
SourcePressureLocalIsland
SourcePressurePositiveBlock
```

へ sliding amplitude をそのまま渡してはならない。

次にはこの差分 identity を Lean に固定し、

```text
absolute prefix profile
relative window-increment profile
```

を型・命名の上でも分ける必要がある。

---

## 8. 既存 packing API が数えているもの

ここも慎重な補正が必要じゃ。

既存の finite-window packing theorem は、任意の positive depth 全体を直接数えているのではない。

主に数えているのは、

```lean
SourcePressureLocalIslandWitness
```

として供給された **孤立した positive center** と、その canonical separator じゃ。

たとえば、

```lean
sourcePressurePositiveWitnesses_card_le_half_window_add_one_direct
```

は、local-island centers が互いに二つ以上離れることから半窓 bound を得ている。

長さが複数ある positive interval、

```text
positive positive positive positive
```

の全四 depth を四個の island witness として数える theorem ではない。

したがって、

> 既存 packing は positive-depth support の大きさを抑える

と一般化して読むのは強すぎる。

正確には、

> 明示された local-island / pulse witness family の中心数と配置を抑える

API じゃ。

amplitude superlevel へ進むなら、各 level $h$ における superlevel set を、

- isolated island
- positive interval
- interval boundary
- unresolved boundary residue

へ分解する新しい coverage theorem が必要になる。

---

## 9. 現在の amplitude は粗い上界

selected bucket の大きさを $B_d$、全 continuation mass を $C_d$、exact-length count を $E_d$ とする。

現在使っている amplitude は、

$$
A_d=\max(C_d-E_d,0)
$$

じゃ。

しかし実際に exact-length tokens で覆い切れなかった selected incidence の最小残余は、

$$
R_d=\max(B_d-E_d,0)
$$

である。

$B_d\le C_d$ なので、

$$
R_d\le A_d
$$

じゃ。

ここで差、

$$
A_d-R_d
$$

には、selected bucket に属さない continuation incidence が含まれ得る。

つまり現在の pressure amplitude は正しい upper bound だが、selected drift の残余を正確に表す最小 carrierではない。

この区別は今後重要になる。

amplitude $A_d$ が大きくても、その多くが positive drift に選ばれていない block 由来である可能性がある。

したがって upper-zero boundary へ輸送すべき本当の対象は、まず、

$$
R_d=\max(B_d-E_d,0)
$$

として切り出した **selected residual units** じゃ。

pressure amplitude $A_d$ は、その residual を収容する外側の capacity として使うべきである。

---

## 10. Stage F/G の正しい到達形

全 active depth にわたり exact-length tokens をまとめる。

各 block は長さを一つしか持たないので、

$$
\sum_d E_{q,m}(d)\le m-q+1
$$

が得られる。

次に selected residual carrier をまとめる。

$$
\operatorname{ResidualCarrier}*{q,m}:=\bigsqcup*{d\in\operatorname{ActiveSupport}}\operatorname{Fin}(R_d)
$$

すると、global selected carrier は、

$$
|\operatorname{GlobalSelectedCarrier}|
\le
(m-q+1)+|\operatorname{ResidualCarrier}_{q,m}|
$$

まで縮む。

さらに、

$$
|\operatorname{ResidualCarrier}*{q,m}|
\le
|\operatorname{PressureAmplitudeCarrier}*{q,m}|
$$

じゃ。

この二段階を明示すると、

```text
真の selected residual
  ↓
coarse pressure amplitude capacity
```

という意味境界が固定される。

これをせず、いきなり amplitude carrier の全 unit を境界へ送ろうとすると、unselected continuation mass まで輸送対象にしてしまう。

---

## 11. Layer-cake route

有限 active depth support $S$ に対して、

$$
\sum_{d\in S}A_d=\sum_{h\ge0}|{d\in S\mid h<A_d}|
$$

という layer-cake identity がある。

Lean では amplitude carrier、

$$
\bigsqcup_{d\in S}\operatorname{Fin}(A_d)
$$

の座標を交換すればよい。

しかし、各 superlevel、

$$
h<A_d
$$

を既存 pressure pulse API で支配するには二つの一般化が必要じゃ。

### Threshold generalization

現在は、

$$
0<M(d)
$$

だけを見ている。

level $h$ では、

$$
h<M(d)
$$

を見る必要がある。

### Window-increment generalization

$q>0$ では absolute margin $M(d)$ ではなく、

$$
M_{\mathrm{end}}(d)-M_{\mathrm{start}}(d)
$$

に threshold を置く必要がある。

単に既存 predicate の `0` を `h` に置換するだけでは、sliding window へは届かない。

---

## 12. Challenge 命題への現在地

最終 Challenge は、

```lean
theorem collatz_conjecture (n : ℕ) (hn : n > 0) :
  ∃ m, collatzStep^[m] n = 1
```

じゃ。

cp-321 はまだ convergence theorem ではない。

しかし、Challenge へ至る幹線の、

```text
正 drift は何によって支えられているか
```

を次まで圧縮した。

```text
正 drift unit
  ↓ same-block embedding
selected source incidence + isolated saturation
  ↓ fixed-depth decomposition
exact-length recovery token + selected residual
  ↓ pressure capacity
pressure amplitude
```

したがって、残る Big の主語はかなり明確になった。

> selected residual pressure が、有限開始値の上位境界資源を無制限に再利用できるか。

ここを否定できれば queue bound へ進む。

---

## 判定まとめ

### Block-preserving embedding

**完成。**

### Active support

**完成。**

### Selected bucket → fixed-depth prefix incidence

**完成。**

### Fixed-depth pressure normal form

**完成。今回の中心成果。**

### Exact-length + amplitude embedding

**完成。ただし cardinality certificate。**

### All-depth aggregation

**未実装。次 checkpoint の機械的前半。**

### Existing pulse API への接続

**prefix / sliding window と island / interval の違いが未解決。**

### 真の残余

**selected residual units。pressure amplitude はその粗い capacity。**

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge Float-window branch after
report-petal-321.

The cp-321 implementation is accepted.

Stages A-E are complete:

    block-preserving positive-drift embedding
    active selected-depth support
    selected bucket to fixed-depth prefix embedding
    exact fixed-depth pressure normal form
    exact-length plus positive-amplitude cardinality embedding

Before applying the existing pressure pulse and packing APIs, separate three
objects that are currently easy to conflate:

    selected bucket mass
    minimal selected residual after exact-length charge
    full pressure amplitude from all continuation incidence

Also separate absolute prefix pressure from sliding-window pressure increments.

Stage A — active bucket decomposition

Define an active bucket carrier indexed only by positive nonsaturated blocks:

    CanonicalActiveSelectedPressureBucketCarrier n q m d.

Construct an explicit equivalence with the existing selected bucket carrier.
Saturated fibers are empty, so this should be a structural cleanup rather than
a new inequality.

Prove the active-support Fubini equivalence:

    CanonicalGlobalSelectedPressureCarrier n q m
      ≃
    Sigma d in active support,
      CanonicalActiveSelectedPressureBucketCarrier n q m d.

Prefer an actual equivalence, not only equality of cardinalities.

Stage B — exact-length tokens across depth

Define:

    CanonicalExactLengthTokenCarrier n q m :=
      Sigma d in active support,
        {k // k belongs to the block interval and blockLength k = d}.

Map this carrier to the canonical block interval by forgetting d.

Prove injectivity from uniqueness of block length.

Derive:

    Nat.card exactLengthTokenCarrier <= m - q + 1

under q <= m.

Stage C — minimal selected residual

For a fixed active depth d define:

    selectedBucketCount B_d
    exactLengthCount E_d
    selectedResidualCount := B_d - E_d.

Define the anonymous residual carrier:

    Fin selectedResidualCount.

Prove the exact minimal cardinality decomposition:

    B_d <= E_d + selectedResidualCount.

Construct a finite embedding of the selected bucket into:

    exact-length tokens at d
      Sum
    selected residual units at d.

This is still an accounting embedding, not a temporal allocation.

Stage D — residual versus full pressure amplitude

Let:

    C_d = complete window continuation count at d + 1
    W_d = canonicalWindowPressureMarginAtDepth n q m d.

Use:

    B_d <= C_d
    W_d = C_d - E_d

to prove:

    selectedResidualCount
      <=
    Int.toNat W_d.

Construct an embedding:

    selected residual units
      ↪
    positive pressure-amplitude units.

Document explicitly that the pressure-amplitude carrier may contain
unselected continuation mass and is an upper capacity, not the minimal
selected residual.

Stage E — all-depth residual reduction

Define:

    CanonicalSelectedResidualCarrier n q m :=
      Sigma d in active support,
        Fin (selectedResidualCount at d).

Define:

    CanonicalPositivePressureAmplitudeCarrier n q m :=
      Sigma d in active support,
        Fin (Int.toNat (canonicalWindowPressureMarginAtDepth n q m d)).

Assemble the depthwise embeddings.

Prove:

    global selected carrier card
      <=
    block interval cardinality
      +
    selected residual carrier card

and:

    selected residual carrier card
      <=
    pressure amplitude carrier card.

Then combine with the existing saturated-token packing theorem.

Keep the selected residual theorem as the primary statement and the full
amplitude theorem as its coarser corollary.

Stage F — sliding pressure identity

Let:

    b_q = canonicalBlockStartTime n q
    e_m = paymentEndpointSeq n m.

For q <= m prove:

    canonicalWindowPressureMarginAtDepth n q m d
      =
    SourcePressureMarginInt n (e_m + 1) d
      -
    SourcePressureMarginInt n b_q d.

The q = 0 specialization must recover the existing endpoint-prefix theorem.

Define a clearly named relative profile:

    canonicalWindowPressureIncrementProfile n q m d.

Do not identify its positivity with IsSourcePressureDepth unless q = 0 and
the initial margin is zero.

Stage G — prefix and relative amplitude APIs

Define separate carriers:

    CanonicalPrefixPressureAmplitudeCarrier
    CanonicalRelativePressureAmplitudeCarrier.

Prove their equality only in the q = 0 specialization.

Update documentation so that existing PressureFrontier and PressureState APIs
are described as absolute-prefix APIs.

Stage H — layer-cake identity

For a finite depth support S and integer profile P define superlevel sets:

    PressureSuperlevel S P h :=
      S.filter fun d => h < Int.toNat (P d).

Prove the generic finite layer-cake theorem:

    sum d in S, Int.toNat (P d)
      =
    sum h in range (1 + maximum amplitude),
      (PressureSuperlevel S P h).card.

Instantiate it for both prefix and relative pressure amplitude.

This theorem is combinatorial and should not yet use pulse packing.

Stage I — audit the existing pressure witness API precisely

The existing finite-window packing theorems count supplied local-island
witness centers and canonical separators. They do not bound all positive
depths, all positive intervals, or pressure amplitude.

Record this distinction in the report.

For each superlevel h determine which additional objects are required:

    threshold-h local island
    threshold-h positive interval
    threshold-h interval boundary
    threshold-h coverage residue.

Do not claim that the level-zero local-island packing theorem automatically
bounds a whole superlevel set.

Stage J — generic threshold profile layer

Investigate a generic finite integer profile API:

    profile : Nat -> Int
    threshold : Int.

Generalize the purely order-theoretic frontier, island, interval, and
sign-change lemmas from:

    0 < profile d

to:

    threshold < profile d.

Keep Collatz-specific recurrence theorems separate.

If this generalization is routine, instantiate it with:

    absolute prefix pressure
    sliding-window pressure increment.

Stage K — block-length histogram alternative

Using the exact pressure normal form, expose the histogram formula:

    windowPressure(d)
      =
    sum over blocks with length >= d + 2 of
      (blockLength - d - 1)
      -
    exactLengthCount(d).

Equivalently express continuation mass through tail counts of the block-length
histogram.

Compare this direct combinatorial profile with the pulse/superlevel route.

If the amplitude carrier is dominated mainly by unselected continuation mass,
record that the full pressure amplitude is too coarse and continue with the
minimal selected residual carrier instead.

Stage L — saturated token slack

Retain the cp-320/cp-319 split for saturated tokens.

For a positive nonsaturated successor with terminal valuation at least two,
prove the one-unit carrier slack:

    successor drift + 1
      <=
    successor selected carrier card.

Use it to charge a preceding saturated token to the successor carrier while
preserving enough units for the successor's own drift.

Keep zero-drift successors and terminal-valuation-one successors as explicit
unresolved branches.

Stopping rule

Stop at the first genuine obstruction among:

    active bucket equivalence cannot be assembled;
    exact-length tokens do not inject into block indices;
    selected residual is not bounded by full pressure amplitude;
    sliding pressure is not a difference of endpoint profiles;
    superlevel layer-cake cannot be made finite;
    local-island packing does not extend to positive intervals;
    the full pressure amplitude is too coarse to reflect selected residual;
    saturated zero-drift successors have no structural charge.

Do not jump directly from amplitude positivity to a boundary allocation.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-322.md
```

cp-321 は、敵を amplitude まで追い詰めた。

だが次に殴るべき本体は、全 continuation が作る粗い amplitude ではない。

**exact-length token を差し引いたあと、本当に残った selected residual** じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
index fa924e21..3276dcc0 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
@@ -24,6 +24,7 @@ import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPositiveBlock
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPrimitiveExcursion
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentSaturatedSuccessor
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentSelectedCarrier
+import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude
 import DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition

 #print "file: DkMath.Collatz.PetalBridge.FloatWindow"
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean
new file mode 100644
index 00000000..d30edb19
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean
@@ -0,0 +1,405 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentSelectedCarrier
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude"
+
+namespace DkMath.Collatz
+
+/-!
+# Fixed-depth pressure amplitude reduction
+
+This module transports the dynamic selected-incidence carrier into the
+existing fixed-depth prefix fibers.  All transports below preserve source
+incidences; none is interpreted as a future repayment allocation.
+-/
+
+/-! ## Block-preserving positive-drift incidence embedding -/
+
+/-- The local certificate attached to one positive block: selected source
+incidences, or the isolated saturated units of that same block. -/
+def CanonicalLocalSelectedOrSaturatedCarrier
+    (n : OddNat) (k : ℕ) :=
+  {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} ⊕
+    Fin (canonicalSaturatedTokenNat n k)
+
+/-- A local finite embedding chosen from the pointwise cardinality theorem.
+Unlike the earlier global cardinality embedding, this choice is made before
+forming the block-indexed sigma, so it cannot move a unit to another block. -/
+noncomputable def canonicalLocalPositiveDriftEmbedding
+    {n : OddNat} {k : ℕ} (hpos : 0 < endpointAccountingTerm n k) :
+    Fin (Int.toNat (endpointAccountingTerm n k)) ↪
+      CanonicalLocalSelectedOrSaturatedCarrier n k := by
+  classical
+  letI : Fintype {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} :=
+    Fintype.ofFinset (canonicalSelectedPressureCarrier n k) (by simp)
+  letI : Fintype (CanonicalLocalSelectedOrSaturatedCarrier n k) := by
+    unfold CanonicalLocalSelectedOrSaturatedCarrier
+    infer_instance
+  have htargetCard :
+      Fintype.card (CanonicalLocalSelectedOrSaturatedCarrier n k) =
+        (canonicalSelectedPressureCarrier n k).card +
+          canonicalSaturatedTokenNat n k := by
+    unfold CanonicalLocalSelectedOrSaturatedCarrier
+    calc
+      Fintype.card
+          ({i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} ⊕
+            Fin (canonicalSaturatedTokenNat n k)) =
+          Fintype.card {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} +
+            Fintype.card (Fin (canonicalSaturatedTokenNat n k)) :=
+        Fintype.card_sum
+      _ = _ := by rw [Fintype.card_coe, Fintype.card_fin]
+  exact Classical.choice (Function.Embedding.nonempty_iff_card_le.mpr (by
+    rw [Fintype.card_fin, htargetCard]
+    exact intToNat_endpointAccountingTerm_le_selectedCarrier_add_saturated hpos))
+
+/-- Block-indexed target of the local incidence embeddings. -/
+def CanonicalBlockPreservingIncidenceCarrier
+    (n : OddNat) (q m : ℕ) :=
+  Σ k : {k : ℕ // k ∈ canonicalPositiveDriftBlockIndices n q m},
+    CanonicalLocalSelectedOrSaturatedCarrier n k.val
+
+/-- Assemble the local maps without forgetting their canonical block. -/
+noncomputable def canonicalBlockPreservingPositiveDriftEmbedding
+    (n : OddNat) (q m : ℕ) :
+    CanonicalPositiveDriftUnitCarrier n q m ↪
+      CanonicalBlockPreservingIncidenceCarrier n q m :=
+  (Function.Embedding.refl _).sigmaMap fun k =>
+    canonicalLocalPositiveDriftEmbedding ((Finset.mem_filter.mp k.property).2)
+
+/-- The assembled embedding preserves the source block definitionally. -/
+@[simp] theorem canonicalBlockPreservingPositiveDriftEmbedding_fst
+    {n : OddNat} {q m : ℕ}
+    (x : CanonicalPositiveDriftUnitCarrier n q m) :
+    (canonicalBlockPreservingPositiveDriftEmbedding n q m x).1 = x.1 :=
+  rfl
+
+/-- Compatibility note: the old theorem remains the coarser cardinality-only
+surface; use `canonicalBlockPreservingPositiveDriftEmbedding` when block
+identity matters. -/
+theorem exists_positiveDriftUnitEmbedding_global_add_saturated_compat
+    (n : OddNat) (q m : ℕ) :
+    Nonempty (CanonicalPositiveDriftUnitCarrier n q m ↪
+      (CanonicalGlobalSelectedPressureCarrier n q m ⊕
+        {k : ℕ // k ∈ canonicalSaturatedBlockIndices n q m})) :=
+  exists_positiveDriftUnitEmbedding_global_add_saturated n q m
+
+/-! ## Active selected-depth support -/
+
+/-- Positive nonsaturated blocks at selected depth `d`. -/
+noncomputable def canonicalActiveSelectedPressureBlocksAtDepth
+    (n : OddNat) (q m d : ℕ) : Finset ℕ := by
+  classical
+  exact (canonicalNonsaturatedPositiveBlockIndices n q m).filter fun k =>
+    canonicalSelectedPositivePressureDepth n k = d
+
+/-- Depths carrying at least one positive nonsaturated selected block. -/
+noncomputable def canonicalActiveSelectedPressureDepthSupport
+    (n : OddNat) (q m : ℕ) : Finset ℕ :=
+  (canonicalNonsaturatedPositiveBlockIndices n q m).image fun k =>
+    canonicalSelectedPositivePressureDepth n k
+
+@[simp] theorem mem_canonicalActiveSelectedPressureBlocksAtDepth
+    {n : OddNat} {q m d k : ℕ} :
+    k ∈ canonicalActiveSelectedPressureBlocksAtDepth n q m d ↔
+      k ∈ canonicalNonsaturatedPositiveBlockIndices n q m ∧
+        canonicalSelectedPositivePressureDepth n k = d := by
+  simp [canonicalActiveSelectedPressureBlocksAtDepth]
+
+/-- Active support is exactly nonemptiness of the active block bucket. -/
+theorem mem_activeSelectedPressureDepthSupport_iff_nonempty
+    {n : OddNat} {q m d : ℕ} :
+    d ∈ canonicalActiveSelectedPressureDepthSupport n q m ↔
+      (canonicalActiveSelectedPressureBlocksAtDepth n q m d).Nonempty := by
+  classical
+  constructor
+  · intro hd
+    rcases Finset.mem_image.mp hd with ⟨k, hk, hkd⟩
+    exact ⟨k, mem_canonicalActiveSelectedPressureBlocksAtDepth.mpr
+      ⟨hk, hkd⟩⟩
+  · rintro ⟨k, hk⟩
+    exact Finset.mem_image.mpr ⟨k,
+      (mem_canonicalActiveSelectedPressureBlocksAtDepth.mp hk).1,
+      (mem_canonicalActiveSelectedPressureBlocksAtDepth.mp hk).2⟩
+
+/-- Every active selected depth has a nonempty incidence bucket. -/
+theorem activeSelectedPressureDepthSupport_bucketCarrier_nonempty
+    {n : OddNat} {q m d : ℕ}
+    (hd : d ∈ canonicalActiveSelectedPressureDepthSupport n q m) :
+    Nonempty (CanonicalSelectedPressureBucketCarrier n q m d) := by
+  classical
+  rcases mem_activeSelectedPressureDepthSupport_iff_nonempty.mp hd with ⟨k, hk⟩
+  have hdata := mem_canonicalActiveSelectedPressureBlocksAtDepth.mp hk
+  have hpos := (mem_canonicalNonsaturatedPositiveBlockIndices.mp hdata.1).2.1
+  have hnot := (mem_canonicalNonsaturatedPositiveBlockIndices.mp hdata.1).2.2
+  have hcard := endpointAccountingTerm_le_card_selectedPressureCarrier hpos hnot
+  have hcarrier : (canonicalSelectedPressureCarrier n k).Nonempty := by
+    apply Finset.card_pos.mp
+    have : 0 < (canonicalSelectedPressureCarrier n k).card := by
+      exact_mod_cast hpos.trans_le hcard
+    exact this
+  rcases hcarrier with ⟨i, hi⟩
+  refine ⟨⟨⟨k, ?_⟩, ⟨i, hi⟩⟩⟩
+  exact mem_canonicalSelectedPressureBlocksAtDepth.mpr
+    ⟨(Finset.mem_filter.mp hdata.1).1, hdata.2⟩
+
+/-! ## Fixed-depth prefix embedding -/
+
+/-- Forgetting the canonical block sends a selected bucket incidence into the
+endpoint-aligned fixed-depth continuation fiber. -/
+noncomputable def selectedPressureBucketToPrefixFiber
+    {n : OddNat} {q m d : ℕ} (_hqm : q ≤ m) :
+    CanonicalSelectedPressureBucketCarrier n q m d →
+      {i : ℕ // i ∈ orbitDepthContinuationRangeFiber n
+        (paymentEndpointSeq n m + 1) (d + 1)} := by
+  classical
+  intro x
+  refine ⟨x.2.val, ?_⟩
+  have hfixed := x.mem_fixedDepthContinuationFiber
+  have hblock := (mem_canonicalPaymentBlockContinuationFiber_iff.mp hfixed).1
+  have hcont := (mem_canonicalPaymentBlockContinuationFiber_iff.mp hfixed).2
+  have hkpos := (mem_canonicalSelectedPressureBlocksAtDepth.mp x.1.property).1
+  have hkIcc := (Finset.mem_filter.mp hkpos).1
+  have hkm := (Finset.mem_Icc.mp hkIcc).2
+  have hprefix : x.2.val ∈ canonicalPaymentBlockPrefix n m :=
+    mem_canonicalPaymentBlockPrefix_iff_exists.mpr ⟨x.1.val, hkm, hblock⟩
+  unfold orbitDepthContinuationRangeFiber
+  apply Finset.mem_filter.mpr
+  constructor
+  · rw [← canonicalPaymentBlockPrefix_eq_range]
+    exact hprefix
+  · exact hcont
+
+/-- The forget-block map is injective because source time determines its unique
+canonical block. -/
+theorem selectedPressureBucketToPrefixFiber_injective
+    {n : OddNat} {q m d : ℕ} (hqm : q ≤ m) :
+    Function.Injective (selectedPressureBucketToPrefixFiber
+      (n := n) (q := q) (m := m) (d := d) hqm) := by
+  intro x y hxy
+  rcases x with ⟨kx, ix⟩
+  rcases y with ⟨ky, iy⟩
+  have hi : ix.val = iy.val := congrArg Subtype.val hxy
+  have hix := canonicalSelectedPressureCarrier_subset_block n kx.val ix.property
+  have hiy := canonicalSelectedPressureCarrier_subset_block n ky.val iy.property
+  have hk : kx.val = ky.val := by
+    rcases existsUnique_mem_canonicalPaymentBlock n ix.val with ⟨j, _, hu⟩
+    exact (hu kx.val hix).trans (hu ky.val (hi ▸ hiy)).symm
+  cases kx with
+  | mk kx hkx =>
+    cases ky with
+    | mk ky hky =>
+      dsimp only at hk
+      subst ky
+      cases Subtype.ext hi
+      rfl
+
+/-- Block-forgetting embedding into the existing fixed-depth prefix fiber. -/
+noncomputable def selectedPressureBucketPrefixEmbedding
+    {n : OddNat} {q m d : ℕ} (hqm : q ≤ m) :
+    CanonicalSelectedPressureBucketCarrier n q m d ↪
+      {i : ℕ // i ∈ orbitDepthContinuationRangeFiber n
+        (paymentEndpointSeq n m + 1) (d + 1)} :=
+  ⟨selectedPressureBucketToPrefixFiber hqm,
+    selectedPressureBucketToPrefixFiber_injective hqm⟩
+
+/-- Fixed-depth continuation count bounds every selected bucket. -/
+theorem natCard_selectedPressureBucket_le_continuationCount
+    {n : OddNat} {q m d : ℕ} (hqm : q ≤ m) :
+    Nat.card (CanonicalSelectedPressureBucketCarrier n q m d) ≤
+      orbitDepthContinuationFiberCount n (paymentEndpointSeq n m + 1) (d + 1) := by
+  rw [orbitDepthContinuationFiberCount_eq_card_filter_range]
+  let e : CanonicalSelectedPressureBucketCarrier n q m d ↪
+      {i : ℕ // i ∈ orbitDepthContinuationRangeFiber n
+        (paymentEndpointSeq n m + 1) (d + 1)} :=
+    selectedPressureBucketPrefixEmbedding hqm
+  have hcard := Nat.card_le_card_of_injective e e.injective
+  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hcard
+
+/-! ## Exact fixed-depth pressure normal form -/
+
+/-- Exact local pressure: continuation one level deeper, minus the unique
+recovery token precisely when the block length equals the queried depth. -/
+theorem blockPressureContributionInt_eq_succCarrier_sub_exactLengthIndicator
+    {n : OddNat} {k d : ℕ} (hd : 1 ≤ d) :
+    blockPressureContributionInt n k d =
+      ((canonicalPaymentBlockContinuationFiber n k (d + 1)).card : ℤ) -
+        if canonicalPaymentBlockLength n k = d then 1 else 0 := by
+  rw [blockPressureContributionInt_eq,
+    canonicalPaymentBlockContinuationFiber_card]
+  by_cases hlt : canonicalPaymentBlockLength n k < d
+  · have hsub : canonicalPaymentBlockLength n k - d = 0 :=
+      Nat.sub_eq_zero_of_le hlt.le
+    have hsubSucc : canonicalPaymentBlockLength n k - (d + 1) = 0 :=
+      Nat.sub_eq_zero_of_le (by omega)
+    simp [hsub, hsubSucc, hlt.ne, Nat.not_le_of_lt hlt]
+  by_cases heq : canonicalPaymentBlockLength n k = d
+  · simp [heq, hd]
+  · have hdl : d < canonicalPaymentBlockLength n k := by omega
+    simp [heq, hd, hdl.le]
+    omega
+
+/-- Blocks of exact canonical length `d` in the closed interval `q..m`. -/
+noncomputable def canonicalExactLengthBlockIndicesAtDepth
+    (n : OddNat) (q m d : ℕ) : Finset ℕ := by
+  classical
+  exact (Finset.Icc q m).filter fun k => canonicalPaymentBlockLength n k = d
+
+/-- Fixed-depth pressure summed on a closed canonical block interval. -/
+noncomputable def canonicalWindowPressureMarginAtDepth
+    (n : OddNat) (q m d : ℕ) : ℤ :=
+  ∑ k ∈ Finset.Icc q m, blockPressureContributionInt n k d
+
+/-- Exact finite-window fixed-depth normal form. -/
+theorem canonicalWindowPressureMarginAtDepth_eq
+    {n : OddNat} {q m d : ℕ} (hd : 1 ≤ d) :
+    canonicalWindowPressureMarginAtDepth n q m d =
+      (∑ k ∈ Finset.Icc q m,
+        ((canonicalPaymentBlockContinuationFiber n k (d + 1)).card : ℤ)) -
+        (canonicalExactLengthBlockIndicesAtDepth n q m d).card := by
+  classical
+  unfold canonicalWindowPressureMarginAtDepth
+  simp_rw [blockPressureContributionInt_eq_succCarrier_sub_exactLengthIndicator hd]
+  rw [Finset.sum_sub_distrib]
+  simp only [canonicalExactLengthBlockIndicesAtDepth, Finset.sum_boole]
+
+/-! ## Bucket charge versus pressure amplitude -/
+
+/-- All continuation incidences at depth `d + 1` in the closed block window. -/
+def CanonicalWindowContinuationCarrierAtDepth
+    (n : OddNat) (q m d : ℕ) :=
+  Σ k : {k : ℕ // k ∈ Finset.Icc q m},
+    {i : ℕ // i ∈ canonicalPaymentBlockContinuationFiber n k.val (d + 1)}
+
+set_option maxHeartbeats 800000 in
+-- Elaborating this dependent sigma embedding requires deeper type reduction.
+/-- Retaining the block coordinate embeds a selected bucket into the complete
+window continuation carrier at the same fixed depth. -/
+noncomputable def selectedPressureBucketWindowEmbedding
+    (n : OddNat) (q m d : ℕ) :
+    CanonicalSelectedPressureBucketCarrier n q m d ↪
+      CanonicalWindowContinuationCarrierAtDepth n q m d := by
+  let ek : {k : ℕ // k ∈ canonicalSelectedPressureBlocksAtDepth n q m d} ↪
+      {k : ℕ // k ∈ Finset.Icc q m} :=
+    { toFun := fun k => ⟨k.val,
+        (Finset.mem_filter.mp (Finset.mem_filter.mp k.property).1).1⟩
+      inj' := by
+        intro x y h
+        apply Subtype.ext
+        exact congrArg (fun z : {k : ℕ // k ∈ Finset.Icc q m} => z.val) h }
+  exact ek.sigmaMap fun k =>
+    { toFun := fun i => ⟨i.val,
+        CanonicalSelectedPressureBucketCarrier.mem_fixedDepthContinuationFiber
+          ⟨k, i⟩⟩
+      inj' := by
+        intro x y h
+        apply Subtype.ext
+        exact congrArg (fun z : {i : ℕ // i ∈
+          canonicalPaymentBlockContinuationFiber n k.val (d + 1)} => z.val) h }
+
+/-- The window continuation carrier has the expected finite Fubini count. -/
+theorem natCard_windowContinuationCarrierAtDepth
+    (n : OddNat) (q m d : ℕ) :
+    Nat.card (CanonicalWindowContinuationCarrierAtDepth n q m d) =
+      ∑ k ∈ Finset.Icc q m,
+        (canonicalPaymentBlockContinuationFiber n k (d + 1)).card := by
+  unfold CanonicalWindowContinuationCarrierAtDepth
+  rw [Nat.card_sigma]
+  simp_rw [Nat.card_eq_fintype_card, Fintype.card_coe]
+  rw [Finset.univ_eq_attach]
+  exact Finset.sum_attach (Finset.Icc q m) fun k =>
+    (canonicalPaymentBlockContinuationFiber n k (d + 1)).card
+
+/-- A selected bucket is bounded by exact-length recovery charge plus the
+positive part of the fixed-depth pressure margin.  This is finite accounting,
+not an allocation to a future boundary. -/
+theorem natCard_selectedPressureBucket_le_exactLength_add_pressureAmplitude
+    {n : OddNat} {q m d : ℕ} (hd : 1 ≤ d) :
+    Nat.card (CanonicalSelectedPressureBucketCarrier n q m d) ≤
+      (canonicalExactLengthBlockIndicesAtDepth n q m d).card +
+        Int.toNat (canonicalWindowPressureMarginAtDepth n q m d) := by
+  classical
+  letI : Fintype {k : ℕ // k ∈ Finset.Icc q m} :=
+    Fintype.ofFinset (Finset.Icc q m) (by simp)
+  letI (k : {k : ℕ // k ∈ Finset.Icc q m}) :
+      Fintype {i : ℕ // i ∈ canonicalPaymentBlockContinuationFiber n k.val (d + 1)} :=
+    Fintype.ofFinset (canonicalPaymentBlockContinuationFiber n k.val (d + 1)) (by simp)
+  letI : Fintype (CanonicalWindowContinuationCarrierAtDepth n q m d) := by
+    unfold CanonicalWindowContinuationCarrierAtDepth
+    infer_instance
+  have hbucket :
+      Nat.card (CanonicalSelectedPressureBucketCarrier n q m d) ≤
+        Nat.card (CanonicalWindowContinuationCarrierAtDepth n q m d) :=
+    Nat.card_le_card_of_injective (selectedPressureBucketWindowEmbedding n q m d)
+      (selectedPressureBucketWindowEmbedding n q m d).injective
+  rw [natCard_windowContinuationCarrierAtDepth] at hbucket
+  let C := ∑ k ∈ Finset.Icc q m,
+    (canonicalPaymentBlockContinuationFiber n k (d + 1)).card
+  let E := (canonicalExactLengthBlockIndicesAtDepth n q m d).card
+  have hnormal : canonicalWindowPressureMarginAtDepth n q m d = (C : ℤ) - E := by
+    simpa [C, E] using canonicalWindowPressureMarginAtDepth_eq (n := n) hd
+  by_cases hCE : C ≤ E
+  · exact hbucket.trans (by omega)
+  · have hEC : E ≤ C := Nat.le_of_lt (Nat.lt_of_not_ge hCE)
+    have htoNat : Int.toNat (canonicalWindowPressureMarginAtDepth n q m d) = C - E := by
+      rw [hnormal]
+      omega
+    rw [htoNat]
+    exact hbucket.trans (by omega)
+
+/-- Finite existence form of the bucket decomposition. -/
+theorem exists_selectedPressureBucketEmbedding_exactLength_add_amplitude
+    {n : OddNat} {q m d : ℕ} (hd : 1 ≤ d) :
+    Nonempty (CanonicalSelectedPressureBucketCarrier n q m d ↪
+      ({k : ℕ // k ∈ canonicalExactLengthBlockIndicesAtDepth n q m d} ⊕
+        Fin (Int.toNat (canonicalWindowPressureMarginAtDepth n q m d)))) := by
+  classical
+  letI : Fintype (CanonicalSelectedPressureBucketCarrier n q m d) := by
+    unfold CanonicalSelectedPressureBucketCarrier
+    infer_instance
+  letI : Fintype {k : ℕ // k ∈ canonicalExactLengthBlockIndicesAtDepth n q m d} :=
+    Fintype.ofFinset (canonicalExactLengthBlockIndicesAtDepth n q m d) (by simp)
+  apply Function.Embedding.nonempty_iff_card_le.mpr
+  have htargetCard :
+      Fintype.card
+          ({k : ℕ // k ∈ canonicalExactLengthBlockIndicesAtDepth n q m d} ⊕
+            Fin (Int.toNat (canonicalWindowPressureMarginAtDepth n q m d))) =
+        (canonicalExactLengthBlockIndicesAtDepth n q m d).card +
+          Int.toNat (canonicalWindowPressureMarginAtDepth n q m d) := by
+    calc
+      _ = Fintype.card
+            {k : ℕ // k ∈ canonicalExactLengthBlockIndicesAtDepth n q m d} +
+          Fintype.card
+            (Fin (Int.toNat (canonicalWindowPressureMarginAtDepth n q m d))) :=
+        Fintype.card_sum
+      _ = _ := by rw [Fintype.card_coe, Fintype.card_fin]
+  rw [htargetCard]
+  simpa only [← Nat.card_eq_fintype_card] using
+    natCard_selectedPressureBucket_le_exactLength_add_pressureAmplitude (n := n) hd
+
+/-- Endpoint-prefix pressure is continuation mass one level deeper minus the
+number of exact-length recovery blocks. -/
+theorem sourcePressureMarginInt_paymentEndpointSeq_eq_continuation_succ_sub_exactLength
+    {n : OddNat} {m d : ℕ} (hd : 1 ≤ d) :
+    SourcePressureMarginInt n (paymentEndpointSeq n m + 1) d =
+      (orbitDepthContinuationFiberCount n
+          (paymentEndpointSeq n m + 1) (d + 1) : ℤ) -
+        (canonicalExactLengthBlockIndicesAtDepth n 0 m d).card := by
+  rw [sourcePressureMarginInt_paymentEndpointSeq_eq_sum_blockPressureContributionInt]
+  simp_rw [blockPressureContributionInt_eq_succCarrier_sub_exactLengthIndicator hd]
+  rw [Finset.sum_sub_distrib,
+    orbitDepthContinuationFiberCount_paymentEndpointSeq_eq_sum]
+  congr 1
+  · exact_mod_cast rfl
+  · classical
+    have hIcc : Finset.Icc 0 m = Finset.range (m + 1) := by
+      ext k
+      simp only [Finset.mem_Icc, Finset.mem_range]
+      omega
+    simp only [canonicalExactLengthBlockIndicesAtDepth, hIcc, Finset.sum_boole]
+
+end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-321.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-321.md
new file mode 100644
index 00000000..e619974a
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-321.md
@@ -0,0 +1,75 @@
+# Petal / FloatWindow implementation report - checkpoint 321
+
+## Scope
+
+This checkpoint starts the fixed-depth pressure-amplitude reduction requested
+after cp-320.  The implementation is in
+`DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude` and remains
+finite, source-incidence based, and no-sorry.
+
+## Implemented facts
+
+### Block-preserving accounting
+
+Positive-drift units now embed blockwise into the selected incidence carrier
+or the saturated token of the same block.  The dependent-sum embedding retains
+the canonical block coordinate definitionally.  The earlier global
+cardinality-only embedding remains available through a compatibility theorem.
+
+### Active depth support
+
+The new active support contains exactly depths selected by positive,
+nonsaturated blocks.  Every member of this support has a nonempty selected
+bucket.  Saturated zero buckets are therefore no longer interpreted as
+pressure witnesses.
+
+### Fixed-depth transport and normal form
+
+Each selected bucket embeds into both:
+
+- the existing endpoint-prefix continuation fiber after forgetting its block;
+- the complete continuation carrier over the original block window while
+  retaining its block.
+
+At every positive depth, local pressure is exactly successor continuation mass
+minus the indicator that the block has that exact length.  Summing gives the
+same identity over arbitrary finite windows and over endpoint prefixes.
+
+### Exact-length charge plus amplitude
+
+For every `d >= 1`, the selected bucket cardinality is bounded by
+
+```text
+exact-length block count at d
+  + Int.toNat (fixed-depth window pressure at d).
+```
+
+A finite embedding into exact-length block tokens plus anonymous positive
+pressure-amplitude units is supplied.  This is not a boundary allocation and
+does not identify any later repayment event.
+
+## What is now proved
+
+The dynamic selected-depth carrier is not an unrelated auxiliary count.  At a
+fixed depth it is a genuine subcarrier of successor continuation incidence.
+The continuation mass has an exact two-term accounting law: one exact-length
+recovery charge per matching block, with only the positive pressure remainder
+left over.  Thus pressure amplitude, rather than positive-depth support or
+source overlap, is the next nontrivial mass.
+
+## Remaining route
+
+1. Package exact-length tokens over active depths and forget depth injectively;
+   uniqueness of canonical block length should bound their total by the block
+   interval cardinality.
+2. Package positive pressure amplitudes over active depths.
+3. Sum the bucket decomposition to reduce the global selected carrier to block
+   count plus the amplitude carrier, then combine saturated-token packing.
+4. Audit pressure superlevels.  Existing level-zero pulse/packing results count
+   positive depths, but currently do not bound multiple amplitude units at one
+   depth.  No such strengthening should be claimed without a superlevel pulse
+   invariant or a bounded-multiplicity transport map.
+
+The first anticipated mathematical obstruction remains the Stage-I transport:
+an amplitude unit has not yet been assigned injectively, or with bounded
+multiplicity, to an upper-zero boundary, separator, or NoLift obstruction.
````
`````
