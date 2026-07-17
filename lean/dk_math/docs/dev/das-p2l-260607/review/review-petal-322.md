# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude

gch: 2ca3150306a6684947fa2dbd85acced6ac783de6

## Report

(22m15s)

cp-322 を実装しました。

**確定した事実**

- 既存 selected bucket と、nonsaturated block のみを使う active bucket は明示的に同値。
- Global selected carrier は active depth bucket の dependent sum と同値。
- Exact-length token は block index へ単射で写り、総数は `m - q + 1` 以下。
- Minimal selected residual を

  ```text
  selected bucket count - exact-length count
  ```

  として分離。
- Minimal residual は full pressure amplitude へ depth-preserving embedding を持つ。
- ただし full amplitude は unselected continuation mass を含み得るため、上限容量にすぎない。
- 主となる有限還元:

  ```text
  global selected carrier
    ≤ block interval cardinality + minimal selected residual
  ```

- Saturated packing と合わせて:

  ```text
  positive drift units
    ≤ block count + minimal residual + saturated half-packing
  ```

これにより、現在の最小の未制御量は **full pressure amplitude ではなく selected residual** だと Lean 上で固定されました。

Stage F の調査では、sliding pressure identity に必要な次の bridge が公開 API に不足しています。

- `0..m = 0..q-1 + q..m` の block-sum 分割
- `canonicalBlockStartTime n q` の pressure と直前 endpoint prefix の同定
- `q = 0` の独立した初期条件

したがって relative pressure の positivity を既存の absolute-prefix `IsSourcePressureDepth` と同一視することは、現時点ではできません。この停止境界をコードコメントと [report-petal-322.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-322.md) に記録しました。

検証済み:

- `lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude`
- `lake build DkMath.Collatz.PetalBridge.FloatWindow`
- `lake build DkMath.Collatz.PetalBridge`
- `git diff --check`
- 新規 `sorry` なし

## Review

## 結論

**全面採用。Stage A–E は正しく閉じた。**

cp-322 により、fixed-depth 会計は次の三層へ明確に分離された。

$$
\text{selected bucket}
\longrightarrow
\text{exact-length charge}
+
\text{selected residual}
$$

$$
\text{selected residual}
\hookrightarrow
\text{full pressure amplitude}
$$

さらに全 depth を集約して、

$$
|\text{global selected carrier}|
\le
|\text{block interval}|
+
|\text{selected residual carrier}|
$$

まで到達した。

これは cp-321 で残った「full amplitude は unselected continuation まで含んでいる」という粗さを、Lean 上で正式に切り離した成果じゃ。

ただし、今回の深い精査から三つの補正が必要になる。

1. `canonicalSelectedResidualCount` は **順序を無視した匿名 cardinality residual** であり、実在する未割当 source 集合ではない。
2. selected carrier 自体が positive drift より大きい場合があるため、これは **positive drift に対する真の最小 residual** でもない。
3. Stage F の停止点は数学的障害ではない。既存の sliding endpoint ledger と全く同じ証明形で閉じられる、小さな API gap じゃ。

そして大域 Big の観点では、selected residual だけでなく、

$$
m-q+1
$$

と、

$$
\frac{m-q+2}{2}
$$

も区間長とともに増える。

したがって report の、

> only uncontrolled term is the minimal selected residual

は、有限会計上は正しいが、大域一様有界性の意味では強すぎる。

正確には、

> **残った非明示的項は selected residual。だが exact-length token 数と saturated token 数も、まだ有限開始値に依存する定数へは落ちていない。**

じゃ。

---

## 1. Active bucket equivalence

```lean
selectedPressureBucketEquivActive
```

は正しい構造整理じゃ。

旧 bucket は全 positive block を index に含むが、saturated block の selected carrier は空なので、実際の要素は必ず nonsaturated block に属する。

したがって、

$$
\operatorname{SelectedBucket}(d)
\simeq
\operatorname{ActiveSelectedBucket}(d)
$$

が成立する。

さらに、

```lean
globalSelectedPressureCarrierEquivActiveBuckets
```

によって、

$$
\operatorname{GlobalSelectedCarrier}
\simeq
\bigsqcup_{d\in\operatorname{ActiveSupport}}
\operatorname{ActiveBucket}(d)
$$

が得られた。

この `Equiv` は単なる cardinality equality ではなく、

- block index
- source time
- selected depth

を全て保存している。

ここは完全に閉じた。

---

## 2. Exact-length token の全深さ集約

depth $d$ の exact-length token は、

$$
L_k=d
$$

を満たす block $k$ 一件につき一個じゃ。

```lean
exactLengthTokenBlockEmbedding
```

は depth coordinate を忘れて block index だけを残す。

一つの block は一つの長さしか持たないので、この写像は単射になる。

したがって、

$$
|\operatorname{ExactLengthTokens}_{q,m}|
\le m-q+1
$$

が得られた。

これは exact-length charge が depth ごとに重複計上されないことを完全に固定した theorem じゃ。

ただし、この $m-q+1$ は有限ではあるが、大域一様定数ではない。

長い open excursion では線形に増え得る。

---

## 3. `canonicalSelectedResidualCount` の正確な意味

depth $d$ について、

$$
B_d=
|\operatorname{ActiveSelectedBucket}(d)|
$$

$$
E_d=
|\operatorname{ExactLengthTokens}(d)|
$$

と置く。

今回の residual は、

$$
R_d=(B_d-E_d)_+
$$

じゃ。

これは確かに、

$$
B_d\le E_d+R_d
$$

を満たす最小の自然数である。

したがって、

> exact-length token を全て自由に使えると仮定したとき、selected bucket を収容するために必要な最小追加 cardinality

という意味では「minimal」で正しい。

しかし、これは次のものではない。

```text
selected bucket の具体的な残余部分集合
時刻順序を守った未払い incidence
将来の exact-length token だけを使った残債
positive drift unit 自身の最小残余
```

現在の、

```lean
CanonicalSelectedResidualCarrier
```

は、

```lean
Fin residualCount
```

であり、source time も block index も持たない匿名 unit じゃ。

したがって今後は、名称または説明に、

```text
unordered cardinal residual
```

という境界を明記した方がよい。

例えば互換 alias として、

```lean
canonicalUnorderedSelectedResidualCount
```

を用意してもよい。

---

## 4. Selected residual は drift に対してまだ最小ではない

positive nonsaturated block $k$ について、

$$
D_k
\le
|\operatorname{SelectedCarrier}_k|
$$

じゃ。

多くの場合、この不等式には slack がある。

したがって depth $d$ で、

$$
U_d=
\sum_{\substack{k\text{ active}\\operatorname{selectedDepth}(k)=d}}
D_k
$$

と置けば、

$$
U_d\le B_d
$$

である。

positive drift unit に必要な真の unordered residual は、

$$
R_d^{\mathrm{drift}}=(U_d-E_d)_+
$$

であり、

$$
R_d^{\mathrm{drift}}\le R_d
$$

じゃ。

よって現在の `canonicalSelectedResidualCount` は、

> selected carrier に対する最小 residual

ではあるが、

> positive drift unit に対する最小 residual

ではない。

cp-321 で block-preserving drift embedding が既に作られているので、次にはその image を depth ごとに集めればよい。

```text
positive drift unit
→ chosen selected source incidence
```

の image carrier を定義すれば、その cardinality は drift unit 数と完全に一致する。

---

## 5. 実在 residual incidence がまだない

将来、upper-zero boundary の bit position へ輸送するには、匿名 `Fin R_d` だけでは足りない。

必要なのは、

```text
どの block の
どの source time の
どの selected depth incidence が
exact-length charge 後に残ったのか
```

を保持する carrier じゃ。

有限集合論的には、次の構成が可能である。

### $E_d<B_d$ の場合

exact-length tokens を selected bucket へ任意に単射し、その image を取り除く。

$$
\operatorname{ResidualIncidence}(d) = \operatorname{SelectedBucket}(d)
\setminus
\operatorname{image}(\operatorname{ExactLengthTokens}(d))
$$

この cardinality は、

$$
B_d-E_d
$$

になる。

### $B_d\le E_d$ の場合

selected bucket 全体を exact-length tokens へ埋め込み、residual は空とする。

この構成は非計算的でもよい。

ただし依然として **非標準的・非時間的な matching** じゃ。

それでも source incidence を保持するため、upper-boundary transport の前段としては匿名 `Fin` より強い。

---

## 6. さらに重要：unordered residual と causal residual

現在の residual は block の時間順序を無視している。

例えば depth $d$ で、

```text
block 0:
  exact-length token 1

block 1:
  selected incidence 1
```

なら、総数としては、

$$
B_d=E_d=1
$$

なので、

$$
R_d=0
$$

じゃ。

しかし block $0$ の token を、未来の block $1$ の incidence の返済に使うことはできない。

したがって causal residual は正になる。

このため、将来の repayment / queue / Big に必要な量は、depth ごとの Lindley queue じゃ。

selected arrivals を $a_k(d)$、exact-length service を $e_k(d)$ として、

$$
Q_{q-1}(d)=0
$$

$$
Q_k(d)=\left(Q_{k-1}(d)+a_k(d)-e_k(d)\right)_+
$$

と置く。

その閉形式は、

$$
Q_m(d) = \max_{q\le t\le m} \left(\sum_{k=t}^{m}a_k(d)-\sum_{k=t}^{m}e_k(d)\right)_+
$$

じゃ。

一方、現在の unordered residual は、そのうち $t=q$ だけを見た、

$$
\left(\sum_{k=q}^{m}a_k(d)-\sum_{k=q}^{m}e_k(d)\right)_+
$$

にすぎない。

したがって、

$$
R_d^{\mathrm{unordered}}
\le
Q_m(d)
$$

である。

この depthwise causal residual は、cp-316 で構築した scalar queue / suffix Hall theorem の完全な固定-depth 版になる。

---

## 7. Global reduction の評価

今回の主 theorem は、

$$
|\operatorname{GlobalSelectedCarrier}| \le (m-q+1) + |\operatorname{SelectedResidualCarrier}|
$$

じゃ。

positive drift unit まで戻すと、

$$
|\operatorname{PositiveDriftUnits}| \le (m-q+1) + |\operatorname{SelectedResidualCarrier}| + \frac{m-q+2}{2}
$$

となった。

これは正確な有限還元である。

しかし、大域 Big に対しては、

```text
block count
saturated half-packing
```

も依然として線形成長し得る。

したがって「残る項は residual 一つ」と読むのではなく、

```text
既知の線形 charges:
  exact-length token
  isolated saturated token

未知の profile-dependent charge:
  selected residual
```

と読むのが正しい。

最終的には三者全てを、

- later negative drift
- finite upper boundary
- separator / NoLift obstruction

のいずれかへ輸送する必要がある。

---

## 8. Stage F の停止は genuine obstruction ではない

report は sliding pressure identity に必要な bridge が公開されていないとして停止した。

これは実装判断としては正しい。

しかし最新 snapshot を照合すると、証明パターンは既に存在している。

`UniversalPaymentRepayment.lean` には、

```lean
sum_endpointAccountingTerm_Icc_eq_bitWidth_sub
```

があり、

$$
\sum_{k=q}^{m}D_k = W_{m}-W_{\mathrm{start}(q)}
$$

を証明している。

その証明は、

```text
Icc q m = range (m + 1) \ range q
```

として `Finset.sum_sdiff_eq_sub` を使い、

- $q=0$
- $q=r+1$

を場合分けするものじゃ。

pressure でも全く同じ形が使える。

さらに、

```lean
canonicalBlockStartTime n q
```

は定義上、

```lean
canonicalEndpointBlockStart n q
```

そのものじゃ。

したがって不足 bridge は数学的には既に揃っている。

---

## 9. Sliding pressure theorem の正確な形

次に置くべき主 theorem はこれじゃ。

```lean
theorem canonicalWindowPressureMarginAtDepth_eq_prefix_sub
    (n : OddNat) {q m d : ℕ} (hqm : q ≤ m) :
    canonicalWindowPressureMarginAtDepth n q m d =
      SourcePressureMarginInt n (paymentEndpointSeq n m + 1) d -
        SourcePressureMarginInt n (canonicalBlockStartTime n q) d := by
  ...
```

証明は概ね次の通り。

```lean
have hsubset : Finset.range q ⊆ Finset.range (m + 1) := by
  intro i hi
  simp only [Finset.mem_range] at hi ⊢
  omega

have hIcc :
    Finset.Icc q m =
      Finset.range (m + 1) \ Finset.range q := by
  ext i
  simp
  omega

rw [canonicalWindowPressureMarginAtDepth, hIcc,
  Finset.sum_sdiff_eq_sub hsubset]

rw [sourcePressureMarginInt_paymentEndpointSeq_eq_sum_blockPressureContributionInt]

cases q with
| zero =>
    simp [canonicalBlockStartTime, canonicalEndpointBlockStart,
      SourcePressureMarginInt]
| succ r =>
    rw [show
      ∑ k ∈ Finset.range (r + 1),
          blockPressureContributionInt n k d =
        SourcePressureMarginInt n (paymentEndpointSeq n r + 1) d by
      symm
      exact
        sourcePressureMarginInt_paymentEndpointSeq_eq_sum_blockPressureContributionInt
          n r d]
    simp [canonicalBlockStartTime, canonicalEndpointBlockStart]
```

実際の `simp` 補題に合わせた微調整は要るが、数理的障害はない。

よって cp-322 の停止点は、

> **小さな caller-facing API gap**

であって、次の登頂障害ではない。

---

## 10. Carrier-level sliding window を作るべき

整数和だけで sliding theorem を作るより、現在の carrier 方針に合わせて source Finset も作る方がよい。

```lean
noncomputable def canonicalPaymentBlockWindow
    (n : OddNat) (q m : ℕ) : Finset ℕ :=
  Finset.biUnion (Finset.Icc q m) (canonicalPaymentBlock n)
```

そして、

$$
\operatorname{BlockWindow}(q,m) = \operatorname{Icc}(b_q,e_m)
$$

または、

$$
\operatorname{BlockWindow}(q,m) = \operatorname{range}(e_m+1) \setminus \operatorname{range}(b_q)
$$

を証明する。

これにより、任意の predicate $P$ について、

$$
|{i\in\operatorname{BlockWindow}(q,m)\mid P(i)}| = \sum_{k=q}^{m} |{i\in B_k\mid P(i)}|
$$

が得られる。

その後、

- continuation fiber
- recovery fiber
- pressure margin

を全て sliding-window carrier として構築できる。

これは将来の causal residual にも必要になる。

---

## 11. Active selected block と exact-length block は同じ block にならない

active selected block の selected depth を $d$ とする。

### terminal valuation $v=1$

このとき $d=1$。

positive nonsaturated なので、

$$
3\le L
$$

したがって、

$$
d+2\le L
$$

じゃ。

### terminal valuation $v\ge2$

このとき、

$$
d=v-1
$$

positive drift より、

$$
v<L
$$

なので、

$$
d+2=v+1\le L
$$

じゃ。

従って全ての場合に、

$$
d+2\le L
$$

となる。

一方 exact-length token は、

$$
L=d
$$

を要求する。

したがって、

> 同じ depth $d$ で、active selected block と exact-length block が同一 block になることはない。

これは次の theorem として固定できる。

```lean
theorem activeSelectedPressureBlock_not_exactLength
```

この分離は、actual residual incidence の構築を明瞭にする。

---

## 12. Saturated token の残る細分化

cp-320 までの成果から、positive nonsaturated successor が terminal valuation $v\ge2$ なら、

$$
D_{k+1}+1 \le |\operatorname{SelectedCarrier}_{k+1}|
$$

が期待できる。

nonsaturated なので、

$$
A\le L-1
$$

したがって、

$$
D=A-v\le L-v-1
$$

一方 selected carrier は、

$$
|\operatorname{Carrier}|=L-v
$$

じゃ。

よって一 unit の slack がある。

この slack へ直前の saturated token を charge できる。

残る saturated successor は、

```text
negative drift:
  token を実際に返済可能

zero drift:
  未解決

positive drift, terminal valuation 1:
  selected carrier に slack がない場合がある
```

まで狭められる。

---

## 13. Lean Comparator Challenge への位置

最終ゴールは、

```lean
theorem collatz_conjecture (n : ℕ) (hn : n > 0) :
  ∃ m, collatzStep^[m] n = 1
```

じゃ。

cp-322 はまだ収束を示していない。

しかし positive drift の内部は、

```text
positive drift units
  ↓
same-block selected incidence / saturation
  ↓
active depth bucket
  ↓
exact-length charge + unordered selected residual
```

まで圧縮された。

次に必要なのは、この unordered residual を、

```text
実在 residual incidence
causal depth queue
finite upper-boundary resource
```

へ順に持ち上げることじゃ。

---

## 判定まとめ

### Active bucket equivalence

**完成。**

### Global structural Fubini

**完成。**

### Exact-length token uniqueness

**完成。**

### Unordered selected residual

**完成。匿名 cardinality residual として正確。**

### Positive drift に対する真の最小 residual

**未実装。selected carrier slack が残る。**

### Causal residual

**未実装。unordered residual より強い。**

### Sliding pressure identity

**未実装だが、既存 sliding ledger の証明を移植すれば閉じる。**

### 真の次戦線

**actual drift-image residual と depthwise causal queue。**

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge FloatWindow branch after
report-petal-322.

The cp-322 implementation is accepted.

Stages A-E are complete, but refine the interpretation:

    canonicalSelectedResidualCount

is the minimal unordered cardinal residual of the full selected carrier after
granting unrestricted same-depth exact-length tokens.

It is not yet:

    an actual residual subset of selected source incidences;
    the minimal residual of positive drift units;
    or a causal future-payment residual.

The reported Stage-F obstruction is only a small public-API gap.  The existing
proof of `sum_endpointAccountingTerm_Icc_eq_bitWidth_sub` already provides the
exact sliding-sum pattern.

# Stage A — sliding pressure bridge

Prove:

    canonicalWindowPressureMarginAtDepth n q m d
      =
    SourcePressureMarginInt n (paymentEndpointSeq n m + 1) d
      -
    SourcePressureMarginInt n (canonicalBlockStartTime n q) d

for `q <= m`.

Reuse the exact proof pattern from:

    sum_endpointAccountingTerm_Icc_eq_bitWidth_sub.

Add the two intermediate public theorems:

    SourcePressureMarginInt n (canonicalBlockStartTime n q) d
      =
    sum k in range q, blockPressureContributionInt n k d

and:

    SourcePressureMarginInt n 0 d = 0.

The `q = 0` specialization must recover the existing endpoint-prefix theorem.

# Stage B — actual block-window carrier

Define:

    canonicalPaymentBlockWindow n q m

as the finite union of canonical blocks indexed by `Icc q m`.

For `q <= m`, prove:

    canonicalPaymentBlockWindow n q m
      =
    Finset.Icc
        (canonicalBlockStartTime n q)
        (paymentEndpointSeq n m)

and equivalently:

    =
    Finset.range (paymentEndpointSeq n m + 1)
      \ Finset.range (canonicalBlockStartTime n q).

Prove the generic filtered-card decomposition over this window.

Derive actual sliding continuation and recovery carriers before deriving the
integer pressure identity.

# Stage C — selected blocks lie strictly beyond exact length

For an active selected block at selected depth `d`, prove:

    d + 2 <= canonicalPaymentBlockLength n k.

Conclude:

    active selected block indices at depth d
      are disjoint from
    exact-length block indices at depth d.

Expose this theorem explicitly; it records that exact-length tokens come from
different blocks, not from the selected block itself.

# Stage D — terminology boundary

Keep `canonicalSelectedResidualCount` for compatibility, but add the alias or
documentation name:

    canonicalUnorderedSelectedCarrierResidualCount.

Prove:

    residual = max (selectedBucketCard - exactLengthCard) 0

in a convenient exact form.

State explicitly that the current `Fin residual` carrier has no source-time or
block coordinate.

# Stage E — actual positive-drift image carrier

For every positive nonsaturated block, construct a direct embedding:

    Fin (Int.toNat drift)
      ↪
    selected pressure carrier of that same block.

Define its actual image Finset/subtype:

    canonicalSelectedDriftImageCarrier n k.

Prove:

    image card = Int.toNat drift;
    image subset selected carrier;
    image empty outside positive nonsaturated blocks.

Bucket these actual drift images by selected depth.

Define:

    CanonicalSelectedDriftBucketCarrier n q m d.

This carrier should retain:

    block index;
    source time;
    selected depth.

# Stage F — drift residual versus carrier residual

Define the unordered drift residual:

    driftBucketCard - exactLengthCount.

Prove:

    unordered drift residual
      <=
    canonicalSelectedResidualCount.

Thus the cp-322 residual is a safe but potentially coarse upper bound caused by
unused selected-carrier slack.

Keep both quantities; do not silently rename one into the other.

# Stage G — actual residual incidence carrier

Construct a noncomputable actual residual source carrier at each depth.

Use a cardinality comparison by cases:

    exactLengthCount <= driftImageBucketCard
    or
    driftImageBucketCard <= exactLengthCount.

In the first branch, choose an injection from exact-length tokens into the
drift-image bucket and retain the complement of its image.

In the second branch, the residual carrier is empty.

Prove:

    actual residual incidence carrier
      is a subset of the drift-image bucket;

    its card
      =
    unordered drift residual.

Document that the chosen matching is noncanonical and unordered.

# Stage H — depthwise causal residual queue

Define per-block fixed-depth arrivals:

    selected drift-image units arriving at block k and depth d.

Define per-block fixed-depth service:

    one exact-length token when blockLength k = d.

For a window q..m define the reflected causal queue:

    queue before q = 0
    queue after k =
      (old queue + arrivals k) - service k.

Prove the Lindley identity:

    depthQueue q m d
      =
    max over t in Icc q m of
      positive part of
        arrivals on t..m - services on t..m.

Prove:

    unordered drift residual <= causal depth queue.

Give a concrete abstract regression showing why equality need not hold when
all exact-length services precede the selected arrivals.

# Stage I — fixed-depth temporal Hall theorem

Define actual claim units from the selected drift-image carrier and exact-length
service tokens.

Eligibility is temporal:

    claim.block <= service.block.

Prove:

    forward matching exists
      <->
    every suffix has claims <= services
      <->
    causal depth queue at m = 0.

Reuse the finite interval-order Hall construction from the scalar queue layer.

Do not interpret unordered residual zero as causal repayment.

# Stage J — prefix and relative profiles

After Stage A, define separate public profiles:

    canonicalPrefixPressureProfile
    canonicalRelativePressureIncrementProfile.

Only the prefix profile should reuse:

    IsSourcePressureDepth
    PressureFrontier
    PressureState.

For `q > 0`, relative positivity means growth from the block-start baseline,
not absolute positive pressure.

# Stage K — generic layer-cake

Prove a generic finite layer-cake theorem for both:

    unordered residual profiles;
    causal residual queue profiles;
    absolute or relative pressure amplitudes.

Do not apply local-island packing yet.

Record that the existing packing API counts supplied isolated centers, not all
superlevel depths.

# Stage L — saturated successor slack

For a positive nonsaturated block with terminal valuation at least two, prove:

    drift + 1 <= selected carrier card.

Use the spare unit to charge an immediately preceding saturated token.

Classify the remaining saturated successor cases:

    negative successor drift;
    zero successor drift;
    positive successor with terminal valuation one.

Do not count zero drift as repayment.

# Stage M — report correction

Update the cp-322 interpretation:

    selected residual is the only non-explicit profile term
    in the finite unordered carrier reduction,

but:

    block-count and saturated half-packing terms remain unbounded with
    excursion length;

and:

    unordered residual is not causal outstanding debt.

Stop at the first genuine obstruction among:

    block-window carrier equality fails;
    drift-image carrier cannot be constructed;
    actual residual complement cannot retain source incidence;
    causal depth queue does not admit the expected Lindley formula;
    temporal Hall matching fails;
    relative pressure cannot be separated from absolute pressure;
    saturated zero-drift successors have no charge.

Do not jump from unordered residual zero to future repayment.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-323.md
```

cp-322 は、selected carrier の中から「余った数」を取り出した。

次はその余りを、**実際の source incidence** として取り戻し、さらに **時間順序を持つ残債** へ変える番じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean
index d30edb19..dedd17ca 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean
@@ -147,6 +147,137 @@ theorem activeSelectedPressureDepthSupport_bucketCarrier_nonempty
   exact mem_canonicalSelectedPressureBlocksAtDepth.mpr
     ⟨(Finset.mem_filter.mp hdata.1).1, hdata.2⟩
 
+/-! ## Active selected buckets and structural Fubini -/
+
+/-- Selected incidences indexed only by positive nonsaturated blocks. -/
+def CanonicalActiveSelectedPressureBucketCarrier
+    (n : OddNat) (q m d : ℕ) :=
+  Σ k : {k : ℕ // k ∈ canonicalActiveSelectedPressureBlocksAtDepth n q m d},
+    {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val}
+
+/-- A selected bucket incidence proves that its block is nonsaturated: the
+selected carrier of a saturated block is empty. -/
+theorem CanonicalSelectedPressureBucketCarrier.block_not_saturated
+    {n : OddNat} {q m d : ℕ}
+    (x : CanonicalSelectedPressureBucketCarrier n q m d) :
+    ¬ CanonicalSaturatedBorderBlock n x.1.val := by
+  intro hs
+  have hempty := hs.selectedPressureCarrier_eq_empty
+  have hi := x.2.property
+  simp [hempty] at hi
+
+/-- Removing saturated blocks from a selected bucket loses no incidence. -/
+noncomputable def selectedPressureBucketEquivActive
+    (n : OddNat) (q m d : ℕ) :
+    CanonicalSelectedPressureBucketCarrier n q m d ≃
+      CanonicalActiveSelectedPressureBucketCarrier n q m d where
+  toFun x := ⟨⟨x.1.val,
+    mem_canonicalActiveSelectedPressureBlocksAtDepth.mpr
+      ⟨mem_canonicalNonsaturatedPositiveBlockIndices.mpr
+        ⟨(Finset.mem_filter.mp
+            (mem_canonicalSelectedPressureBlocksAtDepth.mp x.1.property).1).1,
+          (Finset.mem_filter.mp
+            (mem_canonicalSelectedPressureBlocksAtDepth.mp x.1.property).1).2,
+          x.block_not_saturated⟩,
+        (mem_canonicalSelectedPressureBlocksAtDepth.mp x.1.property).2⟩⟩, x.2⟩
+  invFun x := ⟨⟨x.1.val, mem_canonicalSelectedPressureBlocksAtDepth.mpr
+    ⟨Finset.mem_filter.mpr
+      ⟨(mem_canonicalNonsaturatedPositiveBlockIndices.mp
+          (mem_canonicalActiveSelectedPressureBlocksAtDepth.mp x.1.property).1).1,
+        (mem_canonicalNonsaturatedPositiveBlockIndices.mp
+          (mem_canonicalActiveSelectedPressureBlocksAtDepth.mp x.1.property).1).2.1⟩,
+      (mem_canonicalActiveSelectedPressureBlocksAtDepth.mp x.1.property).2⟩⟩, x.2⟩
+  left_inv := by
+    rintro ⟨k, i⟩
+    rfl
+  right_inv := by
+    rintro ⟨k, i⟩
+    rfl
+
+/-- The global selected carrier is structurally the dependent sum of active
+depth buckets.  The equivalence preserves both block and source incidence. -/
+noncomputable def globalSelectedPressureCarrierEquivActiveBuckets
+    (n : OddNat) (q m : ℕ) :
+    CanonicalGlobalSelectedPressureCarrier n q m ≃
+      Σ d : {d : ℕ // d ∈ canonicalActiveSelectedPressureDepthSupport n q m},
+        CanonicalActiveSelectedPressureBucketCarrier n q m d.val where
+  toFun x := by
+    have hnot : ¬ CanonicalSaturatedBorderBlock n x.1.val := by
+      intro hs
+      have hi := x.2.property
+      simp [hs.selectedPressureCarrier_eq_empty] at hi
+    have hnonsat : x.1.val ∈ canonicalNonsaturatedPositiveBlockIndices n q m :=
+      mem_canonicalNonsaturatedPositiveBlockIndices.mpr
+        ⟨(Finset.mem_filter.mp x.1.property).1,
+          (Finset.mem_filter.mp x.1.property).2, hnot⟩
+    let d := canonicalSelectedPositivePressureDepth n x.1.val
+    exact ⟨⟨d, Finset.mem_image.mpr ⟨x.1.val, hnonsat, rfl⟩⟩,
+      ⟨⟨x.1.val, mem_canonicalActiveSelectedPressureBlocksAtDepth.mpr
+        ⟨hnonsat, rfl⟩⟩, x.2⟩⟩
+  invFun x := ⟨⟨x.2.1.val,
+    Finset.mem_filter.mpr
+      ⟨(mem_canonicalNonsaturatedPositiveBlockIndices.mp
+          (mem_canonicalActiveSelectedPressureBlocksAtDepth.mp x.2.1.property).1).1,
+        (mem_canonicalNonsaturatedPositiveBlockIndices.mp
+          (mem_canonicalActiveSelectedPressureBlocksAtDepth.mp x.2.1.property).1).2.1⟩⟩,
+    x.2.2⟩
+  left_inv := by
+    rintro ⟨k, i⟩
+    rfl
+  right_inv := by
+    rintro ⟨⟨dv, hdv⟩, ⟨⟨kv, hkv⟩, ⟨iv, hiv⟩⟩⟩
+    have heq : canonicalSelectedPositivePressureDepth n kv = dv :=
+      (mem_canonicalActiveSelectedPressureBlocksAtDepth.mp hkv).2
+    subst dv
+    rfl
+
+/-! ## Exact-length tokens across active depths -/
+
+/-- Blocks of exact canonical length `d` in the closed interval `q..m`. -/
+noncomputable def canonicalExactLengthBlockIndicesAtDepth
+    (n : OddNat) (q m d : ℕ) : Finset ℕ := by
+  classical
+  exact (Finset.Icc q m).filter fun k => canonicalPaymentBlockLength n k = d
+
+/-- One exact-length recovery token for each active depth/block match. -/
+def CanonicalExactLengthTokenCarrier
+    (n : OddNat) (q m : ℕ) :=
+  Σ d : {d : ℕ // d ∈ canonicalActiveSelectedPressureDepthSupport n q m},
+    {k : ℕ // k ∈ canonicalExactLengthBlockIndicesAtDepth n q m d.val}
+
+/-- Forget depth while retaining the block address.  Injectivity is exactly
+uniqueness of the canonical block length. -/
+noncomputable def exactLengthTokenBlockEmbedding
+    (n : OddNat) (q m : ℕ) :
+    CanonicalExactLengthTokenCarrier n q m ↪ {k : ℕ // k ∈ Finset.Icc q m} where
+  toFun x := ⟨x.2.val, (Finset.mem_filter.mp x.2.property).1⟩
+  inj' := by
+    rintro ⟨d, k⟩ ⟨e, l⟩ h
+    have hkl : k.val = l.val := congrArg Subtype.val h
+    have hd : canonicalPaymentBlockLength n k.val = d.val :=
+      (Finset.mem_filter.mp k.property).2
+    have he0 : canonicalPaymentBlockLength n l.val = e.val :=
+      (Finset.mem_filter.mp l.property).2
+    have he : canonicalPaymentBlockLength n k.val = e.val := by
+      simpa [hkl] using he0
+    have hde : d = e := Subtype.ext (hd.symm.trans he)
+    subst e
+    have hke : k = l := Subtype.ext hkl
+    subst l
+    rfl
+
+/-- Exact-length charge over active depths uses at most one token per block. -/
+theorem natCard_exactLengthTokenCarrier_le_interval
+    {n : OddNat} {q m : ℕ} (hqm : q ≤ m) :
+    Nat.card (CanonicalExactLengthTokenCarrier n q m) ≤ m - q + 1 := by
+  have hcard := Nat.card_le_card_of_injective
+    (exactLengthTokenBlockEmbedding n q m)
+    (exactLengthTokenBlockEmbedding n q m).injective
+  have hraw : Nat.card (CanonicalExactLengthTokenCarrier n q m) ≤ m + 1 - q := by
+    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe,
+      Nat.card_Icc] using hcard
+  omega
+
 /-! ## Fixed-depth prefix embedding -/
 
 /-- Forgetting the canonical block sends a selected bucket incidence into the
@@ -243,12 +374,6 @@ theorem blockPressureContributionInt_eq_succCarrier_sub_exactLengthIndicator
     simp [heq, hd, hdl.le]
     omega
 
-/-- Blocks of exact canonical length `d` in the closed interval `q..m`. -/
-noncomputable def canonicalExactLengthBlockIndicesAtDepth
-    (n : OddNat) (q m d : ℕ) : Finset ℕ := by
-  classical
-  exact (Finset.Icc q m).filter fun k => canonicalPaymentBlockLength n k = d
-
 /-- Fixed-depth pressure summed on a closed canonical block interval. -/
 noncomputable def canonicalWindowPressureMarginAtDepth
     (n : OddNat) (q m d : ℕ) : ℤ :=
@@ -381,6 +506,247 @@ theorem exists_selectedPressureBucketEmbedding_exactLength_add_amplitude
   simpa only [← Nat.card_eq_fintype_card] using
     natCard_selectedPressureBucket_le_exactLength_add_pressureAmplitude (n := n) hd
 
+/-! ## Minimal selected residual -/
+
+/-- Minimal selected mass left after the available exact-length charge. -/
+noncomputable def canonicalSelectedResidualCount
+    (n : OddNat) (q m d : ℕ) : ℕ :=
+  Nat.card (CanonicalActiveSelectedPressureBucketCarrier n q m d) -
+    (canonicalExactLengthBlockIndicesAtDepth n q m d).card
+
+/-- Exact-length charge plus the minimal residual always covers the active
+selected bucket. -/
+theorem natCard_activeSelectedBucket_le_exactLength_add_residual
+    (n : OddNat) (q m d : ℕ) :
+    Nat.card (CanonicalActiveSelectedPressureBucketCarrier n q m d) ≤
+      (canonicalExactLengthBlockIndicesAtDepth n q m d).card +
+        canonicalSelectedResidualCount n q m d := by
+  unfold canonicalSelectedResidualCount
+  omega
+
+/-- Accounting embedding into exact-length tokens plus minimal residual units. -/
+theorem exists_activeSelectedBucketEmbedding_exactLength_add_residual
+    (n : OddNat) (q m d : ℕ) :
+    Nonempty (CanonicalActiveSelectedPressureBucketCarrier n q m d ↪
+      ({k : ℕ // k ∈ canonicalExactLengthBlockIndicesAtDepth n q m d} ⊕
+        Fin (canonicalSelectedResidualCount n q m d))) := by
+  classical
+  letI : Fintype (CanonicalActiveSelectedPressureBucketCarrier n q m d) := by
+    unfold CanonicalActiveSelectedPressureBucketCarrier
+    infer_instance
+  letI : Fintype {k : ℕ // k ∈ canonicalExactLengthBlockIndicesAtDepth n q m d} :=
+    Fintype.ofFinset (canonicalExactLengthBlockIndicesAtDepth n q m d) (by simp)
+  apply Function.Embedding.nonempty_iff_card_le.mpr
+  have htargetCard :
+      Fintype.card
+          ({k : ℕ // k ∈ canonicalExactLengthBlockIndicesAtDepth n q m d} ⊕
+            Fin (canonicalSelectedResidualCount n q m d)) =
+        (canonicalExactLengthBlockIndicesAtDepth n q m d).card +
+          canonicalSelectedResidualCount n q m d := by
+    calc
+      _ = Fintype.card
+            {k : ℕ // k ∈ canonicalExactLengthBlockIndicesAtDepth n q m d} +
+          Fintype.card (Fin (canonicalSelectedResidualCount n q m d)) :=
+        Fintype.card_sum
+      _ = _ := by rw [Fintype.card_coe, Fintype.card_fin]
+  rw [htargetCard]
+  simpa only [← Nat.card_eq_fintype_card] using
+    natCard_activeSelectedBucket_le_exactLength_add_residual n q m d
+
+/-- The minimal selected residual is bounded by full fixed-depth pressure
+amplitude.  The latter may also contain unselected continuation incidence. -/
+theorem selectedResidualCount_le_pressureAmplitude
+    {n : OddNat} {q m d : ℕ} (hd : 1 ≤ d) :
+    canonicalSelectedResidualCount n q m d ≤
+      Int.toNat (canonicalWindowPressureMarginAtDepth n q m d) := by
+  have hequivCard :
+      Nat.card (CanonicalActiveSelectedPressureBucketCarrier n q m d) =
+        Nat.card (CanonicalSelectedPressureBucketCarrier n q m d) :=
+    Nat.card_congr (selectedPressureBucketEquivActive n q m d).symm
+  have hfull :=
+    natCard_selectedPressureBucket_le_exactLength_add_pressureAmplitude
+      (n := n) (q := q) (m := m) hd
+  unfold canonicalSelectedResidualCount
+  rw [hequivCard]
+  omega
+
+/-- Residual units embed into the coarser full pressure-amplitude capacity. -/
+noncomputable def selectedResidualPressureAmplitudeEmbedding
+    {n : OddNat} {q m d : ℕ} (hd : 1 ≤ d) :
+    Fin (canonicalSelectedResidualCount n q m d) ↪
+      Fin (Int.toNat (canonicalWindowPressureMarginAtDepth n q m d)) :=
+  Fin.castLEEmb (selectedResidualCount_le_pressureAmplitude hd)
+
+/-! ## All-depth residual and full-amplitude carriers -/
+
+/-- Minimal selected residual units over active selected depths. -/
+def CanonicalSelectedResidualCarrier
+    (n : OddNat) (q m : ℕ) :=
+  Σ d : {d : ℕ // d ∈ canonicalActiveSelectedPressureDepthSupport n q m},
+    Fin (canonicalSelectedResidualCount n q m d.val)
+
+/-- Full window pressure-amplitude capacity over active selected depths. -/
+def CanonicalPositivePressureAmplitudeCarrier
+    (n : OddNat) (q m : ℕ) :=
+  Σ d : {d : ℕ // d ∈ canonicalActiveSelectedPressureDepthSupport n q m},
+    Fin (Int.toNat (canonicalWindowPressureMarginAtDepth n q m d.val))
+
+/-- Assemble the depthwise residual-to-amplitude embeddings. -/
+noncomputable def selectedResidualCarrierPressureAmplitudeEmbedding
+    (n : OddNat) (q m : ℕ) :
+    CanonicalSelectedResidualCarrier n q m ↪
+      CanonicalPositivePressureAmplitudeCarrier n q m :=
+  (Function.Embedding.refl _).sigmaMap fun d =>
+    selectedResidualPressureAmplitudeEmbedding (by
+      rcases mem_activeSelectedPressureDepthSupport_iff_nonempty.mp d.property with
+        ⟨k, hk⟩
+      have hdepth :=
+        (mem_canonicalActiveSelectedPressureBlocksAtDepth.mp hk).2
+      simpa [hdepth] using one_le_canonicalSelectedPositivePressureDepth n k)
+
+/-- Cardinality of the active-depth bucket sigma. -/
+theorem natCard_activeSelectedBuckets
+    (n : OddNat) (q m : ℕ) :
+    Nat.card
+        (Σ d : {d : ℕ // d ∈ canonicalActiveSelectedPressureDepthSupport n q m},
+        CanonicalActiveSelectedPressureBucketCarrier n q m d.val) =
+      ∑ d ∈ canonicalActiveSelectedPressureDepthSupport n q m,
+        Nat.card (CanonicalActiveSelectedPressureBucketCarrier n q m d) := by
+  classical
+  letI (d : {d : ℕ // d ∈ canonicalActiveSelectedPressureDepthSupport n q m}) :
+      Fintype (CanonicalActiveSelectedPressureBucketCarrier n q m d.val) := by
+    unfold CanonicalActiveSelectedPressureBucketCarrier
+    infer_instance
+  rw [Nat.card_sigma]
+  rw [Finset.univ_eq_attach]
+  exact Finset.sum_attach (canonicalActiveSelectedPressureDepthSupport n q m)
+    fun d => Nat.card (CanonicalActiveSelectedPressureBucketCarrier n q m d)
+
+/-- Cardinality of all exact-length tokens over active depths. -/
+theorem natCard_exactLengthTokenCarrier
+    (n : OddNat) (q m : ℕ) :
+    Nat.card (CanonicalExactLengthTokenCarrier n q m) =
+      ∑ d ∈ canonicalActiveSelectedPressureDepthSupport n q m,
+        (canonicalExactLengthBlockIndicesAtDepth n q m d).card := by
+  unfold CanonicalExactLengthTokenCarrier
+  rw [Nat.card_sigma]
+  simp_rw [Nat.card_eq_fintype_card, Fintype.card_coe]
+  rw [Finset.univ_eq_attach]
+  exact Finset.sum_attach (canonicalActiveSelectedPressureDepthSupport n q m)
+    fun d => (canonicalExactLengthBlockIndicesAtDepth n q m d).card
+
+/-- Cardinality of the all-depth minimal residual carrier. -/
+theorem natCard_selectedResidualCarrier
+    (n : OddNat) (q m : ℕ) :
+    Nat.card (CanonicalSelectedResidualCarrier n q m) =
+      ∑ d ∈ canonicalActiveSelectedPressureDepthSupport n q m,
+        canonicalSelectedResidualCount n q m d := by
+  unfold CanonicalSelectedResidualCarrier
+  rw [Nat.card_sigma]
+  simp_rw [Nat.card_eq_fintype_card, Fintype.card_fin]
+  rw [Finset.univ_eq_attach]
+  exact Finset.sum_attach (canonicalActiveSelectedPressureDepthSupport n q m)
+    fun d => canonicalSelectedResidualCount n q m d
+
+/-- Primary all-depth reduction: selected incidence is paid first by unique
+exact-length block tokens, and only the minimal selected residual remains. -/
+theorem natCard_globalSelectedPressureCarrier_le_exactLength_add_residual
+    (n : OddNat) (q m : ℕ) :
+    Nat.card (CanonicalGlobalSelectedPressureCarrier n q m) ≤
+      Nat.card (CanonicalExactLengthTokenCarrier n q m) +
+        Nat.card (CanonicalSelectedResidualCarrier n q m) := by
+  rw [Nat.card_congr (globalSelectedPressureCarrierEquivActiveBuckets n q m),
+    natCard_activeSelectedBuckets, natCard_exactLengthTokenCarrier,
+    natCard_selectedResidualCarrier, ← Finset.sum_add_distrib]
+  exact Finset.sum_le_sum fun d _ =>
+    natCard_activeSelectedBucket_le_exactLength_add_residual n q m d
+
+/-- Block-count form of the primary residual reduction. -/
+theorem natCard_globalSelectedPressureCarrier_le_interval_add_residual
+    {n : OddNat} {q m : ℕ} (hqm : q ≤ m) :
+    Nat.card (CanonicalGlobalSelectedPressureCarrier n q m) ≤
+      m - q + 1 + Nat.card (CanonicalSelectedResidualCarrier n q m) :=
+  (natCard_globalSelectedPressureCarrier_le_exactLength_add_residual n q m).trans
+    (Nat.add_le_add_right (natCard_exactLengthTokenCarrier_le_interval hqm) _)
+
+/-- The all-depth minimal residual is bounded by the coarser full-amplitude
+capacity.  This follows from an explicit depth-preserving embedding. -/
+theorem natCard_selectedResidualCarrier_le_pressureAmplitudeCarrier
+    (n : OddNat) (q m : ℕ) :
+    Nat.card (CanonicalSelectedResidualCarrier n q m) ≤
+      Nat.card (CanonicalPositivePressureAmplitudeCarrier n q m) := by
+  classical
+  letI : Fintype
+      {d : ℕ // d ∈ canonicalActiveSelectedPressureDepthSupport n q m} :=
+    Fintype.ofFinset (canonicalActiveSelectedPressureDepthSupport n q m) (by simp)
+  letI : Fintype (CanonicalSelectedResidualCarrier n q m) := by
+    unfold CanonicalSelectedResidualCarrier
+    infer_instance
+  letI : Fintype (CanonicalPositivePressureAmplitudeCarrier n q m) := by
+    unfold CanonicalPositivePressureAmplitudeCarrier
+    infer_instance
+  exact Nat.card_le_card_of_injective
+    (selectedResidualCarrierPressureAmplitudeEmbedding n q m)
+    (selectedResidualCarrierPressureAmplitudeEmbedding n q m).injective
+
+/-- Coarser amplitude corollary of the minimal residual reduction. -/
+theorem natCard_globalSelectedPressureCarrier_le_interval_add_pressureAmplitude
+    {n : OddNat} {q m : ℕ} (hqm : q ≤ m) :
+    Nat.card (CanonicalGlobalSelectedPressureCarrier n q m) ≤
+      m - q + 1 +
+        Nat.card (CanonicalPositivePressureAmplitudeCarrier n q m) :=
+  (natCard_globalSelectedPressureCarrier_le_interval_add_residual hqm).trans
+    (Nat.add_le_add_left
+      (natCard_selectedResidualCarrier_le_pressureAmplitudeCarrier n q m) _)
+
+/-- Positive drift reduced to block count, minimal selected residual, and the
+already isolated saturated-token packing term. -/
+theorem natCard_positiveDriftUnitCarrier_le_interval_add_residual_add_saturated
+    {n : OddNat} {q m : ℕ} (hqm : q ≤ m) :
+    Nat.card (CanonicalPositiveDriftUnitCarrier n q m) ≤
+      (m - q + 1 + Nat.card (CanonicalSelectedResidualCarrier n q m)) +
+        Nat.card {k : ℕ // k ∈ canonicalSaturatedBlockIndices n q m} := by
+  exact (natCard_positiveDriftUnitCarrier_le_global_add_saturated n q m).trans
+    (Nat.add_le_add_right
+      (natCard_globalSelectedPressureCarrier_le_interval_add_residual hqm) _)
+
+/-- Saturated packing yields a completely finite reduction whose only
+uncontrolled term is the minimal selected residual carrier. -/
+theorem natCard_positiveDriftUnitCarrier_le_interval_add_residual_add_half
+    {n : OddNat} {q m : ℕ} (hqm : q ≤ m) :
+    Nat.card (CanonicalPositiveDriftUnitCarrier n q m) ≤
+      (m - q + 1 + Nat.card (CanonicalSelectedResidualCarrier n q m)) +
+        (m - q + 2) / 2 := by
+  have hsat :
+      Nat.card {k : ℕ // k ∈ canonicalSaturatedBlockIndices n q m} ≤
+        (m - q + 2) / 2 := by
+    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
+      card_canonicalSaturatedBlockIndices_le_half n q m
+  exact
+    (natCard_positiveDriftUnitCarrier_le_interval_add_residual_add_saturated
+      hqm).trans (Nat.add_le_add_left hsat _)
+
+/-!
+## Prefix versus sliding-window pressure audit
+
+`canonicalWindowPressureMarginAtDepth n q m d` is the block sum on `q..m`.
+The existing public pressure theorem identifies only the prefix sum `0..m`
+with `SourcePressureMarginInt n (paymentEndpointSeq n m + 1) d`.
+
+The intended sliding identity therefore requires two explicit bridges that are
+not yet present as caller-facing theorems:
+
+1. split the finite block sum `0..m` into `0..q-1` and `q..m`;
+2. identify pressure at `canonicalBlockStartTime n q` with the `0..q-1`
+   prefix (with the separate base case `q = 0`).
+
+Until those bridges are proved, relative window pressure must not be treated as
+absolute `IsSourcePressureDepth`, and no level-zero pulse/packing theorem may be
+applied to its positive part.  This is the first genuine API obstruction after
+the completed finite residual reduction; it is a missing prefix-difference
+bridge, not evidence that the proposed identity is false.
+-/
+
 /-- Endpoint-prefix pressure is continuation mass one level deeper minus the
 number of exact-length recovery blocks. -/
 theorem sourcePressureMarginInt_paymentEndpointSeq_eq_continuation_succ_sub_exactLength
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-322.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-322.md
new file mode 100644
index 00000000..9a7030fe
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-322.md
@@ -0,0 +1,83 @@
+# Petal / FloatWindow implementation report - checkpoint 322
+
+## Result
+
+The fixed-depth accounting layer now distinguishes three finite objects:
+
+1. selected bucket mass;
+2. minimal selected residual after exact-length charge;
+3. full pressure amplitude, which may include unselected continuation mass.
+
+All added Lean declarations are no-sorry.
+
+## Structural cleanup
+
+`CanonicalActiveSelectedPressureBucketCarrier` indexes only positive,
+nonsaturated blocks.  It is explicitly equivalent to the old selected bucket:
+a saturated block cannot carry a selected incidence because its selected
+carrier is empty.
+
+An explicit global equivalence decomposes the global selected carrier into the
+dependent sum of active depth buckets.  It preserves block and source-incidence
+coordinates rather than merely proving equal cardinalities.
+
+## Exact-length charge
+
+`CanonicalExactLengthTokenCarrier` packages exact-length block tokens over all
+active depths.  Forgetting depth is injective because each block has one unique
+canonical length.  Consequently its cardinality is at most `m - q + 1` when
+`q <= m`.
+
+## Minimal residual
+
+At depth `d`, the new residual count is
+
+```text
+active selected bucket count - exact-length block count.
+```
+
+The active bucket embeds into exact-length tokens plus these residual units.
+The residual units in turn embed into full pressure-amplitude units.  This
+second target is intentionally described as upper capacity: it can contain
+continuation incidences that were never selected.
+
+## Global finite reduction
+
+The primary theorem is now
+
+```text
+global selected carrier
+  <= block interval cardinality + selected residual carrier.
+```
+
+The full-amplitude version is only a coarser corollary.  Combined with the
+existing saturated-token packing theorem, positive-drift units are bounded by
+
+```text
+block count + minimal selected residual + saturated half-packing term.
+```
+
+Thus the smallest genuinely uncontrolled mass is the selected residual, not
+the full pressure amplitude.
+
+## First stopping obstruction
+
+The next requested sliding identity is mathematically consistent with the
+block decomposition, but two caller-facing bridges are absent:
+
+- a finite-sum split of block prefixes into `0..q-1` and `q..m`;
+- an identification of pressure at `canonicalBlockStartTime n q` with the
+  preceding endpoint prefix, including the separate `q = 0` case.
+
+Until these are proved, sliding-window positivity cannot be identified with
+the existing absolute-prefix `IsSourcePressureDepth` API.  Likewise, current
+local-island packing counts supplied level-zero witnesses and does not control
+all superlevel amplitudes.
+
+## Next implementation
+
+Add the prefix-difference bridge in a small separate section or module.  Once
+it is established, define distinct prefix and relative amplitude carriers,
+then prove the generic finite layer-cake identity without invoking pulse
+packing.  Threshold-island generalization should follow only after that API
+separation is fixed.
````
`````
