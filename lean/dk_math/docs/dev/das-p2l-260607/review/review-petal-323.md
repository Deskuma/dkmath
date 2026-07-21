# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude

gch: 4b718050e7d46e1c1a9a7c406c65f962eb1763d5

## Report

(26m24s)

cp-323 を Stage G まで実装しました。

**確定した事実**

- sliding pressure は endpoint pressure と block-start pressure の差。
- `q = 0` では既存の prefix pressure と一致。
- block window は連続した実時刻区間。
- active selected block では `d + 2 ≤ blockLength`。
- selected block と同じ深さの exact-length block は必ず別 block。
- positive drift を同一 block 内の実 source incidence へ埋め込み可能。
- actual drift residual は従来の selected-carrier residual 以下。
- 非標準 matching の補集合として、block・depth・source time を保持する actual residual carrier を構成可能。
- その carrier の濃度は unordered drift residual と正確に一致。

Stage H は causal queue の段階です。既存 scalar queue は arrivals/service 固定なので、次に必要なのは汎用 Lindley queue API の抽出です。unordered residual を causal repayment と解釈していない点もコードコメントに固定しました。

検証済み:

- `lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude`
- `lake build DkMath.Collatz.PetalBridge.FloatWindow`
- `lake build DkMath.Collatz.PetalBridge`
- `git diff --check`
- 対象ファイル no-sorry

結果は [report-petal-323.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-323.md) に記録しました。

## Review

# cp-323 実装レビュー

## 結論

**全面採用。Stage A–G は正しく閉じた。**

cp-323 は、cp-322 の匿名 residual を次の二段階へ引き上げた。

$$
\text{positive drift unit} \hookrightarrow \text{同一 block 内の実 source incidence}
$$

$$
\text{unordered drift residual} = \text{非標準 matching 後に残る実 source incidence}
$$

これにより residual は、単なる `Fin R` ではなく、

- selected depth
- canonical block index
- orbit source time

を保持する実在 carrier になった。

同時に sliding pressure が endpoint prefix の差であること、canonical block window が連続した実時刻区間であることも固定された。

停止位置も正しい。

次に必要なのは、unordered matching をさらに加工することではない。

> **block 時間順序を持つ arrivals/service から causal outstanding queue を新しく作ること**

じゃ。

ただし、次の設計では順序が重要になる。

1. まず数値 cardinality だけの generic Lindley queue を抽出する。
2. その後で source-bearing claim carrier と temporal Hall matching を重ねる。
3. cp-323 の unordered residual complement は、causal queue の状態として使わない。

---

## 1. Sliding pressure bridge

今回、

```lean
canonicalWindowPressureMarginAtDepth_eq_endpoint_sub_start
```

によって、$q\le m$ なら、

$$
W_{q,m}(d) = M_{e_m+1}(d) - M_{b_q}(d)
$$

が証明された。

ここで、

- $W_{q,m}(d)$ は block $q,\ldots,m$ の pressure contribution
- $M_K(d)$ は `SourcePressureMarginInt n K d`
- $b_q$ は `canonicalBlockStartTime n q`
- $e_m$ は `paymentEndpointSeq n m`

じゃ。

$q=0$ では、

$$
W_{0,m}(d) = M_{e_m+1}(d)
$$

となり、既存 prefix theorem と完全に一致する。

これで、

```text
absolute prefix pressure
relative window pressure increment
```

が明確に分離された。

この区別を維持した判断は正しい。

$q>0$ で $W_{q,m}(d)>0$ だからといって、endpoint の absolute pressure が正とは限らない。

---

## 2. Canonical block window

新しい、

```lean
canonicalPaymentBlockWindow n q m
```

は、block $q,\ldots,m$ の実 source time の和集合じゃ。

$q\le m$ について、

$$
\operatorname{BlockWindow}(q,m) = \operatorname{Icc}(b_q,e_m)
$$

および、

$$
\operatorname{BlockWindow}(q,m) = \operatorname{range}(e_m+1) \setminus \operatorname{range}(b_q)
$$

が証明された。

これは非常に価値が高い。

canonical blocks が単に抽象的に partition されているだけでなく、

> 連続した block 区間は、orbit time 上でも穴のない一つの区間になる

ことが公開 API になった。

さらに任意の predicate $P$ について、

$$
|{i\in\operatorname{BlockWindow}(q,m)\mid P(i)}| = \sum_{k=q}^{m}|{i\in B_k\mid P(i)}|
$$

が得られた。

これにより、今後の continuation・recovery・carry・source-address の sliding theorem は同じ carrier API に乗せられる。

---

## 3. Actual sliding pressure carrier

今回、実 source Finset として、

```lean
canonicalPaymentBlockWindowContinuationFiber
canonicalPaymentBlockWindowRecoveryFiber
```

が追加された。

そして、

$$
W_{q,m}(d) = |\operatorname{Continuation}*{q,m}(d)| - |\operatorname{Recovery}*{q,m}(d)|
$$

が証明された。

これは整数和だけの identity より強い。

pressure contribution が、

```text
block contribution の形式和
```

ではなく、

```text
実際の orbit source incidence の signed cardinal balance
```

として固定されたからじゃ。

この carrier-level sliding window は、今後の Hall matching や boundary transport の正しい土台になる。

---

## 4. Active selected block と exact-length block の分離

active selected block が selected depth $d$ を持つなら、

$$
d+2\le L_k
$$

が証明された。

一方、depth $d$ の exact-length service block は、

$$
L_k=d
$$

を満たす。

したがって、同一 block が両方になることはない。

$$
\operatorname{ActiveSelectedBlocks}(d)\cap\operatorname{ExactLengthBlocks}(d)=\varnothing
$$

これは重要な構造事実じゃ。

exact-length token は selected block 自身から生じる自己相殺ではない。

> 長い block が発生させた selected arrival を、別の短い exact-length block が service する

という block 間取引になっている。

ここで causal order を導入する必然性が確定した。

---

## 5. Positive drift の実 source image

```lean
canonicalSelectedPositiveDriftEmbedding
```

により、positive nonsaturated block $k$ について、

$$
\operatorname{Fin}(D_k)\hookrightarrow\operatorname{SelectedCarrier}_k
$$

が構成された。

その有限 image が、

```lean
canonicalSelectedDriftImageCarrier
```

じゃ。

この carrier は、

- 同じ block 内に留まる
- source time を保持する
- cardinality が正確に `Int.toNat drift`
- positive nonsaturated branch 外では空

という性質を持つ。

cp-322 の selected carrier は drift より大きい可能性があった。

cp-323 ではその中から、実際の positive drift unit 数と同じ大きさの source subset を選び出した。

これは正しい精密化じゃ。

---

## 6. 非標準性の意味

ただし、

```lean
canonicalSelectedPositiveDriftEmbedding
```

は cardinality inequality から `Classical.choice` で選ばれている。

したがって image は source-bearing ではあるが、canonical ではない。

異なる証明選択では、別の source incidence が image に選ばれ得る。

それでも現在の目的には十分じゃ。

drift unit 自体が匿名 unit なので、ここで必要なのは、

> 実 source incidence によって drift unit を代表できる

という存在だけだからじゃ。

ただし、この image の具体的 source pattern に数論的意味を持たせてはならない。

---

## 7. Actual unordered residual carrier

depth $d$ の drift-image bucket の濃度を $A_d$、exact-length token 数を $S_d$ とする。

unordered drift residual は、

$$
R_d=(A_d-S_d)_+
$$

じゃ。

cp-323 は $S_d\le A_d$ の場合に exact-length tokens を drift image へ任意に単射し、その image の補集合を取った。

$A_d<S_d$ の場合は residual を空とした。

この結果、

```lean
CanonicalActualSelectedDriftResidualCarrier
```

が作られ、

$$
|\operatorname{ActualResidual}(d)|=R_d
$$

が証明された。

この carrier は、

- block
- depth
- source time

を保持する。

したがって「実 source-bearing residual」という呼び方は正しい。

---

## 8. ただし causal residual ではない

ここが最重要の意味境界じゃ。

現在選ばれる exact-length token と drift-image source の matching は、block order を一切見ない。

例えば二 block だけの抽象例を考える。

```text
block 0:
  arrival = 0
  service = 1

block 1:
  arrival = 1
  service = 0
```

総数では、

$$
\sum a_k=\sum s_k=1
$$

なので unordered residual は $0$ になる。

しかし block $0$ の service は、block $1$ で未来に到着する claim を払えない。

causal queue は block $1$ の後に $1$ 残る。

$$
R^{\mathrm{unordered}}=0<1=Q^{\mathrm{causal}}
$$

したがって cp-323 の actual residual carrier は、

> source incidence を持つ有限会計証明書

ではあるが、

> 時間方向に残っている未払い claim 集合

ではない。

report がこの境界を明記したのは正しい。

---

## 9. Window 拡張に対する非単調性

さらに、現在の actual residual carrier は window $q,\ldots,m$ ごとに `Classical.choice` で matching を作り直す。

したがって $m$ を $m+1$ へ延長したとき、

$$
\operatorname{Residual}(q,m)\subseteq\operatorname{Residual}(q,m+1)
$$

とも、

$$
\operatorname{Residual}(q,m+1)\subseteq\operatorname{Residual}(q,m)
$$

とも限らない。

以前 residual だった source が、新しい arbitrary matching では消え、別の source が residual になる可能性がある。

ゆえに、この carrier を再帰的な queue state として更新してはならない。

ここが generic Lindley queue を新しく作る理由じゃ。

---

## 10. 次は generic queue 抽出が正解

既存の、

```lean
canonicalOutstandingClaimQueue
canonicalLocalOutstandingClaimQueue
```

は Lindley reflection の必要な定理を既に持っている。

しかし arrivals と service が、

```lean
canonicalBlockClaimCount
canonicalBlockCapacityCount
```

に固定されている。

固定深さ版で必要なのは、

```text
arrivals(k,d):
  block k の selected drift-image unit 数

service(k,d):
  block k の長さが d なら 1、そうでなければ 0
```

じゃ。

同じ証明をもう一度複製するより、低位モジュールへ generic API を抽出する判断がよい。

推奨ファイルは、

```text
DkMath/Collatz/PetalBridge/FloatWindow/FiniteReflectedQueue.lean
```

じゃ。

後に他分野でも使うことが判明した時点で、`DkMath.Combinatorics` などへ昇格すればよい。

---

## 11. Generic Lindley queue の形

arrivals と service を任意の自然数列とする。

```lean
def finiteReflectedQueueFrom
    (arrivals service : ℕ → ℕ) (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 =>
      (finiteReflectedQueueFrom arrivals service q t +
        arrivals (q + t)) -
      service (q + t)
```

ここで $t$ は、block $q$ から何 block 処理したかを表す。

$q\le m$ のとき terminal queue は、

```lean
def finiteReflectedQueueOn
    (arrivals service : ℕ → ℕ) (q m : ℕ) : ℕ :=
  finiteReflectedQueueFrom arrivals service q (m - q + 1)
```

とすればよい。

signed window balance は、

```lean
def finiteSignedWindowBalance
    (arrivals service : ℕ → ℕ) (t m : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc t m, (arrivals k : ℤ) - service k
```

じゃ。

中心 theorem は、

$$
Q_{q,m}=\max_{q\le t\le m}\left(\sum_{k=t}^{m}(a_k-s_k)\right)_+
$$

となる。

---

## 12. Generic API で先に閉じるもの

最低限、次の theorem 群が必要じゃ。

```lean
finiteReflectedQueueFrom_zero
finiteReflectedQueueFrom_succ
finiteReflectedQueueFrom_succ_eq_intToNat

finiteSignedWindowBalance_self
finiteSignedWindowBalance_succ

intToNat_signedWindowBalance_le_reflectedQueue
reflectedQueue_eq_zero_or_exists_suffixWitness
reflectedQueue_eq_suffixMaximum

reflectedQueue_eq_zero_iff_all_suffix_nonpos
unorderedResidual_le_reflectedQueue
```

特に、

```lean
unorderedResidual_le_reflectedQueue
```

は、

$$
\left(\sum_{k=q}^{m}a_k-\sum_{k=q}^{m}s_k\right)*+\le Q*{q,m}
$$

を表す。

これは suffix maximum の候補 $t=q$ を選ぶだけで得られる。

cp-323 の unordered residual と causal queue の関係を直ちに与える theorem になる。

---

## 13. Fixed-depth arrivals/service

generic API が閉じたら、Collatz 側では次を定義する。

```lean
noncomputable def canonicalSelectedDriftArrivalCountAtDepth
    (n : OddNat) (k d : ℕ) : ℕ :=
  if canonicalSelectedPositivePressureDepth n k = d then
    (canonicalSelectedDriftImageCarrier n k).card
  else
    0
```

ただし、この数値は image の選択に依存しない。

positive nonsaturated block では image card が drift と等しく、それ以外では空だからじゃ。

より proof-independent にするなら、最初から、

```lean
noncomputable def canonicalSelectedDriftArrivalCountAtDepth
    (n : OddNat) (k d : ℕ) : ℕ :=
  if 0 < endpointAccountingTerm n k ∧
      ¬ CanonicalSaturatedBorderBlock n k ∧
      canonicalSelectedPositivePressureDepth n k = d then
    Int.toNat (endpointAccountingTerm n k)
  else
    0
```

と定義する方がよい。

その後、

```lean
theorem selectedDriftArrivalCountAtDepth_eq_imageCard
```

で source-bearing image と接続する。

service は、

```lean
def canonicalExactLengthServiceAtDepth
    (n : OddNat) (k d : ℕ) : ℕ :=
  if canonicalPaymentBlockLength n k = d then 1 else 0
```

でよい。

---

## 14. Fixed-depth causal queue

固定深さ $d$ の causal queue を、

```lean
noncomputable def canonicalSelectedDriftDepthQueue
    (n : OddNat) (q m d : ℕ) : ℕ :=
  finiteReflectedQueueOn
    (canonicalSelectedDriftArrivalCountAtDepth n · d)
    (canonicalExactLengthServiceAtDepth n · d)
    q m
```

として定義する。

すると、

$$
Q_{q,m}(d)=\max_{q\le t\le m}\left(A_{t,m}(d)-S_{t,m}(d)\right)_+
$$

が得られる。

そして cp-323 の unordered residual は、

$$
R_{q,m}(d)\le Q_{q,m}(d)
$$

となる。

ここで初めて、

```text
unordered balance
causal outstanding debt
```

の関係が Lean 上で固定される。

---

## 15. Temporal Hall theorem

generic queue の次には、claim/service carrier を作る。

```lean
def FiniteArrivalCarrier
    (arrivals : ℕ → ℕ) (q m : ℕ) :=
  Σ k : {k : ℕ // k ∈ Finset.Icc q m}, Fin (arrivals k)

def FiniteServiceCarrier
    (service : ℕ → ℕ) (q m : ℕ) :=
  Σ k : {k : ℕ // k ∈ Finset.Icc q m}, Fin (service k)
```

eligibility は、

$$
\operatorname{claimBlock}\le\operatorname{serviceBlock}
$$

じゃ。

既存 scalar queue 層と同じ nested-suffix Hall argument により、

$$
Q_{q,m}=0
$$

$$
\Longleftrightarrow\quad\forall t\in[q,m],\ \operatorname{Claims}[t,m]\le\operatorname{Service}[t,m]
$$

$$
\Longleftrightarrow\quad\text{forward temporal matching exists}
$$

が得られる。

この generic Hall theorem を一度作れば、

- scalar claim/capacity queue
- fixed-depth selected/exact-length queue
- 将来の saturated-token queue

へ再利用できる。

---

## 16. Actual source carrier は Hall 層で重ねる

numeric queue の証明では、source-bearing image carrierを直接使わない方がよい。

まず proof-independent な arrival count で queue を閉じる。

その後、temporal matching carrierを作るときに、

```lean
CanonicalSelectedDriftBucketCarrier
```

を claim carrierとして使う。

この順なら、

```text
数値的 queue theorem:
  classical source choice に依存しない

source-bearing Hall theorem:
  実 source time を保持する
```

と層を分けられる。

これは今後の upper-zero boundary transportにも重要じゃ。

---

## 17. cp-323 の最終的位置

現在の positive drift は、次まで解剖された。

```text
positive drift unit
  ↓ same-block source embedding
selected drift-image incidence
  ↓ unordered exact-length matching
actual unordered residual incidence
  ↓ 次 checkpoint
fixed-depth causal outstanding queue
```

cp-323 で「実体」は戻った。

次はそこへ「時間」を戻す段階じゃ。

---

## 判定まとめ

### Sliding pressure bridge

**完成。**

### Actual block window

**完成。連続実時刻区間として固定。**

### Actual continuation/recovery fibers

**完成。**

### Selected/exact-length block separation

**完成。**

### Same-block positive-drift source image

**完成。非標準だが cardinality は正確。**

### Actual unordered residual incidence

**完成。source-bearing だが非因果。**

### Generic Lindley API

**未実装。次 checkpoint の本体。**

### 真の次戦線

**fixed-depth causal queue と temporal Hall matching。**

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge FloatWindow branch after
report-petal-323.

The cp-323 implementation is accepted.

Stages A-G are complete:

    sliding prefix-difference pressure;
    actual contiguous canonical block windows;
    actual sliding continuation/recovery fibers;
    selected-depth versus exact-length separation;
    same-block positive-drift source images;
    actual source-bearing unordered residual incidence.

The actual residual complement is deliberately noncanonical and unordered.
Do not use it as a recursively updated queue state.  Its chosen matching may
change when the window is extended.

The next checkpoint must extract a generic Nat-valued reflected queue before
adding the fixed-depth Collatz specialization.

# Stage A — generic reflected queue module

Create:

    DkMath/Collatz/PetalBridge/FloatWindow/FiniteReflectedQueue.lean

Keep this module independent of Collatz-specific definitions.  Import only the
minimum Mathlib surface.

Define:

    finiteReflectedQueueFrom
        (arrivals service : Nat -> Nat)
        (q : Nat) : Nat -> Nat

with:

    queue 0 = 0
    queue (t + 1) =
      (queue t + arrivals (q + t)) - service (q + t).

Define the terminal window form for q <= m:

    finiteReflectedQueueOn arrivals service q m
      =
    finiteReflectedQueueFrom arrivals service q (m - q + 1).

Define the signed window balance:

    finiteSignedWindowBalance arrivals service t m
      =
    sum k in Icc t m,
      ((arrivals k : Int) - service k).

Do not use a source-bearing carrier in this numeric module.

# Stage B — generic Lindley reflection theorem

Prove:

    queue successor equation;
    Nat reflection as Int.toNat;
    singleton signed window;
    right-extension signed window.

Then prove:

    every positive suffix balance <= terminal queue;

    terminal queue = 0
      or
    terminal queue is attained by one suffix balance;

    terminal queue =
      maximum over t in Icc q m of
        Int.toNat (signed balance on t..m).

Use the existing proof pattern from
`UniversalPaymentScalarQueue.lean`, but move the generic reasoning here rather
than copying it into the depth specialization.

# Stage C — generic zero and unordered-residual theorems

Prove:

    terminal queue = 0
      <->
    every suffix balance is nonpositive.

Define total unordered residual:

    Int.toNat (signed balance on q..m).

Prove:

    unordered residual <= terminal queue.

Add the exact regression:

    arrivals 0 = 0
    service 0 = 1
    arrivals 1 = 1
    service 1 = 0

for which:

    unordered residual on 0..1 = 0
    causal terminal queue on 0..1 = 1.

This regression must remain as the semantic guardrail.

# Stage D — generic interval-order Hall layer

Define finite carriers:

    FiniteArrivalWindowCarrier arrivals q m
      =
    Sigma k in Icc q m, Fin (arrivals k)

    FiniteServiceWindowCarrier service q m
      =
    Sigma k in Icc q m, Fin (service k).

Define forward eligibility:

    claim.block <= slot.block.

Prove:

    a forward injection implies every suffix Hall inequality;

    every suffix Hall inequality constructs a forward injection.

Reuse the nested-minimum Hall proof from
`canonicalEndpointForwardWindowMatching_of_suffixClaims_le_capacity`.

Conclude:

    terminal queue = 0
      <->
    every suffix has arrivals <= service
      <->
    a forward temporal matching exists.

# Stage E — refactor the scalar queue as an instance

Import `FiniteReflectedQueue` into
`UniversalPaymentScalarQueue.lean`.

Expose the existing canonical scalar queue as an instance or theorem-level
specialization of the generic queue using:

    arrivals = canonicalBlockClaimCount n
    service = canonicalBlockCapacityCount n.

Preserve the existing public theorem names for compatibility.

Avoid rewriting the whole scalar module if compatibility wrappers suffice.

# Stage F — proof-independent fixed-depth arrivals

In `UniversalPaymentAmplitude.lean`, define:

    canonicalSelectedDriftArrivalCountAtDepth n k d

directly from:

    positive drift;
    nonsaturation;
    selectedPositivePressureDepth = d;
    Int.toNat endpointAccountingTerm.

Do not define the numeric arrival count from the classically chosen image.

Prove that it equals the cardinality of the corresponding local selected
drift-image carrier.

Then prove:

    Nat.card (CanonicalSelectedDriftBucketCarrier n q m d)
      =
    sum k in Icc q m,
      canonicalSelectedDriftArrivalCountAtDepth n k d.

# Stage G — fixed-depth exact-length service

Define:

    canonicalExactLengthServiceAtDepth n k d :=
      if canonicalPaymentBlockLength n k = d then 1 else 0.

Prove:

    sum k in Icc q m,
      canonicalExactLengthServiceAtDepth n k d
      =
    card (canonicalExactLengthBlockIndicesAtDepth n q m d).

# Stage H — fixed-depth causal queue

Define:

    canonicalSelectedDriftDepthQueue n q m d

as the generic reflected queue with the fixed-depth arrivals and service.

For q <= m prove:

    queue =
      maximum positive suffix imbalance of selected drift arrivals
      against exact-length service.

Prove:

    canonicalUnorderedSelectedDriftResidualCount n q m d
      <=
    canonicalSelectedDriftDepthQueue n q m d.

Do not compare the queue to
`canonicalActualSelectedDriftResidualCarrier` as a set; that carrier depends on
an unordered classical matching.  Compare cardinalities only.

# Stage I — source-bearing temporal matching

Instantiate the generic forward Hall theorem with:

    claims:
      actual selected drift-image incidences, retaining block and source time;

    service:
      exact-length block tokens.

Prove:

    fixed-depth causal queue = 0
      <->
    a source-bearing forward matching exists.

The matching may forget source time on the service side, but it must retain the
claim source coordinate.

# Stage J — causal residual carrier

Only after Stage I, define an actual causal outstanding claim carrier if useful.

It should be the unmatched claims under a forward-maximal matching or an
abstract carrier of cardinality equal to the causal queue.

Do not reuse the cp-323 unordered complement under a new name.

# Stage K — all-depth causal carrier

Package:

    Sigma d in active selected-depth support,
      Fin (canonicalSelectedDriftDepthQueue n q m d).

Compare:

    unordered drift residual carrier
      <=
    all-depth causal carrier.

Keep depths independent at this checkpoint.  Do not yet assert that service or
boundary resources can be shared across depths.

# Stage L — saturated successor slack

In parallel, prove for a positive nonsaturated block with terminal valuation
at least two:

    Int.toNat drift + 1
      <=
    selected pressure carrier card.

Use the spare selected incidence to charge an immediately preceding saturated
token.

Keep these branches unresolved:

    zero-drift successor;
    positive successor with terminal valuation one.

# Stage M — stopping rule

Stop at the first genuine obstruction among:

    generic suffix-maximum reflection cannot be abstracted;
    generic temporal Hall construction requires additional order structure;
    scalar queue compatibility cannot be preserved;
    fixed-depth arrival count does not equal drift-image cardinality;
    exact-length service does not reproduce the token count;
    unordered residual is not bounded by the causal queue;
    source-bearing forward matching cannot be instantiated;
    saturated zero-drift successors have no charge.

Do not resume pressure-superlevel packing before the causal residual layer is
stable.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-324.md
```

cp-323 で、残差は source incidence になった。

cp-324 では、その incidence に **時間の矢** を与えるのじゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean
index dedd17ca..af59922b 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean
@@ -726,25 +726,531 @@ theorem natCard_positiveDriftUnitCarrier_le_interval_add_residual_add_half
     (natCard_positiveDriftUnitCarrier_le_interval_add_residual_add_saturated
       hqm).trans (Nat.add_le_add_left hsat _)

-/-!
-## Prefix versus sliding-window pressure audit
+/-! ## Prefix versus sliding-window pressure
+
+The following bridge fixes the endpoint interpretation precisely.  Absolute
+source pressure at a canonical block start is the contribution of all earlier
+blocks.  Consequently the pressure contributed by blocks `q..m` is the
+difference between pressure after block `m` and pressure before block `q`.
+
+This remains a relative increment.  It must not be passed to an API requiring
+an absolute `IsSourcePressureDepth` without separately proving the relevant
+prefix-pressure hypothesis.
+-/
+
+/-- The empty source window has zero pressure at every depth. -/
+theorem sourcePressureMarginInt_zero (n : OddNat) (d : ℕ) :
+    SourcePressureMarginInt n 0 d = 0 := by
+  simp [SourcePressureMarginInt, orbitWindowContinuationSiblingMassPow2,
+    orbitWindowRetentionMassPow2]
+
+/-- Pressure at the start of block `q` is the contribution of blocks strictly
+before `q`. -/
+theorem sourcePressureMarginInt_canonicalBlockStartTime_eq_sum_range
+    (n : OddNat) (q d : ℕ) :
+    SourcePressureMarginInt n (canonicalBlockStartTime n q) d =
+      ∑ k ∈ Finset.range q, blockPressureContributionInt n k d := by
+  cases q with
+  | zero =>
+      simp [canonicalBlockStartTime, canonicalEndpointBlockStart,
+        sourcePressureMarginInt_zero]
+  | succ q =>
+      simpa [canonicalBlockStartTime, canonicalEndpointBlockStart] using
+        sourcePressureMarginInt_paymentEndpointSeq_eq_sum_blockPressureContributionInt
+          n q d
+
+/-- Sliding pressure is the endpoint-prefix pressure minus the pressure already
+present at the beginning of the selected block window. -/
+theorem canonicalWindowPressureMarginAtDepth_eq_endpoint_sub_start
+    (n : OddNat) {q m : ℕ} (hqm : q ≤ m) (d : ℕ) :
+    canonicalWindowPressureMarginAtDepth n q m d =
+      SourcePressureMarginInt n (paymentEndpointSeq n m + 1) d -
+        SourcePressureMarginInt n (canonicalBlockStartTime n q) d := by
+  have hsubset : Finset.range q ⊆ Finset.range (m + 1) := by
+    intro i hi
+    simp only [Finset.mem_range] at hi ⊢
+    omega
+  have hIcc : Finset.Icc q m = Finset.range (m + 1) \ Finset.range q := by
+    ext i
+    simp
+    omega
+  unfold canonicalWindowPressureMarginAtDepth
+  rw [hIcc, Finset.sum_sdiff_eq_sub hsubset,
+    ← sourcePressureMarginInt_paymentEndpointSeq_eq_sum_blockPressureContributionInt,
+    ← sourcePressureMarginInt_canonicalBlockStartTime_eq_sum_range]
+
+/-- At block zero, sliding pressure recovers the existing endpoint-prefix
+pressure theorem exactly. -/
+theorem canonicalWindowPressureMarginAtDepth_zero_eq_endpoint
+    (n : OddNat) (m d : ℕ) :
+    canonicalWindowPressureMarginAtDepth n 0 m d =
+      SourcePressureMarginInt n (paymentEndpointSeq n m + 1) d := by
+  rw [canonicalWindowPressureMarginAtDepth_eq_endpoint_sub_start n (Nat.zero_le m),
+    canonicalBlockStartTime, canonicalEndpointBlockStart,
+    sourcePressureMarginInt_zero, sub_zero]
+
+/-! ## Actual canonical block-window carrier -/
+
+/-- The actual source times belonging to canonical blocks `q..m`. -/
+noncomputable def canonicalPaymentBlockWindow
+    (n : OddNat) (q m : ℕ) : Finset ℕ :=
+  (Finset.Icc q m).biUnion (canonicalPaymentBlock n)
+
+/-- A canonical block is the interval from its proof-independent start time to
+its endpoint. -/
+theorem canonicalPaymentBlock_eq_Icc_startTime_endpoint
+    (n : OddNat) (k : ℕ) :
+    canonicalPaymentBlock n k =
+      Finset.Icc (canonicalBlockStartTime n k) (paymentEndpointSeq n k) := by
+  rw [canonicalPaymentBlock_eq_Icc_universalPaymentBlockStart,
+    canonicalBlockStartTime_eq_universalPaymentBlockStart]
+
+/-- The union of consecutive canonical blocks is one closed orbit-time
+interval. -/
+theorem canonicalPaymentBlockWindow_eq_Icc
+    (n : OddNat) {q m : ℕ} (hqm : q ≤ m) :
+    canonicalPaymentBlockWindow n q m =
+      Finset.Icc (canonicalBlockStartTime n q) (paymentEndpointSeq n m) := by
+  classical
+  ext i
+  constructor
+  · intro hi
+    rcases Finset.mem_biUnion.mp hi with ⟨k, hk, hik⟩
+    rcases Finset.mem_Icc.mp hk with ⟨hqk, hkm⟩
+    rw [canonicalPaymentBlock_eq_Icc_startTime_endpoint] at hik
+    rcases Finset.mem_Icc.mp hik with ⟨hstart, hend⟩
+    apply Finset.mem_Icc.mpr
+    constructor
+    · cases q with
+      | zero =>
+          simp [canonicalBlockStartTime, canonicalEndpointBlockStart]
+      | succ q =>
+          cases k with
+          | zero => omega
+          | succ k =>
+              have he : paymentEndpointSeq n q ≤ paymentEndpointSeq n k :=
+                (strictMono_paymentEndpointSeq n).monotone (by omega)
+              simpa [canonicalBlockStartTime, canonicalEndpointBlockStart] using
+                (Nat.add_le_add_right he 1).trans hstart
+    · exact hend.trans ((strictMono_paymentEndpointSeq n).monotone hkm)
+  · intro hi
+    rcases Finset.mem_Icc.mp hi with ⟨hstartQ, hendM⟩
+    rcases existsUnique_mem_canonicalPaymentBlock n i with ⟨k, hik, _⟩
+    have hikBounds : canonicalBlockStartTime n k ≤ i ∧
+        i ≤ paymentEndpointSeq n k := by
+      rw [canonicalPaymentBlock_eq_Icc_startTime_endpoint] at hik
+      exact Finset.mem_Icc.mp hik
+    have hqk : q ≤ k := by
+      by_contra hnot
+      have hkq : k < q := Nat.lt_of_not_ge hnot
+      cases q with
+      | zero => omega
+      | succ q =>
+          have he : paymentEndpointSeq n k ≤ paymentEndpointSeq n q :=
+            (strictMono_paymentEndpointSeq n).monotone (by omega)
+          simp [canonicalBlockStartTime, canonicalEndpointBlockStart] at hstartQ
+          omega
+    have hkm : k ≤ m := by
+      by_contra hnot
+      have hmk : m < k := Nat.lt_of_not_ge hnot
+      cases k with
+      | zero => omega
+      | succ k =>
+          have he : paymentEndpointSeq n m ≤ paymentEndpointSeq n k :=
+            (strictMono_paymentEndpointSeq n).monotone (by omega)
+          simp [canonicalBlockStartTime, canonicalEndpointBlockStart] at hikBounds
+          omega
+    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_Icc.mpr ⟨hqk, hkm⟩, hik⟩
+
+/-- Difference-of-prefixes form of the actual block window. -/
+theorem canonicalPaymentBlockWindow_eq_range_sdiff
+    (n : OddNat) {q m : ℕ} (hqm : q ≤ m) :
+    canonicalPaymentBlockWindow n q m =
+      Finset.range (paymentEndpointSeq n m + 1) \
+        Finset.range (canonicalBlockStartTime n q) := by
+  rw [canonicalPaymentBlockWindow_eq_Icc n hqm]
+  ext i
+  simp
+  omega
+
+/-- Filtering the actual block window decomposes into the disjoint filtered
+canonical blocks retaining their block indices. -/
+theorem card_filter_canonicalPaymentBlockWindow_eq_sum
+    (n : OddNat) {q m : ℕ} (p : ℕ → Prop) [DecidablePred p] :
+    ((canonicalPaymentBlockWindow n q m).filter p).card =
+      ∑ k ∈ Finset.Icc q m, ((canonicalPaymentBlock n k).filter p).card := by
+  classical
+  unfold canonicalPaymentBlockWindow
+  rw [Finset.filter_biUnion]
+  exact Finset.card_biUnion fun k hk l hl hne =>
+    (disjoint_canonicalPaymentBlock_of_ne n hne).mono
+      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
+
+/-- Actual source incidences in the block window continuing beyond depth `d`. -/
+noncomputable def canonicalPaymentBlockWindowContinuationFiber
+    (n : OddNat) (q m d : ℕ) : Finset ℕ := by
+  classical
+  exact (canonicalPaymentBlockWindow n q m).filter fun i =>
+    OrbitDepthContinuesBeyond n i d
+
+/-- Actual source incidences in the block window recovering exactly at depth
+`d`. -/
+noncomputable def canonicalPaymentBlockWindowRecoveryFiber
+    (n : OddNat) (q m d : ℕ) : Finset ℕ := by
+  classical
+  exact (canonicalPaymentBlockWindow n q m).filter fun i =>
+    OrbitDepthRecoversExactlyAt n i d
+
+/-- Sliding continuation incidence decomposes blockwise without losing source
+coordinates. -/
+theorem card_canonicalPaymentBlockWindowContinuationFiber_eq_sum
+    (n : OddNat) (q m d : ℕ) :
+    (canonicalPaymentBlockWindowContinuationFiber n q m d).card =
+      ∑ k ∈ Finset.Icc q m,
+        (canonicalPaymentBlockContinuationFiber n k d).card := by
+  classical
+  unfold canonicalPaymentBlockWindowContinuationFiber
+  unfold canonicalPaymentBlockContinuationFiber
+  exact card_filter_canonicalPaymentBlockWindow_eq_sum n _
+
+/-- Sliding exact-recovery incidence decomposes blockwise without losing
+source coordinates. -/
+theorem card_canonicalPaymentBlockWindowRecoveryFiber_eq_sum
+    (n : OddNat) (q m d : ℕ) :
+    (canonicalPaymentBlockWindowRecoveryFiber n q m d).card =
+      ∑ k ∈ Finset.Icc q m,
+        (canonicalPaymentBlockRecoveryFiber n k d).card := by
+  classical
+  unfold canonicalPaymentBlockWindowRecoveryFiber
+  unfold canonicalPaymentBlockRecoveryFiber
+  exact card_filter_canonicalPaymentBlockWindow_eq_sum n _
+
+/-- The integer sliding pressure is the signed cardinal balance of the two
+actual source-incidence fibers. -/
+theorem canonicalWindowPressureMarginAtDepth_eq_actualFiberCard_sub
+    (n : OddNat) (q m d : ℕ) :
+    canonicalWindowPressureMarginAtDepth n q m d =
+      ((canonicalPaymentBlockWindowContinuationFiber n q m d).card : ℤ) -
+        (canonicalPaymentBlockWindowRecoveryFiber n q m d).card := by
+  rw [card_canonicalPaymentBlockWindowContinuationFiber_eq_sum,
+    card_canonicalPaymentBlockWindowRecoveryFiber_eq_sum]
+  unfold canonicalWindowPressureMarginAtDepth
+  simp_rw [blockPressureContributionInt]
+  push_cast
+  rw [Finset.sum_sub_distrib]
+
+/-! ## Selected-depth separation from exact-length blocks -/
+
+/-- An active selected depth leaves at least one continuation level after its
+selected carrier.  Hence its block length is at least `d + 2`. -/
+theorem activeSelectedPressureBlock_depth_add_two_le_length
+    {n : OddNat} {q m d k : ℕ}
+    (hk : k ∈ canonicalActiveSelectedPressureBlocksAtDepth n q m d) :
+    d + 2 ≤ canonicalPaymentBlockLength n k := by
+  have hdata := mem_canonicalActiveSelectedPressureBlocksAtDepth.mp hk
+  have hnonsat := mem_canonicalNonsaturatedPositiveBlockIndices.mp hdata.1
+  have hcard := endpointAccountingTerm_le_card_selectedPressureCarrier
+    hnonsat.2.1 hnonsat.2.2
+  have hcardPos : 0 < (canonicalSelectedPressureCarrier n k).card := by
+    exact_mod_cast hnonsat.2.1.trans_le hcard
+  unfold canonicalSelectedPressureCarrier at hcardPos
+  rw [canonicalPaymentBlockContinuationFiber_card, hdata.2] at hcardPos
+  omega
+
+/-- Active selected blocks at depth `d` and exact-length blocks at depth `d`
+are disjoint.  Exact-length charge therefore always comes from another block. -/
+theorem disjoint_activeSelectedPressureBlocks_exactLengthBlocks
+    (n : OddNat) (q m d : ℕ) :
+    Disjoint (canonicalActiveSelectedPressureBlocksAtDepth n q m d)
+      (canonicalExactLengthBlockIndicesAtDepth n q m d) := by
+  classical
+  rw [Finset.disjoint_left]
+  intro k hkActive hkExact
+  have hlen := activeSelectedPressureBlock_depth_add_two_le_length hkActive
+  have heq := (Finset.mem_filter.mp hkExact).2
+  omega
+
+/-! ## Unordered residual terminology -/
+
+/-- Explicit name for the cp-322 cardinal residual.  This natural number has
+no source-time or block coordinate and makes no causal matching claim. -/
+noncomputable def canonicalUnorderedSelectedCarrierResidualCount
+    (n : OddNat) (q m d : ℕ) : ℕ :=
+  canonicalSelectedResidualCount n q m d
+
+/-- Exact cardinal-subtraction normal form of the unordered selected residual. -/
+theorem canonicalUnorderedSelectedCarrierResidualCount_eq
+    (n : OddNat) (q m d : ℕ) :
+    canonicalUnorderedSelectedCarrierResidualCount n q m d =
+      Nat.card (CanonicalActiveSelectedPressureBucketCarrier n q m d) -
+        (canonicalExactLengthBlockIndicesAtDepth n q m d).card := by
+  rfl
+
+/-- Max-with-zero presentation used when comparing the natural residual with
+integer positive-part formulas. -/
+theorem canonicalUnorderedSelectedCarrierResidualCount_eq_max_sub_zero
+    (n : OddNat) (q m d : ℕ) :
+    canonicalUnorderedSelectedCarrierResidualCount n q m d =
+      max (Nat.card (CanonicalActiveSelectedPressureBucketCarrier n q m d) -
+        (canonicalExactLengthBlockIndicesAtDepth n q m d).card) 0 := by
+  simp [canonicalUnorderedSelectedCarrierResidualCount,
+    canonicalSelectedResidualCount]
+
+/-! ## Actual selected drift-image carrier -/
+
+/-- Positive nonsaturated drift embeds directly into selected source
+incidences of the same block; no saturated summand or cross-block transport is
+used. -/
+noncomputable def canonicalSelectedPositiveDriftEmbedding
+    {n : OddNat} {k : ℕ}
+    (hpos : 0 < endpointAccountingTerm n k)
+    (hnot : ¬ CanonicalSaturatedBorderBlock n k) :
+    Fin (Int.toNat (endpointAccountingTerm n k)) ↪
+      {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} := by
+  classical
+  letI : Fintype {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} :=
+    Fintype.ofFinset (canonicalSelectedPressureCarrier n k) (by simp)
+  apply Classical.choice
+  apply Function.Embedding.nonempty_iff_card_le.mpr
+  rw [Fintype.card_fin, Fintype.card_coe]
+  have hle := endpointAccountingTerm_le_card_selectedPressureCarrier hpos hnot
+  have hcast : ((Int.toNat (endpointAccountingTerm n k) : ℕ) : ℤ) =
+      endpointAccountingTerm n k := by
+    exact Int.toNat_of_nonneg hpos.le
+  omega
+
+/-- The noncanonical finite image of positive drift inside the selected source
+carrier.  Its elements still carry the actual source time. -/
+noncomputable def canonicalSelectedDriftImageCarrier
+    (n : OddNat) (k : ℕ) :
+    Finset {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} := by
+  classical
+  by_cases h : 0 < endpointAccountingTerm n k ∧
+      ¬ CanonicalSaturatedBorderBlock n k
+  · exact Finset.univ.map (canonicalSelectedPositiveDriftEmbedding h.1 h.2)
+  · exact ∅
+
+/-- The selected drift image has exactly the positive drift cardinality on a
+positive nonsaturated block. -/
+theorem card_canonicalSelectedDriftImageCarrier
+    {n : OddNat} {k : ℕ}
+    (hpos : 0 < endpointAccountingTerm n k)
+    (hnot : ¬ CanonicalSaturatedBorderBlock n k) :
+    (canonicalSelectedDriftImageCarrier n k).card =
+      Int.toNat (endpointAccountingTerm n k) := by
+  classical
+  simp [canonicalSelectedDriftImageCarrier, hpos, hnot]
+
+/-- Every drift-image element is definitionally a selected source incidence. -/
+theorem canonicalSelectedDriftImageCarrier_source_mem
+    {n : OddNat} {k : ℕ}
+    (x : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k})
+    (_hx : x ∈ canonicalSelectedDriftImageCarrier n k) :
+    x.val ∈ canonicalSelectedPressureCarrier n k :=
+  x.property
+
+/-- Outside the positive nonsaturated branch there is no selected drift
+image. -/
+theorem canonicalSelectedDriftImageCarrier_eq_empty_of_not_active
+    {n : OddNat} {k : ℕ}
+    (h : ¬ (0 < endpointAccountingTerm n k ∧
+      ¬ CanonicalSaturatedBorderBlock n k)) :
+    canonicalSelectedDriftImageCarrier n k = ∅ := by
+  classical
+  simp [canonicalSelectedDriftImageCarrier, h]
+
+/-- Actual positive-drift images bucketed by selected depth.  The sigma keeps
+the block index, while the inner subtype keeps the source time. -/
+def CanonicalSelectedDriftBucketCarrier
+    (n : OddNat) (q m d : ℕ) :=
+  Σ k : {k : ℕ // k ∈ canonicalActiveSelectedPressureBlocksAtDepth n q m d},
+    {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} //
+      i ∈ canonicalSelectedDriftImageCarrier n k.val}
+
+/-- Forgetting image membership embeds the actual drift bucket into the full
+active selected bucket without changing block or source coordinates. -/
+def selectedDriftBucketActiveSelectedEmbedding
+    (n : OddNat) (q m d : ℕ) :
+    CanonicalSelectedDriftBucketCarrier n q m d ↪
+      CanonicalActiveSelectedPressureBucketCarrier n q m d :=
+  (Function.Embedding.refl _).sigmaMap fun _ =>
+    { toFun := fun x => x.val
+      inj' := Subtype.val_injective }
+
+/-- Unordered residual of actual positive-drift images after granting all
+same-depth exact-length tokens. -/
+noncomputable def canonicalUnorderedSelectedDriftResidualCount
+    (n : OddNat) (q m d : ℕ) : ℕ :=
+  Nat.card (CanonicalSelectedDriftBucketCarrier n q m d) -
+    (canonicalExactLengthBlockIndicesAtDepth n q m d).card
+
+/-- The actual drift residual is bounded by the cp-322 selected-carrier
+residual.  The difference is precisely unused selected-carrier slack. -/
+theorem unorderedSelectedDriftResidualCount_le_selectedCarrierResidualCount
+    (n : OddNat) (q m d : ℕ) :
+    canonicalUnorderedSelectedDriftResidualCount n q m d ≤
+      canonicalUnorderedSelectedCarrierResidualCount n q m d := by
+  classical
+  letI : Fintype
+      {k : ℕ // k ∈ canonicalActiveSelectedPressureBlocksAtDepth n q m d} :=
+    Fintype.ofFinset (canonicalActiveSelectedPressureBlocksAtDepth n q m d) (by simp)
+  letI (k : {k : ℕ // k ∈
+      canonicalActiveSelectedPressureBlocksAtDepth n q m d}) :
+      Fintype {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} :=
+    Fintype.ofFinset (canonicalSelectedPressureCarrier n k.val) (by simp)
+  letI (k : {k : ℕ // k ∈
+      canonicalActiveSelectedPressureBlocksAtDepth n q m d}) :
+      Fintype {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} //
+        i ∈ canonicalSelectedDriftImageCarrier n k.val} :=
+    Fintype.ofFinset (canonicalSelectedDriftImageCarrier n k.val) (by simp)
+  letI : Fintype (CanonicalSelectedDriftBucketCarrier n q m d) := by
+    unfold CanonicalSelectedDriftBucketCarrier
+    infer_instance
+  letI : Fintype (CanonicalActiveSelectedPressureBucketCarrier n q m d) := by
+    unfold CanonicalActiveSelectedPressureBucketCarrier
+    infer_instance
+  have hcard :
+      Nat.card (CanonicalSelectedDriftBucketCarrier n q m d) ≤
+        Nat.card (CanonicalActiveSelectedPressureBucketCarrier n q m d) :=
+    Nat.card_le_card_of_injective
+      (selectedDriftBucketActiveSelectedEmbedding n q m d)
+      (selectedDriftBucketActiveSelectedEmbedding n q m d).injective
+  unfold canonicalUnorderedSelectedDriftResidualCount
+  unfold canonicalUnorderedSelectedCarrierResidualCount
+  unfold canonicalSelectedResidualCount
+  omega

-`canonicalWindowPressureMarginAtDepth n q m d` is the block sum on `q..m`.
-The existing public pressure theorem identifies only the prefix sum `0..m`
-with `SourcePressureMarginInt n (paymentEndpointSeq n m + 1) d`.
+/-! ## Noncanonical actual residual incidence carrier -/

-The intended sliding identity therefore requires two explicit bridges that are
-not yet present as caller-facing theorems:
+/-- When enough actual drift-image incidences exist, choose an unordered
+injection of exact-length tokens into them.  This choice has no temporal
+meaning. -/
+noncomputable def canonicalExactLengthToDriftBucketEmbedding
+    {n : OddNat} {q m d : ℕ}
+    (hcard : (canonicalExactLengthBlockIndicesAtDepth n q m d).card ≤
+      Nat.card (CanonicalSelectedDriftBucketCarrier n q m d)) :
+    {k : ℕ // k ∈ canonicalExactLengthBlockIndicesAtDepth n q m d} ↪
+      CanonicalSelectedDriftBucketCarrier n q m d := by
+  classical
+  letI : Fintype
+      {k : ℕ // k ∈ canonicalActiveSelectedPressureBlocksAtDepth n q m d} :=
+    Fintype.ofFinset (canonicalActiveSelectedPressureBlocksAtDepth n q m d) (by simp)
+  letI (k : {k : ℕ // k ∈
+      canonicalActiveSelectedPressureBlocksAtDepth n q m d}) :
+      Fintype {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} :=
+    Fintype.ofFinset (canonicalSelectedPressureCarrier n k.val) (by simp)
+  letI (k : {k : ℕ // k ∈
+      canonicalActiveSelectedPressureBlocksAtDepth n q m d}) :
+      Fintype {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} //
+        i ∈ canonicalSelectedDriftImageCarrier n k.val} :=
+    Fintype.ofFinset (canonicalSelectedDriftImageCarrier n k.val) (by simp)
+  letI : Fintype (CanonicalSelectedDriftBucketCarrier n q m d) := by
+    unfold CanonicalSelectedDriftBucketCarrier
+    infer_instance
+  letI : Fintype
+      {k : ℕ // k ∈ canonicalExactLengthBlockIndicesAtDepth n q m d} :=
+    Fintype.ofFinset (canonicalExactLengthBlockIndicesAtDepth n q m d) (by simp)
+  apply Classical.choice
+  apply Function.Embedding.nonempty_iff_card_le.mpr
+  rw [Fintype.card_coe]
+  simpa only [Nat.card_eq_fintype_card] using hcard

-1. split the finite block sum `0..m` into `0..q-1` and `q..m`;
-2. identify pressure at `canonicalBlockStartTime n q` with the `0..q-1`
-   prefix (with the separate base case `q = 0`).
+/-- Actual unmatched drift-image incidences after a noncanonical unordered
+matching with exact-length tokens. -/
+noncomputable def canonicalActualSelectedDriftResidualFinset
+    (n : OddNat) (q m d : ℕ) :
+    Finset (CanonicalSelectedDriftBucketCarrier n q m d) := by
+  classical
+  letI : Fintype
+      {k : ℕ // k ∈ canonicalActiveSelectedPressureBlocksAtDepth n q m d} :=
+    Fintype.ofFinset (canonicalActiveSelectedPressureBlocksAtDepth n q m d) (by simp)
+  letI (k : {k : ℕ // k ∈
+      canonicalActiveSelectedPressureBlocksAtDepth n q m d}) :
+      Fintype {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} :=
+    Fintype.ofFinset (canonicalSelectedPressureCarrier n k.val) (by simp)
+  letI (k : {k : ℕ // k ∈
+      canonicalActiveSelectedPressureBlocksAtDepth n q m d}) :
+      Fintype {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} //
+        i ∈ canonicalSelectedDriftImageCarrier n k.val} :=
+    Fintype.ofFinset (canonicalSelectedDriftImageCarrier n k.val) (by simp)
+  letI : Fintype (CanonicalSelectedDriftBucketCarrier n q m d) := by
+    unfold CanonicalSelectedDriftBucketCarrier
+    infer_instance
+  by_cases hcard : (canonicalExactLengthBlockIndicesAtDepth n q m d).card ≤
+      Nat.card (CanonicalSelectedDriftBucketCarrier n q m d)
+  · exact Finset.univ \ Finset.univ.map
+      (canonicalExactLengthToDriftBucketEmbedding hcard)
+  · exact ∅
+
+/-- Source-bearing subtype of the chosen unmatched drift incidences. -/
+def CanonicalActualSelectedDriftResidualCarrier
+    (n : OddNat) (q m d : ℕ) :=
+  {x : CanonicalSelectedDriftBucketCarrier n q m d //
+    x ∈ canonicalActualSelectedDriftResidualFinset n q m d}
+
+/-- The actual residual carrier is a subtype of the drift-image bucket. -/
+def actualSelectedDriftResidualCarrierEmbedding
+    (n : OddNat) (q m d : ℕ) :
+    CanonicalActualSelectedDriftResidualCarrier n q m d ↪
+      CanonicalSelectedDriftBucketCarrier n q m d :=
+  Function.Embedding.subtype _
+
+/-- The chosen actual residual has exactly the unordered drift-residual
+cardinality. -/
+theorem natCard_actualSelectedDriftResidualCarrier
+    (n : OddNat) (q m d : ℕ) :
+    Nat.card (CanonicalActualSelectedDriftResidualCarrier n q m d) =
+      canonicalUnorderedSelectedDriftResidualCount n q m d := by
+  classical
+  letI : Fintype
+      {k : ℕ // k ∈ canonicalActiveSelectedPressureBlocksAtDepth n q m d} :=
+    Fintype.ofFinset (canonicalActiveSelectedPressureBlocksAtDepth n q m d) (by simp)
+  letI (k : {k : ℕ // k ∈
+      canonicalActiveSelectedPressureBlocksAtDepth n q m d}) :
+      Fintype {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} :=
+    Fintype.ofFinset (canonicalSelectedPressureCarrier n k.val) (by simp)
+  letI (k : {k : ℕ // k ∈
+      canonicalActiveSelectedPressureBlocksAtDepth n q m d}) :
+      Fintype {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} //
+        i ∈ canonicalSelectedDriftImageCarrier n k.val} :=
+    Fintype.ofFinset (canonicalSelectedDriftImageCarrier n k.val) (by simp)
+  letI : Fintype (CanonicalSelectedDriftBucketCarrier n q m d) := by
+    unfold CanonicalSelectedDriftBucketCarrier
+    infer_instance
+  letI : Fintype
+      {k : ℕ // k ∈ canonicalExactLengthBlockIndicesAtDepth n q m d} :=
+    Fintype.ofFinset (canonicalExactLengthBlockIndicesAtDepth n q m d) (by simp)
+  letI : Fintype (CanonicalActualSelectedDriftResidualCarrier n q m d) :=
+    Fintype.ofFinset (canonicalActualSelectedDriftResidualFinset n q m d) (by simp)
+  rw [Nat.card_eq_fintype_card]
+  unfold CanonicalActualSelectedDriftResidualCarrier
+  rw [Fintype.card_coe]
+  unfold canonicalActualSelectedDriftResidualFinset
+  split_ifs with hcard
+  · rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
+      Finset.card_map, Finset.card_univ]
+    simp only [canonicalUnorderedSelectedDriftResidualCount,
+      Nat.card_eq_fintype_card, Fintype.card_coe]
+  · simp only [Finset.card_empty, canonicalUnorderedSelectedDriftResidualCount]
+    omega

-Until those bridges are proved, relative window pressure must not be treated as
-absolute `IsSourcePressureDepth`, and no level-zero pulse/packing theorem may be
-applied to its positive part.  This is the first genuine API obstruction after
-the completed finite residual reduction; it is a missing prefix-difference
-bridge, not evidence that the proposed identity is false.
+/-!
+## Next boundary: causal depth queue
+
+The unordered layer now ends with an actual source-bearing residual subtype.
+The next theorem cannot be obtained by reinterpreting this complement: the
+chosen injection deliberately ignores block order.
+
+Stage H must instead introduce per-block arrivals from
+`canonicalSelectedDriftImageCarrier`, per-block exact-length service, and a
+fresh reflected queue initialized immediately before block `q`.  The existing
+`canonicalOutstandingClaimQueue` proves the required Lindley pattern only for
+the scalar claim/capacity process fixed in `UniversalPaymentScalarQueue`; it is
+not polymorphic in arrivals and service.  The safe next implementation is
+therefore to extract a generic finite Nat-valued Lindley queue API (or prove a
+parallel fixed-depth specialization) in a lower module, then instantiate it
+here.  Until that exists, neither this unordered residual nor its chosen
+matching may be called causal repayment.
 -/

 /-- Endpoint-prefix pressure is continuation mass one level deeper minus the
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-323.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-323.md
new file mode 100644
index 00000000..e860168e
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-323.md
@@ -0,0 +1,112 @@
+# Petal / FloatWindow implementation report - checkpoint 323
+
+## Result
+
+Stages A-G of the revised residual program are implemented in
+`UniversalPaymentAmplitude.lean`.  The branch now reaches an actual
+source-bearing residual incidence carrier.  All additions are no-sorry.
+
+## Sliding pressure bridge
+
+The previously missing prefix-difference API is closed:
+
+```text
+pressure at block start q
+  = sum of block contributions on range q
+
+window pressure q..m
+  = pressure after endpoint m - pressure at block start q.
+```
+
+The zero source window has pressure zero, and the `q = 0` specialization
+recovers endpoint-prefix pressure exactly.  Relative window pressure is still
+kept distinct from an absolute `IsSourcePressureDepth` hypothesis.
+
+## Actual block window
+
+`canonicalPaymentBlockWindow n q m` is the union of canonical blocks indexed
+by `Icc q m`.  For `q <= m`, Lean proves both normal forms:
+
+```text
+Icc (canonicalBlockStartTime n q) (paymentEndpointSeq n m)
+
+range (paymentEndpointSeq n m + 1)
+  \ range (canonicalBlockStartTime n q).
+```
+
+Generic filtered cardinality decomposes over the disjoint blocks.  Actual
+continuation and exact-recovery source finsets are defined from this window,
+and their signed cardinal difference equals the sliding pressure sum.
+
+## Structural separation fact
+
+For an active selected block at selected depth `d`, Lean proves
+
+```text
+d + 2 <= canonicalPaymentBlockLength n k.
+```
+
+Therefore active selected blocks at depth `d` are disjoint from blocks whose
+length is exactly `d`.  Exact-length service at a selected depth necessarily
+comes from a different block; it is not a token emitted by the selected block
+itself.
+
+## Residual terminology
+
+`canonicalSelectedResidualCount` remains for compatibility.  The explicit
+alias `canonicalUnorderedSelectedCarrierResidualCount` records its real
+meaning: natural cardinal subtraction after granting unrestricted same-depth
+tokens.  Its `Fin` carrier has no source-time or block coordinate and no causal
+interpretation.
+
+## Actual drift image
+
+For every positive nonsaturated block, positive drift units now embed directly
+into selected source incidences of that same block.  The finite image:
+
+- has cardinality exactly `Int.toNat endpointAccountingTerm`;
+- is contained in the selected source carrier by construction;
+- is empty outside the positive nonsaturated branch.
+
+`CanonicalSelectedDriftBucketCarrier` retains selected depth, block index, and
+source time.  Its unordered residual is bounded by the older selected-carrier
+residual, proving that the latter is a safe but potentially coarse bound caused
+by unused selected-carrier slack.
+
+## Actual residual incidence carrier
+
+When exact-length token count does not exceed drift-image count, a
+noncanonical unordered injection is chosen and its image is removed.  In the
+opposite cardinal branch the residual is empty.  The resulting
+`CanonicalActualSelectedDriftResidualCarrier`:
+
+- embeds into the actual drift-image bucket;
+- retains depth, block, and source coordinates;
+- has cardinality exactly the unordered drift residual.
+
+This is an actual incidence subset, but the matching remains unordered and is
+not future-payment allocation.
+
+## Safe stopping boundary
+
+Stage H requires a fixed-depth causal queue.  The existing scalar Lindley
+theorems are specialized to `canonicalBlockClaimCount` and
+`canonicalBlockCapacityCount`; they cannot be instantiated with the new
+depthwise arrivals and exact-length service.
+
+The next safe implementation is a generic finite Nat-valued reflected queue
+API, or a parallel fixed-depth specialization, proving the suffix-maximum
+Lindley identity.  Only after that should unordered drift residual be compared
+with causal queue residual.  No causal repayment or temporal Hall conclusion
+is claimed at checkpoint 323.
+
+## Next implementation
+
+1. Extract a generic local reflected queue parameterized by arrivals and
+   service.
+2. Prove its terminal value equals the maximum positive suffix imbalance.
+3. Instantiate arrivals with per-block selected drift-image cardinality at
+   depth `d` and service with the exact-length indicator.
+4. Prove unordered residual is bounded by the causal queue.
+5. Add the temporal interval-order Hall theorem only after the queue surface is
+   stable.
````
`````
