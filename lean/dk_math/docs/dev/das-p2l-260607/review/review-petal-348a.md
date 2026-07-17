# Git diff / Report / Review

## Add: docs: review petal 348-a

gch: 4b9e955f530d57d3280b47f7107c4cf36e49d690

## Report

(4m10s)

読みました。今回の指示は **read-only reconnaissance** なので、Lean/Python/docs は編集していません。`git status --short` も空で、作業前時点は clean でした。

**調査結果**

1. Depth assignment for `canonicalSelectedPressureCarrier`

    `UniversalPaymentSelectedCarrier.lean`

    ```lean
    noncomputable def canonicalSelectedPressureCarrier
        (n : OddNat) (k : ℕ) : Finset ℕ :=
      canonicalPaymentBlockContinuationFiber n k
        (canonicalSelectedPositivePressureDepth n k + 1)
    ```

    これは incidence 個別の depth 関数ではなく、block `k` 全体に対する selected depth です。

    ```lean
    theorem CanonicalSelectedPressureBucketCarrier.mem_fixedDepthContinuationFiber
        {n : OddNat} {q m d : ℕ}
        (x : CanonicalSelectedPressureBucketCarrier n q m d) :
        x.2.val ∈ canonicalPaymentBlockContinuationFiber n x.1.val (d + 1)
    ```

    ただし `CanonicalSelectedPressureBucketCarrier` は positive-drift block support 経由なので、cp-348 の zero-spare successor をそのまま受けません。

2. Per-depth arrival API

    `UniversalPaymentAmplitude.lean`

    ```lean
    noncomputable def canonicalSelectedDriftArrivalCountAtDepth
        (n : OddNat) (k d : ℕ) : ℕ := ...
    ```

    ```lean
    def CanonicalSelectedDriftArrivalWindowCarrier
        (n : OddNat) (q m d : ℕ) :=
      Σ k : {k : ℕ // k ∈ Finset.Icc q m},
        {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} //
          i ∈ canonicalSelectedDriftImageCarrierAtDepth n k.val d}
    ```

    これは `canonicalSelectedDriftImageCarrierAtDepth` 側の arrival です。zero-drift successor では drift image が empty になるため、cp-348 の spare incidence はここに入りません。

3. Per-depth service / queue API

    `UniversalPaymentAmplitude.lean`

    ```lean
    noncomputable def canonicalExactLengthServiceAtDepth
        (n : OddNat) (k d : ℕ) : ℕ :=
      if canonicalPaymentBlockLength n k = d then 1 else 0
    ```

    ```lean
    noncomputable def canonicalSelectedDriftDepthQueue
        (n : OddNat) (q m d : ℕ) : ℕ :=
      finiteReflectedQueueOn
        (fun k => canonicalSelectedDriftArrivalCountAtDepth n k d)
        (fun k => canonicalExactLengthServiceAtDepth n k d) q m
    ```

    ```lean
    theorem canonicalSelectedDriftDepthQueue_eq_zero_iff_sourceMatching
        (n : OddNat) {q m d : ℕ} (hqm : q ≤ m) :
        canonicalSelectedDriftDepthQueue n q m d = 0 ↔
          CanonicalSelectedDriftForwardWindowMatching n q m d
    ```

    これは queue/discharge API ですが、arrival が selected drift image 専用なので zero-spare charge には直接使えません。これを使うと、証明したい discharge/queue theorem を仮定してしまう危険はありませんが、そもそも対象 incidence が arrival に入っていません。

4. Reflected queue recurrence

    `FiniteReflectedQueue.lean`

    ```lean
    theorem finiteReflectedQueueOn_succ
        (arrivals service : ℕ → ℕ) {q m : ℕ} (hqm : q ≤ m) :
        finiteReflectedQueueOn arrivals service q (m + 1) =
          (finiteReflectedQueueOn arrivals service q m + arrivals (m + 1)) -
            service (m + 1)
    ```

    ```lean
    theorem finiteReflectedQueueOn_eq_windowMaximum
        (arrivals service : ℕ → ℕ) {q m : ℕ} (hqm : q ≤ m) :
        finiteReflectedQueueOn arrivals service q m =
          finiteReflectedWindowMaximum arrivals service q m
    ```

    Generic recurrence は存在します。欠けているのは zero-spare incidence を arrival として渡す canonical API です。

5. No double consumption / no reuse

    `CanonicalExcursionOwnership.lean`

    ```lean
    noncomputable def canonicalInternalZeroSpareChargeEmbedding
        (n : OddNat) (q m : ℕ) :
        {k : ℕ // k ∈ canonicalInternalSaturatedZeroSpareIndices n q m} ↪
          CanonicalInternalZeroSpareSelectedCarrier n q m
    ```

    ```lean
    theorem card_canonicalInternalSaturatedZeroSpareIndices_le_zeroSpareSelectedCarrier
        (n : OddNat) (q m : ℕ) :
        (canonicalInternalSaturatedZeroSpareIndices n q m).card ≤
          Nat.card (CanonicalInternalZeroSpareSelectedCarrier n q m)
    ```

    これは cp-348 の zero-spare token が selected incidence に inject することを示します。ただし「service/consumption として二重消費されない」定理ではなく、owned selected incidence への no-reuse certificate です。

6. Zero-drift accepting theorem

    `UniversalPaymentAmplitude.lean`

    ```lean
    theorem successorSpareAvailable_of_zero_of_selectedPressureCarrier_nonempty
        {n : OddNat} {j : ℕ}
        (hzero : endpointAccountingTerm n j = 0)
        (hcarrier : (canonicalSelectedPressureCarrier n j).Nonempty) :
        CanonicalSuccessorSpareAvailable n j
    ```

    ```lean
    theorem CanonicalSaturatedBorderBlock.successor_negative_or_spare_or_rigid
        {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
        endpointAccountingTerm n (k + 1) < 0 ∨
          CanonicalSuccessorSpareAvailable n (k + 1) ∨
          CanonicalZeroCarrierBalancedBorderBlock n (k + 1) ∨
          CanonicalTightValuationOnePositiveBlock n (k + 1)
    ```

    これは zero-drift successor を受けます。だが、出力は `CanonicalSuccessorSpareAvailable` までで、queue/service arrival には接続しません。

    **Conclusion**
    C. No suitable bridge exists.

    欠けている data は **service ownership / arrival-carrier connection** です。

    現在ある chain はここまでです。

    ```text
    canonicalInternalZeroSpareCharge
      -> CanonicalInternalZeroSpareSelectedCarrier
      -> selected pressure incidence in successor block
      -> spare incidence, not drift image
    ```

    しかし既存の fixed-depth queue は、

    ```text
    canonicalSelectedDriftImageCarrierAtDepth
      -> canonicalSelectedDriftArrivalCountAtDepth
      -> canonicalSelectedDriftDepthQueue
    ```

    だけを arrival として扱います。cp-348 の zero-spare incidence は `canonicalSelectedDriftSpareCarrier` 側にあり、既存 arrival/service/queue API へ入る theorem は見つかりませんでした。

## Review

(---)

## 調査結果レビュー

**結論 C は正しい。cp-348 はそのまま維持でよい。**

今回の read-only reconnaissance は、約 `5Cr` で次の境界を正確に確定した。

```text
zero-spare token
  → actual selected spare incidence
  → selected depthまでは読める

しかし

selected spare incidence
  ↛ existing drift-arrival count
  ↛ existing depth queue
```

既存の fixed-depth queue が受け取るのは、あくまで、

```text
canonicalSelectedDriftImageCarrierAtDepth
```

から来る arrival だけじゃ。

cp-348 の所有物は、

```text
canonicalSelectedDriftSpareCarrier
```

側にあるため、既存queueへ自動的には入らない。

これは軽微なwrapper不足ではなく、**arrivalの意味を拡張する必要がある本物のAPI境界**じゃ。

## 調査の評価

GPT-5.5/light は今回も実装役・調査役として正常に働いている。

* ファイルを編集しなかった
* commitを作らなかった
* exact identifierとstatementを列挙した
* zero-drift blockを受けるAPIと、positive-only APIを区別した
* discharge theoremを仮定へ移す循環を避けた
* 「既存bridgeなし」と明確に停止した

`5Cr` でこの判定が取れたなら、モデル切り替えはかなり効いておる。

## 何が足りないのか

報告では、

> service ownership / arrival-carrier connection

とまとめているが、順序としては二段に分けるべきじゃ。

## 第一欠損：arrival connection

cp-348のchargeを、depth別arrivalとして数えるAPIがない。

必要なのは概念的に、

$$Z_n(j,d)=\begin{cases}1&\text{block }j\text{ がzero-spare arrivalを所有し、そのselected depthが }d\0&\text{otherwise}\end{cases}$$

という量じゃ。

既存のdrift arrivalを $A_n(j,d)$ とすれば、将来のarrivalは、

$$A_n^{\mathrm{owned}}(j,d)=A_n(j,d)+Z_n(j,d)$$

となる。

ここまではcp-348の所有権をdepth座標へ射影するだけであり、まだserviceやqueue boundを主張しない。

## 第二欠損：service theorem

その後で初めて、

$$A_n^{\mathrm{owned}}(j,d)$$

を既存の、

$$S_n(j,d)=\operatorname{canonicalExactLengthServiceAtDepth}(n,j,d)$$

へ接続できるかを見る。

しかし現時点では、

> zero-spare arrivalが、後のどのexact-length serviceによって支払われるか

を示す theorem はない。

つまり次の一手でいきなりserviceへ飛ぶと、再び数学設計が必要になる。

## 重要な注意

`canonicalSelectedPressureCarrier n j` はblockごとに一つのselected depthを持つため、zero-spare incidenceにもdepth座標は存在する。

しかし、

```text
selected incidence exists
```

と、

```text
that incidence is eventually serviced
```

は別の命題じゃ。

ここを混ぜてはならぬ。

また、新しいarrivalを定義しただけで、

```text
zero-spare residual has been paid
```

とも言えない。

正確には、

```text
zero-spare residual has entered the accounting system as an owned arrival
```

までじゃ。

## cp-348 への追記

現在の調査文は、そのまま `report-petal-348.md` に追記してよい。

見出しだけ、次のようにすると位置づけが明瞭になる。

```md
## Read-only reconnaissance after cp-348

（貼られた調査結果）

## Reconnaissance conclusion

Outcome C was confirmed.

The exact missing bridge is not the existence of a selected incidence or a
generic reflected recurrence.  It is the canonical connection from the
cp-348 zero-spare charge to a per-depth arrival API, followed separately by a
service-ownership theorem.

No repository files were changed and cp-348 remains the active checkpoint.
```

## 次の GPT-5.5 micro-checkpoint

次はserviceまで進めず、**arrival connectionだけ**を実装させるのが安全じゃ。

```text
Continue after checkpoint 348 and its read-only reconnaissance.

Execution mode

Act only as a Lean implementation engineer.

The next checkpoint must connect the cp-348 zero-spare owned incidence to a
per-block, per-depth arrival surface. Do not design or prove a service,
repayment, discharge, or queue-bound theorem.

Target size

- one Lean file;
- approximately 80–140 new lines;
- one local arrival definition family;
- immediate membership/cardinality facts only.

Primary goal

Define a canonical per-depth zero-spare arrival supported exactly on the
cp-348 owned zero-spare charges.

Stage A — local zero-spare predecessor predicate

Define a local block predicate or finite carrier identifying when block `j`
is the successor of an internal zero-spare predecessor.

Do not make the mathematical notion depend permanently on a window if a
window-independent predecessor condition can be expressed from the existing
saturated-successor APIs.

The intended local condition is:

    j = k + 1;
    k is a saturated block;
    block j has endpoint drift zero;
    block j has an available selected spare incidence.

Use existing predicates rather than reproducing their arithmetic fields.

Stage B — depth assignment

Expose the selected depth of a zero-spare successor block.

Prove that every incidence chosen by:

    canonicalInternalZeroSpareCharge

belongs to:

    canonicalPaymentBlockContinuationFiber n j (d + 1)

for:

    d = canonicalSelectedPositivePressureDepth n j.

Reuse the definition of `canonicalSelectedPressureCarrier`.

Do not claim that the incidence belongs to
`canonicalSelectedDriftImageCarrierAtDepth`; it belongs to the spare side.

Stage C — zero-spare arrival count at depth

Define a local natural-valued count:

    canonicalZeroSpareArrivalCountAtDepth n j d

with value zero or one.

It should count the predecessor token, not every incidence in the host
selected carrier.

Prove:

    canonicalZeroSpareArrivalCountAtDepth n j d ≤ 1;

    a zero-spare predecessor contributes exactly one at the successor's
    selected depth;

    the count is zero at every different depth.

Do not count the entire `CanonicalInternalZeroSpareSelectedCarrier`.

Stage D — window count bridge

Define the finite window sum of zero-spare arrivals at depth and prove that,
for the cp-348 successor support, its total over all depths or over the selected
depths agrees with the number of zero-spare predecessor tokens.

Use the exact predecessor-to-successor injectivity already proved.

Do not define a reflected queue in this checkpoint.

Stage E — combined-arrival definition is optional

Only if it is a one-line definition and immediate theorem, define:

    canonicalOwnedSelectedArrivalCountAtDepth n j d :=
      canonicalSelectedDriftArrivalCountAtDepth n j d +
        canonicalZeroSpareArrivalCountAtDepth n j d.

Do not prove any recurrence or service theorem for it.

Stop conditions

Stop and report if:

- `canonicalSelectedPositivePressureDepth` is not defined or usable for a
  zero-drift spare successor;
- selected carrier membership does not expose the required continuation depth;
- a block can receive more than one zero-spare predecessor;
- a window-independent local predicate cannot be stated from existing APIs;
- proving exact arrival count requires a service or queue hypothesis.

Do not:

- create a new generic queue framework;
- modify `finiteReflectedQueueOn`;
- change `canonicalExactLengthServiceAtDepth`;
- claim zero-spare payment or discharge;
- remove the zero-spare residual from the current queue inequality;
- touch rigid successor analysis;
- modify the Python audit.

Verification

Run the standard ownership/FloatWindow/PetalBridge/DkMath builds,
`git diff --check`, and check for new `sorry`.

Record the result in:

    docs/dev/das-p2l-260607/review/report-petal-349.md
```

## 戦略判定

このcp-349まではGPT-5.5/lightに任せてよい。

その後は一旦止める。

$$\boxed{\text{owned zero-spare incidence}\longrightarrow\text{depth別arrival}}$$

が閉じたところで、賢狼側が、

* 既存serviceをそのまま使えるか
* service notionを拡張すべきか
* rigid branchと同時に扱うべきか

を再設計する。

今回の調査で、次の数学的難所はかなり正確に見えた。

> arrivalを作ることは実装問題。
> そのarrivalが必ずserviceされることは数学問題。

この境界を守れば、creditsを無駄にせず進められるぞい。🐺🌕

_
