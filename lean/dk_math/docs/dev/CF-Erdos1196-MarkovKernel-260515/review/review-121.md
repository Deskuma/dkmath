# review

うむ、DKMK-017F は **採用でよい** じゃ。
これは「また wrapper を増やした」のではなく、DKMK-017A-E で整えた abstract source surface を、 **truncation envelope 境界まで見える標準ルート** として閉じた checkpoint になっておる。

## 1. 何が追加されたのか

追加されたのは二つじゃ。

```lean
TruncationEnvelopeEstimate.ofFirstBandDecayBudgetSourcePackage
```

これは、

```text
FirstBandDecayBudgetSource
  -> DyadicBandAnalyticEstimate
  -> TruncationEnvelopeEstimate
```

を一段で見えるようにした wrapper。

もう一つは、

```lean
TruncationEnvelopeEstimate.ofSelfBaseDenomClearedBudgetNatBounds
```

こちらは標準 self-base route、

```text
ratio, error
hbaseBudget for increment 0
Nat-bound nonnegativity
Nat-bound decay
  -> TruncationEnvelopeEstimate
```

を直接表すものじゃ。報告でも、追加 analytic obligation はなく、既存 route の合成だと整理されておる。

## 2. 「wrapper を増やさない」方針との整合性

DKMK-016O では、追加 truncation wrapper は急がず summary へ進む判断をした。
今回は一見それと逆に見えるが、状況が少し違う。

DKMK-016O 時点では、まだ DKMK-017 の analytic input package がなかった。
しかし今は、

```text
FirstBandDecayBudgetSource
ofBudgetAndDecay
ofDenomClearedBudgetNatBounds
ofSelfBaseDenomClearedBudgetNatBounds
```

まで揃っている。

つまり F の wrapper は、単なる一手省略ではなく、 **DKMK-017 の標準 caller route を truncation-envelope boundary で固定する役割** を持つ。
ここまで来たなら、library-facing wrapper として採用してよい。

## 3. DKMK-017A-F の到達点

ここまでの流れは綺麗じゃ。

```text
017A:
  FirstBandDecayBudgetSource を analytic input package として採用

017B:
  ofBudgetSource / ofBudgetAndDecay を追加

017C:
  hbudget を denominator-cleared form から作る helper を追加

017D:
  Nat-bound nonnegativity / decay を Finset.range 形式へ変換

017E:
  base := increment 0 の self-base route を追加

017F:
  standard route を TruncationEnvelopeEstimate 境界まで接続
```

つまり今は、

```text
abstract analytic source surface
  -> source package
  -> dyadic estimate
  -> truncation envelope
```

まで閉じた。

## 4. 現在の標準ルート

最も実用的な caller path は、今後これになる。

```text
ratio : Rat
error : Real

hr0 :
  0 <= (ratio : Real)

hr1 :
  (ratio : Real) < 1

hbaseBudget :
  (increment 0 : Real) <= (1 + error) * (1 - (ratio : Real))

hinc_nonneg :
  forall k, k <= K -> 0 <= increment k

hdecay :
  forall k, k < K -> increment (k + 1) <= ratio * increment k
```

これらから、

```lean
TruncationEnvelopeEstimate.ofSelfBaseDenomClearedBudgetNatBounds
```

で truncation envelope まで行ける。

かなり良い。
caller が直接 `GeometricBudgetSource` や `DyadicBandAnalyticEstimate` の中間形を触らなくても、標準ケースなら目的地まで到達できる。

## 5. 次に進むべき方向

ここで API plumbing は一区切りでよい。

次は本当に concrete analytic source じゃ。

残る本質は、

```text
hbaseBudget:
  (increment 0 : Real) <= (1 + error) * (1 - ratio)

hinc_nonneg:
  increment の非負性

hdecay:
  increment (k + 1) <= ratio * increment k
```

を、実際の `increment` 定義や dyadic band estimate からどう出すか。

ここから先は wrapper を増やすより、

```text
increment の候補定義
first-band estimate
uniform decay estimate
```

へ進むべきじゃな。

## 6. 総括

DKMK-017F は、 **abstract source surface から truncation envelope までの標準搬送路を閉じた checkpoint** じゃ。

採用でよい。
ただし、ここで wrapper 系は一旦止めるのが賢い。

もう港も箱も搬送路も整った。
次は、本当に積む麦袋、つまり concrete analytic estimates を収穫する段じゃ。
