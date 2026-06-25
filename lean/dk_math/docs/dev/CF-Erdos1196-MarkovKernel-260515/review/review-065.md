# review

## 1. 状況総括

うむ、これは **DKMK-012C 完了** と見てよい。

今回の差分で、`SourceMassTruncation.lean` に

```lean
TruncationEnvelopeEstimate.dyadicRange
```

が追加された。DKMK-012B で docs 上に固定した形そのままに、

```text
steps     = Finset.range (K + 1)
threshold = fun k : ℕ => x * 2^k
```

を持つ dyadic range provider が Lean 上に立ったわけじゃ。

しかも中身は、予定どおり **packaging theorem** に留まっておる。

```lean
increment_nonneg := hinc
analytic_bound := by
  constructor
  exact hbound
```

この薄さがよい。新しい route 証明を増やさず、`TruncationEnvelopeEstimate` を構成する producer だけを足している。

## 2. 何が閉じたのか

DKMK-012A/B では、dyadic provider の設計を docs で固めた。

DKMK-012C では、その設計が Lean に入った。

閉じた route はこれじゃ。

```text
dyadic range data
  -> TruncationEnvelopeEstimate.dyadicRange
  -> TruncationEnvelopeEstimate
  -> existing DKMK-011 route theorem
  -> weightedHitMass <= 1 + error
```

ここで `dyadicRange` が受け取る外部入力は、

```lean
x : ℕ
K : ℕ
increment : ℕ → ℚ
hinc : ∀ k ∈ Finset.range (K + 1), 0 ≤ increment k
hbound :
  ((Finset.sum (Finset.range (K + 1)) increment : ℚ) : ℝ) ≤
    1 + error
```

じゃな。

`hinc` が finite-step source envelope の非負性を担い、`hbound` が analytic total estimate を担う。つまり DKMK-011 の `TruncationEnvelopeEstimate` contract に、dyadic range という最初のまともな finite band provider が接続された。

## 3. 実装評価

かなり良い実装じゃ。

第一に、 `threshold = fun k => x * 2^k` を固定しただけで、これに関する余計な補題を増やしていない。
今の段階では threshold は activation data であり、`FiniteStepTailAnalyticBound` の証明には登場しない。だからここで `2^k` の単調性や範囲評価へ踏み込まなかったのは正しい。

第二に、`increment` を computed formula にしていない。
これは大事じゃ。`increment` は将来の解析評価が供給する band estimate であり、ここで log や Mertens 型の式を混ぜると層分離が崩れる。

第三に、route theorem を増やしていない。
既存の

```lean
TruncationEnvelopeEstimate.finiteStepTail_weightedHitMass_le_one_add_error
```

へ渡すだけで十分じゃ。`dyadicRange` 専用の hitting theorem は便利そうに見えるが、今は API を太らせる段階ではない。

## 4. 数学的な意味

今回で、single-window toy provider から一歩進み、 **有限 dyadic band envelope** の入口ができた。

single-window は、

```text
steps = Finset.univ : Finset Unit
```

という最小検査用だった。

今回の dyadicRange は、

```text
k = 0, 1, ..., K
threshold k = x * 2^k
```

という、解析的分割にかなり近い形じゃ。まだ `increment k` の中身は外部供給だが、band の骨格は立った。

これは、後続で

```text
各 dyadic band に対応する increment k を解析的に評価する
```

という作業へ進むための足場じゃな。

## 5. 検証状況

報告では次が通っている。

```text
lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
lake build DkMath.NumberTheory.PrimitiveSet
```

失敗事例なし。
よって DKMK-012C は **no-sorry 実装完了** と判定してよい。

## 6. まだ閉じていないもの

今回も、あえて次は入っていない。

```text
route theorem の変更
logarithmic provider
Mertens / big-O statement
computed increment formula
```

これは正しい。
DKMK-012C は dyadic provider の **型と接続** を作る段階であり、解析評価そのものはまだ先じゃ。

つまり、まだ残っている山は、

```text
increment k を何で与えるか
sum increment <= 1 + error をどう証明するか
dyadic から logarithmic へ進むか
```

このあたりじゃな。

## 7. 次の一手

次は History にある通り、 **DKMK-012D usage summary** がよい。

書くべき内容は明確じゃ。

```text
dyadic data:
  x, K, increment, error

proof input:
  hinc
  hbound

provider:
  TruncationEnvelopeEstimate.dyadicRange

route:
  TruncationEnvelopeEstimate.finiteStepTail_weightedHitMass_le_one_add_error

result:
  weightedHitMass <= 1 + error
```

ここを docs で一度まとめておくと、次に dyadic-specific example や logarithmic provider へ進むときに迷わぬ。

Lean theorem を追加するなら、`dyadicRange` から route theorem まで直通する wrapper も考えられるが、わっちは今はまだ推さぬ。今は usage summary で十分じゃ。

## 8. 登頂判定

現在地はこう。

```text
DKMK-012A:
  provider design roadmap 完了

DKMK-012B:
  dyadic provider shape docs 完了

DKMK-012C:
  TruncationEnvelopeEstimate.dyadicRange 完了

DKMK-012D:
  次、usage summary
```

DKMK-012 の core はかなり見えてきた。
`TruncationEnvelopeEstimate` に対して、toy provider と dyadic provider の両方が揃ったのは大きい。

## 9. 賢狼の判定

よいぞ、ぬしよ。

DKMK-012C は小さい実装だが、研究路線としてはかなり意味がある。
これで、

```text
dyadic band family
  -> finite-step truncation estimate
  -> DKMK route
```

という線が Lean 上で開いた。

わっちの判定はこうじゃ。

```text
DKMK-012C: 完了
次: DKMK-012D usage summary
方針: route theorem は触らず、dyadicRange の使い方を固定
```

ここまで慎重に層を分けられておるのは良い。次に霧が濃くなるのは `increment` の中身をどう設計するかじゃが、今はまだ、その器を美しく作れておる。
