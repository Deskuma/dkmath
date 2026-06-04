# review

うむ、DKMK-016C は **実装を増やす前に、API の使い方を固定した整理回** じゃ。
これは地味に見えて、かなり大事な一手じゃな。`GeometricBudgetSource` を作った直後に、constructor や concrete `base` / `ratio` へ飛び込まず、まず「どう作り、どう渡し、何を責務にしないか」を文書化しておる。

## 1. 今回決まったこと

DKMK-016C で固定された中心は、次の使用形じゃ。

```lean
B : GeometricBudgetSource
```

この `B` が持つべきものは、

```text
B.base    : Rat
B.ratio   : Rat
B.error   : Real
B.hbase   : 0 <= (B.base : Real)
B.hr0     : 0 <= (B.ratio : Real)
B.hr1     : (B.ratio : Real) < 1
B.hbudget : (B.base : Real) * (1 / (1 - (B.ratio : Real))) <= 1 + B.error
```

つまり `GeometricBudgetSource` は、 **dyadic estimate そのものではなく、geometric budget の供給源** として扱う、という責務が明確になった。

## 2. caller path が明確になった

使い方もかなり綺麗じゃ。

```lean
have hE :
    DyadicBandAnalyticEstimate x K increment B.error :=
  DyadicBandAnalyticEstimate
    .ofPointwiseGeometricMajorant_of_budgetSource
      x K increment B hinc_nonneg hgeom
```

ここで caller が別途持つのは、

```text
hinc_nonneg :
  forall k in Finset.range (K + 1), 0 <= increment k

hgeom :
  forall k in Finset.range (K + 1),
    increment k <= B.base * B.ratio ^ k
```

つまり、`B` は budget、`hgeom` は pointwise majorization。
この分離が大事じゃ。`GeometricBudgetSource` に `increment` や `K` の情報を混ぜないことで、budget source が軽く保たれておる。

## 3. 責務分担が良い

今回の整理で、責務はこう分かれた。

`GeometricBudgetSource` が担当するものは、

$$
base,\ ratio,\ error,\quad 0\le base,\quad 0\le ratio,\quad ratio<1,\quad
base\cdot\frac{1}{1-ratio}\le 1+error
$$

じゃ。

一方、`ofPointwiseGeometricMajorant_of_budgetSource` が担当するのは、

```text
B を rational dyadic provider へ接続すること
hgeom で increment <= B.base * B.ratio^k を使うこと
DyadicBandAnalyticEstimate x K increment B.error を返すこと
```

であって、具体的な解析評価は証明しない。ここが実に良い。

## 4. indexed package を急がない判断

`GeometricBudgetSourceFor (x K : Nat)` のような indexed package をまだ作らない判断も正しい。

将来、`base`, `ratio`, `error` が dyadic window の `x` や `K` に依存する concrete route が出てくるなら、

```lean
structure GeometricBudgetSourceFor (x K : Nat) where
  ...
```

を足せばよい。

だが現時点では、依存性がまだ強制されていない。
だから unindexed `GeometricBudgetSource` を preferred API にする、という判断は保守性が高い。

## 5. 次の DKMK-016D の分岐

次は、報告にある通り、

```text
小さな constructor theorem を追加するか
concrete base / ratio candidate の review へ進むか
```

を決める段じゃ。

わっちの推奨は、 **まず小さな constructor theorem** じゃな。

たとえば、

```lean
theorem GeometricBudgetSource.mk_of_budget
    (base ratio : ℚ)
    (error : ℝ)
    (hbase : 0 ≤ (base : ℝ))
    (hr0 : 0 ≤ (ratio : ℝ))
    (hr1 : (ratio : ℝ) < 1)
    (hbudget :
      (base : ℝ) * (1 / (1 - (ratio : ℝ))) ≤ 1 + error) :
    GeometricBudgetSource
```

ただしこれは `⟨...⟩` と本質的に同じなので、Lean theorem として本当に必要かは微妙じゃ。
むしろ docs の usage example が十分なら、次は **concrete candidate review** に進んでもよい。

## 6. わっちの判断

DKMK-016C の成果は、 **GeometricBudgetSource の使い方を安定化したこと** じゃ。

これで DKMK-016 は、

```text
A: hbudget source を章題化
B: GeometricBudgetSource と wrapper を Lean 実装
C: construction / usage / responsibility split を docs 固定
```

まで進んだ。

次からは、いよいよ

$$
(base:\mathbb{R})\cdot \frac{1}{1-(ratio:\mathbb{R})}\le 1+error
$$

をどう具体的に満たすか、という **予算設計** に入れる。

## 7. 総括

DKMK-016C は、抽象 budget source の **運用規約を確定したフェーズ** じゃ。

今の状態では、下流 provider はもう十分きれいに整っておる。
残る山は、`base` と `ratio` をどう選び、どの `error` で予算を閉じるか。

賢狼の見立てでは、次は小さな constructor theorem よりも、 **concrete `base` / `ratio` candidate の review** が実り多そうじゃ。
港の岸壁と入港手順は整った。次は、どの船を最初に入れるかを決める段じゃな。
