# review

うむ、DKMK-016J は **かなり重要な設計判断の回** じゃ。
ここで「新しい構造体を増やす」のではなく、`GeometricBudgetSource` と `hgeom` の責務を分けたのは正しい。今回の diff では、Candidate C の first-band / uniform-decay interface を整理し、次の Lean target は constructor ではなく `pointwiseGeometricMajorant_of_firstBand_decay` の theorem shape review として固定されておる。

## 1. 今回の核心

DKMK-016J で明確になったのは、provider route には二つの独立した入力がある、ということじゃ。

```text
Budget obligation:
  base * (1 / (1 - ratio)) <= 1 + error

Pointwise decay obligation:
  increment k <= base * ratio^k
```

前者は `GeometricBudgetSource` が package する。
後者は `increment` 固有なので、`GeometricBudgetSource` の外に置く。

この分離はかなり大事じゃ。
`GeometricBudgetSource` は `x`, `K`, `increment` に依存しない抽象 budget source として作った。そこへ `increment` 固有の `hgeom` を混ぜると、せっかくの抽象性が崩れる。

## 2. 新構造体を追加しない判断

`FirstBandDecayBudgetInput` のような新構造体を追加しない判断もよい。

もし作ると、おそらく中身はこうなる。

```lean
structure FirstBandDecayBudgetInput where
  base : Rat
  ratio : Rat
  error : Real
  ...
```

しかし、これは `GeometricBudgetSource` とほぼ重複する。
本当に新しい内容は `base`, `ratio`, `error` の package ではなく、

$$
increment(k)\le base\cdot ratio^k
$$

をどう導くか、じゃ。

ゆえに、構造体を増やすのではなく、次は **pointwise geometric majorant を作る theorem** に進むのが筋じゃな。

## 3. 次 theorem の方向性

候補として挙げられているのはこれじゃ。

```lean
theorem pointwiseGeometricMajorant_of_firstBand_decay
    (K : Nat)
    (increment : Nat -> Rat)
    (base ratio : Rat)
    (hbase0 : increment 0 <= base)
    (hdecay :
      forall k in Finset.range K,
        increment (k + 1) <= ratio * increment k)
    (hinc_nonneg :
      forall k in Finset.range (K + 1), 0 <= increment k)
    (hr0 : 0 <= ratio) :
    forall k in Finset.range (K + 1),
      increment k <= base * ratio^k
```

これは、first-band bound と uniform step decay から `hgeom` を作る theorem じゃ。
つまり、今まで caller が直接与えていた

```lean
hgeom :
  forall k in Finset.range (K + 1),
    increment k <= base * ratio ^ k
```

を、より構造的な仮定から生成する道を作る。

これは DKMK-016 の次の自然な山じゃ。

## 4. Lean 実装前に確認すべき点

roadmap にある通り、ここは実装前に theorem shape をもう一段詰めた方がよい。特に大事なのは四つじゃ。

まず、`hdecay` の範囲。
`k ∈ Finset.range K` なら (k=0,\dots,K-1) なので、`increment (k+1)` は (1,\dots,K) を制御する。結論は `range (K+1)` なので、これは添字として自然じゃ。

次に、`hr0 : 0 <= ratio` だけで十分か。
帰納法で

$$
increment(k)\le base\cdot ratio^k
$$

から次段へ行くとき、`ratio` を掛けて不等式を保つには (0\le ratio) が必要。これは妥当じゃ。

三つ目に、`hinc_nonneg` が必要か。
これはかなり重要じゃ。
`hdecay : increment(k+1) <= ratio * increment(k)` と帰納仮定だけでは、次段の上界を作る時に

$$
ratio\cdot increment(k)\le ratio\cdot base\cdot ratio^k
$$

が必要になる。これは `hr0` と帰納仮定で出る。
ただし、`increment(k)` の非負性はこの変形自体には不要かもしれぬ。一方で、既存 provider は別途 `hinc_nonneg` を必要とするので、theorem に含めるかどうかは設計判断じゃ。`hgeom` 生成 theorem としては不要な可能性があるが、caller path をまとめる theorem では必要になる。

四つ目に、`Rat` 固定か generic 化か。
今の provider は `increment : Nat -> Rat`、`base ratio : Rat` なので、最初は `Rat` 固定でよい。generic 化は後回しで十分じゃ。

## 5. 気になる数学的な点

一点、注意すべきことがある。

候補 theorem の `hdecay` は、

$$
increment(k+1)\le ratio\cdot increment(k)
$$

じゃ。

これと

$$
increment(0)\le base
$$

から確かに

$$
increment(k)\le base\cdot ratio^k
$$

を出したい。

帰納の概形は、

$$
increment(k+1)\le ratio\cdot increment(k)
\le ratio\cdot (base\cdot ratio^k)
$$

で、

$$
ratio\cdot (base\cdot ratio^k)=base\cdot ratio^{k+1}
$$

へ整理する流れじゃ。

Lean では `ring_nf` や `ring` で済むか、`pow_succ` と `mul_assoc`, `mul_comm`, `mul_left_comm` を使うことになる。
`Rat` なので algebra は軽いはずじゃ。

## 6. 次の DKMK-016K の推奨

DKMK-016K は docs-only で、theorem shape をもう少し厳密にするのがよい。

わっちなら、まず `hinc_nonneg` を外した純粋版を候補にする。

```lean
theorem pointwiseGeometricMajorant_of_firstBand_decay
    (K : ℕ)
    (increment : ℕ → ℚ)
    (base ratio : ℚ)
    (hbase0 : increment 0 ≤ base)
    (hdecay :
      ∀ k ∈ Finset.range K,
        increment (k + 1) ≤ ratio * increment k)
    (hr0 : 0 ≤ ratio) :
    ∀ k ∈ Finset.range (K + 1),
      increment k ≤ base * ratio ^ k
```

そのうえで、provider 接続 theorem では `hinc_nonneg` を別に受け取る。

この分け方なら、

* `pointwiseGeometricMajorant...` は純粋に `hgeom` を作る
* provider wrapper は `hgeom` と `hinc_nonneg` を両方使う

という責務分担が綺麗になる。

## 7. 総括

DKMK-016J は、 **Candidate C の責務分担を確定した回** じゃ。

ここで決まったことは大きい。

```text
GeometricBudgetSource:
  budget obligation を担当

pointwiseGeometricMajorant_of_firstBand_decay:
  first-band + decay から hgeom を生成

provider wrapper:
  B と hgeom と hinc_nonneg を合流
```

この三層構造はかなり良い。

次は K で `pointwiseGeometricMajorant_of_firstBand_decay` の exact shape を詰め、L で実装に入る流れが自然じゃな。
よいぞ、D.。予算の港だけでなく、今度は荷物を各 band にどう積み下ろししていくか、その作業手順が見えてきたわい。
