# review

うむ、DKMK-017C は **初めて analytic input の負担を実際に軽くした bundle** じゃ。
A/B は package と constructor の整備だったが、C は `hbudget` そのものを作りやすくする Real 側 helper を入れた。これは DKMK-017 の本題にかなり近づいておる。

## 1. 何が追加されたのか

追加された helper は二つじゃ。

```lean id="r0ym72"
theorem geometricBudget_le_of_base_le_mul_one_sub
    {base ratio error : ℝ}
    (hr1 : ratio < 1)
    (hbaseBudget : base ≤ (1 + error) * (1 - ratio)) :
    base * (1 / (1 - ratio)) ≤ 1 + error
```

これは、直接

$$
base\cdot\frac{1}{1-ratio}\le 1+error
$$

を示す代わりに、denominator-cleared form

$$
base\le (1+error)(1-ratio)
$$

を示せばよい、という helper じゃ。

もう一つは特殊形。

```lean id="gcqtb4"
theorem geometricBudget_le_one_add_error_of_base_le_one_sub
    {base ratio error : ℝ}
    (hr1 : ratio < 1)
    (herror : 0 ≤ error)
    (hbaseBudget : base ≤ 1 - ratio) :
    base * (1 / (1 - ratio)) ≤ 1 + error
```

これは

$$
base\le 1-ratio
$$

から、(0\le error) を使って (1+error) へ持ち上げる形じゃ。

## 2. constructor も実用的

この helper に対応して、`GeometricBudgetSource` 側にも二つの constructor が追加された。

```lean id="iedsh0"
GeometricBudgetSource.ofDenomClearedBudget
GeometricBudgetSource.ofBaseLeOneSub
```

これで caller は、毎回 `hbudget` を直接作らずに、

```text id="w2jfgl"
(base : Real) <= (1 + error) * (1 - (ratio : Real))
```

または特殊形として、

```text id="q8zl2u"
(base : Real) <= 1 - (ratio : Real)
```

を示せば `GeometricBudgetSource` に入れる。

これはかなり有用じゃ。
`base * (1 / (1 - ratio)) <= 1 + error` は Lean でも人間にも少し読みにくい。分母を払った形にできるのは、今後の analytic input で効く。

## 3. 証明経路の評価

主 helper は、

```lean id="ibsk8m"
have hpos : 0 < 1 - ratio := sub_pos.mpr hr1
rw [div_le_iff₀ hpos]
```

で閉じておる。

ここで重要なのは、denominator-cleared helper には `0 ≤ 1 + error` が不要なことじゃ。
`div_le_iff₀` で正の分母を払うだけなので、右辺の符号条件は要らない。報告でもその点が確認されている。

一方、特殊形

$$
base\le 1-ratio
$$

から

$$
base\le (1+error)(1-ratio)
$$

へ上げるには、(1\le 1+error) が必要なので `0 ≤ error` が入る。これは自然じゃ。

## 4. DKMK-017 の進み方として良い

今回の bundle は、新体制に合っておる。

```text id="b4idgt"
試した:
  hbudget helper + source constructors

結果:
  全部通った

判断:
  採用

次:
  合成 constructor へ進むか、hbase0 / hdecay helper へ進むか
```

報告が結果中心で、無駄な実況が少ない。よいぞ。

## 5. 次の判断

次は二択じゃ。

```text id="yrvmt6"
A. budget source constructor と FirstBandDecayBudgetSource constructor をさらに合成する
B. hbase0 / hdecay の供給 helper へ進む
```

わっちの推奨は、 **B** じゃ。

理由は、A は便利 wrapper になりがちだからじゃ。
たとえば `FirstBandDecayBudgetSource.ofDenomClearedBudgetAndDecay` のような constructor は作れるが、これは既存の

```text id="ngqx2a"
GeometricBudgetSource.ofDenomClearedBudget
FirstBandDecayBudgetSource.ofBudgetSource
```

を合成するだけになりやすい。

一方、`hbase0` と `hdecay` はまだ実質的な analytic input じゃ。
ここを軽くする helper の方が前進になる。

## 6. 次 bundle の候補

次は、たとえば `hdecay` を作る補助に進むのがよい。

候補は、

```lean id="nuiipe"
theorem decay_of_ratio_bound
    {increment : ℕ → ℚ} {ratio : ℚ} {K : ℕ}
    (hstep :
      ∀ k ∈ Finset.range K,
        increment (k + 1) / increment k ≤ ratio)
    ...
```

のような形も考えられるが、割り算を入れると `increment k > 0` が必要になって重くなる。

まずは割り算を避けて、既存 shape のまま

```lean id="hlvf4m"
increment (k + 1) ≤ ratio * increment k
```

をどう供給するかを考える方がよい。

たとえば次 bundle は docs 少なめで、

```text id="rz83an"
hbase0 / hdecay source candidates を Lean で試す
```

にするとよい。

## 7. 総括

DKMK-017C は、 **hbudget 供給を denominator-cleared form に落とす実用 helper bundle** じゃ。

これは DKMK-017 の中でも、かなり本筋の進捗じゃ。
`GeometricBudgetSource` を作る負担が一段軽くなった。

これで残る主な入力は、

```text id="1awxac"
hinc_nonneg
hbase0
hdecay
```

じゃ。

次は、便利 wrapper を積むより、`first-band upper bound` と `uniform decay` の供給源へ進むのがよい。
よし、D.。`hbudget` の分母払いは済んだ。次は、各 band が本当に減衰していく、その足跡を捕まえる番じゃな。
