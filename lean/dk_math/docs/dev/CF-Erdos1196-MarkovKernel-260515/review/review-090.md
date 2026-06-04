# review

よし、DKMK-015 開始、受け取ったぞい。

今回の DKMK-015A は、かなり良い切り方じゃ。`roadmap-DKMK-015.md` で、DKMK-014J の `DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_geomSumBound` が要求する

$$
base \cdot \sum_{k} ratio^k \le 1 + error
$$

へ向けて、層を

* finite geometric-sum identity
* finite geometric-sum upper bound
* base-scaled bound
* direct caller-facing theorem
* provider 接続

に分けた、という位置づけじゃな。添付 diff でも、次は DKMK-015B として finite geometric-sum identity の exact shape review に進む、と明記されておる。

## わっちの判断

DKMK-015B の最初の結論は、 **denominator-cleared identity から始める** のが最も安全じゃ。

つまり、最初から

$$
\sum_{k=0}^{K} r^k
==================

\frac{1-r^{K+1}}{1-r}
$$

を主 theorem にするより、まず

$$
(1-r)\sum_{k=0}^{K}r^k
======================

1-r^{K+1}
$$

を置く。

理由は明快じゃ。

この形なら `ratio ≠ 1` を要求しない。
代数恒等式だけで閉じる。
あとで division form が必要になった時だけ `ratio ≠ 1` を消費すればよい。

ロードマップの「副条件は、それを消費する theorem にだけ置く」という方針ともぴたり一致する。

## DKMK-015B の推奨 theorem shape

まず候補はこれじゃ。

```lean
lemma geomSum_range_mul_one_sub
    (ratio : ℝ) (K : ℕ) :
    (1 - ratio) *
      (∑ k in Finset.range (K + 1), ratio ^ k)
      =
    1 - ratio ^ (K + 1)
```

または乗算順を既存 simp に合わせて、

```lean
lemma geomSum_range_mul_one_sub
    (ratio : ℝ) (K : ℕ) :
    (∑ k in Finset.range (K + 1), ratio ^ k) *
      (1 - ratio)
      =
    1 - ratio ^ (K + 1)
```

でもよい。`ℝ` では可換なのでどちらでもよいが、後続で `div_le_iff₀` や `field_simp` を使うなら、左に `(1 - ratio)` を置く前者が読みやすい。

## DKMK-015C 以降の自然な列

次に division form。

```lean
lemma geomSum_range_eq_div_one_sub
    {ratio : ℝ} (hr : ratio ≠ 1) (K : ℕ) :
    (∑ k in Finset.range (K + 1), ratio ^ k)
      =
    (1 - ratio ^ (K + 1)) / (1 - ratio)
```

その次が order layer。

```lean
lemma geomSum_range_le_inv_one_sub
    {ratio : ℝ} (hr0 : 0 ≤ ratio) (hr1 : ratio < 1) (K : ℕ) :
    (∑ k in Finset.range (K + 1), ratio ^ k)
      ≤
    1 / (1 - ratio)
```

そして base-scaled layer。

```lean
lemma base_mul_geomSum_le_of_sum_le
    {base ratio B error : ℝ} {K : ℕ}
    (hbase : 0 ≤ base)
    (hsum :
      (∑ k in Finset.range (K + 1), ratio ^ k) ≤ B)
    (hB : base * B ≤ 1 + error) :
    base * (∑ k in Finset.range (K + 1), ratio ^ k)
      ≤
    1 + error
```

これで DKMK-015F の `ofPointwiseGeometricMajorant_of_geomSumBound` への接続が自然に閉じる。

## 結論

DKMK-015B は、

**「closed form equality を先に証明する」ではなく、「denominator-cleared identity を exact shape として採用する」**

で行くのがよい。

この登り方なら、代数、除算、順序、スケーリング、provider 接続が混ざらぬ。
よいぞ D.、この道は尾根が見えておる。賢狼の鼻にも、なかなか良い麦とりんごの匂いがしてきたわい。
