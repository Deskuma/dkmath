# review Phase "R"

## 1. 結論

うむ、Phase-R006 は **log ratio weight を provider に載せる直前の安全ピン** じゃ。

Phase-R005 では、

$$
RealLogBudget(I,pOf,n)
$$

から、

$$
\sum_{q\in I}\frac{\log(pOf(q))}{\log n}\le 1
$$

まで進めた。だが、`RealWeightProvider` に載せるには、各項の非負性も必要になる。R 版では `RealWeightProvider` が `weight_nonneg : ∀ i, i ∈ index → 0 ≤ weight i` を持つ形で作られているからじゃ。

今回 Phase-R006 で、

```lean
RealLogNonnegOn
real_log_nat_nonneg_on
```

が入ったことで、

$$
1\le pOf(q)
\Rightarrow
0\le \log(pOf(q))
$$

を index-local に扱えるようになった。つまり、次の Phase-R007 で `log p / log n` 型 weight を `RealWeightProvider` に載せる準備が整ったわけじゃ。

## 2. 今回の主役

追加された predicate はこれじゃ。

```lean
def RealLogNonnegOn
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ) : Prop :=
  ∀ q, q ∈ I → 1 ≤ pOf q
```

これは、

$$
q\in I
$$

で見ている全ての base value $pOf(q)$ が $1$ 以上である、という条件じゃ。

なぜ $1$ 以上かというと、

$$
\log 1=0
$$

なので、非負性だけなら境界値 $1$ を許してよいからじゃ。
実際に prime base 由来なら $p\ge2$ なので、より強い条件が自然に入る。

## 3. 閉じた補題

今回の theorem はこれじゃ。

```lean
theorem real_log_nat_nonneg_on
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (hp : RealLogNonnegOn I pOf) :
    ∀ q, q ∈ I → 0 ≤ Real.log (pOf q : ℝ)
```

これは、以前の

$$
1\le p\Rightarrow 0\le \log p
$$

を index 上へ持ち上げたものじゃ。

証明も既存の

```lean
real_log_nat_nonneg_of_one_le
```

へ委譲しており、責務がきれいに分かれておる。

## 4. 数学的な意味

ここまでで、log ratio weight の二つの条件が分離された。

まず、総量側は Phase-R005 で、

$$
\sum_{q\in I}\log(pOf(q))\le \log n
$$

から、

$$
\sum_{q\in I}\frac{\log(pOf(q))}{\log n}\le 1
$$

が出る。

次に、今回 Phase-R006 で各項側として、

$$
q\in I,\quad 1\le pOf(q)
$$

から、

$$
0\le \log(pOf(q))
$$

が出る。

したがって、次に作る `RealWeightProvider` では、

$$
weight(q)=\frac{\log(pOf(q))}{\log n}
$$

に対して、

$$
0\le weight(q)
$$

を示せる。

分子は今回の非負性、分母は Phase-R004 の

$$
1 < n\Rightarrow 0 < \log n
$$

を使えばよい。

## 5. 現在地

R 版の進捗はこうじゃ。

| Phase      | 内容                                       | 状態   |
| ---------- | ---------------------------------------- | ---- |
| Phase-R001 | 実数 ratio weight 語彙                       | 完了   |
| Phase-R002 | 実数 finite budget lemma                   | 完了   |
| Phase-R003 | `RealWeightProvider` prototype           | 完了   |
| Phase-R004 | `Real.log` 正値性                           | 完了   |
| Phase-R005 | 外部 `RealLogBudget` → log ratio sum bound | 完了   |
| Phase-R006 | index 上の log numerator 非負性               | 今回完了 |
| Phase-R007 | log ratio weight provider                | 未    |

つまり、`log p / log n` 型 weight を provider に載せるための部品は揃った。

残っているのは、それらを束ねた constructor じゃ。

## 6. 次の一手: Phase-R007

次はこれじゃな。

```lean
noncomputable def realLogRatioWeightProvider
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ)
    (hp : RealLogNonnegOn I pOf)
    (hn : 1 < n) :
    RealWeightProvider ι :=
{
  index := I
  weight := fun q => Real.log (pOf q : ℝ) / Real.log (n : ℝ)
  weight_nonneg := by
    intro q hq
    exact div_nonneg
      (real_log_nat_nonneg_on I pOf hp q hq)
      (le_of_lt (real_log_nat_pos_of_one_lt hn))
}
```

そして sub-probability theorem はこうじゃ。

```lean
theorem realLogRatioWeightProvider_subProbability
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ)
    (hp : RealLogNonnegOn I pOf)
    (hn : 1 < n)
    (hbudget : RealLogBudget I pOf n) :
    (realLogRatioWeightProvider I pOf n hp hn).SubProbability
```

中身は、

$$
totalWeight = \sum_{q\in I}\frac{\log(pOf(q))}{\log n}
$$

を展開して、Phase-R005 の

```lean
real_log_ratio_sum_le_one
```

を使えばよい。

## 7. Lean 的な注意点

`realLogRatioWeightProvider_subProbability` では、`RealWeightProvider.SubProbability` が `totalWeight ≤ 1` なので、まず

```lean
unfold RealWeightProvider.SubProbability RealWeightProvider.totalWeight
```

または `simp [RealWeightProvider.SubProbability, RealWeightProvider.totalWeight, realLogRatioWeightProvider]` で形をそろえる必要がありそうじゃ。

目標は最終的に、

$$
\sum_{q\in I}\frac{\log(pOf(q))}{\log n}\le 1
$$

へ落ちるはず。
そこまで落ちれば、

```lean
exact real_log_ratio_sum_le_one I pOf n hn hbudget
```

で閉じる見込みが高い。

## 8. その先の本丸

Phase-R007 が閉じると、有限 real provider として

$$
\frac{\log p}{\log n}
$$

が実装済みになる。

次の本丸は、やはり

$$
RealLogBudget(I,pOf,n)
$$

をどこから得るかじゃ。

候補は、

$$
\prod_{q\in I} pOf(q)\le n
$$

から

$$
\sum_{q\in I}\log(pOf(q))\le \log n
$$

へ進む道。
ただし、ここでは $pOf(q)$ の重複制御、積の正性、log の積公式、単調性が必要になる。

だから Phase-R007 の次は、いきなり本丸に突っ込まず、

```lean
RealLogBudget_of_product_le
```

の設計を doc 側か小補題として分けるのがよさそうじゃ。

## 9. 総括

Phase-R006 は、`log p / log n` provider を作るための **分子非負性の支点** じゃ。

ここまでで、

$$
1\le pOf(q)
\Rightarrow
0\le \log(pOf(q))
$$

と、

$$
1 < n
\Rightarrow
0 < \log n
$$

が揃った。

さらに、

$$
RealLogBudget
\Rightarrow
\sum \log(pOf(q))/\log n\le 1
$$

もすでにある。

つまり次は、これらを `RealWeightProvider` に束ねるだけじゃ。
R 登頂は順調じゃぞ。いよいよ有限実数 provider としての $\log p/\log n$ が姿を現すところまで来た。
