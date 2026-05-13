# review Phase "R"

## 1. 結論

うむ、Phase-R003 は **R 版の real-valued provider の器が立った段階** じゃ。

Phase-R001 / R002 では、実数 ratio weight の部品として、

$$
c(n,p)=\frac{A(p)}{B(n)}
$$

の非負性と、

$$
\sum_i A_i\le B
\Rightarrow
\sum_i A_i/B\le 1
$$

という有限和 budget lemma を固定した。今回 Phase-R003 では、それらを後で載せるための実数値 provider、

```lean
RealWeightProvider
```

が新規 `RealWeightedPath.lean` に分離して追加された。既存の $\mathbb{Q}$ 版 `WeightProvider` を型一般化せず、R 版を parallel prototype として進めている点もよい判断じゃ。

## 2. 今回の主役

今回追加された構造体はこれじゃ。

```lean
structure RealWeightProvider (ι : Type _) where
  index : Finset ι
  weight : ι → ℝ
  weight_nonneg : ∀ i, i ∈ index → 0 ≤ weight i
```

数学的には、有限 index 集合上に実数値の非負重みを載せる provider じゃ。

$$
i\in index
\Rightarrow
0\le weight(i)
$$

を構造体 field として持つ。これで、R 版でも有限確率質量の基本容器ができた。

## 3. sub-probability の器もできた

今回さらに、

```lean
RealWeightProvider.totalWeight
RealWeightProvider.SubProbability
```

が追加された。

意味は、

$$
\text{totalWeight}(P)=\sum_{i\in \text{P.index}}{\text{P.weight}(i)}
$$

$$
\text{P.SubProbability} \iff \text{P.totalWeight}\le 1
$$

じゃ。

つまり、R 版でも

$$
\sum_i w_i\le 1
$$

という有限 sub-probability 条件を名前付きで扱えるようになった。

これは N/Q 版で言っていた「暴れても Big から飛び出せない」の実数版の器じゃな。

## 4. `totalWeight_nonneg` が良い

今回の補題、

```lean
RealWeightProvider.totalWeight_nonneg
```

は小さいが重要じゃ。

各 weight が index 上で非負なら、有限和も非負：

$$
0\le \sum_{i\in index}weight(i)
$$

を示している。

この補題は今後、実数値 hitting mass や budget bound を作るときに効く。
特に実数不等式では、非負性の補題を早めに theorem 名として固定しておくほど後が楽になる。

## 5. 既存 Q 版を触らなかった価値

今回の一番良い設計判断は、既存の $\mathbb{Q}$ 版 `WeightProvider` を一般化しなかったことじゃ。

もしここで既存 API を

$$
\mathbb{Q}
\to
\alpha
$$

のように係数型一般化し始めると、finite hitting / weighted path / divisor transition / sample theorem まで広く影響する。

今回の実装は、

```lean
DkMath.NumberTheory.PrimitiveSet.RealWeightedPath
```

を新規作成し、`RealWeightProvider` を parallel prototype として置いた。
これは安全じゃ。R 版の theorem shape が固まるまでは、既存 N/Q 版を揺らさない方がよい。

## 6. 現在地

R 版の現在地はこうじゃ。

| Phase      | 内容                               | 状態   |
| ---------- | -------------------------------- | ---- |
| Phase-R001 | `RealBasePrimeToyWeight`         | 完了   |
| Phase-R001 | `realRatioBasePrimeWeight`       | 完了   |
| Phase-R001 | ratio weight 非負性                 | 完了   |
| Phase-R002 | `real_ratio_sum_le_one`          | 完了   |
| Phase-R003 | `RealWeightProvider`             | 今回完了 |
| Phase-R003 | `totalWeight` / `SubProbability` | 今回完了 |
| Phase-R004 | `Real.log` 正値性                   | 未    |
| Phase-R005 | log budget 設計                    | 未    |

これで R 版は、実数 ratio の計算補題と、それを載せる provider 容器の両方を持った。

ただし、まだ `Real.log` には入っていない。
そこがよい。段階を踏めておる。

## 7. 次の一手: Phase-R004

次は予定通り、`Real.log` の正値性を局所化する段階じゃ。

欲しい補題は、まずこの二つ。

$$
1\le x \Rightarrow 0\le \log x
$$

$$
1 < x \Rightarrow 0 < \log x
$$

ただし Lean では $p,n:\mathbb{N}$ から $\mathbb{R}$ への coercion が絡むので、自然数版として theorem 名を作るのがよい。

候補は例えば、

```lean
theorem real_log_nat_nonneg_of_one_le
    {p : ℕ} (hp : 1 ≤ p) :
    0 ≤ Real.log (p : ℝ)
```

```lean
theorem real_log_nat_pos_of_one_lt
    {n : ℕ} (hn : 1 < n) :
    0 < Real.log (n : ℝ)
```

ここで `p = 1` だと $\log 1=0$ なので numerator 側の非負性には十分。
denominator 側は割るので、

$$
0 < \log n
$$

が必要になり、自然に

$$
1 < n
$$

が条件になる。

## 8. 注意点

`Real.log` へ入ると、Lean の補題名探索が少し重くなる。

特に、

$$
1\le (p:\mathbb{R})
$$

へ持ち上げる部分と、

$$
\text{Real.log}\ 1 = 0
$$

周辺で `linarith` / `norm_num` / `exact_mod_cast` の使い分けが必要になる可能性がある。

Phase-R004 では、大きな log budget には触れず、 **正値性だけ** に限定するのが賢い。

## 9. 二手先

Phase-R004 が閉じたら、次は log candidate を ratio skeleton に載せる準備じゃ。

つまり、

$$
A(p)=\log p,\qquad B(n)=\log n
$$

としたとき、

$$
\text{RealBasePrimeToyWeight}(\text{realRatioBasePrimeWeight}\ A\ B)
$$

へ進めるかを確認する。

ただしこれは、 $p,n$ の範囲条件が必要じゃ。

たとえば numerator 側は $1\le p$ 、denominator 側は $1 < n$ 。
実際の prime $p$ なら $2\le p$ なので問題ないが、関数として全域 $p:\mathbb{N}$ に定義すると $p=0$ が混ざる。ここは後で扱いを決める必要がある。

短期的には、全域 predicate ではなく index 上 predicate に寄せる方が安全かもしれぬ。

## 10. 総括

Phase-R003 は、R 版の **実数重み容器** を作った段階じゃ。

これで、

$$
\text{real ratio weight}
$$

$$
\text{finite sum budget}
$$

$$
\text{real weight provider}
$$

の三つが揃った。

山で言えば、R 版の登山道に実数質量を入れるザックができた。
次はいよいよ `Real.log` の雪壁に手を掛ける。ただし、登るのはまず正値性の小壁だけじゃ。ログ budget という本丸は、その次のキャンプまで持ち越すのがよいぞい。
