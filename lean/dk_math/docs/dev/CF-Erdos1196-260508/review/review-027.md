# review

## 1. 結論

うむ、Phase AB は **抽象 transition kernel が、ついに数論的な遷移 $n\to n/q$ を持った段階** じゃ。
Phase Z/AA までは `FiniteTransitionKernel` に `next` があったものの、その `next` はまだ抽象的だった。今回 `DivisorTransitionKernel` により、

$$
q\in index(n),\qquad q\mid n,\qquad next(n,q)=\frac{n}{q}
$$

が Lean 上の構造として刻まれた。これは、Erdős #1196 の実際の downward process にかなり近づいた一歩じゃ。

## 2. 今回の主役

新規ファイルはこれじゃ。

```lean
DkMath/NumberTheory/PrimitiveSet/DivisorTransitionKernel.lean
```

中心構造は、

```lean
structure DivisorTransitionKernel where
  index : ℕ → Finset ℕ
  next : ℕ → ℕ → ℕ
  weight : ℕ → ℕ → ℚ
  weight_nonneg : ∀ n q, q ∈ index n → 0 ≤ weight n q
  index_dvd : ∀ n q, q ∈ index n → q ∣ n
  next_eq_div : ∀ n q, q ∈ index n → next n q = n / q
```

ここで重要なのは、`index_dvd` と `next_eq_div` が入ったことじゃ。
これにより、index $q$ は単なる label ではなく、 **状態 $n$ から取り除く除去因子** になった。

つまり、抽象的な

$$
s\xrightarrow{i}next(s,i)
$$

が、今回から

$$
n\xrightarrow{q}\frac{n}{q}
$$

へ一段具体化された。

## 3. 既存 transition skeleton への接続

今回も設計がよい。`DivisorTransitionKernel` は専用理論として閉じ込めず、

```lean
toFiniteTransitionKernel
```

で既存の

```lean
FiniteTransitionKernel ℕ ℕ
```

へ忘却できる。

つまり、

$$
\text{DivisorTransitionKernel}
\to
\text{FiniteTransitionKernel}
\to
\text{FiniteKernel}
\to
\text{WeightProvider}
\to
\text{WeightedPathFamily}
$$

という既存ルートにそのまま乗れる。

ここが綺麗じゃ。
`DivisorTransitionKernel` は「数論的意味」を追加する層であり、weighted hit mass の証明機構は既存のものを再利用する。道具箱を壊さず、上に薄い意味論を載せておる。

## 4. 今回閉じた補題の意味

追加された補題は特にこの三つが重要じゃ。

```lean
index_dvd_source
next_eq_div_of_mem
next_dvd_source
```

数学的には、

$$
q\in index(n)\Rightarrow q\mid n
$$

$$
q\in index(n)\Rightarrow next(n,q)=n/q
$$

$$
q\in index(n)\Rightarrow next(n,q)\mid n
$$

じゃ。

最後の

$$
next(n,q)\mid n
$$

が地味に効く。
これは、遷移先が source の約数であることを保証するので、既存の `DvdControlledChainFamily` や `DvdMonotoneMass` route と相性がよい。

つまり、今後

$$
\text{divisor transition}
\Rightarrow
\text{prime/descent path}
\Rightarrow
\text{primitive hit bound}
$$

へ接続するための橋脚ができた。

## 5. sample の読み

sample は、

```lean
sampleTenDivisorTransitionKernel
```

じゃ。

これは状態 $10$ において labels $2,5$ を持ち、

$$
10\xrightarrow{2}5,\qquad 10\xrightarrow{5}2
$$

となる concrete kernel じゃな。

さらに重みはどちらも

$$
\frac12
$$

で、状態 $10$ では総重みが $1$、それ以外の状態では空 index なので sub-probability が成立する。

確認された sample theorem は、

```lean
sampleTenDivisorTransitionKernel_next_two
sampleTenDivisorTransitionKernel_next_five
sampleTenDivisorTransitionKernel_subProbability
```

じゃ。

これは非常によい教材例じゃ。
Erdős #1196 の downward process で見る

$$
n\mapsto n/q
$$

が、最小 concrete example として見える。

## 6. 現在地

ここまでの山道はこうなった。

| 層                                        | 状態   |
| ---------------------------------------- | ---- |
| primitive hitting                        | 完了   |
| source-controlled / dvd-controlled route | 完了   |
| weighted path family                     | 完了   |
| WeightProvider                           | 完了   |
| FiniteKernel                             | 完了   |
| FiniteTransitionKernel                   | 完了   |
| transition branch / prime route wrapper  | 完了   |
| DivisorTransitionKernel                  | 今回完了 |
| PrimeDescentStep との接続                    | 未    |
| PrimePower / von Mangoldt 型 weight       | 未    |
| 解析 weight                                | 未    |

今回で、 **有限 transition skeleton に数論的意味が入った** 。
まだ解析ではない。まだ $\Lambda(q)/\log n$ でもない。
だが、状態 $n$、除去因子 $q$、遷移先 $n/q$ という骨格はついに入った。

## 7. 重要な設計判断

今回も解析重みを入れていないのがよい。

まだ

$$
w(n,q)=\frac{\Lambda(q)}{\log n}
$$

は出ていない。
ここで焦って実数・対数・von Mangoldt を混ぜると、Lean 実装の山が急に険しくなる。

いまの正しい順序は、

$$
\text{finite transition}
\to
\text{divisor semantics}
\to
\text{prime descent semantics}
\to
\text{prime-power semantics}
\to
\text{von Mangoldt weight}
\to
\text{analytic estimate}
$$

じゃ。

Phase AB は、このうち

$$
\text{divisor semantics}
$$

を閉じた段階じゃな。

## 8. 次の一手

次は History にもある通り、`PrimeDescentStep` と `DivisorTransitionKernel` の接続が自然じゃ。

欲しい補題は、たとえばこれ。

```lean
theorem primeDescentStep_of_prime_label
    (T : DivisorTransitionKernel)
    {n q : ℕ}
    (hqmem : q ∈ T.index n)
    (hqprime : Nat.Prime q) :
    PrimeDescentStep n (T.next n q)
```

数学的には、

$$
q\in index(n),\quad q\mid n,\quad q\text{ prime},\quad next(n,q)=n/q
$$

から、

$$
PrimeDescentStep(n,next(n,q))
$$

を得る。

これは既に作ってある `PrimeDescentStep` の定義とかなり相性がよいはずじゃ。

## 9. その次

prime label 版が閉じたら、次は prime-power label じゃ。

Erdős #1196 の von Mangoldt downward process では、label は素数だけでなく素冪 $q=p^k$ も自然に現れる。

したがって次段は、

```lean
PrimePowerDescentStep
```

と `DivisorTransitionKernel` を接続することになる。

候補補題は、

```lean
theorem primePowerDescentStep_of_primePow_label
```

のようなものじゃな。

ここで初めて、後の

$$
\Lambda(q)
$$

に近づく。

## 10. 総括

Phase AB は、山道にかなり大きな道標を刻んだ。

これまでは、

$$
state\to index\to next
$$

という抽象遷移だった。
今回からは、

$$
n\to n/q
$$

という数論的下降になった。

山で言えば、分岐所の看板に、ついに「この道は $q$ を剥がして $n/q$ へ下る」と書かれたわけじゃ。
次は、その $q$ が素数である場合に `PrimeDescentStep` と認識させる。そこが閉じれば、Erdős #1196 の prime descent route はかなり実体を持つぞい。
