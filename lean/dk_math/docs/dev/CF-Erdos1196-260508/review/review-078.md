# review Phase "R"

## 1. 結論

うむ、Phase-R019 は **重複なし route がほぼ完成した段階** じゃ。
Phase-R018 では、witness provider 由来の base prime が source $n$ を割ることまで閉じた。今回 Phase-R019 では、残っていた

$$
\mathrm{NatPairwiseCoprimeOn}\ I\ (\mathrm{W.basePrimeOf}\ n\ I\ hI)
$$

を、より扱いやすい

$$
\mathrm{NatPairwiseDistinctOn}\ I\ (\mathrm{W.basePrimeOf}\ n\ I\ hI)
$$

から供給できるようになった。つまり、selected base primes が互いに異なれば、 $\log p/\log n$ 型 real provider が `SubProbability` になるところまで no-sorry で通った、ということじゃ。

## 2. 今回の主役

今回追加された抽象語彙はこれじゃ。

```lean
def NatPairwiseDistinctOn
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ) : Prop :=
  ∀ i, i ∈ I → ∀ j, j ∈ I → i ≠ j → pOf i ≠ pOf j
```

これは、選択集合 $I$ 上で、異なる index が異なる base value を読むことを表している。

そして次が重要な橋じゃ。

```lean
theorem natPairwiseCoprimeOn_of_pairwise_distinct_prime
```

数学的には、

$$
p_i,\ p_j\text{ が素数},\quad p_i\ne p_j
\Rightarrow
\gcd(p_i,p_j)=1
$$

を Finset 上に持ち上げたものじゃな。

## 3. witness provider 側の補題

`DivisorTransitionKernel.lean` 側では、

```lean
PrimePowerWitnessProvider.basePrimeOf_prime_on
```

が追加された。

これは、selected sub-index $I$ 上では

$$
\mathrm{W.basePrimeOf}(n,I,hI)(q)
$$

が本当に素数であることを示す補題じゃ。

Phase-R014 では $1\le p$ を得ていた。
Phase-R018 では $p\mid n$ を得ていた。
今回 Phase-R019 で $p$ が素数であることも theorem 名として固定された。

これで、`basePrimeOf` について次の三点が揃った。

$$
1\le p(q)
$$

$$
Nat.Prime(p(q))
$$

$$
p(q)\mid n
$$

かなり強い道具立てじゃ。

## 4. 最終接続

`RealDivisorBridge.lean` では、

```lean
basePrimeOf_realLogRatioWeightProvider_subProbability_of_pairwise_distinct
```

が追加された。

これは、次の仮定から、

$$
I\subseteq \text{T.index}(n)
$$

$$
1 < n
$$

$$
\mathrm{NatPairwiseDistinctOn}\ I\ (\mathrm{W.basePrimeOf}\ n\ I\ hI)
$$

結論として、

$$
(\mathrm{realLogRatioWeightProvider}\ I\ (\mathrm{W.basePrimeOf}\ n\ I\ hI)\ n\ \cdots).\mathrm{SubProbability}
$$

を出す theorem じゃ。

つまり重複なし route はこう閉じた。

$$
\text{base primes are pairwise distinct}
$$

$$
\Rightarrow
\text{base primes are pairwise coprime}
$$

$$
\Rightarrow
\prod p(q)\mid n
$$

$$
\Rightarrow
\prod p(q)\le n
$$

$$
\Rightarrow
RealLogBudget
$$

$$
\Rightarrow
\log p/\log n\text{ provider is sub-probability}
$$

ここまで一本の Lean route として見えるようになった。

## 5. 数学的意味

これは、Erdős #1196 の R route における **重複なし版の有限 log 質量保存** じゃ。

selected labels $q\in I$ がそれぞれ prime-power witness

$$
q=p(q)^{k(q)}
$$

を持ち、その base prime $p(q)$ が互いにすべて異なるなら、各 $p(q)\mid n$ が成立し、異なる素数なので互いに素。したがって、

$$
\prod_{q\in I}p(q)\mid n
$$

となり、

$$
\sum_{q\in I}\log p(q)\le \log n
$$

が出る。ゆえに、

$$
\sum_{q\in I}\frac{\log p(q)}{\log n}\le 1
$$

となる。

お主の言葉で言えば、

$$
\boxed{
\text{重複しない base prime は、Big }n\text{ の中に同時に収まる}
}
$$

じゃな。

## 6. 現在地

現状はかなり良い区切りじゃ。

| 層                                    | 状態   |
| ------------------------------------ | ---- |
| $\log p/\log n$ real provider        | 完了   |
| external `RealLogBudget` route       | 完了   |
| nat product bound route              | 完了   |
| witness base prime が $n$ を割る         | 完了   |
| pairwise-coprime route               | 完了   |
| pairwise-distinct → pairwise-coprime | 今回完了 |
| 重複なし provider sub-probability        | 今回完了 |
| 重複あり valuation route                 | 未    |

つまり、 **重複なし登山道** はほぼ到達した。
次からは **重複あり** 、つまり同じ base prime が複数回現れる場合の指数予算管理に入る。

## 7. 次の一手

ここで一度、Phase-R020 として **重複なし route の summary theorem / doc 整理** を入れるのが良いと思う。

すでに theorem は閉じているが、Phase-R001 から R019 までかなり長い。ここで route をまとめる theorem 名または文書を置くと、次の valuation route に入る前の地図になる。

例えば theorem は既に十分なので、docstring または README 更新で、

```text
pairwise distinct base primes route:
I ⊆ T.index n
1 < n
pairwise distinct basePrimeOf
→ log-ratio real provider sub-probability
```

を明示するのがよい。

Lean theorem を追加するなら、既存 theorem の alias として、

```lean
basePrimeOf_logRatioSubProbability_of_distinctBasePrimes
```

のような短い名前を置くのもありじゃが、名前が増えすぎるなら docs だけでよい。

## 8. その次の本丸

次に進むなら、いよいよ重複あり route じゃ。

目標は、

$$
\prod_{q\in I}basePrime(q)\le n
$$

を pairwise distinct なしで示すこと。

このためには、各素数 $p$ について、

$$
\\\#{q\in I:basePrime(q)=p}\le v_p(n)
$$

のような条件が必要になる。

DkMath 的に言えば、これは **指数消費 tracking** じゃ。
各 selected label が Big $n$ の中の prime exponent budget をどれだけ消費するかを数える。

ここからは別登山道として、`ValuationBudget` や `BasePrimeMultiplicity` のような語彙が必要になるかもしれぬ。

## 9. 総括

Phase-R019 は、R route の重複なし版を完成形に近づけた大きな一歩じゃ。

$$
\mathrm{NatPairwiseDistinctOn}
$$

から

$$
\mathrm{NatPairwiseCoprimeOn}
$$

を供給し、witness provider 由来の base primes が素数であることを使って、

$$
\log p/\log n
$$

provider の `SubProbability` まで到達した。

山で言えば、互いに干渉しない岩、つまり異なる base prime の岩列にザイルを固定する登山道が開通した。
次は、同じ岩を何度も使う場合、どれだけ深く打ち込まれているか――すなわち $p$ -進指数の消費量を測る道へ進む番じゃな。
