# review

## 1. 結論

うむ、Phase AA は **FiniteTransitionKernel の route 対称化完了** じゃ。
Phase Z では `FiniteTransitionKernel` が branch/subconservative route に接続された。今回 Phase AA で prime path / dvd-monotone route にも接続され、

$$
\text{FiniteTransitionKernel}
\to
\text{FiniteKernel}
\to
\text{WeightProvider}
\to
\text{WeightedPathFamily}
\to
\mathrm{weightedHitMass}\le C
$$

の導線が、二つの source-control route の両方で使えるようになった。これはかなり綺麗な節目じゃ。

## 2. 今回追加された核

追加された主役はこの二つじゃ。

```lean
transitionPrimePathFamilyAt
transitionPrimePathFamilyAt_hitMass_le_const_of_subprob
```

前者は、transition kernel の state $s$ から得た provider を、

```lean
I.primePathFamilySourceControlled M F hM
```

へ適用する wrapper。

後者は、`DvdMonotoneMass M` による prime path route でも、

$$
T\text{ sub-probability}
+
\text{source mass}\le C
+
S\text{ primitive}
\Rightarrow
\mathrm{weightedHitMass}\le C
$$

を出す theorem じゃ。

つまり、Phase Z で branch route に対してできていたことが、今回は prime route 側でもできるようになった。

## 3. 対称化された現在の形

いまの transition kernel route はこう並ぶ。

| route        | source control の根拠    | wrapper                             |
| ------------ | --------------------- | ----------------------------------- |
| branch route | `SubConservative M B` | `transitionBranchPrimePathFamilyAt` |
| prime route  | `DvdMonotoneMass M`   | `transitionPrimePathFamilyAt`       |

これで、有限遷移 kernel は片側専用ではなくなった。

branch route は宇宙式 Mass API 的な道じゃ。

$$
\sum_{\text{child}}\mu(child)\le\mu(parent)
$$

prime route は整除単調性の道じゃ。

$$
h\mid source\Rightarrow \mu(h)\le\mu(source)
$$

そして両方とも、同じ `FiniteTransitionKernel` 由来の重み供給を受けて、

$$
\mathrm{weightedHitMass}\le C
$$

へ進める。

この左右対称性は、次に実際の $n\mapsto n/q$ transition を作るときにかなり効くぞい。

## 4. concrete sample の意味

今回追加された sample は、

```lean
erdosFinitePrimitiveInput_two_five_transitionPrimePath_hitMass_le_one
```

じゃ。

これは `sampleUnitTransitionKernel` を prime path route に適用し、 $\{2,5\}$ の finite Erdős input に対して、

$$
\mathrm{weightedHitMass}\le 1
$$

を確認している。

Phase Z の sample は branch route だった。
今回で prime route でも同じ形が通ったので、

$$
\text{transition branch sample}
\qquad
\text{transition prime sample}
$$

が揃ったことになる。

これは API の健全性確認として良い。
「抽象構造は作ったが使い道が曖昧」ではなく、既存 sample で実際に theorem が呼べる状態になっておる。

## 5. 現在地

ここまでで finite transition skeleton はかなり整った。

| 層                                           | 状態   |
| ------------------------------------------- | ---- |
| primitive hitting                           | 完了   |
| source-controlled family                    | 完了   |
| weighted path family                        | 完了   |
| WeightProvider                              | 完了   |
| FiniteKernel                                | 完了   |
| FiniteTransitionKernel                      | 完了   |
| transition branch route                     | 完了   |
| transition prime route                      | 今回完了 |
| divisor / prime descent transition skeleton | 未    |
| analytic weight                             | 未    |

つまり、抽象 finite transition 層は一区切りじゃ。

いまはまだ

$$
next(s,i)
$$

が数論的意味を持っていない。
しかし、 **遷移先を持つ kernel が、既存の hitting mass bound に接続される** ところまでは閉じた。

これは山道で言えば、分岐所に「次の地点」まで書ける地図が整った段階じゃ。

## 6. 重要な設計判断

今回も、解析 weight は入れておらぬ。

これは正しい。

まだ

$$
w(n,q)=\frac{\Lambda(q)}{\log n}
$$

を入れる段階ではない。
まずは、

$$
\text{state}
\to
\text{index}
\to
\text{next state}
$$

という有限遷移の型を作り、それを既存の provider / weighted family / hit bound に接続する。
この順番が安全じゃ。

DkMath 的には、解析層を焦って混ぜるより、

$$
\text{有限構造}
\to
\text{数論的意味}
\to
\text{解析重み}
$$

と登るのがよい。

## 7. 次の一手

次は、いよいよ **divisor / prime descent transition skeleton** じゃ。

つまり状態を自然数に寄せて、

$$
\sigma := \mathbb{N}
$$

index を除去因子または素因子候補として読む段階じゃな。

最小 skeleton はこういう方向になる。

```lean
structure DivisorTransitionKernel where
  index : ℕ → Finset ℕ
  next : ℕ → ℕ → ℕ
  weight : ℕ → ℕ → ℚ
  weight_nonneg : ∀ n q, q ∈ index n → 0 ≤ weight n q
  index_dvd : ∀ n q, q ∈ index n → q ∣ n
  next_eq_div : ∀ n q, q ∈ index n → next n q = n / q
```

ここではまだ $\Lambda$ も $\log$ も要らぬ。
まずは

$$
q\mid n,\qquad next(n,q)=n/q
$$

を Lean に刻む。

その後に、

```lean
PrimeDescentTransitionKernel
PrimePowerTransitionKernel
```

のように分けるのが良い。

## 8. 特におすすめの次 Phase

わっちなら次は **Phase AB: Divisor transition skeleton** として切る。

目的は、

$$
n \xrightarrow{q} n/q
$$

を持つ有限 transition kernel を定義し、`FiniteTransitionKernel` へ忘却できるようにすること。

最初の theorem は軽くてよい。

```lean
def toFiniteTransitionKernel :
  FiniteTransitionKernel ℕ ℕ
```

次に、

```lean
theorem next_dvd_source :
  q ∈ index n → next n q ∣ n
```

または、

```lean
theorem next_eq_div_of_mem :
  q ∈ index n → next n q = n / q
```

を置く。

さらに prime path との接続を見据えるなら、

```lean
theorem primeDescentStep_of_index_prime
```

のような補題は次段でよい。

## 9. 総括

Phase AA は「大きく新しい山を登った」というより、Phase Z の道を **もう片方の稜線にも通した** 段階じゃ。

だが、これは大事じゃよ。

これで、

$$
\text{transition kernel}
$$

が branch/subconservative route と prime/dvd-monotone route の両方に接続された。

山で言えば、同じ分岐所から、宇宙式 Mass 側の道にも、整除単調性側の道にも進めるようになった。
次はいよいよ道標に

$$
n\to n/q
$$

と刻む番じゃな。
