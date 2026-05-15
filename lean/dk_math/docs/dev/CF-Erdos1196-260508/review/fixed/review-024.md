# review

## 1. 結論

うむ、Phase Y は **FiniteKernel 周辺の道標整備** じゃ。
Phase W/X で finite kernel route は branch/subconservative 側と prime/dvd-monotone 側の両方に接続された。今回 Phase Y では、その接続で毎回出ていた長い仮定

```lean
(K.providerAt s).Compatible F
```

を、

```lean
K.CompatibleAt s F
```

として扱えるようにした。これは actual finite Markov transition skeleton へ進む前の、かなり良い整地じゃ。

## 2. 今回追加された核

今回の追加は主にこのあたりじゃ。

```lean
providerAt_index
providerAt_weight
CompatibleAt
compatibleAt_iff_index_eq
applyAtToSourceControlledOfCompatibleAt
applyAtToSourceControlledOfCompatibleAt_index
weightedHitMass_le_const_of_subprob_applyAtToSourceControlledOfCompatibleAt
```

数学的には、互換性条件を

$$
K.\mathrm{CompatibleAt}(s,F)
$$

と書けるようにし、その中身が

$$
\text{K.index}(s)=\text{F.index}
$$

であることを `compatibleAt_iff_index_eq` で明示した、ということじゃ。

これは小さいようで大きい。
次に状態 $n$ と index $q$ に意味を持たせるとき、毎回 `providerAt` を展開しながら index 一致を証明するのは読みにくい。今回の alias により、 theorem 文がかなり軽くなる。

## 3. 何が良くなったか

これまでの構造は、

$$
\text{state}
\to
\text{WeightProvider}
\to
\text{WeightedPathFamily}
\to
\mathrm{weightedHitMass}\le C
$$

じゃった。

ただし、`WeightProvider` と `SourceControlledChainFamily` を接続するたびに、

$$
(K.providerAt(s)).\text{index} = \text{F.index}
$$

を Lean に納得させる必要があった。

今回からは、

$$
K.CompatibleAt(s,F)
$$

で済む。

さらに、

```lean
applyAtToSourceControlledOfCompatibleAt
```

により、`CompatibleAt` を使ってそのまま `WeightedPathFamily` を生成できる。

つまり、kernel を使う側の API が、

```lean
providerAt を展開して Compatible を渡す
```

から、

```lean
CompatibleAt を渡す
```

へ整理されたわけじゃな。

## 4. theorem-facing bound も alias 化された

今回、

```lean
weightedHitMass_le_const_of_subprob_applyAtToSourceControlledOfCompatibleAt
```

も入った。

これにより、

$$
K\text{ が sub-probability kernel}
$$

$$
K.CompatibleAt(s,F)
$$

$$
S\text{ primitive}
$$

$$
\forall i\in \text{F.index},\quad \mu(F.source_i)\le C
$$

から、

$$
\mathrm{weightedHitMass}(S)\le C
$$

を直接呼べる。

つまり、Phase W の主定理を、より短い compatibility API で再利用できるようになった。
これは今後かなり効くぞい。

## 5. 現在地

ここまでで finite kernel 周辺はこうなった。

| 層                           | 状態           |
| --------------------------- | ------------ |
| `WeightProvider`            | 完了           |
| `FiniteKernel`              | 完了           |
| kernel branch route         | 完了           |
| kernel prime route          | 完了           |
| compatibility alias         | 今回完了         |
| kernel theorem-facing bound | 今回 alias 版完了 |
| actual transition skeleton  | 未            |
| analytic weight             | 未            |

つまり、finite kernel はもうかなり **API として使える形** になった。

## 6. 次の一手

次は、History にもある通り、いよいよ actual finite Markov transition skeleton じゃな。

ただし、まだ解析重み

$$
\frac{\Lambda(q)}{\log n}
$$

は入れなくてよい。

まずは有限遷移の形だけを定義するのがよい。

候補はこうじゃ。

```lean
structure FiniteTransitionKernel (σ ι : Type _) [DecidableEq ι] where
  index : σ → Finset ι
  next : σ → ι → σ
  weight : σ → ι → ℚ
  weight_nonneg : ∀ s i, i ∈ index s → 0 ≤ weight s i
```

そして既存の `FiniteKernel` へ忘却する。

```lean
def FiniteTransitionKernel.toFiniteKernel :
    FiniteKernel σ ι
```

この形にすると、

$$
s \xrightarrow{i} next(s,i)
$$

という「遷移先」を持ちながら、重み評価は既存の `FiniteKernel` へ流せる。

## 7. Erdős #1196 に寄せるなら

Erdős ルートへ寄せるなら、後で

$$
\sigma := \mathbb{N}
$$

$$
\iota := \text{除去因子 } q
$$

として、

$$
next(n,q)=\frac{n}{q}
$$

を入れる。

ただし最初は `q ∣ n` や素冪条件を深く入れず、有限 index 上の `next` を持つ抽象 skeleton でよい。

その後に、

```lean
DivisorTransitionKernel
PrimeDescentTransitionKernel
PrimePowerTransitionKernel
```

のように具体化していくのが安全じゃ。

## 8. 総括

Phase Y は、派手な山頂アタックではないが、登山道の標識を整理した大事な回じゃ。

$$
(K.providerAt s).Compatible F
$$

という長い道案内を、

$$
K.CompatibleAt(s,F)
$$

に圧縮し、その中身が

$$
\text{K.index}(s)=\text{F.index}
$$

であることも明示できるようになった。

山で言えば、配給所 `FiniteKernel` と登山道 `SourceControlledChainFamily` の接続口に、正式な案内板が立った。
次はいよいよ、状態 $n$、除去因子 $q$、遷移先 $n/q$ を持つ actual finite Markov transition skeleton へ進める段階じゃ。
