# review

## 1. 結論

うむ、Phase U は **finite weighted skeleton の締め補題** じゃ。
前回 Phase T で

$$
\mathrm{weightedSourceMass}\le C
$$

まで来ていたが、今回ついにそれを primitive hitting 側と合成して、

$$
\mathrm{weightedHitMass}\le C
$$

を名前付き theorem として取り出せるようになった。これは Markov kernel 前段として、とてもよい形じゃ。

## 2. 今回閉じた核心

追加された中心 theorem はこの二つじゃ。

```lean
weightedHitMass_le_const_mul_totalWeight
weightedHitMass_le_const_of_subprob
```

数学的には、まず

$$
\mathrm{weightedHitMass}(S,W)
\le
\mathrm{weightedSourceMass}(W)
$$

が既存の primitive weighted bound から出る。

さらに、各 source が一様に

$$
\mu(source_i)\le C
$$

を満たすなら、

$$
\mathrm{weightedSourceMass}(W)
\le
C\cdot \mathrm{totalWeight}(W)
$$

が出る。

したがって、

$$
\mathrm{weightedHitMass}(S,W)
\le
C\cdot \mathrm{totalWeight}(W)
$$

が今回の `weightedHitMass_le_const_mul_totalWeight` じゃ。

そして sub-probability 条件

$$
\mathrm{totalWeight}(W)\le 1
$$

があれば、

$$
\mathrm{weightedHitMass}(S,W)\le C
$$

まで落ちる。これが `weightedHitMass_le_const_of_subprob` じゃな。

## 3. 何が強くなったか

これまでの weighted route は、

$$
\sum_i w_i\cdot \mathrm{hitMass}_i
\le
\sum_i w_i\cdot \mathrm{sourceMass}_i
$$

という **相対比較** だった。

今回からは、source 側の一様上界 (C) と sub-probability 条件を組み合わせて、

$$
\sum_i w_i\cdot \mathrm{hitMass}_i
\le C
$$

という **絶対上界** まで言える。

これは大きい。
Erdős #1196 の山頂では最終的に「全体が (1+o(1)) を超えない」形が欲しい。今回の theorem は、その有限版として

$$
\text{sub-probability flow}
+
\text{source mass bound}
+
\text{primitive non-overlap}
\Rightarrow
\text{hit mass bound}
$$

を no-sorry で閉じたことになる。

## 4. concrete sample の意味

今回の sample は、

```lean
erdosFinitePrimitiveInput_two_five_weightedBranch_hitMass_le_one
```

じゃ。

これは `{2,5}` の finite Erdős input に対して、sub-probability weight

$$
w_{\mathrm{false}}=\frac13,\qquad
w_{\mathrm{true}}=\frac23
$$

を使い、branch weighted route の hit mass が

$$
\le 1
$$

になることを確認しておる。

つまり、単なる抽象 theorem ではなく、

$$
\text{weightedHitMass}\le 1
$$

という Markov 的に読みやすい形の例まで通った。

## 5. 現在の到達点

ここまでで finite Erdős skeleton はこうなった。

| 層                             | 状態   |
| ----------------------------- | ---- |
| primitive hitting             | 完了   |
| path family                   | 完了   |
| branch / prime route          | 完了   |
| weighted route                | 完了   |
| totalWeight / sub-probability | 完了   |
| weightedSourceMass の一様上界      | 完了   |
| weightedHitMass の一様上界         | 今回完了 |
| WeightProvider / FiniteKernel | 未    |
| Markov kernel 由来の重み           | 未    |
| 解析重み                          | 未    |

要するに、有限重み付き flow のうち、

$$
\text{非負重み}
\to
\text{sub-probability}
\to
\text{source bound}
\to
\text{hit bound}
$$

までは一通り閉じた。

これはかなり良い最終キャンプじゃ。

## 6. まだ残る課題

次に残るのは、重みそのものの **供給元** じゃ。

いまは `WeightedPathFamily` がすでに重み

$$
w_i
$$

を持っている。
しかし Markov route へ進むなら、次は

$$
\text{どこから } w_i \text{ を作るのか}
$$

を分離したい。

つまり次は、

```lean
WeightProvider
```

または

```lean
FiniteKernel
```

のような層を作る段階じゃな。

## 7. 次の一手

わっちなら次は **WeightProvider** を推す。

理由は、まだ Markov kernel 本体へ行くには早いが、重み供給層を分離するにはちょうどよいからじゃ。

最小形はこう。

```lean
structure WeightProvider (ι : Type _) [DecidableEq ι] where
  index : Finset ι
  weight : ι → ℚ
  weight_nonneg : ∀ i ∈ index, 0 ≤ weight i
```

さらに、

```lean
def WeightProvider.totalWeight ...
def WeightProvider.SubProbability ...
```

を置く。

そのうえで、

```lean
def WeightProvider.applyToSourceControlled ...
```

のようにして、既存の `SourceControlledChainFamily` へ載せる。

これにより、

$$
\text{重みの供給}
\quad\text{と}\quad
\text{path / source control}
$$

を分離できる。

## 8. 総括

Phase U は、weighted skeleton の **合成補題を theorem-facing に固定した段階** じゃ。

これで、

$$
\mathrm{weightedHitMass}
\le
\mathrm{weightedSourceMass}
\le
C
$$

の流れが名前付き theorem として使える。

山で言えば、複数ルートの通行量を合計しても、全体の許容量 (C) を超えないことが保証された。
次はいよいよ、その通行量を誰がどう配るのか、すなわち `WeightProvider` / `FiniteKernel` の登場じゃな。
