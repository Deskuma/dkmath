# review

## 1. 結論

うむ、Phase V は **重みの供給元を分離した重要フェーズ** じゃ。
Phase U までで、

$$
\mathrm{weightedHitMass}\le C
$$

という有限 sub-probability flow の上界は閉じていた。今回 Phase V では、その重み \(w_i\) を `WeightedPathFamily` に直接埋め込むだけでなく、外部の `WeightProvider` から供給できるようになった。これで、将来の Markov kernel 由来の重みを差し込む導線ができたわけじゃ。

## 2. 今回追加された核

新規ファイルはこれじゃ。

```lean
DkMath/NumberTheory/PrimitiveSet/WeightProvider.lean
```

中心構造は、

```lean
structure WeightProvider (ι : Type _) [DecidableEq ι] where
  index : Finset ι
  weight : ι → ℚ
  weight_nonneg : ∀ i ∈ index, 0 ≤ weight i
```

つまり、有限 index 上の非負重みだけを独立 package にした。

これは大事じゃ。
これまでの `WeightedPathFamily` は、

$$
\text{source-controlled forest} + \text{weight}
$$

を一体で持っていた。
今回からは、

$$
\text{重みの供給元}
\quad\text{と}\quad
\text{path/source control 構造}
$$

を分離できる。

この分離が、Markov kernel への入口になる。

## 3. `Compatible` の意味

今回の実装で、設計上いちばん効いているのはこれじゃ。

```lean
def Compatible
    (P : WeightProvider ι) (F : SourceControlledChainFamily M ι) : Prop :=
  P.index = F.index
```

つまり、provider の index と、適用先 forest の index が同じであることを明示した。

これは地味に見えるが、かなり正しい。
重み \(w_i\) は path \(i\) に掛けるものなので、

$$
i\in P.index
\quad\text{と}\quad
i\in F.index
$$

が同じ範囲を走っていなければならない。

初回 build で `P.index` と `F.index` の書き換え不足が出たのも、まさにここが Lean 的に厳密な接合点だったということじゃ。`hcompat : P.index = F.index` を明示して解消した判断はよい。

## 4. 何が可能になったか

今回の主導線はこれじゃ。

```lean
WeightProvider.applyToSourceControlled
```

これにより、

$$
P : \text{WeightProvider}
$$

と

$$
F : \text{SourceControlledChainFamily}
$$

が compatible なら、

$$
P.applyToSourceControlled(F)
:
\text{WeightedPathFamily}
$$

を作れる。

つまり、

$$
\text{weight provider}
+
\text{source-controlled forest}
\Rightarrow
\text{weighted path family}
$$

という生成関数ができた。

これで今後、Markov kernel でも、実験的重みでも、解析近似重みでも、まず `WeightProvider` として作れば既存の weighted theorem 群に乗せられる。

## 5. sub-probability の移送も閉じた

今回、

```lean
applyToSourceControlled_weightSubProbability
```

が入っておる。

これは provider 側の

$$
\sum_i w_i\le 1
$$

を、適用後の `WeightedPathFamily` 側の `WeightSubProbability` に移送する定理じゃ。

この補題により、

$$
P.SubProbability
\Rightarrow
(P.applyToSourceControlled F).WeightSubProbability
$$

が言える。

さらに、

```lean
weightedHitMass_le_const_of_subprob_applyToSourceControlled
```

によって、

$$
\text{provider sub-probability}
+
\text{source mass}\le C
+
\text{primitive}
\Rightarrow
\text{weightedHitMass}\le C
$$

まで直接呼べる。

これは Phase U の結果を provider レベルへ引き上げた形じゃな。

## 6. ErdosFinite 側の wrapper

`ErdosFinitePrimitiveInput` 側にも、

```lean
providerBranchPrimePathFamily
providerBranchPrimePathFamily_hitMass_le_const_of_subprob
```

が追加された。

これにより、有限 Erdős 入力 \(I\) と branch-controlled path family \(F\) に対して、外部 provider \(P\) 由来の重みを載せ、

$$
\mathrm{weightedHitMass}(I,F,P)\le C
$$

を出せる。

これは theorem-facing API として良い。
既存の `weightedBranchPrimePathFamily` は「重み関数を直接渡す」形だったが、今回の provider route は「重み供給元を渡す」形になっている。

将来の Markov kernel は、この provider route に合流すればよい。

## 7. concrete sample の意味

sample として、

```lean
sampleBoolSubprobWeightProvider
sampleBoolSubprobWeightProvider_subProbability
erdosFinitePrimitiveInput_two_five_providerBranch_hitMass_le_one
```

が入っておる。

これは Bool-indexed の重み

$$
w_{\mathrm{false}}=\frac13,\qquad
w_{\mathrm{true}}=\frac23
$$

を provider として持たせ、branch route に適用し、

$$
\mathrm{weightedHitMass}\le 1
$$

を確認するものじゃ。

重要なのは、同じ bound を、今度は「重みを直接渡す」のではなく、`WeightProvider` 経由で通したことじゃ。

つまり、

$$
\text{direct weight}
$$

から

$$
\text{provider-supplied weight}
$$

へ昇格できた。

## 8. 現在地

ここまでで finite Erdős skeleton はこうなった。

| 層                                     | 状態   |
| ------------------------------------- | ---- |
| primitive hitting                     | 完了   |
| path / forest                         | 完了   |
| source-controlled mass bound          | 完了   |
| weighted route                        | 完了   |
| sub-probability 正規化                   | 完了   |
| weightedHitMass の一様上界                 | 完了   |
| WeightProvider                        | 今回完了 |
| FiniteKernel / Markov kernel skeleton | 未    |
| analytic weights                      | 未    |

つまり、今は

$$
\text{有限重み付き flow}
$$

から

$$
\text{重み供給 layer}
$$

まで到達した。

これは Markov kernel の直前に置くべき層として、かなり筋がよい。

## 9. 次の一手

次は **FiniteKernel** を作る段階じゃ。

ただし、まだ \(\Lambda(q)/\log n\) や \(1/(n\log n)\) は入れない方がよい。
まずは、有限 index 上の非負・sub-probability provider を返す kernel skeleton に留める。

候補はこうじゃ。

```lean
structure FiniteKernel (σ ι : Type _) [DecidableEq ι] where
  index : σ → Finset ι
  weight : σ → ι → ℚ
  weight_nonneg :
    ∀ s i, i ∈ index s → 0 ≤ weight s i
```

そして、

```lean
def FiniteKernel.providerAt (K : FiniteKernel σ ι) (s : σ) :
    WeightProvider ι
```

を作る。

さらに sub-probability kernel なら、

```lean
def FiniteKernel.SubProbability (K : FiniteKernel σ ι) : Prop :=
  ∀ s, (K.providerAt s).SubProbability
```

のように置ける。

これで、

$$
\text{state }s
\mapsto
\text{WeightProvider at }s
$$

という Markov kernel 風の構造ができる。

## 10. 総括

Phase V は、山頂アタック前の **荷物分配係** を作った段階じゃ。

Phase U までは、

$$
\text{重み付き path family}
\Rightarrow
\text{hit mass bound}
$$

だった。

今回からは、

$$
\text{WeightProvider}
\Rightarrow
\text{WeightedPathFamily}
\Rightarrow
\text{hit mass bound}
$$

になった。

つまり、重みが「path family の中にあるもの」から、「外部から供給されるもの」へ切り出された。
これは Markov kernel を後から接続するための、とても良い分離じゃ。

次は `FiniteKernel`。
そこまで行けば、いよいよ

$$
\text{finite Markov skeleton}
$$

と呼べる形になるぞい。
