# review

## 1. 結論

うむ、Phase AH は **prime-power channel 型を weighted route に接続した段階** じゃ。
Phase AG で `PrimePowerDivisorTransitionKernel` ができ、「この divisor transition kernel の index は prime-power label だけ」という条件を型として持てるようになった。今回 Phase AH では、その型から既存の `WeightedPathFamily` / hit mass bound へ直接入れる theorem-facing API が整った。これは、von Mangoldt-like weight を載せる前のかなり良い橋じゃ。

## 2. 今回追加された核

今回の中心はこのあたりじゃ。

```lean
PrimePowerDivisorTransitionKernel.compatibleAt_iff_index_eq
PrimePowerDivisorTransitionKernel.providerAt_subProbability
PrimePowerDivisorTransitionKernel.applyAtToSourceControlled
PrimePowerDivisorTransitionKernel.weightedHitMass_le_const_of_subprob_applyAtToSourceControlled
```

特に重要なのは、

```lean
weightedHitMass_le_const_of_subprob_applyAtToSourceControlled
```

じゃな。

これは、prime-power channel 条件を型として持つ kernel $T$ について、

$$
T\text{ sub-probability}
$$

$$
T.CompatibleAt(n,F)
$$

$$
S\text{ primitive}
$$

$$
\forall q\in \text{F.index},\quad \mu(F.source(q))\le C
$$

から、

$$
\mathrm{weightedHitMass}(S)\le C
$$

を直接出す theorem じゃ。

つまり、

$$
\text{PrimePowerDivisorTransitionKernel}
\to
\text{WeightedPathFamily}
\to
\mathrm{weightedHitMass}\le C
$$

の導線が、専用 API として読めるようになった。

## 3. 何が強くなったか

Phase AG では、

$$
q\in \text{index}(n)
\Rightarrow
q\text{ is prime-power}
\Rightarrow
n\to n/q\text{ is prime-power descent}
$$

が型から言えるようになった。

今回 Phase AH では、それに加えて、

$$
\text{prime-power channel kernel}
+
\text{sub-probability weight}
\Rightarrow
\text{weighted hit mass bound}
$$

まで直接進めるようになった。

これは「素冪 label の意味論」と「重み付き hitting bound」が合流したということじゃ。
まだ $\Lambda(q)$ はない。まだ $\log n$ もない。
しかし、 $\Lambda(q)$ が乗るべき素冪 channel から、既存の mass bound へ入る道は開通した。

## 4. compatibility API の意味

今回、

```lean
compatibleAt_iff_index_eq
```

も追加された。

これは、

$$
T.CompatibleAt(n,F)
\Longleftrightarrow
T.toDivisorTransitionKernel.\text{index}(n)=\text{F.index}
$$

という中身を明示するものじゃ。

ここは地味だが重要じゃ。
prime-power kernel の index と source-controlled family の index が一致することを、今後 theorem 文で扱いやすくする。実際、これから weight provider や channel weight を作ると、compatibility 条件は頻出するはずじゃからの。

## 5. sample の意味

今回の sample は、

```lean
sampleTenPrimePowerDivisorTransitionKernel_subProbability
```

じゃ。

これは、既存の

$$
10\xrightarrow{2}5,\qquad 10\xrightarrow{5}2
$$

を持つ sample kernel が、prime-power channel package としても sub-probability normalized であることを確認している。

この sample は小さいが意味は大きい。

$$
2=2^1,\qquad 5=5^1
$$

という素冪 channel だけを持ち、重みも

$$
\frac12+\frac12=1
$$

に正規化されている。
つまり、今後の finite toy von-Mangoldt route の最小モデルとして使える。

## 6. 現在地

ここまでの構造はこうじゃ。

| 層                                    | 状態   |
| ------------------------------------ | ---- |
| `FiniteTransitionKernel`             | 完了   |
| `DivisorTransitionKernel`            | 完了   |
| $n\to n/q$                           | 完了   |
| prime label bridge                   | 完了   |
| prime-power label bridge             | 完了   |
| `IsPrimePowerLabel`                  | 完了   |
| `PrimePowerIndexed`                  | 完了   |
| `PrimePowerDivisorTransitionKernel`  | 完了   |
| prime-power channel weighted route   | 今回完了 |
| finite toy weight / channel provider | 未    |
| von Mangoldt-like weight             | 未    |
| analytic weight                      | 未    |

つまり、prime-power channel の **型** と **weighted route** は揃った。
次は、そこにどんな重みを載せるかじゃ。

## 7. 次の一手

次は **finite toy weight / channel weight provider** が自然じゃ。

本物の

$$
w(n,q)=\frac{\Lambda(q)}{\log n}
$$

へ行く前に、まず prime-power channel 上で非負重みを供給する有限 skeleton を作るのがよい。

たとえば、最小ならこういう方向じゃ。

```lean
def PrimePowerChannelWeightProvider
    (T : PrimePowerDivisorTransitionKernel) (n : ℕ) :
    WeightProvider ℕ :=
  T.providerAt n
```

これは単なる alias に近いが、名前として

```lean
PrimePowerChannelWeightProvider
```

を立てる意味はある。

もう少し進めるなら、

```lean
structure PrimePowerChannelProvider where
  kernel : PrimePowerDivisorTransitionKernel
  subprob : kernel.SubProbability
```

のようにして、prime-power channel と sub-probability を package 化するのもよい。

ただし、わっちのおすすめは、まず薄く行くことじゃ。

## 8. Phase AI 案

次はこう切るとよい。

**Phase AI: Prime-power channel weight provider**

目的:

$$
\text{PrimePowerDivisorTransitionKernel}
$$

から、state $n$ ごとの prime-power channel weight provider を theorem-facing に取り出す。

最低限ほしいものは、

```lean
def PrimePowerDivisorTransitionKernel.channelProviderAt
    (T : PrimePowerDivisorTransitionKernel) (n : ℕ) :
    WeightProvider ℕ :=
  T.providerAt n
```

```lean
theorem PrimePowerDivisorTransitionKernel.channelProviderAt_subProbability
    (T : PrimePowerDivisorTransitionKernel)
    (hT : T.SubProbability) (n : ℕ) :
    (T.channelProviderAt n).SubProbability
```

さらに、

```lean
theorem PrimePowerDivisorTransitionKernel.channel_weightedHitMass_le_const
```

のような alias を置く。

これで後で von Mangoldt-like weight に差し替えるときも、

$$
\text{channelProviderAt}
$$

という名前の下に統一できる。

## 9. 注意点

今はまだ、`weight` が「prime-power label のときだけ非零」とは明示していない。

ただし `PrimePowerDivisorTransitionKernel` では、そもそも index に入る label がすべて prime-power なので、現行の有限和は index 上だけを走る限り問題ない。
index 外の weight を 0 とする support 条件は、後で必要になってからでよい。

今の設計では、

$$
q\in \text{index}(n)
$$

を持つものだけが channel に参加する。
ゆえに、まずは index 内の重みだけを扱えば十分じゃ。

## 10. 総括

Phase AH は、素冪専用ルートを **weighted mass bound の本線** に接続した回じゃ。

これで、

$$
\text{prime-power channel}
+
\text{sub-probability}
+
\text{source bound}
\Rightarrow
\mathrm{weightedHitMass}\le C
$$

が直接読める。

山で言えば、前回は「素冪専用ルート」が地図に登録された。
今回、そのルートに料金所と通行量の管理が付き、既存の mass bound の道へ合流した。

次は、いよいよその料金所に **有限 toy weight** を載せる段階じゃな。
