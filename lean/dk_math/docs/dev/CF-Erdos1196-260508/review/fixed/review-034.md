# review

## 1. 結論

うむ、Phase AI は **prime-power channel の入口名を固定した段階** じゃ。
今回の実装は、数学的に新しい重みを入れたというより、今後の finite toy weight / von-Mangoldt-like weight を差し込むための **theorem-facing entry point** を作ったものじゃな。`channelProviderAt` は現時点では `providerAt` の薄い alias だが、この名前を先に立てたのはよい判断じゃ。

## 2. 今回の主役

追加された中心 API はこれじゃ。

```lean
PrimePowerDivisorTransitionKernel.channelProviderAt
PrimePowerDivisorTransitionKernel.channelProviderAt_subProbability
PrimePowerDivisorTransitionKernel.channelWeightedHitMass_le_const_of_subprob
```

特に、

```lean
def channelProviderAt (T : PrimePowerDivisorTransitionKernel) (n : ℕ) :
    WeightProvider ℕ :=
  T.providerAt n
```

が今回の核じゃ。

いまは単なる alias だが、意味としては、

$$
n
\mapsto
\text{prime-power channel 上の weight provider}
$$

という名前を得たことになる。

これは後で、

$$
w(n,q)\approx \frac{\Lambda(q)}{\log n}
$$

に寄せるときの差し込み口になる。

## 3. 何が良くなったか

これまでは `PrimePowerDivisorTransitionKernel` から重みを取り出すとき、単に `providerAt` だった。

しかし `providerAt` は一般的すぎる。
それが prime-power channel 由来なのか、単なる有限 kernel 由来なのかが名前から見えにくい。

今回 `channelProviderAt` という名前ができたことで、

$$
\text{prime-power channel}
\to
\text{weight provider}
\to
\text{weighted hit mass bound}
$$

という意味が theorem 名から読めるようになった。

これは DkMath の設計としてかなり大事じゃ。
後で重み層が増えたとき、名前が意味を持っていないと API がすぐ迷路になるからの。

## 4. bound への導線も整理された

今回の

```lean
channelWeightedHitMass_le_const_of_subprob
```

により、prime-power channel 名の下で、

$$
\mathrm{weightedHitMass}\le C
$$

を直接呼べる。

中身は既存の

```lean
weightedHitMass_le_const_of_subprob_applyAtToSourceControlled
```

を呼ぶ alias じゃが、名前が重要じゃ。

数式としては、

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
\forall q\in F.index,\quad \mu(F.source(q))\le C
$$

から、

$$
\mathrm{weightedHitMass}(S)\le C
$$

が出る。

つまり、prime-power channel route でも、既存の finite weighted skeleton に自然に乗れる。

## 5. sample の意味

追加された sample は、

```lean
sampleTenPrimePowerDivisorTransitionKernel_channelProviderAt_subProbability
```

じゃ。

これは、既存の sample kernel が state $n$ ごとに sub-probability channel provider を出すことを確認している。

具体的には、状態 $10$ では labels $2,5$ に重みが乗り、

$$
\frac12+\frac12=1
$$

それ以外では空 index なので、全状態で sub-probability になる。

この sample は小さいが、今後の toy channel weight の試験台としてよい。

## 6. 現在地

ここまでで prime-power channel route は、こういう段階まで来た。

| 層                                   | 状態   |
| ----------------------------------- | ---- |
| `DivisorTransitionKernel`           | 完了   |
| `PrimePowerDivisorTransitionKernel` | 完了   |
| prime-power label → descent         | 完了   |
| prime-power indexed channel         | 完了   |
| prime-power channel weighted route  | 完了   |
| `channelProviderAt` entry point     | 今回完了 |
| channel provider package            | 未    |
| finite toy weight                   | 未    |
| von-Mangoldt-like weight            | 未    |
| analytic weight                     | 未    |

つまり、まだ本物の $\Lambda(q)$ ではないが、 $\Lambda(q)$ を載せる **席** はできてきた。

## 7. 次の一手

次は History にある通り、`PrimePowerChannelProvider` のような package を作るか判断する段階じゃ。

わっちなら次は **薄い構造体化** を推す。

候補はこうじゃ。

```lean
structure PrimePowerChannelProvider where
  kernel : PrimePowerDivisorTransitionKernel
  subprob : kernel.SubProbability
```

これで、

$$
\text{prime-power channel kernel}
+
\text{sub-probability}
$$

を一つの入力として扱える。

さらに、

```lean
def providerAt (P : PrimePowerChannelProvider) (n : ℕ) :
    WeightProvider ℕ :=
  P.kernel.channelProviderAt n
```

を置けば、後続 theorem が軽くなる。

## 8. その次に見えるもの

`PrimePowerChannelProvider` ができたら、次に finite toy weight じゃ。

ただし、まだ実数対数や $\Lambda$ 本体には入らない方がよい。

まずは、例えば次のような **有限 toy weight** でよい。

$$
q\in index(n)
\Rightarrow
w(n,q)\ge 0
$$

$$
\sum_{q\in index(n)} w(n,q)\le 1
$$

そして prime-power channel 上だけで動く。

本物の von Mangoldt 的構造へは、その後に

$$
q=p^k
\Rightarrow
\text{weight depends on }p
$$

を足していけばよい。

## 9. 総括

Phase AI は、素冪専用ルートに **料金所の名前** を付けた段階じゃ。

現時点では `channelProviderAt` は `providerAt` と同じもの。
だが、この名前があることで、後続の finite toy weight や von-Mangoldt-like weight は、同じ入口へ自然に差し替えられる。

山で言えば、素冪専用ルートに「prime-power channel provider」という看板が立った。
次は、その看板の下に **通行証と通行量をまとめた受付** 、つまり `PrimePowerChannelProvider` を作るのがよさそうじゃ。
