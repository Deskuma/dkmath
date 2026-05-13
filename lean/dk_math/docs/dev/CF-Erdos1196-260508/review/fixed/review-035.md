# review

## 1. 結論

うむ、Phase AJ は **prime-power channel provider の package 化** で間違いない。
今回で、

$$
\text{prime-power channel kernel}
+
\text{sub-probability normalization}
$$

を `PrimePowerChannelProvider` として一つの theorem-facing 入力にまとめられた。これにより、後続の finite toy weight / von-Mangoldt-like weight 層では、毎回 `kernel.SubProbability` を別仮定で渡さずに、provider package そのものを受け取ればよくなった。実装・build・no-sorry 検査も通っておる。

## 2. 今回の主役

今回追加された構造はこれじゃ。

```lean
structure PrimePowerChannelProvider where
  kernel : PrimePowerDivisorTransitionKernel
  subprob : kernel.SubProbability
```

数学的には、

$$
\mathrm{P.kernel}
$$

が「index が prime-power label だけから成る divisor transition kernel」であり、

$$
\mathrm{P.subprob}
$$

が「各状態で重み総量が $1$ 以下」という正規化条件じゃ。

つまり、

$$
\forall n,\quad
\sum_{q\in \text{index}(n)} w(n,q)\le 1
$$

を channel package の中に持てる。

これはかなり良い。
Phase AI では `channelProviderAt` という入口名だけだった。Phase AJ では、その入口に **sub-probability 証明込みの受付係** が付いた。

## 3. API として何が使いやすくなったか

今回、`PrimePowerChannelProvider` namespace に次が追加されている。

```lean
providerAt
channelProviderAt
providerAt_subProbability
channelProviderAt_subProbability
applyAtToSourceControlled
weightedHitMass_le_const_applyAtToSourceControlled
```

特に大事なのは、

```lean
weightedHitMass_le_const_applyAtToSourceControlled
```

じゃ。

これにより、

$$
P : \mathrm{PrimePowerChannelProvider}
$$

を持っていれば、別途

$$
hT : \mathrm{P.kernel.SubProbability}
$$

を渡さなくても、

$$
\mathrm{weightedHitMass}\le C
$$

へ進める。

定理の読みはこうじゃ。

$$
\mathrm{P.kernel.CompatibleAt}(n,F)
$$

$$
S\text{ primitive}
$$

$$
\forall q\in \text{F.index},\quad \mu(F.source(q))\le C
$$

なら、

$$
(\mathrm{P.applyAtToSourceControlled}(n,F)).\mathrm{weightedHitMass}(S)\le C
$$

が出る。

つまり、prime-power channel 側の theorem 文がかなり軽くなった。

## 4. sample の意味

今回の sample は、

```lean
sampleTenPrimePowerChannelProvider
sampleTenPrimePowerChannelProvider_channelProviderAt_subProbability
```

じゃ。

これは既存の

$$
10\xrightarrow{2}5,\qquad 10\xrightarrow{5}2
$$

という sample prime-power divisor transition kernel を、sub-probability 証明と一緒に package 化している。

状態 $10$ では、

$$
w(10,2)=\frac12,\qquad w(10,5)=\frac12
$$

なので総量は $1$。それ以外の状態では index が空なので、全状態で sub-probability が成立する。

sample で `channelProviderAt_subProbability` まで確認されているので、今後の toy weight / channel weight の試験台としても使いやすい。

## 5. 現在地

ここまでの階層はかなり整った。

| 層                                      | 状態   |
| -------------------------------------- | ---- |
| `DivisorTransitionKernel`              | 完了   |
| $n\to n/q$ semantics                   | 完了   |
| prime label / prime-power label bridge | 完了   |
| `IsPrimePowerLabel`                    | 完了   |
| `PrimePowerIndexed`                    | 完了   |
| `PrimePowerDivisorTransitionKernel`    | 完了   |
| `channelProviderAt`                    | 完了   |
| `PrimePowerChannelProvider`            | 今回完了 |
| finite toy weight layer                | 未    |
| von-Mangoldt-like weight               | 未    |
| analytic $\Lambda(q)/\log n$           | 未    |

いまは、素冪専用 route に **通行証** と **通行量の正規化** が揃った状態じゃ。

## 6. 何がまだ足りないか

まだ重みそのものは本物の von Mangoldt ではない。

今あるのは、

$$
w(n,q)\ge 0,\qquad
\sum_q w(n,q)\le 1
$$

という有限 skeleton じゃ。

次に必要なのは、

$$
q=p^k
$$

という prime-power channel 上で、「どのような toy weight を載せるか」を theorem-facing に扱う層じゃ。

ここで焦って

$$
\Lambda(q),\quad \log n
$$

を入れると重くなる。
まずは有理値の finite toy weight でよい。

## 7. 次の一手

次は **PrimePowerChannelProvider を入力にした finite toy weight layer** が自然じゃ。

ただし、既に `PrimePowerChannelProvider` は `kernel` の `weight` を持っているので、最初は重い構造体を増やすより、constructor / wrapper を足すのがよいと思う。

候補はこうじゃ。

```lean
def PrimePowerChannelProvider.ofKernel
    (T : PrimePowerDivisorTransitionKernel)
    (hT : T.SubProbability) :
    PrimePowerChannelProvider :=
  { kernel := T
    subprob := hT }
```

これは単純だが、後続で

```lean
PrimePowerChannelProvider.ofToyWeight
PrimePowerChannelProvider.ofVonMangoldtLikeWeight
```

のような constructor を増やす時の命名規則になる。

もう一段進めるなら、

```lean
def PrimePowerDivisorTransitionKernel.withWeight
    (T : PrimePowerDivisorTransitionKernel)
    (w : ℕ → ℕ → ℚ)
    (hw : ∀ n q, q ∈ T.toDivisorTransitionKernel.index n → 0 ≤ w n q) :
    PrimePowerDivisorTransitionKernel
```

のように、既存 kernel の index/next/prime-power 性を保ったまま weight だけ差し替える API が欲しくなる。

ただしこれは少し重い。次の一手としては、まず `ofKernel` と sample alias の整理が安全じゃな。

## 8. 総括

Phase AJ は、素冪専用 route の **受付カウンター完成** じゃ。

これで後続は、

```lean
P : PrimePowerChannelProvider
```

を受け取るだけで、

* prime-power channel であること
* sub-probability であること
* state ごとの provider を取り出せること
* weighted hit mass bound へ進めること

をまとめて使える。

山で言えば、素冪専用ルートに正式な受付小屋が建ち、通行証と通行量管理が一体化した。
次は、その受付で扱う **有限 toy 通行料** を設計する番じゃ。
