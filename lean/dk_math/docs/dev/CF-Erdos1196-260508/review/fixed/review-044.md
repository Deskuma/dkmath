# review

## 1. 結論

うむ、Phase AS は **prime witness dependent weight から provider への直結化** じゃ。
Phase AR で、

$$
w(n,q)=c(n,p)
$$

という形で、prime-power witness の base prime $p$ に依存する toy weight を表現できるようになった。今回 Phase AS では、それをさらに

$$
\mathrm{PrimeWitnessDependentWeight}
\to
\mathrm{VonMangoldtLikeWeight}
\to
\mathrm{withWeight}
\to
\mathrm{PrimePowerChannelProvider}
$$

へ一発で流す constructor が追加された。これはかなり良い接続じゃ。

## 2. 今回の主役

追加された中心 API はこれじゃ。

```lean
def PrimePowerChannelProvider.ofPrimeWitnessDependentWeight
```

入力は、

```lean
T : PrimePowerDivisorTransitionKernel
w c : ℕ → ℕ → ℚ
hw : T.PrimeWitnessDependentWeight w c
hw_subprob : ...
```

で、出力は

```lean
PrimePowerChannelProvider
```

じゃ。

数学的には、

$$
q=p^k,\qquad w(n,q)=c(n,p),\qquad 0\le w(n,q)
$$

という witness-dependent な有限重みを、sub-probability 条件つきで channel provider に package 化する。

つまり、いよいよ

$$
\text{base prime }p\text{ 由来の重み}
$$

が provider の本線に入ったわけじゃな。

## 3. 何が強くなったか

前回までは、`PrimeWitnessDependentWeight` を得ても、いったん

```lean
T.vonMangoldtLikeWeight_of_primeWitnessDependent hw
```

で `VonMangoldtLikeWeight` へ変換し、それをさらに `ofVonMangoldtLikeWeight` に渡す、という二段構えだった。

今回からは、

```lean
PrimePowerChannelProvider.ofPrimeWitnessDependentWeight
```

を呼べばよい。

構造としては同じでも、API としては大きい。
後続で「この weight は $p$ に依存している」と言いたい場合、constructor 名そのものが意味を持つようになった。

## 4. simp API も整っている

今回追加された simp 補題も重要じゃ。

```lean
ofPrimeWitnessDependentWeight_kernel
ofPrimeWitnessDependentWeight_channelProviderAt_index
ofPrimeWitnessDependentWeight_channelProviderAt_weight
```

これにより、constructor で作った provider から、

$$
kernel = T.withWeight(w)
$$

$$
channelProviderAt(n).\text{index} = \text{T.index}(n)
$$

$$
channelProviderAt(n).\text{weight} = w(n)
$$

を自然に取り出せる。

これは今後、具体的な theorem を書く時に効く。
特に weight が本当に $w$ として見えることは、後で「これは $c(n,p)$ に由来する」と展開するための足場になる。

## 5. sample の格上げ

`sampleTenToyWeightChannelProvider` が、今回から

```lean
ofPrimeWitnessDependentWeight
```

経由に切り替わった。

これにより、sample は単なる toy weight でも、単なる von-Mangoldt-like weight でもなく、

$$
w(n,q)=c(n,p)
$$

と説明できる **prime witness dependent toy weight** として provider 化された。

つまり sample の意味が一段上がった。
以前は「この料金表は非負で素冪上にある」だった。
今は「この料金表は prime base $p$ に依存して説明できる」と言える。

## 6. 現在地

ここまでの階層はこうじゃ。

| 層                                           | 状態   |
| ------------------------------------------- | ---- |
| `PrimePowerDivisorTransitionKernel`         | 完了   |
| `PrimePowerChannelProvider`                 | 完了   |
| `VonMangoldtLikeWeight`                     | 完了   |
| `ofVonMangoldtLikeWeight`                   | 完了   |
| `PrimeWitnessDependentWeight`               | 完了   |
| `ofPrimeWitnessDependentWeight`             | 今回完了 |
| witness-dependent sample provider           | 今回完了 |
| witness-dependent concrete hit mass theorem | 未    |
| `PrimePowerLabel` 構造体化                      | 未    |
| analytic $\Lambda(q)/\log n$                | 未    |

かなり登ったのぅ。
いまは、本物の $\log p$ には入っていないが、「 $p$ に依存する weight を provider にする」までは閉じた。

## 7. 次の一手

次は History にある通り、 **PrimeWitnessDependentWeight route を使った concrete weighted hit mass theorem** が自然じゃ。

既に Phase AM で toy weight の hit mass bound は通っている。
しかし今回 constructor が変わったので、次はこの新 route 名で、

```lean
sampleTenToyWeightChannelProvider_hitMass_le_one
```

相当の theorem が、`ofPrimeWitnessDependentWeight` 由来 provider として読めることを整理するのがよい。

もし既存 theorem がそのまま通るなら、名前付き alias を追加するだけでも価値がある。

候補名は、

```lean
sampleTenPrimeWitnessDependentWeight_hitMass_le_one
```

のようなものじゃな。

## 8. その次の分岐

その後は大きな分岐じゃ。

短期的には、まだ

$$
q:\mathbb{N}
$$

label のまま、predicate route を続けるのが軽い。

長期的には、

```lean
structure PrimePowerLabel where
  q : ℕ
  p : ℕ
  k : ℕ
  prime : Nat.Prime p
  k_pos : 0 < k
  eq_pow : q = p ^ k
```

のように label を構造体化すると、本物の

$$
\Lambda(q)=\log p
$$

へ進みやすくなる。

ただし、今すぐ構造体化すると既存の `DivisorTransitionKernel` の label $q:\mathbb{N}$ 路線に大きく影響する。
まずは predicate route で concrete bound をもう少し固めるのが賢い。

## 9. 総括

Phase AS は、素冪由来の料金表を **base prime 依存の正式フォーム** として受付に通した段階じゃ。

これで、

$$
w(n,q)=c(n,p)
$$

という有限 toy 版の von-Mangoldt 的構造が、

$$
PrimePowerChannelProvider
$$

までつながった。

山で言えば、前回は「この料金は base prime $p$ によって決まる」と説明できた。
今回、その説明書付きの料金表を正式に受付へ提出できるようになった。
次は、その料金表で実際に

$$
\mathrm{weightedHitMass}\le 1
$$

を通す看板を整える番じゃな。
