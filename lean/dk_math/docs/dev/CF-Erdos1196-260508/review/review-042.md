# review

## 1. 結論

うむ、Phase AQ は **von-Mangoldt-like weight を provider 化する正式入口の完成** じゃ。
Phase AP で `VonMangoldtLikeWeight` という性格札を作り、Phase AN/AO で任意 weight を `PrimePowerChannelProvider` に載せる constructor と simp API を整えた。今回 Phase AQ では、その二つが合流し、

$$
\text{VonMangoldtLikeWeight}
\to
\text{withWeight}
\to
\text{PrimePowerChannelProvider}
\to
\text{weightedHitMass bound}
$$

が `ofVonMangoldtLikeWeight` という一つの constructor でつながった。これはかなり良い区切りじゃ。

## 2. 今回の主役

中心 API はこれじゃ。

```lean
def ofVonMangoldtLikeWeight
    (T : PrimePowerDivisorTransitionKernel)
    (w : ℕ → ℕ → ℚ)
    (hw : T.VonMangoldtLikeWeight w)
    (hw_subprob :
      (T.withWeight w (T.vonMangoldtLikeWeight_nonneg hw)).SubProbability) :
    PrimePowerChannelProvider :=
  ofKernelWithWeight T w (T.vonMangoldtLikeWeight_nonneg hw) hw_subprob
```

数学的には、

$$
w
$$

が prime-power witness と非負性を持つ有限 von-Mangoldt-like weight であり、さらにその重み付き kernel が sub-probability なら、

$$
\text{PrimePowerChannelProvider}
$$

を作れる、というものじゃ。

以前は `ofKernelWithWeight` に渡すために非負性を別途取り出して渡す必要があった。
今回からは、

$$
hw : T.VonMangoldtLikeWeight(w)
$$

から `T.vonMangoldtLikeWeight_nonneg hw` を内部で使う。これで theorem 側の入力がかなり意味論寄りになった。

## 3. 何が強くなったか

Phase AN の `ofKernelWithWeight` は一般 weight constructor じゃった。
つまり、

$$
0\le w(n,q)
$$

と sub-probability があれば provider 化できた。

Phase AQ の `ofVonMangoldtLikeWeight` は、その上位入口じゃ。

$$
q=p^k
$$

という prime-power witness を持つことと、

$$
0\le w(n,q)
$$

を `VonMangoldtLikeWeight` としてまとめ、その predicate から provider 化する。

つまり、今後は単なる非負 weight ではなく、

$$
\text{prime-power channel 由来の weight}
$$

として登録できるようになった。これは \(\Lambda(q)\) へ進むための名前空間として、かなり重要じゃ。

## 4. simp API も揃っている

今回追加された simp 補題も良い。

```lean
ofVonMangoldtLikeWeight_kernel
ofVonMangoldtLikeWeight_channelProviderAt_index
ofVonMangoldtLikeWeight_channelProviderAt_weight
```

これで、`ofVonMangoldtLikeWeight` で作った provider に対して、

$$
kernel = T.withWeight(w)
$$

$$
channelProviderAt(n).index = T.index(n)
$$

$$
channelProviderAt(n).weight = w(n)
$$

が取り出しやすくなった。

これは次の段階で効く。
特に witness-dependent な weight を設計するとき、provider 化したあとに「本当にこの provider の weight は定義した \(w\) なのか」を `simp` で見えるようにしておくのは大事じゃ。

## 5. sample の切り替えも意味がある

`sampleTenToyWeightChannelProvider` が、以前の

```lean
ofKernelWithWeight
```

経由から、

```lean
ofVonMangoldtLikeWeight
```

経由に切り替わった。

これは良い。
`sampleTenToyWeight` は単なる toy weight ではなく、

```lean
sampleTenToyWeight_vonMangoldtLikeWeight
```

を持つ weight として扱われるようになった。

つまり sample でも、

$$
\text{toy weight}
$$

から

$$
\text{von-Mangoldt-like toy weight}
$$

へ格上げされたわけじゃな。

## 6. 現在地

ここまでの階層はこうじゃ。

| 層                                   | 状態   |
| ----------------------------------- | ---- |
| prime-power channel                 | 完了   |
| `PrimePowerChannelProvider`         | 完了   |
| `withWeight`                        | 完了   |
| `ofKernelWithWeight`                | 完了   |
| `VonMangoldtLikeWeight` predicate   | 完了   |
| `ofVonMangoldtLikeWeight`           | 今回完了 |
| von-Mangoldt-like provider simp API | 今回完了 |
| witness-dependent toy weight        | 未    |
| `PrimePowerLabel` 構造体               | 未    |
| analytic (\Lambda(q)/\log n)        | 未    |

これで、有限 von-Mangoldt-like weight を provider 化して weighted hit mass route に流す入口は、かなり整った。

## 7. 次の一手

次は History にある通り、prime-power witness \((p,k)\) に依存する具体的な finite toy weight の表現方法を検討する段階じゃ。

ここで分岐がある。

### A. 軽い道: \(q:\mathbb{N}\) label のまま進む

今のまま label を \(q:\mathbb{N}\) にして、weight は外から与える。

そして、

```lean
T.VonMangoldtLikeWeight w
```

で性質を管理する。

この道は軽い。
ただし、weight が本当に \(q=p^k\) の \(p\) に依存している、ということは predicate として別に述べる必要がある。

### B. 強い道: `PrimePowerLabel` を構造体化する

将来的に \(\Lambda(q)=\log p\) へ進むなら、

```lean
structure PrimePowerLabel where
  q : ℕ
  p : ℕ
  k : ℕ
  prime : Nat.Prime p
  k_pos : 0 < k
  eq_pow : q = p ^ k
```

のような型を作る道が強い。

この場合、label 自体が \(p,k\) を持つので、weight を

$$
w(n,\ell)
$$

として \(\ell.p\) に依存させやすい。

ただしこれは既存の `DivisorTransitionKernel` が label を \(\mathbb{N}\) としている設計から一段抽象化が必要になる。少し重い。

## 8. わっちの推奨

短期的には A がよい。
つまり、まずは \(q:\mathbb{N}\) label のまま、

$$
w(n,q)
$$

を外から与え、`VonMangoldtLikeWeight` と sub-probability を示して `ofVonMangoldtLikeWeight` に渡す。

そのうえで、次に「witness 依存」を predicate として表す。

たとえば、

```lean
def WitnessDependentToyWeight
    (T : PrimePowerDivisorTransitionKernel)
    (w : ℕ → ℕ → ℚ) : Prop :=
  ∀ n q, q ∈ T.toDivisorTransitionKernel.index n →
    ∃ p k, Nat.Prime p ∧ 0 < k ∧ q = p ^ k ∧
      0 ≤ w n q
```

これは現状の `VonMangoldtLikeWeight` とほぼ同じなので、次に意味を足すなら、

$$
w(n,q)=c(n,p)
$$

のような「\(p\) による表現」を持つ predicate にするのがよい。

## 9. 総括

Phase AQ は、素冪由来の料金表を **正式な provider 登録フォーム** に接続した段階じゃ。

Phase AP では「これは von-Mangoldt-like weight である」という札が付いた。
今回、その札付き weight を `PrimePowerChannelProvider` へ直接登録できるようになった。

山で言えば、料金表に「素冪由来」と書かれた公的書式ができ、それを受付がそのまま受理できるようになった。
次はいよいよ、その料金表がどの素数 \(p\) に基づいているのか、つまり witness-dependent な重み設計へ進む番じゃな。
