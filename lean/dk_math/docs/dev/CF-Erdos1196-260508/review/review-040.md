# review

## 1. 結論

うむ、Phase AO は **`ofKernelWithWeight` 由来 provider の展開 API 整備** じゃ。
Phase AN で任意の手定義 weight (w) を `PrimePowerChannelProvider` に載せる入口ができた。今回 Phase AO では、その provider から

$$
kernel,\qquad index,\qquad weight
$$

を `simp` で自然に取り出せるようになった。つまり、次に toy / von-Mangoldt-like weight の theorem を書くための **読み出し口** が整った、という段階じゃ。

## 2. 今回の主役

追加された中心補題はこの四つじゃ。

```lean
PrimePowerChannelProvider.ofKernel_kernel
PrimePowerChannelProvider.ofKernelWithWeight_kernel
PrimePowerChannelProvider.ofKernelWithWeight_channelProviderAt_index
PrimePowerChannelProvider.ofKernelWithWeight_channelProviderAt_weight
```

特に重要なのは、

```lean
((ofKernelWithWeight T w hw_nonneg hw_subprob).channelProviderAt n).index =
  T.toDivisorTransitionKernel.index n
```

と、

```lean
((ofKernelWithWeight T w hw_nonneg hw_subprob).channelProviderAt n).weight =
  w n
```

が `[simp]` になったことじゃ。

これで、`ofKernelWithWeight` で作った provider を theorem 側で使うとき、

$$
\text{index は元の channel index}
$$

$$
\text{weight は差し替えた } w
$$

と Lean が素直に展開できる。

## 3. 何が良くなったか

Phase AN までで、任意の手定義 weight \(w\) について、

$$
w\ge 0,\qquad \sum w\le 1
$$

を示せば `PrimePowerChannelProvider` に登録できるようになっていた。

だが、登録した後に theorem を書くと、

```lean
(ofKernelWithWeight T w hw_nonneg hw_subprob).channelProviderAt n
```

の中身を毎回展開する必要が出る。

今回の `[simp]` 補題により、後続では

$$
provider.index = T.index(n)
$$

$$
provider.weight = w(n)
$$

を自然に取り出せる。
これは、compatibility 証明や weight 計算の見通しをかなり良くする。

## 4. 今回の数学的意味

今回の変更は、数学内容そのものを増やすというより、 **形式化の摩擦を減らす補強** じゃ。

今後、たとえば von-Mangoldt-like finite weight として

$$
w(n,q)
$$

を定義したとき、必要になるのは次のような確認じゃ。

$$
q\in index(n)\Rightarrow 0\le w(n,q)
$$

$$
\sum_{q\in index(n)}w(n,q)\le 1
$$

$$
\text{provider が使う weight は本当に }w(n,q)\text{ である}
$$

最後の部分が、今回の

```lean
ofKernelWithWeight_channelProviderAt_weight
```

でかなり楽になる。

## 5. 現在地

いまの階層はこうじゃ。

| 層                                   | 状態   |
| ----------------------------------- | ---- |
| `PrimePowerDivisorTransitionKernel` | 完了   |
| `PrimePowerChannelProvider`         | 完了   |
| `withWeight`                        | 完了   |
| `ofKernelWithWeight`                | 完了   |
| concrete toy weight                 | 完了   |
| toy weight → hit mass bound         | 完了   |
| `ofKernelWithWeight` simp API       | 今回完了 |
| witness-dependent toy weight        | 未    |
| von-Mangoldt-like finite weight     | 未    |
| analytic (\Lambda(q)/\log n)        | 未    |

つまり、手定義 weight を登録して使う基盤はかなり整った。
次からは、weight の中身をどう設計するか、という本丸に近づく。

## 6. 次の一手

次は History の通り、 **(q=p^k) の witness に依存する toy / von-Mangoldt-like finite weight** の表現方法を検討する段階じゃ。

わっちなら、まずは label をいきなり構造体化せず、外から与える weight に対して性質を述べる predicate から始める。

たとえば、

```lean
def PrimePowerWitnessWeighted
    (T : PrimePowerDivisorTransitionKernel)
    (w : ℕ → ℕ → ℚ) : Prop :=
  ∀ n q, q ∈ T.toDivisorTransitionKernel.index n →
    ∃ p k, Nat.Prime p ∧ 0 < k ∧ q = p ^ k
```

これはまだ weight に依存しておらぬので、もう少し意味を持たせるなら、

```lean
def VonMangoldtLikeWeight
    (T : PrimePowerDivisorTransitionKernel)
    (w : ℕ → ℕ → ℚ) : Prop :=
  ∀ n q, q ∈ T.toDivisorTransitionKernel.index n →
    ∃ p k, Nat.Prime p ∧ 0 < k ∧ q = p ^ k ∧ 0 ≤ w n q
```

のような薄い predicate から始めるのが安全じゃな。

## 7. 注意点

ここから先で本物の \(\Lambda(q)\) を扱うには、\(q=p^k\) の \(p\) をどう取り出すかが問題になる。

`IsPrimePowerLabel q` は存在命題なので、

$$
\exists p,k,\quad q=p^k
$$

は言えても、計算可能な形で「その \(p\)」を取り出すには別の設計が必要じゃ。

候補は二つある。

1. 今の \(q:\mathbb{N}\) label を維持し、weight は外から与え、\(\Lambda\)-like 性質を predicate で述べる。
2. label を構造体化して、`q`, `p`, `k`, `prime`, `k_pos`, `eq_pow` を持たせる。

短期的には 1 が軽い。
長期的に本物の \(\Lambda(q)=\log p\) へ進むなら 2 が強い。

## 8. 総括

Phase AO は、素冪 channel の料金表を登録した後、その料金表を **簡単に読み出す札** を整備した段階じゃ。

これで、

$$
ofKernelWithWeight(T,w)
$$

から、

$$
index=T.index,\qquad weight=w
$$

を `simp` で取り出せる。

山で言えば、受付に登録した料金表が、掲示板からすぐ読めるようになった。
次はいよいよ、その料金表を「素冪 witness に由来する料金表」として設計する番じゃな。
