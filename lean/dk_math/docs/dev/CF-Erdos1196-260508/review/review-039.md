# review

## 1. 結論

うむ、Phase AN は **finite toy weight の一般 constructor 化** じゃ。
前回 Phase AM では、具体例として

$$
w(10,2)=1,\qquad w(10,5)=0
$$

を `withWeight` で載せ替え、`PrimePowerChannelProvider` へ接続し、さらに weighted hit mass bound まで通した。

今回 Phase AN では、その流れ

$$
\text{withWeight}
\to
\text{SubProbability}
\to
\text{ofKernel}
$$

を

```lean
PrimePowerChannelProvider.ofKernelWithWeight
```

として一つにまとめた。これはかなり良い整理じゃ。

## 2. 今回の主役

追加された中心 API はこれじゃ。

```lean
def ofKernelWithWeight
    (T : PrimePowerDivisorTransitionKernel)
    (w : ℕ → ℕ → ℚ)
    (hw_nonneg :
      ∀ n q, q ∈ T.toDivisorTransitionKernel.index n → 0 ≤ w n q)
    (hw_subprob : (T.withWeight w hw_nonneg).SubProbability) :
    PrimePowerChannelProvider :=
  ofKernel (T.withWeight w hw_nonneg) hw_subprob
```

数学的には、

$$
T:\text{prime-power divisor transition kernel}
$$

$$
w:\mathbb{N}\times\mathbb{N}\to\mathbb{Q}
$$

を与え、

$$
q\in index_T(n)\Rightarrow 0\le w(n,q)
$$

と

$$
\sum_{q\in index_T(n)} w(n,q)\le 1
$$

を示せば、ただちに `PrimePowerChannelProvider` が得られる。

つまり、任意の手定義 finite toy weight を channel provider 化する標準入口ができた。

## 3. 何が楽になったか

以前は、toy weight を載せるたびに次の流れを手で書く必要があった。

```lean
T.withWeight w hw_nonneg
```

を作り、

```lean
(T.withWeight w hw_nonneg).SubProbability
```

を証明し、

```lean
PrimePowerChannelProvider.ofKernel ...
```

に渡す。

今回からは、それが

```lean
PrimePowerChannelProvider.ofKernelWithWeight T w hw_nonneg hw_subprob
```

で済む。

これは今後効く。
`sampleTenToyWeight` のような手定義 toy weight だけでなく、将来の

$$
w_{\Lambda\text{-like}}(n,q)
$$

を同じ形式で載せられるからじゃ。

## 4. sample の変更も正しい

`sampleTenToyWeightChannelProvider` が、

```lean
PrimePowerChannelProvider.ofKernelWithWeight
  sampleTenPrimePowerDivisorTransitionKernel
  sampleTenToyWeight
  sampleTenToyWeight_nonneg
  sampleTenToyWeightKernel_subProbability
```

経由に切り替わった。

これは良い。
サンプルが標準 constructor を通ることで、今後の実装者は「toy weight を provider 化するときはこの入口を使う」と自然に読める。

この種の整理は、証明力そのものよりも **API の作法** を固める意味が大きいのじゃ。

## 5. 現在地

ここまでの層はこうじゃ。

| 層                                     | 状態   |
| ------------------------------------- | ---- |
| `DivisorTransitionKernel`             | 完了   |
| `PrimePowerDivisorTransitionKernel`   | 完了   |
| `PrimePowerChannelProvider`           | 完了   |
| `withWeight`                          | 完了   |
| concrete finite toy weight            | 完了   |
| toy weight → hit mass bound           | 完了   |
| general finite toy weight constructor | 今回完了 |
| constructor 由来 provider の simp API    | 未    |
| witness-dependent toy weight          | 未    |
| von-Mangoldt-like finite weight       | 未    |

これで、finite toy weight 層はかなり実用段階に入った。

## 6. 次の一手

次は History にある通り、`ofKernelWithWeight` で得た provider の中身を取り出す simp API が自然じゃ。

欲しいのは、例えばこういう補題じゃな。

```lean
@[simp] theorem ofKernelWithWeight_kernel ...
@[simp] theorem ofKernelWithWeight_providerAt ...
@[simp] theorem ofKernelWithWeight_channelProviderAt ...
```

特に重要なのは、生成された provider の underlying kernel が

$$
T.withWeight(w)
$$

であることを簡単に展開できることじゃ。

後続で、

$$
provider.channelProviderAt(n).weight(q)=w(n,q)
$$

のような式を扱いたくなる。
そのとき、毎回 `ofKernelWithWeight`, `ofKernel`, `withWeight`, `providerAt`, `channelProviderAt` を手で展開すると読みにくい。

## 7. Phase AO 案

次は **Phase AO: ofKernelWithWeight simp API** がよい。

候補は次のようなものじゃ。

```lean
@[simp] theorem ofKernelWithWeight_kernel
    (T : PrimePowerDivisorTransitionKernel)
    (w : ℕ → ℕ → ℚ)
    (hw_nonneg : ...)
    (hw_subprob : ...) :
    (PrimePowerChannelProvider.ofKernelWithWeight
      T w hw_nonneg hw_subprob).kernel =
      T.withWeight w hw_nonneg := rfl
```

さらに可能なら、

```lean
@[simp] theorem ofKernelWithWeight_channelProviderAt
```

や、

```lean
@[simp] theorem ofKernelWithWeight_channelProviderAt_weight
```

も欲しい。

ただし `WeightProvider.weight` まで一気に simp する補題は、Lean の展開が重くなりすぎる場合がある。
まずは `kernel` / `channelProviderAt` の軽い `[simp]` からでよい。

## 8. その次の山

その後はいよいよ、

$$
q=p^k
\Rightarrow
w(n,q)\text{ depends on }p
$$

という witness-dependent toy weight へ進める。

ここは少し慎重に行くべきじゃ。
`IsPrimePowerLabel q` は存在命題なので、(p,k) をどう選ぶかが Lean 的な問題になる。

候補は二つ。

1. 今の (q:\mathbb{N}) label を保ち、weight は外から手定義して、(\Lambda)-like 性質だけを predicate で持つ。
2. label を構造体化して、最初から (q,p,k) と証明を持たせる。

```lean
structure PrimePowerLabel where
  q : ℕ
  p : ℕ
  k : ℕ
  prime : Nat.Prime p
  k_pos : 0 < k
  eq_pow : q = p ^ k
```

今の流れなら、まずは 1 の方が軽い。
ただ、将来的に (\Lambda(q)=\log p) を本当に扱うなら、2 の構造体化もかなり魅力がある。

## 9. 総括

Phase AN は、素冪 channel の toy weight を **一般入力化** した段階じゃ。

前回までは、具体的な料金表を一つ登録した。
今回からは、任意の料金表 (w) について、

$$
w\ge 0,\qquad \sum w\le 1
$$

を示せば、同じ受付から `PrimePowerChannelProvider` へ登録できる。

山で言えば、素冪専用ルートの受付が「手書き料金表を受け付ける標準フォーム」を持った。
次は、そのフォームで登録された料金表を読み出しやすくする案内札、つまり simp API の整備じゃな。
