# review

## 1. 結論

うむ、Phase AP は **finite von-Mangoldt-like weight の predicate 化** じゃ。
ここでは本物の von Mangoldt 関数 $\Lambda(q)$ や解析的な $\log n$ にはまだ入らず、

$$
q\in \text{index}(n)
$$

上の label が prime-power witness を持ち、かつ weight が非負である、という有限・形式的な条件を `VonMangoldtLikeWeight` として切り出した。これはかなり良い一手じゃ。

## 2. 今回の主役

追加された定義はこれじゃ。

```lean
def VonMangoldtLikeWeight
    (T : PrimePowerDivisorTransitionKernel) (w : ℕ → ℕ → ℚ) : Prop :=
  ∀ n q, q ∈ T.toDivisorTransitionKernel.index n →
    ∃ p k, Nat.Prime p ∧ 0 < k ∧ q = p ^ k ∧ 0 ≤ w n q
```

数学的には、

$$
q\in \text{index}_T(n)
\Rightarrow
\exists p,k,\quad p\text{ prime}\land 0 < k\land q=p^k\land 0\le w(n,q)
$$

ということじゃ。

名前に von Mangoldt-like とあるが、まだ

$$
\Lambda(q)=\log p
$$

を定義しているわけではない。
いまは「 $\Lambda$ が反応する prime-power channel 上で、非負重みを持つ」という有限 predicate じゃな。

## 3. 何が強くなったか

今回の良い点は、label をまだ構造体化せず、

$$
q:\mathbb{N}
$$

のまま進めていることじゃ。

`IsPrimePowerLabel q` は存在命題なので、後で $p,k$ をどう取り出すかは山場になる。
だが、いまはまず軽く、

$$
q=p^k\text{ である証拠が存在する}
$$

ことと、

$$
0\le w(n,q)
$$

をまとめて theorem-facing predicate とした。

これにより、後続の theorem は

```lean
hw : T.VonMangoldtLikeWeight w
```

を受け取るだけで、prime-power witness と非負性の両方を使える。

## 4. 補題の粒度が良い

今回追加された補題は、かなり自然じゃ。

```lean
vonMangoldtLikeWeight_nonneg
vonMangoldtLikeWeight_isPrimePowerLabel
vonMangoldtLikeWeight_of_nonneg
```

それぞれの意味はこうじゃ。

$$
\mathrm{T.VonMangoldtLikeWeight}(w)
\Rightarrow
0\le w(n,q)
$$

$$
\mathrm{T.VonMangoldtLikeWeight}(w)
\Rightarrow
IsPrimePowerLabel(q)
$$

そして、`T : PrimePowerDivisorTransitionKernel` はすでに index が prime-power だけであることを持っているので、

$$
\left(\forall q\in \text{index}(n),\ 0\le w(n,q)\right)
\Rightarrow
\mathrm{T.VonMangoldtLikeWeight}(w)
$$

が出る。

最後の `vonMangoldtLikeWeight_of_nonneg` が特に良い。
なぜなら `PrimePowerDivisorTransitionKernel` の型がすでに prime-power witness を持っているため、外から追加で必要なのは weight の非負性だけになるからじゃ。

## 5. sample の意味

今回追加された sample は、

```lean
sampleTenToyWeight_vonMangoldtLikeWeight
```

じゃ。

既存の toy weight

$$
w(10,2)=1,\qquad w(10,5)=0
$$

について、`sampleTenPrimePowerDivisorTransitionKernel` 上で `VonMangoldtLikeWeight` であることを示している。

ここでは `vonMangoldtLikeWeight_of_nonneg` が使われている。
つまり、sample kernel が prime-power indexed であることは型側にあり、toy weight の非負性だけで von-Mangoldt-like predicate へ上がれる。

これは美しい。
Phase AP の狙いが concrete sample でもちゃんと効いておる。

## 6. 現在地

ここまでの階層はこうじゃ。

| 層                                              | 状態   |
| ---------------------------------------------- | ---- |
| `PrimePowerDivisorTransitionKernel`            | 完了   |
| `PrimePowerChannelProvider`                    | 完了   |
| `withWeight`                                   | 完了   |
| `ofKernelWithWeight`                           | 完了   |
| concrete toy weight                            | 完了   |
| toy weight → hit mass bound                    | 完了   |
| `ofKernelWithWeight` simp API                  | 完了   |
| `VonMangoldtLikeWeight` predicate              | 今回完了 |
| `VonMangoldtLikeWeight` → provider constructor | 未    |
| witness-dependent concrete weight              | 未    |
| analytic $\Lambda(q)/\log n$                   | 未    |

これで、finite toy weight が単なる手書き重みではなく、 **prime-power witness を持つ von-Mangoldt-like weight** として扱えるようになった。

## 7. 次の一手

次は History にある通り、`VonMangoldtLikeWeight` と `ofKernelWithWeight` を直接つなぐ constructor / theorem が自然じゃ。

候補はこう。

```lean
def PrimePowerChannelProvider.ofVonMangoldtLikeWeight
    (T : PrimePowerDivisorTransitionKernel)
    (w : ℕ → ℕ → ℚ)
    (hw : T.VonMangoldtLikeWeight w)
    (hsub :
      (T.withWeight w (T.vonMangoldtLikeWeight_nonneg hw)).SubProbability) :
    PrimePowerChannelProvider :=
  PrimePowerChannelProvider.ofKernelWithWeight
    T w (T.vonMangoldtLikeWeight_nonneg hw) hsub
```

これが入ると、後続では

$$
\mathrm{T.VonMangoldtLikeWeight}(w)
$$

と sub-probability を示すだけで、provider 化できる。

つまり、

$$
\mathrm{von-Mangoldt-like predicate}
\to
\mathrm{withWeight}
\to
\mathrm{PrimePowerChannelProvider}
\to
\mathrm{weightedHitMass bound}
$$

が一本につながる。

## 8. その次に見える山

その後は、いよいよ

$$
q=p^k
\Rightarrow
w(n,q)\text{ depends on }p
$$

という、より von Mangoldt らしい重みに進む段階じゃ。

ただし、ここは慎重に進むべきじゃ。
`IsPrimePowerLabel q` は存在命題なので、「その $p$ 」を計算的・定義的に取り出すのは簡単ではない。

短期的には、

$$
w
$$

を外から与えて、

$$
\mathrm{T.VonMangoldtLikeWeight}(w)
$$

という predicate で性質だけを管理するのが安全。
長期的には、label を

```lean
structure PrimePowerLabel where
  q : ℕ
  p : ℕ
  k : ℕ
  prime : Nat.Prime p
  k_pos : 0 < k
  eq_pow : q = p ^ k
```

のように構造体化する道もある。

## 9. 総括

Phase AP は、素冪 channel 上の weight に **von-Mangoldt-like という性格札** を付けた段階じゃ。

まだ本物の $\Lambda$ ではない。
だが、

$$
q=p^k
$$

という witness と、

$$
0\le w(n,q)
$$

を一つの predicate として持てるようになった。

山で言えば、これまでは料金表が「非負である」だけだった。
今回からは、その料金表に「素冪由来の料金表」という札が付いた。
次はその札付き料金表を、`PrimePowerChannelProvider` へ直接登録する constructor を作るのがよいぞい。
