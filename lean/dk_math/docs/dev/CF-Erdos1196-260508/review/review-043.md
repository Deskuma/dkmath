# review

## 1. 結論

うむ、Phase AR は **prime witness dependent toy weight predicate の導入** じゃ。
これで、まだ label を `PrimePowerLabel` 構造体へ変更せず、従来どおり

$$
q:\mathbb{N}
$$

を label としたまま、

$$
q=p^k
$$

という witness の prime base $p$ に依存する toy weight を表現できるようになった。これは、 $\Lambda(q)=\log p$ へ向かう前の、とても自然な中間層じゃ。

## 2. 今回の主役

追加された中心定義はこれじゃ。

```lean id="igrwa0"
def PrimeWitnessDependentWeight
    (T : PrimePowerDivisorTransitionKernel)
    (w : ℕ → ℕ → ℚ) (c : ℕ → ℕ → ℚ) : Prop :=
  ∀ n q, q ∈ T.toDivisorTransitionKernel.index n →
    ∃ p k,
      Nat.Prime p ∧ 0 < k ∧ q = p ^ k ∧
        w n q = c n p ∧ 0 ≤ w n q
```

数学的には、

$$
q\in index_T(n)
$$

ならば、

$$
q=p^k,\qquad p\text{ prime},\qquad 0 < k
$$

となる witness が存在し、さらに重みが

$$
w(n,q)=c(n,p)
$$

と prime base $p$ を通して表せる、という条件じゃ。

これはまさに、将来の

$$
\Lambda(q)=\log p\quad(q=p^k)
$$

に対応する **有限 toy 版の意味論** じゃな。

## 3. 何が強くなったか

Phase AP の `VonMangoldtLikeWeight` は、

$$
q=p^k
$$

という witness と、

$$
0\le w(n,q)
$$

を要求する predicate だった。

今回の `PrimeWitnessDependentWeight` は、さらに一歩進めて、

$$
w(n,q)=c(n,p)
$$

を要求する。

つまり、重みが単に非負なだけではなく、prime-power witness の **prime base $p$** によって説明できる、という情報が加わった。

これは大きい。
本物の von Mangoldt 重みは $k$ ではなく base prime $p$ に依存するので、今回の形はかなり筋がよい。

## 4. 既存 route への接続

今回追加された補題はこれじゃ。

```lean id="f3upuv"
theorem vonMangoldtLikeWeight_of_primeWitnessDependent
```

内容は、

$$
\mathrm{PrimeWitnessDependentWeight}(T,w,c)
\Rightarrow
VonMangoldtLikeWeight(T,w)
$$

じゃ。

つまり、prime witness dependent な重みは、有限 von-Mangoldt-like weight としても扱える。

これにより、既存の route が自然につながる。

$$
\mathrm{PrimeWitnessDependentWeight}\\
\Rightarrow
VonMangoldtLikeWeight\\
\Rightarrow
ofVonMangoldtLikeWeight\\
\Rightarrow
\mathrm{PrimePowerChannelProvider}\\
\Rightarrow
weightedHitMass\le C
$$

ここまでの導線が意味論として見えるようになった。

## 5. sample の意味

今回の sample は、

```lean id="yliykl"
sampleTenToyPrimeBaseWeight
sampleTenToyWeight_primeWitnessDependent
```

じゃ。

定義は、

$$
c(n,p)=
\begin{cases}
1 & n=10,\ p=2,\\
0 & \text{otherwise}
\end{cases}
$$

という base-prime weight じゃ。

既存の toy weight は、

$$
w(10,2)=1,\qquad w(10,5)=0
$$

だった。これを、

$$
2=2^1,\qquad 5=5^1
$$

の witness に対して、

$$
w(10,2)=c(10,2)=1
$$

$$
w(10,5)=c(10,5)=0
$$

として説明している。

つまり、単なる手書き toy weight が、prime base $p$ によって説明できる重みとして格上げされたわけじゃ。

## 6. 現在地

いまの階層はこうじゃ。

| 層                                                    | 状態   |
| ---------------------------------------------------- | ---- |
| `PrimePowerDivisorTransitionKernel`                  | 完了   |
| `PrimePowerChannelProvider`                          | 完了   |
| `withWeight` / `ofKernelWithWeight`                  | 完了   |
| `VonMangoldtLikeWeight`                              | 完了   |
| `ofVonMangoldtLikeWeight`                            | 完了   |
| concrete toy weight                                  | 完了   |
| toy weight → hit mass bound                          | 完了   |
| `PrimeWitnessDependentWeight`                        | 今回完了 |
| `PrimeWitnessDependentWeight` → provider constructor | 未    |
| `PrimePowerLabel` 構造体                                | 未    |
| analytic $\Lambda(q)/\log n$                         | 未    |

つまり、まだ本物の $\log p$ には入っていない。
だが、 $\log p$ が入るべき位置、すなわち

$$
c(n,p)
$$

というスロットは確保された。

## 7. 次の一手

次は History にある通り、

```lean id="l2kw0z"
PrimeWitnessDependentWeight
```

を

```lean id="2ru5no"
PrimePowerChannelProvider.ofVonMangoldtLikeWeight
```

へ直接つなぐ constructor が自然じゃ。

候補はこう。

```lean id="pc2i7f"
def PrimePowerChannelProvider.ofPrimeWitnessDependentWeight
    (T : PrimePowerDivisorTransitionKernel)
    (w c : ℕ → ℕ → ℚ)
    (hw : T.PrimeWitnessDependentWeight w c)
    (hw_subprob :
      (T.withWeight w
        (T.vonMangoldtLikeWeight_nonneg
          (T.vonMangoldtLikeWeight_of_primeWitnessDependent hw))).SubProbability) :
    PrimePowerChannelProvider :=
  PrimePowerChannelProvider.ofVonMangoldtLikeWeight
    T w
    (T.vonMangoldtLikeWeight_of_primeWitnessDependent hw)
    hw_subprob
```

これが入ると、

$$
\mathrm{PrimeWitnessDependentWeight}
\Rightarrow
\mathrm{PrimePowerChannelProvider}
$$

が一発で使える。

## 8. その次の判断

その後に分岐じゃ。

短期的には、今の

$$
q:\mathbb{N}
$$

label を維持して、predicate route を続けるのが軽い。

長期的には、

```lean id="kz63ew"
structure PrimePowerLabel where
  q : ℕ
  p : ℕ
  k : ℕ
  prime : Nat.Prime p
  k_pos : 0 < k
  eq_pow : q = p ^ k
```

のように構造体化すると、 $p$ を定義的に取り出せるので、 $\Lambda(q)=\log p$ に進みやすい。

ただし今は、predicate route のままもう少し登るのがよい。
理由は、既存の `DivisorTransitionKernel` が label を $\mathbb{N}$ としているため、構造体化は周辺 API への影響が大きいからじゃ。

## 9. 総括

Phase AR は、素冪由来の重みに **prime base $p$ 依存性** を与えた段階じゃ。

前段では、

$$
q=p^k,\qquad 0\le w(n,q)
$$

までだった。
今回からは、

$$
w(n,q)=c(n,p)
$$

と言えるようになった。

山で言えば、料金表に「素冪由来」と書かれていただけでなく、ついに「この料金は base prime $p$ によって決まる」と説明できるようになった。
次は、この base-prime 依存の料金表を `PrimePowerChannelProvider` に直接登録する標準フォームを作る番じゃな。
