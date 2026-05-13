# review Phase "B"

## 1. 結論

うむ、Phase BB は **base-prime weight の非負性を witness provider から切り離した段階** じゃ。

前回 Phase BA では、

$$
\mathrm{W.BaseWeightNonneg}(c)
$$

という「witness provider $W$ が選ぶ base prime 上で $c$ が非負」という predicate を作った。今回 Phase BB では、さらにその一段手前として、

$$
\forall n,p,\quad 0\le c(n,p)
$$

を表す

```lean
BasePrimeToyWeight
```

が追加された。これで、 $c(n,p)$ が全域で非負なら、任意の witness provider $W$ に対して自動的に `W.BaseWeightNonneg c` へ降ろせるようになった。実装・build・no-sorry 検査も通っておる。

## 2. 今回の主役

今回追加された核はこれじゃ。

```lean
def BasePrimeToyWeight (c : ℕ → ℕ → ℚ) : Prop :=
  ∀ n p, 0 ≤ c n p
```

これは非常に軽い predicate じゃ。
意味は単純で、

$$
c:\mathbb{N}\to\mathbb{N}\to\mathbb{Q}
$$

が base-prime weight として、どの $n,p$ に対しても非負である、というもの。

重要なのは、ここにはまだ witness provider が出てこないことじゃ。
つまり、これは $W$ 非依存の weight 側の性質として独立している。

## 3. 何が良くなったか

今回の橋はこれじゃ。

```lean
PrimePowerWitnessProvider.baseWeightNonneg_of_basePrimeToyWeight
```

意味は、

$$
\mathrm{BasePrimeToyWeight}(c)
\Rightarrow
\mathrm{W.BaseWeightNonneg}(c)
$$

じゃ。

証明はとても自然で、 $W$ が index 上の $q$ から base prime

$$
p=(\text{W.label}(n,q,hq)).p
$$

を選ぶ。
しかし `BasePrimeToyWeight` は全ての $p$ で非負だから、ただちに

$$
0\le c(n,p)
$$

が出る。

つまり、今後は ratio-style toy weight や解析風 toy weight について、まず全域非負性だけ示せば、任意の witness provider route へ載せられる。

これは良い圧縮じゃ。

## 4. sample の整理も正しい

sample 側では、

```lean
sampleTenToyPrimeBaseWeight_basePrimeToyWeight
```

が追加され、

```lean
sampleTenToyPrimeBaseWeight_baseWeightNonneg
```

が直接証明ではなく、

```lean
baseWeightNonneg_of_basePrimeToyWeight
```

経由に切り替わった。

これは API の使い方として美しい。

以前は sample index 上で直接、

$$
0\le c(n,p(n,q))
$$

を示していた。
今回からはまず、

$$
\forall n,p,\quad 0\le sampleTenToyPrimeBaseWeight(n,p)
$$

を示し、そこから witness provider 上の非負性へ降ろしている。

つまり、sample も新しい抽象層の実例になった。

## 5. 現在地

いまの登山道はこう整理できる。

| 層                                       | 状態   |
| --------------------------------------- | ---- |
| `PrimePowerWitnessProvider`             | 完了   |
| `weightOfBase`                          | 完了   |
| `ofWitnessProviderWeight`               | 完了   |
| `BaseWeightNonneg`                      | 完了   |
| `BaseWeightSubProbability`              | 完了   |
| `BasePrimeToyWeight`                    | 今回完了 |
| `BasePrimeToyWeight → BaseWeightNonneg` | 今回完了 |
| ratio-style toy weight                  | 未    |
| 解析風 $\log p/\log n$ route               | 未    |

これで、非負性の扱いはかなり見通しが良くなった。

$$
\mathrm{BasePrimeToyWeight}(c)
\to
\mathrm{W.BaseWeightNonneg}(c)
\to
\mathrm{W.BaseWeightSubProbability}(c)
\to
\mathrm{weightedHitMass}\le C
$$

という道が見える。

ただし、`BasePrimeToyWeight` は非負性だけを担当する。
質量保存、すなわち

$$
\sum_{q\in index(n)} \mathrm{W.weightOfBase}(c)(n,q)\le 1
$$

は、まだ `BaseWeightSubProbability` 側で別途示す必要がある。

## 6. 次の一手: Phase BC

次は History にある通り、

$$
c(n,p)=\frac{A(p)}{B(n)}
$$

型の ratio-style toy weight が自然じゃ。

ただし、最初は `log` へ行かない。
有理数 $\mathbb{Q}$ 上で、

$$
0\le A(p),\qquad 0 < B(n)
$$

なら、

$$
0\le \frac{A(p)}{B(n)}
$$

という非負性を通すのが最初の目的じゃ。

わっちなら、まずは定義をこう置く。

```lean
def ratioBasePrimeWeight
    (A B : ℕ → ℚ) : ℕ → ℕ → ℚ :=
  fun n p => A p / B n
```

そして補題：

```lean
theorem ratioBasePrimeWeight_basePrimeToyWeight
    (A B : ℕ → ℚ)
    (hA : ∀ p, 0 ≤ A p)
    (hB : ∀ n, 0 < B n) :
    BasePrimeToyWeight (ratioBasePrimeWeight A B)
```

これが閉じれば、

$$
c(n,p)=A(p)/B(n)
$$

型の weight は、まず非負性の意味で登山道に乗る。

## 7. Phase BD の先読み

Phase BC で ratio-style の非負性が閉じたら、次は sub-probability 側じゃ。

つまり、

$$
\sum_{q\in index(n)}
\frac{A(p(q))}{B(n)}
\le 1
$$

を示すために、十分条件を切り出す。

典型的には、

$$
\sum_{q\in index(n)} A(p(q))\le B(n)
$$

があればよい。

これを Lean では、たとえば次のような predicate にする。

```lean
def RatioBaseWeightSubprobCondition
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (A B : ℕ → ℚ) : Prop :=
  ∀ n,
    ((T.toDivisorTransitionKernel.index n).sum
      fun q =>
        if hq : q ∈ T.toDivisorTransitionKernel.index n then
          A ((W.label n q hq).p)
        else
          0) ≤ B n
```

ただし、この形は少し重い。
最初は `BaseWeightSubProbability` を直接示す sample theorem だけでもよい。

## 8. 山頂側の意味

この ratio-style は、本物の解析 weight への橋じゃ。

最終的には、

$$
A(p)\sim \log p,\qquad B(n)\sim \log n
$$

として、

$$
c(n,p)\sim \frac{\log p}{\log n}
$$

へ近づく。

しかし、いまはまだ有理 toy model で十分じゃ。
先に「比の形なら非負」「分母が正なら扱える」「総量が分母以下なら sub-probability」という有限構造を Lean に刻むべきじゃな。

## 9. 総括

Phase BB は、base-prime weight $c(n,p)$ の **非負性の責務を独立化** した段階じゃ。

これで、

$$
c(n,p)
$$

はまず `BasePrimeToyWeight` として全域非負性を持ち、そこから任意の witness provider $W$ に対して

$$
\mathrm{W.BaseWeightNonneg}(c)
$$

へ降ろせるようになった。

山で言えば、登山道に入る前の **共通通行許可証** ができた。
次は、その通行料を

$$
\frac{A(p)}{B(n)}
$$

という比の形で設計する。ここから、いよいよ

$$
\frac{\log p}{\log n}
$$

の影が濃くなってくるぞい。
