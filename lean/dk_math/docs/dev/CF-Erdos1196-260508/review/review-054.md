# review Phase "B"

## 1. 結論

うむ、Phase BC は **解析風 weight への安全な入口** じゃ。

今回で、

$$
c(n,p)=\frac{A(p)}{B(n)}
$$

という ratio-style toy weight が入った。まだ $\log p/\log n$ には踏み込まず、有理数 $\mathbb{Q}$ 上で、

$$
0\le A(p),\qquad 0 < B(n)
$$

なら、

$$
0\le \frac{A(p)}{B(n)}
$$

を示して `BasePrimeToyWeight` へ接続した。さらに任意の witness provider $W$ に対して `W.BaseWeightNonneg` へ降ろせるようになった。これは登頂アタックとして、かなり筋の良い一歩じゃ。

## 2. 今回の主役

追加された中心はこれじゃ。

```lean
def ratioBasePrimeWeight (A B : ℕ → ℚ) : ℕ → ℕ → ℚ :=
  fun n p => A p / B n
```

数学的には、

$$
A:\mathbb{N}\to\mathbb{Q}
$$

を base prime 側の重み、

$$
B:\mathbb{N}\to\mathbb{Q}
$$

を state $n$ 側の正規化量と見て、

$$
c(n,p)=A(p)/B(n)
$$

とする。

これは将来の

$$
c(n,p)\approx \frac{\log p}{\log n}
$$

にかなり近い形じゃ。
ただし、今はまだ $\log$ ではなく、有限・有理・toy model として安全に扱っている。

## 3. 何が閉じたか

今回閉じた theorem はこの二本じゃ。

```lean
ratioBasePrimeWeight_basePrimeToyWeight
PrimePowerWitnessProvider.baseWeightNonneg_of_ratioBasePrimeWeight
```

前者は、

$$
\forall p,\ 0\le A(p)
$$

$$
\forall n,\ 0 < B(n)
$$

から、

$$
\mathrm{BasePrimeToyWeight}(\mathrm{ratioBasePrimeWeight}(A,B))
$$

を出す。

後者はさらに、それを任意の witness provider $W$ に降ろして、

$$
\mathrm{W.BaseWeightNonneg}(\mathrm{ratioBasePrimeWeight}(A,B))
$$

を得る。

つまり、ratio-style weight はもう witness-provider route に入れる。

導線はこうじゃ。

$$
0\le A(p),\quad 0 < B(n)
$$

$$
\Downarrow
$$

$$
\mathrm{BasePrimeToyWeight}(c)
$$

$$
\Downarrow
$$

$$
\mathrm{W.BaseWeightNonneg}(c)
$$

ここまでが Phase BC の成果じゃな。

## 4. 数学的な意味

これは、今まで抽象的だった $c(n,p)$ に初めて **解析風の形** を与えた段階じゃ。

Erdős #1196 の本物ルートでは、直感的には

$$
w(n,q)\approx \frac{\Lambda(q)}{\log n}
$$

であり、 $q=p^k$ なら $\Lambda(q)=\log p$ なので、

$$
w(n,q)\approx \frac{\log p}{\log n}
$$

となる。

今回の ratio-style toy weight は、その形を抽象化して、

$$
A(p)\sim \log p,\qquad B(n)\sim \log n
$$

と読めるようにしたものじゃ。

ただし、実装上はまだ

$$
A(p),B(n)\in\mathbb{Q}
$$

の有限 toy weight。
この慎重さがよい。いきなり実数対数へ行くと、解析・極限・正値性・除算の補題が一気に重くなるからの。

## 5. 現在地

いまの到達点はこうじゃ。

| 層                                  | 状態   |
| ---------------------------------- | ---- |
| `BaseWeightNonneg`                 | 完了   |
| `BaseWeightSubProbability`         | 完了   |
| `BasePrimeToyWeight`               | 完了   |
| `ratioBasePrimeWeight`             | 今回完了 |
| ratio-style 非負性                    | 今回完了 |
| ratio-style → `W.BaseWeightNonneg` | 今回完了 |
| ratio-style sub-probability 十分条件   | 未    |
| 有理 toy model の hit mass bound      | 未    |
| 実数 $\log p/\log n$ route           | 未    |

つまり、非負性側はかなりきれいに整った。
次は、質量保存側、すなわち sub-probability じゃ。

## 6. 次の一手: Phase BD

次に狙うべきは、

$$
\sum_{q\in \text{index}(n)}
\frac{A(p(q))}{B(n)}
\le 1
$$

を示す十分条件じゃ。

自然な十分条件は、

$$
\sum_{q\in \text{index}(n)} A(p(q))\le B(n)
$$

である。

なぜなら $B(n) > 0$ なら、

$$
\sum_q \frac{A(p(q))}{B(n)} =
\frac{\sum_q A(p(q))}{B(n)} \le
\frac{B(n)}{B(n)} = 1
$$

となるからじゃ。

つまり Phase BD の中核は、

$$
\boxed{
\sum_q A(p(q))\le B(n)
\Rightarrow
\mathrm{BaseWeightSubProbability}(\mathrm{ratioBasePrimeWeight}(A,B))
}
$$

を Lean で言うことじゃな。

## 7. Phase BD の API 案

まず、十分条件を predicate として切るのがよい。

```lean
def RatioBaseWeightBudget
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

名前はもう少し短くして、

```lean
BaseWeightBudget
```

でもよい。

そして theorem は、

```lean
theorem baseWeightSubProbability_of_ratioBudget
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (A B : ℕ → ℚ)
    (hA : ∀ p, 0 ≤ A p)
    (hB : ∀ n, 0 < B n)
    (hbudget : RatioBaseWeightBudget W A B) :
    W.BaseWeightSubProbability
      (ratioBasePrimeWeight A B)
      (W.baseWeightNonneg_of_ratioBasePrimeWeight A B hA hB)
```

という形が自然じゃ。

## 8. Lean 的な注意点

ここは少しだけ手強い。

理由は、

$$
\mathrm{W.weightOfBase}(\mathrm{ratioBasePrimeWeight}(A,B))(n,q)
$$

を展開すると、

$$
\frac{A((\text{W.label}(n,q,hq)).p)}{B(n)}
$$

になるが、`hq` が依存引数として出てくるからじゃ。

既に `weightOfBase_of_mem` があるので、まずはそれを使って index 上の項を展開するのがよい。

また、Finset の和で

$$
\sum_q \frac{A_q}{B} = \frac{\sum_q A_q}{B}
$$

を使うなら、`Finset.sum_div` 系の補題が使えるか確認が必要じゃ。
重ければ、初回は直接 `field_simp` や `nlinarith` に頼らず、補題を小さく分けるのが安全。

## 9. 二手先: Phase BE

Phase BD で sub-probability 十分条件が閉じたら、次は ratio-style route 全体の hit mass bound を作れる。

つまり、

$$
0\le A(p)
$$

$$
0 < B(n)
$$

$$
\sum_q A(p(q))\le B(n)
$$

から、

$$
\mathrm{weightedHitMass}\le C
$$

へ進む alias じゃ。

候補名は、

```lean
PrimePowerWitnessProvider.ratioBaseWeight_hitMass_le_const
```

じゃな。

これが入ると、ratio-style toy model は一通り完成する。

## 10. その先の山影

Phase BE の先に、いよいよ本物寄りの選択肢が見える。

$$
A(p)=\log p,\qquad B(n)=\log n
$$

を目指す道じゃ。

ただし、その前に有理 toy model として、

$$
A(p)=\text{手定義の非負スコア}
$$

$$
B(n)=\text{その総量以上の正規化項}
$$

を sample で通しておくとよい。

つまり、

$$
\text{ratio-style toy model}
$$

を完成させてから、

$$
\text{real/log analytic model}
$$

に入るのが、登山道としては安全じゃ。

## 11. 総括

Phase BC は、いよいよ

$$
\frac{\log p}{\log n}
$$

の影が見えるところまで来た段階じゃ。

ただし、賢いことにまだ $\log$ そのものには触れていない。
まずは

$$
\frac{A(p)}{B(n)}
$$

という有理 toy model を導入し、分子非負・分母正から非負性を閉じた。

次は、

$$
\sum_q A(p(q))\le B(n)
$$

という **予算条件** から、

$$
\sum_q \frac{A(p(q))}{B(n)}\le 1
$$

を出す。
ここが閉じれば、ratio-style toy weight は「非負」だけでなく「Big から飛び出せない」weight になる。

山で言えば、Phase BC で登山料の比率表ができた。
Phase BD では、その総額が予算 $B(n)$ を超えないことを示し、有限質量保存の本線へ載せる番じゃな。
