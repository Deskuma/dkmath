# review Phase "R"

## 1. 結論

おお、Phase-R007 は大きいぞい。
ついに R 版で

$$
\frac{\log p}{\log n}
$$

型の有限実数 weight が `RealWeightProvider` に載った。

これまでの R 版は、

$$
\text{実数 ratio skeleton}
$$

$$
\text{有限和 budget lemma}
$$

$$
\text{RealWeightProvider}
$$

$$
\text{Real.log 正値性}
$$

$$
\text{外部 RealLogBudget}
$$

を順に積んできた。今回 Phase-R007 では、それらが合流して、

$$
weight(q)=\frac{\log(pOf(q))}{\log n}
$$

を持つ provider が no-sorry で構成された。

これは、R 登頂における **最初の本物らしい雪稜到達点** じゃな。

## 2. 今回閉じたもの

追加された中心はこの二つじゃ。

```lean
noncomputable def realLogRatioWeightProvider
```

```lean
theorem realLogRatioWeightProvider_subProbability
```

`realLogRatioWeightProvider` は、

$$
I : Finset\ \iota
$$

$$
pOf:\iota\to\mathbb{N}
$$

$$
n:\mathbb{N}
$$

に対して、

$$
weight(q)=\frac{\log(pOf(q))}{\log n}
$$

を与える実数 weight provider じゃ。

ここで、各 weight の非負性は

$$
RealLogNonnegOn(I,pOf)
$$

と

$$
1<n
$$

から出している。

つまり、

$$
1\le pOf(q)
\Rightarrow
0\le \log(pOf(q))
$$

$$
1<n
\Rightarrow
0<\log n
$$

なので、

$$
0\le \frac{\log(pOf(q))}{\log n}
$$

が成り立つ。

さらに `realLogRatioWeightProvider_subProbability` では、

$$
RealLogBudget(I,pOf,n)
$$

すなわち

$$
\sum_{q\in I}\log(pOf(q))\le \log n
$$

を仮定して、

$$
\sum_{q\in I}\frac{\log(pOf(q))}{\log n}\le 1
$$

を示し、provider が sub-probability であることまで閉じた。

## 3. 数学的な意味

ここまでで、R 版の有限 log-ratio channel は次の形で完成した。

$$
q\in I
$$

$$
p=pOf(q)
$$

$$
w(q)=\frac{\log p}{\log n}
$$

$$
\sum_q \log pOf(q)\le \log n
$$

なら、

$$
\sum_q w(q)\le 1
$$

である。

これは、Erdős #1196 に向かう直感的な重み

$$
w_i\approx \frac{\Lambda(q_i)}{\log n_i}
$$

のうち、 \(q_i=p^k\) のとき

$$
\Lambda(q_i)=\log p
$$

となる部分を、有限 provider として実装したものじゃ。

まだ von Mangoldt 関数そのものではない。
しかし、prime-power label の base prime \(p\) を読む route と接続すれば、まさに

$$
\frac{\log p}{\log n}
$$

型の有限 Markov 的重みへ進める。

## 4. 現在地

いまの R 版はこうじゃ。

| Phase      | 内容                                    | 状態   |
| ---------- | ------------------------------------- | ---- |
| Phase-R001 | real ratio weight 語彙                  | 完了   |
| Phase-R002 | real finite budget lemma              | 完了   |
| Phase-R003 | `RealWeightProvider` prototype        | 完了   |
| Phase-R004 | `Real.log` 正値性                        | 完了   |
| Phase-R005 | `RealLogBudget` と log ratio sum bound | 完了   |
| Phase-R006 | index 上の log numerator 非負性            | 完了   |
| Phase-R007 | `log p / log n` provider              | 今回完了 |
| Phase-R008 | `RealLogBudget` の起源設計                 | 未    |

ここで一段、明確に到達した。

$$
\boxed{
\text{外部 log budget があれば、log-ratio provider は sub-probability}
}
$$

これが no-sorry で通ったわけじゃ。

## 5. 何がまだ本丸か

次の本丸は、やはり

$$
RealLogBudget(I,pOf,n)
$$

をどこから導くかじゃ。

つまり、

$$
\sum_{q\in I}\log(pOf(q))\le \log n
$$

を、どの数論構造から出すか。

候補は、

$$
\prod_{q\in I}pOf(q)\le n
$$

から、

$$
\log\left(\prod_{q\in I}pOf(q)\right)\le \log n
$$

を経由し、

$$
\sum_{q\in I}\log(pOf(q))\le \log n
$$

へ進む道じゃ。

ただし、ここでは三つの問題がある。

第一に、有限積の正性。

$$
1\le pOf(q)
$$

または

$$
2\le pOf(q)
$$

が必要になる。

第二に、log の積公式。

$$
\log\left(\prod_q p_q\right)=\sum_q\log p_q
$$

を使うには正値性が必要になる。

第三に、重複制御。

同じ base prime が複数回出るなら、

$$
\prod_q pOf(q)
$$

がどの程度 \(n\) を割る、または \(n\) 以下であるかを制御せねばならぬ。

ここが本物の登攀部じゃな。

## 6. 次の一手: Phase-R008

次は、いきなり大定理にせず、設計を小補題に分解するのがよい。

Phase-R008 はまず、

```lean
RealLogBudget_of_product_le
```

の設計でよいと思う。

概念的にはこうじゃ。

$$
\forall q\in I,\ 1\le pOf(q)
$$

$$
\prod_{q\in I}pOf(q)\le n
$$

から、

$$
RealLogBudget(I,pOf,n)
$$

を出す。

ただし Lean では最初から `Nat` 積と `Real.log` の積公式に突っ込むと重い。
そこで、まずは実数版の補題を先に作るのが安全じゃ。

```lean
theorem real_log_sum_le_log_of_prod_le
    {ι : Type _}
    (I : Finset ι)
    (a : ι → ℝ)
    (ha : ∀ i, i ∈ I → 0 < a i)
    {N : ℝ}
    (hN : 0 < N)
    (hprod : (I.prod fun i => a i) ≤ N) :
    (I.sum fun i => Real.log (a i)) ≤ Real.log N
```

これは少し重い可能性がある。
だからさらに分けて、

$$
\sum\log a_i=\log\prod a_i
$$

の補題と、

$$
\prod a_i\le N\Rightarrow \log\prod a_i\le \log N
$$

の補題に分けるのが良い。

## 7. もっと安全な Phase-R008 案

わっちなら、次はまず doc / small lemma でこう分ける。

1. `RealLogBudget` を外部仮定として使う route は完了。
2. 次は `RealLogBudget` の供給方法を別ファイルか別 section に分離。
3. 最初の供給候補は product budget。
4. product budget はさらに、
   $$
   \sum\log = \log\prod
   $$
   と
   $$
   \log\text{ monotone}
   $$
   に分ける。

つまり Phase-R008 は、いきなり `PrimePowerWitnessProvider` に戻らず、

```lean
RealLogBudgetProduct.lean
```

のような小さな実験ファイルでもよい。

## 8. その次に prime-power route へ戻る

product budget が見えてから、ようやく既存の \(q=p^k\) route へ戻る。

そこで、

$$
pOf(q)=\text{base prime read from witness provider}
$$

とし、

$$
\prod_{q\in I}pOf(q)\le n
$$

をどのように得るかを見る。

このとき、`PrimePowerWitnessProvider` の \(p\) field が生きてくる。

つまり最終的な道はこうじゃ。

$$
PrimePowerWitnessProvider
$$

$$
\Downarrow
$$

$$
pOf(q)=W.label(n,q,hq).p
$$

$$
\Downarrow
$$

$$
\prod_q pOf(q)\le n
$$

$$
\Downarrow
$$

$$
RealLogBudget
$$

$$
\Downarrow
$$

$$
realLogRatioWeightProvider.SubProbability
$$

## 9. 総括

Phase-R007 は、R 版における **log-ratio finite provider 完成** じゃ。

これで、

$$
weight(q)=\frac{\log(pOf(q))}{\log n}
$$

を持つ `RealWeightProvider` ができた。
そして外部 budget

$$
\sum_q\log(pOf(q))\le \log n
$$

があれば、sub-probability になることも閉じた。

ここまでで、R 版は「実数比率表」から「本物の log-ratio weight」へ進んだ。
次の戦いは、budget の起源じゃ。

山で言えば、ついに \(\log p/\log n\) のザイルを実際に張った。
次は、そのザイルをどの岩、すなわちどの数論構造に固定するかを決める番じゃな。
