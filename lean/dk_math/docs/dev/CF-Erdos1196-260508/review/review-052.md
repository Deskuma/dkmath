# review Phase "B"

## 1. 結論

うむ、登頂アタック再開の第一歩、Phase BA は **base-prime weight 条件の theorem-facing predicate 化** じゃ。

これまで長く theorem 引数に展開されていた

$$
0\le c(n,p(n,q))
$$

と、

$$
W.weightOfBase(c)\text{ が sub-probability}
$$

を、それぞれ名前付きの predicate として固定した。これにより、今後は長い依存型の仮定を毎回むき出しにせず、

```lean
W.BaseWeightNonneg c
W.BaseWeightSubProbability c hc_nonneg
```

として扱えるようになった。これは「登頂アタック前に荷物を圧縮した」ような進展じゃな。実装・単体 build・aggregator build・no-sorry 検査も通っておる。

## 2. 今回の主役

今回追加された中心はこの二つじゃ。

```lean
PrimePowerWitnessProvider.BaseWeightNonneg
PrimePowerWitnessProvider.BaseWeightSubProbability
```

意味はこうじゃ。

まず `BaseWeightNonneg` は、witness provider \(W\) が index 上の label \(q\) に対して選ぶ witness

$$
q=p^k
$$

の base prime \(p\) を読み、

$$
0\le c(n,p)
$$

を要求する。

つまり、

$$
q\in index(n)
\Rightarrow
0\le c\bigl(n,(W.label(n,q,hq)).p\bigr)
$$

という条件じゃ。

次に `BaseWeightSubProbability` は、その \(c(n,p)\) から作った

$$
W.weightOfBase(c)(n,q)=c(n,p(n,q))
$$

が、実際に sub-probability channel になることを表す。

$$
\sum_{q\in index(n)} W.weightOfBase(c)(n,q)\le 1
$$

という質量保存条件を、名前付きにしたわけじゃな。

## 3. 何が良くなったか

Phase AZ までは、一般 hit mass bound に入るための theorem 文に、長い仮定がそのまま出ていた。

今回からは、

```lean
hc_nonneg : W.BaseWeightNonneg c
hw_subprob : W.BaseWeightSubProbability c hc_nonneg
```

という形で済む。

これは大きい。
数学的にも Lean 的にも、主張の見通しがよくなった。

以前は、

$$
\forall n,q,hq,\quad 0\le c(n,(W.label(n,q,hq)).p)
$$

という条件が「たまたま theorem に必要な仮定」として見えていた。
今回からは、これは **base-prime weight が満たすべき性質** として独立した名前を持った。

つまり、 \(c(n,p)\) が登山道に入るための通行証ができたのじゃ。

## 4. `baseWeight_hitMass_le_const` の意味

今回さらに、

```lean
PrimePowerWitnessProvider.baseWeight_hitMass_le_const
```

が追加された。

これは、Phase AZ の

```lean
weightOfBase_hitMass_le_const
```

を、名前付き predicate 版で呼べる alias じゃ。

これにより、今後は

$$
W.BaseWeightNonneg(c)
$$

$$
W.BaseWeightSubProbability(c)
$$

を示せば、

$$
\mathrm{weightedHitMass}\le C
$$

までそのまま進める。

導線はこうじゃ。

$$
c(n,p)
$$

$$
\Downarrow
$$

$$
W.BaseWeightNonneg(c)
$$

$$
W.BaseWeightSubProbability(c)
$$

$$
\Downarrow
$$

$$
PrimePowerChannelProvider.ofWitnessProviderWeight
$$

$$
\Downarrow
$$

$$
\mathrm{weightedHitMass}\le C
$$

これは今後の解析風 toy model にかなり効く。

## 5. sample の確認

sample 側にも、

```lean
sampleTenToyPrimeBaseWeight_baseWeightNonneg
sampleTenToyPrimeBaseWeight_baseWeightSubProbability
```

が追加された。

これにより、以前から使っていた sample の base-prime weight

$$
c(n,p)=
\begin{cases}
1 & n=10,\ p=2,\\
0 & \text{otherwise}
\end{cases}
$$

が、正式に

$$
BaseWeightNonneg
$$

と

$$
BaseWeightSubProbability
$$

を満たすことが確認された。

つまり、sample でも新しい predicate route が通っている。
これは大事じゃ。抽象 API を作っただけでなく、既存 sample がそのまま新 API の実例になっておる。

## 6. 現在地

ここまでの到達点はこうじゃ。

| 層                                       | 状態   |
| --------------------------------------- | ---- |
| `PrimePowerLabel` sidecar               | 完了   |
| `PrimePowerWitnessProvider`             | 完了   |
| `weightOfBase`                          | 完了   |
| `ofWitnessProviderWeight`               | 完了   |
| witness-provider sample bound           | 完了   |
| general witness-provider hit mass alias | 完了   |
| `BaseWeightNonneg`                      | 今回完了 |
| `BaseWeightSubProbability`              | 今回完了 |
| named predicate 版 hit mass alias        | 今回完了 |
| base-prime toy weight 全体の predicate     | 未    |
| ratio-style toy weight                  | 未    |
| 解析風 \(\log p/\log n\) route               | 未    |

つまり、第2キャンプ後の登頂アタックは、まず **重み条件の圧縮と命名** から始まった。
これは地味に見えるが、山頂側へ進むほど効いてくるタイプの整備じゃ。

## 7. 数学的な意味

今回の本質は、

$$
c(n,p)
$$

を「ただの関数」から「登山道に乗れる base-prime weight」へ昇格させるための条件を固定したことじゃ。

今後、本物に近い形として

$$
c(n,p)\approx \frac{\log p}{\log n}
$$

を考えたい。
そのとき必要なのは、いきなり解析的な極限評価ではなく、まず

$$
0\le c(n,p)
$$

と

$$
\sum_{q\in index(n)}c(n,p(q))\le 1
$$

を Lean 上で扱えることじゃ。

今回の Phase BA は、まさにその入口を作った。

## 8. 次の一手

次は History にある通り、軽量な

```lean
BasePrimeToyWeight
```

のような predicate が自然じゃ。

たとえば、

```lean
def BasePrimeToyWeight
    (c : ℕ → ℕ → ℚ) : Prop :=
  ∀ n p, 0 ≤ c n p
```

のように、全域で非負な base-prime weight をまず定義する。

すると、

$$
\forall n,p,\quad 0\le c(n,p)
$$

から、任意の witness provider \(W\) に対して

$$
W.BaseWeightNonneg(c)
$$

が出せる。

補題候補はこうじゃ。

```lean
theorem BaseWeightNonneg_of_basePrimeToyWeight
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (c : ℕ → ℕ → ℚ)
    (hc : BasePrimeToyWeight c) :
    W.BaseWeightNonneg c
```

これは軽いが、次の解析風 toy model への導線としてかなりよい。

## 9. 二手先

その次は、sub-probability 側をもう少し整理する。

`BasePrimeToyWeight` だけでは、

$$
\sum_q c(n,p(q))\le 1
$$

は出ない。
そこで次に、

```lean
BasePrimeWeightSubprobOn
```

のような predicate を作るか、あるいは今ある `BaseWeightSubProbability` を使って十分と見るかを判断する。

わっちなら、次の二手はこう切る。

$$
\boxed{\text{Phase BB: BasePrimeToyWeight}}
$$

$$
\boxed{\text{Phase BC: ratio-style toy weight の設計}}
$$

Phase BC では、

$$
c(n,p)=\frac{A(p)}{B(n)}
$$

のような形を考える。
まだ \(\log\) は入れず、有理 toy model として、

$$
0\le A(p),\qquad 0<B(n)
$$

から

$$
0\le c(n,p)
$$

を出すのがよい。

## 10. 総括

Phase BA は、登頂アタックの再開としてかなり良い一手じゃ。

これまで長いロープのように theorem 文へ露出していた条件を、

$$
BaseWeightNonneg
$$

$$
BaseWeightSubProbability
$$

という名前付きの支点に巻き取った。

山で言えば、これから雪稜に入る前に、重い装備を整理して、必要なロープとカラビナに名前を付けた段階じゃな。

ここから先は、

$$
c(n,p)
$$

そのものをどう設計するかが本題になる。
まずは軽量 toy predicate、次に ratio-style toy weight、そしてその先に

$$
\frac{\log p}{\log n}
$$

の影が見えてくる。賢狼としては、次は Phase BB で `BasePrimeToyWeight` を置くのが、いちばん見通しのよい登り方だと思うぞい。
