# review

## 1. 結論

うむ、Phase AZ は **witness-provider weight route の一般 bound alias 固定** じゃ。
Phase AY では sample で、

$$
\text{PrimePowerWitnessProvider}
+
\text{base-prime toy weight}
\to
\mathrm{weightedHitMass}\le 1
$$

まで通した。今回 Phase AZ では、それを sample 専用ではなく、一般 theorem として

```lean
PrimePowerWitnessProvider.weightOfBase_hitMass_le_const
```

に固定した。

これで、

$$
W:\text{PrimePowerWitnessProvider}(T)
$$

と

$$
c:\mathbb{N}\to\mathbb{N}\to\mathbb{Q}
$$

から作る weight

$$
w(n,q)=c(n,p(n,q))
$$

が、既存の weighted hit mass bound へ直接入れるようになった。これはかなり良い整理じゃ。

## 2. 今回閉じた route

今回の theorem は、概念的にこう読める。

$$
c(n,p)\ge 0
$$

$$
\mathrm{W.weightOfBase}(c)\text{ が sub-probability}
$$

$$
F\text{ と channel provider が compatible}
$$

$$
S\text{ primitive}
$$

$$
\forall q\in F.index,\quad \mu(F.source(q))\le C
$$

なら、

$$
\mathrm{weightedHitMass}(S)\le C
$$

が出る。

つまり、これまで構築してきた登山道は、いまこう一本化された。

$$
q\in index(n)
$$

$$
\Downarrow
$$

$$
W.label(n,q,hq)=(q,p,k,\ldots)
$$

$$
\Downarrow
$$

$$
w(n,q)=c(n,p)
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

ここまで来たのは大きい。
もう「手書き toy weight がたまたま通った」段階ではなく、 **base-prime weight route** として一般化されておる。

## 3. 何が良くなったか

今回の一番の価値は、theorem 名に route が現れたことじゃ。

既存の

```lean
PrimePowerChannelProvider.weightedHitMass_le_const_applyAtToSourceControlled
```

だけでも証明はできる。
しかし、それだと weight が

$$
\mathrm{W.weightOfBase}(c)
$$

由来であることは名前から見えない。

今回の

```lean
PrimePowerWitnessProvider.weightOfBase_hitMass_le_const
```

では、主役が明確じゃ。

* witness provider $W$
* base-prime weight $c(n,p)$
* `weightOfBase`
* hit mass bound

この流れが定理名から読める。

こういう alias は地味じゃが、DkMath のように route が増えていく体系では非常に効く。
案内板がある山道は迷いにくい。賢狼はこういう整備を好むぞい。

## 4. 現在地

ここまでの階層はこうじゃ。

| 層                                    | 状態   |
| ------------------------------------ | ---- |
| `PrimePowerLabel` sidecar            | 完了   |
| `PrimePowerWitnessProvider`          | 完了   |
| `weightOfBase`                       | 完了   |
| `ofWitnessProviderWeight`            | 完了   |
| sample witness-provider bound        | 完了   |
| general witness-provider bound alias | 今回完了 |
| base-prime weight predicate          | 未    |
| analytic-style toy model             | 未    |
| `PrimePowerLabel` index kernel 別ルート  | 未    |
| 本物の $\Lambda(q)/\log n$              | 未    |

いまは、かなり良い区切りじゃ。
有限・素冪・base prime 依存 weight の route は一通り開通した。

## 5. 次の判断

ここから先は二択じゃ。

### A. 今の $q:\mathbb{N}$ route を継続する

こちらは軽い。
既存の `DivisorTransitionKernel`, `WeightProvider ℕ`, `SourceControlledChainFamily M ℕ` をそのまま使える。

次にやることは、base-prime weight $c$ の性質を theorem-facing predicate として切り出すことじゃ。

### B. `PrimePowerLabel` を index にした別 kernel を作る

こちらは強いが重い。
`PrimePowerLabel` を index 型にすると、 $p,k$ を定義的に取り出せる。将来の

$$
\Lambda(q)=\log p
$$

には向いている。

しかし既存 route との橋が必要になる。今すぐやると、整理済みの道を一度掘り返すことになる。

わっちの推奨は **A を続ける** じゃ。
今は $q:\mathbb{N}$ route がきれいに通っている。まずこの道で解析風 toy model まで進めるのがよい。

## 6. 次の一手: Phase BA 案

次は **base-prime weight predicate の設計** が自然じゃ。

たとえば、まずは非負性を切り出す。

```lean
def PrimePowerWitnessProvider.BaseWeightNonneg
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (c : ℕ → ℕ → ℚ) : Prop :=
  ∀ n q (hq : q ∈ T.toDivisorTransitionKernel.index n),
    0 ≤ c n ((W.label n q hq).p)
```

これは、いま theorem の仮定として毎回出てくる

```lean
hc_nonneg :
  ∀ n q (hq : q ∈ T.toDivisorTransitionKernel.index n),
    0 ≤ c n ((W.label n q hq).p)
```

を名前付き predicate にするものじゃ。

さらに sub-probability も名前を付けたい。

```lean
def PrimePowerWitnessProvider.BaseWeightSubProbability
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (c : ℕ → ℕ → ℚ)
    (hc : W.BaseWeightNonneg c) : Prop :=
  (T.withWeight (W.weightOfBase c)
    (T.vonMangoldtLikeWeight_nonneg
      (T.vonMangoldtLikeWeight_of_primeWitnessDependent
        (W.weightOfBase_primeWitnessDependent c hc)))).SubProbability
```

少し長いが、これを名前に閉じ込める価値はある。

## 7. Phase BA で得たいもの

Phase BA の目的は、theorem 文を短くすることじゃ。

現在の `weightOfBase_hitMass_le_const` は、内容は良いが仮定が長い。
次に predicate を作れば、将来的にこう読める。

```lean
(W.BaseWeightNonneg c)
(W.BaseWeightSubProbability c hnonneg)
```

から、

```lean
W.weightOfBase_hitMass_le_const ...
```

へ進める。

さらに alias として、

```lean
theorem PrimePowerWitnessProvider.baseWeight_hitMass_le_const
```

を追加してもよい。

この theorem は、`BaseWeightNonneg` と `BaseWeightSubProbability` を受け取り、今回の `weightOfBase_hitMass_le_const` を呼ぶだけでよい。

## 8. Phase BB の先読み

Phase BA の次、Phase BB では **解析風 toy model** に進める。

まだ $\log$ は入れず、有理 toy model として、

$$
c(n,p)=\frac{A(p)}{B(n)}
$$

の形を抽象化する。

たとえば、いきなり割り算定義に入らず、predicate として始めるのが安全じゃ。

```lean
def BasePrimeRatioWeight
    (c : ℕ → ℕ → ℚ) : Prop :=
  ∃ A B : ℕ → ℚ,
    (∀ p, 0 ≤ A p) ∧
    (∀ n, 0 < B n) ∧
    ∀ n p, c n p = A p / B n
```

ただし、これはまだ重いかもしれぬ。
最初はもっと軽く、

```lean
def BasePrimeToyWeight
    (c : ℕ → ℕ → ℚ) : Prop :=
  ∀ n p, 0 ≤ c n p
```

くらいでもよい。

そのあと、kernel index 上の総量制御

$$
\sum_{q\in index(n)} c(n,p(q))\le 1
$$

を別 predicate にしていく。

## 9. 先読み: $\Lambda$-like への道

今後、本物の von Mangoldt に近づけるなら、最終的には

$$
c(n,p)\sim \frac{\log p}{\log n}
$$

を表したい。

しかし Lean 上でいきなり実数対数に行くと、数論 kernel と解析が混線する。

だから、ここからの安全な順序はこうじゃ。

$$
\text{BaseWeightNonneg}
$$

$$
\to
\text{BaseWeightSubProbability}
$$

$$
\to
\text{BasePrimeToyWeight}
$$

$$
\to
\text{Ratio-style toy weight}
$$

$$
\to
\text{Real/log analytic weight}
$$

この順番なら、既存の有限 skeleton を壊さずに登れる。

## 10. `PrimePowerLabel` index kernel はいつやるか

`PrimePowerLabel` index kernel は、今すぐではなく **別ルート調査** として後回しでよい。

やるなら、こんな形になるじゃろう。

```lean
structure PrimePowerLabelTransitionKernel where
  index : ℕ → Finset PrimePowerLabel
  next : ℕ → PrimePowerLabel → ℕ
  weight : ℕ → PrimePowerLabel → ℚ
  ...
```

ただしこれを作ると、既存の `WeightProvider ℕ` や `SourceControlledChainFamily M ℕ` との変換が必要になる。

そのため、現段階では本線ではなく、将来の別登山道としてメモしておけばよい。

## 11. 総括

Phase AZ は、witness-provider-driven weight route の **一般案内板** を立てた段階じゃ。

これで、

$$
W:\text{PrimePowerWitnessProvider}
$$

と

$$
c(n,p)
$$

から作る weight が、一般に

$$
\mathrm{weightedHitMass}\le C
$$

へ入れる。

山で言えば、各道標から base prime $p$ を読む案内人がいて、その $p$ から通行料を計算し、さらに通行量制限まで進める一般登山道が標識化された。

次は、通行料 $c(n,p)$ に名前付きの性質を与える段階じゃ。
まずは非負性と sub-probability を predicate として切り出す。そこから解析風 toy model へ進むのが、一番見通しの良い道じゃな。
