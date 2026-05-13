# review

## 1. 結論

うむ、Phase AG は **prime-power channel の構造体化** じゃ。
前回 Phase AF では、

$$
T.PrimePowerIndexed
$$

という predicate により「この divisor transition kernel の index は全状態で prime-power label だけ」という条件を表せるようになった。今回 Phase AG では、それを

```lean
structure PrimePowerDivisorTransitionKernel
```

として package 化した。つまり、prime-power channel 条件を毎回 theorem の仮定として渡すだけでなく、 **型のフィールドとして保持できる** ようになったわけじゃ。

## 2. 今回の主役

今回追加された中心構造はこれじゃ。

```lean
structure PrimePowerDivisorTransitionKernel where
  toDivisorTransitionKernel : DivisorTransitionKernel
  primePowerIndexed : toDivisorTransitionKernel.PrimePowerIndexed
```

これは非常に素直でよい。

数学的には、

$$
\text{DivisorTransitionKernel}
+
\forall n,\forall q\in index(n),\ q\text{ is prime-power}
$$

を一つに束ねた構造じゃ。

これにより、後続の channel / weight API は、

```lean
T : PrimePowerDivisorTransitionKernel
```

を受け取るだけで、

$$
q\in T.index(n)
\Rightarrow q=p^k
$$

という前提を内部フィールドから使える。

## 3. 何が強くなったか

前回までは、任意の indexed transition が prime-power descent であることを使うには、

```lean
T.PrimePowerIndexed
```

を別仮定として渡していた。

今回からは、

```lean
PrimePowerDivisorTransitionKernel.primePowerDescentStep_of_mem
```

により、package 化された kernel では、任意の indexed transition から直接

$$
\mathrm{PrimePowerDescentStep}; n; (T.next\ n\ q)
$$

が得られる。

つまり、

$$
q\in index(n)
\Rightarrow
n\to n/q
\text{ is prime-power descent}
$$

が、型から自動的に読めるようになった。

これは theorem-facing API として大きい。
後続で von Mangoldt 型 weight を扱うとき、「この index は $\Lambda$ が反応する prime-power channel だけである」という条件を、別証明ではなく入力型そのものに持たせられるからじゃ。

## 4. 既存 API への忘却もよい

今回、

```lean
toFiniteTransitionKernel
providerAt
totalWeightAt
SubProbability
CompatibleAt
```

も追加されておる。

これは重要じゃ。
`PrimePowerDivisorTransitionKernel` は新しい構造体だが、既存の

$$
\text{DivisorTransitionKernel}
\to
\text{FiniteTransitionKernel}
\to
\text{FiniteKernel}
\to
\text{WeightProvider}
\to
\text{WeightedPathFamily}
$$

という導線を壊しておらぬ。

つまり、prime-power channel 条件を追加しつつ、重み評価や sub-probability 評価は既存 skeleton に忘却して使える。

この設計はかなり良い。
「意味論を足すが、既存の証明機構は再利用する」という DkMath らしい薄い bridge になっておる。

## 5. sample の意味

今回の sample は、

```lean
sampleTenPrimePowerDivisorTransitionKernel
```

じゃ。

これは既存の

$$
10\xrightarrow{2}5,\qquad 10\xrightarrow{5}2
$$

を持つ `sampleTenDivisorTransitionKernel` に、全 index が prime-power label である証明を添えて package 化したものじゃ。

さらに、既存 sample の prime-power descent theorem も、

```lean
sampleTenPrimePowerDivisorTransitionKernel.primePowerDescentStep_of_mem
```

経由に切り替えられている。

これはよい。
「prime-power indexed である」という性質を外から渡すのではなく、構造体に詰めた状態で使えることが、実例でも確認された。

## 6. 現在地

ここまでの階層は、かなり美しく積み上がっている。

| 層                                           | 状態   |
| ------------------------------------------- | ---- |
| `FiniteTransitionKernel`                    | 完了   |
| `DivisorTransitionKernel`                   | 完了   |
| $q\mid n$, $next=n/q$                       | 完了   |
| prime label → `PrimeDescentStep`            | 完了   |
| prime-power label → `PrimePowerDescentStep` | 完了   |
| `IsPrimePowerLabel`                         | 完了   |
| `PrimePowerIndexOn` / `PrimePowerIndexed`   | 完了   |
| `PrimePowerDivisorTransitionKernel`         | 今回完了 |
| prime-power channel / weight API            | 未    |
| von Mangoldt 型 weight                       | 未    |
| 解析 weight                                   | 未    |

つまり、今回で **prime-power channel の型** ができた。
これは、 $\Lambda(q)$ を導入する前の最終的な通行路としてかなり重要じゃ。

## 7. 数学的な意味

Erdős #1196 の重みは、概念的には

$$
w(n,q)\approx \frac{\Lambda(q)}{\log n}
$$

じゃが、 $\Lambda(q)$ が非零になるのは $q$ が prime-power のときじゃ。

今回の `PrimePowerDivisorTransitionKernel` は、

$$
index(n)\subseteq {q : q\text{ is a prime power}}
$$

を型として表している。

つまり、まだ $\Lambda$ そのものはないが、

$$
\Lambda\text{ が乗るべき channel だけを持つ transition kernel}
$$

ができたことになる。

これは解析層に入る前の、かなり正しい中間層じゃな。

## 8. 次の一手

次は、History にもある通り **prime-power channel / weight API** の設計じゃ。

ただし、まだ本物の von Mangoldt weight や実数対数には入らぬ方がよい。

まずは有限 toy weight でよい。

たとえば、次のような層が自然じゃ。

```lean
structure PrimePowerWeightProvider where
  kernel : PrimePowerDivisorTransitionKernel
  weightProviderAt : ℕ → WeightProvider ℕ
  compatible : ...
```

あるいは、既存の `weight` を使うなら、より薄く、

```lean
def PrimePowerChannelWeight
    (T : PrimePowerDivisorTransitionKernel) : Prop := ...
```

のような predicate から始めるのもありじゃ。

わっちのおすすめは、まず重くせず、

```lean
def PrimePowerChannelOn
    (T : PrimePowerDivisorTransitionKernel) (n : ℕ) : Prop := True
```

のような空構造ではなく、実用的に、

```lean
def PrimePowerWeightSupported
    (T : PrimePowerDivisorTransitionKernel) : Prop :=
  ∀ n q, q ∉ T.toDivisorTransitionKernel.index n →
    T.toDivisorTransitionKernel.weight n q = 0
```

を検討することじゃ。

ただし現在の `weight` は index 外では theorem 的に使わない設計なので、まずは無理に support outside を固定せず、index 内だけで十分かもしれぬ。

## 9. 具体的な Phase AH 案

わっちなら次はこう切る。

**Phase AH: Prime-power channel route API**

目的は、`PrimePowerDivisorTransitionKernel` から既存 transition route に自然に入れる wrapper を作ることじゃ。

最低限ほしいのは、

```lean
def PrimePowerDivisorTransitionKernel.transitionPrimePathFamilyAt ...
```

または既存の `FiniteTransitionKernel` route に忘却する wrapper。

さらに、

```lean
theorem PrimePowerDivisorTransitionKernel.weightedHitMass_le_const_of_subprob ...
```

を置くと、後続で

$$
\text{prime-power transition kernel}
+
\text{sub-probability}
\Rightarrow
\text{weightedHitMass}\le C
$$

が直接読める。

ここでまだ $\Lambda$ は不要じゃ。
まず「prime-power channel 型でも既存 weighted bound が使える」という theorem-facing API を整える。

## 10. 総括

Phase AG は、素冪 label の通行規則を **正式な登山道の型** にした段階じゃ。

前回までは、

$$
T.PrimePowerIndexed
$$

という看板を別に持っていた。
今回からは、

$$
T : PrimePowerDivisorTransitionKernel
$$

そのものが「この道は prime-power labels だけを通す」と語る。

山で言えば、ついに **素冪専用ルート** が地図に正式登録された。
次は、その素冪専用ルートに重みを載せるための料金所、すなわち prime-power channel / weight API を整える番じゃな。
