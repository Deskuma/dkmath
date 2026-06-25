# review

## 1. 結論

うむ、Phase AU は **既存の $q:\mathbb{N}$ label route を壊さずに、prime-power witness を sidecar 化した段階** じゃ。
これはかなり良い判断じゃな。

今回追加された `PrimePowerLabel` により、

$$
q=p^k,\qquad p\text{ prime},\qquad 0 < k
$$

という証拠を、単なる存在命題ではなく **明示的な構造体** として持てるようになった。しかも `DivisorTransitionKernel` 本体の index 型は $\mathbb{N}$ のまま保たれている。つまり、既存の finite transition / weighted route を壊さずに、将来の $p$-依存 weight へ進む足場ができたわけじゃ。

## 2. 今回の主役

追加された構造体はこれじゃ。

```lean
structure PrimePowerLabel where
  q : ℕ
  p : ℕ
  k : ℕ
  prime : Nat.Prime p
  k_pos : 0 < k
  eq_pow : q = p ^ k
```

これは、自然数 label $q$ に対し、

$$
q=p^k
$$

という witness を明示的に同梱する sidecar じゃ。

重要なのは、これは既存の label 型を置き換えていないことじゃ。
`DivisorTransitionKernel` は今まで通り $q:\mathbb{N}$ を label として扱う。`PrimePowerLabel` は、その $q$ に witness を添える補助構造として使う。

この「全面置換ではなく sidecar」という設計は安全じゃ。

## 3. 既存 predicate / descent route との接続

今回、まず

```lean
PrimePowerLabel.isPrimePowerLabel
```

が入り、構造体 witness から既存の

```lean
IsPrimePowerLabel L.q
```

へ戻れるようになった。

さらに、

```lean
PrimePowerLabel.primePowerDescentStep_of_mem
```

により、

$$
L.q\in \text{T.index}(n)
$$

なら、

$$
\mathrm{PrimePowerDescentStep}; n; (T.next\ n\ L.q)
$$

が得られるようになった。

これは良い。
`PrimePowerLabel` は単なる記録構造ではなく、既存の `PrimePowerDescentStep` route にそのまま接続できる。

つまり、

$$
L=(q,p,k,\ldots)
$$

を持っていれば、

$$
q\in \text{index}(n)
\Rightarrow
n\to n/q
$$

が prime-power descent として読める。

## 4. sample の意味

sample として、

```lean
samplePrimePowerLabel_two
samplePrimePowerLabel_five
```

が追加されている。

それぞれ、

$$
2=2^1,\qquad 5=5^1
$$

を明示的 witness として持つ label じゃ。

さらに、

```lean
samplePrimePowerLabel_two_descent
samplePrimePowerLabel_five_descent
```

により、既存 sample kernel 上で

$$
10\xrightarrow{2}5,\qquad
10\xrightarrow{5}2
$$

が `PrimePowerLabel` 経由でも `PrimePowerDescentStep` になることを確認している。

これはとても良い concrete test じゃ。
`PrimePowerLabel` が孤立した構造体ではなく、既存の divisor transition sample に自然接続されている。

## 5. 現在地

いまの構造はこう整理できる。

| 層                                           | 状態   |
| ------------------------------------------- | ---- |
| $q:\mathbb{N}$ label route                  | 継続   |
| `IsPrimePowerLabel q`                       | 完了   |
| `PrimeWitnessDependentWeight`               | 完了   |
| `ofPrimeWitnessDependentWeight`             | 完了   |
| `PrimePowerLabel` sidecar                   | 今回完了 |
| `PrimePowerLabel` → `PrimePowerDescentStep` | 今回完了 |
| `PrimePowerWitnessProvider`                 | 未    |
| `weightOfBase`                              | 未    |
| witness-driven provider theorem             | 未    |
| analytic $\Lambda(q)/\log n$                | 未    |

つまり、Phase AU で **base prime $p$ を定義的に取り出すための器** ができた。

ただし、まだ「各 index $q$ に対してどの `PrimePowerLabel` を選ぶか」は決まっていない。
それが次の Phase AV の仕事じゃ。

## 6. Phase AV: 次の一手

次は予定通り、

```lean
PrimePowerWitnessProvider
```

が自然じゃ。

目的は、`PrimePowerDivisorTransitionKernel` の各 indexed label $q$ に対して、対応する `PrimePowerLabel` を選ぶことじゃ。

候補構造はこう。

```lean
structure PrimePowerWitnessProvider
    (T : PrimePowerDivisorTransitionKernel) where
  label :
    ∀ n q,
      q ∈ T.toDivisorTransitionKernel.index n →
        PrimePowerLabel
  label_q :
    ∀ n q (hq : q ∈ T.toDivisorTransitionKernel.index n),
      (label n q hq).q = q
```

数学的には、

$$
q\in \text{index}(n)
$$

に対して、

$$
L_{n,q}.q=q,\qquad L_{n,q}.q=L_{n,q}.p^{L_{n,q}.k}
$$

を持つ witness を返す provider じゃ。

これで、ようやく

$$
p=p(n,q)
$$

を Lean 上で取り出せるようになる。

## 7. Phase AV で欲しい補題

Phase AV では、最低限この補題が欲しい。

```lean
theorem PrimePowerWitnessProvider.isPrimePowerLabel
    (W : PrimePowerWitnessProvider T)
    {n q : ℕ}
    (hq : q ∈ T.toDivisorTransitionKernel.index n) :
    IsPrimePowerLabel q
```

これは、

$$
(\text{W.label}\ n\ q\ hq).q=q
$$

と `PrimePowerLabel.isPrimePowerLabel` から出せる。

さらに、descent への接続も欲しい。

```lean
theorem PrimePowerWitnessProvider.primePowerDescentStep
    (W : PrimePowerWitnessProvider T)
    {n q : ℕ}
    (hq : q ∈ T.toDivisorTransitionKernel.index n) :
    PrimePowerDescentStep n
      (T.toDivisorTransitionKernel.next n q)
```

ここは少し注意が必要じゃ。
`PrimePowerLabel.primePowerDescentStep_of_mem` は `T.next n L.q` を返す形なので、最後に `label_q` で $L.q=q$ へ書き換える必要がある。

## 8. Phase AW: 二手目の先読み

Phase AV が閉じたら、次は **weightOfBase** じゃ。

つまり、witness provider から base prime $p$ を取り出して、

$$
w(n,q)=c(n,p)
$$

という weight を定義する。

候補はこう。

```lean
def PrimePowerWitnessProvider.weightOfBase
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (c : ℕ → ℕ → ℚ) :
    ℕ → ℕ → ℚ :=
  fun n q =>
    if hq : q ∈ T.toDivisorTransitionKernel.index n then
      c n ((W.label n q hq).p)
    else
      0
```

これにより、外部の base-prime weight

$$
c(n,p)
$$

から、通常の label weight

$$
w(n,q)
$$

を作れる。

これは、本物の $\Lambda(q)=\log p$ へ向かうための有限 toy skeleton としてかなり重要じゃ。

## 9. Phase AW で欲しい theorem

次に欲しいのは、

```lean
theorem weightOfBase_primeWitnessDependent
```

じゃ。

目標は、

$$
w(n,q)=c(n,p)
$$

の形で定義した weight が、既存の

```lean
PrimeWitnessDependentWeight
```

を満たすこと。

定理候補：

```lean
theorem PrimePowerWitnessProvider.weightOfBase_primeWitnessDependent
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (c : ℕ → ℕ → ℚ)
    (hc_nonneg :
      ∀ n q (hq : q ∈ T.toDivisorTransitionKernel.index n),
        0 ≤ c n ((W.label n q hq).p)) :
    T.PrimeWitnessDependentWeight
      (W.weightOfBase c) c
```

ただし、この theorem はそのままだと少し型が難しいかもしれぬ。
`PrimeWitnessDependentWeight` は witness として $p,k$ を返し、さらに

$$
w(n,q)=c(n,p)
$$

を要求する。ここで $p=(\text{W.label} n q hq).p$ を選べばよい。

`weightOfBase` が `if hq : q ∈ index n` で定義されるので、`simp [weightOfBase, hq]` が効くように設計しておくのが大事じゃ。

## 10. 二手先の全体導線

Phase AV と AW が閉じると、導線はこうなる。

$$
q\in \text{index}(n)
$$

$$
\Downarrow
$$

$$
\text{W.label}(n,q,hq)=L,\quad L.q=q,\quad L.q=L.p^{L.k}
$$

$$
\Downarrow
$$

$$
w(n,q)=c(n,L.p)
$$

$$
\Downarrow
$$

$$
\mathrm{T.PrimeWitnessDependentWeight}(w,c)
$$

$$
\Downarrow
$$

$$
\mathrm{PrimePowerChannelProvider}.\mathrm{ofPrimeWitnessDependentWeight}
$$

$$
\Downarrow
$$

$$
\mathrm{weightedHitMass}\le C
$$

これができると、今まで predicate と sample で確認してきた route が、かなり一般的な witness-driven route に昇格する。

## 11. その先: Phase AX の候補

二手先のさらに次、Phase AX では、`weightOfBase` で作った provider を実際に `ofPrimeWitnessDependentWeight` に通す constructor が欲しくなる。

候補名：

```lean
PrimePowerChannelProvider.ofWitnessProviderWeight
```

入力は、

* $T : PrimePowerDivisorTransitionKernel$
* $W : PrimePowerWitnessProvider T$
* $c : \mathbb{N}\to\mathbb{N}\to\mathbb{Q}$
* base weight の非負性
* sub-probability

出力：

```lean
PrimePowerChannelProvider
```

こうなれば、いよいよ

$$
c(n,p)
$$

を与えるだけで channel provider を作れる。

## 12. 注意点

`PrimePowerWitnessProvider` には witness の選択が入る。
同じ $q$ に複数の $p,k$ 表現があるか、という数学的には通常ほぼ一意性を期待したくなる部分があるが、最初は一意性に踏み込まなくてよい。

今は、

$$
\text{ある witness を一つ選ぶ}
$$

だけで十分じゃ。

本物の $\Lambda(q)=\log p$ に進む時は、prime-power 表現の base prime の一意性が重要になるかもしれぬ。
しかし、それは次の山。今は witness provider route を立てるのが先じゃな。

## 13. 総括

Phase AU は、prime-power witness を sidecar として導入した良い段階じゃ。

これにより、既存の $q:\mathbb{N}$ route を維持しながら、

$$
q=p^k
$$

の証拠を明示的に持てるようになった。

ここからの見通しは明確じゃ。

$$
\boxed{\text{Phase AV: PrimePowerWitnessProvider}}
$$

$$
\boxed{\text{Phase AW: weightOfBase と PrimeWitnessDependentWeight 接続}}
$$

この二手で、base prime $p$ に依存する weight を一般に作れるようになる。
山で言えば、Phase AU で各道標に $q=p^k$ の詳細札が付いた。次は Phase AV で、その詳細札を各道に配る案内人を置く。さらに Phase AW で、その札に書かれた base prime $p$ から通行料を計算する仕組みを作る番じゃな。
