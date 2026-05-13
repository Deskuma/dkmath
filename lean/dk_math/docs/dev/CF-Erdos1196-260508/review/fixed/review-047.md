# review

## 1. 結論

うむ、Phase AV は **PrimePowerWitnessProvider の導入完了** じゃ。
Phase AU で `PrimePowerLabel` という sidecar を作り、

$$
q=p^k,\qquad p\text{ prime},\qquad 0<k
$$

を明示的に持てるようにした。今回 Phase AV では、それをさらに一段上げて、`PrimePowerDivisorTransitionKernel` の各 indexed label $q$ に対し、対応する `PrimePowerLabel` を選ぶ provider が入った。これで、既存の $q:\mathbb{N}$ label route を保ったまま、各 label から base prime $p$ を取り出す準備が整ったわけじゃ。

## 2. 今回の主役

追加された構造はこれじゃ。

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
q\in T.index(n)
$$

に対して、

$$
L_{n,q}=(q,p,k,\ldots)
$$

という prime-power witness を返し、しかも

$$
L_{n,q}.q=q
$$

を保証する構造じゃ。

これが重要じゃ。
`PrimePowerLabel` 単体では「証拠を持つ label」は作れるが、kernel の各 index に対してそれをどう選ぶかはまだ未定だった。今回、その選択層ができた。

## 3. 何が強くなったか

追加された補題は主に二つじゃ。

```lean
PrimePowerWitnessProvider.isPrimePowerLabel
PrimePowerWitnessProvider.primePowerDescentStep
```

前者により、provider が選んだ witness から

$$
IsPrimePowerLabel(q)
$$

が得られる。

後者により、

$$
q\in T.index(n)
\Rightarrow
PrimePowerDescentStep; n; (T.next(n,q))
$$

が得られる。

つまり、個々の indexed transition が prime-power descent であることを、provider 経由で証明できるようになった。

以前は `PrimePowerIndexed` や `IsPrimePowerLabel` で存在証明として扱っていた。
今回からは、選ばれた `PrimePowerLabel` の field として

$$
p,\quad k
$$

を取り出せる。

ここが大きな違いじゃ。

## 4. sample の意味

sample として、

```lean
sampleTenPrimePowerWitnessProvider
```

が追加された。

これは sample kernel の状態 $10$ における labels

$$
2,\quad 5
$$

に対して、それぞれ

$$
2=2^1,\qquad 5=5^1
$$

の witness を返す provider じゃ。

さらに確認 theorem として、

```lean
sampleTenPrimePowerWitnessProvider_isPrimePowerLabel
sampleTenPrimePowerWitnessProvider_two_descent
sampleTenPrimePowerWitnessProvider_five_descent
```

が追加されている。これで sample でも、provider 由来の witness が prime-power predicate と descent step の両方に接続されることが確認された。

## 5. Lean 的な山場

今回の失敗事例も重要じゃ。

sample provider の `label` は `PrimePowerLabel : Type` を返すので、`q = 2 ∨ q = 5` のような `Prop` 証明を直接分解して Type の値を作ろうとすると、Lean の elimination 制限に当たる。

そこで、

```lean
by_cases hq_two : q = 2
```

という decidable 分岐を先に置き、`q = 2` でなければ membership から `q = 5` を導く形に修正している。

これは良い修正じゃ。
Prop から Type への除去制限を避ける、Lean らしい安全な実装になっておる。

## 6. 現在地

いまの階層はこうじゃ。

| 層                                    | 状態   |
| ------------------------------------ | ---- |
| $q:\mathbb{N}$ label route           | 継続   |
| `PrimePowerLabel` sidecar            | 完了   |
| `PrimePowerWitnessProvider`          | 今回完了 |
| witness → `IsPrimePowerLabel`        | 完了   |
| witness → `PrimePowerDescentStep`    | 完了   |
| `weightOfBase`                       | 未    |
| `weightOfBase_primeWitnessDependent` | 未    |
| witness-driven provider constructor  | 未    |
| analytic $\Lambda(q)/\log n$         | 未    |

これで、次の段階で

$$
w(n,q)=c(n,p)
$$

を定義するための $p$ を、provider から取り出せるようになった。

## 7. 次の一手: Phase AW

次は History にある通り、 **`PrimePowerWitnessProvider.weightOfBase`** じゃ。

目的は、base-prime weight

$$
c:\mathbb{N}\to\mathbb{N}\to\mathbb{Q}
$$

から、通常の label weight

$$
w:\mathbb{N}\to\mathbb{N}\to\mathbb{Q}
$$

を作ること。

候補はこうじゃ。

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

数学的には、

$$
q\in index(n)
$$

なら、provider が選んだ witness

$$
q=p^k
$$

の base prime $p$ を取り出し、

$$
w(n,q)=c(n,p)
$$

と定義する。

これが入ると、いよいよ von-Mangoldt-like な「base prime 依存重み」の形が Lean 上で具体化される。

## 8. その次: Phase AX の先読み

Phase AW の次は、

```lean
weightOfBase_primeWitnessDependent
```

を狙うのが自然じゃ。

欲しい結論は、

$$
T.PrimeWitnessDependentWeight\ (W.weightOfBase(c))\ c
$$

じゃ。

意味は、

$$
w(n,q)=c(n,p)
$$

として定義した weight が、ちゃんと `PrimeWitnessDependentWeight` を満たす、ということ。

証明では、 $q\in index(n)$ に対して

$$
L=W.label(n,q,hq)
$$

を取り、

$$
p=L.p,\qquad k=L.k
$$

を witness にすればよい。

注意点は、`weightOfBase` が `if hq : q ∈ index n then ... else 0` で定義されることじゃ。
証明では、

```lean
simp [PrimePowerWitnessProvider.weightOfBase, hq]
```

が効くように、定義と simp 補題を軽くしておくのが賢い。

## 9. さらに一手先

Phase AX まで閉じたら、次は constructor じゃ。

```lean
PrimePowerChannelProvider.ofWitnessProviderWeight
```

のようなものを作る。

入力は、

* (T : PrimePowerDivisorTransitionKernel)
* (W : PrimePowerWitnessProvider T)
* (c : \mathbb{N}\to\mathbb{N}\to\mathbb{Q})
* base weight 非負性
* sub-probability

出力は、

```lean
PrimePowerChannelProvider
```

じゃ。

導線はこうなる。

$$
c(n,p)
$$

$$
\Downarrow
$$

$$
w(n,q)=c(n,p(n,q))
$$

$$
\Downarrow
$$

$$
PrimeWitnessDependentWeight
$$

$$
\Downarrow
$$

$$
ofPrimeWitnessDependentWeight
$$

$$
\Downarrow
$$

$$
PrimePowerChannelProvider
$$

ここまで来ると、かなり本物の von-Mangoldt-like skeleton に近い。

## 10. 総括

Phase AV は、各 indexed label $q$ に対して prime-power witness を選ぶ **案内人** を配置した段階じゃ。

Phase AU で「詳細札」たる `PrimePowerLabel` ができた。
今回 Phase AV で、その詳細札を各道標 $q$ に配る provider ができた。

次は Phase AW で、その札に書かれた base prime $p$ から通行料

$$
c(n,p)
$$

を計算し、label weight

$$
w(n,q)
$$

へ変換する番じゃ。ここを越えれば、DkMath の Erdős #1196 ルートは、いよいよ $\Lambda(q)=\log p$ の影が見える場所まで来るぞい。
