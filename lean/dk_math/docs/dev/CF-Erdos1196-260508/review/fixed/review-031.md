# review

## 1. 結論

うむ、Phase AF は **prime-power channel 条件の state/kernel レベル化** じゃ。
前回 Phase AE では、個々の label $q$ に対して

$$
\mathrm{IsPrimePowerLabel}(q)
$$

を持てば `PrimePowerDescentStep` に進めるようになった。今回 Phase AF では、それをさらに持ち上げて、

$$
\forall q\in index(n),\quad \mathrm{IsPrimePowerLabel}(q)
$$

を `PrimePowerIndexOn` として、全状態版を `PrimePowerIndexed` として定義した。これで「この kernel の index はすべて von Mangoldt channel 候補である」と言える入口ができたわけじゃ。

## 2. 今回追加された核

中心定義はこの二つじゃ。

```lean
def DivisorTransitionKernel.PrimePowerIndexOn
    (T : DivisorTransitionKernel) (n : ℕ) : Prop :=
  ∀ q ∈ T.index n, IsPrimePowerLabel q

def DivisorTransitionKernel.PrimePowerIndexed
    (T : DivisorTransitionKernel) : Prop :=
  ∀ n, T.PrimePowerIndexOn n
```

数学的には、

$$
T.\mathrm{PrimePowerIndexOn}(n)
$$

は「状態 $n$ から出るすべての label が prime-power label」という条件。

$$
T.\mathrm{PrimePowerIndexed}
$$

は「全状態でそれが成り立つ」という条件じゃ。

これはかなり良い。
今までは各 theorem 呼び出しごとに

$$
\mathrm{IsPrimePowerLabel}(q)
$$

を個別に渡していた。今回からは、kernel/state 単位で prime-power channel 条件を持てる。

## 3. theorem の流れが強くなった

今回追加された theorem は、

```lean
primePowerDescentStep_of_primePowerIndexOn
primePowerDescentStep_of_primePowerIndexed
```

じゃな。

つまり、

$$
T.\mathrm{PrimePowerIndexOn}(n)
\quad\text{かつ}\quad
q\in T.index(n)
$$

から、

$$
\mathrm{PrimePowerDescentStep}; n; (T.next\ n\ q)
$$

が得られる。

全状態版なら、

$$
T.\mathrm{PrimePowerIndexed}
\quad\text{かつ}\quad
q\in T.index(n)
$$

だけで同じ結論が出る。

これは後続層で効く。
「この kernel は prime-power labels だけを出す」と一度仮定すれば、任意の遷移が prime-power descent として読めるからじゃ。

## 4. sample の意味

sample では、

```lean
sampleTenDivisorTransitionKernel_primePowerIndexOn_ten
sampleTenDivisorTransitionKernel_primePowerIndexed
```

が追加された。

これは状態 $10$ の index が $\{2,5\}$ であり、

$$
2=2^1,\qquad 5=5^1
$$

なので、すべて prime-power label であることを確認している。

さらに既存の sample prime-power descent theorem も、個別の `IsPrimePowerLabel` ではなく、全状態版 `PrimePowerIndexed` 経由に切り替わった。
これは API の使い方として正しい。低レベル witness から、kernel-level predicate へ視点が上がっておる。

## 5. 現在地

ここまでの divisor / transition skeleton はこうじゃ。

| 層                                           | 状態   |
| ------------------------------------------- | ---- |
| `FiniteTransitionKernel`                    | 完了   |
| `DivisorTransitionKernel`                   | 完了   |
| $q\mid n$, $next=n/q$                       | 完了   |
| prime label → `PrimeDescentStep`            | 完了   |
| prime-power label → `PrimePowerDescentStep` | 完了   |
| `IsPrimePowerLabel q`                       | 完了   |
| `PrimePowerIndexOn T n`                     | 今回完了 |
| `PrimePowerIndexed T`                       | 今回完了 |
| `PrimePowerDivisorTransitionKernel` 構造体     | 未    |
| von Mangoldt channel / weight               | 未    |

つまり、個別 label から state-level、さらに kernel-level へ prime-power 条件が持ち上がった。
これは $\Lambda(q)$ の前段としてかなり自然な整理じゃ。

## 6. 今回の数学的意味

Erdős #1196 の von Mangoldt downward process では、重みは概念的に

$$
w(n,q)\sim \frac{\Lambda(q)}{\log n}
$$

であり、 $\Lambda(q)$ が非零になるのは $q$ が prime-power のときじゃ。

今回の `PrimePowerIndexed` は、

$$
index(n)\subseteq {q : q\text{ is a prime power}}
$$

を表す条件になる。

つまり、まだ $\Lambda$ そのものは入っていないが、

$$
\Lambda\text{ が乗るべき channel だけを index にする}
$$

という有限構造が表現可能になった。

この意味で Phase AF は、解析 weight ではなく **channel selection** の層じゃな。

## 7. 次の一手

次は二択じゃ。

### A. predicate のまま進む

今のまま、

```lean
T.PrimePowerIndexed
```

を theorem の仮定として渡す。

これは軽い。構造体を増やさないので、当面の実装は楽じゃ。

### B. 構造体化する

```lean
structure PrimePowerDivisorTransitionKernel where
  toDivisorTransitionKernel : DivisorTransitionKernel
  primePowerIndexed : toDivisorTransitionKernel.PrimePowerIndexed
```

として package 化する。

わっちは **B を推す** 。
理由は、ここから channel / weight API に進むなら、「prime-power label だけを持つ divisor transition kernel」を一つの型として持った方が theorem 文が締まるからじゃ。

## 8. Phase AG 案

次はこうじゃ。

```lean
structure PrimePowerDivisorTransitionKernel where
  toDivisorTransitionKernel : DivisorTransitionKernel
  primePowerIndexed : toDivisorTransitionKernel.PrimePowerIndexed
```

最低限ほしい wrapper は、

```lean
def toFiniteTransitionKernel :
    FiniteTransitionKernel ℕ ℕ

def providerAt (T : PrimePowerDivisorTransitionKernel) (n : ℕ) :
    WeightProvider ℕ

def SubProbability (T : PrimePowerDivisorTransitionKernel) : Prop :=
    T.toDivisorTransitionKernel.SubProbability
```

そして主 theorem は、

```lean
theorem primePowerDescentStep_of_mem
    (T : PrimePowerDivisorTransitionKernel)
    {n q : ℕ}
    (hq : q ∈ T.toDivisorTransitionKernel.index n) :
    PrimePowerDescentStep n (T.toDivisorTransitionKernel.next n q)
```

中身は今回の

```lean
primePowerDescentStep_of_primePowerIndexed
```

を呼ぶだけでよい。

## 9. その次に見える層

`PrimePowerDivisorTransitionKernel` ができたら、いよいよ weight/channel 側へ進める。

ただし、まだ実数対数や $\Lambda$ 本体に入る前に、有限 skeleton として次を考えるのが安全じゃ。

```lean
structure PrimePowerWeightProvider ...
```

または

```lean
def vonMangoldtLikeWeight : ℕ → ℕ → ℚ
```

ただし最初は本物の $\Lambda(q)$ ではなく、prime-power label にだけ非零になる **有限 toy weight** でよい。

つまり順序は、

$$
\text{PrimePowerIndexed}
\to
\text{PrimePowerDivisorTransitionKernel}
\to
\text{prime-power channel weight}
\to
\text{von Mangoldt-like finite weight}
\to
\text{analytic weight}
$$

じゃ。

## 10. 総括

Phase AF は、素冪 label を **個別通行証** から **全 index の通行規則** へ持ち上げた段階じゃ。

これで、

$$
q\in T.index(n)
\Rightarrow
q\text{ is prime-power}
\Rightarrow
n\to n/q\text{ is prime-power descent}
$$

が kernel/state 単位で扱える。

山で言えば、前回までは各登山者が「素冪道通行証」を見せていた。
今回からは、そもそもこの登山道の入口には **素冪通行証を持つ者しか入れない** と看板が立った。
次は、その看板付き登山道を `PrimePowerDivisorTransitionKernel` として一つの正式ルートにまとめる番じゃな。
