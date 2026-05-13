# review

## 1. 結論

うむ、Phase AD は **prime-power descent bridge 完了** じゃ。
Phase AC では prime label $q$ から `PrimeDescentStep` へ接続した。今回 Phase AD ではさらに、

$$
q=p^k,\qquad p\text{ prime},\qquad 0 < k
$$

という positive prime-power label から、

$$
\mathrm{PrimePowerDescentStep}; n; (T.next\ n\ q)
$$

を得られるようになった。これで divisor transition の $n\to n/q$ skeleton は、prime label と prime-power label の両方で既存 descent route に接続されたわけじゃ。

## 2. 今回の主役

追加された中心定理はこれじゃ。

```lean
theorem DivisorTransitionKernel.primePowerDescentStep_of_primePow_label
    (T : DivisorTransitionKernel) {n q p k : ℕ}
    (hqmem : q ∈ T.index n)
    (hp : Nat.Prime p)
    (hk : 0 < k)
    (hq : q = p ^ k) :
    PrimePowerDescentStep n (T.next n q)
```

数学的には、

$$
q\in index(n)
\Rightarrow q\mid n
$$

と

$$
next(n,q)=\frac{n}{q}
$$

を、仮定 $q=p^k$ で書き換えて、

$$
p^k\mid n,
\qquad
next(n,q)=\frac{n}{p^k}
$$

にしている。あとは `PrimePowerDescentStep` の witness として $p,k$ を渡せばよい。

証明が短いのも良い兆候じゃ。既存 API の分解がうまく効いておる。

## 3. 何が強くなったか

Phase AC までの導線は、

$$
q\in index(n),\quad q\text{ prime}
\Rightarrow
PrimeDescentStep(n,next(n,q))
$$

だった。

今回からは、

$$
q\in index(n),\quad q=p^k,\quad p\text{ prime},\quad 0 < k
\Rightarrow
PrimePowerDescentStep(n,next(n,q))
$$

も使える。

これは Erdős #1196 の実際の von Mangoldt 型 downward process に近い。
なぜなら $\Lambda(q)$ は、まさに $q=p^k$ のときに非零になるからじゃ。

まだ $\Lambda(q)$ や $\log$ は導入していない。
しかし、 $\Lambda$ が乗るべき **prime-power channel** の認識は、今回で Lean 上に入った。

## 4. sample の意味

今回追加された sample は、

```lean
sampleTenDivisorTransitionKernel_primePowerDescentStep_two
sampleTenDivisorTransitionKernel_primePowerDescentStep_five
```

じゃ。

これは、

$$
2=2^1,\qquad 5=5^1
$$

として、

$$
10\xrightarrow{2}5,
\qquad
10\xrightarrow{5}2
$$

が prime-power descent step でもあることを確認している。

prime label は prime-power label の $k=1$ 特殊例でもある。
この sample により、実例としてその接続が通っている。

## 5. 現在地

ここまでの finite transition / descent skeleton はこうじゃ。

| 層                                           | 状態   |
| ------------------------------------------- | ---- |
| `FiniteTransitionKernel`                    | 完了   |
| `DivisorTransitionKernel`                   | 完了   |
| $q\mid n$, $next=n/q$                       | 完了   |
| prime label → `PrimeDescentStep`            | 完了   |
| prime-power label → `PrimePowerDescentStep` | 今回完了 |
| prime-power label predicate                 | 未    |
| von Mangoldt channel                        | 未    |
| analytic weight $\Lambda(q)/\log n$         | 未    |

つまり、

$$
n\to \frac{n}{q}
$$

という除去因子遷移に対して、 $q$ が prime でも prime-power でも descent route に乗れるようになった。

## 6. 今回の位置づけ

これは **解析に入る前の最後の数論的ラベル付け** に近い。

これまで作ってきた skeleton は、

$$
\text{state}
\to
\text{index}
\to
\text{next state}
\to
\text{weight}
$$

だった。

今回の成果は、index $q$ に

$$
q=p^k
$$

という意味を持たせたとき、その transition が prime-power descent として読めるようになったことじゃ。

つまり、

$$
\text{finite transition label}
$$

が、

$$
\text{von Mangoldt が反応する prime-power label}
$$

へ近づいた。

## 7. 次の一手

次は History にある通り、`IsPrimePowerLabel` を切り出すのが自然じゃ。

```lean
def IsPrimePowerLabel (q : ℕ) : Prop :=
  ∃ p k, Nat.Prime p ∧ 0 < k ∧ q = p ^ k
```

そして今回の theorem を、直接 $p,k$ を渡す形だけでなく、

```lean
theorem primePowerDescentStep_of_isPrimePowerLabel
    (T : DivisorTransitionKernel) {n q : ℕ}
    (hqmem : q ∈ T.index n)
    (hqpp : IsPrimePowerLabel q) :
    PrimePowerDescentStep n (T.next n q)
```

のように呼べるようにするとよい。

これにより、後続の weight/channel 層では、

$$
q\text{ is prime power}
$$

だけを見ればよくなり、毎回 $p,k$ を明示的に分解しなくて済む。

## 8. その次に見える層

`IsPrimePowerLabel` が入ったら、次は channel API じゃな。

たとえば、

```lean
structure PrimePowerChannel where
  q : ℕ
  isPrimePower : IsPrimePowerLabel q
```

または divisor transition に寄せて、

```lean
def PrimePowerIndexOn (T : DivisorTransitionKernel) (n : ℕ) : Prop :=
  ∀ q ∈ T.index n, IsPrimePowerLabel q
```

のような形が考えられる。

これがあると、

$$
index(n)\text{ は prime-power labels だけ}
$$

という有限 kernel を定義できる。
その後でようやく、

$$
w(n,q)
$$

を von Mangoldt 型に寄せる準備が整う。

## 9. 総括

Phase AD は、Erdős #1196 ルートでかなり象徴的な進展じゃ。

$$
q\in index(n),\quad q=p^k
\Rightarrow
n\to n/q
\text{ is prime-power descent}
$$

が no-sorry で閉じた。

山で言えば、前回は「素数の道標」が立った。
今回は「素冪の道標」まで立った。
ここまで来ると、次に立てる看板はもう

$$
\Lambda(q)
$$

じゃ。ただし、賢く進むなら、まず `IsPrimePowerLabel` という **通行証** を作ってから、von Mangoldt 型 weight へ進むのがよいぞい。
