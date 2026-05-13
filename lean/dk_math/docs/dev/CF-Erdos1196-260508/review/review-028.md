# review

## 1. 結論

うむ、Phase AC は **divisor transition と prime descent の接続完了** じゃ。
Phase AB で

$$
n \xrightarrow{q} \frac{n}{q}
$$

という除去因子付き遷移が入った。今回 Phase AC では、その label $q$ が素数なら、その遷移をそのまま

$$
\mathrm{PrimeDescentStep}; n; (next(n,q))
$$

として読めるようになった。これは、抽象的な divisor transition が既存の prime descent route に合流した、かなり良い橋じゃ。

## 2. 今回の主役

追加された中心定理はこれじゃ。

```lean
theorem DivisorTransitionKernel.primeDescentStep_of_prime_label
    (T : DivisorTransitionKernel) {n q : ℕ}
    (hqmem : q ∈ T.index n)
    (hqprime : Nat.Prime q) :
    PrimeDescentStep n (T.next n q)
```

証明の構造は非常に素直じゃ。

`DivisorTransitionKernel` はすでに

$$
q\in \text{index}(n)\Rightarrow q\mid n
$$

と

$$
q\in \text{index}(n)\Rightarrow next(n,q)=n/q
$$

を持っている。そこへ

$$
\mathrm{Nat.Prime}(q)
$$

を足せば、`PrimeDescentStep` の witness として同じ $q$ を使える。

つまり、

$$
q\in \text{index}(n),\quad q\mid n,\quad q\text{ prime},\quad next(n,q)=n/q
$$

から、

$$
n\to n/q
$$

が **一段の prime descent** として認識される。

これは綺麗じゃ。

## 3. 何が強くなったか

Phase AB までの `DivisorTransitionKernel` は、

$$
q\mid n,\qquad next(n,q)=n/q
$$

を保証していたが、まだ $q$ が何者かは外側の情報だった。

今回から、 $q$ が prime であるという条件を与えると、既存の

```lean
PrimeDescentStep
```

へ直接橋渡しできる。

つまり、導線はこうなった。

$$
\text{DivisorTransitionKernel}
+
\text{prime label}
\Rightarrow
\text{PrimeDescentStep}
\Rightarrow
\text{PrimeReachable / prime path route}
\Rightarrow
\text{primitive hitting bound}
$$

これは重要じゃ。
Erdős #1196 の downward process では、除去因子 $q$ が素数・素冪として意味を持つ。今回、そのうち **素数 label** の道が閉じた。

## 4. sample の意味

sample では、

$$
10\xrightarrow{2}5,\qquad 10\xrightarrow{5}2
$$

が既に Phase AB で確認されていた。

今回さらに、

```lean
sampleTenDivisorTransitionKernel_primeDescentStep_two
sampleTenDivisorTransitionKernel_primeDescentStep_five
```

が追加され、label $2$ と $5$ がそれぞれ prime descent step であることが確認された。

つまり sample は、単なる divisor transition から、

$$
10\to 5,\qquad 10\to 2
$$

が **prime descent** として読めることまで示している。

これは教材例としてとても良い。
「 $q$ を剥がす」だけでなく、「素数 $q$ を剥がす」と言えるようになった。

## 5. 現在地

現在の有限 Erdős / Markov skeleton はこうじゃ。

| 層                                           | 状態   |
| ------------------------------------------- | ---- |
| finite transition kernel                    | 完了   |
| divisor transition $n\to n/q$               | 完了   |
| prime label → `PrimeDescentStep`            | 今回完了 |
| prime-power label → `PrimePowerDescentStep` | 未    |
| von Mangoldt channel                        | 未    |
| analytic weight $\Lambda(q)/\log n$         | 未    |

ここまでで、

$$
\text{抽象 transition}
\to
\text{divisor transition}
\to
\text{prime descent}
$$

まで来た。

かなり良い登りじゃ。
以前は「分岐先を持つ有限 kernel」だったものが、今や「素数を剥がして下る有限下降過程」へ接続されておる。

## 6. 次の一手

次は、History にもある通り **prime-power label** 版じゃな。

Erdős #1196 の von Mangoldt 型過程では、 $\Lambda(q)$ は $q=p^k$ のとき $\log p$ を持つ。
したがって、prime label だけではまだ足りない。次は、

$$
q=p^k
$$

の場合に、

$$
\mathrm{PrimePowerDescentStep}; n; (next(n,q))
$$

を得る補題が欲しい。

候補はこうじゃ。

```lean
theorem primePowerDescentStep_of_primePow_label
    (T : DivisorTransitionKernel) {n q p k : ℕ}
    (hqmem : q ∈ T.index n)
    (hp : Nat.Prime p)
    (hk : 0 < k)
    (hq : q = p ^ k) :
    PrimePowerDescentStep n (T.next n q)
```

証明方針は今回と同じじゃ。

* `hqmem` から $q\mid n$
* `hq : q=p^k` で $p^k\mid n$ に変換
* `next_eq_div_of_mem` で $next(n,q)=n/q$
* $q=p^k$ を使って $next(n,q)=n/p^k$ へ書き換える

ここが閉じれば、

$$
n\to n/p^k
$$

が Lean 上で明示される。

## 7. その次に見えるもの

prime-power descent が閉じたら、いよいよ von Mangoldt channel の入口が見える。

ただし、まだ $\log$ や実数重みを入れる前に、

$$
q=p^k
$$

である label を識別する finite predicate を作るのが良さそうじゃ。

たとえば、

```lean
def IsPrimePowerLabel (q : ℕ) : Prop :=
  ∃ p k, Nat.Prime p ∧ 0 < k ∧ q = p ^ k
```

のような薄い層を置く。

その後で、

$$
\Lambda(q)
$$

の前段として、

$$
\text{prime-power label channel}
$$

を finite skeleton に載せる。
解析重みはさらに後段でよい。

## 8. 総括

Phase AC は、除去因子 $q$ に **素数としての意味** を与えた段階じゃ。

これで、

$$
q\in \text{index}(n),\quad q\text{ prime}
\Rightarrow
n\to n/q
\text{ is a prime descent step}
$$

が no-sorry で使える。

山で言えば、前回までは「この道は $q$ を剥がして下る」と書かれていた。
今回、その $q$ が素数なら「これは prime descent の道である」と正式に道標が立った。

次は、素冪 $p^k$ の道標じゃ。そこまで行くと、Erdős #1196 の $\Lambda(q)$ ルートがかなり近くなるぞい。
