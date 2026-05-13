# review Phase "R"

## 1. 結論

うむ、Phase-R009 は **RealLogBudget 供給路の最初の岩場を固定した段階** じゃ。

Phase-R005 ～ R007 では、

$$
RealLogBudget(I,pOf,n)
\Rightarrow
\sum_{q\in I}\frac{\log(pOf(q))}{\log n}\le 1
$$

および、それを `RealWeightProvider` に載せる route が閉じた。

Phase-R008 では、その `RealLogBudget` を product route から供給する設計を立てた。

そして今回 Phase-R009 では、その product route の第一部品として、

$$
0 < a_i
\Rightarrow
0 < \prod_i a_i
$$

と、

$$
\log\left(\prod_i a_i\right) = \sum_i\log(a_i)
$$

を Lean 上で no-sorry に固定した。

つまり、次の目標である

$$
\prod_i a_i\le N
\Rightarrow
\sum_i\log(a_i)\le \log N
$$

へ進むための左側の変形が整ったわけじゃ。

## 2. 今回の主役

追加された theorem はこの三つじゃ。

```lean
real_finset_prod_pos_of_pos
real_log_prod_eq_sum_log_of_pos
real_sum_log_eq_log_prod_of_pos
```

数学的にはこうじゃ。

まず、

$$
\forall i\in I,\quad 0 < a_i
$$

なら、

$$
0 < \prod_{i\in I}a_i
$$

が出る。

次に、正の実数有限積に対して、

$$
\log\left(\prod_{i\in I}a_i\right) = \sum_{i\in I}\log(a_i)
$$

を得る。

そして後続で使いやすい向きとして、

$$
\sum_{i\in I}\log(a_i) = \log\left(\prod_{i\in I}a_i\right)
$$

も alias として追加した。

この alias は良い。次の Phase-R010 では、おそらく左辺が

$$
\sum_i \log(a_i)
$$

で出てくるので、それを

$$
\log\prod_i a_i
$$

へ書き換える向きが使いやすいからじゃ。

## 3. Lean 的にも良い閉じ方

`real_finset_prod_pos_of_pos` は `Finset.prod_pos` で閉じている。

```lean
Finset.prod_pos ha
```

`real_log_prod_eq_sum_log_of_pos` は `Real.log_prod` を使っている。

```lean
Real.log_prod (s := I) (f := a) fun i hi => ne_of_gt (ha i hi)
```

ここも良い。
`Real.log_prod` が要求するのは非零性であり、こちらは正性

$$
0 < a_i
$$

を持っているので、

$$
a_i\ne0
$$

を `ne_of_gt` で渡している。

この形なら今後も安定して使える。
特に、実数 product route では「正性」と「非零性」が頻繁に行き来するので、この theorem 名で正性版を固定したのは正解じゃ。

## 4. 現在地

R 版 product route はこう進んでいる。

| Phase         | 内容                             | 状態   |
| ------------- | ------------------------------ | ---- |
| Phase-R005    | external `RealLogBudget`       | 完了   |
| Phase-R006    | index 上の log 分子非負性             | 完了   |
| Phase-R007    | `log p / log n` provider       | 完了   |
| Phase-R008    | product route 設計               | 完了   |
| Phase-R009    | 正の実数有限積と log-prod 補題           | 今回完了 |
| Phase-R010    | product bound から log sum bound | 未    |
| Phase-R011    | Nat `pOf`, `n` 版へ戻す            | 未    |
| Phase-R012 以降 | 重複制御・prime-power 接続            | 未    |

ここまでで、

$$
\sum\log
$$

を

$$
\log\prod
$$

へ変換する道はできた。

次は、右側の

$$
\prod_i a_i\le N
$$

から

$$
\log\prod_i a_i\le\log N
$$

を出す番じゃ。

## 5. 次の一手: Phase-R010

次はこの合成補題が自然じゃ。

```lean
theorem real_sum_log_le_log_of_prod_le
    {ι : Type _}
    (I : Finset ι)
    (a : ι → ℝ)
    (N : ℝ)
    (ha : ∀ i, i ∈ I → 0 < a i)
    (hN : 0 < N)
    (hprod : I.prod a ≤ N) :
    (I.sum fun i => Real.log (a i)) ≤ Real.log N
```

証明の流れはこう。

まず Phase-R009 の alias で、

$$
\sum_i\log(a_i) = \log\left(\prod_i a_i\right)
$$

へ変形する。

次に、

$$
0 < \prod_i a_i
$$

を `real_finset_prod_pos_of_pos` から得る。

そして、

$$
\prod_i a_i\le N
$$

と log の単調性から、

$$
\log\left(\prod_i a_i\right)\le\log N
$$

を得る。

Lean ではおそらく `Real.log_le_log` 系が使えるはずじゃ。形としては、

```lean
have hprod_pos : 0 < I.prod a :=
  real_finset_prod_pos_of_pos I a ha

have hlog :
    Real.log (I.prod a) ≤ Real.log N :=
  Real.log_le_log hprod_pos hprod
```

のようになる可能性が高い。

最後に、

```lean
rw [real_sum_log_eq_log_prod_of_pos I a ha]
exact hlog
```

で閉じる見込みじゃ。

## 6. Phase-R010 での注意点

`Real.log_le_log` の仮定形が、Mathlib 側で

$$
0 < x
$$

と

$$
x\le y
$$

を要求する形か、あるいは $0 < y$ も要求する形かは確認が必要じゃ。

`hN : 0 < N` は theorem に入れておくのが良い。
たとえ `Real.log_le_log` が $0 < x$ だけで十分でも、後続の自然数版へ戻すときに $N$ の正性は必要になるからじゃ。

また、空集合の場合も自然に通るはずじゃ。

$$
\prod_{\emptyset}a_i=1
$$

なので、`ha` は vacuous。
ただし `hprod : 1 ≤ N` が必要になる。これがあれば、

$$
0=\sum_{\emptyset}\log(a_i)\le\log N
$$

になる。問題なしじゃ。

## 7. Phase-R011 の先読み

Phase-R010 が閉じたら、次は自然数版へ戻す。

狙いは、

```lean
theorem realLogBudget_of_nat_product_le
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ)
    (hp : ∀ q, q ∈ I → 1 ≤ pOf q)
    (hn : 0 < n)
    (hprod : (I.prod fun q => pOf q) ≤ n) :
    RealLogBudget I pOf n
```

ただしここは、少し調整が必要じゃ。

`real_sum_log_le_log_of_prod_le` は $0 < a_i$ を要求する。
自然数から実数に戻すなら、

$$
a(q)=(pOf(q):\mathbb{R})
$$

で、

$$
0 < (pOf(q):\mathbb{R})
$$

が必要。

`hp : 1 ≤ pOf q` があれば出せる。

また、

$$
(I.prod fun q => (pOf q : \mathbb{R})) = ((I.prod fun q => pOf q):\mathbb{R})
$$

という cast-prod の橋が必要になる。

ここは `norm_num`, `exact_mod_cast`, `Nat.cast_prod` / `map_prod` 系を確認する場所じゃな。

## 8. さらに先の本丸

Nat product route が閉じると、

$$
\prod_{q\in I}pOf(q)\le n
\Rightarrow
RealLogBudget(I,pOf,n)
$$

が得られる。

その次に本当に大事なのは、

$$
\prod_{q\in I}pOf(q)\le n
$$

を prime-power channel からどう出すか。

これは、base prime の重複制御と指数消費の問題じゃ。

たとえば、

$$
q=p^k
$$

で各 $q\mid n$ なら $p\mid n$ ではある。
しかし、複数の $q$ が同じ $p$ を読んだ場合、

$$
p\cdot p
$$

として数えるには、 $n$ 側に少なくとも $p^2$ の指数が必要になる。

つまり次の深い課題は、

$$
\text{selected base primes の積が }n\text{ を超えない}
$$

を保証するための重複・指数管理じゃ。

ただし、これは R011 の後でよい。
いまはまだ実数 product route を閉じる段階じゃ。

## 9. 総括

Phase-R009 は、product route の **log-prod 部品** を固定した段階じゃ。

ここで、

$$
\sum_i\log(a_i) = \log\prod_i a_i
$$

が正の有限積に対して使えるようになった。

次は、

$$
\prod_i a_i\le N
$$

を使って、

$$
\sum_i\log(a_i)\le \log N
$$

へ進む Phase-R010 じゃ。

山で言えば、 $\log p/\log n$ のザイルを固定するための岩場のうち、まず「積と和を結ぶ岩」を打ち込んだ。
次は、その岩を上限 $N$ の岩へつなぐ。ここが閉じれば、`RealLogBudget` の供給路がかなり見えてくるぞい。
