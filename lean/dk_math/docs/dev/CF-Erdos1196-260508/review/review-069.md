# review Phase "R"

## 1. 結論

うむ、Phase-R010 は **product bound から log budget へ進む実数版コア補題** が閉じた段階じゃ。

Phase-R009 では、

$$
\sum_i \log(a_i)=\log\prod_i a_i
$$

を正の実数有限積に対して使えるようにした。今回 Phase-R010 では、さらに

$$
\prod_{i\in I} a_i \le N
$$

を仮定すれば、

$$
\sum_{i\in I}\log(a_i)\le \log N
$$

が得られることを no-sorry で通した。

つまり、`RealLogBudget` を product route から供給するための **実数側の中核** ができたわけじゃな。

## 2. 今回の主役

追加された theorem はこれじゃ。

```lean
theorem real_sum_log_le_log_of_prod_le
    {ι : Type _}
    (I : Finset ι)
    (a : ι → ℝ)
    (N : ℝ)
    (ha : ∀ i, i ∈ I → 0 < a i)
    (_hN : 0 < N)
    (hprod : I.prod a ≤ N) :
    (I.sum fun i => Real.log (a i)) ≤ Real.log N
```

数学的には、正の項 $a_i$ について、

$$
\sum_i\log(a_i) = \log\left(\prod_i a_i\right)
$$

かつ、

$$
\prod_i a_i\le N
$$

なので、対数の単調性から

$$
\log\left(\prod_i a_i\right)\le \log N
$$

が出る、という流れじゃ。

## 3. 証明構造が美しい

証明はかなり綺麗じゃ。

```lean
rw [real_sum_log_eq_log_prod_of_pos I a ha]
exact Real.log_le_log (real_finset_prod_pos_of_pos I a ha) hprod
```

Phase-R009 で入れた

```lean
real_sum_log_eq_log_prod_of_pos
```

がそのまま効いている。

そして

```lean
real_finset_prod_pos_of_pos
```

で

$$
0 < \prod_i a_i
$$

を得て、`Real.log_le_log` に渡している。

この分割は正解じゃ。
`sum log = log prod`、積の正性、log の単調性がそれぞれ theorem 名で分かれているので、後続で自然数版へ戻す時にも壊れにくい。

## 4. `_hN` について

今回 theorem の仮定には

```lean
(_hN : 0 < N)
```

があるが、証明本体では直接使っていない。

これは悪くない。
`Real.log_le_log` は、左側の正性

$$
0 < \prod_i a_i
$$

と

$$
\prod_i a_i\le N
$$

から十分に進められる形だった、ということじゃろう。

ただし、API としては $0 < N$ を持っている方が自然じゃ。後続の自然数版や denominator 正性と接続する時に、`N` が正であることは意味論上かなり大事だからの。

## 5. 現在地

R 版 product route はこうなった。

| Phase         | 内容                           | 状態   |
| ------------- | ---------------------------- | ---- |
| Phase-R005    | external `RealLogBudget`     | 完了   |
| Phase-R007    | `log p / log n` provider     | 完了   |
| Phase-R008    | product route 設計             | 完了   |
| Phase-R009    | `sum log = log prod`         | 完了   |
| Phase-R010    | `prod ≤ N → sum log ≤ log N` | 今回完了 |
| Phase-R011    | Nat `pOf`, `n` 版へ戻す          | 未    |
| Phase-R012 以降 | 重複制御・prime-power 接続          | 未    |

これで実数側では、

$$
\prod a_i\le N
\Rightarrow
\sum\log a_i\le \log N
$$

が閉じた。
次は、ここへ

$$
a_i=(\mathrm{pOf}(i):\mathbb{R}),\qquad N=(n:\mathbb{R})
$$

を代入する段階じゃ。

## 6. 次の一手: Phase-R011

次は自然数版へ戻し、

$$
\prod_{q\in I} \mathrm{pOf}(q)\le n
$$

から

$$
\mathrm{RealLogBudget}(I,\mathrm{pOf},n)
$$

を供給する theorem が自然じゃ。

候補はこう。

```lean
theorem realLogBudget_of_nat_product_le
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ)
    (hp : RealLogNonnegOn I pOf)
    (hn : 0 < n)
    (hprod : (I.prod fun q => pOf q) ≤ n) :
    RealLogBudget I pOf n
```

証明の骨格はこうじゃ。

```lean
unfold RealLogBudget
exact real_sum_log_le_log_of_prod_le
  I
  (fun q => (pOf q : ℝ))
  (n : ℝ)
  ?ha
  ?hN
  ?hprodReal
```

ここで必要になるのは三つ。

$$
q\in I\Rightarrow 0 < (\mathrm{pOf}(q):\mathbb{R})
$$

$$
0 < (n:\mathbb{R})
$$

$$
\prod_q (\mathrm{pOf}(q):\mathbb{R})\le (n:\mathbb{R})
$$

じゃ。

## 7. Phase-R011 の注意点

一番の山は cast product じゃな。

必要なのは、

$$
\left(\prod_{q\in I}\mathrm{pOf}(q):\mathbb{R}\right) = \prod_{q\in I}(\mathrm{pOf}(q):\mathbb{R})
$$

という橋じゃ。

Lean では `exact_mod_cast hprod` で通る可能性がある。通らなければ、`map_prod` 系または `norm_num` / `simp` で cast product を明示する小補題を置くとよい。

小補題候補はこうじゃ。

```lean
theorem real_finset_prod_nat_cast
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ) :
    ((I.prod fun q => pOf q : ℕ) : ℝ) =
      I.prod fun q => (pOf q : ℝ)
```

向きは後続で使いやすい方にしてよい。
たぶん `norm_num` より `simp` が効くかもしれぬ。

## 8. その先の本丸

Phase-R011 が閉じると、

$$
\prod \mathrm{pOf}(q)\le n
\Rightarrow
\mathrm{RealLogBudget}(I,\mathrm{pOf},n)
$$

が得られる。

すると Phase-R007 と合成して、

$$
\prod \mathrm{pOf}(q)\le n
\Rightarrow
\frac{\log \mathrm{pOf}(q)}{\log n}
\text{ provider is sub-probability}
$$

へ進める。

だが、その次に来る本丸は、

$$
\prod_{q\in I}\mathrm{pOf}(q)\le n
$$

を prime-power / divisor channel からどう得るかじゃ。

ここでは、同じ base prime が何度出るか、各 $q=p^k$ が $n$ のどの指数を消費するか、重複した base prime をどう数えるかが問題になる。

これは R012 以降で扱うべきで、いまはまだ急がなくてよい。

## 9. 総括

Phase-R010 は、`RealLogBudget` 供給 route の **実数 product-to-log budget core** を閉じた段階じゃ。

これで、

$$
\prod_i a_i\le N
$$

から、

$$
\sum_i\log(a_i)\le \log N
$$

まで行ける。

山で言えば、Phase-R009 で「和の log と積の log をつなぐ岩」を打ち、今回 Phase-R010 で「積の上界を log の上界へ送るロープ」を張った。

次は自然数 $\mathrm{pOf}$ と $n$ に戻す Phase-R011。
ここを越えると、外部仮定だった `RealLogBudget` の供給源が、かなり具体的に見えてくるぞい。
