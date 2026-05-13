# review Phase "R"

## 1. 結論

うむ、Phase-R011 は **外部仮定だった `RealLogBudget` の供給源が、自然数 product bound まで降りてきた段階** じゃ。

これまでは、

$$
RealLogBudget(I,pOf,n)
$$

を外から仮定して、

$$
\sum_{q\in I}\frac{\log(pOf(q))}{\log n}\le 1
$$

や `realLogRatioWeightProvider.SubProbability` を得ていた。今回ついに、

$$
\prod_{q\in I} pOf(q)\le n
$$

から、

$$
\sum_{q\in I}\log(pOf(q))\le \log n
$$

を供給できるようになった。つまり、`RealLogBudget` が **抽象仮定** から **自然数有限積の上界条件** へ接続されたわけじゃ。build と no-sorry 検査も通っておる。

## 2. 今回の主役

追加された theorem は二つじゃ。

```lean
real_finset_prod_nat_cast
realLogBudget_of_nat_product_le
```

まず、

```lean
real_finset_prod_nat_cast
```

は、

$$
\left(\prod_{q\in I} pOf(q):\mathbb{R}\right) = \prod_{q\in I}(pOf(q):\mathbb{R})
$$

を固定する橋じゃ。

次に、

```lean
realLogBudget_of_nat_product_le
```

が本命で、

$$
RealLogNonnegOn(I,pOf)
$$

$$
0 < n
$$

$$
\prod_{q\in I}pOf(q)\le n
$$

から、

$$
RealLogBudget(I,pOf,n)
$$

を出す。

これはかなり重要じゃ。
外部 budget だったものが、ついに product budget から供給可能になった。

## 3. 数学的な流れ

今回の証明の数学はこうじゃ。

まず、各 $q\in I$ に対して

$$
1\le pOf(q)
$$

があるので、

$$
0 < (pOf(q):\mathbb{R})
$$

が出る。

次に、

$$
\prod_{q\in I}pOf(q)\le n
$$

を実数へ cast し、

$$
\prod_{q\in I}(pOf(q):\mathbb{R})\le (n:\mathbb{R})
$$

へ移す。

すると Phase-R010 の実数補題より、

$$
\sum_{q\in I}\log(pOf(q):\mathbb{R})\le \log(n:\mathbb{R})
$$

が得られる。

これがまさに、

$$
RealLogBudget(I,pOf,n)
$$

じゃ。

## 4. Lean 的な勝ち筋

今回の実装で良いのは、cast 周りを小補題として分けたことじゃ。

```lean
theorem real_finset_prod_nat_cast
```

を先に置いたことで、

```lean
rw [← real_finset_prod_nat_cast I pOf]
exact_mod_cast hprod
```

という形で自然数積の上界を実数積の上界へ移せる。

また、実数正性のところで `exact_mod_cast` が苦しんだため、

```lean
Nat.cast_pos.mpr
```

で明示的に

$$
0 < (pOf(q):\mathbb{R})
$$

を作ったのも良い判断じゃ。
coercion が絡む場所では、こうして正性を明示的に作る方が安定する。

## 5. 現在地

R 版 product route はここまで来た。

| Phase         | 内容                                                 | 状態   |
| ------------- | -------------------------------------------------- | ---- |
| Phase-R005    | 外部 `RealLogBudget`                                 | 完了   |
| Phase-R007    | `log p / log n` provider                           | 完了   |
| Phase-R009    | `sum log = log prod`                               | 完了   |
| Phase-R010    | 実数 product bound → log-sum bound                   | 完了   |
| Phase-R011    | 自然数 product bound → `RealLogBudget`                | 今回完了 |
| Phase-R012    | product bound → log-ratio provider sub-probability | 未    |
| Phase-R013 以降 | prime-power / 重複制御との接続                             | 未    |

ここまでで、

$$
\prod pOf(q)\le n
\Rightarrow
RealLogBudget(I,pOf,n)
\Rightarrow
\text{log-ratio provider is sub-probability}
$$

という道が見えてきた。

## 6. 次の一手: Phase-R012

次は、今回の `realLogBudget_of_nat_product_le` と、既存の

```lean
realLogRatioWeightProvider_subProbability
```

を接続する alias が自然じゃ。

つまり、

$$
RealLogNonnegOn(I,pOf)
$$

$$
1 < n
$$

$$
\prod pOf(q)\le n
$$

から、直接

$$
(realLogRatioWeightProvider I pOf n hp hn).SubProbability
$$

を出す theorem じゃ。

候補名は、

```lean
realLogRatioWeightProvider_subProbability_of_nat_product_le
```

のようなものがよい。

概念的にはこうじゃ。

```lean
theorem realLogRatioWeightProvider_subProbability_of_nat_product_le
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ)
    (hp : RealLogNonnegOn I pOf)
    (hn : 1 < n)
    (hprod : (I.prod fun q => pOf q) ≤ n) :
    (realLogRatioWeightProvider I pOf n hp hn).SubProbability := by
  exact realLogRatioWeightProvider_subProbability
    I pOf n hp hn
    (realLogBudget_of_nat_product_le I pOf n hp (Nat.lt_trans Nat.zero_lt_one hn) hprod)
```

これが入ると、外部 `RealLogBudget` を明示せず、product bound から provider の sub-probability へ直行できる。

## 7. その次の本丸

Phase-R012 が閉じたら、いよいよ次は、

$$
\prod_{q\in I}pOf(q)\le n
$$

をどこから得るかじゃ。

ここから先は、prime-power witness provider 側に戻ることになる。

候補の流れは、

$$
q=p^k
$$

$$
p=pOf(q)
$$

$$
q\mid n
$$

から、

$$
p\mid n
$$

を得る。

しかし、複数の $q$ が同じ base prime $p$ を読む場合、

$$
p\cdot p
$$

を product に入れるには、 $n$ 側に $p^2$ 分の指数が必要じゃ。
つまり、ここからは **重複制御** あるいは **指数消費 tracking** が必要になる。

ここは急がず、次の段階で、

$$
\text{selected base primes are product-bounded by }n
$$

という predicate を先に作るのがよさそうじゃ。

## 8. 総括

Phase-R011 は、R 版 log route の大きな前進じゃ。

これで、

$$
\prod_{q\in I}pOf(q)\le n
$$

という自然数 product bound から、

$$
\sum_{q\in I}\log(pOf(q))\le \log n
$$

すなわち `RealLogBudget` を供給できるようになった。

山で言えば、これまでは $\log p/\log n$ のザイルを張るために `RealLogBudget` という外部支点を仮置きしていた。
今回、その支点を

$$
\prod pOf(q)\le n
$$

という自然数の岩場へ固定できた。

次は、その岩場から直接 `log-ratio provider` の sub-probability へつなぐ短絡 theorem。
そのあとに、いよいよ prime-power channel の重複制御という本当の岩稜へ入る番じゃな。
