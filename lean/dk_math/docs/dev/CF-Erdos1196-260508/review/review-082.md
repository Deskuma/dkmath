# review Phase "R" 2nd

うむ。R023 は **かなり大きい前進** じゃ。
R022 が「重複あり route を語るための言語」だったのに対して、R023 はその言語から実際に

$$
\prod_{i\in I} \mathrm{pOf}(i) \mid n
$$

を取り出す **自然数側の核心 bridge** を閉じておる。

## 1. 今回、何が閉じたのか

今回追加された主定理はこの 2 本じゃな。

```lean
factorization_prod_primeValued_eq_multiplicity_of_prime
natProductDvdOn_of_multiplicityBudget
```

数学的には、まず

$$
\mathrm{pOf}(i)\ \text{がすべて素数}
$$

であるとき、任意の素数 $p$ について

$$
\left(\prod_{i\in I} \mathrm{pOf}(i)\right).\mathrm{factorization}(p) = \#{i\in I \mid \mathrm{pOf}(i)=p}
$$

を証明した。

そのうえで、multiplicity budget

$$
\#{i\in I \mid \mathrm{pOf}(i)=p}
\le
n.\mathrm{factorization}(p)
$$

を使い、

$$
\left(\prod_{i\in I} \mathrm{pOf}(i)\right).\mathrm{factorization}(p)
\le
n.\mathrm{factorization}(p)
$$

を全ての $p$ で示し、素因数分解の指数比較から

$$
\prod_{i\in I} \mathrm{pOf}(i)\mid n
$$

へ戻した。
つまり、 **重複あり route の自然数側は実質的に閉じた** と見てよい。

## 2. 数学的な意味

重複なし route では、

$$
p_1,p_2,\dots,p_r
$$

が互いに異なる素数で、各 $p_j\mid n$ なら

$$
p_1p_2\cdots p_r\mid n
$$

と言えた。

しかし重複ありでは、たとえば

$$
2,2,2,3
$$

のような列が出る。これは単に $2\mid n$, $3\mid n$ では足りず、

$$
2^3\cdot 3\mid n
$$

が必要になる。

R023 の bridge は、この「同じ素数を何回消費したか」を

$$
n.\mathrm{factorization}(p)
$$

と比較することで処理しておる。
これは非常に自然で、数論的にも最小の正攻法じゃ。

## 3. `factorization_prod_primeValued_eq_multiplicity_of_prime` の役割

この補題は、R023 の心臓じゃ。

Lean の証明では、

```lean
rw [Nat.factorization_prod_apply hnonzero]
```

により、

$$
\left(\prod_{i\in I}\mathrm{pOf}(i)\right).\mathrm{factorization}(p) = \sum_{i\in I}(\mathrm{pOf}(i)).\mathrm{factorization}(p)
$$

へ展開しておる。

そして $\mathrm{pOf}(i)$ は素数なので、

$$
(\mathrm{pOf}(i)).\mathrm{factorization}(p) =
\begin{cases}
1 & \mathrm{pOf}(i)=p,\\
0 & \mathrm{pOf}(i)\ne p
\end{cases}
$$

となる。
したがって和は indicator の和になり、

$$
\sum_{i\in I}
\mathbf{1}_{\mathrm{pOf}(i)=p} = \#{i\in I\mid \mathrm{pOf}(i)=p}
$$

へ落ちる。

これはまさに multiplicity の意味そのものじゃな。

## 4. `natProductDvdOn_of_multiplicityBudget` の役割

こちらは、上の局所指数計算を divisibility に戻す補題じゃ。

定理の骨格はこう。

$$
\forall p,\quad
\left(\prod_{i\in I}\mathrm{pOf}(i)\right).\mathrm{factorization}(p)
\le
n.\mathrm{factorization}(p)
$$

なら、

$$
\prod_{i\in I}\mathrm{pOf}(i)\mid n
$$

である。

Lean では `Nat.factorization_le_iff_dvd` を使っておる。ここで必要な非ゼロ条件も丁寧に処理している。

特に良いのは、`n = 0` を別分岐にして

```lean
exact dvd_zero _
```

で処理している点じゃ。
これで定理自体は一般の $n$ に対して使える。後段の log route ではもちろん $1 < n$ が必要になるが、この自然数 bridge 自体を広めに保っているのは悪くない。

## 5. これで何が可能になったか

R023 によって、次の鎖が Lean 上で通った。

$$
\text{prime-valued selected bases}
$$

$$
+
$$

$$
\text{multiplicity budget against } n.\mathrm{factorization}
$$

$$
\Longrightarrow
$$

$$
\prod_{i\in I}\mathrm{pOf}(i)\mid n
$$

つまり、同じ base prime が複数回出ても、その回数が $n$ の指数予算内なら product divisibility を供給できる。

これは R/log route へ接続する直前の最重要地点じゃ。
なぜなら log route で欲しいのは概ね

$$
\prod_{i\in I}\mathrm{pOf}(i)\le n
$$

であり、正の自然数では

$$
\prod_{i\in I}\mathrm{pOf}(i)\mid n
\quad\Longrightarrow\quad
\prod_{i\in I}\mathrm{pOf}(i)\le n
$$

が使えるからじゃ。

## 6. 今回の実装の評価

これは綺麗じゃ。

特に評価できる点は 3 つある。

まず、`NatPrimeValuedOn` を明示したことで、product factorization を multiplicity として読む条件が明確になった。
次に、`Nat.factorization_prod_apply` から indicator sum へ落とすルートが素直で、後続が読みやすい。
最後に、`Nat.factorization_le_iff_dvd` で divisibility へ戻しているため、mathlib の標準語彙に乗っている。

つまり、独自理論の語彙を増やしつつも、証明の芯は mathlib の定番定理へ寄せておる。
これは長期保守しやすい書き方じゃ。

## 7. R024 の見通し

次の R024 は、かなり見通しがよい。

目標はおそらくこの形じゃ。

```lean
theorem natProductBoundOn_of_multiplicityBudget
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    {n : ℕ}
    (hn : 0 < n)
    (hprime : NatPrimeValuedOn I pOf)
    (hbudget : NatBaseMultiplicityBudgetOn I pOf n) :
    NatProductBoundOn I pOf n
```

証明は、

1. R023 で `NatProductDvdOn I pOf n`
2. `pOf` が prime-valued なので product は正
3. $0 < n$ と divisibility から product bound

という流れになるはずじゃ。

そして provider bridge は最終的に、

```lean
basePrimeOf_logRatioSubProbability_of_multiplicityBudget
```

のような名前で、重複ありでも `SubProbability` を供給する入口になる。

## 8. 数学的な到達点

今回で、重複あり route の核心は次の形に整理された。

$$
\text{重複なし}
\quad
\text{distinct primes}
\Rightarrow
\prod p_i\mid n
$$

から、

$$
\text{重複あり}
\quad
\text{multiplicity}(p)\le v_p(n)
\Rightarrow
\prod p_i\mid n
$$

へ昇格した。

これは単なる一般化ではなく、#1196 的な「素因子チャネルの消費量」を正確に扱えるようになった、という意味がある。

同じ prime channel を何度も使うなら、そのぶん $n$ の valuation budget を消費する。
その消費量が予算内なら、log mass は親 $n$ を超えない。
この流れが、Lean 上でかなり明瞭になってきた。

## 9. 総合判定

R023 は **登頂直前の核心 bridge が閉じた** と言ってよい。

まだ `SubProbability` そのものへは接続していない。
しかし、そこに必要な自然数側の重い部分、

$$
\text{multiplicity budget}
\Rightarrow
\text{product divisibility}
$$

は閉じた。

次の R024 は、数学的には仕上げの接続層じゃ。
ここまで来れば、重複あり R/log route はかなり現実的に閉じる。

よくぞここまで来たの、ぬしよ。これはもう「行けそう」ではない。
**行くための橋が、実際に架かった** 段階じゃ。
