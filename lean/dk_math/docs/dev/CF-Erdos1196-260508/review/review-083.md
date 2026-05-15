# review Phase "R" 2nd

うむ。R024 は **抽象 `pOf` レベルの重複あり R/log route が閉じた** という意味で、かなり大きい節目じゃ。
R023 で自然数側の核心、

$$
\mathrm{multiplicity\ budget}
\Longrightarrow
\prod_{i\in I}\mathrm{pOf}(i)\mid n
$$

を閉じ、R024 でそれをそのまま log 質量評価へ接続した形じゃな。

## 1. 何が閉じたのか

今回の到達点は、次の鎖が Lean 上で通ったことじゃ。

$$
\text{NatPrimeValuedOn } I\ \mathrm{pOf}
$$

$$
\text{NatBaseMultiplicityBudgetOn } I\ \mathrm{pOf}\ n
$$

から、

$$
\prod_{i\in I}\mathrm{pOf}(i)\le n
$$

を得て、さらに

$$
\sum_{i\in I}\frac{\log(\mathrm{pOf}(i))}{\log n}\le 1
$$

へ進み、最終的に

```lean
(realLogRatioWeightProvider I pOf n ... hn).SubProbability
```

まで到達した。

つまり、数学的には

$$
\prod_{i\in I} p_i \le n
\quad\Longrightarrow\quad
\sum_{i\in I}\log p_i \le \log n
\quad\Longrightarrow\quad
\sum_{i\in I}\frac{\log p_i}{\log n}\le 1
$$

という、R/log route の本体が閉じた。

## 2. 各補題の意味

### `realLogNonnegOn_of_natPrimeValuedOn`

これは素数なら $1 < p$ なので、log route 側で必要な自然数下界を供給する補題じゃ。

$$
\mathrm{pOf}(i)\ \text{is prime}
\quad\Longrightarrow\quad
1\le \mathrm{pOf}(i)
$$

実際には素数なら $2\le p$ なので、log の非負性にも都合がよい。

ここで良いのは、R/log route 側の仮定 `RealLogNonnegOn` を、数論側の自然な仮定 `NatPrimeValuedOn` から自動供給できるようにした点じゃな。

### `natProductBoundOn_of_multiplicityBudget`

これは R023 の

$$
\prod_{i\in I}\mathrm{pOf}(i)\mid n
$$

を、R/log route が欲しがる

$$
\prod_{i\in I}\mathrm{pOf}(i)\le n
$$

へ変換する橋じゃ。

`hn : 0 < n` を仮定して、

```lean
natProductBoundOn_of_product_dvd
```

へ渡している。
数学的には、正の自然数 $n$ に対して $m\mid n$ なら、通常 $m\le n$ が成り立つ、という基本事実じゃ。

### `realLogProductBudget_of_multiplicityBudget`

これは bundle 化された中間結論じゃ。

$$
\text{prime-valued}
+
\text{multiplicity budget}
+
1<n
$$

から `RealLogProductBudget` を作る。

ここで `RealLogProductBudget` は、おそらく次の三つを束ねた構造じゃな。

1. 各 selected base の log 側非負性
2. $1 < n$ による分母 $\log n$ の正性
3. product bound $\prod p_i\le n$

この bundle ができた時点で、あとは既存の R/log theorem へ流すだけになる。

### `realLogRatioWeightProvider_subProbability_of_multiplicityBudget`

これが R024 の頂上じゃ。

$$
w_i:=\frac{\log(\mathrm{pOf}(i))}{\log n}
$$

と置いた provider が、

$$
\sum_{i\in I}w_i\le 1
$$

を満たす、つまり `SubProbability` であることを示している。

証明は既存の

```lean
realLogRatioWeightProvider_subProbability_of_productBudget
```

へ渡すだけになっておる。
この形は美しい。R024 は新しい解析を再証明していない。必要な自然数予算を既存 log route の入口へ供給しただけじゃ。

## 3. 数学的な見取り図

今回で、重複あり route は次のように完成した。

まず、各 selected label $i\in I$ が base prime $p_i=\mathrm{pOf}(i)$ を持つ。

同じ素数 $p$ が何回出たかを

$$
m_I(p):=\#{i\in I\mid \mathrm{pOf}(i)=p}
$$

と数える。

multiplicity budget は、

$$
m_I(p)\le v_p(n)
$$

という条件じゃ。ここで Lean では

$$
v_p(n)
$$

を

$$
n.\mathrm{factorization}(p)
$$

で読む。

R023 により、

$$
m_I(p)\le v_p(n)\ \forall p
\quad\Longrightarrow\quad
\prod_{i\in I}p_i\mid n
$$

が出た。

R024 により、

$$
\prod_{i\in I}p_i\mid n,\quad 0<n
\quad\Longrightarrow\quad
\prod_{i\in I}p_i\le n
$$

さらに、

$$
\prod_{i\in I}p_i\le n,\quad 1<n
\quad\Longrightarrow\quad
\sum_{i\in I}\frac{\log p_i}{\log n}\le 1
$$

となる。

つまり、同じ base prime が複数回出ても、その消費量が $n$ の valuation budget 内に収まっていれば、log 質量は親 $n$ を超えない。

これが R024 の数学的成果じゃ。

## 4. 何が重要か

R024 の重要性は、 **重複なし仮定からの脱却** にある。

これまでの route は、

$$
p_i\ \text{が pairwise distinct}
$$

という強い仮定で積を制御していた。
しかし R024 では、

$$
p_i\ \text{は重複してもよい}
$$

ただし、

$$
\text{重複回数}\le n\text{ の素因数指数}
$$

であればよい。

これは数論的にはかなり自然な一般化じゃ。
素数チャネルを一度使うなら指数を 1 消費する。二度使うなら指数を 2 消費する。消費量が予算内なら積は $n$ に収まる。
まさに valuation budget という名前どおりじゃな。

## 5. 今回の実装評価

設計はきれいじゃ。

`ValuationBudget.lean` に、

```lean
multiplicity budget
→ product divisibility
→ product bound
→ real/log product budget
→ SubProbability
```

が一直線に並んだ。

しかも、R024 はまだ witness provider に依存していない。
これはとても良い。抽象 `pOf : ι → ℕ` で閉じているため、後で

```lean
pOf := W.basePrimeOf n I hI
```

を代入するだけで provider route へ移れる。

つまり R024 は、 **再利用可能な一般定理** として閉じている。
ここが美しい。

## 6. R025 の見通し

次は witness-provider bridge じゃな。

おそらく目標形はこうなる。

```lean
theorem basePrimeOf_logRatioSubProbability_of_multiplicityBudget
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    (hn : 1 < n)
    (hbudget :
      NatBaseMultiplicityBudgetOn I (W.basePrimeOf n I hI) n) :
    (realLogRatioWeightProvider I (W.basePrimeOf n I hI) n
      (realLogNonnegOn_of_natPrimeValuedOn I (W.basePrimeOf n I hI)
        (W.basePrimeOf_prime_on n I hI))
      hn).SubProbability
```

実際には既存の `W.basePrimeOf_realLogNonnegOn` を使うか、今回の `realLogNonnegOn_of_natPrimeValuedOn` を使うかで statement の見た目が変わるじゃろう。

ただ、数学的には単純じゃ。

1. witness provider から
   $$
   \mathrm{pOf}(q):=W.basePrimeOf(n,I,hI,q)
   $$
   が prime-valued であることを得る。
2. R024 の抽象 theorem に流す。
3. `SubProbability` が出る。

したがって R025 は、証明負荷としては R023 より軽いはずじゃ。

## 7. 到達点の評価

ここまでで、

$$
\text{abstract repeated-base R/log route}
$$

は閉じた。

残るのは、

$$
\text{witness provider 由来の }\mathrm{pOf}
$$

へ特殊化することだけじゃ。

なので進捗としては、

* R022: 語彙固定
* R023: multiplicity budget から product divisibility
* R024: product bound から SubProbability
* R025: witness provider bridge

という流れのうち、最も数学的に重い R023/R024 は通過済み。

これはかなり大きい。

## 8. 総合判定

R024 によって、重複あり route は **抽象レベルでは登頂成功** じゃ。

まだ witness provider bridge が残っておるので、リポジトリ全体の公開導線としては R025 が必要。
しかし数学的には、すでに核心は閉じておる。

$$
\text{同じ素数が重複する}
$$

という問題を、

$$
\text{指数予算を消費する}
$$

という正しい形に変換し、その予算内なら log 質量は 1 を超えないと証明した。
これは #1196 的な確率質量保存の Lean 実装として、非常に良い形じゃ。

ぬしよ、ここは素直に喜んでよい。
R024 は「あと一歩」ではなく、 **最後の一般橋が架かった** 段階じゃ。
