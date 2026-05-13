# review Phase "R"

## 1. 結論

うむ、Phase-R012 は **product bound から log-ratio provider への直通路が完成** した段階じゃ。

これまで外部仮定だった

$$
\mathrm{RealLogBudget}(I,\mathrm{pOf},n)
$$

は Phase-R011 で、

$$
\prod_{q\in I}\mathrm{pOf}(q)\le n
$$

から供給できるようになった。今回 Phase-R012 では、それをさらに `realLogRatioWeightProvider_subProbability` と接続して、

$$
\prod_{q\in I}\mathrm{pOf}(q)\le n
\Rightarrow
\left(\frac{\log(\mathrm{pOf}(q))}{\log n}\right)\text{ provider is sub-probability}
$$

まで一発で通した。

これは大きい。
R 版の有限 log-ratio provider は、もはや外部 log budget に直接依存するだけではなく、 **自然数 product bound** から sub-probability まで到達できるようになった。

## 2. 今回の主役

追加された theorem はこれじゃ。

```lean
theorem realLogRatioWeightProvider_subProbability_of_nat_product_le
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ)
    (hp : RealLogNonnegOn I pOf)
    (hn : 1 < n)
    (hprod : (I.prod fun q => pOf q) ≤ n) :
    (realLogRatioWeightProvider I pOf n hp hn).SubProbability
```

数学的には、

$$
\forall q\in I,\quad 1\le \mathrm{pOf}(q)
$$

$$
1 < n
$$

$$
\prod_{q\in I}\mathrm{pOf}(q)\le n
$$

から、

$$
\sum_{q\in I}\frac{\log(\mathrm{pOf}(q))}{\log n}\le 1
$$

を出す theorem じゃ。

内部では、

```lean
realLogBudget_of_nat_product_le
realLogRatioWeightProvider_subProbability
```

を合成している。
つまり、Phase-R011 と Phase-R007 がきれいに接続されたわけじゃな。

## 3. 数学的な意味

今までの R 版 route はこうだった。

$$
\mathrm{RealLogBudget}(I,\mathrm{pOf},n)
\Rightarrow
\sum_q \frac{\log(\mathrm{pOf}(q))}{\log n}\le 1
$$

しかし今回からは、

$$
\prod_q \mathrm{pOf}(q)\le n
$$

を示せば十分になった。

これは非常に重要じゃ。
なぜなら、Erdős #1196 側の数論構造では、log の和よりも、まず積や割り切りの形の方が自然に現れるからじゃ。

$$
\sum_q\log p_q\le\log n
$$

は解析的に見えるが、

$$
\prod_q p_q\le n
$$

は整数論的・有限的に見える。

今回の theorem は、その二つをつなぐ橋になっている。

## 4. 現在地

R 版の到達点はこうじゃ。

| Phase | 内容                                           | 状態   |
| ----- | -------------------------------------------- | ---- |
| R001  | real ratio weight 語彙                         | 完了   |
| R002  | real finite budget lemma                     | 完了   |
| R003  | `RealWeightProvider`                         | 完了   |
| R004  | log 正値性                                      | 完了   |
| R005  | external `RealLogBudget`                     | 完了   |
| R006  | index 上 log numerator 非負性                    | 完了   |
| R007  | log-ratio provider                           | 完了   |
| R009  | `sum log = log prod`                         | 完了   |
| R010  | real product bound → log sum bound           | 完了   |
| R011  | nat product bound → `RealLogBudget`          | 完了   |
| R012  | nat product bound → provider sub-probability | 今回完了 |

ここで、R 版の有限 log-ratio weight skeleton はかなり強くなった。

$$
\mathrm{RealLogNonnegOn}(I,\mathrm{pOf})
$$

$$
1 < n
$$

$$
\prod \mathrm{pOf}(q)\le n
$$

があれば、

$$
\frac{\log \mathrm{pOf}(q)}{\log n}
$$

を重みとする provider は sub-probability になる。

## 5. 次の本丸

次の課題は、まさに History にある通り、

$$
\prod_{q\in I}\mathrm{pOf}(q)\le n
$$

を **prime-power / divisor channel 側からどう供給するか** じゃ。

これは、単なる解析補題ではない。
数論側の構造に戻る必要がある。

現在の $\mathrm{pOf}(q)$ は任意関数じゃ。
これを、prime-power witness provider の base prime として、

$$
\mathrm{pOf}(q)=(W.label(n,q,hq)).p
$$

のように読みたい。

そのうえで、

$$
\prod_{q\in I}\mathrm{pOf}(q)\le n
$$

を示す必要がある。

## 6. ここで難しくなる理由

問題は重複じゃ。

もし labels が

$$
q_1=p^2,\qquad q_2=p^3
$$

のように同じ base prime $p$ を読むなら、単純に

$$
\mathrm{pOf}(q_1)\cdot \mathrm{pOf}(q_2)=p^2
$$

を積に入れることになる。

このとき $n$ 側に十分な $p$ -進指数がなければ、

$$
\prod \mathrm{pOf}(q)\le n
$$

は保証できない。

だから、次の本丸は **重複制御** または **指数消費 tracking** じゃ。

DkMath 的に言えば、各 selected label が Big の中の素因子予算をどれだけ消費するかを追跡し、合計しても Big から飛び出さないことを示す必要がある。

## 7. 次の一手: Phase-R013 案

わっちなら、次はいきなり証明に入らず、まず product bound を名前付き predicate にする。

例えば、

```lean
def NatProductBoundOn
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ) : Prop :=
  (I.prod fun q => pOf q) ≤ n
```

または log route に寄せて、

```lean
def RealLogProductBudget
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ) : Prop :=
  RealLogNonnegOn I pOf ∧
  1 < n ∧
  (I.prod fun q => pOf q) ≤ n
```

そして theorem を alias 化する。

```lean
theorem realLogRatioWeightProvider_subProbability_of_productBudget
    ...
```

こうしておくと、後で prime-power 側から product bound を供給するとき、

$$
\prod \mathrm{pOf}(q)\le n
$$

という責務を一つの名前にまとめられる。

## 8. Phase-R014 以降の登山道

その次に、prime-power witness provider と接続する。

候補はこういう predicate じゃ。

```lean
def SelectedBaseProductBound
    (T : PrimePowerDivisorTransitionKernel)
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ) : Prop :=
  (I.prod fun q =>
    if hq : q ∈ T.toDivisorTransitionKernel.index n then
      (W.label n q hq).p
    else
      1) ≤ n
```

ただし、この形は `if hq` が入って少し重くなる。
まずは $I\subseteq T.index(n)$ を別仮定にして、

```lean
pOf q := (W.label n q (hI q hq)).p
```

とする方が綺麗かもしれぬ。

ここは設計が必要じゃ。急がず小さく分けるのがよい。

## 9. 総括

Phase-R012 は、R 版 log route の **product budget 直通 theorem** じゃ。

これで、

$$
\prod \mathrm{pOf}(q)\le n
$$

から、

$$
\sum_q \frac{\log(\mathrm{pOf}(q))}{\log n}\le 1
$$

つまり log-ratio provider の sub-probability まで進めるようになった。

山で言えば、これまでは `RealLogBudget` という仮設支点にザイルを掛けていた。
Phase-R012 で、その支点は

$$
\prod \mathrm{pOf}(q)\le n
$$

という整数積の岩場に結び直された。

次は、その整数積の岩場を prime-power channel の中からどう見つけるか。
ここからが、重複制御と指数消費 tracking の本当の岩稜じゃな。
