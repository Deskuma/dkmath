# review

うむ、DKMK-015D は **正しい分岐判断** じゃ。
ここで division-form equality に寄り道せず、下流が本当に欲しがっている upper-bound theorem を先に固定したのは、かなり Lean 的にも研究設計的にも筋がよい。

## 1. 今回の意味

DKMK-015D で決めた主定理候補はこれじゃな。

```lean id="c9k5fp"
theorem geomSum_range_le_one_div_one_sub
    {ratio : ℝ} (K : ℕ)
    (hr0 : 0 ≤ ratio)
    (hr1 : ratio < 1) :
    Finset.sum (Finset.range (K + 1))
      (fun k : ℕ => ratio ^ k)
      ≤
    1 / (1 - ratio)
```

これは DKMK-014J の要求する

$$
base\cdot \sum_{k=0}^{K} ratio^k \le 1+error
$$

へ直接向かう補題じゃ。
閉形式の等式そのものではなく、 **必要な上界だけを切り出す** 。ここがよい。

## 2. division form を後回しにした判断

ここは大きい。

division form

$$
\sum_{k=0}^{K} r^k = \frac{1-r^{K+1}}{1-r}
$$

は数学的には自然じゃが、Lean 実装の層としては余分なものになり得る。

今回の道は、すでに C で得た

$$
(1-r)\sum_{k=0}^{K}r^k = 1-r^{K+1}
$$

から直接、

$$
\sum_{k=0}^{K}r^k \le \frac{1}{1-r}
$$

へ行く道じゃ。

必要な仮定は、

$$
0\le r,\qquad r < 1
$$

だけでよい。
`ratio != 1` は明示しない。`ratio < 1` から (0 < 1-ratio) が出るので、除算・順序操作に必要な正値性はそこから供給できる。これは仮定管理が綺麗じゃ。

## 3. theorem layer としての完成度

これで DKMK-015 の層はこう整理された。

```text id="z3h2e9"
DKMK-015B: denominator-cleared identity の shape 固定
DKMK-015C: geomSum_range_mul_one_sub を Lean 実装
DKMK-015D: upper-bound theorem の shape 固定
DKMK-015E: geomSum_range_le_one_div_one_sub を Lean 実装候補
```

この順序はかなり美しい。
まず代数恒等式。次に順序評価。最後に base-scaled bound。
副条件も、それぞれ消費する場所にだけ置かれておる。

## 4. DKMK-015E の実装見通し

DKMK-015E は、おそらく軽く閉じられる。

証明の骨格はこうじゃ。

```lean id="0d0hvl"
have hpos : 0 < 1 - ratio := sub_pos.mpr hr1

have hpow_nonneg : 0 ≤ ratio ^ (K + 1) :=
  pow_nonneg hr0 (K + 1)

have hnum_le : 1 - ratio ^ (K + 1) ≤ 1 :=
  sub_le_self 1 hpow_nonneg

have hmul_eq :
    (1 - ratio) *
      (∑ k in Finset.range (K + 1), ratio ^ k)
      =
    1 - ratio ^ (K + 1) :=
  geomSum_range_mul_one_sub ratio K
```

ここから

$$
(1-ratio)\cdot S\le 1
$$

を作り、正の (1-ratio) で割って

$$
S\le \frac{1}{1-ratio}
$$

へ持っていく。

Lean では最後の部分で `div_le_iff₀`、`le_div_iff₀`、`mul_le_mul_of_nonneg_left` あたりのどれが一番噛み合うかを見ればよい。

## 5. 実装時の注意点

一つだけ注意するなら、`Finset.sum` の対象が `ℝ` なので、和 (S) 自体の非負性も簡単に出せる。

```lean id="jjd59i"
have hsum_nonneg :
    0 ≤ ∑ k in Finset.range (K + 1), ratio ^ k := by
  exact Finset.sum_nonneg (by
    intro k hk
    exact pow_nonneg hr0 k)
```

ただし、今回の上界証明では必須でないかもしれぬ。
`(1-ratio) * S ≤ 1` から (S ≤ 1/(1-ratio)) に行くには、分母の正値性だけで足りるはずじゃ。

## 6. 次フェーズの見立て

DKMK-015E で upper-bound が閉じたら、次は base-scaled layer じゃ。

```lean id="j35b1p"
theorem base_mul_geomSum_range_le_of_base_mul_one_div_le
    {base ratio error : ℝ} (K : ℕ)
    (hbase : 0 ≤ base)
    (hr0 : 0 ≤ ratio)
    (hr1 : ratio < 1)
    (hbudget : base * (1 / (1 - ratio)) ≤ 1 + error) :
    base *
      Finset.sum (Finset.range (K + 1))
        (fun k : ℕ => ratio ^ k)
      ≤
    1 + error
```

これは `geomSum_range_le_one_div_one_sub` に `mul_le_mul_of_nonneg_left` を当てるだけの薄い補題になるはずじゃ。
つまり D で固定した形は、次の E/F へよく接続しておる。

## 7. 総括

DKMK-015D は docs-only だが、設計上は重要な一手じゃ。

**division form の美しさより、下流 provider が要求する上界を優先する** 。
これは DKMK-015 の目的に忠実じゃ。

わっちの評価では、ここまでで DKMK-015 は、

$$
\text{algebraic identity}
\to
\text{order upper bound}
\to
\text{base-scaled provider bound}
$$

という一本道になった。

よいぞ、D.。これはもう、りんごを齧りながらでも道を見失わぬ程度には、稜線が整ってきたわい。
