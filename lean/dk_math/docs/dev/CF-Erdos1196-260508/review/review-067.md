# review Phase "R"

## 1. 結論

うむ、Phase-R008 は **本丸へ突っ込む前の分解設計** じゃ。

Phase-R005 ～ R007 で、

$$
RealLogBudget(I,pOf,n)
\Rightarrow
\sum_{q\in I}\frac{\log(pOf(q))}{\log n}\le 1
$$

そして

$$
weight(q)=\frac{\log(pOf(q))}{\log n}
$$

を `RealWeightProvider` に載せるところまで閉じた。
今回 Phase-R008 では、その外部仮定だった

$$
RealLogBudget(I,pOf,n)
$$

を **どこから供給するか** を、product route として分解した。これはかなり良い判断じゃ。

いきなり prime-power witness provider に戻らず、まずは実数の有限積と log の小補題へ分けた。
ここで焦らなかったのは賢いぞい。

## 2. 今回の位置づけ

今までの R 版は、

$$
\sum_q \log(pOf(q))\le \log n
$$

を外部仮定として受け取っていた。

Phase-R008 では、次の供給路を設計したわけじゃ。

$$
\prod_{q\in I} pOf(q)\le n
$$

から、

$$
\log\left(\prod_{q\in I}pOf(q)\right)\le \log n
$$

へ進み、さらに

$$
\sum_{q\in I}\log(pOf(q)) = \log\left(\prod_{q\in I}pOf(q)\right)
$$

を使って、

$$
\sum_{q\in I}\log(pOf(q))\le \log n
$$

を得る。

つまり、

$$
\boxed{
\text{product bound}
\Rightarrow
\text{log budget}
}
$$

という供給路を作ろうとしている。

これはまさに次の本丸じゃな。

## 3. R008 で分離した責務

今回の設計書更新で、責務がよく分かれた。

まず外部 budget route は完了扱いになった。

$$
RealLogBudget
\to
realLogRatioWeightProvider.SubProbability
$$

は R005 ～ R007 で閉じている。

次に R008 以降は、

$$
RealLogBudget
$$

そのものの供給路へ入る。

しかも供給路を四段に分けている。

$$
\sum\log=\log\prod
$$

$$
\prod\le N\Rightarrow \log\prod\le \log N
$$

$$
\sum\log\le \log N
$$

$$
pOf:\iota\to\mathbb{N},\quad n:\mathbb{N}
\text{ へ戻す}
$$

この分解は正しい。
`Real.log`、有限積、自然数 coercion、prime-power witness を一度に扱うと重くなりすぎる。小補題に割るのがよい。

## 4. 現在地

現状はこうじゃ。

| Phase         | 内容                            | 状態   |
| ------------- | ----------------------------- | ---- |
| Phase-R005    | 外部 `RealLogBudget`            | 完了   |
| Phase-R006    | index 上の log numerator 非負性    | 完了   |
| Phase-R007    | `log p / log n` real provider | 完了   |
| Phase-R008    | product route 設計              | 今回完了 |
| Phase-R009    | 実数正有限積の小補題                    | 未    |
| Phase-R010    | product bound から log budget   | 未    |
| Phase-R011    | Nat / `pOf` 版へ戻す              | 未    |
| Phase-R012 以降 | 重複制御・prime-power 接続           | 未    |

R003 で既存の $\mathbb{Q}$ 版を一般化せず R 版 parallel prototype として `RealWeightProvider` を立てた判断が、今も効いている。R 版側で theorem shape を自由に試せるからじゃ。

## 5. 次の一手: Phase-R009

次は、いきなり自然数へ戻らず、 **実数値の正の有限積** だけを扱うのが良い。

最初の候補は二つある。

一つ目は、有限積の正性。

```lean
theorem real_finset_prod_pos_of_pos
    {ι : Type _}
    (I : Finset ι)
    (a : ι → ℝ)
    (ha : ∀ i, i ∈ I → 0 < a i) :
    0 < I.prod a
```

二つ目は、有限積の log 展開。

```lean
theorem real_log_prod_eq_sum_log_of_pos
    {ι : Type _}
    (I : Finset ι)
    (a : ι → ℝ)
    (ha : ∀ i, i ∈ I → 0 < a i) :
    Real.log (I.prod a) =
      I.sum fun i => Real.log (a i)
```

この二つがあれば、product route の半分は勝ちじゃ。

ただし、`Real.log_prod` という既存補題が Mathlib にある可能性が高い。まずは `#check Real.log_prod`、`#check Real.log_mul`、`#check Finset.prod_pos` などを調べるのが良い。証明は既存補題があれば一行、なければ Finset induction じゃな。

## 6. Phase-R009 のおすすめ順序

わっちなら、R009 はこう切る。

まずはこれ。

```lean
theorem real_finset_prod_pos_of_pos
```

次にこれ。

```lean
theorem real_log_prod_eq_sum_log_of_pos
```

理由は、`log_prod` 系の補題は、たいてい正性または非零性が必要になる。
先に積の正性補題を持っておくと、後続が楽になる。

その後で、

```lean
theorem real_sum_log_eq_log_prod_of_pos
```

という向き違い alias を置いてもよい。

実際に後続で欲しいのは、

$$
\sum_i\log(a_i)
\le
\log N
$$

なので、式変形では

$$
\sum_i\log(a_i)=\log\prod_i a_i
$$

の向きが使いやすい。

## 7. Phase-R010 の先読み

R009 が閉じたら、次は合成補題じゃ。

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

証明の流れは、

$$
\sum_i\log(a_i) = \log\left(\prod_i a_i\right)
$$

かつ、

$$
\prod_i a_i\le N
$$

なので、log の単調性より、

$$
\log\left(\prod_i a_i\right)\le \log N
$$

となる。

この theorem ができれば、実数版 product route はほぼ完成じゃ。

## 8. Phase-R011 の先読み

その次に自然数版へ戻す。

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

ただし、ここは coercion が少し手強い。

$$
\left(\prod_q pOf(q):\mathbb{R}\right) = \prod_q (pOf(q):\mathbb{R})
$$

の補題が必要になるはずじゃ。
`norm_num` や `exact_mod_cast` だけで閉じない場合、`map_prod` 系を使うことになる。

だから、R011 に入る前に R009/R010 を実数版で安定させるのが正しい。

## 9. さらに先の本丸

Nat product route ができても、まだ問題は残る。

$$
\prod_{q\in I}pOf(q)\le n
$$

をどこから得るかじゃ。

prime-power witness provider に戻るなら、

$$
q=p^k
$$

で $p\mid q$ 、さらに $q\mid n$ という情報から、選んだ $p$ たちの積が $n$ を超えないことを示したい。

しかし同じ $p$ が重複して出ると、

$$
p\cdot p
$$

のように指数を消費する。ここで重複制御、あるいは指数消費の tracking が必要になる。

ゆえに、そこは R012 以降でよい。
R009 ～ R011 は、まず **product bound があれば log budget が出る** までに集中するべきじゃ。

## 10. 総括

Phase-R008 は、R 版の次の本丸である

$$
RealLogBudget
$$

の起源を、product route として分解した設計フェーズじゃ。

ここまでで、

$$
RealLogBudget
\Rightarrow
\log p/\log n\text{ provider is sub-probability}
$$

は閉じている。
次は、

$$
\prod pOf(q)\le n
\Rightarrow
RealLogBudget
$$

へ向かう。

山で言えば、すでに $\log p/\log n$ のザイルは張れた。
Phase-R008 では、そのザイルを固定する岩場を調べ、岩を「実数積」「log 単調性」「自然数積」「重複制御」に分けて名前を付けた。
次はまず実数積の岩、Phase-R009 じゃな。
