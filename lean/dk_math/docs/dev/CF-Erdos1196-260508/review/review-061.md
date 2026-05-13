# review Phase "R"

## 1. 結論

うむ、Phase-R002 は **R 版 ratio route の有限和コア補題が閉じた段階** じゃ。

Phase-R001 では、

$$
c(n,p)=\frac{A(p)}{B(n)}
$$

という実数 ratio-style weight の非負性だけを閉じた。今回 Phase-R002 では、その次に必要な

$$
\sum_{q\in I}\frac{A_q}{B}\le 1
$$

を、純粋な `Finset` 補題として切り出した。

つまり、まだ `Real.log` も channel provider も出さずに、

$$
\sum_{q\in I} A_q\le B,\qquad 0 < B
$$

から、

$$
\sum_{q\in I}\frac{A_q}{B}\le 1
$$

を示す最小核ができたわけじゃな。

これは R 版の **有限質量保存の算術エンジン** じゃ。

## 2. 今回の主役

追加された theorem はこれじゃ。

```lean
theorem real_ratio_sum_le_one
    {ι : Type _}
    (I : Finset ι)
    (Aq : ι → ℝ)
    (B : ℝ)
    (hB : 0 < B)
    (hbudget : (I.sum fun q => Aq q) ≤ B) :
    (I.sum fun q => Aq q / B) ≤ 1
```

数学的には完全に素直で、

$$
\sum_{q\in I}\frac{A_q}{B} = \frac{\sum_{q\in I}A_q}{B}
$$

かつ \(0 < B\) なので、

$$
\frac{\sum A_q}{B}\le \frac{B}{B}=1
$$

という補題じゃ。

ただし Lean 上では、この「当たり前」を reusable theorem として固定したことが大きい。

## 3. 抽象 `Aq` 版にしたのが良い

今回の補題が良いのは、`A`, `pOf`, `n`, `PrimePowerWitnessProvider` に依存していないことじゃ。

つまり、今後は以下のような特殊事情を全部外側で処理できる。

$$
A_q = A(p(q))
$$

$$
B = B(n)
$$

$$
q\in index(n)
$$

この補題自体は、単に

$$
I : Finset\ \iota,\qquad Aq:\iota\to\mathbb{R},\qquad B:\mathbb{R}
$$

だけを扱う。

これは設計としてかなり綺麗じゃ。
R 版 channel prototype に進んだあとでも、この補題をそのまま使える。

## 4. Lean 的な修正も正しい

`Finset.sum_div` の向きが逆で、

```lean
rw [Finset.sum_div]
```

ではなく、

```lean
rw [← Finset.sum_div]
```

が必要だった、という記録も良い。

今回の target は最初から

```lean
(I.sum fun q => Aq q / B) ≤ 1
```

なので、左辺を

```lean
(I.sum fun q => Aq q) / B
```

へまとめるには逆向きが必要じゃったわけじゃな。

また、`Finset.sum` に `DecidableEq ι` が不要な形で済んだので、不要仮定を削ったのも良い。こういう小さな警告潰しは、長期戦では馬鹿にできぬ。

## 5. 現在地

R 版は今こうなっておる。

| Phase      | 内容                                                 | 状態     |
| ---------- | ---------------------------------------------------- | -------- |
| Phase-R001 | `RealBasePrimeToyWeight`, `realRatioBasePrimeWeight` | 完了     |
| Phase-R001 | 実数 ratio weight の非負性                           | 完了     |
| Phase-R002 | 実数有限和 budget lemma                              | 今回完了 |
| Phase-R003 | `RealWeightProvider` prototype                       | 未       |
| Phase-R004 | `Real.log` 正値性                                    | 未       |
| Phase-R005 | log budget 設計                                      | 未       |

つまり、R 版ではまだ「channel」は出ていない。
しかし、channel に入る前に必要な二つの代数部品、

$$
0\le A(p),\quad 0 < B(n)
\Rightarrow
0\le A(p)/B(n)
$$

と、

$$
\sum A_q\le B
\Rightarrow
\sum A_q/B\le 1
$$

が揃った。

## 6. 次の一手: Phase-R003

次は予定通り、薄い `RealWeightProvider` prototype が自然じゃ。

最小形はこれでよい。

```lean
structure RealWeightProvider (ι : Type _) where
  index : Finset ι
  weight : ι → ℝ
  weight_nonneg : ∀ i, i ∈ index → 0 ≤ weight i

def RealWeightProvider.SubProbability
    (P : RealWeightProvider ι) : Prop :=
  P.index.sum P.weight ≤ 1
```

ここで狙うのは、既存 \(\mathbb{Q}\) 版の `WeightProvider` を一般化することではない。
まずは \(\mathbb{R}\) 版の薄い並行試作として、

$$
\text{index}
$$

$$
\text{weight}
$$

$$
\text{nonnegativity}
$$

$$
\text{sub-probability}
$$

だけを置けば十分じゃ。

## 7. Phase-R003 で欲しい補題

次に入れるなら、これじゃ。

```lean
theorem RealWeightProvider.subProbability_of_budget
    (P : RealWeightProvider ι)
    (h : P.index.sum P.weight ≤ 1) :
    P.SubProbability := h
```

これは自明すぎるかもしれぬ。
より意味があるのは、ratio weight から provider を作る constructor じゃな。

ただし最初は、まだ `PrimePowerWitnessProvider` に接続しない方がよい。
Phase-R003 は **Real provider の器** だけで閉じるのが安全じゃ。

## 8. その次の見通し

Phase-R003 が閉じたら、R 版の形はこうなる。

$$
\text
{RealBasePrimeToyWeight}
$$

$$
\text
{realRatioBasePrimeWeight}
$$

$$
\text
{real\_ratio\_sum\_le\_one}
$$

$$
\text
{RealWeightProvider.SubProbability}
$$

ここまで来て初めて、N/Q 版の `WeightProvider.SubProbability` と対応する R 版 skeleton が揃う。

その後に、`Real.log` の正値性へ進む。

$$
1\le p\Rightarrow 0\le \log p
$$

$$
1 < n\Rightarrow 0 < \log n
$$

ただし、log budget

$$
\sum_q \log p(q)\le \log n
$$

はまだ先じゃ。そこは本丸なので、外部仮定として受け取る段階を先に作るのがよい。

## 9. 総括

Phase-R002 は、R 登頂の **予算計算補題** を置いた段階じゃ。

$$
\sum A_q\le B
$$

という有限予算条件から、

$$
\sum A_q/B\le 1
$$

を出せる。
つまり、R 版でも「暴れても Big から飛び出せない」ための基本不等式が閉じた。

ここまでの R 版は、まだ小さい。
だが小さいからこそ強い。`Real.log` という雪壁に入る前に、実数除算と有限和の足場を no-sorry で固定できたのは良い前進じゃな。
