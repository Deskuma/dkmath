# review Phase "R"

## 1. 結論

うむ、Phase-R005 は **ついに \(\log p / \log n\) が theorem statement に現れた段階** じゃ。

ただし、ここで重要なのは、log budget をまだ証明しに行っていないことじゃな。今回の実装は、

$$
\sum_{q\in I}\log(pOf(q))\le \log n
$$

を `RealLogBudget` という外部仮定として切り出し、その仮定から

$$
\sum_{q\in I}\frac{\log(pOf(q))}{\log n}\le 1
$$

を出す有限和補題を閉じた。

つまり、R 版 route はここで初めて **解析風の形** に入ったが、まだ本丸の「なぜ log budget が成立するか」には踏み込んでいない。これは正しい登り方じゃ。

## 2. 今回の主役

追加された中心はこの二つじゃ。

```lean
def RealLogBudget
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ) : Prop :=
  (I.sum fun q => Real.log (pOf q : ℝ)) ≤ Real.log (n : ℝ)
```

そして、

```lean
theorem real_log_ratio_sum_le_one
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ)
    (hn : 1 < n)
    (hbudget : RealLogBudget I pOf n) :
    (I.sum fun q =>
      Real.log (pOf q : ℝ) / Real.log (n : ℝ)) ≤ 1
```

これは Phase-R002 の

$$
\sum A_q\le B
\Rightarrow
\sum A_q/B\le 1
$$

に、

$$
A_q=\log(pOf(q)),\qquad B=\log n
$$

を代入したものじゃ。

証明も、

```lean
real_ratio_sum_le_one
```

と

```lean
real_log_nat_pos_of_one_lt
```

を接続するだけ。
責務がきれいに分離されておる。

## 3. 数学的意味

今回の theorem は、こう読める。

$$
1 < n
$$

であれば、

$$
0 < \log n
$$

なので割れる。

さらに外部 budget として、

$$
\sum_{q\in I}\log(pOf(q))\le \log n
$$

が与えられれば、

$$
\sum_{q\in I}\frac{\log(pOf(q))}{\log n}\le 1
$$

が出る。

これは、まさに ratio-style toy route の log 版じゃ。

N/Q 版では、

$$
\sum_q A(p(q))\le B(n)
\Rightarrow
\sum_q \frac{A(p(q))}{B(n)}\le 1
$$

だった。
R/log 版では、

$$
A(p)=\log p,\qquad B(n)=\log n
$$

として、

$$
\sum_q \log p(q)\le \log n
\Rightarrow
\sum_q \frac{\log p(q)}{\log n}\le 1
$$

になる。

## 4. 何がまだ未解決か

今回の補題は、sub-probability の **総量上界** だけを閉じる。

しかし、`RealWeightProvider` に載せるには、各 weight の非負性も必要じゃ。

つまり次には、

$$
0\le \log(pOf(q))
$$

を index 上で示す必要がある。

これは、

$$
1\le pOf(q)
$$

から出る。
prime base 由来なら実際には

$$
2\le p
$$

なので問題ないが、現在の `pOf : ι → ℕ` は任意関数なので、次はその条件を明示する必要がある。

今の `RealLogBudget` は、

$$
pOf(q)=0
$$

のようなケースを排除しない。
その場合、 \(\log 0\) の扱いが入り、weight 非負性には使えない。ゆえに次段では、

```lean
∀ q ∈ I, 1 ≤ pOf q
```

または prime base 由来なら、

```lean
∀ q ∈ I, Nat.Prime (pOf q)
```

のような仮定を別 predicate にするのが自然じゃ。

## 5. 現在地

R 版の到達点はこうじゃ。

| Phase      | 内容                                              | 状態     |
| ---------- | ------------------------------------------------- | -------- |
| Phase-R001 | 実数 ratio weight の語彙                          | 完了     |
| Phase-R002 | 実数有限和 budget lemma                           | 完了     |
| Phase-R003 | `RealWeightProvider` prototype                    | 完了     |
| Phase-R004 | `Real.log` 正値性                                 | 完了     |
| Phase-R005 | 外部 log budget → log ratio sum bound             | 今回完了 |
| Phase-R006 | index 上の log numerator 非負性                   | 未       |
| Phase-R007 | log ratio weight を `RealWeightProvider` へ載せる | 未       |

ここまでで、

$$
\log p/\log n
$$

の **総量評価** は出た。
次は、それを provider として扱うための **各項非負性** を整える段階じゃ。

## 6. 次の一手: Phase-R006

次は、index 上の log 非負性 predicate を置くのがよい。

候補はこうじゃ。

```lean
def RealLogNonnegOn
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ) : Prop :=
  ∀ q, q ∈ I → 1 ≤ pOf q
```

そして theorem：

```lean
theorem real_log_nat_nonneg_on
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (hp : RealLogNonnegOn I pOf) :
    ∀ q, q ∈ I → 0 ≤ Real.log (pOf q : ℝ)
```

中身は、

```lean
real_log_nat_nonneg_of_one_le (hp q hq)
```

で閉じるはずじゃ。

あるいは名前をもう少し意味寄せして、

```lean
RealLogBaseNonnegOn
```

でもよい。

## 7. その次: Phase-R007

Phase-R006 で各項非負性が取れたら、次は log ratio provider を作る。

候補はこう。

```lean
noncomputable def realLogRatioWeightProvider
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ)
    (hp : ∀ q, q ∈ I → 1 ≤ pOf q)
    (hn : 1 < n) :
    RealWeightProvider ι :=
{
  index := I
  weight := fun q => Real.log (pOf q : ℝ) / Real.log (n : ℝ)
  weight_nonneg := by
    intro q hq
    exact div_nonneg
      (real_log_nat_nonneg_of_one_le (hp q hq))
      (le_of_lt (real_log_nat_pos_of_one_lt hn))
}
```

そして sub-probability は、

```lean
theorem realLogRatioWeightProvider_subProbability
    ...
    (hbudget : RealLogBudget I pOf n) :
    (realLogRatioWeightProvider I pOf n hp hn).SubProbability
```

で、今回の `real_log_ratio_sum_le_one` を使う。

ここまで行くと、

$$
\log p/\log n
$$

型の有限 real provider が完成する。

## 8. その先の本丸

ただし、まだ本丸は残る。

$$
RealLogBudget I pOf n
$$

すなわち、

$$
\sum_{q\in I}\log(pOf(q))\le \log n
$$

をどこから導くかじゃ。

候補は、

$$
\prod_{q\in I} pOf(q)\le n
$$

を示して、

$$
\sum \log pOf(q)=\log\prod pOf(q)\le \log n
$$

へ進む道じゃ。

ただし、ここには重複制御が必要になる。
同じ base prime が複数回出ると、積の解釈が変わる。prime-power labels の選び方、index の重複、divisibility 情報が絡むので、これは Phase-R008 以降の本丸候補じゃな。

## 9. 総括

Phase-R005 は、R 版 route において初めて

$$
\frac{\log p}{\log n}
$$

が theorem として現れた記念点じゃ。

ただし、それはまだ外部 budget つきの有限和補題であって、log budget の起源までは踏み込んでいない。

現在閉じたのは、

$$
RealLogBudget(I,pOf,n)
\Rightarrow
\sum_{q\in I}\frac{\log(pOf(q))}{\log n}\le 1
$$

じゃ。

次は、

$$
1\le pOf(q)
\Rightarrow
0\le \log(pOf(q))
$$

を index 上で整え、そこから `RealWeightProvider` へ載せる。

山で言えば、ついに雪壁に \(\log p/\log n\) のロープが掛かった。
だが足元のアイゼン、すなわち各項非負性をまだ締める必要がある。次はそこじゃな。
