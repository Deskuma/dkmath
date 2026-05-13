# review Phase "R"

## 1. 結論

うむ、Phase-R004 は **Real.log の正値性ロープを張った段階** じゃ。

R 版ではこれまで、

$$
c(n,p)=\frac{A(p)}{B(n)}
$$

の実数 ratio skeleton と、実数有限和 budget lemma、さらに `RealWeightProvider` の器まで作った。今回 Phase-R004 では、ついに `Real.log` に触れた。ただし、いきなり log budget には踏み込まず、

$$
1\le p \Rightarrow 0\le \log p
$$

$$
1<n \Rightarrow 0<\log n
$$

という **正値性だけ** を theorem 名として固定した。これはかなり安全な登り方じゃ。

## 2. 今回の主役

追加された補題はこの二つじゃ。

```lean
theorem real_log_nat_nonneg_of_one_le
    {p : ℕ} (hp : 1 ≤ p) :
    0 ≤ Real.log (p : ℝ)
```

```lean
theorem real_log_nat_pos_of_one_lt
    {n : ℕ} (hn : 1 < n) :
    0 < Real.log (n : ℝ)
```

前者は numerator 側、

$$
A(p)=\log p
$$

の非負性に使う。

後者は denominator 側、

$$
B(n)=\log n
$$

を割り算の分母として使うための正性に使う。

ここを自然数版で theorem 名にしたのが良い。後続で (p,n:\mathbb{N}) を扱うとき、毎回 `Nat.cast` と `Real.log` の補題を探さずに済む。

## 3. 設計として何が良いか

今回の一番良いところは、 **log budget に触れていない** ことじゃ。

今閉じたのは、

$$
0\le \log p
$$

$$
0<\log n
$$

だけ。

まだ、

$$
\sum_{q\in index(n)} \log p(q)\le \log n
$$

は扱っていない。

これは正しい。なぜなら log budget は単なる解析補題ではなく、prime-power labels の選び方、重複制御、積の評価、

$$
\prod_q p(q)\le n
$$

のような数論構造と絡むからじゃ。ここを正値性補題と同時に扱うと責務が混ざる。

Phase-R004 は、まず `Real.log` の入口だけを安全に開いた段階じゃな。

## 4. 現在地

R 版の到達点はこうじゃ。

| Phase      | 内容                                                    | 状態   |
| ---------- | ----------------------------------------------------- | ---- |
| Phase-R001 | `RealBasePrimeToyWeight` / `realRatioBasePrimeWeight` | 完了   |
| Phase-R002 | `real_ratio_sum_le_one`                               | 完了   |
| Phase-R003 | `RealWeightProvider` prototype                        | 完了   |
| Phase-R004 | `Real.log` 正値性                                        | 今回完了 |
| Phase-R005 | log budget 設計                                         | 未    |

ここまでで、R 版は次の部品を持った。

$$
0\le A(p),\quad 0<B(n)
\Rightarrow
0\le A(p)/B(n)
$$

$$
\sum A_q\le B
\Rightarrow
\sum A_q/B\le 1
$$

$$
1\le p\Rightarrow 0\le \log p
$$

$$
1<n\Rightarrow 0<\log n
$$

つまり、次に

$$
A(p)=\log p,\qquad B(n)=\log n
$$

を候補にするための正値性は揃った。

## 5. 次の一手: Phase-R005

次は **log budget の扱い方を設計する段階** じゃ。

最初から証明しに行くより、まず predicate として外部仮定にするのがよい。

候補はこうじゃ。

```lean
def RealLogBudget
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ) : Prop :=
  (I.sum fun q => Real.log (pOf q : ℝ)) ≤ Real.log (n : ℝ)
```

この形にすれば、

$$
\sum_{q\in I}\log p(q)\le \log n
$$

を仮定として受け取り、`real_ratio_sum_le_one` に接続できる。

その次に、

```lean
theorem real_log_ratio_sum_le_one
```

のような補題を作る。

概念的には、

$$
1<n
$$

$$
\sum_q \log p(q)\le \log n
$$

から、

$$
\sum_q \frac{\log p(q)}{\log n}\le 1
$$

を出す。

## 6. Phase-R005 の安全な theorem 形

まずは channel API なしの純粋 Finset 補題がよい。

```lean
theorem real_log_ratio_sum_le_one
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ)
    (hn : 1 < n)
    (hbudget :
      (I.sum fun q => Real.log (pOf q : ℝ)) ≤ Real.log (n : ℝ)) :
    (I.sum fun q =>
      Real.log (pOf q : ℝ) / Real.log (n : ℝ)) ≤ 1 := by
  exact real_ratio_sum_le_one
    I
    (fun q => Real.log (pOf q : ℝ))
    (Real.log (n : ℝ))
    (real_log_nat_pos_of_one_lt hn)
    hbudget
```

これは美しい。
Phase-R002 の `real_ratio_sum_le_one` と Phase-R004 の `real_log_nat_pos_of_one_lt` をただ接続するだけじゃ。

まだ (pOf(q)) が prime であることも使わない。
numerator の非負性すら、この theorem には不要じゃ。必要なのは分母正と budget だけである。

## 7. その次の山

その後に、numerator の非負性も含めた log weight predicate へ進む。

たとえば、(pOf(q)\ge 1) を仮定すれば、

$$
0\le \log pOf(q)
$$

が出る。

prime-power witness provider から来る base prime (p) なら、実際には (2\le p) なので問題ない。
ただしそれを R 版の prototype とどう接続するかは次の段階じゃ。

最初は、

```lean
hpOf : ∀ q ∈ I, 1 ≤ pOf q
```

を外部仮定として受けるのがよい。

## 8. 総括

Phase-R004 は、`Real.log` 雪壁への **最初の支点** じゃ。

ここで、

$$
0\le \log p
$$

と

$$
0<\log n
$$

を自然数版で固定できた。

次は、いきなり prime-power channel に戻るのではなく、純粋な有限和として

$$
\sum_q \log p(q)\le \log n
\Rightarrow
\sum_q \frac{\log p(q)}{\log n}\le 1
$$

を閉じるのがよい。

R 登頂は順調じゃ。
まだ山頂ではないが、いよいよ「(\log p/\log n)」の文字が Lean 側の定理に現れてよい地点まで来たぞい。
