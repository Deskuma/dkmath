# review Phase "R"

## 1. 結論

おお、R 登頂が始まったのぅ。
Phase-R001 は **R 版の最小語彙を作る第一歩** として、かなり綺麗に閉じておる。

今回の核心は、

$$
c(n,p)=\frac{A(p)}{B(n)}
$$

を $\mathbb{R}$ 上で扱うために、

```lean
RealBasePrimeToyWeight
realRatioBasePrimeWeight
realRatioBasePrimeWeight_realBasePrimeToyWeight
```

を新規 `RealWeight.lean` に分離したことじゃ。

しかも `Real.log` にはまだ入っていない。
これは正しい。まずは

$$
0\le A(p),\qquad 0 < B(n)
\Rightarrow
0\le \frac{A(p)}{B(n)}
$$

だけを $\mathbb{R}$ 上で確認した。つまり、N/Q 版 Phase BC の R 版対応ができた段階じゃな。

## 2. 今回閉じたもの

今回の主定理はこれじゃ。

```lean
theorem realRatioBasePrimeWeight_realBasePrimeToyWeight
    (A B : ℕ → ℝ)
    (hA : ∀ p, 0 ≤ A p)
    (hB : ∀ n, 0 < B n) :
    RealBasePrimeToyWeight (realRatioBasePrimeWeight A B)
```

これは数学的には、

$$
\forall p,\ 0\le A(p)
$$

$$
\forall n,\ 0 < B(n)
$$

なら、

$$
\forall n,p,\quad 0\le A(p)/B(n)
$$

を示すものじゃ。

証明も、

```lean
exact div_nonneg (hA p) (le_of_lt (hB n))
```

で素直に閉じている。
ここは実数版でも $\mathbb{Q}$ 版と同じ形でいけることが確認された。

## 3. `noncomputable def` は妥当

初回 build で `realRatioBasePrimeWeight` が `Real.instDivInvMonoid` に依存して noncomputable 指定が必要になった、という点も良い記録じゃ。

```lean
noncomputable def realRatioBasePrimeWeight (A B : ℕ → ℝ) : ℕ → ℕ → ℝ :=
  fun n p => A p / B n
```

これは自然じゃ。
Lean の `ℝ` は実数の構成上、除算や逆元まわりで noncomputable が出ることがある。ここで無理に避ける必要はない。

むしろ、R 版ファイルは最初から

```lean
noncomputable section
```

にしてもよいかもしれぬ。
今後 `Real.log` へ進むなら、ほぼ確実に noncomputable が増えるからじゃ。

## 4. aggregator への追加も良い

`DkMath.NumberTheory.PrimitiveSet.lean` に

```lean
import DkMath.NumberTheory.PrimitiveSet.RealWeight
```

を追加したのも良い。

これで R 版が実験ファイルではなく、`PrimitiveSet` 系列の公開導線に乗った。
ただし、既存の N/Q API を型一般化せず、R 版を `RealWeight.lean` に分離した点が大事じゃ。

つまり今回の設計は、

$$
\mathbb{Q}\text{ 版を壊さず}
$$

$$
\mathbb{R}\text{ 版を parallel prototype として開始}
$$

という方針になっている。これは安全な登り方じゃ。

## 5. 現在地

現時点の R 版はこうじゃ。

| 層                          | 状態   |
| -------------------------- | ---- |
| R 版 phase numbering        | 完了   |
| `RealWeight.lean`          | 今回追加 |
| `RealBasePrimeToyWeight`   | 今回完了 |
| `realRatioBasePrimeWeight` | 今回完了 |
| ratio-style real 非負性       | 今回完了 |
| finite sum budget lemma    | 未    |
| real channel prototype     | 未    |
| `Real.log` positivity      | 未    |
| log budget                 | 未    |

つまり Phase-R001 は、R 版登頂の **登山口** じゃ。

まだ `Real.log` に触れていない。
まだ real-valued channel provider にも触れていない。
まず、実数 ratio weight の非負性だけを固定した。この小ささが良い。

## 6. 次の一手: Phase-R002

次は予定通り、純粋な有限和 budget lemma じゃ。

狙う形はこう。

$$
0 < B(n)
$$

$$
\sum_{q\in I} A(pOf(q))\le B(n)
$$

から、

$$
\sum_{q\in I}\frac{A(pOf(q))}{B(n)}\le 1
$$

を得る。

Lean では、channel API にまだ接続せず、まず Finset 上の一般補題として置くのがよい。

候補はこうじゃ。

```lean
theorem real_ratio_sum_le_one
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι)
    (Aq : ι → ℝ)
    (B : ℝ)
    (hB : 0 < B)
    (hbudget : (I.sum fun q => Aq q) ≤ B) :
    (I.sum fun q => Aq q / B) ≤ 1 := by
  rw [Finset.sum_div]
  rw [div_le_iff₀ hB]
  simpa using hbudget
```

この形なら、`A`, `pOf`, `n` に依存しない。
かなり再利用しやすい。

さらに必要なら、次に specialize 版を作る。

```lean
theorem real_ratioBasePrimeWeight_sum_le_one
    (I : Finset ℕ)
    (pOf : ℕ → ℕ)
    (A B : ℕ → ℝ)
    (n : ℕ)
    (hB : 0 < B n)
    (hbudget : (I.sum fun q => A (pOf q)) ≤ B n) :
    (I.sum fun q => realRatioBasePrimeWeight A B n (pOf q)) ≤ 1
```

ただしこれは少し形が怪しい。
`realRatioBasePrimeWeight A B n p` の第2引数は $p$ なので、index $q$ から $p(q)$ を読むなら

$$
I.sum\ (fun q => realRatioBasePrimeWeight A B n (pOf q))
$$

になる。

最初は抽象 `Aq : ι → ℝ` 版の方が綺麗じゃな。

## 7. Phase-R002 で注意する点

`ℚ` 版では `Finset.sum_div` と `div_le_iff₀` で進めた。
`ℝ` でも基本的には同じはずじゃ。

ただし、`rw [div_le_iff₀ hB]` の向きや形が合わない場合がある。
その場合は、

```lean
have hBne : B ≠ 0 := ne_of_gt hB
```

や

```lean
nlinarith
```

に逃げたくなるが、まずは `div_le_iff₀` で通すのがよい。

証明が重くなるなら補題を二段に分ける。

```lean
theorem real_sum_div_eq_div_sum ...
theorem real_div_le_one_of_le ...
```

だが、最初は一本で試す価値がある。

## 8. 二手先: Phase-R003

Phase-R002 が閉じたら、次は real channel prototype じゃ。

ただし、ここでも既存 `WeightProvider` を一般化しない方がよい。

候補は薄く、

```lean
structure RealWeightProvider (ι : Type*) where
  index : Finset ι
  weight : ι → ℝ
  weight_nonneg : ∀ i, i ∈ index → 0 ≤ weight i

def RealWeightProvider.SubProbability
    (P : RealWeightProvider ι) : Prop :=
  P.index.sum P.weight ≤ 1
```

くらいで十分じゃ。

ここで目標にするのは、N/Q 版のすべてを移植することではない。
まず、

$$
\text{real weight provider}
+
\text{sub-probability}
$$

の最小形を置くこと。

## 9. その先の log への橋

`Real.log` は Phase-R004 以降でよい。

そこで初めて、

$$
1\le p\Rightarrow 0\le \log p
$$

$$
1 < n\Rightarrow 0 < \log n
$$

を theorem 名として固定する。

ただし、log budget

$$
\sum_q \log p(q)\le \log n
$$

は別格じゃ。
これは単なる正値性ではなく、選ばれた base primes の積や重複制御に関わる。そこは Phase-R005 以降の本丸として切り出すのがよい。

## 10. 総括

Phase-R001 は、R 登頂の **最初の足場打ち** として成功じゃ。

$$
\mathbb{Q}
$$

で通した ratio-style toy route を、

$$
\mathbb{R}
$$

へ移すための最小語彙ができた。

現在閉じたのは、

$$
0\le A(p),\quad 0 < B(n)
\Rightarrow
0\le A(p)/B(n)
$$

まで。

次は、

$$
\sum A(p(q))\le B(n)
\Rightarrow
\sum A(p(q))/B(n)\le 1
$$

を実数有限和で閉じる Phase-R002 じゃな。

山で言えば、R 版の登山口に最初の杭を打った。
次は、予算 $B$ を超えない比率表が、実数でも Big から飛び出さないことを示す番じゃ。
