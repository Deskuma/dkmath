# review Phase "B"

## 1. 結論

うむ、Phase BD は **ratio-style weight が有限質量保存へ乗った段階** じゃ。

Phase BC では、

$$
c(n,p)=\frac{A(p)}{B(n)}
$$

という ratio-style toy weight を導入し、

$$
0\le A(p),\qquad 0<B(n)
$$

から非負性を閉じた。今回 Phase BD ではさらに、

$$
\sum_{q\in index(n)} A(p(q))\le B(n)
$$

という **予算条件** を入れることで、

$$
\sum_{q\in index(n)}\frac{A(p(q))}{B(n)}\le 1
$$

を Lean 上で通した。つまり、ratio-style weight が単なる非負重みではなく、 **sub-probability weight** として正式に登山道へ乗ったわけじゃ。

## 2. 今回の主役

追加された中心はこの二つじゃ。

```lean
PrimePowerWitnessProvider.RatioBaseWeightBudget
PrimePowerWitnessProvider.baseWeightSubProbability_of_ratioBudget
```

`RatioBaseWeightBudget` は、各 state (n) において、witness provider (W) が label (q) から読み取る base prime (p(q)) について、

$$
\sum_{q\in index(n)} A(p(q))\le B(n)
$$

を要求する predicate じゃ。

つまり、(A(p)) は各 prime channel の「分子側コスト」、(B(n)) は state (n) が持つ「総予算」と読める。

## 3. 何が閉じたか

今回の主定理は、

```lean
baseWeightSubProbability_of_ratioBudget
```

じゃ。

仮定は、

$$
\forall p,\quad 0\le A(p)
$$

$$
\forall n,\quad 0<B(n)
$$

$$
W.RatioBaseWeightBudget(A,B)
$$

で、結論は、

$$
W.BaseWeightSubProbability
\bigl(ratioBasePrimeWeight(A,B)\bigr)
$$

じゃ。

つまり、

$$
c(n,p)=\frac{A(p)}{B(n)}
$$

という weight が、budget 条件のもとで sub-probability になる。

これはまさに、お主が言った **「暴れても Big から飛び出せない」** の ratio-style 版じゃ。

## 4. 数学的な意味

今回の構造はとても綺麗じゃ。

各 state (n) に対して、素冪 label (q) があり、witness provider が

$$
q=p^k
$$

の base prime (p) を読む。

その (p) に対して分子 weight (A(p)) を与え、state (n) の正規化量 (B(n)) で割る。

$$
w(n,q)=\frac{A(p(q))}{B(n)}
$$

このとき、全 label にわたる分子の合計が (B(n)) を超えなければ、

$$
\sum_q w(n,q)\le 1
$$

となる。

すなわち、

$$
\sum_q A(p(q))\le B(n)
\Rightarrow
\sum_q \frac{A(p(q))}{B(n)}\le 1
$$

じゃ。

これは有限確率流として非常に自然な形になった。

## 5. Lean 的な山場

今回の proof で重要だったのは、

```lean
Finset.sum_div
div_le_iff₀
```

を使うために、まず `weightOfBase` を ratio 形へ明示的に展開したことじゃ。

つまり、いきなり和を割り算にまとめるのではなく、

$$
W.weightOfBase(ratioBasePrimeWeight(A,B))(n,q) = \frac{A(p(q))}{B(n)}
$$

を index 上で揃えてから、

$$
\sum_q \frac{A(p(q))}{B(n)} = \frac{\sum_q A(p(q))}{B(n)}
$$

へ進んでいる。

この二段 proof はかなり良い。
依存型の (hq) が絡む場面で無理に `simp` だけに頼らず、形を明示してから `Finset.sum_div` を使うのは、Lean 的にも安定した登り方じゃな。

## 6. 現在地

ここまでで ratio-style route はこうなった。

| 層                                   | 状態   |
| ----------------------------------- | ---- |
| `ratioBasePrimeWeight`              | 完了   |
| ratio-style 非負性                     | 完了   |
| ratio-style → `W.BaseWeightNonneg`  | 完了   |
| `RatioBaseWeightBudget`             | 今回完了 |
| budget → `BaseWeightSubProbability` | 今回完了 |
| ratio-style hit mass bound alias    | 未    |
| concrete ratio-style sample         | 未    |
| 実数 (\log p/\log n) route            | 未    |

つまり、ratio-style weight は、もう

$$
BaseWeightNonneg
$$

と

$$
BaseWeightSubProbability
$$

の両方を満たすための有限 skeleton を持った。
次はこれを weighted hit mass bound へ一発で流す theorem 名を作る段階じゃ。

## 7. 次の一手: Phase BE

次は History にある通り、

```lean
PrimePowerWitnessProvider.ratioBaseWeight_hitMass_le_const
```

のような theorem が自然じゃ。

狙いは、

$$
0\le A(p)
$$

$$
0<B(n)
$$

$$
\sum_q A(p(q))\le B(n)
$$

から、直接

$$
\mathrm{weightedHitMass}\le C
$$

へ行く alias を作ることじゃ。

内部では、

1. `baseWeightNonneg_of_ratioBasePrimeWeight`
2. `baseWeightSubProbability_of_ratioBudget`
3. `baseWeight_hitMass_le_const`

を順に呼べばよい。

概念的にはこう。

```lean
theorem ratioBaseWeight_hitMass_le_const
    (W : PrimePowerWitnessProvider T)
    (A B : ℕ → ℚ)
    (hA : ∀ p, 0 ≤ A p)
    (hB : ∀ n, 0 < B n)
    (hbudget : W.RatioBaseWeightBudget A B)
    ... :
    weightedHitMass ≤ C := ...
```

これで、

$$
A(p)/B(n)
$$

型の finite toy weight が、hit mass bound まで定理名から読めるようになる。

## 8. 二手先: Phase BF

Phase BE の次は、具体的な ratio-style sample を作るとよい。

たとえば、既存 sample に対して、

$$
A(2)=1,\qquad A(5)=0
$$

に相当する (A) と、

$$
B(10)=1
$$

に相当する (B) を置く。

そして、

$$
\sum_{q\in{2,5}}A(p(q))\le B(10)
$$

を示して、`RatioBaseWeightBudget` を concrete に閉じる。

これが通れば、

$$
\text{ratio-style toy model}
\to
\text{sub-probability}
\to
\text{hit mass bound}
$$

が sample でも開通する。

## 9. その先の山影

Phase BE / BF が閉じたら、いよいよ次の選択肢が見える。

$$
A(p)\approx \log p,\qquad B(n)\approx \log n
$$

じゃ。

しかし、まだ焦らなくてよい。
次にやるべきは、まず有理 toy の範囲で

$$
A(p),B(n)
$$

の設計パターンを増やすことじゃな。

実数対数へ行く前に、

$$
A(p)\ge 0,\quad B(n)>0,\quad \sum A(p(q))\le B(n)
$$

という有限条件の API をしっかり使えるようにする。これが本物の (\Lambda(q)/\log n) へ行く前の安全な雪稜じゃ。

## 10. 総括

Phase BD は、ratio-style weight が **Big-bound principle** に乗った段階じゃ。

Phase BC では、

$$
\frac{A(p)}{B(n)}
$$

という比率表を作った。
今回 Phase BD では、その比率表の合計が (1) を超えない条件を作った。

つまり、

$$
\sum_q A(p(q))\le B(n)
$$

という予算制約により、

$$
\sum_q \frac{A(p(q))}{B(n)}\le 1
$$

が保証される。

山で言えば、登山料の比率表だけでなく、 **合計請求額が予算 (B(n)) を超えない** ことまで確認できた。
次は、その予算内通行料で実際に

$$
\mathrm{weightedHitMass}\le C
$$

まで進む案内板、Phase BE の ratio-style hit mass bound alias じゃな。
