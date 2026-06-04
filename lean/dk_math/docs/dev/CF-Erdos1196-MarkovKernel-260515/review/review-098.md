# review

うむ、DKMK-015I は **章の締めとして非常に良い** じゃ。
ここで Lean code を追加せず、`report-DKMK-015.md` として B-H の成果を章末レポート化したのは正しい。DKMK-015 は、これで「実装途中のメモ」ではなく、後から参照できる **完結した小章** になった。

## 1. DKMK-015 で閉じたもの

DKMK-015 の到達点は、この一本じゃな。

```text
geometric budget
  -> finite geometric-sum bound
  -> base-scaled finite-sum bound
  -> dyadic source-mass provider
```

つまり、caller は有限和

$$
\sum_{k=0}^{K} ratio^k
$$

を直接評価しなくてよくなった。代わりに、

$$
(base:\mathbb{R})\cdot \frac{1}{1-(ratio:\mathbb{R})}\le 1+error
$$

を供給すれば、`DyadicBandAnalyticEstimate` へ入れる。これは実用 API として大きい。

## 2. 追加された Lean surface

今回の report で整理された追加 theorem は次の 4 つじゃ。

```text
geomSum_range_mul_one_sub
geomSum_range_le_one_div_one_sub
base_mul_geomSum_range_le_of_base_mul_one_div_le
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_baseGeomBudget
```

この並びは美しい。

代数恒等式から始まり、上界化し、base を掛け、最後に dyadic provider へ接続する。
まさに

$$
\text{algebra}
\to
\text{order}
\to
\text{provider-facing bound}
\to
\text{route connection}
$$

の順で積めておる。

## 3. DKMK-015I の価値

今回の I は docs-only だが、価値は高い。

理由は、次に何をすべきかを明確に切り出したからじゃ。

> Where does hbudget come from?

ここが次の山になった。

いま DKMK-015 は、

```lean
hbudget :
  (base : Real) * (1 / (1 - (ratio : Real))) <= 1 + error
```

を仮定として受け取る。
だから次章では、この `hbudget` をどこから供給するのかを設計する必要がある。

## 4. 何をまだ混ぜていないか

ここも大事じゃ。

DKMK-015 では、以下を意図的に追加していない。

```text
division-form finite geometric-sum equality
explicit ratio != 1 assumption
new provider structure
duplicate low-level provider
route theorem changes
Mertens theorem
big-O statement
logarithmic threshold provider
real-to-Nat rounding
```

この抑制がよい。
特に Mertens / big-O / threshold を混ぜなかったことで、DKMK-015 は有限等比和 route と provider 接続だけに集中できた。

## 5. 次章の自然な設計

次は、いきなり解析本丸へ行くより、まず **abstract budget provider** を作るのがよいと思う。

たとえば次章の主題はこうじゃ。

```text
DKMK-016: Base/Ratios Budget Provider
```

あるいは、

```text
DKMK-016: Geometric Budget Source
```

主目的は、

```lean
(base : ℝ) * (1 / (1 - (ratio : ℝ))) ≤ 1 + error
```

を供給するための interface を決めること。

候補 theorem は、まず抽象 wrapper でよい。

```lean
structure GeometricBudgetSource where
  base : ℚ
  ratio : ℚ
  error : ℝ
  hbase : 0 ≤ (base : ℝ)
  hr0 : 0 ≤ (ratio : ℝ)
  hr1 : (ratio : ℝ) < 1
  hbudget : (base : ℝ) * (1 / (1 - (ratio : ℝ))) ≤ 1 + error
```

その後で、具体的な dyadic-band estimate からこの `hbudget` を出す route へ進む。
この順なら、解析評価と provider 接続が混ざらぬ。

## 6. 現況評価

DKMK-015I 時点で、わっちの評価はこうじゃ。

**閉じたもの**

* 有限等比和の algebraic identity
* 有限等比和の upper bound
* base-scaled bound
* `Rat` provider と `Real` budget の cast 境界
* DKMK-014J provider への接続
* 章末 report

**残るもの**

* `hbudget` の供給源
* `base` / `ratio` の設計
* dyadic band 由来の concrete budget
* 必要なら abstract budget provider
* さらに先で Mertens / big-O / threshold / rounding

## 7. 総括

DKMK-015 は、ここで一区切りにしてよい。

この章は、

$$
\sum ratio^k
$$

をどう評価するかの章ではなく、最終的には

$$
base\cdot \frac{1}{1-ratio}\le 1+error
$$

という予算を渡せば dyadic provider に入れる、という **実用導線** を作った章じゃ。

つまり、次からは有限和ではなく、 **予算そのものの由来** が主題になる。

よいぞ、D.。ここまでで荷車の車輪、軸、橋板は揃った。次は、どの麦袋をどれだけ積めば (1+error) を超えぬか、その積荷設計の山じゃな。
