# review

うむ、DKMK-016A、受け取ったぞい。
これは **DKMK-015 の自然な次章** として、かなりよい開始じゃ。DKMK-015 が

```text
geometric budget
  -> finite geometric-sum bound
  -> dyadic source-mass provider
```

まで橋を架けたので、DKMK-016 はその入口で未解決として残った

$$
(base:\mathbb{R})\cdot \frac{1}{1-(ratio:\mathbb{R})}\le 1+error
$$

を **どこから供給するか** に焦点を移した章、という位置づけじゃな。実際、roadmap でも残課題を “Where does hbudget come from?” と明示しておる。

## 1. 今回の DKMK-016A の意味

DKMK-016A は Lean code 追加ではなく、 **予算供給源の抽象 surface を決めるフェーズ** じゃ。

候補として固定された構造はこれじゃな。

```lean
structure GeometricBudgetSource where
  base : Rat
  ratio : Rat
  error : Real
  hbase : 0 <= (base : Real)
  hr0 : 0 <= (ratio : Real)
  hr1 : (ratio : Real) < 1
  hbudget : (base : Real) * (1 / (1 - (ratio : Real))) <= 1 + error
```

これは非常に素直でよい。
DKMK-015H の wrapper が要求していた `hbase`, `hr0`, `hr1`, `hbudget` を、そのままひとつの package にまとめる設計じゃ。roadmap でも、最初は `x`, `K`, `increment`, pointwise majorization, `DyadicBandAnalyticEstimate` には触れず、小さな抽象 package に留める方針が明記されておる。

## 2. なぜこの抽象化がよいか

ここでいきなり Mertens や big-O や logarithmic threshold に行かないのが賢い。

なぜなら、現時点で必要なのは解析定理そのものではなく、

$$
base,\ ratio,\ error
$$

を持ち、それらが geometric budget を満たす、という **契約** だからじゃ。

つまり、DKMK-016A はこういう役目を持つ。

```text
具体的な解析評価
  -> GeometricBudgetSource
  -> DKMK-015H provider wrapper
  -> DyadicBandAnalyticEstimate
```

この形にしておけば、将来 `base` と `ratio` の作り方が変わっても、下流の provider route は変えなくてよい。

これは DkMath らしい「橋を先に作り、具体的な水源は後から増やす」設計じゃな。

## 3. 次の wrapper も自然

roadmap では次の theorem 候補も出ておる。

```lean
theorem DyadicBandAnalyticEstimate
    .ofPointwiseGeometricMajorant_of_budgetSource
    (x K : Nat)
    (increment : Nat -> Rat)
    (B : GeometricBudgetSource)
    (hinc_nonneg :
      forall k in Finset.range (K + 1), 0 <= increment k)
    (hgeom :
      forall k in Finset.range (K + 1),
        increment k <= B.base * B.ratio ^ k) :
    DyadicBandAnalyticEstimate x K increment B.error
```

これもよい。
DKMK-015H の

```lean
ofPointwiseGeometricMajorant_of_baseGeomBudget
```

をさらに caller-friendly に包む薄い wrapper になる。

呼び出し側は `base`, `ratio`, `error`, `hbase`, `hr0`, `hr1`, `hbudget` を個別に持ち回らず、`B : GeometricBudgetSource` を渡せばよい。

これは API として見通しが良くなる。

## 4. DKMK-016B の実装見通し

DKMK-016B は軽く閉じられる可能性が高い。

まず structure を `SourceMassTruncation.lean` のどこに置くかが焦点じゃ。わっちなら、`DyadicBandAnalyticEstimate` namespace より前、または geometric-sum 補題群の直後に置くのがよいと思う。

候補はこうじゃ。

```lean
/--
Abstract source of the one-over-one-minus geometric budget.

This package separates the analytic origin of `base` and `ratio`
from the dyadic provider route.
-/
structure GeometricBudgetSource where
  base : ℚ
  ratio : ℚ
  error : ℝ
  hbase : 0 ≤ (base : ℝ)
  hr0 : 0 ≤ (ratio : ℝ)
  hr1 : (ratio : ℝ) < 1
  hbudget : (base : ℝ) * (1 / (1 - (ratio : ℝ))) ≤ 1 + error
```

そして wrapper はこうじゃ。

```lean
theorem DyadicBandAnalyticEstimate
    .ofPointwiseGeometricMajorant_of_budgetSource
    (x K : ℕ)
    (increment : ℕ → ℚ)
    (B : GeometricBudgetSource)
    (hinc_nonneg :
      ∀ k ∈ Finset.range (K + 1), 0 ≤ increment k)
    (hgeom :
      ∀ k ∈ Finset.range (K + 1),
        increment k ≤ B.base * B.ratio ^ k) :
    DyadicBandAnalyticEstimate x K increment B.error :=
  DyadicBandAnalyticEstimate
    .ofPointwiseGeometricMajorant_of_baseGeomBudget
      x K increment B.base B.ratio
      hinc_nonneg hgeom
      B.hbase B.hr0 B.hr1 B.hbudget
```

証明はこの程度の薄さで閉じるはずじゃ。
これはよい Lean surface になる。

## 5. ここで気をつける点

一点、設計上の留意点がある。

`GeometricBudgetSource` は `x` や `K` を持たない。これは今の段階では正しい。
ただし将来、`base` や `ratio` が `K` や dyadic band に依存する場合は、次のような dependent 版が欲しくなる可能性がある。

```lean
def GeometricBudgetSourceFor (K : ℕ) := ...
```

または、

```lean
structure GeometricBudgetSourceFor (x K : ℕ) where ...
```

じゃが、今はまだ早い。
まずは非依存の小さな `GeometricBudgetSource` を置くのがよい。必要になったら `For` 版を後で足せばよい。

この順序なら、抽象 API を壊さずに拡張できる。

## 6. 現在地の評価

DKMK-016A で決まったことは、次の通りじゃ。

**閉じたもの**

```text
DKMK-016 の章題:
  Geometric Budget Source

第一 interface:
  GeometricBudgetSource

次 wrapper 候補:
  DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_budgetSource
```

**まだ入れていないもの**

```text
Lean code
concrete base / ratio
Mertens theorem
big-O
logarithmic threshold
real-to-Nat rounding
new provider structure
DKMK-015H の重複
```

この切り分けは非常に健全じゃ。
DKMK-016 は「解析評価の章」へ突入する前に、まず「解析評価を受け取る器」を作る章として開始されておる。

## 7. 総括

DKMK-016A は、DKMK-015 の終点を正しく受けている。

DKMK-015 の最後の未解決 obligation は、

$$
hbudget:
(base:\mathbb{R})\cdot \frac{1}{1-(ratio:\mathbb{R})}\le 1+error
$$

だった。
DKMK-016A は、それを `GeometricBudgetSource` という抽象 source に切り出した。

これはよい。
次の DKMK-016B では、この structure と thin wrapper を Lean に置けば、上位解析 route を差し込むための「港」ができる。

ここから先は、いよいよ **どんな船がこの港へ予算を運んでくるか** の設計じゃな。
賢狼としては、まずは抽象 source を小さく閉じ、その後に `base` / `ratio` の concrete constructor を別フェーズで増やすのが最も安全と見るぞい。
