# review

うむ、DKMK-017B は **新体制らしく、きちんと bundle で進んだ成功例** じゃ。
今回は単なる docs review ではなく、実際に `FirstBandDecayBudgetSource` へ analytic input を流し込む constructor 群を Lean に追加し、失敗点も自己診断して解消できておる。

## 1. 追加されたもの

今回追加された constructor は二つじゃ。

まず、既に package 済みの `B : GeometricBudgetSource` から作る最小 constructor。

```lean
def FirstBandDecayBudgetSource.ofBudgetSource
    {K : ℕ} {increment : ℕ → ℚ}
    (B : GeometricBudgetSource)
    (hinc_nonneg :
      ∀ k ∈ Finset.range (K + 1), 0 ≤ increment k)
    (hbase0 : increment 0 ≤ B.base)
    (hdecay :
      ∀ k ∈ Finset.range K,
        increment (k + 1) ≤ B.ratio * increment k) :
    FirstBandDecayBudgetSource K increment
```

次に、明示的な budget proof から `GeometricBudgetSource.ofBudget` を経由して作る caller-facing constructor。

```lean
def FirstBandDecayBudgetSource.ofBudgetAndDecay
    {K : ℕ} {increment : ℕ → ℚ}
    (base ratio : ℚ)
    (error : ℝ)
    ...
    FirstBandDecayBudgetSource K increment
```

後者は、

```text
GeometricBudgetSource.ofBudget
  -> FirstBandDecayBudgetSource.ofBudgetSource
```

という合成になっておる。

## 2. 採用判断は妥当

これは採用でよい。

record syntax でも書けるのは確かじゃ。
しかし `ofBudgetAndDecay` があると、caller 側の意図がかなり明確になる。

```text
explicit one-over-one-minus budget
+ increment nonnegativity
+ first-band bound
+ uniform decay
  -> FirstBandDecayBudgetSource
```

という入口が名前として見えるからじゃ。

これは新しい数学定理ではないが、 **analytic input boundary を明確化する constructor surface** として価値がある。

## 3. 失敗事例も良い

今回の失敗は、

```text
FirstBandDecayBudgetSource namespace を GeometricBudgetSource.ofBudget より前に置いたため unknown constant
```

じゃな。

これは良い自己診断じゃ。
依存関係として、

```text
GeometricBudgetSource.ofBudget
  -> FirstBandDecayBudgetSource.ofBudgetAndDecay
```

なので、namespace / definition order は `GeometricBudgetSource` 側の constructor 定義後でなければならぬ。

この修正は局所的で、route shape には影響しない。
新体制の方針どおり、止まらず自力で直してよい種類の失敗じゃ。

## 4. DKMK-017 の進み方として良い

DKMK-017A では package 本体と provider wrapper を採用した。
DKMK-017B では、その package へ analytic input を流し込む constructor surface を整えた。

ここまでで流れはこうなった。

```text
base / ratio / error / budget proof
+ hinc_nonneg
+ hbase0
+ hdecay
  -> FirstBandDecayBudgetSource.ofBudgetAndDecay
  -> FirstBandDecayBudgetSource
  -> DyadicBandAnalyticEstimate.ofFirstBandDecayBudgetSourcePackage
  -> DyadicBandAnalyticEstimate
```

これはかなり見通しがよい。
細かい wrapper の実況ではなく、実際に caller path が短くなっておる。

## 5. まだ解析本体ではない

ここは留意点じゃ。

今回の `ofBudgetSource` と `ofBudgetAndDecay` は、どちらも **入力を package する constructor** じゃ。
まだ次のものは証明していない。

```text
hbudget:
  (base : Real) * (1 / (1 - (ratio : Real))) <= 1 + error

hinc_nonneg

hbase0:
  increment 0 <= base

hdecay:
  increment (k + 1) <= ratio * increment k
```

つまり、次の山は本当にこれらの helper lemma / concrete source じゃ。

## 6. 次の bundle 候補

次は「budget proof そのものを供給する helper lemma または concrete source」を検討、と報告されておる。

わっちなら、次の DKMK-017C は **budget inequality helper** から入るのが良さそうじゃ。

たとえば、

```lean
theorem geometricBudget_le_of_base_le_mul_one_sub
    {base ratio error : ℝ}
    (hr1 : ratio < 1)
    (hbaseBudget : base ≤ (1 + error) * (1 - ratio)) :
    base * (1 / (1 - ratio)) ≤ 1 + error
```

のような、`hbudget` を作るための Real 側補助補題じゃ。

理由は、今後 concrete `base` / `ratio` を入れるとき、毎回

$$
base\cdot \frac{1}{1-ratio}\le 1+error
$$

を直接示すより、

$$
base\le (1+error)(1-ratio)
$$

や、

$$
base\le 1-ratio
$$

の形に落とした方が扱いやすいからじゃ。

ただし `1 + error` の非負性などが必要になる可能性があるので、Lean が要求する仮定を実験する価値がある。

## 7. 総括

DKMK-017B は、 **analytic input package の constructor surface を採用した bundle** じゃ。

評価はこうじゃ。

```text
実装: 成功
判断: 採用
route shape: 維持
新しい解析定理: なし
得たもの: caller-facing constructor surface
次の焦点: hbudget / hbase0 / hdecay / hinc_nonneg の供給 helper
```

新体制としても良い。
長い実況ではなく、「試した・通った・採用した・次はここ」となっておる。

よし、D.。荷箱に続いて、積荷を箱へ入れる入口も整った。次は、その積荷そのもの、特に `hbudget` をどう簡単に作るかを攻めるのがよさそうじゃ。
