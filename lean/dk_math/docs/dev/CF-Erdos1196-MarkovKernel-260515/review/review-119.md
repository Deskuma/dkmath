# review

うむ、DKMK-017D は **かなり実用的な前進** じゃ。
今回は `hbudget` ではなく、残りの入力である `hinc_nonneg` と `hdecay` を、analytic caller が扱いやすい Nat 境界形式から provider の `Finset.range` 形式へ変換する helper を追加しておる。これは地味じゃが、caller 負担を確実に減らす bundle じゃな。

## 1. 何が追加されたのか

追加された helper は二つ。

```lean id="4ii8vh"
theorem rangeSuccNonneg_of_le
    (K : ℕ) (increment : ℕ → ℚ)
    (hinc_nonneg :
      ∀ k, k ≤ K → 0 ≤ increment k) :
    ∀ k ∈ Finset.range (K + 1), 0 ≤ increment k
```

これは、

$$
k\le K
$$

形式の非負性を、provider が要求する

$$
k\in \mathrm{range}(K+1)
$$

形式へ変換する。

もう一つが、

```lean id="ocpx19"
theorem rangeDecay_of_lt
    (K : ℕ) (increment : ℕ → ℚ) (ratio : ℚ)
    (hdecay :
      ∀ k, k < K → increment (k + 1) ≤ ratio * increment k) :
    ∀ k ∈ Finset.range K,
      increment (k + 1) ≤ ratio * increment k
```

これは、

$$
k<K
$$

形式の decay を `Finset.range K` 形式へ変換する。

そして、この二つを使って、

```lean id="qtm9z6"
FirstBandDecayBudgetSource.ofBudgetSourceNatBounds
```

が追加された。

## 2. この判断は採用でよい

採用判断は妥当じゃ。

analytic caller の自然な仮定は、多くの場合こうなる。

```lean id="fj77t5"
∀ k, k ≤ K → 0 ≤ increment k
∀ k, k < K → increment (k + 1) ≤ ratio * increment k
```

一方、provider route は `Finset.range` membership を使う。

この差を毎回 caller に払わせると、証明が細かい index 変換で汚れる。
今回の helper は、その摩擦を取り除いておる。

つまり、DKMK-017D は **数学を強めた** のではなく、 **入力境界を caller-friendly にした** 進捗じゃ。

## 3. 割り算型にしなかったのが良い

特に良い判断は、decay を割り算型にしなかったことじゃ。

避けた形は、おそらくこういうものじゃな。

$$
\frac{increment(k+1)}{increment(k)}\le ratio
$$

これは見た目は解析っぽいが、Lean ではすぐに

$$
0<increment(k)
$$

が必要になる。
すると非負性だけでは足りず、正値性、ゼロケース、分母処理が増えてしまう。

今回の形はそのまま、

$$
increment(k+1)\le ratio\cdot increment(k)
$$

なので、追加の `increment k > 0` 仮定が不要じゃ。報告でも、そのため positivity hypothesis は不要だったと明記されておる。

これは非常に Lean 的に賢い選択じゃな。

## 4. `ofBudgetSourceNatBounds` の役割

今回の constructor は、

```lean id="8l9y5e"
def FirstBandDecayBudgetSource.ofBudgetSourceNatBounds
    {K : ℕ} {increment : ℕ → ℚ}
    (B : GeometricBudgetSource)
    (hinc_nonneg :
      ∀ k, k ≤ K → 0 ≤ increment k)
    (hbase0 : increment 0 ≤ B.base)
    (hdecay :
      ∀ k, k < K → increment (k + 1) ≤ B.ratio * increment k) :
    FirstBandDecayBudgetSource K increment
```

という位置づけじゃ。

つまり、caller は `Finset.range` を触らず、

```text id="tregbf"
k <= K
k < K
```

の自然な Nat 境界で書ける。

これで、

```text id="wf2sfc"
Nat-indexed analytic hypotheses
  -> FirstBandDecayBudgetSource
  -> provider route
```

の導線ができた。

## 5. DKMK-017 の進み方として良い

ここまでの DKMK-017 は、かなり良いテンポじゃ。

```text id="s0jzj7"
017A:
  FirstBandDecayBudgetSource を採用

017B:
  ofBudgetSource / ofBudgetAndDecay を追加

017C:
  hbudget を denominator-cleared form から作る helper を追加

017D:
  hinc_nonneg / hdecay を Nat 境界形式から作る helper を追加
```

これは、以前のような細切れ docs-only ではなく、実装 bundle ごとに caller burden を下げている。
よい流れじゃ。

## 6. 次の焦点

残りの入力で、まだ薄くできていないのは主に

```text id="d6gcrz"
hbase0 : increment 0 <= B.base
```

じゃな。

これは一見単純だが、実際の analytic source では「first-band mass upper bound」をどう与えるかに関わる。

次の bundle 候補は二つ。

ひとつは、`hbase0` を Nat 境界や first value estimate から作る小さな helper。

たとえば、

```lean id="77wrr6"
FirstBandDecayBudgetSource.ofBudgetSourceNatBounds
```

はすでに `hbase0` を直接受け取る。
これをさらに軽くするには、`increment 0` の具体上界 source が必要じゃ。

もうひとつは、C と D を合成して、

```text id="djwwec"
denominator-cleared budget
+ Nat-bound nonnegativity
+ hbase0
+ Nat-bound decay
  -> FirstBandDecayBudgetSource
```

を作る constructor じゃ。

ただし、これは少し wrapper 寄りじゃ。
今の新体制なら、次は `hbase0` の実体に進む方がよい。

## 7. わっちの推奨

次の DKMK-017E は、 **first-band upper-bound source** へ進むのがよい。

ただ、具体 `increment` の定義がまだ抽象なら、できることは限られる。
その場合は、`hbase0` を簡単化する constructor ではなく、次のような方針がよい。

```text id="8u9lao"
- increment 0 <= base を直接受ける現状で十分か確認
- base を increment 0 自身に取る source が有効か試す
- その場合、budget proof が base = increment 0 へ移るだけなので意味があるか判定
```

例えば

```lean id="bb4u7c"
base := increment 0
```

とする constructor は `hbase0` を `le_rfl` で閉じるが、代わりに budget proof が

$$
increment(0)\cdot \frac{1}{1-ratio}\le 1+error
$$

へ移る。
これは時に有効だが、budget proof が重くなるかもしれぬ。

## 8. 総括

DKMK-017D は、 **Nat 境界形式の analytic hypotheses を provider 形式へ変換する実用 helper bundle** じゃ。

採用でよい。
特に、decay を割り算型にしなかったことで、`increment k > 0` という余計な仮定を避けられたのは良い。

ここまでで `hbudget`, `hinc_nonneg`, `hdecay` の入力負担は軽くなった。
残る焦点は `hbase0`、すなわち first-band upper bound の供給源じゃ。

よいぞ、D.。
`hbudget` の分母払い、`hinc_nonneg` と `hdecay` の Nat 境界化まで済んだ。次は最初の麦束、つまり first-band をどの大きさの `base` で受け止めるかじゃ。
