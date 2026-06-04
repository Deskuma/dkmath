# review

うむ、DKMK-016D は **concrete constructor へ入る前の候補選定として正しい一手** じゃ。
今回の diff では、`GeometricBudgetSource` の最初の concrete `base` / `ratio` 候補を比較し、次の Lean target として `GeometricBudgetSource.ofZeroRatio` を推奨候補に固定しておる。これは解析結果ではなく、API sanity constructor として位置づけられている。

## 1. 今回の位置づけ

DKMK-016B で `GeometricBudgetSource` が実装され、DKMK-016C で使い方が整理された。
そこで DKMK-016D は、次の問いに移ったわけじゃ。

```text
最初にどんな GeometricBudgetSource constructor を置くべきか
```

ここでいきなり Mertens や big-O に行かず、候補を

* constructor なし
* zero-ratio sanity constructor
* external positive ratio constructor
* analytic budget constructor

に分けたのはよい。

## 2. `ofZeroRatio` を選んだ判断

次 target として選ばれたのはこれじゃな。

```lean
theorem GeometricBudgetSource.ofZeroRatio
    (base : Rat)
    (error : Real)
    (hbase : 0 <= (base : Real))
    (hbudget : (base : Real) <= 1 + error) :
    GeometricBudgetSource
```

ここで `ratio = 0` とする。

すると budget は、

$$
(base:\mathbb{R})\cdot \frac{1}{1-0}\le 1+error
$$

なので、

$$
(base:\mathbb{R})\le 1+error
$$

に潰れる。

これは解析的には何も深くない。
だが、API sanity check としてはかなり良い。

なぜなら、`GeometricBudgetSource` を concrete value から作り、後で `ofPointwiseGeometricMajorant_of_budgetSource` に流す最小パターンを示せるからじゃ。

## 3. なぜ `ofBudget` ではなく `ofZeroRatio` が先か

`ofBudget` は一般的には自然じゃ。

```lean
theorem GeometricBudgetSource.ofBudget
    (base ratio : Rat)
    (error : Real)
    ...
```

しかしこれは、実質的に record syntax の別名に近い。
最初の constructor としては、あまり「具体例」にならぬ。

一方、`ofZeroRatio` は、

* concrete `ratio = 0`
* `hr0`, `hr1` は自動的に閉じる
* `hbudget` は単純な `base <= 1 + error`
* API の流れを実際に確認できる

という利点がある。

つまり `ofZeroRatio` は **constructor theorem であると同時に、小さな動作確認例** なのじゃ。

## 4. 実装見通し

DKMK-016E は軽く閉じられるはずじゃ。

候補コードはほぼこれでよい。

```lean
namespace GeometricBudgetSource

/--
Build a geometric budget source with zero ratio.

This is an API sanity constructor, not an analytic estimate.
-/
theorem ofZeroRatio
    (base : ℚ)
    (error : ℝ)
    (hbase : 0 ≤ (base : ℝ))
    (hbudget : (base : ℝ) ≤ 1 + error) :
    GeometricBudgetSource where
  base := base
  ratio := 0
  error := error
  hbase := hbase
  hr0 := by norm_num
  hr1 := by norm_num
  hbudget := by
    simpa using hbudget

end GeometricBudgetSource
```

もし `simpa` が budget を潰しきらなければ、

```lean
  hbudget := by
    norm_num
    simpa using hbudget
```

や、

```lean
  hbudget := by
    simpa using hbudget
```

の前後を少し調整すればよい。
`ratio = 0` なので、たぶん素直に閉じる。

## 5. 注意点

`ratio = 0` の source は、pointwise majorant と組み合わせるとかなり強い制約になる。

なぜなら、

$$
base\cdot 0^k
$$

は (k=0) では (base)、(k>0) では (0) じゃ。
Lean の自然数冪でも通常 (0^0=1) なので、

$$
base\cdot 0^0=base
$$

となる。

したがって、この source を provider に使うと、`increment k` は (k>0) で 0 以下に抑えられる必要がある。`hinc_nonneg` と合わせると、多くの場合 (k>0) の increment は 0 になる。

つまり `ofZeroRatio` は、一般用途の analytic source ではなく、本当に **sanity constructor / degenerate example** と見るべきじゃ。
docs にその含意も少し書いておくと親切じゃな。

## 6. 次の展開

DKMK-016E で `ofZeroRatio` が閉じたら、その次は二択じゃ。

ひとつは、zero-ratio source を実際に provider wrapper へ流す example theorem を作る道。

もうひとつは、positive ratio の候補へ進む道。

わっちなら、E で `ofZeroRatio` を実装した後、F で **zero-ratio usage example** を docs-only か Lean theorem として軽く置くのがよいと思う。
その後で positive ratio / analytic budget へ進めば、API の最小動作確認が済んだ状態になる。

## 7. 総括

DKMK-016D は、 **最初の concrete constructor を選んだ設計回** じゃ。

選ばれた `ofZeroRatio` は解析本丸ではない。
しかし、`GeometricBudgetSource` が実際に concrete data から作れることを確認する、最初の小さな足場としてよい。

この選択は、DkMath の進め方として堅い。
いきなり大きな解析の船を港に入れる前に、小舟で水深を測るようなものじゃな。
わっちはこういう慎重な航路取り、嫌いではないぞい。
