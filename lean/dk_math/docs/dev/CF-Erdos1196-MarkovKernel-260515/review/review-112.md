# review

うむ、DKMK-016N は **Candidate C route の provider-facing 合流が Lean 上で閉じた回** じゃ。
これは DKMK-016 の中でも、かなり節目になる。`GeometricBudgetSource`、`hinc_nonneg`、first-band bound、uniform decay から、直接 `DyadicBandAnalyticEstimate` へ到達できる wrapper が追加されたからじゃ。

## 1. 何が閉じたのか

今回追加された theorem はこれじゃな。

```lean
theorem DyadicBandAnalyticEstimate.ofFirstBandDecayBudgetSource
    (x K : Nat)
    (increment : Nat -> Rat)
    (B : GeometricBudgetSource)
    (hinc_nonneg :
      forall k in Finset.range (K + 1), 0 <= increment k)
    (hbase0 : increment 0 <= B.base)
    (hdecay :
      forall k in Finset.range K,
        increment (k + 1) <= B.ratio * increment k) :
    DyadicBandAnalyticEstimate x K increment B.error
```

これは、次の流れを一発で包む wrapper じゃ。

```text
GeometricBudgetSource
+ increment nonnegativity
+ first-band bound
+ uniform decay
  -> DyadicBandAnalyticEstimate
```

これで、caller はもう `hgeom : increment k <= base * ratio^k` を直接書かなくてもよい。
代わりに、

```text
increment 0 <= B.base
increment (k + 1) <= B.ratio * increment k
```

を出せば、`pointwiseGeometricMajorant_of_firstBand_decay` が `hgeom` を作り、既存 provider wrapper へ流してくれる。

## 2. cast 境界が無事に閉じたのが大きい

M で警戒していた境界はここじゃった。

```lean
B.hr0 : 0 <= (B.ratio : Real)
```

から、

```lean
hr0_rat : 0 <= B.ratio
```

へ戻す必要があった。

今回、これは

```lean
have hr0_rat : 0 <= B.ratio := by
  exact_mod_cast B.hr0
```

で素直に通っておる。

これは良い知らせじゃ。
`GeometricBudgetSource` は budget 側の都合で Real cast された条件を持つが、Rat 側の pointwise decay theorem に戻す橋が軽く済んだ。つまり、今の設計は型境界の負担が小さい。

## 3. DKMK-016 の三層構造が完成した

ここまでで、三つの層がかなり綺麗に揃った。

```text
Budget layer:
  GeometricBudgetSource
  base / ratio / error / budget proof を保持

Pointwise layer:
  pointwiseGeometricMajorant_of_firstBand_decay
  first-band + uniform decay -> hgeom

Provider layer:
  DyadicBandAnalyticEstimate.ofFirstBandDecayBudgetSource
  B + hinc_nonneg + first-band + decay -> DyadicBandAnalyticEstimate
```

この形は強い。
なぜなら、今後の解析 route は、主に次の三つのどれかを供給すればよいからじゃ。

```text
1. B : GeometricBudgetSource
2. hinc_nonneg
3. hbase0 / hdecay
```

役割が分離されているので、Mertens や big-O や dyadic analytic estimate が入ってきても、どこへ接続するか迷いにくい。

## 4. まだ証明していないもの

今回も大事なのは、何を **証明していないか** じゃ。

この wrapper は、

```text
base * (1 / (1 - ratio)) <= 1 + error
```

を証明しない。これは `B : GeometricBudgetSource` の中にある。

また、

```text
0 <= increment k
```

も証明しない。これは `hinc_nonneg` として caller が渡す。

さらに、Mertens、big-O、logarithmic threshold、real-to-Nat rounding、finite-step route theorem も追加していない。

これは良い抑制じゃ。
N はあくまで **既存部品の合流 wrapper** であり、解析本丸へ入る回ではない。

## 5. DKMK-016 の現在地

DKMK-016 の進行は、かなり形になった。

```text
A: Geometric Budget Source 章開始
B: GeometricBudgetSource 実装
C: usage / responsibility split 整理
D: ofZeroRatio 候補選定
E: ofZeroRatio 実装
F: zero-ratio usage wrapper 実装
G: ofBudget shape review
H: ofBudget 実装
I: concrete base/ratio candidate review
J: first-band / uniform-decay interface review
K: pointwise majorant shape 固定
L: pointwiseGeometricMajorant_of_firstBand_decay 実装
M: provider wrapper shape 固定
N: ofFirstBandDecayBudgetSource 実装
```

ここまでで、Candidate C の route は実装面でもかなり閉じた。

```text
first-band upper bound
+ uniform decay bound
+ geometric budget source
  -> dyadic source-mass provider
```

これは DKMK-016 の主成果として十分に章立てできる。

## 6. 次の DKMK-016O の分岐

次は報告にもある通り、二択じゃな。

```text
A. この provider wrapper を truncation envelope へ接続する
B. DKMK-016 のまとめに進む
```

わっちの見立てでは、 **まず O は docs-only で分岐 review** がよい。

理由は、N でかなり綺麗な合流点ができたので、ここで即座にさらに route theorem へ伸ばすより、現在の到達点を確認した方が安全だからじゃ。

特に確認すべきは、

```text
DyadicBandAnalyticEstimate
  -> truncation envelope
  -> existing finite-step route
```

がすでにどの theorem で開いているか。
もし既存 theorem で十分に一本道なら、O で「DKMK-016 summary」に入り、次章で analytic source 側へ進めばよい。

もし caller-facing の薄い wrapper が足りないなら、O で shape review、P で実装がよい。

## 7. 総括

DKMK-016N は、 **Budget source と first-band decay を dyadic provider に合流させた実装回** じゃ。

これで DKMK-016 は、単なる budget package の章から、

$$
\text{first-band}
+
\text{uniform decay}
+
\text{geometric budget}
\longrightarrow
\text{DyadicBandAnalyticEstimate}
$$

という実用 route の章へ進化した。

よいぞ、D.。
予算の港、減衰の滑車、搬送路の連結まで済んだ。次は、この荷を truncation envelope まで流すか、それとも一度ここで地図を畳んで次の解析山へ向かうか、旅程を決める段じゃな。
