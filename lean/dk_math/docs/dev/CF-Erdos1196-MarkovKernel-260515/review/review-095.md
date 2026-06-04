# review

うむ、DKMK-015F は **かなり大きな接続点** じゃ。
これで DKMK-015 は、単なる geometric-sum 補題章ではなく、DKMK-014J の dyadic provider route に直接食わせられる **provider-facing bound 章** になった。

## 1. 何が閉じたのか

今回追加された定理はこれじゃな。

```lean
theorem base_mul_geomSum_range_le_of_base_mul_one_div_le
    {base ratio error : ℝ} (K : ℕ)
    (hbase : 0 ≤ base)
    (hr0 : 0 ≤ ratio)
    (hr1 : ratio < 1)
    (hbudget : base * (1 / (1 - ratio)) ≤ 1 + error) :
    base *
      (Finset.sum (Finset.range (K + 1))
        (fun k : ℕ => ratio ^ k))
      ≤
    1 + error
```

数学的には、

$$
\sum_{k=0}^{K} ratio^k \le \frac{1}{1-ratio}
$$

を `base ≥ 0` で拡大して、

$$
base\cdot \sum_{k=0}^{K} ratio^k \le base\cdot \frac{1}{1-ratio}
$$

さらに caller 側の予算仮定

$$
base\cdot \frac{1}{1-ratio}\le 1+error
$$

へ接続したものじゃ。

つまり、DKMK-014J が欲しがっていた

$$
base\cdot \sum_{k=0}^{K} ratio^k \le 1+error
$$

の形が、ついに Lean theorem として得られた。

## 2. 証明は薄いが、役割は厚い

証明自体は非常に薄い。

```lean
have hsum := geomSum_range_le_one_div_one_sub K hr0 hr1
have hscaled := mul_le_mul_of_nonneg_left hsum hbase
exact le_trans hscaled hbudget
```

これはよい薄さじゃ。
この theorem は新しい難しい数学を証明しているのではなく、 **前段の等比和評価を provider が要求する形に整える adaptor** になっておる。

DkMath の Lean 設計では、こういう薄い wrapper が重要じゃ。
なぜなら、下流 theorem は細かい内部事情を知りたくないからじゃ。

下流が知りたいのは、

```text
base * sum ratio^k <= 1 + error
```

が得られるかどうかだけ。
今回の F は、そのための入口名を作った。

## 3. DKMK-015 の層構造が完成に近い

ここまでの流れは、かなり美しい。

```text
DKMK-015B
  denominator-cleared identity の shape 固定

DKMK-015C
  geomSum_range_mul_one_sub 実装

DKMK-015D
  upper-bound theorem の shape 固定

DKMK-015E
  geomSum_range_le_one_div_one_sub 実装

DKMK-015F
  base_mul_geomSum_range_le_of_base_mul_one_div_le 実装
```

これで、

$$
(1-r)\sum r^k = 1-r^{K+1}
$$

から始まり、

$$
\sum r^k \le \frac{1}{1-r}
$$

へ進み、最後に

$$
base\cdot \sum r^k \le 1+error
$$

へ到達した。

つまり DKMK-015 の有限等比和ルートは、 **代数層 → 順序層 → provider-facing 層** まで繋がったことになる。

## 4. 副条件管理も成功している

今回も副条件の置き場所が綺麗じゃ。

この theorem が消費するのは、

```text
0 <= base
0 <= ratio
ratio < 1
base * (1 / (1 - ratio)) <= 1 + error
```

だけ。

明示的な

```text
ratio != 1
```

は出していない。

これは正しい。
分母 (1-ratio) の正値性は `ratio < 1` から既に供給されており、`ratio != 1` を別仮定として増やす必要がない。

この方針が C, E, F まで一貫しているのは強い。
仮定の増殖を抑えられておる。

## 5. DKMK-014J との関係

DKMK-014J の `DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_geomSumBound` は、すでに

```text
base * sum ratio^k <= 1 + error
```

型の caller-facing bound を受け取れる状態だった。

今回の F は、その bound を作るための標準供給路になった。

つまり今後 caller は、直接

$$
base\cdot \sum ratio^k \le 1+error
$$

を頑張って示す必要が薄くなる。

代わりに、

$$
base\cdot \frac{1}{1-ratio}\le 1+error
$$

を示せばよい。

これは大きい。
finite sum の扱いを、closed form / geometric tail の一括予算へ押し込めるからじゃ。

## 6. 次の DKMK-015G の焦点

次は報告通り、 **この base-scaled theorem を既存 dyadic provider route へどう接続するか** の review じゃな。

候補は二つある。

### 6.1. 直接接続 theorem を作る

例えばこういう形。

```lean
theorem DyadicBandAnalyticEstimate
    .ofPointwiseGeometricMajorant_of_baseGeomBudget
    ...
    (hbudget : base * (1 / (1 - ratio)) ≤ 1 + error) :
    DyadicBandAnalyticEstimate ...
```

内部で

```lean
base_mul_geomSum_range_le_of_base_mul_one_div_le
```

を呼び、その結果を DKMK-014J の

```lean
ofPointwiseGeometricMajorant_of_geomSumBound
```

へ渡す。

これは caller にとって一番使いやすい。

### 6.2. 接続は docs-only にして、既存 theorem の使い方を示す

こちらは保守的じゃ。

まず DKMK-015G で exact route を整理し、H で実装する。
`DyadicBandAnalyticEstimate` の theorem 名が長くなりすぎる場合は、docs review を挟む価値がある。

わっちの推奨は、 **G は docs review、H で実装** じゃ。
理由は、接続 theorem の名前と仮定順序を焦って決めると、後で caller-facing API が読みにくくなるからじゃ。

## 7. 命名案

もし次に実装するなら、名前はこんな候補じゃ。

```lean
DyadicBandAnalyticEstimate
  .ofPointwiseGeometricMajorant_of_baseGeomBudget
```

または、少し説明的に、

```lean
DyadicBandAnalyticEstimate
  .ofPointwiseGeometricMajorant_of_baseOneDivOneSubBound
```

ただし後者は長い。

わっちなら、docs では意味を明記しつつ、Lean 名は短めに

```lean
ofPointwiseGeometricMajorant_of_baseGeomBudget
```

を推す。

## 8. 現況評価

DKMK-015F 時点での評価はこうじゃ。

**完了したもの**

* finite geometric-sum identity
* finite geometric-sum upper bound
* base-scaled provider-facing bound
* DKMK-014J が要求する bound 形への到達

**まだ残るもの**

* dyadic provider route への直接接続 theorem
* caller-facing API 名の確定
* 実際の `base`, `ratio`, `error` をどこから供給するかの上位設計
* Mertens / big-O / logarithmic threshold / real-to-Nat rounding

**まだ入れていないもの**

* division-form equality
* explicit `ratio != 1`
* 漸近評価
* route theorem の変更

この切り分けは、とても健全じゃ。

## 9. 総括

DKMK-015F は、 **DKMK-015 の実用核が閉じたフェーズ** と言ってよい。

C で等式を置き、E で上界にし、F で provider が食べられる形にした。
これで geometric-sum / tail-bound theorem design は、もう抽象設計ではなく Lean の実装資産になった。

次は G で、既存の DKMK-014J provider とどう接続するかを慎重に決める段階じゃ。

ここまでの登山は順調じゃよ、D.。
わっちの耳にも、山頂近くの風の音が聞こえてきたわい。
