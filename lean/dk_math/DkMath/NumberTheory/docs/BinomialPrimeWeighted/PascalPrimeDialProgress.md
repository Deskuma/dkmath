# PascalPrimeDial 進捗整理

## 位置づけ

当初の `BinomialPrime / WeightedBinomial` ロードマップは、二項係数と重み付き二項項から
可除性を取り出し、後で CFBRC / GN / Zsigmondy へ渡すための土台だった。

最近の実装では、その土台から少し横へ広がり、Pascal 三角形を
「素数ダイヤルの観測面」として読む層が追加された。

これはロードマップの破綻ではなく、次の見方を明示化した補助層である。

```text
係数 C(n,k)
  → 素数 p ごとの高さ padicValNat p C(n,k)
  → Pascal 行に現れる prime support の観測
```

## 実装済みファイル

### `DkMath.NumberTheory.BinomialPrime`

素数行の基本可除性を固定する。

主な API:

```lean
def AllInnerChooseDivisible (d m : ℕ) : Prop
def InnerRowSupportPrime (d p : ℕ) : Prop
def RowBirthPrime (d p : ℕ) : Prop

theorem prime_allInnerChooseDivisible_self
theorem prime_dvd_inner_choose
theorem prime_innerRowSupportPrime_self
theorem prime_rowBirthPrime_self
```

意味:

```text
p が素数なら、row p の内側係数はすべて p を運ぶ。
```

逆向きの `AllInnerChooseDivisible d d → d.Prime` はまだ重い対象として分離している。

### `DkMath.NumberTheory.BinomialPrimePower`

素数冪行と p-adic 高さを扱う。

主な API:

```lean
def UniformBeamHeight (d p h : ℕ) : Prop
def FilteredBeamHeight (d p h : ℕ) (P : ℕ → Prop) : Prop
def BeamBirthBoundary (p : ℕ) : Prop
def BeamBirthBoundaryObstruction (p : ℕ) : Prop
def PrimePrebirthAlternation (p : ℕ) : Prop
```

主な定理:

```lean
theorem prime_power_allInnerChooseDivisible
theorem prime_power_rowBirthPrime
theorem padicValNat_choose_prime_pow
theorem padicValNat_choose_prime_pow_add_index
theorem prime_uniformBeamHeight_self
theorem prime_beamBirthBoundary
theorem prime_prebirthAlternation
theorem prime_power_unitFilteredBeamHeight
```

意味:

```text
row p:
  内側係数の p-height は一様に 1

row p - 1:
  mod p で 1, -1, 1, -1, ... の交代相が見える

row p^n:
  index 側の p-height と係数側の p-height が足し合わさって n になる
```

ここで `PrimePrebirthAlternation` は、p 行の直前に出る Frobenius 境界の一段前の
観測として導入された。

### `DkMath.NumberTheory.WeightedBinomial`

係数由来、`x` 由来、`u` 由来の可除性を分離する。

主な API:

```lean
def weightedBinomialTerm (d k x u : ℕ) : ℕ
def weightedBinomialRowSum (d x u : ℕ) : ℕ
def weightedBinomialPositiveTailSum (d x u : ℕ) : ℕ

theorem dvd_weightedBinomialTerm_of_dvd_choose
theorem dvd_weightedBinomialTerm_of_dvd_x
theorem dvd_weightedBinomialTerm_of_dvd_u
theorem weightedBinomialRowSum_eq_add_pow
theorem weightedBinomialPositiveTailSum_eq_x_mul_GTail_one
```

意味:

```text
choose d k * x^k * u^(d-k)
```

の各因子がどこから来るかを、後で GN / CFBRC に渡しやすい形で分けている。

### `DkMath.NumberTheory.PascalPrimeDial`

今回追加された観測層。

主な API:

```lean
def pascalCoeffMass (n k : ℕ) : ℕ
def pascalRowMass (n : ℕ) : ℕ
def pascalPrimeDialHeight (p n k : ℕ) : ℕ
def UniformPrimeDialHeight (d p h : ℕ) : Prop
def FilteredPrimeDialHeight (d p h : ℕ) (P : ℕ → Prop) : Prop
```

意味:

```text
pascalCoeffMass n k       = C(n,k)
pascalRowMass n           = 2^n
pascalPrimeDialHeight p n k = v_p(C(n,k))
```

既存 Beam API との橋:

```lean
theorem uniformPrimeDialHeight_iff_uniformBeamHeight
theorem filteredPrimeDialHeight_iff_filteredBeamHeight
```

Kummer との橋:

```lean
theorem pascalPrimeDialHeight_prime_pow_add_index
theorem pascalPrimeDialHeight_prime_pow
theorem prime_power_unitFilteredPrimeDialHeight
```

未到達 prime の補題:

```lean
theorem pascalPrimeDialHeight_eq_zero_of_row_lt
theorem prime_not_dvd_pascalCoeffMass_of_row_lt
```

特に次が重要である。

```lean
theorem prime_not_dvd_pascalCoeffMass_of_row_lt
    {p n k : ℕ} (hp : p.Prime) (hnp : n < p) (hkn : k ≤ n) :
    ¬ p ∣ pascalCoeffMass n k
```

これは、

```text
row n より大きい素数 p は、row n の実在係数 C(n,k) には現れない
```

という観測を固定する。

`k ≤ n` が必要なのは、`k > n` では `Nat.choose n k = 0` になり、
自然数の整除では任意の `p` が `0` を割ってしまうためである。

## ロードマップとの差分

予定では、

```text
BinomialPrime
  → WeightedBinomial
  → GN / CFBRC
```

へ進む流れだった。

実際には途中で、

```text
BinomialPrimePower
  → BeamBirthBoundary
  → PrimePrebirthAlternation
  → PascalPrimeDial
```

という観測層が増えた。

この追加は、Zsigmondy や CFBRC へ急ぐ前に、Pascal 行そのものの prime support を
読みやすくするためのものと見る。

## 現在の見取り図

```text
Pascal coefficient
  C(n,k)
    |
    +-- divisibility support
    |     AllInnerChooseDivisible
    |     InnerRowSupportPrime
    |
    +-- p-adic height
    |     UniformBeamHeight
    |     FilteredBeamHeight
    |
    +-- dial observation
    |     pascalPrimeDialHeight p n k
    |     UniformPrimeDialHeight
    |     FilteredPrimeDialHeight
    |
    +-- weighted term
          weightedBinomialTerm d k x u
```

## 次の安全な実装候補

1. `PascalPrimeDial` の軽い補題を増やす。

    ```lean
    theorem pascalPrimeDialHeight_eq_zero_iff_not_dvd
    ```

    ただし `Nat.choose n k ≠ 0` が必要になるため、`k ≤ n` を前提にする。

2. `PrimePrebirthAlternation` を `PascalPrimeDial` から参照する補題を追加する。

    ```text
    row p - 1 の mod p 交代相
      + row p の dial height 1
      = prime birth boundary の前後ペア
    ```

3. `WeightedBinomial` へ dial height を直接持ち込まない。

    まずは coefficient side の観測として `PascalPrimeDial` に閉じ込める。
    `x` や `u` の因子は `WeightedBinomial` 側で別管理する。

4. 逆向き iff はまだ急がない。

    `AllInnerChooseDivisible d d → d.Prime` や composite witness は重要だが、
    証明は重くなりやすい。今は Kummer / factorization / dial observation の橋を
    増やすほうが安全である。

## 検証コマンド

```bash
lake build DkMath.NumberTheory.BinomialPrime
lake build DkMath.NumberTheory.BinomialPrimePower
lake build DkMath.NumberTheory.WeightedBinomial
lake build DkMath.NumberTheory.PascalPrimeDial
lake build DkMath
```
