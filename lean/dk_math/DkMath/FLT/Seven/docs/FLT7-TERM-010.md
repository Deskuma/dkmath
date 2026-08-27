# FLT7-TERM-010

## TERM-009 レビュー

**Outcome C、全面採用です。変更要求はありません。**

PR head は差分記載どおり、

```text
775bc159aa23c8ba944fbe616faab0d4a5e594ad
```

へ更新されています。PR は open / draft / mergeable、Lean CI run 343 も **success** です。

[PR レビューコメント](https://github.com/Deskuma/dkmath/pull/65#issuecomment-5080246155)

実装・報告・文書更新の内容も差分と一致しています。

## 三分岐の評価

### Row Y

```lean
AwaySevenBaseTerminalRowYProfile.to_swapped_ramified
```

は正しい chart 遷移です。

```text
7 ∣ y
x + y ≡ z mod 7
        ↓
x ≡ z mod 7
        ↓
7 ∣ z - x
```

`source.swapXY : CounterexamplePack y x z` の既存 `coordinateCounterexampleRoute` を開き、away constructor の `¬7 ∣ z-x` と衝突させて ramified constructor を回収しています。

これは新しい ramified packet を手作業で再構成せず、既存 route の完全性を利用している点がよいです。

### Row Sum

```lean
AwaySevenBaseTerminalRowSumProfile.false_of_swapped_away
```

は TERM-009 の直接的成果です。

交換後の chart において、

```text
7 ∤ x
7 ∤ z
7 ∤ x + z
7 ∤ z - x
```

を確定し、ramified route を排除したうえで、away route が要求する、

```text
7 ∣ x * z * (x + z)
```

と衝突させています。

したがって Row Sum は「別 chart へ移った」のではなく、**完全に消滅**しました。

### Row Z

```lean
CounterexamplePack.signedOddPermutation
```

により、

```text
(z, -y, x)
```

が primitive な整数 Fermat chart になります。

$$z^7+(-y)^7=x^7$$

さらに、

```lean
AwaySevenBaseTerminalRowZProfile.seven_dvd_signed_gap
```

が、

$$7\mid x-(-y)=x+y$$

を証明しています。

`SignedFermatSevenChart` に不必要な positivity を追加せず、非零・primitive・方程式だけに留めた設計も適切です。

## 最終 decision 型

```lean
AwaySevenBaseTerminalUnitSectorPacket.fermatChartResolution
```

が持つ constructor は、

```text
rowYRamified
rowZSigned
```

だけです。

Row Sum constructor が存在しないこと自体が、三行の整理結果を型に固定しています。

```text
terminal away branch
  ├─ Row Y   → natural ramified
  ├─ Row Z   → signed ramified-gap chart
  └─ Row Sum → False
```

これは TERM-001 以来の三行 receiver を、初めて二系統へ削減した重要な checkpoint です。

## 露出した魔核

### 一般 signed extractor は不要

実装レポートでは、既存 natural extractor が負 endpoint `-y` を受け取れないことが正しく確認されています。

しかし次に必要なのは、任意の整数に対応する巨大な signed extraction framework ではありません。

Row Z に限定すると、対象は正の自然数 $x,y$ による交代型和因子です。

$$A_7(x,y)=\frac{x^7+y^7}{x+y}$$

これは整数 cyclotomic 表現では、

$$A_7(x,y)=\operatorname{cyclotomicSeven}(x,-y)$$

に対応します。

したがって既存 ramified chain との対応は、

```text
既存自然 ramified           Row-Z alternating ramified

z - y                    ↔ x + y
GN 7 (z - y) y           ↔ A₇(x,y)
distinguished x          ↔ z
```

です。

### 狙う exact split

既存 `SevenAdicPowerSplit` は、

```text
z - y    = 7^6 * a^7
GN        = 7 * b^7
x         = 7 * a * b
```

を保持しています。

Row Z の鏡像として必要なのは、

```text
x + y    = 7^6 * a^7
A₇(x,y)  = 7 * b^7
z         = 7 * a * b
```

です。

候補 packet はこの程度で足ります。

```lean
structure AwaySevenBaseTerminalRowZAlternatingPowerSplit
    (hz : AwaySevenBaseTerminalRowZProfile terminal) : Type where
  a : ℕ
  b : ℕ
  a_pos : 0 < a
  b_pos : 0 < b
  coprime_a_b : Nat.Coprime a b

  sum_eq :
    x + y = 7 ^ 6 * a ^ 7

  residual_eq :
    alternatingCyclotomicSeven x y = 7 * b ^ 7

  distinguished_eq :
    z = 7 * a * b
```

## 既存 API との接続

ここが今回の最重要点です。

既存の、

```lean
exists_cyclotomicSeven_terminal_core
```

は最初から引数が整数です。

必要なのは、

```text
7 ∣ c - b
7 ∤ b
```

だけであり、負 endpoint を禁止していません。そこから、

```text
cyclotomicSevenToTraceOne c b
  = sevenAxis * residualCore
```

と、残余核の terminal 性・norm 関係を返します。

Row Z では、

```text
c = x
b = -y
```

としてそのまま適用できます。

つまり signed domain の **sevenAxis peeling はすでに完成済み**です。

さらに、

```lean
exists_eq_seventh_power_of_coprime_mul_eq_pow
```

も `TraceOneInt (-2)` 上の一般定理であり、符号や自然数 positivity には依存しません。

したがって残りは次だけです。

```text
1. alternating natural factor split
2. signed cyclotomic coordinates の coprimality
3. residualCore と conjugate の gcd が unit
4. norm residualCore = b^7
```

すると、

```text
residualCore * conj residualCore = b^7
        ↓
residualCore = gamma^7
        ↓
cyclotomicSevenToTraceOne x (-y)
  = sevenAxis * gamma^7
```

が得られ、現在の、

```lean
AwaySevenBaseTerminalRowZSignedRamifiedArithmeticObligation
```

を inhabit できます。

## 実装上の最小追加

### 1. 交代型 residual

```lean
def alternatingCyclotomicSeven (x y : ℕ) : ℕ :=
  (x ^ 7 + y ^ 7) / (x + y)
```

公開 API としては少なくとも、

```lean
theorem add_mul_alternatingCyclotomicSeven :
    (x + y) * alternatingCyclotomicSeven x y =
      x ^ 7 + y ^ 7

theorem alternatingCyclotomicSeven_intCast :
    (alternatingCyclotomicSeven x y : ℤ) =
      cyclotomicSeven (x : ℤ) (-(y : ℤ))
```

が欲しいところです。

### 2. gcd の中心恒等式

既存 GN 側と同じく、

```text
gcd(x+y, A₇(x,y)) ∣ 7
```

を示します。

$7\mid x+y$ なら $7\mid A_7(x,y)$ でもあるため、

```text
gcd(x+y, A₇(x,y)) = 7
```

へ到達します。

あとは既存 `SevenAdicPowerSplit` と同じ normalized product argument を使えます。

### 3. signed coordinate coprime bridge

現在の自然数版、

```lean
cyclotomicSeven_coordinates_isCoprime
```

を、整数 endpoint へ一般化するか、Row Z 専用に、

```lean
theorem rowZ_signed_cyclotomic_coordinates_isCoprime :
    IsCoprime
      (cyclotomicSevenFst (x : ℤ) (-(y : ℤ)))
      (cyclotomicSevenSnd (x : ℤ) (-(y : ℤ)))
```

を作れば十分です。

`source.hxy` がそのまま入力になります。

## 二つの ramified branch の合流

TERM-010 完了後は、

```text
Row Y:
  cyclotomicSevenToTraceOne z x
    = sevenAxis * rootY^7

Row Z:
  cyclotomicSevenToTraceOne x (-y)
    = sevenAxis * rootZ^7
```

となります。

見た目の endpoint は異なりますが、代数的な終着点は同一です。

```text
primitive endpoint pair
+
seven-divisible gap
+
cyclotomic coordinate = sevenAxis * seventh power
```

したがって RAMIFIED-001 では、自然版と signed 版を別々に閉じるより、共通 façade を置くのがよいです。

```lean
structure PrimitiveRamifiedTraceOneCore (c b : ℤ) : Type where
  endpoint_coprime : IsCoprime c b
  seven_dvd_gap : (7 : ℤ) ∣ c - b
  root : TraceOneInt (-2)
  coordinate_eq :
    cyclotomicSevenToTraceOne c b =
      sevenAxis * root ^ 7
```

```text
Row Y natural ramified ─┐
                        ├→ PrimitiveRamifiedTraceOneCore
Row Z signed ramified ──┘
```

ここから先が、本当の ramified summit closure です。

## 次 checkpoint

```text
FLT7-TERM-010
  Row-Z alternating cyclotomic power split
  +
  signed residual-core seventh-power extraction
```

到達定理：

```lean
theorem AwaySevenBaseTerminalRowZProfile
    .signedRamifiedArithmeticObligation :
    AwaySevenBaseTerminalRowZSignedRamifiedArithmeticObligation hz
```

## 総括

TERM-009 により、

```text
Row Sum   消滅
Row Y     natural ramified へ合流
Row Z     交代型和因子へ圧縮
```

まで進みました。

露出した魔核は「負の数一般」ではありません。

$$\boxed{\frac{x^7+y^7}{x+y}\text{ を }7\times(\text{七乗})\text{へ分離する交代型 ramified core}}$$

ここを閉じれば terminal away branch は、すべて ramified summit へ統合できます。
