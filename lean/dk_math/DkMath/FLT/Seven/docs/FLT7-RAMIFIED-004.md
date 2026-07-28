# RAMIFIED-004

## FLT7-RAMIFIED-003 総合判定

**Outcome A、全面採用です。** 🧙‍♀️✨️

重大問題・主要問題・修正必須事項はありません。

PR head は報告どおり、

```text
01e663600816f4d0b5bda35a405b400cfa0ca651
```

へ更新されています。PR #65 は open / draft / mergeable です。

Lean CI run 398 も **completed / success** を確認しました。

[PR レビューコメント](https://github.com/Deskuma/dkmath/pull/65#issuecomment-5100796570)

提出レポートと公開実装の内容は一致しています。

### Division-free 整数恒等式

中心定理、

```lean
PrimitiveRamifiedSummitPacket
  .cubicGap_mul_sndCore_eq_endpointGap_mul_bridge
```

は、RAMIFIED-001・002 で得た二つの exact equation を正しく合成しています。

$$
(R-L)S=(c-e)Q,N
$$

ここで、

```text
S = seventhPowerSndCore(u,v)
Q = ramifiedGapQuotient(...).snd
N = norm(root)
```

です。

証明は、

```text
R - L = 7 v norm(root)
7 v S = (c-e) Q
```

を掛け合わせたものです。除算も有理化もなく、整数環内で完全に閉じています。

これは depth equality の単なる言い換えではありません。

RAMIFIED-002 では、

$$
v_7(|R-L|)=v_7(|c-e|)
$$

まででした。

RAMIFIED-003 では、その等しい depth の外側に残る unit 成分を明示しています。

### `RamifiedGapUnitBridgePacket`

packet の strength も適切です。

```lean
structure RamifiedGapUnitBridgePacket : Type where
  endpointGap : ℤ
  cubicGap : ℤ
  leftUnit : ℤ
  rightUnit : ℤ
  leftUnit_not_seven_dvd : ¬ (7 : ℤ) ∣ leftUnit
  rightUnit_not_seven_dvd : ¬ (7 : ℤ) ∣ rightUnit
  bridge_eq :
    cubicGap * leftUnit =
      endpointGap * rightUnit
```

単なる、

```text
二つの gap の valuation が等しい
```

ではなく、

```text
二つの gap
+
左右の明示係数
+
両係数の 7-unit 性
+
exact integer equality
```

を一つの再利用可能な型へ固定しています。

canonical constructor では、

```text
leftUnit  = seventhPowerSndCore
rightUnit = Q * norm(root)
```

が採用されています。

`rightUnit_not_seven_dvd` は $7$ の素数性で積を分解し、`Q` と `norm(root)` の既存非可除性にそれぞれ衝突させています。

### 任意の $7^k$ 上の unit 化

```lean
leftUnit_isUnit
rightUnit_isUnit
```

は、整数係数が $7$ で割れないことから、

```lean
IsUnit (coefficient : ZMod (7 ^ k))
```

を任意の $k$ に対して構成しています。

続く、

```lean
explicitUnit p k
```

は、

$$
U_k=\operatorname{rightUnit}\cdot\operatorname{leftUnit}^{-1}
$$

です。

さらに、

```lean
explicitUnit_isUnit
```

も積の unit 性として閉じています。

### Gap の explicit unit equality

最終定理、

```lean
RamifiedGapUnitBridgePacket
  .cubicGap_eq_endpointGap_mul_explicitUnit
```

は、

$$
R-L=(c-e)U_k\qquad\text{in }\operatorname{ZMod}(7^k)
$$

を証明しています。

証明は `leftUnit` の unit witness の逆元を明示的に掛け、整数 bridge の cast を代入してキャンセルしています。

したがって、この theorem は、

```text
valuation が等しいので、何らかの unit が存在する
```

という存在証明ではありません。

```text
この式で定義された unit が実際に gap を変換する
```

という constructive な局所同値です。

$k=0$ の退化 modulus まで含めた statement も整合しています。

## 現在確定した ramified 自己相似

RAMIFIED-001〜003 を合成すると、現在 Lean は次を認可しています。

```text
endpoint gap:
  c - e

root-cubic gap:
  R - L

complete depth:
  6 + 7 * padicValNat 7 gapRoot

exact local relationship:
  R - L = (c-e) × explicit 7-unit
```

すなわち、

$$
\boxed{\text{root-cubic gap は endpoint gap の }7\text{-adic unit 変換である}}
$$

です。

これは「同じ大きさ」でも「同じ valuation」でもなく、**同じ $7$-進局所軸上の同一 orbit**まで昇格しました。

## 露出した次の魔核

次に問うべきは、`explicitUnit` が単なる unit なのか、それとも **七乗へ吸収できる unit** なのかです。

endpoint gap は、

$$
c-e=7^6A^7
$$

という exact seventh-power shape を持っています。

したがって、

$$
R-L=(c-e)U
$$

において $U$ が七乗なら、

$$
R-L=7^6(AW)^7
$$

という同じ ramified gap shape を再生成できます。

逆に、$U$ が七乗でなければ、ここに **unit-class obstruction** が存在します。

### 最初の非自明 modulus は $49$

mod $7$ では、任意の unit が Frobenius によって七乗として見えるため、分類力がありません。

最初の本当の判定面は、

$$
\operatorname{ZMod}(49)
$$

です。

$(\mathbb Z/49\mathbb Z)^\times$ は位数 $42$ で、七乗写像の像は六元しかありません。

unit $U$ について、

$$
U\text{ が七乗}\iff U^7=U\pmod{49}
$$

となります。

したがって次の最小 audit は、

```lean
def RamifiedGapUnitBridgePacket.IsSeventhPowerMod49
    (p : RamifiedGapUnitBridgePacket) : Prop :=
  ∃ w : ZMod 49, w ^ 7 = p.explicitUnit 2
```

そして unit 条件を使い、

```lean
theorem isSeventhPowerMod49_iff :
    p.IsSeventhPowerMod49 ↔
      (p.explicitUnit 2) ^ 7 = p.explicitUnit 2
```

を固定することです。

### coherence も同時に欲しい

現在の `explicitUnit p k` は各 $k$ ごとに正しく構成されています。

次に $7$-進整数の一つの unit として扱うなら、reduction compatibility、

```text
explicitUnit (k + 1)
  ↓ mod 7^k
explicitUnit k
```

も証明すべきです。

逆元 witness は noncomputable ですが、逆元の一意性を使えば coherence は示せるはずです。

## 次 checkpoint

```text
FLT7-RAMIFIED-004
explicit ramified unit-class audit
```

到達目標は二段です。

```text
1. explicitUnit の 7^k reduction coherence

2. explicitUnit mod 49 の seventh-power class 判定
```

想定 outcomes：

```text
Outcome A
  explicitUnit は七乗 class
  → 高次 7^k への lift 条件を調べる

Outcome B
  explicitUnit は非七乗 class
  → ramified unit obstruction として固定

Outcome C
  summit の residue により class が分岐
  → finite residue classifier を構成
```

ここで大事なのは、非七乗だった場合にも即座に `False` としないことです。

矛盾にするには別途、

```text
root-cubic gap も seventh-power shape を持たねばならない
```

という receiver が必要です。

**RAMIFIED-003 は、その receiver の直前にある unit 魔核を完全に露出しました。**
