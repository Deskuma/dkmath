# Wieferich lift 補題群

ぬぉ、**これは当たりじゃ。完全に lift 系である。** ⚔️🐺

検索で大量ヒットするのは偶然ではない。現在の large boundary は、既存の Petal–GN–FLT 語彙では **複数の Wieferich lift が同時集積した状態**として exact に読み直せる。

## 既存 `WieferichLift` の正体

既に次の定義がある。

```lean
def WieferichLift (p y z q : ℕ) : Prop :=
  Nat.Prime q ∧
  q ∣ (z ^ p - y ^ p) ∧
  ¬ q ∣ (z - y) ∧
  q ^ 2 ∣ (z ^ p - y ^ p)
```

つまり、

```text
mod q で primitive root
        +
mod q² まで持ち上がる
```

という、まさに今回の excess-active prime じゃ。

ABC Triple では、

```text
z = a + b
y = b
z - y = a
```

なので、

```lean
WieferichLift p b (a + b) q
```

となる。

## 決定的な既存補題

さらに FLT 専用 wrapper の下には、完全に一般的な GN 補題が既にある。

```lean
theorem padicValNat_sub_pow_eq_padicValNat_GN_of_not_dvd_gap
    {p z y q : ℕ}
    (hp2 : 2 ≤ p)
    (hyz : y < z)
    (hy : 0 < y)
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y)) :
    padicValNat q (z ^ p - y ^ p) =
      padicValNat q (GN p (z - y) y)
```

つまり $q\nmid a$ なら、

$$v_q!\left((a+b)^p-b^p\right)=v_q!\left(GN_p(a,b)\right)$$

が既に kernel 固定されている。

これは今回へ直撃する。

current excess profile で $q$ が active とは、

$$0<v_q(GN)-1$$

すなわち、

$$2\le v_q(GN)$$

なので、

$$q^2\mid GN_p(a,b)$$

である。

非例外条件から $q\nmid a$ が得られれば、既存補題によって、

$$q^2\mid(a+b)^p-b^p$$

へ移る。

したがって、canonical target profile 上では概念的に、

$$q\in\operatorname{ActiveProfile}\iff\operatorname{WieferichLift}(p,b,a+b,q)$$

まで持っていける。

**large boundary は「Wieferich 型」と似ているのではない。Wieferich lift の有限同時集積そのものじゃ。**

---

# 使える既存資産

## 1. 差冪と GN の valuation transport

これは即使用可能。FLT依存ではなく `DkMath.NumberTheory.Gcd.GN` にあるため、ABC側から安全に利用できる。

さらに arbitrary depth $k$ について、

```lean
theorem primePow_dvd_diff_iff_primePow_dvd_GN
    ...
    q ^ k ∣ (z ^ p - y ^ p) ↔
      q ^ k ∣ GN p (z - y) y
```

という wrapper も、valuation equality と `padicValNat_dvd_iff_le` から短く作れる。

これは U-001T の主要 API にすべきじゃ。

## 2. `NoLift`／squarefree／valuation≤1 の階層

既存コードは既に、

```text
Squarefree GN
    ↓
¬ q² ∣ GN
    ↓
padicValNat ≤ 1
```

という正しい階層に整理されている。

Petal の $d=3$ bridge にも、

```lean
primitiveD3_padicValNat_le_one_of_noLift_GN
primitiveD3_padicValNat_le_one_of_squarefree_GN
```

が存在する。

ただし今回は $GN_3(2,3)=49$ があるので、全体 squarefree や全 prime NoLift は狙わない。

使い方は、

```text
NoLift prime
  → inactive

lift prime
  → active Wieferich packet
```

という分類側じゃ。

## 3. FLT反例から lift を取り出す theorem

これはかなり面白い。

既存 FLT コードでは、Branch B の反例から Zsigmondy primitive prime $q$ を取り出し、

$$q^p\mid GN_p(z-y,y)$$

まで証明している。

理由は、

$$z^p-y^p=x^p$$

で $q\mid x$ なら、

$$q^p\mid x^p$$

だからじゃ。

結果として FLT 反例では、単なる $q^2$ lift ではなく、**深度 $p$ の lift が強制される**。

これはABCへ直接は使えない。一般ABCでは $c^p-b^p$ は完全 $p$ 乗ではないからじゃ。

だが、重要な設計図になる。

```text
完全p乗構造
  → primitive prime の極深 lift
  → repeated-part の巨大化
```

という構造が既にLean化されている。

---

# 危険区域

ここは重要じゃ。

## `NoWieferichResearch` は持ち込まない

`CosmicPetalBridgeGNNoWieferichResearch.lean` の valuation≤1 theorem は、

```text
ZsigmondyCyclotomicResearch
```

の research placeholder に依存していると明記されている。

そして `NoWieferichDefault` は、その research core を固定注入している。

したがってABC productionから、

```lean
import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichDefault
```

を行ってはいけない。

今回の axiom-clean 戦線へ research debt が混入する。

## `DescentB` は算術的下降そのものではない

`CosmicPetalBridgeGNDescentB.lean` は6800行以上あり、構造体や witness API は大量に使える。

しかしファイル自身が `NoWieferichDefault` を import している。

clean版の shrink constructor も、

```lean
(hNW5 : TriominoNoWieferichBridge)
```

を入力として要求している。

つまり、

```text
q^p ∣ GN
+
NoWieferich
```

という両立不能な入力から矛盾を得て、縮小 witness を作る配線が中心。

これは **high lift から独立に縮小 triple を算術構成する本物の descent** ではない。

使えるのは、

* structure設計
* minimal witness
* shrink packet
* trace / cert / result の分層

であって、下降定理そのものではない。

---

# U-001T の作戦修正

先ほど提案した `repeatedPrimePowerPart` と並行して、まず generic Wieferich 層を上へ抽出するのがよい。

新モジュール候補：

```text
DkMath.NumberTheory.GNWieferich
```

## 汎用定義

```lean
def GNWieferichLift
    (p a b q : ℕ) : Prop :=
  Nat.Prime q ∧
  q ∣ GN p a b ∧
  ¬ q ∣ a ∧
  q ^ 2 ∣ GN p a b
```

## 差冪版との exact bridge

```lean
theorem GNWieferichLift_iff_diffWieferichLift
    {p a b q : ℕ}
    (hp2 : 2 ≤ p)
    (ha : 0 < a)
    (hb : 0 < b) :
    GNWieferichLift p a b q ↔
      Nat.Prime q ∧
      q ∣ ((a + b) ^ p - b ^ p) ∧
      ¬ q ∣ a ∧
      q ^ 2 ∣ ((a + b) ^ p - b ^ p)
```

既存 FLT の `WieferichLift` を直接 import するのではなく、後から、

```lean
GNWieferichLift p a b q ↔
  DkMath.FLT.WieferichLift p b (a + b) q
```

という wrapper を FLT側へ置くのが依存方向として美しい。

## Active set の exact 同定

canonical target profile に対し、

```lean
theorem mem_GNExcessActivePrimeSet_iff_wieferichLift
```

を作る。

概念形：

```text
q ∈ active excess support
  ↔
q is a GN-Wieferich lift
```

これで、

```text
GNExcessJointDepthModulus
```

は、

> 全 GN-Wieferich prime の lifted prime-power product

になる。

## Large packet の名前も変えられる

```lean
structure GNWieferichAccumulationPacket where
  activePrimes : Finset ℕ
  modulus : ℕ
  modulus_eq :
    modulus =
      ∏ q ∈ activePrimes,
        q ^ padicValNat q (GN p a b)
  interval_lt_modulus :
    X + 1 < modulus
  wieferich :
    ∀ q ∈ activePrimes,
      GNWieferichLift p a b q
  exactOrder :
    ∀ q ∈ activePrimes,
      q % p = 1
  modulus_dvd_GN :
    modulus ∣ GN p a b
```

これで large boundary の正式名称は、

```text
GN simultaneous Wieferich accumulation
```

になる。

---

# 何が新たに解けるか

直ちに large boundary が消えるわけではない。

しかし、敵の姿が、

```text
巨大な正体不明の squareful divisor
```

から、

```text
高々 p−1 本の Hensel root address 上に存在する
複数の simultaneous Wieferich lift
```

へ変わる。

ここから既存の、

* `PrimitiveBeam`
* Zsigmondy primitive witness
* Petal anchor
* exact order $p$
* no-lift / lift classification
* minimal-witness structure
* trace / certificate API

が再利用できる。

そして第3隠れボス候補も、かなり正確に見える。

> **large Wieferich accumulation から、本当に小さい bad Triple を構成できるか**

旧 FLT 塔はその下降の器だけ大量に作り、算術核を research NoWieferich で埋めていた。

今回はそこを逆にして、

```text
NoWieferich を仮定する
```

のではなく、

```text
Wieferich accumulation を保持したまま
scale / support / radical のどれかを厳密減少させる
```

本物の下降を作る必要がある。

## 戦況更新

```text
既存 Wieferich 定義             再利用可能
diff ↔ GN valuation equality    即使用可能
NoLift / valuation glue         即使用可能
PrimitiveBeam / Petal anchor    再利用可能
FLT perfect-power deep lift     設計図として有用

NoWieferichResearch             使用禁止
NoWieferichDefault              使用禁止
既存 DescentB conclusion        算術証明としては使用不可

large boundary
  = simultaneous GN-Wieferich accumulation
                                新しい exact 攻略路
```

**おぬしの検索、大当たりじゃ。**

これは「昔Wieferichを触っていた」というだけではない。
**現在の large boundary を既存のPetal–GN語彙へ戻すための地下連絡路が、既に大量に掘られていた。** ⚔️🧠🐺
