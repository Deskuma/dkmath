# FLT5 local tower: cp-001–cp-004 summary

作成日: 2026-07-20

対象:

- Repository: `Deskuma/dkmath`
- Branch: `hackathon/feature-gn5-flt5-260719-v0`
- Pull request: `#56`
- Current head at summary creation: `5845094577283a948ab9ae391e6f838cce6912ff`

本資料は、FLT5 local experiment tower の会話・実装作業を `cp-001` から `cp-004` の四段階に圧縮した索引である。

詳細な発想、分岐、失敗経路、レビュー過程は会話アーカイブ側へ残す。本資料では、Lean source に定着した定義・定理・frontier の移動だけを記録する。

## 0. 現在の最終到達点

現在、FLT5 local tower は次の一命題へ圧縮されている。

```lean
GoldenZeroSectorArithmeticExclusion → FLT5Target
```

Lean 上の公開 receiver は次である。

```lean
theorem flt5Target_of_zeroArithmetic
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    FLT5Target
```

したがって、現時点で未証明の frontier は次の一項だけである。

```text
GoldenZeroSectorArithmeticExclusion
```

本資料は FLT5 の無条件証明完成を主張しない。

---

# cp-001 — Standalone-first GN5 local tower

## 目的

既存の一般指数 FLT research route を直接再利用せず、指数 `5` 専用の小さな実験塔を独立に構築する。

基本方針は次である。

```text
局所定義
→ Lean で認可
→ standalone 化
→ 完成部品だけを後に共通化
```

## 中核定義

```lean
def Fermat5Equation (x y z : ℕ) : Prop :=
  x ^ 5 + y ^ 5 = z ^ 5
```

```lean
structure CounterexamplePack (x y z : ℕ) : Prop where
  hx : 0 < x
  hy : 0 < y
  hz : 0 < z
  hxy : Nat.Coprime x y
  hEq : Fermat5Equation x y z
```

指数五専用 GN 多項式を定義した。

```text
GN5(g,y)
  = g^4
  + 5 g^3 y
  + 10 g^2 y^2
  + 10 g y^3
  + 5 y^4
```

主恒等式は次である。

```text
(g + y)^5 - y^5 = g * GN5(g,y)
```

## Clean channel

局所素数 channel を明示的な contract として分離した。

```lean
def CleanGN5Channel (g y q : ℕ) : Prop :=
  Nat.Prime q ∧
  q ∣ GN5 g y ∧
  ¬ q ∣ g ∧
  ¬ q ^ 2 ∣ GN5 g y
```

この contract から、直接整除版と `padicValNat` 版の二経路で、完全五乗との衝突を構成した。

概念的な証明線は次である。

```text
x^5 = g * GN5(g,y)
q ∣ GN5(g,y)
q ∤ g
q^2 ∤ GN5(g,y)

完全五乗側:
  q ∣ x → q^5 ∣ x^5

clean channel 側:
  q^2 ∤ g * GN5(g,y)

矛盾
```

## モジュール群

cp-001 で確立した主要 surface:

```text
DkMath.FLT.Five.Basic
DkMath.FLT.Five.GN5
DkMath.FLT.Five.CleanChannel
DkMath.FLT.Five.Valuation
DkMath.FLT.Five.BranchB
DkMath.FLT.Five.Provider
DkMath.FLT.Five.BranchA
DkMath.FLT.Five.Main
DkMath.FLT.Five.Standalone
DkMathTest.FLT.Five.CheckAxioms
```

## 到達点

```text
CleanGN5Channel が与えられれば、その局所反例候補は排除できる。
```

ただし、すべての反例候補へ clean channel を供給する theorem と、`5 ∣ z-y` 側の exceptional branch は未解決であった。

---

# cp-002 — Signed five-adic and golden exceptional reduction

## 目的

単純な clean channel では閉じない exceptional branch を、符号付き五進構造と黄金整数環へ移送する。

## Signed Branch-A orientation

差側・和側の向きを分離し、符号付き routing を構築した。

```text
z - y orientation
z + y orientation
```

その後、共通の五進 exceptional packet へ合流させた。

## Exact five-adic packet

exceptional branch は、概念的に次の power split へ圧縮された。

```text
carrier = 5^4 * a^5
residual = 5 * b^5
```

ここで `a` と `b` は正で互いに素であり、さらに `5 ∤ b` が得られる。

## Square-golden bridge

平方差構造を黄金整数環へ移し、`GoldenInt` 上の要素 `beta` を構成した。

重要な packet data は次である。

```text
goldenNorm beta = b^5
beta.snd = -5^7 * a^10
```

`tau` による visible ramifier を除去し、stripped packet を得た。

```text
tau_not_dvd_beta
five_not_dvd_beta_norm
```

さらに共役との相対素性を確定した。

```text
GoldenRelPrime beta (goldenConj beta)
```

## 主なモジュール

```text
DkMath.FLT.Five.SignedBranchA
DkMath.FLT.Five.SignedFiveAdic
DkMath.FLT.Five.SignedFiveAdicPowerSplit
DkMath.FLT.Five.SignedSquareGoldenExceptional
DkMath.FLT.Five.SquareGoldenBridge
DkMath.FLT.Five.SquareGoldenNormalForm
DkMath.FLT.Five.GoldenOrder
DkMath.FLT.Five.GoldenDivisibility
DkMath.FLT.Five.SignedGoldenRamifierStripped
DkMath.FLT.Five.SignedGoldenConjugateCoprime
```

## 到達点

exceptional branch は、次の因数分解問題へ縮約された。

```text
beta * goldenConj beta = goldenOfInt(b)^5
GoldenRelPrime beta (goldenConj beta)
```

残る frontier は、互いに素な二因子の積が第五冪なら、各因子が unit 倍の第五冪になることの証明であった。

---

# cp-003 — Golden Euclidean domain and coprime fifth-power extraction

## 目的

`GoldenInt = ℤ[φ]` 上で Euclidean algorithm を構築し、互いに素な第五冪因子分離を無条件化する。

## Golden Euclidean geometry

有理座標上の商を作り、最近整数への同時丸めを用いた。

誤差座標を `u,v` とすると、基本 norm form は次である。

```text
u^2 + u*v - v^2
```

平方セル `|u|,|v| ≤ 1/2` 上で、次の sharp bound を証明した。

```text
|u^2 + u*v - v^2| ≤ 5/16 < 1
```

これにより、明示的な商と剰余について norm size の strict decrease を得た。

## EuclideanDomain instance

```text
EuclideanDomain GoldenInt
```

を構築し、そこから局所 `GCDMonoid GoldenInt` を得た。

## Coprime fifth-power extraction

`GoldenRelPrime x y` から `gcd x y` が unit であることを示し、Mathlib の associated-power theorem と接続した。

中心 theorem:

```lean
theorem goldenCoprimeFactorOfFifthPower :
    GoldenCoprimeFactorOfFifthPower
```

これにより stripped packet について無条件に次が得られた。

```text
beta = epsilon * gamma^5
GoldenUnit epsilon
```

公開 core:

```lean
theorem signedGoldenFifthPowerUpToUnitCore :
    SignedGoldenFifthPowerUpToUnitCore
```

## 主なモジュール

```text
DkMath.FLT.Five.GoldenEuclidean
DkMath.FLT.Five.GoldenCoprimeFactor
DkMath.FLT.Five.SignedGoldenFifthPower
```

## 到達点

factorization obstruction は消滅し、frontier は unit の不定性へ移った。

```text
beta = epsilon * gamma^5
```

次の問題は、黄金 unit `epsilon` を第五冪を法として有限個の sector に分類し、その各 sector を排除することであった。

---

# cp-004 — Golden unit sectors and zero-sector reduction

cp-004 は複数の小 checkpoint に分けて実装されたが、本資料では一つの frontier 圧縮段階として扱う。

## 4.1. Fifth-power coordinate formulas

`gamma = (r,s)` に対する第五冪座標を明示した。

```text
F(r,s)
  = r^5
  + 10 r^3 s^2
  + 10 r^2 s^3
  + 10 r s^4
  + 3 s^5
```

```text
S(r,s)
  = 5 s H(r,s)
```

ここで quartic factor は次である。

```text
H(r,s)
  = r^4
  + 2 r^3 s
  + 4 r^2 s^2
  + 3 r s^3
  + s^4
```

`φ^i * gamma^5` の第二座標は五 sector で次になる。

```text
i = 0: S
i = 1: F + S
i = 2: F + 2S
i = 3: 2F + 3S
i = 4: 3F + 5S
```

## 4.2. Nonzero sectors 1–4 の排除

packet factorization から、第五冪 base の norm を固定した。

```text
goldenNorm gamma = b
or
goldenNorm gamma = -b
```

したがって、packet data `5 ∤ b` より次を得た。

```text
5 ∤ goldenNorm gamma
```

一方、mod 5 で次を証明した。

```text
F(r,s) ≡ r + 3s          (mod 5)
goldenNorm(r,s) ≡ (r+3s)^2 (mod 5)
```

sector `1,2,3,4` では、packet の第二座標が 5 で割れることと `5 ∣ S` から `5 ∣ F` が導かれる。

よって、

```text
5 ∣ F
→ 5 ∣ goldenNorm gamma
```

となり、`5 ∤ goldenNorm gamma` と矛盾する。

中心 theorem:

```lean
theorem signedGolden_nonzero_unitSector_false
```

これにより、五 sector のうち `i = 0` だけが残った。

## 4.3. Zero-sector arithmetic

zero sector は次である。

```text
beta = gamma^5
```

第二座標から、符号付き方程式を得た。

```text
s * H(r,s) = -5^6 * a^10
```

さらに次を証明した。

```text
H(r,s) ≡ goldenNorm(r,s)^2  (mod 5)
5 ∤ H(r,s)
gcd(|r|,|s|) = 1
gcd(|s|,|H(r,s)|) = 1
```

これらから exact tenth-power split を得た。

```text
|s| = 5^6 * c^10
|H(r,s)| = d^10
```

中心 theorem:

```lean
theorem SignedGoldenRamifierStrippedPacket.zeroSector_tenthPower_split
```

## 4.4. Exact arithmetic frontier

zero sector の残問題を packet 型から切り離し、純整数命題として定義した。

```lean
abbrev GoldenZeroSectorArithmeticExclusion : Prop := ...
```

この contract は概念的に次の情報を受け取る。

```text
goldenNorm(r,s) = ±b
s * H(r,s) = -5^6 * a^10
gcd(a,b) = 1
5 ∤ b
gcd(|r|,|s|) = 1
|s| = 5^6 * c^10
|H(r,s)| = d^10
```

そして `False` を要求する。

## 4.5. Orientation closure and primitive normalization

任意の primitive packet について、少なくとも一方の gap orientation が Branch-B receiver に入ることを証明した。

```lean
theorem CounterexamplePack.branchB_orientation
```

また任意の正の Fermat5 解から gcd を除去し、primitive `CounterexamplePack` を構成した。

```lean
theorem exists_counterexamplePack_of_positive_fermat5
```

これにより、unit classification と zero-sector arithmetic exclusion を仮定すれば、一般の正の解まで排除できる receiver が完成した。

```lean
theorem flt5Target_of_unitClasses_of_zeroArithmetic
```

## 4.6. Golden unit classification

最後に、unit sector contract 自体を無条件に証明した。

黄金逆単位を定義した。

```lean
def goldenPhiInv : GoldenInt := ⟨-1, 1⟩
```

座標作用:

```text
(a,b) * φ      = (b, a+b)
(a,b) * φ⁻¹    = (b-a, a)
```

unit measure:

```lean
def goldenUnitMeasure (x : GoldenInt) : ℕ :=
  |x.fst| + |x.snd|
```

非最小 unit について、`φ` または `φ⁻¹` を掛けることで measure が strict に減少する descent を証明した。

```lean
theorem goldenUnit_descent
```

第五冪を法とする sector membership を定義した。

```lean
def GoldenUnitFifthClass (x : GoldenInt) : Prop :=
  ∃ i : Fin 5, ∃ delta : GoldenInt,
    x = goldenPhi ^ i.val * delta ^ 5
```

`φ` と `φ⁻¹` を掛けたときの sector 遷移を証明し、measure による強帰納法で全 unit を分類した。

```lean
theorem goldenUnitFifthClass_of_unit
```

最終 theorem:

```lean
theorem goldenUnitClassesModFifth :
    GoldenUnitClassesModFifth
```

これにより第一障壁は消滅した。

## 4.7. cp-004 最終 receiver

unit classification は無条件となったため、最終 receiver は一仮定だけになった。

```lean
theorem flt5Target_of_zeroArithmetic
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    FLT5Target
```

同じ仮定から、次も得られる。

```text
CounterexamplePackRefuter
PositiveFermat5Refuter
FLT5Target
```

---

# 5. Frontier の移動

四段階の frontier は次のように移動した。

```text
cp-001
  clean GN5 channel provider
  + exceptional Branch A

cp-002
  coprime golden factors of a fifth power

cp-003
  golden unit ambiguity in beta = epsilon * gamma^5

cp-004 前半
  unit classification
  + zero-sector arithmetic

cp-004 完了
  GoldenZeroSectorArithmeticExclusion only
```

最終的には次の一本となった。

```text
GoldenZeroSectorArithmeticExclusion
  → SignedGoldenZeroSectorExclusion
  → SignedGoldenUnitFifthPowerExclusion
  → CounterexamplePackRefuter
  → PositiveFermat5Refuter
  → FLT5Target
```

---

# 6. 現在の主要モジュール一覧

```text
DkMath.FLT.Five.Basic
DkMath.FLT.Five.GN5
DkMath.FLT.Five.CleanChannel
DkMath.FLT.Five.Valuation
DkMath.FLT.Five.BranchA
DkMath.FLT.Five.BranchB
DkMath.FLT.Five.Provider
DkMath.FLT.Five.SignedBranchA
DkMath.FLT.Five.SignedFiveAdic
DkMath.FLT.Five.SignedFiveAdicPowerSplit
DkMath.FLT.Five.SignedSquareGoldenExceptional
DkMath.FLT.Five.SquareGoldenBridge
DkMath.FLT.Five.SquareGoldenNormalForm
DkMath.FLT.Five.GoldenOrder
DkMath.FLT.Five.GoldenDivisibility
DkMath.FLT.Five.GoldenEuclidean
DkMath.FLT.Five.GoldenCoprimeFactor
DkMath.FLT.Five.GoldenUnitClassification
DkMath.FLT.Five.SignedGoldenRamifierStripped
DkMath.FLT.Five.SignedGoldenConjugateCoprime
DkMath.FLT.Five.SignedGoldenFifthPower
DkMath.FLT.Five.SignedGoldenUnitClasses
DkMath.FLT.Five.SignedGoldenSectorArithmetic
DkMath.FLT.Five.SignedGoldenZeroSector
DkMath.FLT.Five.SignedGoldenClosure
DkMath.FLT.Five.Main
DkMath.FLT.Five.Standalone
DkMathTest.FLT.Five.CheckAxioms
```

---

# 7. Validation state

総括作成時点の PR head:

```text
5845094577283a948ab9ae391e6f838cce6912ff
```

最新 Lean CI:

```text
Lean CI #142
completed / success
```

`Main.lean` は `GoldenUnitClassification` を含む最終 tower を import し、`CheckAxioms.lean` は次の主要 theorem 群まで監査対象に含めている。

```text
goldenUnit_descent
goldenUnitFifthClass_mul_phi
goldenUnitFifthClass_mul_phiInv
goldenUnitFifthClass_of_unit
goldenUnitClassesModFifth
signedGoldenFiniteUnitSectorCore
counterexamplePackRefuter_of_zeroArithmetic
positiveFermat5Refuter_of_zeroArithmetic
flt5Target_of_zeroArithmetic
```

---

# 8. 次 checkpoint の対象

残る対象は次だけである。

```text
GoldenZeroSectorArithmeticExclusion
```

既に得られている zero-sector data:

```text
s * H(r,s) = -5^6 * a^10
|s| = 5^6 * c^10
|H(r,s)| = d^10
gcd(|r|,|s|) = 1
gcd(|s|,|H(r,s)|) = 1
5 ∤ H(r,s)
```

次段候補として観測されている反転式は次である。

```text
16 H(r,s)
  = (2r+s)^4
  + 10 (2r+s)^2 s^2
  + 5 s^4
```

これを平方 norm へ反転すると、候補的に次の generalized Pell 型へ移る。

```text
U^2 - 5 V^2 = W^2
```

ただし以下は本資料作成時点では未証明の次段課題である。

```text
gcd(U-W,U+W) の exact evaluation
2-adic / 5-adic mass distribution
factor-power split
strictly smaller zero-sector solution
well-founded descent
```

---

# 9. 一文総括

```text
cp-001 で GN5 の局所剣を鍛え、
cp-002 で exceptional branch を黄金整数世界へ移し、
cp-003 で Euclidean/GCD により unit-times-fifth-power まで分解し、
cp-004 で無限 unit 軌道を五 sector へ反転して四 sector を消し、
最後の zero-sector arithmetic 一点だけを残した。
```
