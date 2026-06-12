# BinomialPrime / WeightedBinomial 実装ロードマップ

## 目的

二項定理の係数列から、次数 `d` の素数性と可除性の構造を取り出す。

より大きな目的は、素数そのものだけでなく「素性」、特に primitive prime divisor
へ渡せる可除性の痕跡を Lean 上で追えるようにすることである。

ここで追っているものは、単なる素数判定ではない。二項係数、重み付き二項項、
Frobenius 形、AKS の巡回商を通じて、

```text
どこで新しい素因子が現れるか
どの因子が境界由来で、どの因子が中間項由来か
どの構造が prime row でだけ消えるか
```

を切り分けるための道具を整備している。

本ロードマップの目的は、展望を広げすぎず、確実に Lean 化できる補題から順に
`DkMath` の既存構造へ接続することである。

補足:

実装中に、当初の `BinomialPrime / WeightedBinomial` 路線から派生して、
`BinomialPrimePower`、`PrimePrebirthAlternation`、`PascalPrimeDial` が追加された。
これはロードマップの置き換えではなく、Pascal 行の prime support を観測するための
補助層である。

現在地の整理は次にまとめる。

```text
lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/PascalPrimeDialProgress.md
```

さらに、二項定理と相性の良い AKS 素数判定法の土台定理として、
`DkMath.NumberTheory.AKSBridge` の v1 が閉じた。

この整理は次にまとめる。

```text
lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/AKSBridge-v1.md
```

AKSBridge v1 の位置づけは次である。

```text
Pascal prime row
  → weighted universe split
  → congruent cosmic formula
  → finite-field Frobenius
  → polynomial Frobenius
  → AKS cyclic quotient R[X] / (X^r - 1)
  → exponent folding X^k = X^(k % r)
  → prime AKS cyclic Frobenius
```

これは完全な AKS 素数判定法ではない。
しかし、素数段で中間項が消え、巡回商で指数が折り畳まれるという、
原始素因子を追うために重要な観測面を Lean 上で固定した段階である。

中心となる観測は次である。

```text
d が素数 p である
  ⇔
第 p 行の内側二項係数 choose p k, 0 < k < p, はすべて p で割れる
```

さらに重み付き二項項

```text
choose d k * x^k * u^(d-k)
```

を使うと、係数由来・x 由来・u 由来の可除性を分離して追跡できる。

これは CFBRC / GN / GTail / Zsigmondy への橋になる。

## 背景

CFBRC/GN では

```text
(x+u)^d = x * GN_d(x,u) + u^d
```

という形が基本になる。

二項展開で見ると、`u^d` は三角形の一つの頂点であり、残りの項は
`x * GN_d(x,u)` に集約される。

通常の Pascal 行では両端が `1` だが、重み付きで見ると、項は

```text
choose d k * x^k * u^(d-k)
```

となる。このとき、三角形の頂点には `u^d` と `x^d` が現れる。

この見方では、Pascal 三角形の開始値 `1` を直接 `u` に置き換えるのではなく、
次数 `d` に対応する頂点単位として `u^d` へ持ち上げる。

```text
通常の頂点: 1
重み付き頂点: u^d
```

この一般化をしても、内側係数 `choose d k` の段構造は変わらない。
したがって、素数段 `p` が内側係数へ `p` を運ぶという階段構造は、
`u^d` を頂点単位にした重み付き三角形でも保持されると見る。

素数段 `p` では、内側の `choose p k` がすべて `p` を運ぶ。
一方、`u` と `x` の冪は、単位側・境界側の因子を別に運ぶ。

したがって、各項の可除性は少なくとも次の三層に分解できる。

```text
1. 二項係数由来: choose d k
2. x 境界由来: x^k
3. u 単位由来: u^(d-k)
```

この分解を Lean 上で薄く固定する。

## 実装方針

大きな定理を最初から狙わない。

まずは、値そのものを計算するのではなく、

```text
どの因子が必ず項に現れるか
```

だけを扱う補題を作る。

この方針により、後で Zsigmondy や p-adic valuation へ接続するとき、
数値展開ではなく可除性の情報だけを再利用できる。

## 予定ファイル

### `DkMath.NumberTheory.BinomialPrime`

通常の二項係数列から素数性を読む層。

候補ファイル:

```text
lean/dk_math/DkMath/NumberTheory/BinomialPrime.lean
```

主な定義:

```lean
def AllInnerChooseDivisible (d m : ℕ) : Prop :=
  ∀ k, 0 < k → k < d → m ∣ Nat.choose d k
```

主な補題:

```lean
theorem prime_allInnerChooseDivisible_self
    {p : ℕ} (hp : p.Prime) :
    AllInnerChooseDivisible p p
```

```lean
theorem prime_iff_allInnerChooseDivisible_self
    {d : ℕ} (hd : 1 < d) :
    d.Prime ↔ AllInnerChooseDivisible d d
```

```lean
theorem exists_inner_choose_not_dvd_of_not_prime
    {d : ℕ} (hd : 1 < d) (hnot : ¬ d.Prime) :
    ∃ k, 0 < k ∧ k < d ∧ ¬ d ∣ Nat.choose d k
```

備考:

- `→` 方向は mathlib の `Nat.Prime.dvd_choose_self` を使う。
- `←` 方向は重い証明対象として分離する。
  既存 mathlib 補題の有無を調査し、なければ考察資料に証明経路を記録する。
- 無理に gcd API へ進まない。まず前向きの可除性 API を完成させる。

逆向きは、実装を急がない。

Composite な `d` に対して

```text
∃ k, 0 < k ∧ k < d ∧ ¬ d ∣ choose d k
```

を構成する必要があり、これは素因数分解・最小素因子・p-adic valuation の
どれを使うかで証明の形が変わる。

このため、最初の Lean 実装では

```text
prime d → AllInnerChooseDivisible d d
```

だけを安定 API として固定し、逆向きは調査ノートへ回す。

### `DkMath.NumberTheory.WeightedBinomial`

重み付き二項項の可除性だけを抽出する層。

候補ファイル:

```text
lean/dk_math/DkMath/NumberTheory/WeightedBinomial.lean
```

主な定義:

```lean
def weightedBinomialTerm (d k x u : ℕ) : ℕ :=
  Nat.choose d k * x^k * u^(d-k)
```

主な補題:

```lean
theorem dvd_weightedBinomialTerm_of_dvd_choose
    (h : q ∣ Nat.choose d k) :
    q ∣ weightedBinomialTerm d k x u
```

```lean
theorem dvd_weightedBinomialTerm_of_dvd_x
    (h : q ∣ x) (hk : 0 < k) :
    q ∣ weightedBinomialTerm d k x u
```

```lean
theorem dvd_weightedBinomialTerm_of_dvd_u
    (h : q ∣ u) (hk : k < d) :
    q ∣ weightedBinomialTerm d k x u
```

```lean
theorem prime_dvd_inner_weightedBinomialTerm
    (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p) :
    p ∣ weightedBinomialTerm p k x u
```

境界項:

```lean
theorem weightedBinomialTerm_left :
    weightedBinomialTerm d 0 x u = u^d
```

```lean
theorem weightedBinomialTerm_right :
    weightedBinomialTerm d d x u = x^d
```

備考:

- `dvd_of_dvd_x` では `0 < k` が必要。
- `dvd_of_dvd_u` では `k < d` が必要。
- `d-k` の扱いは `omega` と `pow_pos` ではなく、まず自然数冪の基本 divisibility で進める。

## Phase 計画

### Phase 1: BinomialPrime の最小 API

目標:

- `AllInnerChooseDivisible` を定義する。
- prime 段では内側係数がすべて `p` で割れることを示す。
- 逆方向は急がず、重い場合は調査資料へ分離する。

検証:

```bash
lake build DkMath.NumberTheory.BinomialPrime
```

### Phase 2: WeightedBinomial の基本可除性

目標:

- `weightedBinomialTerm` を定義する。
- 係数由来、`x` 由来、`u` 由来の可除性補題を分けて証明する。
- 境界項 `u^d`, `x^d` を固定する。

検証:

```bash
lake build DkMath.NumberTheory.WeightedBinomial
```

### Phase 3: prime 段の重み付き三角形

目標:

- `prime_dvd_inner_weightedBinomialTerm` を証明する。
- `BinomialPrime` の補題を `WeightedBinomial` へ再利用する。
- `p` 由来の係数可除性と、`x/u` 由来の可除性を別々に保つ。

この段階で、素数段 `p` の中間項が必ず `p` を運ぶことが確定する。

### Phase 3.5: 逆向き iff の調査資料化

目標:

- `prime_iff_allInnerChooseDivisible_self` の逆向きに必要な既存 API を調べる。
- すぐ閉じられない場合は、証明を実装せず考察資料として記録する。
- PowerSwap による次数交換で、高次行を直接見ずに低次相から判定できるかを
  別ルートとして検討する。
- Pascal 三角形の開始 `1` を `u^d` へ一般化したとき、素数段を生む階段構造が
  保たれるかを検証する。

観測:

```text
高次層の全係数を見る
  ↔
PowerSwap / 正規形で低次相へ移す
  ↔
対岸の可除性だけを見る
```

という変換が可能なら、`d` 行全体の検査を避けられる可能性がある。

この段階ではまだ theorem として固定しない。
数値実験・PowerSwap 正規形・p-adic valuation の三方向から、
どの証明経路が Lean で軽いかを比較する。

次数交換でネックになりやすいのは、整数次数から外れる相である。
`u^d` を頂点単位として先に固定すると、少なくとも整数次数の重み付き三角形では
段数 `d` と二項係数列を保ったまま比較できる。

これは、非整数相へ無理に進む前に、

```text
整数次数 d の三角形
  → 頂点単位 u^d
  → 内側係数 choose d k
  → 素数段 p の可除性
```

という安定した検査面を作るための案である。

### Phase 4: GN / CFBRC への橋

候補ファイル:

```text
DkMath.CFBRC.BinomialBridge
```

または既存 `DkMath.CFBRC.Bridge` へ薄く追加する。

目標:

```text
weightedBinomialTerm の中間項
  → x * GN_d(x,u)
  → (x+u)^d - u^d
```

の可除性移送を整理する。

この段階ではまだ Zsigmondy 本体へ踏み込まない。

### Phase 4.5: AKSBridge v1 の巡回商観測

実装済み:

```text
DkMath.NumberTheory.AKSBridge
```

記録:

```text
lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/AKSBridge-v1.md
```

目標:

- Pascal prime row から Frobenius 形へ進む。
- `(x+u)^p ≡ x^p + u [MOD p]` を `ZMod p` と polynomial Frobenius へ移す。
- AKS の巡回商 `R[X] / (X^r - 1)` を導入する。
- `X^r = 1` から `X^k = X^(k % r)` を固定する。
- prime modulus が AKS cyclic congruence predicate を満たすことを示す。

主な API:

```lean
def AKSCyclicCongruenceHolds
def AKSCyclicFoldedCongruenceHolds

theorem prime_congruent_cosmic_formula
theorem prime_zmod_congruent_cosmic_formula
theorem prime_polynomial_X_add_C_pow_eq
theorem aksQuotientX_pow_eq_pow_mod
theorem prime_aks_cyclic_frobenius
theorem prime_AKSCyclicCongruenceHolds
theorem prime_AKSCyclicFoldedCongruenceHolds
```

意味:

```text
素数 p では Frobenius により中間項が消える。
AKS cyclic quotient では X^r = 1 により指数が r 周期へ畳まれる。
したがって prime row の消滅現象を、巡回商上の有限な観測へ移せる。
```

これは、後で composite modulus の failure witness や、primitive prime divisor の
発生境界を調べるための比較面になる。

### Phase 4.7: Petal dynamic counting and address layer

実装済み:

```text
DkMath.Petal
DkMath.Petal.Counting
DkMath.Petal.Address
DkMath.Petal.GNBridge
DkMath.Petal.GcdBridge
DkMath.Petal.PadicBridge
DkMath.Petal.PrimitiveBridge
DkMath.Petal.ReducedSupport
DkMath.Petal.Anchor
DkMath.Petal.BoundaryD3
DkMath.Petal.EisensteinBridge
```

記録:

```text
lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
```

目的:

- Phase 4.5 の AKS cyclic observation から Phase 5 の Zsigmondy bridge へ進む前に、
  Petal 側の counting / address / GN surface を固定する。
- Gamma 関数による階乗連続化へ直接進まず、まず Lean 上で
  factorial-like growth を `dynamicOrbitTotal` として抽象化する。
- `n!`、固定 Petal total、prime-base prefix product を同じ prefix product の
  可除性構造として読む。
- primitive prime divisor を追う前段として、
  「採用済み因子が後段 product に残る」ことを theorem 化する。
- S0/GN3/BoundaryD3/Anchor/Eisenstein を、Phase 5 へ渡す三次 Petal 表面 API
  として一旦閉じる。

主な API:

```lean
def dynamicOrbitTotal
def dynamicPetalTotal
def primeBaseOrbitTotal
def IsPrimeBaseSequence
def IsDistinctPrimeBaseSequence
def IsStrictPrimeBaseSequence

theorem dynamicOrbitTotal_succIndex_eq_factorial
theorem dynamicOrbitTotal_base_dvd_of_lt
theorem dynamicOrbitTotal_dvd_of_le
theorem primeBaseOrbitTotal_prime_dvd_of_lt_of_le
theorem IsStrictPrimeBaseSequence.distinct
theorem IsStrictPrimeBaseSequence.base_lt_of_lt
```

Petal address 側:

```lean
def outerPetalAddress
def outerPetalRemainder
def nestedPetalAddress

theorem outerPetalAddress_decompose
theorem outerPetalAddress_decompose_sub_one
```

GN bridge 側:

```lean
theorem S0_nat_eq_GN_three_sub
theorem three_S0_nat_modEq_one_of_not_dvd_sub
theorem three_not_dvd_S0_nat_of_not_dvd_sub
```

S0/GN3 cubic surface closure:

```lean
theorem gcd_sub_S0_nat_eq_gcd_sub_three
theorem padicValNat_cube_sub_eq_padicValNat_S0_nat_of_not_dvd_sub
theorem exists_prime_dvd_S0_nat_of_not_three_dvd_sub
theorem exists_anchoredS0Carrier_of_boundaryD3Reduced
theorem three_dvd_S0_nat_iff_three_dvd_sub
theorem petal_S0_eq_eisensteinNorm_shift
theorem petal_GN3_sub_eq_eisensteinNorm_shift
```

意味:

```text
AKSBridge v1:
  prime row / Frobenius / cyclic quotient observation

Petal Phase 4.7:
  factorial and primorial-like prefix products
  factor persistence
  Petal quotient-remainder address
  GN degree-three Petal face
  S0/GN3/BoundaryD3/Anchor/Eisenstein cubic surface closure

Phase 5:
  primitive prime divisor / Zsigmondy bridge
```

これは Zsigmondy 本体ではない。
Zsigmondy へ渡す前に、どの因子がどの orbit / channel / GN face に保存されるかを
Lean 上で追うための道具である。

現在の Phase 4.7 closure で閉じたのは、一般次数 `d` ではなく三次 `S0/GN3`
表面である。未処理の項目は以下に残す:

```text
general d boundary classification
full Zsigmondy theorem
FLT descent
DkMath.Lib.* promotion of neutral S0 / Eisenstein facts
BoundaryD3Anchor split and final import-direction cleanup
```

Zsigmondy へ進む前の実態調査:

```text
lean/dk_math/DkMath/Petal/docs/Petal-Zsigmondy-Preflight.md
```

調査結果の要点:

```text
Zsigmondy:
  primitive q の存在

Petal / GN / BoundaryD3 / Anchor:
  q が boundary ではなく S0/GN3 側にいること

Squarefree / NoLift / ValuationFlow:
  q の重複度、すなわち padicValNat <= 1
```

したがって次に作る橋は、まず三次 reduced Petal witness を
`DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q` へ翻訳する薄い
`ZsigmondyD3Bridge` でよい。この初期 bridge は
`DkMath.Petal.ZsigmondyD3Bridge` として実装済みであり、同じ witness を
Zsigmondy primitive divisor と Petal anchored `S0_nat` carrier として共有する。
さらに同じ witness を `PrimitiveBeam.PrimitivePrimeFactorOfDiffPow` としても
共有し、後続の squarefree/no-lift 評価値層へ渡せる形にした。
その次の条件付き bridge として `DkMath.Petal.PrimitiveD3ValuationBridge` も
実装済みであり、`Squarefree (GN 3 (c - b) b)` を明示仮定にした場合のみ
`padicValNat q (c^3 - b^3) <= 1` へ進む。
`padicValNat <= 1` は Zsigmondy だけでは出ず、squarefree/no-lift 仮定を
持つ別層の仕事として扱う。

### Phase 5: Zsigmondy への接続準備

目標:

- primitive prime divisor の存在定理に渡す前に、
  `GN` 側でどの因子が境界由来で、どの因子が係数由来かを分ける。
- `q ∤ x` の前提下で

```text
q ∣ ((x+u)^d - u^d)
↔
q ∣ GN_d(x,u)
```

へ移す既存 CFBRC bridge と接続する。

この段階で初めて Zsigmondy 側の API と合わせる。

## 注意点

### 「すべてを割る数」は `p` だけではない

素数段 `p` の内側係数はすべて `p` で割れる。
しかし `1` も当然すべてを割る。

したがって、安全な表現は次である。

```text
素数段 p の内側係数すべてを割る非自明な共通因子は p 由来である
```

まずはこの精密化には踏み込まず、
`p` が必ず割ることと、`d` 自身がすべて割る iff `d` prime を優先する。

### `u` を「係数の 1 の一般化」と見ない

通常 Pascal 行の両端 `1` を `u` に置き換える、という直感は有用だが、
Lean では次のように分ける。

```text
係数: choose d k
項: choose d k * x^k * u^(d-k)
```

`u^d` は係数ではなく、重み付き項の境界値である。

この区別を守ると、可除性補題が壊れにくくなる。

### Zsigmondy へ急がない

Zsigmondy は差冪の primitive prime divisor を扱う。
WeightedBinomial はその前段であり、

```text
二項展開の各項がどの因子を運ぶか
```

を記録するだけに留める。

## 既存 mathlib / DkMath API

利用予定の mathlib 補題:

- `Nat.Prime.dvd_choose_self`
- `Nat.Prime.dvd_choose`
- `Nat.Prime.coprime_choose_of_lt`
- `Nat.choose_zero_right`
- `Nat.choose_self`
- `Nat.choose_eq_zero_of_lt`

将来の valuation 接続候補:

- `padicValNat_choose`
- Kummer/Lucas 系の `Nat.choose` 補題

既存 DkMath 接続候補:

- `DkMath.Lib.Cosmic.GTail`
- `DkMath.Lib.Cosmic.GTailNat`
- `DkMath.Lib.Cosmic.GTailCongruence`
- `DkMath.Lib.Cosmic.GTailPadic`
- `DkMath.CFBRC.Basic`
- `DkMath.CFBRC.Bridge`
- `DkMath.NumberTheory.ZsigmondyCyclotomic`

## 成功条件

この章の成功条件は、次の通り。

1. `d` の素数性を二項係数列の整除性として読める。
2. 重み付き二項項の可除性を、係数由来・x 由来・u 由来に分けて使える。
3. CFBRC/GN へ接続する前段補題として、数値展開ではなく divisibility API を提供できる。
4. Zsigmondy へ進む前に、境界因子と中間係数因子を Lean 上で区別できる。
