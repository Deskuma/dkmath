# BinomialPrime / WeightedBinomial 実装ロードマップ

## 目的

二項定理の係数列から、次数 `d` の素数性と可除性の構造を取り出す。

本ロードマップの目的は、展望を広げすぎず、確実に Lean 化できる補題から順に
`DkMath` の既存構造へ接続することである。

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
- `←` 方向は既存 mathlib 補題の有無を調査し、なければ最小証明を作る。
- 無理に gcd API へ進まない。まず iff を完成させる。

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
- 逆方向の実装可能性を調査し、可能なら `prime_iff` を閉じる。

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

