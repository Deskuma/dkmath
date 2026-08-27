# Prime Harmony / PHZ / Primorial / GN / Prime Gauge 実装計画

- Status: implementation plan / not implemented
- Date: 2026-08-26
- Branch at recording: `develop`
- Repository: `Deskuma/dkmath`
- Target area: `DkMath.NumberTheory.Primitive`, `DkMath.NumberTheory.Gcd`, `DkMath.CosmicFormula`, future `DkMath.NumberTheory.PrimeHarmony` / RH bridge

## 1. 目的

本資料は、Prime Harmony の原型から始まり、有限 prime world、プリモリアル剰余類の鏡映対称、GN の Boundary / Beam 二チャネル、`x = 1` 正規化、さらに実数スケールへ拡張された Prime Gauge までを、一つの実装予定として整理する。

現在の DkMath には局所的な部品がかなり揃っている。

一方で、次の一本の意味論はまだ theorem family として固定されていない。

```text
有限既知 prime world
  ↓
primorial / product modulus
  ↓
周期的 residue observer
  ↓
鏡映対称な candidate seats
  ↓
新しい prime direction の追加による refinement
  ↓
Cosmic Formula / GN の Boundary-GN 二チャネル
  ↓
x = 1 による Boundary channel の透明化
  ↓
GN integer value の primitive / prime crystallization
  ↓
Prime Harmony observer
  ↓
PHZ log-prime phase observer
```

第一目標は、既存定理を再証明することではなく、これらを橋渡しする最小 API を追加することである。

---

## 2. 用語の原点

### 2.1 Prime Harmony (PH)

Prime Harmony の原型は、既知素数ごとに周期 `p` を持つ cosine wave を置き、それらを合成することで、整数位置と剰余類の対称性を波形として観測する構想である。

基本波の代表形を

$$
W_p(n)=\cos\left(\frac{2\pi n}{p}\right)
$$

とする。

`p ∣ n` なら `W_p(n) = 1` となり、また cosine の偶対称性により

$$
W_p(r)=W_p(p-r)
$$

が成立する。

複数の既知素数 `S` に対して

$$
H_S(n)=\sum_{p\in S}W_p(n)
$$

を観測すると、各 `p` の剰余類構造が重なり、既知素数で割れない位置が soft sieve の candidate seat として現れる。

Prime Harmony は primality を100%判定する装置ではない。

その意味は、

```text
既知 prime directions
  ↓
剰余類の周期・対称性
  ↓
既知 prime に捕まる位置 / 捕まらない位置
  ↓
future-prime admissible seat の可視化
```

である。

### 2.2 PHZ

PHZ は元来、Prime Harmony を zeta-side の位相へ持ち上げ、ゼータ関数の zero-coordinate 観測を狙った派生である。

Euler-product 側の素数項では

$$
p^{-s}=p^{-\sigma}e^{-it\log p}
$$

となるため、実部の prime wave は概念的に

$$
p^{-\sigma}\cos(t\log p)
$$

となる。

したがって PH と PHZ は、同じ prime direction `p` を

```text
PH   : period / residue coordinate p
PHZ  : log-phase coordinate log p
```

で読む二つの observer と位置づける。

**注意:** 現在の `DkMath.NumberTheory.Primitive.PHZ30` は、歴史的 PHZ の zeta / `log p` 意味より広く、`{2,3,5}` finite prime world の candidate-seat classification 名として使用されている。既存 API は壊さないが、将来の命名整理ではこの意味のずれを明記する。

---

## 3. 有限 prime world とプリモリアル周期

有限な既知素数集合を `S` とし、その product modulus を

$$
M_S:=\prod_{p\in S}p
$$

とする。

現在の DkMath では、

```text
DkMath.NumberTheory.Primitive.FinitePrimeWorld
DkMath.NumberTheory.Primitive.PeriodicPrimeWorld
DkMath.NumberTheory.Primitive.PrimeWorldResidues
DkMath.NumberTheory.Primitive.PrimeWorldRefinement
DkMath.NumberTheory.Primitive.PHZ30
```

がこの層を担っている。

`SupportDisjointFrom S n` は、既知 prime directions のどれも `n` を割らないことを表す。

`KnownPrimeScales S` の下では既に

$$
\operatorname{SupportDisjointFrom}(S,n)
\iff
\gcd(n,M_S)=1
$$

が実装されている。

また support state は `M_S` 周期である。

$$
\operatorname{SupportDisjointFrom}(S,n+kM_S)
\iff
\operatorname{SupportDisjointFrom}(S,n)
$$

---

## 4. 鏡映対称性

既知 prime world の residue geometry は、modulus の中心に関して鏡映対称である。

現在 `PeriodicPrimeWorld.lean` には、任意の modulus multiple を中心とする generic mirror theorem が既にある。

概念的には

$$
r\longleftrightarrow M_S-r
$$

であり、

$$
\gcd(r,M_S)=1
\iff
\gcd(M_S-r,M_S)=1
$$

となる。

特に `2 ∈ S` の場合、中心 `M_S/2` 自身は candidate seat ではないため、canonical reduced residues は固定点なしの mirror pair に分かれる。

### 4.1 例: `M = 210`

$$
210=2\cdot3\cdot5\cdot7
$$

であり、

$$
\varphi(210)=48
$$

なので candidate residues は48席、mirror pair は24組となる。

各 pair は

$$
r+(210-r)=210
$$

を満たし、共通中心は

$$
105=\frac{210}{2}
$$

である。

したがって有限 prime world の骨格自体には左右の候補席数の偏りはない。

**重要:** これは candidate seats の対称性であり、actual primes が pair ごとに同時に存在することを主張しない。

Prime distribution の偏りを議論する場合、

```text
symmetric admissible skeleton
+
actual-prime occupation fluctuation
```

を分離する。

---

## 5. Refinement: 新しい prime を追加したときの自己相似成長

旧 world `S` に fresh prime `q` を追加する。

$$
M_{S\cup\{q\}}=qM_S
$$

旧 period representative `r` は、新 world では

$$
r,\quad r+M_S,\quad r+2M_S,\quad\ldots,\quad r+(q-1)M_S
$$

という `q` 個の child を持つ。

現在 `PrimeWorldRefinement.lean` は、fresh `q` に対してこの `q` 個の child のうち **ちょうど1個だけ** が `q`-wave に乗り、残る `q-1` 個が enlarged world の surviving seat になることを既に証明している。

したがって、

$$
\boxed{\text{one old seat}\to q\text{ children}\to q-1\text{ survivors}}
$$

という refinement law が既に Lean 上にある。

### 5.1 `30 → 210`

現在 `PHZ30.lean` には、

```text
primeWorld235 = {2,3,5}
primeWorldModulus primeWorld235 = 30
phzResidues30 = {1,7,11,13,17,19,23,29}
```

があり、8 candidate seats が形式化されている。

さらに fresh direction `7` の追加によって

$$
30\longrightarrow210
$$

となり、各旧 seat が `7-1 = 6` 個の surviving child を持つため、

$$
8\cdot6=48
$$

として `card_phzResidues210 = 48` まで実装済みである。

この recursive refinement を、本資料では Euclidean/Hausdorff 的な厳密フラクタルとは区別し、まず

```text
self-similar primorial residue refinement
```

または

```text
recursive prime-world refinement
```

と呼ぶ。

---

## 6. 観測に採用された prime の singleton anchor

finite world の構成素数 `p ∈ S` は、modulus `M_S` において自分自身の residue class を prime に関して独占する。

新規 theorem 候補:

```lean
theorem prime_eq_of_modEq_worldPrime
    {S : Finset ℕ} {p q : ℕ}
    (hpS : p ∈ S)
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hmod : q ≡ p [MOD primeWorldModulus S]) :
    q = p
```

本質は `p ∣ M_S` と `q ≡ p mod M_S` から `p ∣ q` を得て、`q` の primality で `q = p` とするだけである。

例として mod `30` では、

```text
+2 class : prime は 2 のみ
+3 class : prime は 3 のみ
+5 class : prime は 5 のみ
```

となる。

したがって新しい prime `q` は、発見前には future-prime candidate seat に属し、world に追加された後は自分専用の prime anchor へ昇格する。

```text
unknown / future prime
  ↓
candidate seat
  ↓
prime discovered
  ↓
insert q into finite prime world
  ↓
q becomes singleton prime anchor
  ↓
q is now part of the next observer
```

この **observed object → next observer** の循環を Prime Harmony 成長則の中心とする。

---

## 7. 二つの平方境界を混同しない

今回の議論では宇宙式境界と exact sieve frontier が接近して見えるため、実装では明確に分離する。

### 7.1 Cosmic Formula square window

任意の `P` に対して

$$
P(P+2)+1=(P+1)^2
$$

である。

すなわち

$$
\operatorname{squareBody}(P)=P^2+2P=(P+1)^2-1
$$

となる。

現在 `Primitive/SquareBody.lean` にこの identity と square-Body closure が存在する。

### 7.2 Exact prime certification

`SquareBody.lean` が prime を結論する際に必要なのは、**すべての prime directions `q ≤ P` を除外していること**である。

したがって、例えば product modulus `30 = 2·3·5` だけを observer として用いたからといって、`960 = 31^2-1` まで `gcd(n,30)=1` と primality が一致するわけではない。

実際 `49 = 7^2` は `gcd(49,30)=1` だが composite である。

よって次の二つを別 API とする。

```text
Cosmic square window:
  P(P+2) = (P+1)^2 - 1

Exact finite-prime sieve frontier:
  all primes ≤ P are excluded
  ⇒ points ≤ P(P+2) are prime
```

この分離を維持したうえで、primorial product `M` と Cosmic Formula anchor `P = M` の関係を研究する。

---

## 8. Cosmic Formula / GN の二チャネル

一般差冪は

$$
(x+u)^d-u^d=x\,GN_d(x,u)
$$

と分解される。

ここで

```text
Boundary channel : x
GN / Beam channel: GN_d(x,u)
```

という二つの divisibility channel が現れる。

素数 `q` が Body を割るなら Euclid lemma により

$$
q\mid x
\quad\text{or}\quad
q\mid GN_d(x,u)
$$

となる。

現在 `DkMath.NumberTheory.Gcd.GN` には、適切な coprime 仮定の下で Boundary と GN を coprime にする theorem が既に存在する。

代表例:

```lean
coprime_boundary_GN_of_coprime_add_of_coprime_exp
```

この既存資産を用いて、新しい semantic wrapper を追加する。

候補:

```lean
theorem prime_dvd_boundary_or_GN

theorem prime_dvd_boundary_xor_GN_of_coprime
```

目的は新しい整数論を証明することではなく、`Boundary / GN` 二チャネルとして再公開することである。

---

## 9. `x = 1`: unit Boundary による純粋 GN 観測

`x = 1` とすると

$$
(1+u)^d-u^d=GN_d(1,u)
$$

となり、Boundary channel `x` は乗法単位元 `1` に退化する。

`1` は prime support を持たないため、Body の divisibility information は全て GN 側へ移る。

新規 theorem 候補:

```lean
theorem body_one_eq_GN

theorem prime_dvd_body_one_iff_dvd_GN
```

さらに `GN d 1 u` が自然数 prime `p` へ一致した場合、

$$
(1+u)^d-u^d=1\cdot p
$$

となる。

これは通常の prime の divisor normal form

$$
p=1\cdot p
$$

と一致する。

ここで重要なのは、`x = 1` だから GN が自動的に prime になる、とは主張しないことである。

必要条件は別に

```lean
Nat.Prime (GN d 1 u)
```

として持つ。

---

## 10. Prime Crystal / Prime Gauge の候補概念

### 10.1 Integer Prime Crystal

以下を semantic package として考える。

```text
Boundary = 1
GN       = p
p        is prime
```

候補 structure / predicate:

```lean
structure GNPrimeCrystal (d u : ℕ) where
  value : ℕ
  hvalue : value = GN d 1 u
  hprime : Nat.Prime value
```

ただし初期実装では structure を急がず、theorem family だけで十分である可能性が高い。

### 10.2 Real Prime Gauge / Primitive Gauge

Cosmic Formula は整数に固定されない。

$$
N(x;u,d)=(x+u)^d-u^d
$$

は `x,u ∈ ℝ` でも意味を持つ。

したがって DkMath の研究語彙としては、prime を直接実数へ拡張するのではなく、

> 現在の既知 gauge では表現できない、新しく発生した relative primitive scale

を `PrimitiveGauge` / `PrimeGauge` として定義する方向を検討する。

これは標準数学の prime / irreducible の定義ではない。

実数の乗法モノイド上の通常の「素数」を主張するものでもない。

むしろ、

```text
continuous primitive gauge
  ↓ integer sampling / crystallization
integer primitive candidate
  ↓ factor exclusion
prime
```

という DkMath 独自の observer semantics を与えるための候補概念である。

この層は現段階では **研究仮説 / 定義設計** とし、既実装 theorem と混同しない。

---

## 11. GN → finite prime world → PH の生成・観測ループ

現在の finite prime world は既知 prime directions を入力として residue geometry を作る。

一方 GN 側では primitive prime / fresh prime direction が発生する theorem 群が既に存在する。

今後必要なのは、この二方向を接続する bridge である。

```text
GN / difference-power
  ↓
primitive or fresh prime q
  ↓
insert q into finite prime world
  ↓
primeWorldRefinement
  ↓
new residue geometry
  ↓
Prime Harmony observer
```

候補 theorem / wrapper:

```lean
theorem primitivePrime_insert_primeWorld

theorem freshPrimeDirection_refines_primeWorld
```

これによって

$$
\boxed{\text{GN generates}\quad\leftrightarrow\quad\text{PH observes}}
$$

という往復構造を固定する。

---

## 12. PH の解析 API 候補

整数 residue wave を実数値関数として定義する。

```lean
def primeWave (p : ℕ) (x : ℝ) : ℝ :=
  Real.cos (2 * Real.pi * x / p)
```

型・zero division の都合から、実装時には `p > 0` を theorem 側で要求するか、`Nat.Prime p` を受け取る wrapper にする。

最小 theorem 候補:

```lean
primeWave_add_period
primeWave_neg
primeWave_residue_mirror
primeHarmony_add_period
primeHarmony_mirror
```

有限 world `S` の合成波:

```lean
def primeHarmony (S : Finset ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ S, primeWave p x
```

目的は primality proof ではなく、既存の `SupportDisjointFrom` / `primeWorldResidues` の対称骨格を harmonic visualization へ接続することである。

PH は soft sieve / visualization layer とする。

---

## 13. PHZ log-prime phase bridge

PHZ は PH と分離して、zeta-side に置く。

基本 prime mode:

$$
Z_p(\sigma,t)=p^{-\sigma}\cos(t\log p)
$$

候補:

```lean
def primeZetaWave (p : ℕ) (σ t : ℝ) : ℝ := ...

def primeHarmonyZeta (S : Finset ℕ) (σ t : ℝ) : ℝ := ...
```

ただし、有限 PHZ 合成波の zero / stationary point が Riemann zeta の zero と一致する、とは初期 API では主張しない。

初期実装は次に限定する。

```text
prime p
  ↓
period coordinate p        -- PH
log-phase coordinate log p -- PHZ
```

PHZ と actual zeta zero との bridge は RH 側の独立 research module とする。

---

## 14. 推奨モジュール構成

既存 `Primitive` API を壊さず、まず薄い bridge を追加する。

```text
DkMath/NumberTheory/Primitive/
  PrimeAnchor.lean              -- known prime の singleton residue anchor
  GNPrimeGauge.lean             -- Boundary/GN 二チャネルと x=1
  PrimeWorldGNBridge.lean       -- GN fresh prime → finite world insertion

DkMath/NumberTheory/PrimeHarmony/
  Basic.lean                    -- primeWave / finite harmonic sum
  Periodic.lean                 -- period / residue mirror
  PrimeWorldBridge.lean         -- finite prime worldとの接続

DkMath/NumberTheory/PrimeHarmony.lean

DkMath/RH/...                    -- PHZ log-prime phase は RH 側へ bridge
```

`PHZ30.lean` は既存互換のため当面維持する。

将来的には、原義の PHZ と finite-world candidate-seat API の名称衝突を避けるため、alias / documentation による整理を検討する。

---

## 15. 最小 theorem surface

初回実装では次を候補とする。

### Phase A: Prime anchor

```lean
prime_eq_of_modEq_worldPrime
worldPrime_residue_prime_unique
```

### Phase B: Mirror packaging

既存 `supportDisjointFrom_centered_mirror_iff` を再利用し、canonical residue set 向け wrapper を追加する。

```lean
primeWorldResidues_mirror_mem_iff
primeWorldResidues_pair_sum_modulus
```

必要なら `2 ∈ S` 条件下の half-cardinality を別 checkpoint とする。

### Phase C: Boundary / GN channels

```lean
prime_dvd_boundary_or_GN
prime_dvd_boundary_xor_GN_of_coprime
body_one_eq_GN
prime_dvd_body_one_iff_dvd_GN
```

### Phase D: Prime crystallization wrapper

```lean
GNPrimeCrystal
primeCrystal_factor_normalForm
```

structure が重い場合は theorem のみで開始する。

### Phase E: GN → PrimeWorld bridge

```lean
primitivePrime_insert_primeWorld
freshPrimeDirection_refines_primeWorld
```

### Phase F: Prime Harmony

```lean
primeWave
primeWave_periodic
primeWave_mirror
primeHarmony
primeHarmony_periodic
primeHarmony_mirror
```

### Phase G: PHZ

```lean
primeZetaWave
primeHarmonyZeta
```

zeta-zero bridge は別プロジェクトとする。

---

## 16. 実装 checkpoint 案

### PHG-001: terminology / inventory

- 既存 `PHZ30`, `FinitePrimeWorld`, `PeriodicPrimeWorld`, `PrimeWorldRefinement` の API inventory
- 原義 PH / PHZ を docs で固定
- 名前衝突を記録
- コード変更は最小または無し

### PHG-002: Prime anchor

- known world prime の singleton prime residue theorem
- `30` の `2,3,5` を concrete examples にする

### PHG-003: canonical mirror pairs

- generic mirror theoremを `primeWorldResidues` membership へ transport
- pair sum = modulus
- center = modulus / 2 の geometry wrapper
- actual-prime symmetry は主張しない

### PHG-004: GN two-channel bridge

- Body factorizationを semantic wrapper 化
- prime divisor `Boundary ∨ GN`
- coprime 時 `xor`

### PHG-005: unit Boundary

- `x = 1` で Body = GN
- all prime support lies on GN channel
- prime GN 値なら `1 * p` normal form

### PHG-006: GN → finite prime world

- primitive/fresh prime witness を `insert` へ接続
- `PrimeWorldRefinement` まで一本道にする

### PHG-007: Prime Harmony wave layer

- cosine wave
- period
- mirror
- finite sum
- candidate skeleton visualization theorem

### PHG-008: PHZ log-prime phase

- `log p` mode
- PH prime directionとの bridge
- actual zeta zero identificationは保留

### PHG-009: Real Primitive Gauge reconnaissance

- real `x,u` Cosmic Formula 上で何を `PrimitiveGauge` と定義すべきか調査
- 標準 irreducible / prime と明確に区別
- integer crystallization interface のみ先に設計

---

## 17. 数学的に既に確定しているもの / 未確定なもの

### 17.1 既に Lean 側に強い土台がある

```text
finite prime world
product modulus
support-disjoint ↔ gcd = 1
periodicity
centered mirror symmetry
fresh-prime insertion
exactly one reserved child
q - 1 surviving children
PHZ30 eight residues
30 → 210, 48 residues
SquareBody identity
SquareBody 内の finite-prime exclusion → primality
GN gcd / coprime bridge
primitive prime / GN divisibility bridge
```

### 17.2 新しいが、ほぼ wrapper / packaging で済む候補

```text
known prime singleton residue anchor
canonical mirror pair packaging
Boundary / GN semantic channel theorem
x = 1 pure-GN theorem family
GN prime → factor normal form 1 * p
GN fresh prime → PrimeWorld insertion
```

### 17.3 研究仮説・新定義設計

```text
Prime Gauge / Primitive Gauge over ℝ
continuous primitive germ
integer crystallization as prime
"any small Cosmic Formula growth creates a prime egg" の厳密定義
PH wave score と primality likelihood の定量関係
PHZ finite wave と actual zeta zeros の厳密 bridge
```

これらは既存数学上の prime 定義と混同せず、まず observer / gauge semantics として定義する。

---

## 18. 中心となる研究像

今回の議論の最終像は次である。

```text
Cosmic Formula growth
        ↓
(x+u)^d - u^d = x * GN_d(x,u)
        ↓
Boundary / GN divisibility channels
        ↓
x = 1
        ↓
Boundary support disappears
        ↓
GN carries all nontrivial prime information
        ↓
integer prime crystallization p
        ↓
p becomes a finite-prime-world direction
        ↓
primorial/product-period residue geometry
        ↓
recursive refinement + mirror symmetry
        ↓
Prime Harmony
        ↓
log p phase lift
        ↓
PHZ
```

この見方では、素数を最初から基本対象として置かない。

素数は、より一般の成長構造・primitive scale が整数世界で一意に結晶化した特殊点として読む。

これは現段階では DkMath の研究的解釈であり、標準整数論の prime 定義を置換するものではない。

実装ではまず標準数学上で完全に閉じる有限 theorem family を作り、その上に Gauge / PH / PHZ の observer semantics を薄く載せる。

---

## 19. 実装原則

1. 既存 `Primitive` theorem を再証明しない。
2. `PHZ30.lean` の candidate-seat / no-primality 境界を維持する。
3. actual prime と prime-admissible seat を混同しない。
4. Cosmic square window と exact sieve frontier を混同しない。
5. `x = 1` は GN を prime にする条件ではなく、Boundary support を消す正規化として扱う。
6. Real Prime Gauge は標準的な real prime の主張にしない。
7. PH は harmonic visualization / soft sieve として実装する。
8. PHZ は `log p` phase observer として PH と区別する。
9. actual zeta zero bridge は独立 proof obligation とする。
10. 各 checkpoint は小さくし、既存 API の alias / wrapper を優先する。
11. 新規 `sorry` / axiom は追加しない。
12. theorem statement と研究解釈を docs 上でも明確に分離する。

---

## 20. 最終目標

最終的に次の三層を一つの依存方向へ整理する。

```text
Layer 1: exact finite arithmetic
  FinitePrimeWorld
  PeriodicPrimeWorld
  PrimeWorldRefinement
  GN gcd / divisibility
  SquareBody

Layer 2: DkMath semantic bridges
  Boundary / GN channels
  unit Boundary
  prime crystallization
  recursive prime-world growth

Layer 3: harmonic observers
  Prime Harmony
  PHZ
  future Real Primitive Gauge / RH bridge
```

中心原理を一文でまとめる。

> 既知 prime directions は有限周期・鏡映対称な admissible geometry を作る。新しい prime はその geometry の candidate として観測され、確定後は次世代 observer の方向へ昇格する。一方 Cosmic Formula / GN は新しい divisibility direction を生成する側を担い、`x = 1` では Boundary channel が単位へ退化して GN の prime information が純化される。Prime Harmony はこの離散 prime-world geometry を波として読み、PHZ は同じ prime directions を `log p` 位相へ持ち上げる。
