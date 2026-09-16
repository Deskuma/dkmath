# Prime Gauge / Cosmic Inversion Projection / Twin Prime Harmony 実装設計

- Status: implementation design / not implemented
- Date: 2026-08-30
- Branch at recording: `develop`
- Repository: `Deskuma/dkmath`
- Resume point: Wallis / Pascal cell-growth completion + StructuralArithmetic A-I completion
- Predecessor design: `docs/not_implements/260826-Prime-Harmony-PHZ-GN-PrimeGauge-ImplementationPlan.md`
- Historical projection design: `docs/not_implements/宇宙式の反転射影-260708.md`

---

## 0. この文書の役割

本資料は、DkMath における次の再開地点を固定するための実装設計である。

```text
Wallis / Pascal Cell Growth 完成
        ↓
StructuralArithmetic A-I 完成
        ↓
Generic GN / fresh prime direction / real radial scaling
        ↓
Prime Gauge
        ↓
Cosmic Inversion Projection
        ↓
continuous no-hole
        ↓
discrete prime-cell realization
        ↓
Prime Harmony
        ↓
Twin Prime Harmony
```

目的は、双子素数予想や素数分布の未解決命題をいきなり主張することではない。

まず、既に Lean で認証済みの有限 prime-world / GN / primitive-direction / real-scaling 部品を、

1. `PrimeGauge`
2. 反転射影
3. 離散整数への結晶化
4. Prime Harmony observer
5. Twin Prime Harmony observer

へ接続するための theorem family を構築する。

この文書を、今後この研究路線を再開する際の **入口 marker** とする。

---

# 1. 現在地

## 1.1 `develop` の直近完成地点

Wallis / Pascal 側では、少なくとも次の公開層まで到達している。

```text
DkMath.Pascal.WallisCosmicPetalBridge
DkMath.Pascal.WallisLimitBridge
DkMath.Pascal.WallisGrowthBridge
DkMath.Pascal.WallisCellGrowth
```

`WallisCellGrowth` は、有限 Cosmic product から central Pascal cell を exact に読み出し、Wallis の有限上下界、remainder、低演算近似、even/odd row を含む cell-growth API へ接続している。

したがって本研究路線は、Wallis の続きとしてではなく、**NumberTheory / StructuralArithmetic 側の新しい独立 phase** として開始する。

## 1.2 StructuralArithmetic は再利用する

現在の public aggregator:

```lean
import DkMath.NumberTheory.StructuralArithmetic
```

は、少なくとも次を公開している。

```text
PowerGauge
PrimeCoordinates
InterPeriod
KUSObservation
PrimitiveDirection
FinitePrimeEscapeBridge
GNBridge
GoldenUnitBridge
RadialScaling
CosmicSquareScaling
```

重要なのは、generic GN を新たに再定義しないことである。

既存の canonical / public GN を使用する。

概念的には

$$
(x+u)^d-u^d=x\,GN_d(x,u)
$$

である。

`StructuralArithmetic.GNBridge` は既に、primitive-prime witness から generic GN の `FreshPrimeDirection` を得る橋を持つ。

また FLT5 専用 `GN5` と generic degree-five GN の exact identity も既に theorem-level で接続されている。

したがって、本計画では **GN5 ハッカソン実装を再起点にしない**。

---

# 2. 既実装・未実装・研究仮説を分離する

本路線では次の三層を混同しない。

## 2.1 既実装として利用する層

```text
finite prime-world support
periodicity / residue observer
mirror symmetry
prime-world refinement
fresh prime direction
primitive prime → GN divisibility
GN5 = generic GN at degree 5
real radial scaling
Cosmic-square dynamic scaling
```

これらは provider として消費する。

## 2.2 新規に Lean 実装すべき層

```text
Boundary / GN semantic two-channel API
x = 1 unit-boundary normalization
PrimeGauge integer interface
Cosmic inversion projection
projection no-hole primitives
PrimeGauge ↔ Nat.Prime crystallization bridge
Prime Harmony exact arithmetic observer
Twin Prime Harmony finite refinement
```

## 2.3 研究仮説として隔離する層

次は現時点で theorem として仮定しない。

```text
continuous no-hole alone implies existence of integer primes
PrimeGauge on arbitrary real values is ordinary ring-theoretic primality
every Twin-safe residue class contains a twin prime
Twin Prime Harmony proves infinitely many twin primes
PHZ zero-coordinate interpretation follows automatically from PH
```

特に、実数上の `PrimeGauge` は「実数の素数」を定義するものではない。

目標は、**連続成長の primitive direction と、その整数格子上の prime crystallization を分離して扱うこと**である。

---

# 3. Phase PG-0 — Boundary / GN 二チャネル

一般 GN identity:

$$
(x+u)^d-u^d=x\,GN_d(x,u)
$$

に対して、prime divisor `q` は積のどちらかの channel に属する。

候補 theorem surface:

```lean
theorem prime_dvd_boundary_or_GN

theorem prime_dvd_boundary_xor_GN_of_coprime

theorem boundary_GN_coprime_of_existing_GN_gcd_hypotheses
```

実装方針:

- `Nat.Prime.dvd_mul` / Euclid lemma を再利用する。
- `DkMath.NumberTheory.Gcd.GN` の既存 coprime theorem を consumer として使う。
- 新しい gcd 理論は作らない。
- 目的は「Boundary channel / GN channel」という semantic wrapper を theorem family として固定すること。

中心読み:

```text
Body prime support
   ├─ Boundary x
   └─ GN_d(x,u)
```

coprime 条件下では両 channel は排他的になる。

---

# 4. Phase PG-1 — `x = 1` Unit-Boundary normalization

`x = 1` とすると Boundary の prime-support 情報が消える。

$$
(1+u)^d-u^d=GN_d(1,u)
$$

候補 theorem:

```lean
theorem body_one_eq_GN

theorem prime_dvd_body_one_iff_dvd_GN

theorem boundary_one_has_no_prime_support
```

この phase の数学的意味は、

```text
Boundary = 1
GN       = all nontrivial multiplicative information
```

という純粋 GN probe を作ることにある。

Mersenne case

$$
GN_d(1,1)=2^d-1
$$

は example として使用できるが、Mersenne-specific theory を本体にはしない。

---

# 5. Phase PG-2 — Prime Gauge 最小定義

ここで初めて `PrimeGauge` を定義する。

ただし、通常の `Nat.Prime` を別名で包むだけにはしない。

目標は **既知有限 prime world に対する relative primitive direction** と **整数 prime crystallization** を分けることである。

候補構造:

```lean
structure PrimeGaugeWitness (S : Finset ℕ) (n : ℕ) where
  q : ℕ
  prime_q : Nat.Prime q
  divides_target : q ∣ n
  fresh : q ∉ S
```

ただし既存 `FreshPrimeDirection` と重複するなら新 structure は作らず alias / theorem wrapper に留める。

重要なのは、新しい概念を増やすことではなく、次の意味論を theorem-level で固定すること。

```text
finite known prime world S
        ↓
GN / other growth target n
        ↓
fresh primitive direction q
        ↓
q is a new scale relative to S
```

この phase では **real-valued prime factorization は導入しない**。

---

# 6. Phase PG-3 — Integer crystallization

Prime Gauge と通常の prime を接続する最小 bridge を作る。

ここでは二種類を分ける。

## 6.1 relative primitive witness

これは既知 finite world に対する freshness であり、target 自身が prime であることを意味しない。

## 6.2 prime crystal

Boundary を `1` に正規化した GN target が整数であり、その target 自身が prime である場合、

$$
N=1\cdot p
$$

という通常 prime の最小乗法形を得る。

候補 theorem:

```lean
theorem primeCrystal_of_GN_prime
    (hp : Nat.Prime (GN d 1 u)) : ...
```

またはより汎用に、

```lean
def IsPrimeCrystal (n : ℕ) : Prop := Nat.Prime n
```

と単純化し、DkMath 的意味論を theorem 名側で与える。

ここで重要なのは、

```text
continuous/generic primitive gauge
        ↓ integer realization
Nat.Prime
```

という橋の **integer side** を先に閉じること。

continuous side は後続 phase で扱う。

---

# 7. Phase CP-0 — Cosmic Inversion Projection

歴史的設計 `宇宙式の反転射影-260708.md` を、Collatz 専用ではなく独立 API として再開する。

基本定義:

$$
\Pi(P)=-\frac{P}{P+1}
$$

および gap coordinate:

$$
u(P)=\frac{1}{P+1}
$$

関係:

$$
\Pi(P)+1=u(P)
$$

候補 module:

```text
DkMath/CosmicFormula/Projection/Basic.lean
DkMath/CosmicFormula/Projection/Inverse.lean
```

候補 theorem:

```lean
cosmicProjection_mem_Icc
cosmicProjection_strictMono_or_Anti
cosmicProjection_injective
cosmicProjection_inverse
cosmicProjection_surjective_openClosed
cosmicGap_mem_unitInterval
cosmicProjection_gap_eq
```

実装時には endpoint convention を一つに固定する。

```text
P ∈ [0,∞)
Pi(P) ∈ (-1,0]
```

または gap coordinate なら

```text
u(P) ∈ (0,1]
```

とする。

`P = ∞` を実数値として直接入れず、`P → ∞` と endpoint limit を分けて形式化する。

---

# 8. Phase CP-1 — compactification / no-hole primitives

反転射影そのものの全射性は、prime の存在を意味しない。

この phase では、まず純粋な位相・順序・区間 theorem として no-hole を固定する。

候補:

```lean
projection_preimage_nonempty
projection_image_interval
projection_image_no_order_hole
hole_transports_back_under_bijection
```

目標は、

```text
unbounded positive scale
        ↓ inversion projection
bounded interval
```

を厳密化すること。

ここでの `no-hole` は **real interval の欠損がない** という意味であり、

```text
all integer cells are occupied
all prime seats are occupied
```

とは別である。

この semantic boundary を docstring に明記する。

---

# 9. Phase CP-2 — `discrete_cell_realization`

歴史的反転射影設計で未解決の中心 bridge。

名前候補:

```lean
discreteCellRealization
primeCellRealization
```

この phase は最初から強い theorem を置かず、以下の段階に分解する。

## 9.1 cell map

実数 interval 上の cell と整数 / residue cell の対応を定義する。

## 9.2 finite realization

有限 observation window に対し、projection image の cell が元の finite discrete object と対応する条件を定義する。

## 9.3 prime realization

PrimeGauge witness を持つ discrete cell が、どの追加条件のもとで `Nat.Prime` へ結晶化するかを theorem とする。

**この phase が研究上の最重要 frontier である。**

`continuous no-hole → prime existence` を直接証明しようとせず、必要条件をすべて theorem assumption として露出させる。

---

# 10. Phase PH-0 — Prime Harmony arithmetic observer

波形を先に定義するのではなく、exact arithmetic predicate を正本とする。

有限 known-prime set `S` に対し、

```lean
def PrimeSeatSafe (S : Finset ℕ) (n : ℕ) : Prop :=
  ∀ p ∈ S, ¬ p ∣ n
```

または既存 `SupportDisjointFrom` をそのまま使用する。

その後に cosine observer を追加する。

概念的には

$$
W_p(x)=\cos\left(\frac{2\pi x}{p}\right)
$$

整数 `x` について

$$
W_p(x)=1\iff p\mid x
$$

を bridge theorem とする。

候補 module:

```text
DkMath/NumberTheory/PrimeHarmony/Arithmetic.lean
DkMath/NumberTheory/PrimeHarmony/Wave.lean
DkMath/NumberTheory/PrimeHarmony/Symmetry.lean
```

波形は soft observer であり、primality oracle とはしない。

---

# 11. Phase TPH-0 — Twin Prime Harmony finite structure

ここから twin-specific layer。

中心 `c` に対する pair を

$$
(c-1,c+1)
$$

とする。

既知 prime `p` が pair を kill する条件は

$$
p\mid c-1\quad\text{or}\quad p\mid c+1.
$$

中心 residue では

$$
c\equiv\pm1\pmod p
$$

が forbidden seat となる。

候補 definition:

```lean
def TwinKilledBy (p c : ℕ) : Prop :=
  p ∣ c - 1 ∨ p ∣ c + 1

def TwinSafeFrom (S : Finset ℕ) (c : ℕ) : Prop :=
  ∀ p ∈ S, ¬ TwinKilledBy p c
```

Nat subtraction endpoint が煩雑なら `ℤ` center を使うか、`1 ≤ c` を structure invariant とする。

---

# 12. Phase TPH-1 — `6k ± 1` 最小 boundary

`2,3` を既知世界とすると、3より大きい twin prime pair の center は `6` の倍数になる。

候補 theorem:

```lean
twinSafe_two_three_iff_six_dvd_center
```

意味:

```text
center c = 6k
left  = 6k - 1
right = 6k + 1
```

この phase では `(3,5)` の small exceptional pair を別扱いにする。

---

# 13. Phase TPH-2 — primorial refinement `q → q - 2`

通常 prime-world refinement では、fresh prime `q` の追加により、旧 seat の `q` children のうち1席が kill され、`q-1` が survive する。

Twin world では forbidden center residue が `+1,-1` の2席ある。

したがって奇 prime `q > 2` に対して、

$$
\boxed{q\text{ children}\to q-2\text{ survivors}}
$$

を証明する。

候補 theorem:

```lean
twinRefinement_exactly_two_killed

twinRefinement_survivor_card_eq_q_sub_two

twinRefinement_reflection_preserved
```

既存 `PrimeWorldRefinement` の child/lift API を可能な限り再利用する。

独立した second wheel implementation を作らない。

---

# 14. Phase TPH-3 — finite Twin-safe zone density

有限 primorial world における center survival ratio を exact finite product として定義する。

各奇 prime `p` に対する local survival factor:

$$
1-\frac{2}{p}=\frac{p-2}{p}.
$$

候補 finite theorem:

$$
\operatorname{TwinSafeDensity}(S)
=
\prod_{p\in S,\ p>2}\frac{p-2}{p}
$$

ただし Lean では cardinal identity を正本にする。

```text
number of surviving center classes
=
product of (p - 2)
```

modulus side:

```text
number of all center residue combinations
=
product of p
```

この quotient を `ℚ` / `ℝ` へ transport して density とする。

---

# 15. Phase TPH-4 — Hardy–Littlewood local factor bridge

これは証明済み古典予想を主張する phase ではない。

finite local correction identity として、各 `p > 2` について

$$
\frac{1-2/p}{(1-1/p)^2}
=
1-\frac{1}{(p-1)^2}
$$

を証明する。

候補 theorem:

```lean
twinLocalCorrection_eq
```

有限 product 版:

```lean
twinFiniteCorrectionProduct_eq
```

ここまでなら純粋有限代数であり、Twin Prime Conjecture を仮定しない。

無限積 `C₂` への極限接続は別 phase とする。

---

# 16. Phase TPH-5 — Paired crystallization frontier

双子素数予想へ進む場合の本丸は、candidate-seat geometry ではなく occupation である。

必要となる概念的 bridge:

```text
Twin-safe continuous / projected cell
        ↓
left primitive gauge
right primitive gauge
        ↓
simultaneous integer realization
        ↓
Nat.Prime (c - 1)
Nat.Prime (c + 1)
```

候補 contract:

```lean
structure TwinPrimeCrystallizationContract ... where
  left_prime  : Nat.Prime (c - 1)
  right_prime : Nat.Prime (c + 1)
```

ただし、初期実装では theorem assumption / contract として置き、未証明の核心を隠さない。

この contract を無条件化できたとき初めて、Twin Prime Conjecture への本格的な closure を議論する。

---

# 17. PHZ は後段に置く

歴史的 PHZ は、Prime Harmony の prime direction を zeta-side の log phase へ持ち上げる observer である。

$$
p^{-s}=p^{-\sigma}e^{-it\log p}
$$

したがって phase は `log p` を使う。

本設計では PHZ を Twin / PrimeGauge の証明依存にしない。

```text
Prime direction p
   ├─ PH  : residue / period p
   └─ PHZ : log-phase log p
```

として observer layer に留める。

`DkMath.NumberTheory.Primitive.PHZ30` の既存命名は壊さない。

---

# 18. 推奨 module 構成

候補:

```text
DkMath/NumberTheory/PrimeGauge/
  BoundaryGN.lean
  UnitBoundary.lean
  Crystal.lean

DkMath/CosmicFormula/Projection/
  Basic.lean
  Inverse.lean
  NoHole.lean
  DiscreteCell.lean

DkMath/NumberTheory/PrimeHarmony/
  Arithmetic.lean
  Wave.lean
  Symmetry.lean

DkMath/NumberTheory/PrimeHarmony/Twin/
  Basic.lean
  SixBoundary.lean
  Refinement.lean
  Symmetry.lean
  Density.lean
  LocalCorrection.lean
  CrystallizationContract.lean
```

aggregator 候補:

```text
DkMath/NumberTheory/PrimeGauge.lean
DkMath/CosmicFormula/Projection.lean
DkMath/NumberTheory/PrimeHarmony.lean
```

既存 namespace と衝突する場合は、実装開始時に repository-first で調整する。

---

# 19. checkpoint 案

最初から大規模 campaign にしない。

```text
PGCP-000  reconnaissance / existing theorem inventory
PGCP-001  Boundary-GN two-channel wrappers
PGCP-002  x=1 unit-boundary normalization
PGCP-003  PrimeCrystal minimal API
PGCP-004  CosmicProjection Basic
PGCP-005  CosmicProjection inverse / interval image
PGCP-006  no-hole primitives
PGCP-007  discrete-cell contract skeleton
PGCP-008  PrimeHarmony arithmetic observer
PGCP-009  PH cosine divisibility bridge
PGCP-010  Twin basic / six-boundary
PGCP-011  Twin q→q-2 refinement
PGCP-012  Twin reflection symmetry
PGCP-013  finite density / product cardinality
PGCP-014  finite Hardy–Littlewood local correction
PGCP-015  crystallization frontier audit
```

`PGCP-007` と `PGCP-015` は research frontier とし、未証明 contract を theorem と誤認しない。

---

# 20. 最初の実装で絶対に避けること

1. `GN` を再定義しない。
2. `FreshPrimeDirection` と同じ意味の structure を不用意に増やさない。
3. 実数の通常 prime factorization を導入しない。
4. 反転射影の区間全射性だけから prime existence を結論しない。
5. candidate-seat symmetry から actual prime symmetry を結論しない。
6. finite Twin-safe density から twin-prime infinitude を結論しない。
7. Hardy–Littlewood asymptotic を finite local product identity と混同しない。
8. `PHZ30` の既存 API を歴史的 PHZ の意味へ破壊的 rename しない。
9. Collatz 用の旧反転射影設計へ依存しすぎない。Projection core は独立 API とする。
10. Wallis / Pascal completed layer をこの campaign へ巻き込まない。

---

# 21. 最終到達図

本路線の理想的な到達図は次である。

```text
Generic Cosmic Formula / GN
        ↓
Boundary / GN divisibility channels
        ↓
x = 1 unit-boundary normalization
        ↓
finite-world fresh primitive direction
        ↓
Prime Gauge
        ↓
integer prime crystallization
        ↓
Prime Harmony arithmetic + wave observer
        ↓
primorial recursive refinement
        ↓
Cosmic Inversion Projection
        ↓
continuous compactified no-hole
        ↓
discrete-cell realization
        ↓
paired ±1 realization
        ↓
Twin Prime Harmony occupation problem
```

有限 residue geometry、prime-wave exclusion、`q → q-2` refinement、finite density は比較的早い段階で Lean に固定できる見込みがある。

一方、

```text
continuous no-hole
→ discrete prime realization
```

および

```text
Twin-safe cell
→ simultaneous twin-prime occupation
```

は本研究路線の核心 frontier である。

---

# 22. 再開時の最初の一手

次回この路線を再開するときは、まず `develop` の最新正本を確認した後、次を読む。

```text
DkMath/NumberTheory/StructuralArithmetic.lean
DkMath/NumberTheory/StructuralArithmetic/GNBridge.lean
DkMath/NumberTheory/StructuralArithmetic/PrimitiveDirection.lean
DkMath/NumberTheory/StructuralArithmetic/FinitePrimeEscapeBridge.lean
DkMath/NumberTheory/Gcd/GN.lean
DkMath/NumberTheory/Primitive/PrimeWorldRefinement.lean
DkMath/NumberTheory/Primitive/PeriodicPrimeWorld.lean
DkMath/NumberTheory/Primitive/PHZ30.lean

docs/not_implements/260826-Prime-Harmony-PHZ-GN-PrimeGauge-ImplementationPlan.md
docs/not_implements/宇宙式の反転射影-260708.md
```

その上で **PGCP-000 reconnaissance** から開始する。

最初の coding target は、反転射影ではなく

```text
Boundary / GN two-channel
        ↓
x = 1 unit-boundary
        ↓
PrimeCrystal minimal API
```

とする。

この三つを閉じてから `CosmicProjection` を実装する。

---

## まとめ

DkMath は既に、

```text
GN
finite prime escape
primitive direction
prime coordinates
real radial scaling
```

まで実装済みである。

ハッカソン時に届かなかった反転射影を再開するために、現在不足しているのは **新しい GN ではなく、Prime Gauge と離散結晶化の意味論** である。

Prime Harmony / Twin Prime Harmony は、その上に乗る finite arithmetic observer とする。

この文書を、Wallis / Pascal cell-growth 完了後に開始する次の研究 campaign の正式な入口とする。
