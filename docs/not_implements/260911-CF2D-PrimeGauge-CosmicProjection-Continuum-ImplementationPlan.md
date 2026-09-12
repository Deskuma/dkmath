# CF2D / Prime Gauge / Primorial / Cosmic Projection / Continuum 実装計画

- Status: implementation plan / not implemented
- Date: 2026-09-11
- Branch at recording: `docs/cf2d-prime-gauge-projection-260911-v0`
- Base branch: `develop`
- Repository: `Deskuma/dkmath`
- Related plans:
  - `docs/not_implements/260901-実装可能定理候補-実装順調査.md`
  - `docs/not_implements/260826-Prime-Harmony-PHZ-GN-PrimeGauge-ImplementationPlan.md`
  - `docs/not_implements/260830-PrimeGauge-CosmicProjection-TwinPrimeHarmony-ImplementationDesign.md`
  - `docs/not_implements/宇宙式の反転射影-260708.md`

---

## 0. この文書の目的

本資料は、これまで別々の未実装案件として記録されていた

```text
CF2D finite rotation / exact order
Prime Gauge
Primorial / finite prime-world synchronization
Cosmic Inversion Projection
CRT / residue phase observer
continuous completion / no-hole
```

を、一つの実装幹へ統合するための計画である。

今回新しく得た中心視座は次である。

```text
CF2D は「円を描かずに有限回転を表す」既実装 provider である。
Prime Gauge は、その有限回転の周期を整数可除性として観測する層にできる。
Primorial は、複数 prime gauge の最小同時帰還周期として読める。
Cosmic Projection の gap 1/(P+1) は、P = k - 1 と置くと CF2D の normalized cycle step 1/k と一致する。
```

したがって新しい幹は、概念的に

```text
CF2D exact finite orbit
        ↓
return ⇔ divisibility
        ↓
prime-period gauge
        ↓
finite prime-family synchronization
        ↓
primorial / CRT phase coordinates
        ↓
Cosmic Projection gap bridge
        ↓
mesh → 0 / continuum completion
```

とする。

重要なのは、**continuous no-hole から prime existence を結論しない**ことである。
この計画の初期実装は、既存の exact algebraic / finite arithmetic theorem を接続することに限定する。

---

## 1. 2026-09-01 候補文書との照合結果

`260901-実装可能定理候補-実装順調査.md` には、以下は既に現れている。

- Boundary / GN 二チャネル
- unit Boundary
- 整数側 Prime Gauge
- Cosmic Projection の後段利用
- continuous no-hole を prime existence と混同しない停止条件

また `260830-PrimeGauge-CosmicProjection-TwinPrimeHarmony-ImplementationDesign.md` には、

- Prime Gauge
- Cosmic Inversion Projection
- `discreteCellRealization`
- Prime Harmony の周期波 `cos(2πn/p)`

が記録されている。

一方、今回の中心である次の橋は、既存候補文書では theorem family として明示されていない。

1. `CF2D.regularKernel k` の exact order を、`k ∣ n` と return event の同値へ変換すること。
2. 素数 `p` を prime-order gauge として読むこと。
3. 異なる素数 gauge の帰還排他性を可除性から得ること。
4. 有限 prime family の同時帰還を product modulus / primorial に接続すること。
5. Cosmic Projection の gap と `CF2D.regularPhaseStep` を
   `U(k - 1) = 1/k` で直接同一視すること。
6. Primorial refinement の mesh `1/Q` と、projection boundary gap `Pi(Q-1)+1` を同一の量として扱うこと。
7. この mesh が 0 に近づくことを、prime existence とは独立な continuum approximation として切り出すこと。

よって本資料は、旧計画を置き換えるものではなく、**既存計画間に欠けていた CF2D 軸を追加する統合 bridge 計画**と位置づける。

---

## 2. 既実装 provider

### 2.1 CF2D

現在の `develop` には既に次がある。

```text
DkMath.CosmicFormula.Rotation.CF2D.Basic
DkMath.CosmicFormula.Rotation.CF2D.KernelPower
DkMath.CosmicFormula.Rotation.CF2D.CycleDivision
DkMath.CosmicFormula.Rotation.CF2D.RegularOrbit
DkMath.CosmicFormula.Rotation.CF2D.EuclideanRegularOrbit
```

特に再利用する theorem / definition は次である。

```lean
regularPhaseStep
regularKernel
regularPhaseStep_nsmul_eq_one
regularKernel_pow_eq_one
regularKernel_exactOrder
orderOf_regularKernel
regularKernel_iterate_act_eq_id
regularVertex
regularVertex_injective
regularVertex_ncard_range
```

中心事実は、正の `k` について

$$
\operatorname{orderOf}(\operatorname{regularKernel}(k))=k.
$$

したがって、円・角・多角形を新規定義せず、有限周期構造をそのまま使える。

### 2.2 finite prime world / product modulus

既存の

```text
FinitePrimeWorld
PeriodicPrimeWorld
PrimeWorldResidues
PrimeWorldRefinement
PHZ30
```

を再利用する。

既知 prime set `S` の product modulus は、新しい primorial 定義を重複して作らず、可能な限り既存 `primeWorldModulus S` を使う。

### 2.3 Cosmic Projection prototype

`DkMath/Samples/Projection.lean` には試作として

```lean
def Pi (P : ℝ) : ℝ := -P / (P + 1)
def U  (P : ℝ) : ℝ := 1 / (P + 1)

cosmicProjection_gap_eq
cosmicProjection_mem_interval
```

がある。

これは正式 API ではないため、実装時には `Samples` を provider として import せず、必要な定義・定理を `DkMath.CosmicFormula.Projection` へ回収する。

---

## 3. 中心数学

### 3.1 CF2D return と可除性

正の `k` に対して、`regularKernel k` は exact order `k` を持つ。
従って任意の `n` について

$$
(\operatorname{regularKernel}(k))^n=1
\iff
k\mid n.
$$

これは今回の最重要 bridge である。

候補 theorem:

```lean
theorem regularKernel_pow_eq_one_iff_dvd
    {k n : ℕ} (hk : 0 < k) :
    regularKernel k ^ n = 1 ↔ k ∣ n
```

証明は `orderOf_regularKernel hk` と Mathlib の `orderOf_dvd_iff_pow_eq_one` を使う薄い wrapper とする。

この theorem により、

```text
CF2D kernel return
        ⇕
integer divisibility
```

が kernel-checked に固定される。

### 3.2 Prime Gauge

`p` が素数であるとき、`regularKernel p` を prime-period gauge と読む。

ここで注意する。

`regularKernel k` が最初に `k` で帰還すること自体は、合成数 `k` に対しても成立する。
素数性の意味は「first return」だけではなく、周期群の位数 `p` が素数であり、非自明な proper divisor / subgroup decomposition を持たない点にある。

初期実装では新しい大きな structure を作らず、semantic theorem wrapper に留める。

候補:

```lean
def IsPrimePeriodGauge (r : UnitKernel ℝ) : Prop :=
  Nat.Prime (orderOf r)

 theorem regularKernel_isPrimePeriodGauge
    {p : ℕ} (hp : Nat.Prime p) :
    IsPrimePeriodGauge (regularKernel p)
```

ただしこの定義が単なる `Nat.Prime (orderOf r)` の別名に過ぎず API 価値が小さい場合、定義自体は作らず theorem 名と docstring のみに意味論を置く。

### 3.3 異なる prime gauge の帰還排他性

異なる素数 `p ≠ q` に対して

$$
(\operatorname{regularKernel}(q))^p\ne1.
$$

候補:

```lean
theorem distinct_prime_regularKernel_not_return
    {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    regularKernel q ^ p ≠ 1
```

証明方針:

```text
return at p
→ q ∣ p
→ prime divisor of prime
→ q = p
→ contradiction
```

これは Prime Harmony の `p ∣ n ↔ phase return` を、cosine observer より前の exact algebraic layer で固定する。

---

## 4. 有限 prime family と Primorial synchronization

有限 prime set `S` を考える。

各 `p ∈ S` に対し gauge `regularKernel p` を置く。

同時帰還条件は

$$
\forall p\in S,\quad (\operatorname{regularKernel}(p))^n=1.
$$

各 return を可除性へ変換すれば

$$
\forall p\in S,\quad p\mid n.
$$

`S` が prime set なら pairwise coprime なので、これは product modulus

$$
M_S=\prod_{p\in S}p
$$

について

$$
M_S\mid n
$$

と同値になる。

中心 theorem 候補:

```lean
theorem all_primeGauge_return_iff_worldModulus_dvd
    (S : Finset ℕ)
    (hS : KnownPrimeScales S)
    (n : ℕ) :
    (∀ p ∈ S, regularKernel p ^ n = 1) ↔
      primeWorldModulus S ∣ n
```

さらに正の同期点について、最小同期周期を得る。

```lean
theorem primeGauge_worldModulus_is_first_positive_sync
```

意味:

$$
0<n\land\bigl(\forall p\in S, r_p^n=1\bigr)
\Longrightarrow
M_S\le n,
$$

かつ `n = M_S` では全 gauge が帰還する。

この結果により primorial / product modulus は

> finite prime-family の最小同時帰還周期

として CF2D semantics を持つ。

**非目標:** 初期 phase では、全 kernel の積 `∏ regularKernel p` の `orderOf` が product modulus に等しいことは要求しない。family synchronization と product-kernel order を混同しない。

---

## 5. CRT phase observer

同時帰還だけでなく、各 gauge の途中位相を整数剰余として観測する。

算術側の基本 observer は

$$
n\mapsto n\bmod p.
$$

必要なら `ZMod p` を使う。

有限 `S` では CRT により

$$
\mathbb Z/M_S\mathbb Z
\simeq
\prod_{p\in S}\mathbb Z/p\mathbb Z.
$$

これを

```text
one product-modulus phase
        ⇕ CRT
vector of prime-gauge phases
```

として読む。

候補 module:

```text
DkMath/NumberTheory/PrimeGauge/CRTPhase.lean
```

候補 theorem family:

```lean
primeGaugePhase_eq_zero_iff_dvd
primeGaugePhaseVector
primeGaugePhaseVector_eq_iff_mod_worldModulus
primeGaugePhaseVector_injective_mod_worldModulus
```

既存 finite prime-world API が同値内容を既に持つ場合は、新 theorem を増やさず bridge / alias / docstring に留める。

---

## 6. Cosmic Projection と CF2D の直接 bridge

Cosmic Projection を

$$
\Pi(P)=-\frac{P}{P+1},
\qquad
U(P)=\frac1{P+1}
$$

とする。

CF2D の normalized cycle step は

$$
\operatorname{regularPhaseStep}(k)=\frac1k.
$$

そこで

$$
P=k-1
$$

と置くと

$$
U(k-1)=\frac1k
=\operatorname{regularPhaseStep}(k).
$$

さらに

$$
\Pi(P)+1=U(P)
$$

より

$$
\boxed{
\Pi(k-1)+1
=U(k-1)
=\operatorname{regularPhaseStep}(k)
=\frac1k
}.
$$

これを本計画の第二中心 bridge とする。

候補 theorem:

```lean
theorem projectionGap_eq_regularPhaseStep
    {k : ℕ} (hk : 0 < k) :
    Projection.U ((k : ℝ) - 1) = regularPhaseStep k

 theorem projection_add_one_eq_regularPhaseStep
    {k : ℕ} (hk : 0 < k) :
    Projection.Pi ((k : ℝ) - 1) + 1 = regularPhaseStep k

 theorem projection_eq_regularPhaseStep_sub_one
    {k : ℕ} (hk : 0 < k) :
    Projection.Pi ((k : ℝ) - 1) = regularPhaseStep k - 1
```

この bridge の意味は、

```text
CF2D side       : cycle resolution / step size
Projection side : distance from compactified boundary -1
```

が同じ数 `1/k` で測られることである。

---

## 7. Primorial refinement と projection boundary

finite prime world の product modulus `M_S` に対して

$$
\Delta_S:=\frac1{M_S}
$$

を mesh / gauge resolution と読む。

Projection bridge により

$$
\Delta_S
=
U(M_S-1)
=
\Pi(M_S-1)+1.
$$

特に primorial chain

$$
2,6,30,210,\ldots
$$

では

$$
\frac12,\frac16,\frac1{30},\frac1{210},\ldots
$$

が CF2D/prime-world の解像度であり、Projection 上では

$$
-\frac12,-\frac56,-\frac{29}{30},-\frac{209}{210},\ldots
$$

として境界 `-1` に接近する。

候補 theorem:

```lean
theorem worldModulus_projection_gap

theorem worldModulus_projection_add_one
```

新しい素数 `q` を追加し

$$
M' = qM
$$

となる refinement に対して

$$
\Delta' = \frac{\Delta}{q}
$$

も fixed theorem とする候補がある。

```lean
theorem freshPrime_refinement_mesh
```

これは既存 `PrimeWorldRefinement` の `M' = q*M` identity を再利用する。

---

## 8. Continuum completion の安全な範囲

今回の「素数は連続を埋めるゲージ」という直観は、Lean ではまず次の安全な形へ落とす。

整数 `k > 0` に対する normalized grid

$$
G_k
=
\left\{\frac{j}{k}\mid 0\le j<k\right\}
$$

を考える。

mesh は `1/k` である。

`k` が増大して `1/k → 0` なら、任意の `x ∈ [0,1]` は grid point で任意精度近似できる。

初期 theorem は「素数そのものが実数点を全て踏む」とせず、例えば

```lean
normalizedGrid_approx
```

として

$$
\forall x\in[0,1],\quad
\exists j\le k,\quad
\left|x-\frac jk\right|\le\frac1k
$$

を証明する。

その後、増大する product modulus sequence `M_n` と

$$
\frac1{M_n}\to0
$$

を仮定または既存 primorial growth theorem から供給し、grid union の稠密性へ進む。

候補:

```lean
normalizedGrid_dense_of_inv_tendsto_zero
primeWorldGrid_dense_of_modulus_tendsto_atTop
```

ここでの dense / no-hole は実数区間の近似性だけを意味する。

**明確な非主張:** 

```text
dense grid
≠ every grid point is prime
≠ every interval contains a newly realized prime from this theorem alone
≠ continuous no-hole implies prime existence
```

この分離を docstring と設計文書で維持する。

---

## 9. 既存「宇宙式反転射影」計画との接続

`宇宙式の反転射影-260708.md` には既に

```text
Cosmic Projection
p-scale valuation flow
finite synchronization / CRT
cofinal extension
no-hole
Collatz odd-core transfer
```

が記録されている。

本計画は、その前半の汎用部分を次のように具体化する。

```text
旧: finite synchronization / CRT
新: CF2D return ⇔ divisibility
    → finite prime-family synchronization
    → product modulus / CRT

旧: Cosmic Projection gap
新: U(k-1) = regularPhaseStep k

旧: no-hole / continuum
新: mesh = 1/M = projection boundary gap
    → grid approximation
```

一方、Collatz 側の相対 scale

$$
P_m=\frac{2^{R_m}}{3^m}
$$

は、今回の `P = k - 1` と意味が異なる。

同じ Projection API を共有してよいが、入力 `P` の semantics は明示的に分離する。

```text
cycle bridge P = k - 1
  : discrete period → normalized cycle resolution

Collatz P_m = 2^{R_m}/3^m
  : relative valuation scale
```

---

## 10. 推奨 module 構成

新規候補:

```text
DkMath/CosmicFormula/Projection/
  Basic.lean
  Inverse.lean
  CF2DBridge.lean

DkMath/NumberTheory/PrimeGauge/
  Return.lean
  PrimePeriod.lean
  PrimorialSync.lean
  CRTPhase.lean
  ContinuumGrid.lean
```

aggregator:

```text
DkMath/CosmicFormula/Projection.lean
DkMath/NumberTheory/PrimeGauge.lean
```

ただし `Return.lean` / `PrimePeriod.lean` が薄すぎる場合は統合する。

既存 `260830` 計画の

```text
BoundaryGN.lean
UnitBoundary.lean
Crystal.lean
```

は別軸として残し、今回の CF2D bridge と無理に同じファイルへ詰め込まない。

Prime Gauge には今後二つの独立 observer があると整理する。

```text
multiplicative / GN observer
  Boundary → GN → primitive fresh direction

periodic / CF2D observer
  exact order → return ⇔ divisibility → finite synchronization
```

両者は `Nat.Prime` / finite prime-world を介して後段で合流する。

---

## 11. 実装 checkpoint

### CPG-000: repository-first audit

確認対象:

```text
CF2D.CycleDivision
CF2D.RegularOrbit
FinitePrimeWorld
PeriodicPrimeWorld
PrimeWorldRefinement
StructuralArithmetic.GNBridge
Samples.Projection
```

完了条件:

- theorem 名・namespace・引数順を現行 `develop` で固定。
- `orderOf_dvd_iff_pow_eq_one` の向きを `#check`。
- product modulus の既存 divisibility API を確認。
- `Samples.Projection` を正式 module へ昇格する際の依存を洗う。

### CPG-001: CF2D return / divisibility bridge

実装:

```lean
regularKernel_pow_eq_one_iff_dvd
```

加えて `n % k = 0` / `ZMod` との bridge が既存 API で薄く書けるなら追加。

検証:

```text
k = 2,3,5,6
n = 0,k,2k,k+1
```

`#print axioms` で CF2D 既存依存以外の axiom を増やさない。

### CPG-002: prime-period wrappers

実装:

```lean
distinct_prime_regularKernel_not_return
```

必要なら prime-order semantic wrapper。

停止条件:
新 structure が単なる `Nat.Prime` の言い換えだけなら structure は作らない。

### CPG-003: finite prime-family synchronization

実装:

```lean
all_primeGauge_return_iff_worldModulus_dvd
primeGauge_worldModulus_is_first_positive_sync
```

既存 `KnownPrimeScales` と `primeWorldModulus` を再利用。

回帰:

```text
{2,3}   → 6
{2,3,5} → 30
{2,3,5,7} → 210
```

### CPG-004: Projection API 正式化

`Samples.Projection` の必要最小限を正式 module へ移す。

実装優先:

```lean
Pi
U
cosmicProjection_gap_eq
cosmicProjection_mem_interval
cosmicProjection_inverse
cosmicProjection_injective
```

旧 sample を直ちに削除する必要はない。compatibility / migration を先に作る。

### CPG-005: CF2D–Projection bridge

実装:

```lean
projectionGap_eq_regularPhaseStep
projection_add_one_eq_regularPhaseStep
projection_eq_regularPhaseStep_sub_one
```

ここが第一統合頂上。

### CPG-006: Primorial / world-modulus projection

実装:

```lean
worldModulus_projection_gap
freshPrime_refinement_mesh
```

`30 → 210` を regression example として固定する。

### CPG-007: CRT phase observer

既存 finite-world residue API と重複監査後、必要な theorem のみ追加。

第一目標:

```text
prime gauge return vector
⇔ divisibility vector
⇔ residue phase zero vector
```

全 CRT 同型そのものを DkMath で再証明しない。

### CPG-008: finite grid approximation

実装:

```lean
normalizedGrid_approx
```

この checkpoint では primorial の無限性を必要としない。

### CPG-009: continuum completion

必要な growth provider が既に存在する場合のみ

```lean
primeWorldGrid_dense_of_modulus_tendsto_atTop
```

へ進む。

ここで review stop とする。

`continuous no-hole → prime realization` は次 phase の research contract であり、この campaign の完了条件に含めない。

---

## 12. 旧 PGN / CP 計画との統合順序

2026-09-01 の実装候補列は

```text
PGN-001 Boundary/GN
PGN-002 GN ↔ cyclotomic
PGN-003 unit Boundary / integer fresh direction
PGN-004 PowerSwap
PGN-005 FLT/GN/Jacobian projection demo
```

であった。

今回の CPG 列は、これと競合しない。

統合後の全体像は次のように読む。

```text
                         ┌─ GN / multiplicative branch ─ PGN-001..003
existing arithmetic ────┤
                         └─ CF2D / periodic branch ───── CPG-001..003
                                                       ↓
                                              finite prime world
                                                       ↓
                                                product modulus
                                                       ↓
                       Cosmic Projection ← CPG-004..006
                                                       ↓
                                  CRT / grid / continuum observer
```

`PGN-004 PowerSwap` は独立 branch。
`PGN-005 FLT/GN/Jacobian projection` は Cosmic Projection の共通中間表現という別用途なので、CPG の Projection API が安定すれば consumer にできる可能性がある。

---

## 13. 非目標・誤読防止

この計画から次を結論しない。

- `regularKernel k` の exact order `k` だけから `k` が prime である。
- finite prime-family synchronization だけから新しい prime が存在する。
- primorial grid の稠密性から任意区間に prime が存在する。
- Cosmic Projection の全射性から整数 prime realization が得られる。
- CRT から無限個の prime を同時同期する有限 modulus が得られる。
- CF2D の real trigonometric model が prime distribution を自動的に決定する。
- Prime Harmony cosine observer が primality oracle になる。
- continuum completion が Twin Prime / Legendre / RH を閉じる。

また、次を区別する。

```text
first return of generator
prime order of a cyclic gauge
family simultaneous return
order of a product kernel
integer residue phase
real normalized phase
projection boundary gap
```

これらは接続できるが、同一概念として潰さない。

---

## 14. 最初の実装目標

最短の有効 chain は次である。

```text
orderOf_regularKernel
        ↓
regularKernel_pow_eq_one_iff_dvd
        ↓
distinct_prime_regularKernel_not_return
        ↓
all_primeGauge_return_iff_worldModulus_dvd
        ↓
projectionGap_eq_regularPhaseStep
        ↓
worldModulus_projection_gap
```

数学的には、

$$
\boxed{
(\operatorname{regularKernel}(k))^n=1
\iff
k\mid n
}
$$

と

$$
\boxed{
\Pi(k-1)+1
=U(k-1)
=\operatorname{regularPhaseStep}(k)
=\frac1k
}
$$

の二本を中心に置く。

この二本が Lean で固定されれば、

```text
回転周期
↔ 可除性
↔ prime-family synchronization
↔ primorial/product modulus
↔ projection boundary resolution
```

という一つの実装 spine が成立する。

ここまでを first milestone とする。
