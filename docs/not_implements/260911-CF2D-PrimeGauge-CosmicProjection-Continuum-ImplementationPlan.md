# CF2D / Prime Gauge / Goldbach Dynamic Phase / Cosmic Projection / Continuum 実装計画

- cid: `6aa35ef2-c298-83ee-96f9-391d89f175f1`
- Status: implementation plan / v1 research direction / not implemented
- Date: 2026-09-11
- Updated: 2026-09-12
- Previous branch: `docs/cf2d-prime-gauge-projection-260911-v0` — merged to `develop`
- Suggested next branch: `wip/cf2d-prime-gauge-projection-260911-v1`
- Base branch: `develop`
- Repository: `Deskuma/dkmath`
- Related plans / reports:
  - `docs/not_implements/260901-実装可能定理候補-実装順調査.md`
  - `docs/not_implements/260826-Prime-Harmony-PHZ-GN-PrimeGauge-ImplementationPlan.md`
  - `docs/not_implements/260830-PrimeGauge-CosmicProjection-TwinPrimeHarmony-ImplementationDesign.md`
  - `docs/not_implements/260909-Goldbach-GN-PrimePair-Fiber-Strategy.md`
  - `docs/not_implements/宇宙式の反転射影-260708.md`
  - `lean/dk_math/docs/dev/NumberTheory-Goldbach-GNFiber-260910-v0/README.md`
  - `lean/dk_math/docs/dev/NumberTheory-Goldbach-QuadraticPrimitiveFiber-260912-v0/report-005.md`

---

## 0. 2026-09-12 更新要旨

本資料の v0 は、次の一本化を目的としていた。

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

この spine 自体は維持する。

ただし 2026-09-12 に完了した Goldbach quadratic primitive audit により、優先順位を変更する。

Astra による調査では、固定中心 `n` の Goldbach fiber に対する

```text
primitive normalization
parity normalization
left/right support separation
LL / LR / RR split
oriented CRT product-wave
```

はすべて有効な構造である一方、対角解を戻した normalized capacity 条件は既存 `GoldbachCapacityEscape` と exact に同値であった。

従って結果は

> **Outcome B — structural normalization only**

であり、固定された一枚の fiber をさらに静的に正規化するだけでは、Strong Goldbach に対する strict information gain は得られなかった。

この結果を受け、v1 では CF2D / Prime Gauge を単なる可除性の別表現として終わらせず、**Goldbach obstruction configuration の center motion / seat motion / prime-world refinement を exact finite dynamics として固定すること**を第一研究目的へ昇格する。

新しい優先 spine は次である。

```text
CF2D exact order
        ↓
return ⇔ divisibility / phase equality
        ↓
Goldbach left/right conjugate prime gauges
        ↓
center motion n → n+1
        ↓
paired refinement under fresh prime q
        ↓
parent-independent relative phase / two-hole shape
        ↓
finite prime-world dynamic phase vector
        ↓
information-gain audit
        ↓
[有望なら] Cosmic Projection / mesh / continuum
```

**重要:** Projection / continuum は廃止しない。ただし Goldbach への応用では、dynamic phase 層で strict information gain が確認できるまで後段へ送る。

---

## 1. v1 の研究判断基準

今回の Goldbach audit から、次の区別を明示する。

### 1.1 static equivalence

次は有用な正規形であっても、それ自体では新情報ではない可能性が高い。

```text
residue ↔ phase
CRT residue vector ↔ product-modulus coordinate
primitive/parity filtering
full-period survivor count
local support cardinality
same-orientation spacing
```

固定 `n` について既存 theorem の言い換えに留まるなら、Goldbach の universal short-fiber escape へ進んだとは数えない。

### 1.2 dynamic information

v1 で狙うのは、次のいずれかを与える theorem である。

- center `n → n+1` で obstruction configuration がどう移動するか。
- seat `u → u+1` と center motion の二つの flow の関係。
- prime-world refinement `M → qM` において、複数 parent cell の間で保存される形。
- left/right forbidden children の相対位相が parent に依存しないこと。
- 複数 prime gauge を束ねたとき、単なる独立 CRT 座標では表現されない collision / transport constraint。
- neighboring fibers 間で保存・単調化・交換される有限量。

最終的な判定は次の三段階とする。

```text
Outcome A: strict information gain が得られた。
Outcome B: 正しい dynamic normal form だが既存 CRT / capacity の再表現。
Outcome C: 想定した保存・分離・局所化が反例で崩れる。
```

---

## 2. 既実装 provider

### 2.1 CF2D exact finite orbit

現在の `develop` には次がある。

```text
DkMath.CosmicFormula.Rotation.CF2D.Basic
DkMath.CosmicFormula.Rotation.CF2D.KernelPower
DkMath.CosmicFormula.Rotation.CF2D.CycleDivision
DkMath.CosmicFormula.Rotation.CF2D.RegularOrbit
DkMath.CosmicFormula.Rotation.CF2D.EuclideanRegularOrbit
```

再利用する中心 API:

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

正の `k` について既に

$$
\operatorname{orderOf}(\operatorname{regularKernel}(k))=k
$$

が成立する。

ここから return / phase equality / residue observer を薄い bridge として構築する。

### 2.2 finite prime world / periodicity / refinement

既存の

```text
FinitePrimeWorld
PeriodicPrimeWorld
PrimeWorldResidues
PrimeWorldRefinement
PrimeWorldCardinality
EulerTotientBridge
PHZ30
```

を再利用する。

特に重要な既実装 theorem は次である。

```lean
primeWorldModulus
dvd_primeWorldModulus_of_mem
supportDisjointFrom_add_mul_primeWorldModulus_iff
supportDisjointFrom_mod_primeWorldModulus_iff
supportDisjointFrom_centered_mirror_iff
primeWorldModulus_insert
prime_coprime_primeWorldModulus_of_not_mem
primeWorldChild
existsUnique_child_dvd_new_prime
exists_unique_reserved_child_and_other_children_survive
reservedChildIndices_eq_singleton
card_survivingChildIndices
```

one-sided prime-world refinement では、fresh prime `q` により old parent の `q` children のうち exactly one が新 `q` wave に予約され、残り `q-1` が survive するところまで実装済みである。

v1 ではこれを **Goldbach paired refinement** へ拡張する。

### 2.3 Goldbach fixed-center layer

現在の production Goldbach modules は、少なくとも次を実装済みである。

```text
fixed-center degree-two GN equivalence
proper small-prime obstruction
small-prime completeness
full-period CRT counting
covered / survivor capacity
incidence / overlap conservation
Pascal pair residual
```

また research scratch では、次を kernel-check 済みである。

```text
positive prime pair → Nat.Coprime n u
primitive + opposite parity → endpoint coprime
center divisors / 2 removal on normalized fiber
left/right proper support disjointness
LL / LR / RR split
oriented CRT spacing
normalized capacity ↔ existing capacity ↔ StrongGoldbach
```

従って v1 で同じ fixed-center normalization を再実装しない。

### 2.4 Cosmic Projection prototype

`DkMath/Samples/Projection.lean` には試作として

```lean
def Pi (P : ℝ) : ℝ := -P / (P + 1)
def U  (P : ℝ) : ℝ := 1 / (P + 1)

cosmicProjection_gap_eq
cosmicProjection_mem_interval
```

がある。

Projection は依然として正式化候補だが、Goldbach dynamic phase の事実監査より後に置く。

---

## 3. 第一基礎 bridge — CF2D return / phase equality / divisibility

### 3.1 return ⇔ divisibility

候補 theorem:

```lean
theorem regularKernel_pow_eq_one_iff_dvd
    {k n : ℕ} (hk : 0 < k) :
    regularKernel k ^ n = 1 ↔ k ∣ n
```

数学的内容:

$$
(\operatorname{regularKernel}(k))^n=1
\iff
k\mid n.
$$

証明は `orderOf_regularKernel hk` と Mathlib の order theorem を利用する薄い wrapper とする。

この theorem 単独は新しい数論結果ではない。目的は DkMath 内で

```text
CF2D return event
⇕
integer divisibility
```

を canonical に固定することである。

### 3.2 phase equality ⇔ congruence

Goldbach 応用では return-to-one だけでなく二つの phase の一致が必要になる。

候補 theorem:

```lean
theorem regularKernel_pow_eq_pow_iff_modEq
    {k a b : ℕ} (hk : 0 < k) :
    regularKernel k ^ a = regularKernel k ^ b ↔ Nat.ModEq k a b
```

名称・statement は repository audit 後に調整する。

この theorem により、可除性だけでなく residue class 全体を CF2D phase で観測できる。

### 3.3 prime-period semantics

`p` が素数なら `regularKernel p` は prime-order cyclic gauge と読める。

新 structure は原則作らない。単なる

```lean
Nat.Prime (orderOf r)
```

の言い換えしか持たない場合は theorem / docstring の semantic wrapper に留める。

候補:

```lean
theorem distinct_prime_regularKernel_not_return
    {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    regularKernel q ^ p ≠ 1
```

---

## 4. Goldbach conjugate prime gauge

固定 center `n` と prime `p` に対し、Goldbach obstruction は

$$
p\mid n-u
\qquad\text{or}\qquad
p\mid n+u
$$

である。

`g_p := regularKernel p` と読むと、第一候補 bridge は

$$
p\mid n-u
\iff
g_p^n=g_p^u,
$$

$$
p\mid n+u
\iff
g_p^u=g_p^{-n}.
$$

自然数減算の truncation を避けるため、実装では `u ≤ n` を明示するか、`Nat.ModEq` / `ZMod p` を中間層に使う。

候補 theorem family:

```lean
goldbachLeftObstructed_iff_gauge_eq
goldbachRightObstructed_iff_gauge_eq_inv
goldbachProperLeftObstructed_iff_gauge_eq_and_endpoint_ne
goldbachProperRightObstructed_iff_gauge_eq_inv_and_endpoint_ne
```

重要なのは、proper endpoint exception を phase periodicity と混同しないこと。

### 4.1 two forbidden markers

各 odd prime `p` に対し、center `n` は二つの forbidden phase

$$
g_p^n,
\qquad
g_p^{-n}
$$

を持つ。

固定 `n` ではこれは既存二 residue obstruction の同値表現に過ぎない。

v1 では、この pair を **動く conjugate marker** として扱う。

候補 definition は必要最小限とし、structure が重い場合は pair theorem に留める。

```lean
GoldbachGaugeMarkers p n := (regularKernel p ^ n, (regularKernel p ^ n)⁻¹)
```

---

## 5. center motion と seat motion

### 5.1 center motion `n → n+1`

`g_p := regularKernel p` とすると、forbidden markers は

$$
(g_p^n,g_p^{-n})
\longmapsto
(g_p\,g_p^n,\;g_p^{-1}g_p^{-n}).
$$

従って left/right marker は CF2D cycle 上を逆方向に一 step ずつ進む。

候補 theorem:

```lean
goldbachGaugeMarkers_succ
```

この theorem 自体は group algebra で薄いが、後段の cross-fiber observer の基礎とする。

### 5.2 seat motion `u → u+1`

Goldbach coordinates

$$
L_n(u)=n-u,
\qquad
R_n(u)=n+u
$$

では、seat を一つ進めると left は -1、right は +1 だけ進む。

```text
center motion n → n+1
  : left marker +1, right marker +1 in endpoint coordinates

seat motion u → u+1
  : left endpoint -1, right endpoint +1
```

phase observer 上ではこの二 flow を明確に区別する。

### 5.3 relative phase

二つの forbidden markers の相対位相は

$$
\rho_p(n)
:=
g_p^n(g_p^{-n})^{-1}
=
g_p^{2n}.
$$

従って

$$
\rho_p(n)=1
\iff
p\mid2n.
$$

odd prime `p` なら

$$
\rho_p(n)=1
\iff
p\mid n.
$$

これは既存 Goldbach residue theorem

```text
left/right forbidden residues coincide ↔ p ∣ 2*n
```

の dynamic phase 読みである。

候補 theorem family:

```lean
goldbachGaugeRelativePhase_eq_pow_two_mul
goldbachGaugeRelativePhase_eq_one_iff_dvd_two_center
goldbachGaugeRelativePhase_succ
```

**判定条件:** ここまでが既存 residue theorem の同値再表現だけなら Outcome B。次の paired refinement で cross-parent / cross-fiber 情報を探す。

---

## 6. Goldbach paired prime-world refinement

既存 `PrimeWorldRefinement` は one-sided divisibility wave に対し、fresh prime `q` を挿入すると old parent `r` の `q` children

$$
u_j=r+jM,
\qquad
0\le j<q,
\qquad
M=\operatorname{primeWorldModulus}(S)
$$

のうち exactly one を新 `q` wave が予約する。

Goldbach では fresh odd prime `q` に対し、raw obstruction は

$$
q\mid n-u_j
$$

または

$$
q\mid n+u_j.
$$

従って通常は left/right それぞれ exactly one child が予約される。

### 6.1 paired unique children

候補 theorem family:

```lean
existsUnique_leftReservedChild
existsUnique_rightReservedChild
leftReservedChild_eq_rightReservedChild_iff_dvd_two_center
leftReservedChild_ne_rightReservedChild_of_not_dvd_two_center
```

`q ∤ 2*n` の場合、二つの reserved child は distinct であるため raw level では

$$
q-2
$$

children が新しい `q` の左右 obstruction を回避する。

候補:

```lean
pairedReservedChildIndices_card_eq_two
pairedSurvivingChildIndices_card_eq_q_sub_two
```

これは既存 full-period Goldbach factor `q-2` の local tree versionであり、**この cardinality だけでは strict information gain とみなさない**。

### 6.2 parent-independent relative position — v1 の本命候補

old modulus を `M`、parent を `r` とし、left/right reserved child index を `jL`, `jR` とする。

`M` は fresh prime `q` と coprime なので `ZMod q` 上で invertible である。

formal target は次の形で置く。

$$
[j_L-j_R]_q
=
[2n]_q\,[M]^{-1}_q.
$$

同値に、inverse を避けるなら

$$
M(j_L-j_R)\equiv2n\pmod q.
$$

**重要な点は右辺に parent `r` が現れないこと。**

一方、pair の absolute placement は parent に依存する。

したがって各 old parent cell に開く二つの forbidden child は

> absolute phase は parent ごとに変わるが、二穴の相対形状は同じ

という構造を持つ。

候補 theorem family:

```lean
pairedReserved_relative_modEq_two_center
pairedReserved_relativePhase_independent_of_parent
pairedReserved_shape_eq_of_parents
```

この部分は v1 の第一 research checkpoint とする。

### 6.3 center motion of the two-hole shape

center を `n → n+1` と動かすと

$$
[j_L-j_R]_{n+1}
=
[j_L-j_R]_n+2[M]^{-1}
\pmod q.
$$

したがって fresh `q` refinement が作る二穴 shape は、center ごとに一定速度で phase space を移動する。

候補:

```lean
pairedReserved_relativePhase_succ
pairedReserved_relativePhase_periodic
```

ここで初めて cross-fiber dynamic theorem となる。

---

## 7. finite prime-family dynamic phase vector

finite prime world `S` に対し、各 `p ∈ S` の Goldbach relative phase

$$
\rho_p(n)=g_p^{2n}
$$

を束ねる。

概念上の observer:

$$
\rho_S(n)
=
(\rho_p(n))_{p\in S}.
$$

CRT により、これは `n mod primeWorldModulus S` と密接に対応する。

ただし v1 では、単なる CRT isomorphism を再証明することを目的としない。

狙うのは次である。

- `n → n+1` が phase vector に一様な translation を与える。
- fresh `q` insertion が old state を children へどう refinement するか。
- paired two-hole relative shape が parent independent であることを family level に持ち上げられるか。
- proper endpoint exception が dynamic orbit 上でどのような finite defect として現れるか。

候補 module:

```text
DkMath/NumberTheory/PrimeGauge/GoldbachPhase.lean
DkMath/NumberTheory/PrimeGauge/GoldbachRefinement.lean
```

候補 theorem family:

```lean
primeGaugePhaseVector
primeGaugePhaseVector_succ
primeGaugePhaseVector_eq_iff_mod_worldModulus
goldbachRelativePhaseVector
goldbachRelativePhaseVector_succ
```

既存 finite-world residue API と同値なだけなら alias / bridge / docstring に留める。

---

## 8. information-gain audit — Projection へ進む前の停止点

Goldbach v1 consumer としては、ここで一度必ず停止し、次を判定する。

### Outcome A

次のいずれかが得られた場合。

- parent-independent relative shape から short-fiber occupancy に新しい bound が出る。
- neighboring centers の phase transport から survivor existence に利用できる monotone / conservation law が出る。
- multiple prime refinements 間に独立 CRT では説明できない collision constraint が出る。
- proper endpoint defect を uniform に control する cross-fiber theorem が出る。

この場合、Goldbach dynamic phase 研究を継続する。

### Outcome B

すべての theorem が

```text
CRT coordinate change
full-period cardinality
existing spacing
existing capacity
```

へ exact に還元される場合。

この場合も reusable API として価値はあるが、Goldbach の strict progress と主張しない。

### Outcome C

期待した parent-independence / two-hole distinctness / cross-fiber rule が条件不足で崩れる場合。

最小反例と exact hypothesis を記録して branch を閉じる。

---

## 9. Prime-family synchronization — v0 spine の維持

Goldbach dynamic phase とは独立に、v0 で計画した finite prime-family synchronization は依然有効である。

有限 prime set `S` に対し

$$
\forall p\in S,\quad (\operatorname{regularKernel}(p))^n=1
$$

は

$$
\forall p\in S,\quad p\mid n
$$

と同値であり、`KnownPrimeScales S` なら product modulus

$$
M_S=\prod_{p\in S}p
$$

について

$$
M_S\mid n
$$

へ接続する。

候補 theorem:

```lean
all_primeGauge_return_iff_worldModulus_dvd
primeGauge_worldModulus_is_first_positive_sync
```

意味:

> `primeWorldModulus S` は finite prime-family の最小正同期周期。

**非目標:** `∏ regularKernel p` という product kernel の `orderOf` を product modulus と同一視しない。family synchronization と product-kernel order は別概念。

---

## 10. CRT phase observer

算術側の observer は

$$
n\mapsto n\bmod p.
$$

有限 `S` では

$$
\mathbb Z/M_S\mathbb Z
\simeq
\prod_{p\in S}\mathbb Z/p\mathbb Z
$$

と読める。

候補 theorem family:

```lean
primeGaugePhase_eq_zero_iff_dvd
primeGaugePhaseVector
primeGaugePhaseVector_eq_iff_mod_worldModulus
primeGaugePhaseVector_injective_mod_worldModulus
```

ただし既存 `PrimeWorldResidues` / `PeriodicPrimeWorld` / Mathlib CRT と重複する場合は新 API を増やさない。

Goldbach consumer では absolute residue vector より **conjugate pair / relative phase** を優先する。

---

## 11. Cosmic Projection と CF2D の直接 bridge

Projection を

$$
\Pi(P)=-\frac{P}{P+1},
\qquad
U(P)=\frac1{P+1}
$$

とする。

CF2D normalized cycle step は

$$
\operatorname{regularPhaseStep}(k)=\frac1k.
$$

`P=k-1` と置けば

$$
\boxed{
\Pi(k-1)+1
=U(k-1)
=\operatorname{regularPhaseStep}(k)
=\frac1k
}.
$$

候補 theorem:

```lean
projectionGap_eq_regularPhaseStep
projection_add_one_eq_regularPhaseStep
projection_eq_regularPhaseStep_sub_one
```

意味:

```text
CF2D side       : finite cycle resolution
Projection side : distance from compactified boundary -1
```

が同じ `1/k` で測られる。

Projection API を正式化する際は `Samples.Projection` を直接 provider とせず、必要部分を `DkMath.CosmicFormula.Projection` へ回収する。

---

## 12. Primorial refinement と projection boundary

finite prime world の product modulus `M_S` に対し

$$
\Delta_S:=\frac1{M_S}
$$

を mesh / gauge resolution と読む。

Projection bridge から

$$
\Delta_S
=U(M_S-1)
=\Pi(M_S-1)+1.
$$

fresh prime `q` の insertion で

$$
M'=qM
$$

なら

$$
\Delta'=\frac{\Delta}{q}.
$$

候補 theorem:

```lean
worldModulus_projection_gap
worldModulus_projection_add_one
freshPrime_refinement_mesh
```

ここで既存 `primeWorldModulus_insert` を再利用する。

Goldbach dynamic phase との接続が得られた場合には、各 old cell が `q` children に refinement され、そのうち raw Goldbach obstruction が通常二つの moving forbidden subcells を作る、と読むことができる。

ただしこれは geometry / semantics であり、survivor existence を自動的には与えない。

---

## 13. Continuum completion の安全な範囲

整数 `k>0` に対する normalized grid

$$
G_k
=
\left\{\frac{j}{k}\mid0\le j<k\right\}
$$

を考える。mesh は `1/k`。

候補 theorem:

```lean
normalizedGrid_approx
```

$$
\forall x\in[0,1],\quad
\exists j\le k,\quad
\left|x-\frac jk\right|\le\frac1k.
$$

さらに `M_n → ∞` または `1/M_n → 0` の provider が得られる場合のみ

```lean
normalizedGrid_dense_of_inv_tendsto_zero
primeWorldGrid_dense_of_modulus_tendsto_atTop
```

へ進む。

**明確な非主張:**

```text
dense grid
≠ every grid point is prime
≠ every interval contains a new prime
≠ continuum no-hole implies Goldbach / Twin Prime / Legendre
≠ projection boundary completion implies prime realization
```

Goldbach consumer では、Section 8 の information-gain audit を通る前に continuum を proof provider として使用しない。

---

## 14. 推奨 module 構成 v1

候補:

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
  GoldbachPhase.lean
  GoldbachRefinement.lean
  ContinuumGrid.lean
```

aggregator:

```text
DkMath/CosmicFormula/Projection.lean
DkMath/NumberTheory/PrimeGauge.lean
```

ただし薄い file / structure を量産しない。

Prime Gauge は少なくとも二 observer を持つと整理する。

```text
multiplicative / GN observer
  Boundary → GTail/GN → primitive fresh direction

periodic / CF2D observer
  exact order → return / phase equality → finite synchronization
```

Goldbach は後者の consumer として

```text
left/right conjugate marker
paired child refinement
center motion
relative phase
```

を追加する。

---

## 15. v1 実装 checkpoint

### CPG-V1-000: repository-first audit

確認対象:

```text
CF2D.CycleDivision
CF2D.RegularOrbit
PeriodicPrimeWorld
PrimeWorldRefinement
PrimeWorldResidues
Goldbach.Basic
Goldbach.Obstruction
Goldbach.PrimeWorld
Goldbach.PairOverlap
Goldbach quadratic primitive Astra scratch
Samples.Projection
```

完了条件:

- theorem 名・namespace・引数順を現行 `develop` で固定。
- Mathlib の `orderOf` / pow equality / `Nat.ModEq` API を確認。
- Goldbach raw/proper obstruction の既存 theorem と重複監査。
- one-sided unique child theorem の再利用範囲を固定。
- `ZMod q` inverse を使う場合の `q ≠ 0` / coprimality hypotheses を固定。

### CPG-V1-001: CF2D return / congruence bridge

実装候補:

```lean
regularKernel_pow_eq_one_iff_dvd
regularKernel_pow_eq_pow_iff_modEq
```

回帰:

```text
k = 2,3,5,6
n = 0,k,2k,k+1
```

### CPG-V1-002: Goldbach conjugate gauge bridge

実装候補:

```lean
goldbachLeftObstructed_iff_gauge_eq
goldbachRightObstructed_iff_gauge_eq_inv
```

raw / proper の区別を維持する。

### CPG-V1-003: center / relative phase dynamics

実装候補:

```lean
goldbachGaugeMarkers_succ
goldbachGaugeRelativePhase_eq_pow_two_mul
goldbachGaugeRelativePhase_eq_one_iff_dvd_two_center
goldbachGaugeRelativePhase_succ
```

ここまでは既存 residue theorem の phase lift である可能性が高い。

### CPG-V1-004: paired prime-world refinement

one-sided `existsUnique_child_dvd_new_prime` を利用し、left/right reserved child を構成する。

候補:

```lean
existsUnique_leftReservedChild
existsUnique_rightReservedChild
leftReservedChild_ne_rightReservedChild_of_not_dvd_two_center
pairedReservedChildIndices_card_eq_two
pairedSurvivingChildIndices_card_eq_q_sub_two
```

### CPG-V1-005: parent-independent two-hole shape

第一研究頂上。

候補 statement:

$$
M(j_L-j_R)\equiv2n\pmod q.
$$

Lean では `Nat.ModEq` または `ZMod q` を使い、truncated subtraction を避ける。

候補:

```lean
pairedReserved_relative_modEq_two_center
pairedReserved_relativePhase_independent_of_parent
pairedReserved_shape_eq_of_parents
```

### CPG-V1-006: cross-fiber center transport

候補:

```lean
pairedReserved_relativePhase_succ
pairedReserved_relativePhase_periodic
goldbachRelativePhaseVector_succ
```

`n → n+1` で two-hole shape が一定 step で動くことを固定する。

### CPG-V1-007: information-gain audit

ここで必ず停止する。

- existing CRT/capacity への exact reduction を調べる。
- short-fiber localization に新 bound が出るか検査する。
- counterexample を Python / Lean regression で探索する。
- Outcome A/B/C を明記する。

**Outcome B/C なら Goldbach proof campaign としては一旦閉じる。**

### CPG-V1-008: finite prime-family synchronization

v0 の

```lean
all_primeGauge_return_iff_worldModulus_dvd
primeGauge_worldModulus_is_first_positive_sync
```

を実装する。

Goldbach outcome に依存しない reusable core。

### CPG-V1-009: Projection API / CF2D bridge

必要最小限を正式 module 化する。

```lean
Pi
U
cosmicProjection_gap_eq
cosmicProjection_inverse
cosmicProjection_injective
projectionGap_eq_regularPhaseStep
projection_add_one_eq_regularPhaseStep
```

### CPG-V1-010: world-modulus projection / mesh

```lean
worldModulus_projection_gap
freshPrime_refinement_mesh
```

### CPG-V1-011: continuum grid

```lean
normalizedGrid_approx
```

までを基本 milestone とする。

無限 dense theorem は growth provider と用途が明確な場合のみ別 campaign とする。

---

## 16. 実装時の数値・scratch 調査

Goldbach dynamic phase 層は、production 実装前に scratch / Python で反例探索を行う価値が高い。

最低限、次を検査する。

```text
1. q-children 上の left/right reserved index の uniqueness
2. q ∤ 2n のとき二 index が distinct
3. M(jL-jR) ≡ 2n (mod q)
4. parent r を変えても relative difference が不変
5. n → n+1 で relative difference が定 step で変化
6. proper endpoint exception が raw phase orbit から削除する seat
7. 複数 q を束ねたとき独立 CRT 以上の constraint が本当に存在するか
```

反例が出た場合は hypothesis を強めるか theorem を破棄し、数値観測だけを普遍定理として昇格しない。

---

## 17. 非目標・誤読防止

この計画から次を結論しない。

- `regularKernel k` の exact order `k` だけから `k` が prime である。
- residue を CF2D phase と書き換えただけで Goldbach に新情報が加わる。
- paired `q-2` child count だけから short-fiber survivor が存在する。
- parent-independent two-hole shape が証明されただけで Strong Goldbach が従う。
- finite prime-family synchronization だけから新しい prime が存在する。
- primorial grid の稠密性から任意区間に prime が存在する。
- Cosmic Projection の全射性から整数 prime realization が得られる。
- continuum completion が Twin Prime / Legendre / RH / Goldbach を閉じる。

また、次を区別する。

```text
first return of generator
prime order of a cyclic gauge
integer residue phase
Goldbach conjugate marker
relative left/right phase
family simultaneous return
order of a product kernel
product-modulus coordinate
real normalized phase
projection boundary gap
continuum mesh
```

これらは接続できるが同一概念として潰さない。

---

## 18. v1 の最初の実装目標

v1 の最短 chain は、v0 の Projection 直行ではなく次とする。

```text
orderOf_regularKernel
        ↓
regularKernel_pow_eq_one_iff_dvd
        ↓
regularKernel_pow_eq_pow_iff_modEq
        ↓
Goldbach left/right gauge bridge
        ↓
center / relative phase dynamics
        ↓
paired fresh-prime refinement
        ↓
parent-independent two-hole shape
        ↓
cross-fiber center transport
        ↓
information-gain audit
```

第一研究核は

$$
\boxed{
M(j_L-j_R)\equiv2n\pmod q
}
$$

である。

この式が期待通り formalize できれば、fresh prime `q` が各 old parent cell に作る二つの Goldbach obstruction hole は

> parent により absolute phase は変わるが、relative shape は保存される

と読める。

さらに center motion により、この保存形状自体が phase space 上を一定 step で移動する。

これは現在の Goldbach fixed-center capacity / static normalization には無かった **cross-parent / cross-fiber dynamic observer** の候補である。

この dynamic layer が既存 CRT の単なる言い換えを超えるかどうかを Lean と数値検証で判定し、その結果が有望な場合に限って、v0 由来の

```text
prime-family synchronization
→ Cosmic Projection
→ mesh refinement
→ continuum observer
```

へ接続する。

ここを v1 の first milestone とする。
