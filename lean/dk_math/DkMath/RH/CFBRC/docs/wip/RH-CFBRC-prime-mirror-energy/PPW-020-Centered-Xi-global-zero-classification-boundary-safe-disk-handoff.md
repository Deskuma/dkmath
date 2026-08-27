# PPW-020 — centered Xi global zero classification / boundary-safe disk bridge 実装指示

## 1. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-prime-mirror-energy-260807-v0
previous checkpoint: PPW-019 complete Green
previous implementation: dd2ba92fb68b6b33f62fb871ded6e574b486a22d
Lean toolchain: v4.32.2
mathlib rev: 905b95818eb32af7874a58b427f50c1711a5e96c
```

PPW-019 までで、fixed entire function

```text
pascalCenteredRiemannXiKernel : ℂ → ℂ
```

の zero set / intrinsic multiplicity / fixed negative log derivative / local circle charge が Green になった。

さらに非自明 zeta zero `ρ` について

```text
zρ := ρ - criticalLineCenter
```

と置けば、

```text
pascalCenteredXiZeroMultiplicity zρ
  = riemannZetaZeroMultiplicity ρ
```

が analytic-order transport として証明済みである。

PPW-019 の finite local-circle accounting では、index set として既存

```text
pascalCriticalMirrorZeroWindowFinset R
```

をそのまま使用した。

しかし one outer contour へ進む前に、次の二点を exact に閉じる必要がある。

```text
1. centered Xi の global zero set に extra zero が存在しないこと
2. centered Xi の closed disk zero set が PPW window の centered image と完全一致すること
```

これを証明せずに outer circle の内部零点を PPW window の零点だけとして数えることは禁止する。

PPW-020 の目的は、**global Xi-zero classification と boundary-safe disk geometry を完成させ、outer contour の正しい有限 zero index set を固定すること**である。

今回、local-circle finite sum と one outer contour の積分値同一視はまだ mandatory にしない。current pinned Mathlib には Cauchy-Goursat / circle Cauchy formula はあるが、一般 residue theorem / argument principle の一発 API はない。PPW-021 では有限個の pole を明示的に差し引く route を検討する。

---

## 2. 新規 module

```text
DkMath.RH.CFBRC.PascalCenteredXiGlobalZeroDiskBridge
```

候補 file:

```text
lean/dk_math/DkMath/RH/CFBRC/PascalCenteredXiGlobalZeroDiskBridge.lean
```

推奨 import:

```lean
import DkMath.RH.CFBRC.PascalCenteredXiMultiplicityLocalChargeBridge
import DkMath.RH.CFBRC.CriticalMirrorZeroBridge
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
```

単体 Green 後に `DkMath/RH.lean` の PPW-019 import 直後へ公開 import を追加する。

---

## 3. 既存 exact API

### 3.1 PPW-018 / PPW-019

```text
pascalRiemannXiKernel
pascalRiemannXiKernel_one_sub
pascalRiemannXiKernel_eq_mul_completedRiemannZeta
pascalRiemannXiKernel_eq_zero_iff_riemannZeta_eq_zero_of_openCriticalStrip
pascalRiemannXiKernel_eq_zero_of_nontrivialRiemannZetaZero

pascalCenteredRiemannXiKernel
pascalCenteredRiemannXiKernel_neg
pascalCenteredXiZeros
mem_pascalCenteredXiZeros
pascalCenteredXiZeroMultiplicity
isClosed_pascalCenteredXiZeros
isDiscrete_pascalCenteredXiZeros
finite_pascalCenteredXiZeros_in_compact
pascalCenteredXiZeroMultiplicity_sub_center_eq_riemannZetaZeroMultiplicity
```

### 3.2 zeta / completed-zeta

既存 Mathlib / project:

```text
completedRiemannZeta_one_sub
riemannZeta_def_of_ne_zero
riemannZeta_ne_zero_of_one_le_re
riemannZeta_eq_zero_iff_completedRiemannZeta_eq_zero
Complex.Gammaℝ_ne_zero_of_re_pos
```

既存 project helper:

```text
ne_zero_of_pos_re
ne_one_of_re_lt_one
gammaR_ne_zero_of_pos_re
```

### 3.3 PPW window

既存:

```lean
noncomputable def pascalCriticalMirrorZeroWindow (R : ℝ) : Set ℂ :=
  {s | s ∈ Metric.closedBall criticalLineCenter R ∧ NontrivialRiemannZetaZero s}

noncomputable def pascalCriticalMirrorZeroWindowFinset (R : ℝ) : Finset ℂ := ...
```

したがって PPW window は **criticalLineCenter を中心とする closed ball 内の非自明 zeta zero** である。

---

## 4. Phase A — uncentered Xi zero は必ず open critical strip に入る

ここが PPW-020 の第一 load-bearing 部分。

まず endpoint の非零性を薄く固定してよい。

候補:

```lean
@[simp] theorem pascalRiemannXiKernel_zero :
    pascalRiemannXiKernel 0 = -1 := by
  simp [pascalRiemannXiKernel]

@[simp] theorem pascalRiemannXiKernel_one :
    pascalRiemannXiKernel 1 = -1 := by
  rw [← pascalRiemannXiKernel_one_sub 0]
  simp [pascalRiemannXiKernel]
```

### 4.1 right half-plane exclusion

必須 theorem:

```lean
theorem pascalRiemannXiKernel_zero_re_lt_one
    {s : ℂ} (hXi : pascalRiemannXiKernel s = 0) :
    s.re < 1 := by
  ...
```

proof route:

```text
assume 1 ≤ s.re
  ↓
Xi(s)=0 implies s ≠ 0,1
  ↓
Xi(s)=s(1-s) completedZeta(s)
  ↓
completedZeta(s)=0
  ↓
GammaR(s) ≠ 0 because re(s)>0
  ↓
zeta(s)=0
  ↓
contradiction with riemannZeta_ne_zero_of_one_le_re
```

`Xi = s(1-s) completedZeta` は `s ≠ 0,1` を得てから使用する。

### 4.2 left half-plane exclusion

必須 theorem:

```lean
theorem pascalRiemannXiKernel_zero_re_pos
    {s : ℂ} (hXi : pascalRiemannXiKernel s = 0) :
    0 < s.re := by
  ...
```

proof route:

```text
assume s.re ≤ 0
  ↓
Xi(s)=0 implies s ≠ 0,1
  ↓
completedZeta(s)=0
  ↓ functional equation
completedZeta(1-s)=0
  ↓
1 ≤ re(1-s)
  ↓
GammaR(1-s) ≠ 0
  ↓
zeta(1-s)=0
  ↓
contradiction with riemannZeta_ne_zero_of_one_le_re
```

ここでは trivial zeta zero を直接展開しない。completed-zeta functional equation と右半平面 zero-free theorem だけで left side を排除する。

### 4.3 strip packaging

```lean
theorem pascalRiemannXiKernel_zero_mem_openCriticalStrip
    {s : ℂ} (hXi : pascalRiemannXiKernel s = 0) :
    0 < s.re ∧ s.re < 1 :=
  ⟨pascalRiemannXiKernel_zero_re_pos hXi,
    pascalRiemannXiKernel_zero_re_lt_one hXi⟩
```

---

## 5. Phase B — global Xi zero classification

open critical strip に入った後は PPW-018 の zero equivalence を使用する。

### 5.1 Xi zero → nontrivial zeta zero

必須 theorem:

```lean
theorem nontrivialRiemannZetaZero_of_pascalRiemannXiKernel_eq_zero
    {s : ℂ} (hXi : pascalRiemannXiKernel s = 0) :
    NontrivialRiemannZetaZero s := by
  ...
```

`NontrivialRiemannZetaZero` は project 上

```text
riemannZeta s = 0
∧ ¬∃ n, s = -2*(n+1)
∧ s ≠ 1
```

なので、zeta zero は PPW-018 equivalence から取得し、domain 条件は `0 < s.re < 1` から証明する。

### 5.2 exact global iff

今回の第一最終 theorem:

```lean
@[simp] theorem pascalRiemannXiKernel_eq_zero_iff_nontrivialRiemannZetaZero
    (s : ℂ) :
    pascalRiemannXiKernel s = 0 ↔
      NontrivialRiemannZetaZero s := by
  constructor
  · exact nontrivialRiemannZetaZero_of_pascalRiemannXiKernel_eq_zero
  · exact pascalRiemannXiKernel_eq_zero_of_nontrivialRiemannZetaZero
```

これにより **uncentered Xi の全 zero は非自明 zeta zero だけ**であることを formalize する。

これは RH ではない。zero の横位置を制限せず、zero set の種類を分類するだけである。

---

## 6. Phase C — centered Xi global zero classification

centered coordinate:

```text
z ↦ criticalLineCenter + z
```

を使う。

必須 theorem:

```lean
@[simp] theorem mem_pascalCenteredXiZeros_iff_nontrivial_shift
    (z : ℂ) :
    z ∈ pascalCenteredXiZeros ↔
      NontrivialRiemannZetaZero (criticalLineCenter + z) := by
  ...
```

また zeta zero 側から centered coordinate に戻す convenience:

```lean
@[simp] theorem sub_center_mem_pascalCenteredXiZeros_iff_nontrivial
    (s : ℂ) :
    s - criticalLineCenter ∈ pascalCenteredXiZeros ↔
      NontrivialRiemannZetaZero s := by
  ...
```

この theorem により PPW-019 の one-way bridge が global iff に強化される。

---

## 7. Phase D — centered Xi disk zero set / Finset

### 7.1 set

```lean
noncomputable def pascalCenteredXiZeroDisk (R : ℝ) : Set ℂ :=
  {z | z ∈ Metric.closedBall 0 R ∧ z ∈ pascalCenteredXiZeros}
```

```lean
@[simp] theorem mem_pascalCenteredXiZeroDisk_iff
    {R : ℝ} {z : ℂ} :
    z ∈ pascalCenteredXiZeroDisk R ↔
      z ∈ Metric.closedBall 0 R ∧ z ∈ pascalCenteredXiZeros :=
  Iff.rfl
```

### 7.2 finite / Finset

`finite_pascalCenteredXiZeros_in_compact` と compact closed ball から:

```lean
theorem finite_pascalCenteredXiZeroDisk (R : ℝ) :
    (pascalCenteredXiZeroDisk R).Finite
```

```lean
noncomputable def pascalCenteredXiZeroDiskFinset (R : ℝ) : Finset ℂ :=
  (finite_pascalCenteredXiZeroDisk R).toFinset
```

```lean
@[simp] theorem mem_pascalCenteredXiZeroDiskFinset_iff ...
```

---

## 8. Phase E — PPW window と centered Xi disk の exact equality

center shift:

```lean
noncomputable def pascalCenterZeroShift (s : ℂ) : ℂ :=
  s - criticalLineCenter
```

inverse shift:

```lean
noncomputable def pascalUncenterZeroShift (z : ℂ) : ℂ :=
  criticalLineCenter + z
```

必要なら mutual inverse theorem を作る。

### 8.1 distance transport

必須 helper:

```lean
@[simp] theorem dist_sub_criticalLineCenter_zero (s : ℂ) :
    dist (s - criticalLineCenter) 0 =
      dist s criticalLineCenter := by
  ...
```

### 8.2 Finset image equality

PPW-020 の第二 load-bearing theorem:

```lean
theorem image_pascalCenterZeroShift_window_eq_centeredXiDisk
    (R : ℝ) :
    (pascalCriticalMirrorZeroWindowFinset R).image
        pascalCenterZeroShift =
      pascalCenteredXiZeroDiskFinset R := by
  ...
```

`Finset.ext` + membership iff で証明するのが安全。

reverse direction では centered Xi zero `z` から

```text
s := criticalLineCenter + z
```

を作り、Phase C の global classification から `NontrivialRiemannZetaZero s` を取得する。

**停止線:** PPW window の centered image が Xi disk zero set を包含するだけでは不十分。必ず equality を証明する。

---

## 9. Phase F — multiplicity / second-moment index transport

PPW-019 の local circle sums は zeta window を index にしている。outer contour work では Xi disk Finset 自身を index にしたい。

### 9.1 multiplicity mass

候補 definition:

```lean
noncomputable def pascalCenteredXiZeroDiskMultiplicity (R : ℝ) : ℕ :=
  (pascalCenteredXiZeroDiskFinset R).sum pascalCenteredXiZeroMultiplicity
```

必須 theorem:

```lean
@[simp] theorem pascalCenteredXiZeroDiskMultiplicity_eq_windowMultiplicity
    (R : ℝ) :
    pascalCenteredXiZeroDiskMultiplicity R =
      pascalCriticalMirrorZeroWindowMultiplicity R := by
  ...
```

proof は Phase E の image equality と PPW-019 multiplicity transport を使う。

### 9.2 centered complex second moment

候補:

```lean
noncomputable def pascalCenteredXiZeroDiskSecondMoment (R : ℝ) : ℂ :=
  ∑ z ∈ pascalCenteredXiZeroDiskFinset R,
    (pascalCenteredXiZeroMultiplicity z : ℂ) * z ^ 2
```

必須 theorem:

```lean
@[simp] theorem pascalCenteredXiZeroDiskSecondMoment_eq_windowCenteredSecondMoment
    (R : ℝ) :
    pascalCenteredXiZeroDiskSecondMoment R =
      pascalCriticalMirrorZeroWindowCenteredSecondMoment R := by
  ...
```

これで outer contour の zero index を Xi 自身だけで記述できる。

---

## 10. Phase G — boundary-safe radius

outer circle 上に Xi zero があると `-Xi'/Xi` の contour integrand が regular でない。

### 10.1 predicate

```lean
def IsPascalCenteredXiBoundarySafeRadius (R : ℝ) : Prop :=
  0 < R ∧
    ∀ z ∈ Metric.sphere (0 : ℂ) R,
      pascalCenteredRiemannXiKernel z ≠ 0
```

equivalent zero-set formを用意してよい:

```lean
theorem isPascalCenteredXiBoundarySafeRadius_iff_no_zero_on_sphere ...
```

### 10.2 closed-ball / open-ball coincidence for zero set

boundary-safe `R` なら zero について `≤ R` と `< R` が同じになる。

候補 theorem:

```lean
theorem mem_centeredXiZeroDiskFinset_iff_mem_ball_of_boundarySafe
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) {z : ℂ} :
    z ∈ pascalCenteredXiZeroDiskFinset R ↔
      z ∈ Metric.ball 0 R ∧ z ∈ pascalCenteredXiZeros := by
  ...
```

### 10.3 boundary-safe radius existence

strongly recommended:

```lean
theorem exists_isPascalCenteredXiBoundarySafeRadius_gt
    (A : ℝ) :
    ∃ R : ℝ, A < R ∧ IsPascalCenteredXiBoundarySafeRadius R := by
  ...
```

これは outer contour 条件が vacuous ではないことを保証する。

proof route は自由だが、zero discreteness / compact finiteness を使用し、数値的な zero height を埋め込まない。

この existence theorem の formalization が想定以上に重い場合、PPW-020 mandatory からは外してよい。その場合は module comment に「outer theorem は boundary-safe radius を hypothesis として受ける」と明記する。

---

## 11. Phase H — fixed outer contour observable の定義だけを置く

PPW-020 では contour value の residue-sum equality はまだ主張しない。

### 11.1 unweighted

```lean
noncomputable def pascalCenteredXiOuterContourMass (R : ℝ) : ℂ :=
  circleIntegral pascalCenteredXiNegLogDeriv 0 R
```

### 11.2 fixed second weight

```lean
noncomputable def pascalCenteredXiSecondOuterContourMass (R : ℝ) : ℂ :=
  circleIntegral
    (fun z => z ^ 2 * pascalCenteredXiNegLogDeriv z)
    0 R
```

boundary-safe `R` について、少なくとも sphere 上の denominator nonzero / continuity / circle integrability を theorem-facing にしておく。

候補:

```lean
theorem pascalCenteredXiNegLogDeriv_continuousOn_sphere
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    ContinuousOn pascalCenteredXiNegLogDeriv (Metric.sphere 0 R)
```

```lean
theorem pascalCenteredXiSecondWeightedNegLogDeriv_continuousOn_sphere
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    ContinuousOn
      (fun z => z ^ 2 * pascalCenteredXiNegLogDeriv z)
      (Metric.sphere 0 R)
```

必要なら `ContinuousOn.circleIntegrable` を使って circle integrability まで package する。

---

## 12. current Mathlib contour audit

pinned Mathlib `Mathlib.Analysis.Complex.CauchyIntegral` には以下がある。

```text
Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
Complex.circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable
Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto
circleIntegral.integral_sub_inv_of_mem_ball
```

特に Cauchy-Goursat により、closed disk 上 continuous かつ open disk 内で complex differentiable な regular function の outer circle integral は `0` にできる。

一方 pinned Mathlib の undergrad coverage では general `residue theorem` は未実装扱いである。

従って PPW-021 で outer contour equality を実装する場合、一般 residue theorem の theorem 名を仮定してはならない。

推奨 route は次である。

```text
fixed integrand h(z) * (-Xi'/Xi)
  ↓
inside-disk Xi zeros を finite list 化
  ↓
各 pole の principal part を有限和で明示的に加えて cancellation
  ↓
removable singularity を埋めた regularizer を構成
  ↓
Cauchy-Goursat で regularizer outer integral = 0
  ↓
principal-part circle integrals を Cauchy formula で評価
  ↓
outer contour = finite local residue sum
```

unweighted `h=1` と fixed second weight `h(z)=z²` を最初の対象とする。

---

## 13. 今回やらないこと

PPW-020 では以下を実装しない。

```text
local-circle finite sum = one outer contour
一般 residue theorem の独自大規模実装
argument principle の一般ライブラリ化
outer contour = radial q2 mass
|z|² を holomorphic weight として使用
SecondMomentDefect = 0
HorizontalEnergy = 0
primeMirror window energy = 0
RiemannHypothesis
critical-strip finite PHZ convergence
explicit formula / Li / Weil positivity
```

---

## 14. Stop conditions / audit warnings

1. `pascalRiemannXiKernel` の zero が open critical strip に入ることを証明する前に global zeta-zero equivalence を主張しない。
2. left-half-plane exclusionでは trivial zero cancellationを手計算せず、completed-zeta functional equation と right-half-plane nonvanishing を使う。
3. `Xi = s(1-s) completedZeta` は `s ≠ 0,1` の下でのみ使う。
4. Xi zero set と nontrivial zeta zero set の equality は RH ではない。横位置 `re=1/2` は一切導かない。
5. centered Xi disk と PPW window の関係は subset ではなく exact image equality を完成条件とする。
6. closed-ball window と outer open-disk interior を混同しない。boundary zero の有無を明示する。
7. outer circle 上に zero がある場合に `-Xi'/Xi` を regular integrand と扱わない。
8. totalized division の point valueを pole の実値として解釈しない。
9. general residue theorem が Mathlib にあると仮定しない。
10. outer contour observable を定義しただけで local residue sum と等しいと主張しない。
11. PPW-017 radial `q2` mass はまだ zero-dependent mirror-frozen routeであり、fixed Xi holomorphic contourからは得られていない。
12. `SecondMomentDefect = 0` と同値な provider を新しい名前で completion 条件にしない。

---

## 15. Build / acceptance criteria

最低限:

```text
lake build DkMath.RH.CFBRC.PascalCenteredXiGlobalZeroDiskBridge
lake build DkMath.RH
./lean-build.sh DkMath.RH.CFBRC.PascalCenteredXiGlobalZeroDiskBridge
git diff --check
```

新規 module に

```text
sorry
axiom
admit
```

を追加しない。

### mandatory acceptance

```text
pascalRiemannXiKernel_zero_re_pos
pascalRiemannXiKernel_zero_re_lt_one
pascalRiemannXiKernel_zero_mem_openCriticalStrip

nontrivialRiemannZetaZero_of_pascalRiemannXiKernel_eq_zero
pascalRiemannXiKernel_eq_zero_iff_nontrivialRiemannZetaZero

mem_pascalCenteredXiZeros_iff_nontrivial_shift
sub_center_mem_pascalCenteredXiZeros_iff_nontrivial

pascalCenteredXiZeroDisk
pascalCenteredXiZeroDiskFinset
mem_pascalCenteredXiZeroDiskFinset_iff

image_pascalCenterZeroShift_window_eq_centeredXiDisk

pascalCenteredXiZeroDiskMultiplicity_eq_windowMultiplicity
pascalCenteredXiZeroDiskSecondMoment_eq_windowCenteredSecondMoment

IsPascalCenteredXiBoundarySafeRadius
mem_centeredXiZeroDiskFinset_iff_mem_ball_of_boundarySafe

pascalCenteredXiOuterContourMass
pascalCenteredXiSecondOuterContourMass
```

### strongly recommended

```text
pascalRiemannXiKernel_zero
pascalRiemannXiKernel_one

dist_sub_criticalLineCenter_zero
finite_pascalCenteredXiZeroDisk

exists_isPascalCenteredXiBoundarySafeRadius_gt

pascalCenteredXiNegLogDeriv_continuousOn_sphere
pascalCenteredXiSecondWeightedNegLogDeriv_continuousOn_sphere
```

---

## 16. PPW-020 完了条件の意味

PPW-020 が Green になれば、centered Xi の zero set は単なる「nontrivial zero を含む entire zero set」ではなく、

```text
centered Xi zeros
  ↕ exact global classification
centered nontrivial zeta zeros
```

となる。

さらに任意の radius `R` について、

```text
PPW critical-mirror zero window
  ↓ center shift
centered Xi closed-disk zero Finset
```

が exact equality で固定される。

従って PPW-021 では extra Xi zero を心配せず、boundary-safe radius `R` の disk 内にある有限個の Xi zero を **完全な pole list** として使用できる。

次の問いはそこで初めて、

```text
fixed local circles の finite residue accounting
        ↓
finite principal-part subtraction
        ↓
Cauchy-Goursat
        ↓
one fixed outer circle
```

へ進む。

この順序を守ることで、outer contour 内部の zero を無証明に落とす循環を避けること。