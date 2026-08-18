# CFZP-0028 — CFZP-006X negative-frequency boundary profile derivative / local monotonicity audit 実装指示書

## 0. 作業対象

Repository:

```text
Deskuma/dkmath
```

Working branch:

```text
wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0
```

この指示書作成直前の Green checkpoint:

```text
8ccd290e6022c50b3226f01e90bd933e92142889
Add: CFZP-0027: CFZP-006W branch-free prime-power event sign-cell / centered-displacement audit
```

直前 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaBranchFreePrimePowerSignCellAudit
```

006W で safe-frequency prime-power event は exact に

```text
Event(p,j)
  = PositiveScale(p,j)
    * [F(L-ε) - F(L+ε)]

L := j * log p
F(u) := NegativeFrequencyBoundaryProfile(a,T,u)
```

まで局所化された。

さらに

```text
0 < L-ε < L+ε
```

および event の zero/sign/order と centered profile comparison の exact iff が得られている。

今回 CFZP-006X では、残る local ordering problem

```text
F(L-ε) ? F(L+ε)
```

を derivative の符号問題へ exact に降ろす。

ただし **global / universal monotonicity を証明しようとしない**。

006W の profile は trigonometric oscillation を含み、derivative は generic に符号変化する構造を持つ。006X の目的は

```text
F'(u) の exact branch-free formula
  ↓
derivative sign core
  ↓
local monotonicity on a chosen interval
  ↓
prime-power centered event sign
```

という条件付き bridge を構築することである。

---

# 1. 006W で確立済みの正本

006W の first-class definitions:

```lean
cfzpNegativeFrequencyBoundaryCore
cfzpNegativeFrequencyBoundaryProfile
cfzpPrimePowerPhaseCenter
cfzpPrimePowerPhaseMagnitudeLeft
cfzpPrimePowerPhaseMagnitudeRight
cfzpPrimePowerEventPositiveScale
```

profile は

```text
Core(a,u,T)
  := (a*u + 1) * sin(u*T) - u*T*cos(u*T)

F(a,T,u)
  := exp(-a*u) / u^2 * Core(a,u,T)
```

である。

safe-frequency witnessed prime power では

```text
uL := L - ε
uR := L + ε
L  := j * log p

0 < uL < uR
```

かつ

```text
Event(p,j)
  = PositiveScale(p,j) * (F(a,T,uL) - F(a,T,uR))
```

である。

ここから universal ordering はまだ得ていない。

---

# 2. 推奨 module

```text
DkMath.RH.CFBRC.CosmicFormulaZetaNegativeFrequencyProfileDerivativeAudit
```

推奨 path:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaNegativeFrequencyProfileDerivativeAudit.lean
```

最低限 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaBranchFreePrimePowerSignCellAudit
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic
```

既存 import chain で MeanValue API が見えるなら explicit import は省略可。

`DkMath/RH.lean` に public import を追加する。

---

# 3. Gate A — derivative core を first-class 化

006W profile

```text
F(u)
  = exp(-a*u) / u^2
    * ((a*u+1) sin(u*T) - u*T cos(u*T))
```

の derivative は `u ≠ 0` で exact に

```text
F'(u)
  = exp(-a*u) / u^3 * D(a,T,u)
```

と整理できる。

ここで derivative core は

```text
D(a,T,u)
  :=
    (u^2 * (T^2 - a^2) - 2 * (a*u + 1)) * sin(u*T)
    + 2 * T * u * (a*u + 1) * cos(u*T)
```

である。

推奨 definition:

```lean
noncomputable def cfzpNegativeFrequencyBoundaryProfileDerivativeCore
    (a T u : ℝ) : ℝ :=
  (u ^ 2 * (T ^ 2 - a ^ 2) - 2 * (a * u + 1)) * Real.sin (u * T) +
    2 * T * u * (a * u + 1) * Real.cos (u * T)
```

必要なら sin coefficient も分離してよい。

```lean
noncomputable def cfzpNegativeFrequencyBoundaryProfileDerivativeSinCoeff
    (a T u : ℝ) : ℝ :=
  u ^ 2 * (T ^ 2 - a ^ 2) - 2 * (a * u + 1)
```

ただし definition の乱立は避ける。

---

# 4. Gate B — exact derivative theorem

中心 theorem 1。

`hu : u ≠ 0` の下で

```text
HasDerivAt
  (fun x => cfzpNegativeFrequencyBoundaryProfile a T x)
  (exp(-a*u) / u^3 * D(a,T,u))
  u
```

を証明する。

推奨 theorem 名:

```lean
cfzpNegativeFrequencyBoundaryProfile_hasDerivAt
```

可能なら続けて

```lean
cfzpNegativeFrequencyBoundaryProfile_deriv
```

として

```text
deriv (fun x => cfzpNegativeFrequencyBoundaryProfile a T x) u
  = exp(-a*u) / u^3 * D(a,T,u)
```

も公開する。

proof は `Real.exp`, `sin`, `cos`, division / power の標準 derivative と ring/field simplification だけで閉じる。

`u = 0` を totalized division の挙動から解析しない。今回の domain は `u > 0` で十分。

---

# 5. Gate C — derivative sign を derivative core sign へ exact reduction

`hu : 0 < u` の下では

```text
exp(-a*u) / u^3 > 0
```

である。

したがって exact に

```text
F'(u) = 0 ↔ D(a,T,u) = 0
0 < F'(u) ↔ 0 < D(a,T,u)
F'(u) < 0 ↔ D(a,T,u) < 0
0 ≤ F'(u) ↔ 0 ≤ D(a,T,u)
F'(u) ≤ 0 ↔ D(a,T,u) ≤ 0
```

を公開する。

推奨 theorem family:

```lean
cfzpNegativeFrequencyBoundaryProfile_deriv_eq_zero_iff_derivativeCore_eq_zero
cfzpNegativeFrequencyBoundaryProfile_deriv_pos_iff_derivativeCore_pos
cfzpNegativeFrequencyBoundaryProfile_deriv_neg_iff_derivativeCore_neg
cfzpNegativeFrequencyBoundaryProfile_deriv_nonneg_iff_derivativeCore_nonneg
cfzpNegativeFrequencyBoundaryProfile_deriv_nonpos_iff_derivativeCore_nonpos
```

ここで sign provider はまだ derivative core 側に残る。

---

# 6. Gate D — rectangle geometry の lightweight positivity bridge

現行 rectangle structure は

```text
W.rectangle.hσ : 1 < W.rectangle.σ
W.rectangle.hT : 0 < W.rectangle.T
```

を持つ。

したがって

```text
a := cfzpModePhaseAbscissa W
  = W.rectangle.σ - 1/2
```

について

```text
0 < a
0 < W.rectangle.T
```

を CFZP-facing helper として薄く公開してよい。

候補:

```lean
cfzpModePhaseAbscissa_pos
cfzpModePhaseHeight_pos
```

既存 field `W.rectangle.hT` をそのまま使えるなら height helper は不要。

この positivity は derivative core の係数符号を扱う際に使う。

---

# 7. Gate E — derivative-core local sign cells

`u > 0`, `T > 0`, `a ≥ 0` の下では

```text
2 * T * u * (a*u + 1) > 0
```

である。

sin coefficient を

```text
A(a,T,u)
  := u^2 * (T^2 - a^2) - 2 * (a*u + 1)
```

と略記する。

すると

```text
D = A * sin(uT) + positiveCoefficient * cos(uT)
```

である。

以下のような **conditional sign cells** を安全に公開してよい。

### nonpositive cells

```text
0 ≤ A,
sin(uT) ≤ 0,
cos(uT) ≤ 0
  → D ≤ 0
```

または

```text
A ≤ 0,
0 ≤ sin(uT),
cos(uT) ≤ 0
  → D ≤ 0
```

### nonnegative cells

```text
0 ≤ A,
0 ≤ sin(uT),
0 ≤ cos(uT)
  → 0 ≤ D
```

または

```text
A ≤ 0,
sin(uT) ≤ 0,
0 ≤ cos(uT)
  → 0 ≤ D
```

推奨 theorem 名は orientation を明示する。

```lean
cfzpNegativeFrequencyBoundaryProfileDerivativeCore_nonpos_of_...
cfzpNegativeFrequencyBoundaryProfileDerivativeCore_nonneg_of_...
```

すべての cell を実装する必要はない。最低限 one nonpositive / one nonnegative cell を exact に公開する。

---

# 8. Gate F — `T ≤ a` の簡約 cell は conditional のみ

追加仮定

```text
0 ≤ a
0 < u
0 ≤ T
T ≤ a
```

があるなら

```text
T^2 - a^2 ≤ 0
```

なので

```text
A(a,T,u) < 0
```

まで得られる。

これを optional theorem として公開してよい。

候補:

```lean
cfzpNegativeFrequencyBoundaryProfileDerivativeSinCoeff_neg_of_T_le_a
```

この条件下では derivative sign cell が簡単になり、例えば

```text
0 ≤ sin(uT), cos(uT) ≤ 0
  → D ≤ 0
```

となる。

ただし repository の rectangle contract は `T ≤ a` を保証していない。**W から無条件に導出してはならない。**

---

# 9. Gate G — derivative sign から local monotonicity への adapter

中心 theorem 2。

Mathlib の現行 MeanValue API にある

```lean
antitoneOn_of_deriv_nonpos
monotoneOn_of_deriv_nonneg
strictAntiOn_of_hasDerivWithinAt_neg
```

等を利用し、positive interval 上の conditional monotonicity bridge を作る。

例えば `0 < l`, `l ≤ r` の下で

```text
∀ u ∈ Ioo l r, D(a,T,u) ≤ 0
```

なら

```text
AntitoneOn
  (cfzpNegativeFrequencyBoundaryProfile a T)
  (Icc l r)
```

を証明する。

推奨 theorem 名:

```lean
cfzpNegativeFrequencyBoundaryProfile_antitoneOn_Icc_of_derivativeCore_nonpos
```

dual:

```lean
cfzpNegativeFrequencyBoundaryProfile_monotoneOn_Icc_of_derivativeCore_nonneg
```

も安価なら追加する。

strict version は optional:

```text
D < 0 on Ioo l r
  → StrictAntiOn F (Icc l r)

0 < D on Ioo l r
  → StrictMonoOn F (Icc l r)
```

proof が MeanValue theorem の hypotheses 整理で重くなる場合、nonstrict version を優先する。

---

# 10. Gate H — prime-power event sign を local derivative cell へ接続

中心 theorem 3。

safe-frequency hypotheses

```text
hε : 0 < ε
hε2 : ε < Real.log 2
hp : Nat.Prime p
hj : 0 < j
```

の下で

```text
uL := cfzpPrimePowerPhaseMagnitudeLeft ε p j
uR := cfzpPrimePowerPhaseMagnitudeRight ε p j
```

と置く。

006W から

```text
0 < uL < uR
```

および

```text
Event = positiveScale * (F(uL) - F(uR))
```

がある。

したがって

```text
∀ u ∈ Ioo uL uR, D(a,T,u) ≤ 0
  → 0 ≤ Event
```

を exact に証明する。

推奨 theorem 名:

```lean
cfzpPrimePowerBranchFreeTrigEvent_nonneg_of_derivativeCore_nonpos_on_centeredInterval
```

dual:

```text
∀ u ∈ Ioo uL uR, 0 ≤ D(a,T,u)
  → Event ≤ 0
```

推奨:

```lean
cfzpPrimePowerBranchFreeTrigEvent_nonpos_of_derivativeCore_nonneg_on_centeredInterval
```

strict local monotonicity adapter が自然に使えるなら

```text
D < 0 on Ioo uL uR → 0 < Event
0 < D on Ioo uL uR → Event < 0
```

も追加してよい。

重要:

この theorem は event sign を **局所 derivative condition に条件付ける**だけであり、すべての prime-power event が同符号とは言わない。

---

# 11. Gate I — global derivative sign が成立しないことを示す explicit phase witnesses

006X では universal monotonicityを狙わない理由を scalar level で可視化する。

`a ≥ 0`, `T > 0` の下で

```text
u₁ := π / T
u₂ := 2π / T
```

とすると

```text
u₁*T = π
u₂*T = 2π
```

である。

DerivativeCore の sin 項は消え、cos 項だけが残るため exact に

```text
D(a,T,π/T)
  = -2 * π * (a * (π/T) + 1)
  < 0

D(a,T,2π/T)
  = 4 * π * (a * (2π/T) + 1)
  > 0
```

が期待される。

Mathlib の `Real.sin_pi`, `Real.cos_pi` と `two_mul` 周辺 simplification で自然に閉じる場合、以下を公開する。

```lean
cfzpNegativeFrequencyBoundaryProfileDerivativeCore_at_pi_div_neg
cfzpNegativeFrequencyBoundaryProfileDerivativeCore_at_two_pi_div_pos
```

さらに Gate C へ接続し、profile derivative 自体の負／正 witness を公開してもよい。

これは fixed prime-power centered interval が必ずこれらの点を含むという主張ではない。

意味は

> generic profile の derivative sign は positive half-line 全体では一定ではない

という有限 real audit である。

proof が theorem-name 探索で重い場合、この Gate は optional とするが、数学的には優先度が高い。

---

# 12. 今回閉じる frontier / 残す frontier

## 12.1 今回閉じるもの

006W marker

```lean
CfzpPrimePowerBoundaryProfileMonotonicityGap
```

が示していた不足を、**global monotonicity provider** ではなく

```text
derivative exact formula
+ local monotonicity condition
+ event sign adapter
```

へ精密化する。

もし Gate I が Green なら、global derivative fixed-sign route は generic に不適切であることも explicit に記録できる。

## 12.2 必ず残すもの

未解決:

- 各 prime-power centered interval がどの derivative sign cell に入るか
- all prime powers に共通する event sign
- cumulative ledger monotonicity
- cumulative ledger one-sidedness / boundedness
- finite baseline reach existence
- cofinal reach
- convergence
- correction source sign
- top-horizontal matching
- finite contact から pointwise source zero への短絡
- zeta-zero conclusion
- RH conclusion

新しい frontier marker 候補:

```lean
inductive CfzpPrimePowerCenteredDerivativeCellCoverageGap : Prop
  | noIndependentPrimePowerCenteredIntervalDerivativeSignCellProvider
```

これは 006X 後の本質をよく表す。

---

# 13. Dependency / firewall

006X は finite real differential/local-order audit である。

禁止:

- `Complex.arg`
- 新しい global `Complex.log` branch
- arbitrary complex-base branch analysis
- infinite Euler product
- 新規 `X → ∞` argument
- infinite sum/integral exchange
- unconditional global profile monotonicity
- unconditional event sign
- cumulative ledger monotonicity
- baseline reach existence
- convergence
- zeta-zero conclusion
- RH conclusion
- `sorry`
- `admit`
- `axiom`
- `native_decide`

使う解析は finite real `exp/sin/cos`, derivative, interval monotonicity のみ。

---

# 14. 実装順序

推奨:

```text
1. new module / imports
2. derivative core definition
3. profile HasDerivAt exact formula
4. deriv exact formula
5. positive derivative prefactor
6. derivative sign iff derivative-core sign
7. optional rectangle a/T positivity helper
8. local derivative-core sign cells
9. local AntitoneOn / MonotoneOn adapters
10. prime-power centered interval event sign adapters
11. optional π/T, 2π/T derivative sign witnesses
12. refined frontier marker
13. DkMath/RH.lean public import
```

---

# 15. 成功条件

006X Green 条件:

1. `CosmicFormulaZetaNegativeFrequencyProfileDerivativeAudit.lean` を追加。
2. `DkMath/RH.lean` に public import。
3. derivative core `D(a,T,u)` を first-class 化。
4. `u ≠ 0` で profile の exact `HasDerivAt` formula。
5. 可能なら `deriv` formula も public。
6. `u > 0` で derivative sign/zero と derivative-core sign/zero の exact iff。
7. 少なくとも一つの safe nonpositive derivative-core sign cell。
8. 少なくとも一つの safe nonnegative derivative-core sign cell。
9. derivative-core nonpositive on an interval から profile `AntitoneOn` を conditional に得る。
10. derivative-core nonnegative on an interval から profile `MonotoneOn` を conditional に得るか、少なくとも dual event-sign theorem を直接得る。
11. prime-power centered interval上の derivative-core nonpositive から event nonnegative。
12. dualに derivative-core nonnegative から event nonpositive。
13. universal/global profile monotonicityを主張しない。
14. universal event signを主張しない。
15. cumulative ledger monotonicityを主張しない。
16. reach existence / convergence を主張しない。
17. zeta-zero / RH を主張しない。
18. target module build Green。
19. `lake build DkMath.RH` Green。
20. `./lean-build.sh` Green。
21. `./lean-test.sh` Green。
22. `git diff --check` Green。
23. new module に `sorry`, `admit`, `axiom`, `native_decide` なし。
24. new module に新規 `Complex.arg` / global `Complex.log` branch なし。

---

# 16. 006Y への候補

006X が Green になった後の第一候補は

```text
CFZP-006Y — prime-power centered phase-cell coverage audit
```

である。

006X 後の remaining local problem は

```text
D(a,T,u) の符号を
u ∈ [L-ε, L+ε]
全体でどう保証するか
```

となる。

ここで phase angle を

```text
θ := u*T
Θ := j*T*log p
η := ε*T
```

と置くと prime-power centered interval は

```text
θ ∈ [Θ-η, Θ+η]
```

になる。

したがって006Yでは

```text
prime-power arithmetic center Θ = j*T*log p
  ↓
finite phase cell occupancy
  ↓
derivative-core sign cell coverage
  ↓
one-event sign
```

を監査する。

ただし equidistribution、density、infinite prime argument、新しい `X → ∞` はまだ扱わない。

まず finite witnessed prime-power に対する cell membership certificate と条件付き sign theorem を優先する。

---

# 17. 006X の位置づけ

```text
006R  cutoff dynamics
006S  event support = prime powers
006T  one-event sign = phase primitive balance
006U  cumulative contact = closed-phase ledger reaches baseline
006V  safe regimeで branch-free exp/cos/sin ledger
006W  one-event = centered profile displacement F(L-ε)-F(L+ε)
006X  derivative core / local monotonicity → centered event sign
```

006X は global sign provider ではない。

役割は「左右二点の balance」を微分可能な一変数 profile の局所増減問題へ正確に変換し、次段の phase-cell arithmetic audit に渡すことである。
