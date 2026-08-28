# PPW-016 — weighted second-moment contour / horizontal-energy audit 実装指示

## 1. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-prime-mirror-energy-260807-v0
previous checkpoint: PPW-015 complete Green
Lean toolchain: v4.32.2
```

PPW-015 までで、各 zeta zero `ρ` に対して Mathlib 標準 orientation の local circle charge

```text
circleIntegral pascalZetaNegLogDeriv ρ rρ
  = -2πi · multiplicity(ρ)
```

および finite critical-mirror zero window `W_R` 上の独立小円和

```text
LocalContourMass(R)
  = -2πi · totalMultiplicity(R)
```

まで Green になった。

しかし、この unweighted contour mass が数えるのは **zero multiplicity の総量だけ**であり、零点が critical line からどれだけ横へ離れているかは検出しない。

PPW-016 の目的は、holomorphic weight を local circle integral に掛ける weighted contour bridge を構成し、特に centered second weight

```text
h₂(s) = (s - 1/2)^2
```

を用いて **location-sensitive な second moment** を contour observable として取り出すことである。

そのうえで、critical-line からの実方向平方偏差

```text
HorizontalEnergy(R)
  = Σ multiplicity(ρ) · (ρ.re - 1/2)^2
```

と、

```text
RadialSecondMoment(R)
  = Σ multiplicity(ρ) · |ρ - 1/2|²
```

および weighted contour から得られる centered complex second moment の間に exact identity を作る。

核心 identity は各 zero ごとの

```text
2 · (Re(ρ) - 1/2)^2
  = |ρ - 1/2|^2 + Re((ρ - 1/2)^2)
```

である。

weighted contour の normalized value は centered second moment の負値になるため、finite window 全体では

```text
2 · HorizontalEnergy(R)
  = RadialSecondMoment(R)
      - Re(NormalizedCenteredSecondContourMass(R))
```

を目標とする。

これにより、PPW-013 の `primeMirrorOffsetGapAt` energy と contour 側の location data の間に、**zero condition の exact bridge** を張る。

**重要:** PPW-016 では `HorizontalEnergy(R) = 0` を独立に証明しない。右辺の radial / contour equality を全 window で証明することも RH と同値な境界へ戻るため禁止する。この checkpoint は「何が足りないか」を exact finite identity として露出させる audit 層である。

---

## 2. 新規 module

```text
DkMath.RH.CFBRC.PascalZetaWeightedSecondMomentBridge
```

候補 file:

```text
lean/dk_math/DkMath/RH/CFBRC/PascalZetaWeightedSecondMomentBridge.lean
```

推奨 import:

```lean
import DkMath.RH.CFBRC.PascalZetaLocalCircleChargeBridge
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
```

単体 Green 後に `DkMath/RH.lean` へ公開 import を追加する。

---

## 3. 既存 API — 再実装禁止

### 3.1 PPW-015 local circle

```lean
def IsPascalZetaIsolatingRadius (ρ : ℂ) (r : ℝ) : Prop

noncomputable def pascalZetaIsolatingRadius (ρ : ℂ) : ℝ

theorem pascalZetaIsolatingRadius_spec ...

theorem tendsto_pascalZetaLocalResidueKernel ...

theorem circleIntegral_pascalZetaNegLogDeriv_eq_of_isolatingRadius ...

theorem circleIntegral_pascalZetaNegLogDeriv_eq ...
```

`circleIntegral` の orientation / normalization は Mathlib 標準を正本とする。独自 contour convention を作らない。

### 3.2 finite zero window

```lean
noncomputable def pascalCriticalMirrorZeroWindowFinset (R : ℝ) : Finset ℂ

@[simp] theorem mem_pascalCriticalMirrorZeroWindowFinset_iff ...

noncomputable def criticalLineCenter : ℂ := (1 : ℂ) / 2
```

### 3.3 multiplicity

```lean
noncomputable def riemannZetaZeroMultiplicity (ρ : ℂ) : ℕ

theorem riemannZetaZeroMultiplicity_pos
    {ρ : ℂ} (hρ : ρ ∈ riemannZetaZeros) :
    0 < riemannZetaZeroMultiplicity ρ
```

### 3.4 PPW-013 prime-mirror window energy

```lean
noncomputable def pascalCriticalMirrorZeroWindowEnergy
    (n : ℕ) (R : ℝ) : ℝ

theorem pascalCriticalMirrorZeroWindowEnergy_eq_zero_iff
    {n : ℕ} (hn : 1 < n) (R : ℝ) :
    pascalCriticalMirrorZeroWindowEnergy n R = 0 ↔
      ∀ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
        ρ.re = (1 : ℝ) / 2
```

この theorem を zero-condition bridge に使う。`primeMirrorOffsetGapAt` と quadratic horizontal energy を termwise 同一視してはならない。

---

## 4. Mathlib API audit

実装時に current toolchain 上で exact type を `#check` すること。

主要候補:

```lean
#check Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto
#check Complex.normSq
#check Finset.sum_nonneg
#check Finset.sum_eq_zero_iff_of_nonneg
#check Finset.mul_sum
#check Finset.sum_mul
```

PPW-015 で使用した Cauchy integral theorem をそのまま再利用する。

---

## 5. Phase A — generic holomorphic weight local charge

### 5.1 weighted residue kernel

まず general weight `h : ℂ → ℂ` を掛けた regular kernel を定義する。

```lean
noncomputable def pascalZetaWeightedLocalResidueKernel
    (h : ℂ → ℂ) (ρ w : ℂ) : ℂ :=
  h w * pascalZetaLocalResidueKernel ρ w
```

### 5.2 punctured limit

`h` が少なくとも `ρ` で continuous なら、

```lean
theorem tendsto_pascalZetaWeightedLocalResidueKernel
    {h : ℂ → ℂ} {ρ : ℂ}
    (hρzero : ρ ∈ riemannZetaZeros)
    (hh : ContinuousAt h ρ) :
    Tendsto (pascalZetaWeightedLocalResidueKernel h ρ)
      (𝓝[≠] ρ)
      (𝓝 (h ρ * (-(riemannZetaZeroMultiplicity ρ : ℂ))))
```

を作る。

proof は

```text
h(w) → h(ρ)
localResidueKernel(ρ,w) → -mρ
```

の積だけでよい。

### 5.3 weighted local circle theorem

load-bearing generic theorem:

```lean
theorem circleIntegral_weight_mul_pascalZetaNegLogDeriv_eq_of_isolatingRadius
    {h : ℂ → ℂ} {ρ : ℂ}
    (hρzero : ρ ∈ riemannZetaZeros)
    {r : ℝ} (hr : IsPascalZetaIsolatingRadius ρ r)
    (hh : Differentiable ℂ h) :
    circleIntegral (fun w => h w * pascalZetaNegLogDeriv w) ρ r =
      -(2 * Real.pi * Complex.I) *
        (riemannZetaZeroMultiplicity ρ : ℂ) * h ρ
```

積の順序は Lean elaboration に合わせてよいが、数学的内容を変えない。

推奨 proof route:

1. Cauchy theorem に `pascalZetaWeightedLocalResidueKernel h ρ` を渡す。
2. punctured disk 上の differentiability は `hh` と PPW-015 の local kernel differentiability の積。
3. closed punctured disk 上の continuity も同様。
4. local limit は Phase A.2。
5. circle 上で
   `h(w) * pascalZetaNegLogDeriv(w)` と
   `(w-ρ)⁻¹ * weightedKernel(w)` を exact に同一視。

`h` の global `Differentiable` 仮定は、この checkpoint では意図的に強くてよい。centered polynomial weights を安全に通すことを優先する。

---

## 6. Phase B — finite weighted local-circle mass

### 6.1 definition

```lean
noncomputable def pascalCriticalMirrorZeroWindowWeightedLocalContourMass
    (h : ℂ → ℂ) (R : ℝ) : ℂ :=
  ∑ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
    circleIntegral (fun w => h w * pascalZetaNegLogDeriv w)
      ρ (pascalZetaIsolatingRadius ρ)
```

### 6.2 finite weighted zero sum

```lean
theorem pascalCriticalMirrorZeroWindowWeightedLocalContourMass_eq
    {h : ℂ → ℂ} (hh : Differentiable ℂ h) (R : ℝ) :
    pascalCriticalMirrorZeroWindowWeightedLocalContourMass h R =
      -(2 * Real.pi * Complex.I) *
        ∑ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
          (riemannZetaZeroMultiplicity ρ : ℂ) * h ρ
```

各 window member を `riemannZetaZeros` へ移し、Phase A.3 を有限和で足す。

### 6.3 normalized version

```lean
theorem pascalCriticalMirrorZeroWindowNormalizedWeightedLocalContourMass_eq
    {h : ℂ → ℂ} (hh : Differentiable ℂ h) (R : ℝ) :
    (2 * Real.pi * Complex.I)⁻¹ *
      pascalCriticalMirrorZeroWindowWeightedLocalContourMass h R =
      - ∑ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
          (riemannZetaZeroMultiplicity ρ : ℂ) * h ρ
```

PPW-015 と同じ `2πi ≠ 0` proof を再利用可能なら helper lemma 化してよい。

---

## 7. Phase C — centered second weight

### 7.1 weight

```lean
noncomputable def pascalCenteredSecondWeight (s : ℂ) : ℂ :=
  (s - criticalLineCenter) ^ 2
```

```lean
theorem differentiable_pascalCenteredSecondWeight :
    Differentiable ℂ pascalCenteredSecondWeight := by
  fun_prop
```

### 7.2 centered second moment

```lean
noncomputable def pascalCriticalMirrorZeroWindowCenteredSecondMoment
    (R : ℝ) : ℂ :=
  ∑ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
    (riemannZetaZeroMultiplicity ρ : ℂ) *
      (ρ - criticalLineCenter) ^ 2
```

### 7.3 normalized contour = negative second moment

```lean
theorem pascalCriticalMirrorZeroWindowNormalizedCenteredSecondContourMass_eq
    (R : ℝ) :
    (2 * Real.pi * Complex.I)⁻¹ *
      pascalCriticalMirrorZeroWindowWeightedLocalContourMass
        pascalCenteredSecondWeight R =
      - pascalCriticalMirrorZeroWindowCenteredSecondMoment R
```

ここで初めて contour observable が zero の位置を含む complex second moment を読む。

---

## 8. Phase D — multiplicity-weighted horizontal / radial energy

### 8.1 horizontal energy

```lean
noncomputable def pascalCriticalMirrorZeroWindowHorizontalEnergy
    (R : ℝ) : ℝ :=
  ∑ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
    (riemannZetaZeroMultiplicity ρ : ℝ) *
      (ρ.re - (1 : ℝ) / 2) ^ 2
```

これは `primeMirrorOffsetGapAt` energy とは別 quantity である。名称を明確に分けること。

### 8.2 radial second moment

```lean
noncomputable def pascalCriticalMirrorZeroWindowRadialSecondMoment
    (R : ℝ) : ℝ :=
  ∑ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
    (riemannZetaZeroMultiplicity ρ : ℝ) *
      Complex.normSq (ρ - criticalLineCenter)
```

### 8.3 pointwise algebra kernel

まず zero predicate と無関係な pure algebra lemma を作る。

```lean
theorem two_mul_horizontalOffsetSq_eq_normSq_add_centeredSquare_re
    (z : ℂ) :
    2 * (z.re - (1 : ℝ) / 2) ^ 2 =
      Complex.normSq (z - criticalLineCenter) +
        (((z - criticalLineCenter) ^ 2).re) := by
  ...
```

`criticalLineCenter` の re/im simp が必要なら薄い helper:

```lean
@[simp] theorem criticalLineCenter_re :
    criticalLineCenter.re = (1 : ℝ) / 2 := by ...

@[simp] theorem criticalLineCenter_im :
    criticalLineCenter.im = 0 := by ...
```

証明は `Complex.normSq_apply` 相当の展開と `ring` / `ring_nf` で閉じる。

### 8.4 finite sum identity

```lean
theorem two_mul_pascalCriticalMirrorZeroWindowHorizontalEnergy_eq
    (R : ℝ) :
    2 * pascalCriticalMirrorZeroWindowHorizontalEnergy R =
      pascalCriticalMirrorZeroWindowRadialSecondMoment R +
        (pascalCriticalMirrorZeroWindowCenteredSecondMoment R).re
```

有限和だけの exact algebra theorem とする。

---

## 9. Phase E — contour / horizontal-energy exact bridge

normalized centered second contour mass を名前付き object にしてもよい。

```lean
noncomputable def pascalCriticalMirrorZeroWindowNormalizedCenteredSecondContourMass
    (R : ℝ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ *
    pascalCriticalMirrorZeroWindowWeightedLocalContourMass
      pascalCenteredSecondWeight R
```

すると Phase C により

```text
NormalizedCenteredSecondContourMass(R)
  = -CenteredSecondMoment(R)
```

だから、Phase D の identity は

```lean
theorem two_mul_horizontalEnergy_eq_radialSecondMoment_sub_contour_re
    (R : ℝ) :
    2 * pascalCriticalMirrorZeroWindowHorizontalEnergy R =
      pascalCriticalMirrorZeroWindowRadialSecondMoment R -
        (pascalCriticalMirrorZeroWindowNormalizedCenteredSecondContourMass R).re
```

となる。

これが PPW-016 の最重要 load-bearing theorem。

---

## 10. Phase F — horizontal energy の positivity / zero detector

### 10.1 nonnegative

```lean
theorem pascalCriticalMirrorZeroWindowHorizontalEnergy_nonneg
    (R : ℝ) :
    0 ≤ pascalCriticalMirrorZeroWindowHorizontalEnergy R
```

multiplicity は Nat cast なので非負、平方も非負。

### 10.2 zero iff all window zeros are critical

```lean
theorem pascalCriticalMirrorZeroWindowHorizontalEnergy_eq_zero_iff
    (R : ℝ) :
    pascalCriticalMirrorZeroWindowHorizontalEnergy R = 0 ↔
      ∀ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
        ρ.re = (1 : ℝ) / 2
```

各 summand の multiplicity が **strictly positive** であることを使う。

zero product から offset square zero を得る際、`riemannZetaZeroMultiplicity_pos` を window membership から適用する。

### 10.3 positive iff off-critical zero exists

可能なら同時に:

```lean
theorem pascalCriticalMirrorZeroWindowHorizontalEnergy_pos_iff
    (R : ℝ) :
    0 < pascalCriticalMirrorZeroWindowHorizontalEnergy R ↔
      ∃ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
        ρ.re ≠ (1 : ℝ) / 2
```

---

## 11. Phase G — PPW-013 prime-mirror energy との zero-condition bridge

`n > 1` なら PPW-013 energy も同じ finite RH-condition を検出する。

したがって termwise equality を主張せず、zero condition だけを exact に bridge する。

```lean
theorem pascalHorizontalEnergy_eq_zero_iff_primeMirrorWindowEnergy_eq_zero
    {n : ℕ} (hn : 1 < n) (R : ℝ) :
    pascalCriticalMirrorZeroWindowHorizontalEnergy R = 0 ↔
      pascalCriticalMirrorZeroWindowEnergy n R = 0 := by
  rw [pascalCriticalMirrorZeroWindowHorizontalEnergy_eq_zero_iff]
  symm
  exact pascalCriticalMirrorZeroWindowEnergy_eq_zero_iff hn R
```

exact elaboration に合わせて書き換えてよい。

これにより

```text
quadratic horizontal energy
  ↔ zero condition
  ↔ primeMirrorOffsetGapAt finite energy
```

が Green になる。

---

## 12. Phase H — second-moment defect と研究 Gap の明示

### 12.1 defect definition

```lean
noncomputable def pascalCriticalMirrorZeroWindowSecondMomentDefect
    (R : ℝ) : ℝ :=
  pascalCriticalMirrorZeroWindowRadialSecondMoment R -
    (pascalCriticalMirrorZeroWindowNormalizedCenteredSecondContourMass R).re
```

### 12.2 defect = twice horizontal energy

```lean
@[simp] theorem pascalCriticalMirrorZeroWindowSecondMomentDefect_eq
    (R : ℝ) :
    pascalCriticalMirrorZeroWindowSecondMomentDefect R =
      2 * pascalCriticalMirrorZeroWindowHorizontalEnergy R
```

### 12.3 zero / positive characterization

```lean
theorem pascalCriticalMirrorZeroWindowSecondMomentDefect_eq_zero_iff
    {n : ℕ} (hn : 1 < n) (R : ℝ) :
    pascalCriticalMirrorZeroWindowSecondMomentDefect R = 0 ↔
      pascalCriticalMirrorZeroWindowEnergy n R = 0
```

および可能なら

```lean
theorem pascalCriticalMirrorZeroWindowSecondMomentDefect_pos_iff
    (R : ℝ) :
    0 < pascalCriticalMirrorZeroWindowSecondMomentDefect R ↔
      ∃ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
        ρ.re ≠ (1 : ℝ) / 2
```

これが PPW-016 の研究上の出口である。

---

## 13. 今回やらないこと

PPW-016 では以下を実装しない。

```text
independent local circles の outer contour への deformation
argument principle の global rectangle theorem
critical strip 上の finite PHZ convergence
weighted contour と finite Pascal PHZ の積分交換
explicit formula
Weil positivity
Li criterion
mirror multiplicity invariance
全 window で SecondMomentDefect = 0
全 window で HorizontalEnergy = 0
RiemannHypothesis の導出
```

特に次を禁止する。

```text
holomorphic centered second moment
  = horizontal energy
```

これは偽である。

centered complex square の実部は

```text
(Re offset)^2 - (Im offset)^2
```

であり、horizontal square だけではない。

horizontal energy を得るには必ず radial moment

```text
|ρ - 1/2|²
```

との組み合わせが必要である。

---

## 14. Stop conditions / audit warnings

1. unweighted contour mass が multiplicity を数えるだけで RH を制約すると推論しない。
2. `Re((ρ-1/2)^2)` を `(ρ.re-1/2)^2` と同一視しない。
3. non-holomorphic `Complex.normSq` weight を Cauchy contour の holomorphic weightとして扱わない。
4. `primeMirrorOffsetGapAt` energy と quadratic horizontal energy を termwise equal と主張しない。
5. zero-set equivalenceだけを bridge として使う。
6. finite window identity から `∀ R` の zero defect を結論しない。
7. outer contour deformation を実装せずに independent local circles と outer boundary を同一視しない。
8. second-moment defect の nonnegativity から defect `= 0` を結論しない。
9. `radialSecondMoment = contourSecondMoment.re` を independent theorem として証明できたと主張しない。それが次の本質的 provider 候補である。
10. RH-equivalent provider を単なる bookkeeping lemma と呼ばない。

---

## 15. Build / acceptance criteria

最低限:

```text
lake build DkMath.RH.CFBRC.PascalZetaWeightedSecondMomentBridge
lake build DkMath.RH
git diff --check
```

可能なら wrapper build も実行。

新規 module に

```text
sorry
axiom
admit
```

を追加しない。

必須 acceptance theorem 群:

```lean
tendsto_pascalZetaWeightedLocalResidueKernel

circleIntegral_weight_mul_pascalZetaNegLogDeriv_eq_of_isolatingRadius

pascalCriticalMirrorZeroWindowWeightedLocalContourMass_eq
pascalCriticalMirrorZeroWindowNormalizedWeightedLocalContourMass_eq

pascalCriticalMirrorZeroWindowNormalizedCenteredSecondContourMass_eq

two_mul_horizontalOffsetSq_eq_normSq_add_centeredSquare_re

two_mul_pascalCriticalMirrorZeroWindowHorizontalEnergy_eq

two_mul_horizontalEnergy_eq_radialSecondMoment_sub_contour_re

pascalCriticalMirrorZeroWindowHorizontalEnergy_nonneg
pascalCriticalMirrorZeroWindowHorizontalEnergy_eq_zero_iff

pascalHorizontalEnergy_eq_zero_iff_primeMirrorWindowEnergy_eq_zero

pascalCriticalMirrorZeroWindowSecondMomentDefect_eq
pascalCriticalMirrorZeroWindowSecondMomentDefect_eq_zero_iff
```

`HorizontalEnergy_pos_iff` と `SecondMomentDefect_pos_iff` は推奨。必須群が Green なら PPW-016 complete としてよい。

---

## 16. PPW-016 の意味

PPW-015 では contour は zero の **数と multiplicity** しか読んでいなかった。

PPW-016 では weighted local contour により zero の **complex second moment** を読む。

しかし critical-line からの horizontal energy は holomorphic second moment 単独では得られず、exact に

```text
horizontal energy
  = 1/2 · (radial second moment - normalized contour second moment real part)
```

として現れる。

したがって PPW-016 が Green になれば、残る研究 Gap は非常に具体化される。

```text
contour side:
  centered holomorphic second moment

CFBRC / q2 / geometry side:
  radial second moment

差:
  positive horizontal off-critical energy
```

次 checkpoint PPW-017 では、`RadialSecondMoment` を completed-zeta / CFBRC q2 / prime-side explicit-formula data のどこから独立に供給できるかを監査する。

もし

```text
RadialSecondMoment(R)
  = Re(NormalizedCenteredSecondContourMass(R))
```

を RH を仮定せず導ける mechanism が見つかれば、PPW-016 identity により finite horizontal energy がゼロへ落ちる。

逆に、その equality が既に RH と同値でしかないことが判明した場合は、named obstruction として固定し、Weil / Li positivity または explicit-formula test-function route へ移る。
