# PPW-017 — critical-mirror frozen radial contour / CF2D q2 bridge 実装指示

## 1. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-prime-mirror-energy-260807-v0
previous checkpoint: PPW-016 complete Green
Lean toolchain: v4.32.2
```

PPW-016 までで、finite critical-mirror zero window `W_R` に対し、

```text
HorizontalEnergy(R)
RadialSecondMoment(R)
NormalizedCenteredSecondContourMass(R)
SecondMomentDefect(R)
```

が theorem-facing object になり、

```text
2 * HorizontalEnergy(R)
  = RadialSecondMoment(R)
      - Re(NormalizedCenteredSecondContourMass(R))
```

および

```text
SecondMomentDefect(R) = 2 * HorizontalEnergy(R)
```

まで Green になった。

ただし `RadialSecondMoment` は `Complex.normSq` を使うため non-holomorphic であり、単一の holomorphic weight として PPW-016 の weighted contour theorem に直接投入できない。

PPW-017 の目的は、この non-holomorphic radial quantity を **critical mirror を零点ごとに frozen parameter として使う局所 holomorphic weight** に変換し、

```text
local weighted contour charge
  ↔ radial normSq
  ↔ CF2D Vec.q2
```

を exact に接続することである。

中心となる有限代数 identity は、critical-line centered coordinate

```text
z = ρ - 1/2
```

に対して

```text
criticalMirror(ρ) - 1/2 = -conj(z)
```

したがって

```text
z * (criticalMirror(ρ) - 1/2)
  = - z * conj(z)
  = - |z|².
```

ここで、零点 `ρ` を固定して

```text
hρ(w) = (w - 1/2) * (criticalMirror ρ - 1/2)
```

と置けば、`w` に関しては一次多項式なので holomorphic である。

PPW-016 の generic weighted local charge を `hρ` に適用すると、正規化 charge は

```text
mρ * |ρ - 1/2|²
```

となる。

これにより `RadialSecondMoment(R)` 全体が **零点ごとに mirror を frozen した local contour charge の有限和**として exact に再構成できる。

さらに `|ρ - 1/2|²` は、CF2D centered state

```text
⟨ρ.re - 1/2, ρ.im⟩
```

の `Vec.q2` そのものなので、

```text
mirror-frozen contour radial mass
  = CF2D q2 radial mass
  = PPW-016 RadialSecondMoment
```

という analytic / CFBRC algebra bridge を作る。

**重要:** 各 local circle で weight `hρ` は center `ρ` に依存する。したがって、この有限和を「一つの固定 holomorphic weight を持つ outer contour integral」と同一視してはならない。これは PPW-017 で明示する重要な obstruction である。

---

## 2. 新規 module

```text
DkMath.RH.CFBRC.PascalCriticalMirrorRadialContourCF2DBridge
```

候補 file:

```text
lean/dk_math/DkMath/RH/CFBRC/PascalCriticalMirrorRadialContourCF2DBridge.lean
```

推奨 import:

```lean
import DkMath.RH.CFBRC.PascalZetaWeightedSecondMomentBridge
import DkMath.CosmicFormula.Rotation.CF2D.ThreeElementBridge
import DkMath.RH.CFBRC.CriticalMirrorGeometry
import Mathlib.Tactic
```

単体 Green 後に `DkMath/RH.lean` へ公開 import を追加する。

---

## 3. 既存 API — 再実装禁止

### 3.1 Critical mirror geometry

既存 `CriticalMirrorGeometry`:

```lean
noncomputable def criticalMirror (s : ℂ) : ℂ :=
  ⟨1 - s.re, s.im⟩

@[simp] theorem criticalMirror_re (s : ℂ) :
    (criticalMirror s).re = 1 - s.re

@[simp] theorem criticalMirror_im (s : ℂ) :
    (criticalMirror s).im = s.im

theorem criticalMirror_involutive (s : ℂ) :
    criticalMirror (criticalMirror s) = s

noncomputable def centeredComplex (s : ℂ) : ℂ :=
  ⟨s.re - (1 : ℝ) / 2, s.im⟩
```

`criticalMirror` や centered coordinate を duplicate 定義しない。

PPW-013/016 で導入済みの

```lean
criticalLineCenter : ℂ
criticalLineCenter_re
criticalLineCenter_im
```

も再利用する。

### 3.2 PPW-016 weighted contour

```lean
noncomputable def pascalZetaWeightedLocalResidueKernel ...

theorem circleIntegral_weight_mul_pascalZetaNegLogDeriv_eq_of_isolatingRadius ...

theorem circleIntegral_weight_mul_pascalZetaNegLogDeriv_eq ...

noncomputable def pascalCriticalMirrorZeroWindowNormalizedCenteredSecondContourMass ...

noncomputable def pascalCriticalMirrorZeroWindowRadialSecondMoment ...

noncomputable def pascalCriticalMirrorZeroWindowHorizontalEnergy ...

noncomputable def pascalCriticalMirrorZeroWindowSecondMomentDefect ...

@[simp] theorem pascalCriticalMirrorZeroWindowSecondMomentDefect_eq ...
```

### 3.3 CF2D q2

既存 `DkMath.CosmicFormula.Rotation.CF2D.Basic`:

```lean
structure Vec (R : Type u) where
  core : R
  beam : R

def Vec.q2 [Semiring R] (z : Vec R) : R :=
  z.core ^ 2 + z.beam ^ 2

theorem Vec.q2_mk ...
theorem Vec.q2_star ...
theorem Vec.q2_conj ...
```

既存 `ThreeElementBridge`:

```lean
theorem cf2d_squareMass_eq_q2 (z : Vec ℝ) :
    squareMass z.core z.beam = Vec.q2 z
```

この checkpoint では `interactionBeam` や same-object assimilation を無理に使用しない。目的は radial square mass `q2` の exact bridge までである。

---

## 4. Phase A — centered complex / critical mirror algebra

### 4.1 subtraction form と既存 centeredComplex の一致

```lean
@[simp] theorem centeredComplex_eq_sub_criticalLineCenter
    (s : ℂ) :
    centeredComplex s = s - criticalLineCenter := by
  apply Complex.ext <;> simp [centeredComplex, criticalLineCenter]
```

exact syntax は current simp normal form に合わせてよい。

### 4.2 critical mirror の centered coordinate

目標:

```lean
@[simp] theorem centeredComplex_criticalMirror
    (s : ℂ) :
    centeredComplex (criticalMirror s) =
      ⟨-(centeredComplex s).re, (centeredComplex s).im⟩ := by
  apply Complex.ext <;> simp [centeredComplex, criticalMirror]
```

あるいは complex conjugation を使って、より強く

```lean
theorem centeredComplex_criticalMirror_eq_neg_conj
    (s : ℂ) :
    centeredComplex (criticalMirror s) =
      -conj (centeredComplex s)
```

を狙ってよい。

**符号確認:** `-conj(x+iy) = -x + iy` なので critical mirror centered state と一致する。

### 4.3 mirror product = negative normSq

load-bearing pure algebra theorem:

```lean
theorem centeredComplex_mul_criticalMirror_eq_neg_normSq
    (s : ℂ) :
    centeredComplex s * centeredComplex (criticalMirror s) =
      -(Complex.normSq (centeredComplex s) : ℂ) := by
  ...
```

subtraction formでも同型 theorem を置いてよい:

```lean
theorem sub_center_mul_criticalMirror_sub_center_eq_neg_normSq
    (s : ℂ) :
    (s - criticalLineCenter) *
        (criticalMirror s - criticalLineCenter) =
      -(Complex.normSq (s - criticalLineCenter) : ℂ)
```

これが radial contour weight の数学核である。

---

## 5. Phase B — mirror-frozen local holomorphic weight

### 5.1 definition

```lean
noncomputable def pascalMirrorFrozenRadialWeight
    (ρ w : ℂ) : ℂ :=
  (w - criticalLineCenter) *
    (criticalMirror ρ - criticalLineCenter)
```

`ρ` は parameter、`w` が analytic variable。

### 5.2 differentiability

```lean
theorem differentiable_pascalMirrorFrozenRadialWeight
    (ρ : ℂ) :
    Differentiable ℂ (pascalMirrorFrozenRadialWeight ρ) := by
  unfold pascalMirrorFrozenRadialWeight
  fun_prop
```

### 5.3 center evaluation

```lean
@[simp] theorem pascalMirrorFrozenRadialWeight_self
    (ρ : ℂ) :
    pascalMirrorFrozenRadialWeight ρ ρ =
      -(Complex.normSq (ρ - criticalLineCenter) : ℂ) := by
  ...
```

Phase A の mirror-product theorem を再利用する。

---

## 6. Phase C — local radial contour charge

### 6.1 normalized local charge

```lean
noncomputable def pascalZetaNormalizedMirrorFrozenRadialLocalCharge
    (ρ : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ *
    circleIntegral
      (fun w =>
        pascalMirrorFrozenRadialWeight ρ w *
          pascalZetaNegLogDeriv w)
      ρ (pascalZetaIsolatingRadius ρ)
```

### 6.2 exact radial charge

load-bearing theorem:

```lean
@[simp] theorem pascalZetaNormalizedMirrorFrozenRadialLocalCharge_eq
    {ρ : ℂ} (hρ : ρ ∈ riemannZetaZeros) :
    pascalZetaNormalizedMirrorFrozenRadialLocalCharge ρ =
      (riemannZetaZeroMultiplicity ρ : ℂ) *
        (Complex.normSq (ρ - criticalLineCenter) : ℂ)
```

推奨 proof route:

1. `circleIntegral_weight_mul_pascalZetaNegLogDeriv_eq` を
   `pascalMirrorFrozenRadialWeight ρ` に適用。
2. `pascalMirrorFrozenRadialWeight_self` で center value を `-normSq` にする。
3. negative log derivative 側の `-multiplicity` と weight 側の `-normSq` が相殺。
4. `2πi ≠ 0` を PPW-015/016 と同様に処理。

ここで得られる符号は **正の radial mass** であることを必ず確認する。

---

## 7. Phase D — finite mirror-frozen radial contour mass

### 7.1 definition

```lean
noncomputable def pascalCriticalMirrorZeroWindowNormalizedMirrorFrozenRadialContourMass
    (R : ℝ) : ℂ :=
  ∑ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
    pascalZetaNormalizedMirrorFrozenRadialLocalCharge ρ
```

### 7.2 equals radial second moment

```lean
theorem pascalCriticalMirrorZeroWindowNormalizedMirrorFrozenRadialContourMass_eq
    (R : ℝ) :
    pascalCriticalMirrorZeroWindowNormalizedMirrorFrozenRadialContourMass R =
      (pascalCriticalMirrorZeroWindowRadialSecondMoment R : ℂ)
```

finite sum member から `ρ ∈ riemannZetaZeros` を取得し Phase C theorem を使う。

この theorem により、PPW-016 で non-holomorphic object として残っていた radial second moment が、**center-dependent holomorphic local weights の有限 contour sum**へ exact に翻訳される。

---

## 8. Phase E — CF2D centered zero state / q2 bridge

### 8.1 centered CF2D state

```lean
noncomputable def pascalCenteredZeroCF2DState
    (s : ℂ) : DkMath.CosmicFormula.Rotation.CF2D.Vec ℝ :=
  ⟨s.re - (1 : ℝ) / 2, s.im⟩
```

既存 `centeredComplex` を使って

```lean
⟨(centeredComplex s).re, (centeredComplex s).im⟩
```

と書いてもよい。

### 8.2 q2 = normSq

```lean
@[simp] theorem pascalCenteredZeroCF2DState_q2_eq_normSq
    (s : ℂ) :
    DkMath.CosmicFormula.Rotation.CF2D.Vec.q2
      (pascalCenteredZeroCF2DState s) =
      Complex.normSq (s - criticalLineCenter)
```

証明は平方和の展開のみ。

### 8.3 critical mirror preserves q2

```lean
@[simp] theorem pascalCenteredZeroCF2DState_q2_criticalMirror
    (s : ℂ) :
    Vec.q2 (pascalCenteredZeroCF2DState (criticalMirror s)) =
      Vec.q2 (pascalCenteredZeroCF2DState s)
```

これは critical mirror が centered core の符号だけを反転し beam を保存することの square-mass version。

**注意:** CF2D `Vec.conj` は beam の符号を反転する operation であり、critical mirror centered state は core の符号を反転する。両者を同一視しない。

### 8.4 finite CF2D radial mass

```lean
noncomputable def pascalCriticalMirrorZeroWindowCF2DRadialMass
    (R : ℝ) : ℝ :=
  ∑ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
    (riemannZetaZeroMultiplicity ρ : ℝ) *
      Vec.q2 (pascalCenteredZeroCF2DState ρ)
```

```lean
@[simp] theorem pascalCriticalMirrorZeroWindowCF2DRadialMass_eq
    (R : ℝ) :
    pascalCriticalMirrorZeroWindowCF2DRadialMass R =
      pascalCriticalMirrorZeroWindowRadialSecondMoment R
```

---

## 9. Phase F — analytic contour ↔ CF2D q2 exact bridge

ここが PPW-017 の主定理。

```lean
theorem pascalNormalizedMirrorFrozenRadialContourMass_eq_CF2DRadialMass
    (R : ℝ) :
    pascalCriticalMirrorZeroWindowNormalizedMirrorFrozenRadialContourMass R =
      (pascalCriticalMirrorZeroWindowCF2DRadialMass R : ℂ)
```

これは Phase D と Phase E を合成するだけでよいが、次段階への theorem-facing interface として明示する。

意味:

```text
zero-side local residue calculus
  ↓
critical-mirror frozen holomorphic weight
  ↓
radial norm-square mass
  ↓
CF2D q2 square mass
```

ここまでで prime/analytic route と DkMath CF2D preservation algebra が、finite zero window の radial quantity 上で exact に接続する。

---

## 10. Phase G — second-moment defect を二つの contour observable の差へ書き換える

PPW-016 では

```text
SecondMomentDefect
  = RadialSecondMoment
      - Re(NormalizedCenteredSecondContourMass)
```

だった。

Phase D により radial side も contour observable になったため、次を作る。

```lean
theorem pascalSecondMomentDefect_eq_mirrorFrozenContour_sub_centeredContour_re
    (R : ℝ) :
    pascalCriticalMirrorZeroWindowSecondMomentDefect R =
      (pascalCriticalMirrorZeroWindowNormalizedMirrorFrozenRadialContourMass R).re -
        (pascalCriticalMirrorZeroWindowNormalizedCenteredSecondContourMass R).re
```

さらに既存 theorem と組み合わせ、

```lean
theorem pascalMirrorFrozenContourDifference_eq_two_horizontalEnergy
    (R : ℝ) :
    (pascalCriticalMirrorZeroWindowNormalizedMirrorFrozenRadialContourMass R).re -
        (pascalCriticalMirrorZeroWindowNormalizedCenteredSecondContourMass R).re =
      2 * pascalCriticalMirrorZeroWindowHorizontalEnergy R
```

まで置いてよい。

これは RH を証明する theorem ではない。horizontal defect が **二種類の local contour observable の差**として exact に見えるようになっただけである。

---

## 11. Optional — pointwise local contour defect

実装が自然なら、各 zero ごとにも defect を定義する。

```lean
noncomputable def pascalZetaNormalizedLocalHorizontalContourDefect
    (ρ : ℂ) : ℝ :=
  (pascalZetaNormalizedMirrorFrozenRadialLocalCharge ρ).re -
    ((2 * Real.pi * Complex.I)⁻¹ *
      circleIntegral
        (fun w => pascalCenteredSecondWeight w * pascalZetaNegLogDeriv w)
        ρ (pascalZetaIsolatingRadius ρ)).re
```

zero `ρ` では

```lean
theorem pascalZetaNormalizedLocalHorizontalContourDefect_eq
    {ρ : ℂ} (hρ : ρ ∈ riemannZetaZeros) :
    pascalZetaNormalizedLocalHorizontalContourDefect ρ =
      2 * (riemannZetaZeroMultiplicity ρ : ℝ) *
        (ρ.re - (1 : ℝ) / 2) ^ 2
```

となる。

これは finite sum theorem の pointwise source を明示するが、PPW-017 必須条件ではない。

---

## 12. Named obstruction — zero-dependent weight

PPW-017 ではコードコメントまたは theorem-facing structure で、次を明示する。

```text
pascalMirrorFrozenRadialWeight ρ
```

は `ρ` ごとに異なる。

したがって

```text
Σρ ∮ hρ(w) (-ζ'/ζ)(w) dw
```

は、一般には

```text
∮ h(w) (-ζ'/ζ)(w) dw
```

という **一つの固定 holomorphic weight `h`** を持つ outer contour integral へそのまま統合できない。

この checkpoint で「outer contour 化」を主張しない。

必要なら概念名として、

```text
MirrorFrozenWeightObstruction
```

を doc comment / structure で置いてよいが、偽の impossibility theorem を証明する必要はない。

次段階では、

1. zero-dependent local weights を fixed boundary data に変換する追加 identity があるか、
2. あるいは completed-zeta / explicit-formula / CFBRC q2 から同じ radial mass を別経路で供給できるか、

を監査する。

---

## 13. 今回やらないこと

```text
single outer contour equality
argument principle の再実装
critical strip での finite PHZ convergence
explicit formula
Hadamard product
Li / Weil positivity
mirror multiplicity invariance の全面証明
ThreeElement interaction assimilation
SecondMomentDefect = 0
HorizontalEnergy = 0
RiemannHypothesis
```

特に、

```text
NormalizedMirrorFrozenRadialContourMass
  = NormalizedCenteredSecondContourMass.real
```

を無条件に証明してはならない。

これは PPW-016 の identity により `HorizontalEnergy = 0` を強制し、本質的に finite-window RH condition そのものになる。

---

## 14. Stop conditions / audit warnings

1. `criticalMirror` centered state と CF2D `Vec.conj` を同一視しない。
2. `Complex.normSq` を holomorphic weight として contour theorem に投入しない。
3. mirror-frozen weight は analytic variable `w` には holomorphic だが、parameter `ρ` に critical mirror / conjugation dependence を含むことを忘れない。
4. zero-dependent local weights の有限和を single fixed-weight outer contour と呼ばない。
5. radial q2 preservation だけから horizontal coordinate がゼロとは結論しない。
6. `q2` mass と PPW-013 primeMirror Gap energy を termwise 同一視しない。
7. `SecondMomentDefect = 0` を independent theorem として仮定・証明しない。
8. この bridge は RH-equivalent missing estimate を解決するものではなく、その estimate を contour / CF2D 共通言語へ変換する audit bridge である。

---

## 15. Build / acceptance criteria

最低限:

```text
lake build DkMath.RH.CFBRC.PascalCriticalMirrorRadialContourCF2DBridge
lake build DkMath.RH
./lean-build.sh DkMath.RH.CFBRC.PascalCriticalMirrorRadialContourCF2DBridge
git diff --check
```

新規 module に

```text
sorry
axiom
admit
```

を追加しない。

必須 acceptance theorem 群:

```text
centeredComplex_eq_sub_criticalLineCenter
centeredComplex_criticalMirror_eq_neg_conj
centeredComplex_mul_criticalMirror_eq_neg_normSq

pascalMirrorFrozenRadialWeight_self
pascalZetaNormalizedMirrorFrozenRadialLocalCharge_eq

pascalCriticalMirrorZeroWindowNormalizedMirrorFrozenRadialContourMass_eq

pascalCenteredZeroCF2DState_q2_eq_normSq
pascalCenteredZeroCF2DState_q2_criticalMirror
pascalCriticalMirrorZeroWindowCF2DRadialMass_eq

pascalNormalizedMirrorFrozenRadialContourMass_eq_CF2DRadialMass

pascalSecondMomentDefect_eq_mirrorFrozenContour_sub_centeredContour_re
pascalMirrorFrozenContourDifference_eq_two_horizontalEnergy
```

`centeredComplex_criticalMirror_eq_neg_conj` が elaboration 上不便なら同等の componentwise theorem で代替可。ただし mirror-product `= -normSq` は必須。

---

## 16. PPW-017 の意味

PPW-016 では、RH に必要な horizontal defect が

```text
radial norm-square mass
minus
holomorphic centered-second contour moment
```

として露出した。

PPW-017 では radial 側について、critical mirror を frozen parameter とすることで、non-holomorphic `normSq` を直接 weight に使わず、

```text
local holomorphic weight
  ↓
weighted -ζ'/ζ circle charge
  ↓
radial normSq
  ↓
CF2D q2
```

という exact bridge を作る。

これにより finite-window defect は最終的に、

```text
mirror-frozen radial contour observable
minus
fixed centered-second contour observable
```

という二つの analytic quantities の差として読める。

同時に、radial side は DkMath の `Vec.q2` 保存量そのものとして読める。

したがって次段階 PPW-018 の研究 question は明確になる。

```text
zero-dependent mirror-frozen local weight を
zero list を直接参照しない fixed boundary / prime-side / completed-zeta data
へ変換できる exact identity は存在するか？
```

ここで初めて、explicit formula、Hadamard-type zero product、completed-zeta boundary identity、あるいは CFBRC q2 global conservation のどれが本当に radial mass provider になり得るかを比較監査する。
