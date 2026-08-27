# PPW-022 — centered Xi radial layer-cake / fixed outer-count integral bridge 実装指示

## 1. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-prime-mirror-energy-260807-v0
previous checkpoint: PPW-021 complete Green
previous implementation: ff2b73f964fafe82ce3ce23cf6f22f6922bf9147
Lean toolchain: v4.32.2
mathlib rev: 905b95818eb32af7874a58b427f50c1711a5e96c
```

PPW-021 までで centered Xi の fixed outer contour theory は次まで Green になった。

```text
centered Xi zero set = centered nontrivial zeta zero set
Xi intrinsic multiplicity = zeta multiplicity
closed centered disk zero Finset = PPW window centered image
boundary-safe radius は任意の閾値より外側に存在

fixed integrand:
  pascalCenteredXiNegLogDeriv = -Xi_c'/Xi_c

fixed holomorphic weight h に対して:
  one outer circle
    = finite principal-part residue sum
    = finite local-circle sum

h = 1:
  outer contour reads multiplicity count

h = z^2:
  outer contour reads centered complex second moment
```

特に PPW-021 は boundary-safe `R` について、概念的に

```text
(2πi)^(-1) ∮[-Xi_c'/Xi_c]
  = - M_R
```

および

```text
(2πi)^(-1) ∮[z^2 (-Xi_c'/Xi_c)]
  = - M2_R
```

を exact に実装した。

一方、PPW-016 / PPW-017 で horizontal energy を読むために必要な radial second moment

```text
Q_R = Σ_a m_a |a|^2
```

は、現状では zero Finset または zero-dependent mirror-frozen local weight を使って構成されている。

PPW-022 の目的は、`|z|^2` を holomorphic weight に偽装することではない。

**zero counting function の layer-cake identity を使い、`Q_R` を半径ごとの fixed Xi outer multiplicity count の積分へ変換する。**

到達目標は、boundary-safe `R` に対する zero-list-free RHS

```text
Q_R
  = R^2 * OuterCount(R)
      - ∫ r in 0..R, 2*r*OuterCount(r)
```

である。

ここで `OuterCount(r)` は `pascalCenteredXiOuterContourMass r` だけから定義する固定 Xi observable とする。unsafe radius では pointwise residue theorem は使えないが、固定 bounded interval 内の unsafe radius は有限集合に含まれるため Lebesgue interval integral では無視できる。

これは radial mass の **表現 bridge** であり、RH や horizontal-energy 消滅を証明する estimate ではない。

---

## 2. 新規 module

```text
DkMath.RH.CFBRC.PascalCenteredXiRadialLayerCakeOuterCountBridge
```

候補 file:

```text
lean/dk_math/DkMath/RH/CFBRC/PascalCenteredXiRadialLayerCakeOuterCountBridge.lean
```

推奨 import:

```lean
import DkMath.RH.CFBRC.PascalCenteredXiOuterContourResidueBridge
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
```

`Mathlib.MeasureTheory.Integral.Layercake` は pinned rev に存在する。ただし今回の対象は finite weighted zero set なので、まず explicit Finset proof を優先してよい。Mathlib の一般 layer-cake theorem を使うために weighted atomic measure を新設し、proof surface を不必要に広げないこと。

単体 Green 後に `DkMath/RH.lean` の PPW-021 import 直後へ公開 import を追加する。

---

## 3. 数学的中心式

fixed `R > 0` と、その closed disk 内の centered Xi zeros `a` を multiplicity `m_a` 付きで考える。

```text
M_R = Σ_a m_a
Q_R = Σ_a m_a |a|^2
```

半径 `r` までの multiplicity count を

```text
N(r) = Σ_{|a| ≤ r} m_a
```

とする。

各 `a` について `|a| ≤ R` なら

```text
∫ r in 0..R, 2*r * 1_{|a| ≤ r}
  = R^2 - |a|^2
```

である。

有限和を取れば

```text
∫ r in 0..R, 2*r*N(r)
  = R^2*M_R - Q_R
```

従って

```text
Q_R
  = R^2*M_R
      - ∫ r in 0..R, 2*r*N(r)
```

となる。

PPW-021 より boundary-safe `r` では

```text
N(r)
  = - Re ((2πi)^(-1) * pascalCenteredXiOuterContourMass r)
```

である。

fixed `R` 内で boundary-unsafe になり得る正の半径は、`pascalCenteredXiZeroDiskFinset R` に属する zero の距離

```text
{ dist a 0 | a ∈ pascalCenteredXiZeroDiskFinset R }
```

に含まれるため有限である。

よって radial interval integral 内では `N(r)` を fixed Xi outer count へ almost-everywhere 置換できる。

---

## 4. Phase A — Xi intrinsic radial second moment

PPW-020 には Xi disk intrinsic multiplicity と holomorphic second momentはあるが、radial moment は window 側を主としている。

まず Xi disk 自身の radial second moment を定義する。

候補:

```lean
noncomputable def pascalCenteredXiZeroDiskRadialSecondMoment
    (R : ℝ) : ℝ :=
  ∑ z ∈ pascalCenteredXiZeroDiskFinset R,
    (pascalCenteredXiZeroMultiplicity z : ℝ) * Complex.normSq z
```

必須 transport theorem:

```lean
@[simp] theorem pascalCenteredXiZeroDiskRadialSecondMoment_eq_window
    (R : ℝ) :
    pascalCenteredXiZeroDiskRadialSecondMoment R =
      pascalCriticalMirrorZeroWindowRadialSecondMoment R
```

proof は PPW-020 の

```text
image_pascalCenterZeroShift_window_eq_centeredXiDisk
pascalCenteredXiZeroMultiplicity_sub_center_eq_riemannZetaZeroMultiplicity
```

を使う。

`Complex.normSq (s - criticalLineCenter)` は既存 window radial second moment と同じ量であることを exact に合わせる。

この phase では contour を使わない。

---

## 5. Phase B — fixed outer disk に対する finite layer count

`R` を固定したとき、layer-cake proof は disk `R` 内の有限 zero Finsetだけで構成すると扱いやすい。

候補:

```lean
noncomputable def pascalCenteredXiZeroDiskLayerCount
    (R r : ℝ) : ℝ :=
  ∑ z ∈ pascalCenteredXiZeroDiskFinset R,
    if dist z 0 ≤ r then
      (pascalCenteredXiZeroMultiplicity z : ℝ)
    else 0
```

`0 ≤ r ≤ R` では、これは radius `r` の intrinsic closed-disk multiplicity と一致する。

必須 theorem:

```lean
theorem pascalCenteredXiZeroDiskLayerCount_eq_multiplicity
    {R r : ℝ} (hr0 : 0 ≤ r) (hrR : r ≤ R) :
    pascalCenteredXiZeroDiskLayerCount R r =
      (pascalCenteredXiZeroDiskMultiplicity r : ℝ)
```

証明の要点:

```text
z ∈ disk R
かつ dist z 0 ≤ r
  ↔
z ∈ disk r
```

を membership theorem から示し、Finset sum を一致させる。

`R` 自体が boundary-safe である必要はない。

strongly recommended:

```lean
theorem pascalCenteredXiZeroDiskLayerCount_nonneg
    (R r : ℝ) :
    0 ≤ pascalCenteredXiZeroDiskLayerCount R r
```

```lean
theorem pascalCenteredXiZeroDiskLayerCount_mono
    (R : ℝ) : Monotone (pascalCenteredXiZeroDiskLayerCount R)
```

後者は必須ではないが、step-count semantics の監査に有用。

---

## 6. Phase C — one-zero layer integral

ここが layer-cake の最小解析核。

`z ∈ pascalCenteredXiZeroDiskFinset R`、`0 ≤ R` とする。

`d := dist z 0` と置けば `0 ≤ d ≤ R`。

必須 helper の概形:

```lean
theorem intervalIntegral_two_mul_radius_indicator_ge_dist
    {R : ℝ} (hR : 0 ≤ R)
    {z : ℂ}
    (hz : z ∈ pascalCenteredXiZeroDiskFinset R) :
    (∫ r in 0..R,
      2 * r * (if dist z 0 ≤ r then (1 : ℝ) else 0)) =
      R ^ 2 - (dist z 0) ^ 2
```

statement の indicator 表現は変更してよい。

例えば次のどちらでもよい。

```text
if dist z 0 ≤ r then 1 else 0
```

または

```text
(Set.Ici (dist z 0)).indicator (fun _ => 1) r
```

proof route は direct finite calculus を推奨する。

```text
1. d ∈ [0,R]
2. interval を 0..d と d..R に分割
3. 0..d 側は indicator = 0 a.e.
4. d..R 側は indicator = 1 a.e.
5. ∫ 2r dr = R^2 - d^2
```

endpoint `r = d` の値は Lebesgue interval integral に影響しないため、`≤` / `<` の差を無理に pointwise 揃えなくてよい。

pinned Mathlib の exact theorem 名は実装開始時に `#check` すること。`intervalIntegral` の endpoint convention は `Ioc` ベースなので、endpoint singletons の扱いを暗黙に推測しない。

また `Complex.normSq z = (dist z 0)^2` の bridge は既存 `Complex.normSq` / norm simp API を優先して証明する。

---

## 7. Phase D — finite layer-cake identity

Phase C を Finset sum へ上げる。

まず weighted integrand:

```lean
noncomputable def pascalCenteredXiZeroDiskLayerIntegrand
    (R r : ℝ) : ℝ :=
  2 * r * pascalCenteredXiZeroDiskLayerCount R r
```

必要なら count の定義展開後、有限和と integral の交換を `intervalIntegral.integral_finset_sum` 相当の API または `integral_finset_sum` 系で処理する。

必須 theorem:

```lean
theorem integral_pascalCenteredXiZeroDiskLayerIntegrand_eq
    {R : ℝ} (hR : 0 ≤ R) :
    (∫ r in 0..R,
      pascalCenteredXiZeroDiskLayerIntegrand R r) =
      R ^ 2 * (pascalCenteredXiZeroDiskMultiplicity R : ℝ) -
        pascalCenteredXiZeroDiskRadialSecondMoment R
```

従って radial form:

```lean
theorem pascalCenteredXiZeroDiskRadialSecondMoment_eq_layerCake
    {R : ℝ} (hR : 0 ≤ R) :
    pascalCenteredXiZeroDiskRadialSecondMoment R =
      R ^ 2 * (pascalCenteredXiZeroDiskMultiplicity R : ℝ) -
        (∫ r in 0..R,
          pascalCenteredXiZeroDiskLayerIntegrand R r)
```

これが PPW-022 の第一 load-bearing endpoint。

この theorem は pure finite-zero accounting であり、RH を含まない。

---

## 8. Phase E — fixed Xi outer count observable

PPW-021 の unweighted outer contour を実数 multiplicity count として正規化する。

候補:

```lean
noncomputable def pascalCenteredXiOuterCount
    (r : ℝ) : ℝ :=
  -((2 * Real.pi * Complex.I)⁻¹ *
      pascalCenteredXiOuterContourMass r).re
```

boundary-safe `r` では PPW-021 より exact に intrinsic multiplicity count と一致する。

必須 theorem:

```lean
@[simp] theorem pascalCenteredXiOuterCount_eq_zeroDiskMultiplicity
    {r : ℝ} (hr : IsPascalCenteredXiBoundarySafeRadius r) :
    pascalCenteredXiOuterCount r =
      (pascalCenteredXiZeroDiskMultiplicity r : ℝ)
```

符号監査:

PPW-021 は

```text
(2πi)^(-1) * OuterContourMass(r)
  = - multiplicity(r)
```

なので `pascalCenteredXiOuterCount` には先頭の minus が必要。

ここを逆にしない。

`pascalCenteredXiOuterCount r` の定義自体は全 `r` に total でよいが、unsafe radius で multiplicity theorem を主張しない。

---

## 9. Phase F — bounded interval 内の forbidden radii

fixed outer radius `R` に対し、disk 内 zero が作る半径集合を Finset にする。

候補:

```lean
noncomputable def pascalCenteredXiForbiddenRadii
    (R : ℝ) : Finset ℝ :=
  (pascalCenteredXiZeroDiskFinset R).image (fun z => dist z 0)
```

必須 theorem:

```lean
theorem isBoundarySafe_of_pos_le_not_mem_forbiddenRadii
    {R r : ℝ}
    (hr0 : 0 < r) (hrR : r ≤ R)
    (hr : r ∉ pascalCenteredXiForbiddenRadii R) :
    IsPascalCenteredXiBoundarySafeRadius r
```

proof:

zero `z` が sphere radius `r` 上にあると仮定すれば、`r ≤ R` なので `z` は disk `R` に入り、`dist z 0 = r` が forbidden Finset に入って矛盾する。

strongly recommended:

```lean
theorem finite_boundaryUnsafeRadii_in_Icc
    (R : ℝ) :
    {r : ℝ | r ∈ Set.Icc 0 R ∧
      ¬ IsPascalCenteredXiBoundarySafeRadius r}.Finite
```

ただし `r = 0` は `IsPascalCenteredXiBoundarySafeRadius` の定義上自動的に unsafe なので、集合は

```text
{0} ∪ forbidden radii
```

に含めればよい。

この finite exceptional set は Lebesgue measure zero である。

---

## 10. Phase G — layer count と fixed outer count の a.e. equality

fixed `R > 0` の interval `0..R` 上で、Phase F の finite exceptional radii を除けば各 `r` は boundary-safe。

さらに `0 < r ≤ R` では Phase B により

```text
LayerCount(R,r)
  = ZeroDiskMultiplicity(r)
```

であり、Phase E により

```text
OuterCount(r)
  = ZeroDiskMultiplicity(r)
```

である。

従って almost everywhere:

```text
LayerCount(R,r) = OuterCount(r)
```

となる。

必須 theorem は weighted integrand の形で直接置いてよい。

候補:

```lean
theorem pascalCenteredXiZeroDiskLayerIntegrand_ae_eq_outerCountIntegrand
    {R : ℝ} (hR : 0 < R) :
    (fun r => pascalCenteredXiZeroDiskLayerIntegrand R r) =ᵐ[
      MeasureTheory.volume.restrict (Set.Icc 0 R)]
      (fun r => 2 * r * pascalCenteredXiOuterCount r)
```

または `Set.Ioc 0 R` / `Set.uIoc` に合わせてもよい。

重要なのは pointwise theorem にしないこと。

unsafe radii では raw outer contour の integrand が boundary zero を通るため、PPW-021 の residue formula は適用できない。finite measure-zero set を a.e. で落とすのが正しい処理である。

この a.e. theorem を使い、outer count weighted integrand の `IntervalIntegrable` を layer integrand から transport してよい。

strongly recommended:

```lean
theorem intervalIntegrable_two_mul_radius_mul_pascalCenteredXiOuterCount
    {R : ℝ} (hR : 0 < R) :
    IntervalIntegrable
      (fun r => 2 * r * pascalCenteredXiOuterCount r)
      MeasureTheory.volume 0 R
```

独立に circle integral の radius dependence の measurability を証明する必要はない。a.e. congruence から integrability を輸送するほうが安全。

---

## 11. Phase H — radial mass を fixed Xi outer-count integral へ置換

Phase D と Phase G を合成する。

まず multiplicity endpoint をまだ Finset count のまま残した版:

```lean
theorem pascalCenteredXiZeroDiskRadialSecondMoment_eq_outerCountIntegral
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiZeroDiskRadialSecondMoment R =
      R ^ 2 * (pascalCenteredXiZeroDiskMultiplicity R : ℝ) -
        (∫ r in 0..R,
          2 * r * pascalCenteredXiOuterCount r)
```

次に endpoint multiplicity も Phase E で outer contour count へ置換する。

PPW-022 の主 theorem:

```lean
theorem pascalCenteredXiZeroDiskRadialSecondMoment_eq_fixedXiOuterCountLayerCake
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiZeroDiskRadialSecondMoment R =
      R ^ 2 * pascalCenteredXiOuterCount R -
        (∫ r in 0..R,
          2 * r * pascalCenteredXiOuterCount r)
```

これは今回の第二 load-bearing endpoint。

RHS の theorem-facing data は

```text
pascalCenteredXiKernel
pascalCenteredXiNegLogDeriv
pascalCenteredXiOuterContourMass
R
```

のみであり、個別 zero parameter や mirror-frozen weight を含まない。

さらに PPW window radial moment へ transport する。

必須 theorem:

```lean
theorem pascalCriticalMirrorZeroWindowRadialSecondMoment_eq_fixedXiOuterCountLayerCake
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCriticalMirrorZeroWindowRadialSecondMoment R =
      R ^ 2 * pascalCenteredXiOuterCount R -
        (∫ r in 0..R,
          2 * r * pascalCenteredXiOuterCount r)
```

これで PPW-017 の radial `Q_R` は、zero-dependent frozen contour を theorem statement から除いた fixed Xi representation を持つ。

---

## 12. CF2D q2 への再接続

PPW-017 には

```text
pascalCriticalMirrorZeroWindowCF2DRadialMass
pascalCriticalMirrorZeroWindowCF2DRadialMass_eq
```

があり、window radial second moment と CF2D `q2` mass が exact に一致する。

従って strongly recommended:

```lean
theorem pascalCriticalMirrorZeroWindowCF2DRadialMass_eq_fixedXiOuterCountLayerCake
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCriticalMirrorZeroWindowCF2DRadialMass R =
      R ^ 2 * pascalCenteredXiOuterCount R -
        (∫ r in 0..R,
          2 * r * pascalCenteredXiOuterCount r)
```

これにより

```text
CF2D q2 radial mass
      ↕ exact
fixed Xi outer-count layer-cake
```

という zero-list-free theorem-facing bridge が得られる。

これは PPW-022 の重要な統合点だが、新しい q2 保存則や RH collision theorem は今回追加しない。

---

## 13. PPW-023 へ残すもの

PPW-021 で holomorphic centered second moment は既に

```text
NormalizedSecondOuterContour(R)
  = - M2_R
```

として fixed Xi outer circle から読める。

PPW-022 が Green になれば radial side も

```text
Q_R
  = R^2 * OuterCount(R)
      - ∫ 2r*OuterCount(r)
```

として fixed Xi family of outer circles から読める。

この二本をまとめた

```text
FullFixedXiSecondMomentDefectFunctional
```

の定義・API 化は **PPW-023** に残す。

PPW-023 の概念式は

```text
SecondMomentDefect(R)
  = [R^2 * OuterCount(R)
       - ∫_0^R 2r*OuterCount(r) dr]
    - Re[NormalizedSecondOuterContour(R)]
```

となる。

ただし PPW-022 でこの式を one-off theorem として確認する程度は可。新しい `Defect = 0` provider や RH closure は置かない。

---

## 14. pinned Mathlib API audit

current branch の `lake-manifest.json` は mathlib

```text
905b95818eb32af7874a58b427f50c1711a5e96c
```

を pin している。

この rev には

```text
Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
Mathlib.MeasureTheory.Integral.Layercake
```

が存在する。

`Layercake.lean` には一般 Cavalieri / layer-cake theorem があるが、今回の multiplicity-weighted finite zero set にそのまま適用するには weighted atomic measure の構築が必要になる可能性がある。

推奨優先順位:

```text
Route A:
  explicit Finset + interval integral
  → 最優先

Route B:
  finite weighted atomic measure + general Layercake theorem
  → Route A より proof surface が明確に短くなる場合のみ
```

実装開始時に local toolchain で次を確認すること。

```lean
#check intervalIntegral.integral_finset_sum
#check intervalIntegral.integral_add
#check intervalIntegral.integral_congr_ae
#check IntervalIntegrable.congr_ae
#check Set.Finite.measure_zero
```

名称・namespace が異なる場合は pinned source の実名に従う。

one-zero integral については、既存の polynomial primitive theorem が使えるなら再利用する。そうでなければ `2*r` の原始関数 `r^2` を `intervalIntegral.integral_eq_sub_of_hasDerivAt` 系 API で処理する。

---

## 15. 今回やらないこと

PPW-022 では以下を実装しない。

```text
|z|^2 を holomorphic contour weight とすること
unsafe radius で outer count = multiplicity と主張すること
boundary zero の totalized logDeriv 値を residue とみなすこと
radial moment = single z^2 outer contour
SecondMomentDefect = 0
HorizontalEnergy = 0
primeMirror window energy = 0
RiemannHypothesis
Li / Weil positivity theorem
explicit formula positivity estimate
prime-side radial estimate
moving-line / ThreeElement RH closure
```

また layer-cake identity 自体を「新しい independent analytic estimate」と表現しない。

これは同じ Xi zero data の exact re-expression である。

---

## 16. Stop conditions / audit warnings

1. `|z|^2` は non-holomorphic のまま扱う。holomorphic weight に偽装しない。
2. multiplicity を落とさない。zero count は常に intrinsic Xi multiplicity 付き。
3. `pascalCenteredXiOuterCount r = multiplicity(r)` は boundary-safe `r` でのみ pointwise 使用する。
4. unsafe radius は bounded interval 内で有限集合として除外し、a.e. equality に落とす。
5. `r = 0` は boundary-safe predicate の positivity 条件を満たさない。一点集合として measure-zero 処理するか別 case にする。
6. fixed outer radius `R` の forbidden-radii Finset で制御できるのは `0 ≤ r ≤ R` の範囲。外側の半径へ無条件に拡張しない。
7. layer count の `≤` と `<` の差は jump radius 上だけ。interval integral では measure-zero として処理し、無意味な pointwise rewrite を増やさない。
8. outer contour の radius dependence を独立に continuous / measurable と仮定しない。必要なら a.e. congruence から integrability を輸送する。
9. boundary-safe `R` では disk zero は open ball 内に入るが、内側のすべての `r` が safe とは限らない。finite exceptional radii を必ず残す。
10. PPW-021 の normalized outer contour sign は `-multiplicity`。positive count を定義するとき minus を一つ入れる。
11. radial layer-cake formula が Green でも `Q_R` の新しい inequality は得られない。
12. fixed Xi representation が得られても `Q_R + Re(M2_R) = 0` は出ない。
13. `SecondMomentDefect = 0` と同値な provider を別名で completion 条件にしない。
14. RH を示す theorem は今回の acceptance に含めない。

---

## 17. Build / acceptance criteria

最低限:

```text
lake build DkMath.RH.CFBRC.PascalCenteredXiRadialLayerCakeOuterCountBridge
lake build DkMath.RH
./lean-build.sh DkMath.RH.CFBRC.PascalCenteredXiRadialLayerCakeOuterCountBridge
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
pascalCenteredXiZeroDiskRadialSecondMoment
pascalCenteredXiZeroDiskRadialSecondMoment_eq_window

pascalCenteredXiZeroDiskLayerCount
pascalCenteredXiZeroDiskLayerCount_eq_multiplicity

one-zero layer integral helper
integral_pascalCenteredXiZeroDiskLayerIntegrand_eq
pascalCenteredXiZeroDiskRadialSecondMoment_eq_layerCake

pascalCenteredXiOuterCount
pascalCenteredXiOuterCount_eq_zeroDiskMultiplicity

pascalCenteredXiForbiddenRadii
isBoundarySafe_of_pos_le_not_mem_forbiddenRadii

layer integrand = outer-count integrand almost everywhere on 0..R

pascalCenteredXiZeroDiskRadialSecondMoment_eq_fixedXiOuterCountLayerCake
pascalCriticalMirrorZeroWindowRadialSecondMoment_eq_fixedXiOuterCountLayerCake
```

### strongly recommended

```text
pascalCenteredXiZeroDiskLayerCount_nonneg
pascalCenteredXiZeroDiskLayerCount_mono

finite_boundaryUnsafeRadii_in_Icc
intervalIntegrable_two_mul_radius_mul_pascalCenteredXiOuterCount

pascalCriticalMirrorZeroWindowCF2DRadialMass_eq_fixedXiOuterCountLayerCake

PPW-021 second outer contour と組み合わせた defect representation の one-off theorem
```

helper 名は実装都合で変更可。

completion の本質は、radial second moment の最終 theorem statement から個別 zero weight / mirror-frozen weight を除き、固定 Xi の outer count family のみで表現することにある。

---

## 18. PPW-022 完了条件の意味

PPW-021 までで、holomorphic centered second moment は一つの fixed outer circle へ閉じた。

PPW-022 では non-holomorphic radial momentを、holomorphic weightへ直接変換せず、**zero counting の半径積分**へ一段持ち上げる。

```text
fixed Xi
  ↓
-Xi_c'/Xi_c
  ↓
outer multiplicity count N(r)
  ↓
layer-cake in radius
  ↓
Q_R = Σ m_a |a|^2
  ↓
CF2D q2 radial mass
```

この経路で重要なのは、`|z|^2` を contour integrand に入れていないこと。

代わりに各 radius の argument count だけを使う。

PPW-022 が Green になれば、PPW-016 の second-moment decomposition の両側が fixed Xi data だけで記述可能になる。

```text
radial Q_R:
  fixed Xi outer-count family

holomorphic M2_R:
  fixed Xi z^2 outer contour
```

そこで PPW-023 では初めて

```text
FullFixedXiSecondMomentDefectFunctional
```

を一つの theorem-facing object として定義し、

```text
FullFixedXiDefect(R) = 2 * HorizontalEnergy(R)
```

を exact に固定する。

その先が本当の analytic frontier である。

```text
Prime / explicit formula
CF2D q2 / ThreeElement
global Xi symmetry / moment identity
```

のどれを使うにせよ、PPW-023 以降で必要なのは **defect を独立に制約する新しい identity / estimate** であり、contour bookkeeping の追加ではない。
