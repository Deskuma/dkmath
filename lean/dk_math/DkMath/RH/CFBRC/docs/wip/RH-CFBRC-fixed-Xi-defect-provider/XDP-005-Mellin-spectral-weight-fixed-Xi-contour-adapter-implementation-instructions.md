# XDP-005 — Mellin spectral weight / fixed-Xi contour adapter Codex 実装指示書

作成日: 2026-08-12

## 0. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-fixed-Xi-defect-provider-260812-v0
Lean: v4.32.2
mathlib: repository pinned revision
```

作業 directory:

```text
lean/dk_math
```

XDP-001〜XDP-004 は Green 完了済みである。

本 phase の目的は、XDP-004 の compact Mellin admissibility と、既に存在する centered-Xi の generic weighted outer-contour residue theorem を接続することである。

XDP-005 では、spectral hard cutoff を Mellin transform と exact に同一視しない。
また finite zero set 上の値だけを補間して classical global zero sum に投入する route も採らない。

理由は、global explicit-formula zero-side が全零点和である場合、window 内の有限点で値を合わせるだけでは window 外零点の寄与が残るためである。

代わりに、既存 fixed-Xi outer contour が boundary-safe radius 内の零点だけを residue で exact に切り出せることを利用する。

XDP-005 の主構造は次である。

```text
positive compact Mellin data h
        ↓
H_h(z) := mellin h (1/2 + z)
        ↓
H_h is entire / globally differentiable
        ↓
existing fixed-Xi weighted contour theorem
        ↓
finite weighted centered-Xi zero sum inside safe radius
```

この段階では `H_h(z) = z^2`、hard cutoff realization、Guinand--Weil explicit formula、prime-side formula、defect vanishing、RH は証明しない。

---

# 1. 必ず読む既存正本

最初に次を読むこと。

```text
DkMath/Analysis/MellinCriticalMirror.lean
DkMath/Analysis/MellinCompactSupport.lean
DkMath/RH/CFBRC/MellinCenteredMirrorAdapter.lean
DkMath/RH/CFBRC/PascalCenteredXiSafeRadiusAnnulusBridge.lean
DkMath/RH/CFBRC/PascalCenteredXiOuterContourResidueBridge.lean
DkMath/RH/CFBRC/PascalCenteredXiWeilMirrorDefectBridge.lean
DkMath/RH/CFBRC/PascalCenteredXiFixedSecondMomentDefectBridge.lean
```

XDP-004 result report も読むこと。

```text
DkMath/RH/CFBRC/docs/wip/RH-CFBRC-fixed-Xi-defect-provider/
  XDP-004-Safe-radius-annulus-and-compact-Mellin-admissibility-result.md
```

実 repository head の theorem 名・signature を正本とする。

---

# 2. 既存 contour Core の再利用

`PascalCenteredXiOuterContourResidueBridge.lean` には既に generic weighted theorem がある。

```lean
pascalCenteredXiWeightedOuterContourMass_eq
pascalCenteredXiNormalizedWeightedOuterContourMass_eq
```

概念形は次である。

```lean
theorem pascalCenteredXiWeightedOuterContourMass_eq
    {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiWeightedOuterContourMass H R =
      -(2 * Real.pi * Complex.I) *
        pascalCenteredXiZeroDiskWeightedMoment H R
```

この theorem を再証明しない。

XDP-005 で必要なのは、Mellin transform 由来の spectral weight `H_h` がこの `Differentiable ℂ H` contract を満たすことだけである。

---

# 3. Route selection — Route C を優先する理由

XDP-004 handoff では Route I（finite spectral interpolation）と Route C（fixed-Xi contour transport）が候補だった。

XDP-005 では Route C を primary とする。

理由:

1. finite interpolation は window 内零点で desired value を合わせても、classical global zero sum の window 外寄与を自動では消さない。
2. fixed-Xi outer contour は既に safe radius 内の有限零点集合を exact に residue 抽出する。
3. generic holomorphic weight `H` を受け取る theorem が Green 済み。
4. XDP-004 は compact positive support から Mellin convergence を任意 `s : ℂ` で供給済み。
5. 従って残る最小 Gap は Mellin spectral weight の holomorphicity / differentiability である。

finite interpolation route を否定する theorem を作る必要はない。ただし「window 内補間だけで global zero-side identity が得られる」とは docstring / report で主張禁止。

---

# 4. 新規 generic Analysis Core

第一候補 module:

```text
DkMath/Analysis/MellinCompactSupportHolomorphic.lean
```

namespace:

```lean
namespace DkMath.Analysis
```

import 第一候補:

```lean
import DkMath.Analysis.MellinCompactSupport
import Mathlib.Analysis.MellinTransform
import Mathlib.Tactic
```

不要な RH / Xi module を generic Analysis Core から import しない。

## 4.1 centered spectral weight

Mellin parameter shift を generic に定義してよい。

第一候補:

```lean
noncomputable def centeredMellinSpectralWeight
    (h : ℝ → ℂ) (z : ℂ) : ℂ :=
  mellin h ((1 : ℂ) / 2 + z)
```

もし `criticalLineCenter` を使うと RH namespace 依存になる場合、generic Core では `(1 : ℂ) / 2` を使う。

CFBRC 側で既存 `criticalLineCenter` との equality を薄く接続してよい。

---

# 5. 最重要 Gate A — compact support から Mellin entire / differentiable

XDP-004 で Green の hypotheses を継承する。

概念形:

```text
0 < a
 a ≤ b
support h ⊆ Icc a b
ContinuousOn h (Icc a b)
```

ただし `Differentiable ℂ (fun s => mellin h s)` を証明するには `ContinuousOn` だけで十分かを最初に audit すること。

Mathlib の候補 API:

```lean
mellin_differentiableAt_of_isBigO_rpow
MellinConvergent
```

pinned Mathlib の exact signature を `#check` / source grep で確認する。

### 5.1 第一目標

可能なら次を generic theorem として Green 化する。

```lean
theorem differentiable_mellin_of_support_subset_Icc_pos
    {h : ℝ → ℂ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support h ⊆ Set.Icc a b)
    (hcont : ContinuousOn h (Set.Icc a b)) :
    Differentiable ℂ (fun s : ℂ => mellin h s) := by
  ...
```

signature は Mathlib proof ergonomics に合わせて調整可。

### 5.2 Continuity が不足する場合

もし Mathlib の Mellin holomorphicity theorem が local integrability や zero/infinity での `IsBigO` 条件を要求し、`ContinuousOn` からの transport が過度に重い場合は、次の順で補助 theorem を分離する。

```lean
locallyIntegrableOn_pos_of_support_subset_Icc_pos
isBigO_zero_of_support_away_from_zero
isBigO_atTop_of_compact_support
mellin_differentiableAt_of_support_subset_Icc_pos
```

compact support が `0 < a` から zero 近傍で identically zero になること、`b < ∞` から infinity 近傍で identically zero になることを利用する。

不必要な具体的 rpow exponent の最適化はしない。Mathlib theorem が要求する admissible exponent を通す最小 statement を選ぶ。

### 5.3 Gate A の停止条件

もし XDP-004 の `ContinuousOn` contract だけでは既存 Mathlib API から global differentiability を安全に出せない場合、statement を無理に強行しない。

その場合は必要な追加 regularity（例 `Continuous`, `ContDiff`, `HasCompactSupport` + smoothness 等）を exact に report し、その追加 hypothesis で theorem を Green 化する。

**数学的 statement を偽に強めない。**

---

# 6. Gate B — centered spectral weight の differentiability

Gate A が Green になれば、shift composition だけで次を証明する。

```lean
theorem differentiable_centeredMellinSpectralWeight_of_support_subset_Icc_pos
    ... :
    Differentiable ℂ (centeredMellinSpectralWeight h) := by
  ...
```

これは新しい Mellin 積分計算をしない。

`Differentiable.comp` / `fun_prop` 等で薄く閉じる。

必要なら pointwise:

```lean
DifferentiableAt ℂ (centeredMellinSpectralWeight h) z
```

も expose してよい。

---

# 7. Gate C — XDP-003 mirror contract を spectral weight 上へ固定

XDP-003 / XDP-004 の theorem を再利用し、centered spectral weights が multiplicative mirror と critical reflection で対応することを固定する。

概念形:

```lean
centeredMellinSpectralWeight (mellinCriticalMirror h) z
  = starRingEnd ℂ
      (centeredMellinSpectralWeight h (-(starRingEnd ℂ) z))
```

実際の右辺 parameter は XDP-003 Green theorem の normal form を優先する。

既存 theorem:

```lean
mellin_mellinCriticalMirror_centered
mellin_mellinCriticalMirror_centered_of_support_subset_Icc_pos
```

を直接利用する。

support hypotheses から convergence を再証明しない。

候補 theorem:

```lean
centeredMellinSpectralWeight_mirror
```

または既存 theorem の alias が不要なら新定理を増やさなくてよい。

目的は後の CFBRC contour bridge で readable な API を一つ持つこと。

---

# 8. 新規 CFBRC bridge module

第一候補:

```text
DkMath/RH/CFBRC/PascalCenteredXiMellinWeightedOuterContourBridge.lean
```

namespace:

```lean
namespace DkMath.RH.CFBRCProjection
```

import 第一候補:

```lean
import DkMath.Analysis.MellinCompactSupportHolomorphic
import DkMath.RH.CFBRC.MellinCenteredMirrorAdapter
import DkMath.RH.CFBRC.PascalCenteredXiOuterContourResidueBridge
import Mathlib.Tactic
```

---

# 9. Gate D — Mellin weight を fixed-Xi contour へ載せる

centered spectral weight を既存 generic contour theorem へ直接渡す。

候補 theorem:

```lean
theorem pascalCenteredXiMellinWeightedOuterContourMass_eq
    {h : ℝ → ℂ} {a b R : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support h ⊆ Set.Icc a b)
    (hcont : ContinuousOn h (Set.Icc a b))
    (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiWeightedOuterContourMass
        (DkMath.Analysis.centeredMellinSpectralWeight h) R =
      -(2 * Real.pi * Complex.I) *
        pascalCenteredXiZeroDiskWeightedMoment
          (DkMath.Analysis.centeredMellinSpectralWeight h) R := by
  ...
```

もし Gate A で追加 regularity が必要になった場合、同じ hypothesis をここへ正直に持ち上げる。

proof は必ず既存

```lean
pascalCenteredXiWeightedOuterContourMass_eq
```

へ `Differentiable` proof を供給して閉じる。

principal part / residue / Cauchy integral を再実装しない。

normalized version も置く。

```lean
theorem pascalCenteredXiNormalizedMellinWeightedOuterContourMass_eq
    ... :
    (2 * Real.pi * Complex.I)⁻¹ *
      pascalCenteredXiWeightedOuterContourMass
        (DkMath.Analysis.centeredMellinSpectralWeight h) R =
      -pascalCenteredXiZeroDiskWeightedMoment
        (DkMath.Analysis.centeredMellinSpectralWeight h) R := by
  ...
```

これは XDP-005 の主 endpoint である。

---

# 10. Gate E — zero-window transport は generic に可能なら追加

既存 PPW では centered Xi zero disk と `pascalCriticalMirrorZeroWindow` の対応が Green である。

もし generic weight transport を短く実装できるなら、次の形を追加してよい。

概念形:

```text
Σ_{a in centered Xi zero disk} mult(a) * H(a)
=
Σ_{ρ in nontrivial zero window} mult(ρ) * H(centeredComplex ρ)
```

候補 theorem:

```lean
pascalCenteredXiZeroDiskWeightedMoment_eq_windowWeightedMoment
```

ただし既存 finset equivalence / multiplicity transport が specialized second moment 用にしか整備されておらず、この generic transport が XDP-005 を大幅に膨らませる場合は **必須ではない**。

その場合は centered Xi zero-disk weighted moment を endpoint としてよい。

XDP-005 の本質は Mellin weight を fixed contour に合法的に載せることである。

---

# 11. Gate F — public root import

新規 generic Core が Green なら:

```text
DkMath/Analysis.lean
```

へ import を追加。

新規 CFBRC bridge が Green なら:

```text
DkMath/RH.lean
```

へ import を追加。

既存 root import order を壊さない。

---

# 12. この phase で禁止する主張

XDP-005 は次を証明しない。

1. `centeredMellinSpectralWeight h z = z ^ 2`
2. hard radial spectral indicator が Mellin transform である
3. finite zero-window indicator が Mellin transform である
4. arbitrary finite interpolation が compact Mellin transform class で可能
5. window 内 interpolation だけで global explicit-formula zero sum が閉じる
6. Guinand--Weil explicit formula
7. Li criterion
8. Weil positivity criterion
9. prime-side equality
10. `pascalCenteredXiFixedSecondMomentDefectFunctional R ≤ 0`
11. defect vanishing
12. `RiemannHypothesis`

`Mellin weighted contour = finite weighted zero sum` は representation bridge であり provider theorem ではない。

---

# 13. XDP-005 の数学的意味

XDP-005 が Green になると、二つの既存 machinery が初めて exact に合流する。

```text
XDP-003/004:
positive compact test data
→ Mellin transform
→ centered critical-mirror symmetry

PPW/Xi contour:
entire spectral weight
→ fixed outer Xi contour
→ finite zero residue sum
```

合流後:

```text
positive compact h
→ centered Mellin spectral weight H_h
→ fixed Xi weighted contour
→ finite weighted centered zero sum
```

この route は hard cutoff を Mellin transform へ変換しない。
Safe radius の finite spectral localization は contour geometry が担当し、Mellin transform は holomorphic weight の供給だけを担当する。

この責務分離を保持すること。

---

# 14. XDP-006 handoff candidate

XDP-005 が Green なら、次は centered second-weight

$$
z^2
$$

を Mellin spectral weights からどう回収するかを監査する。

候補 route:

```text
Route A: approximate identity near x = 1
  Mellin transforms → 1 uniformly on compact spectral sets
  Euler/log derivatives → polynomial spectral weights

Route B: fixed contour 上だけで uniform approximation
  H_n → z^2 on |z| = R
  circle integral convergence で second contour を回収

Route C: avoid z^2 realization and derive an equivalent weighted defect family
  whose sign/limit controls the existing second defect
```

XDP-006 では、この三候補を比較し、一つだけ primary route を選ぶ。

特に、**全複素平面で `H_h = z^2` を要求しない**。
Fixed radius contour 上または有限 zero disk 上で十分な convergence / approximation があればよい可能性を優先評価する。

---

# 15. 検証 Gate

最低限:

```bash
cd lean/dk_math

lake env lean DkMath/Analysis/MellinCompactSupportHolomorphic.lean
lake env lean DkMath/RH/CFBRC/PascalCenteredXiMellinWeightedOuterContourBridge.lean

./lean-build.sh
./lean-test.sh
git diff --check
```

新規 module に次を入れない。

```text
sorry
admit
axiom
native_decide
```

既存 unrelated `sorry` warning は今回追加したものと混同しない。

---

# 16. 結果報告

実装後、同 directory に次を作成する。

```text
XDP-005-Mellin-spectral-weight-fixed-Xi-contour-adapter-result.md
```

最低限記録すること。

1. Gate A で実際に必要だった regularity hypotheses
2. 使用した Mathlib Mellin holomorphicity theorem と exact signature
3. 新規 generic theorem 名
4. centered spectral weight definition
5. mirror/reflection theorem surface
6. fixed-Xi weighted contour bridge theorem 名
7. normalized finite zero-sum endpoint
8. generic zero-window transport を追加したか否か
9. build / test result
10. XDP-006 に残った obstruction
11. explicit formula / provider / RH を証明していないこと

---

# 17. 完了条件

XDP-005 は次で完了とする。

```text
positive compact Mellin data
  ↓
centered Mellin spectral weight is globally differentiable
  ↓
existing fixed-Xi generic weighted contour is applicable
  ↓
normalized contour = negative finite weighted centered-Xi zero moment
```

ここまでを Lean Green にする。

`z^2` の spectral realization、prime transport、sign theorem は次 phase へ送る。
