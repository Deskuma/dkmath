# XDP-007 — Multiplicative approximate identity / quadratic realization Codex 実装指示書

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

XDP-001 から XDP-006 までで、次の chain は Green である。

```text
finite centered-Xi defect
→ finite critical-mirror pairing
→ generic Mellin critical mirror
→ positive compact-support Mellin admissibility
→ centered Mellin spectral weight
→ fixed-Xi weighted outer contour
→ centered multiplicative dilation
→ symmetric second difference
→ quadratic Mellin-weighted finite Xi moment
```

XDP-006 の exact endpoint は

$$
Q_{\tau,h}(z)
\longrightarrow
z^2 H_h(z),
\qquad
H_h(z):=
\mathcal M h\!\left(\frac12+z\right).
$$

残る named realization gap は `H_h(z)` を constant one に近づける ordinary compact-support Mellin family の構成である。

XDP-007 の目的は、positive multiplicative variable `x` 上で `x = 1` へ集中する reciprocal-symmetric approximate identity を構成し、その centered Mellin spectral weight が

$$
H_\varepsilon(z)\longrightarrow1
$$

となることを Lean で証明することである。

その後、有限 centered-Xi zero disk 上で

$$
z^2H_\varepsilon(z)
\longrightarrow
z^2
$$

を Finset sum へ transport し、XDP-006 の quadratic Mellin-weighted endpoint から既存 centered second moment を極限として回収する。

本 phase は **quadratic realization** の phase であり、prime-side explicit formula、defect sign、defect vanishing、RH はまだ扱わない。

---

# 1. 必読 Green API

最初に実 repository head の次を読むこと。

```text
DkMath/Analysis/MellinCriticalMirror.lean
DkMath/Analysis/MellinCompactSupport.lean
DkMath/Analysis/MellinCompactSupportHolomorphic.lean
DkMath/Analysis/MellinCenteredDilation.lean

DkMath/RH/CFBRC/PascalCenteredXiMellinWeightedOuterContourBridge.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinSecondDifferenceBridge.lean
DkMath/RH/CFBRC/PascalCenteredXiOuterContourResidueBridge.lean
DkMath/RH/CFBRC/PascalCenteredXiFixedSecondMomentDefectBridge.lean
```

特に次の API を正本として再利用する。

```lean
DkMath.Analysis.mellinCriticalMirror
DkMath.Analysis.centeredMellinSpectralWeight
DkMath.Analysis.mellinConvergent_of_support_subset_Icc_pos
DkMath.Analysis.differentiable_centeredMellinSpectralWeight_of_support_subset_Icc_pos
DkMath.Analysis.centeredMellinSpectralWeight_mirror_of_support_subset_Icc_pos

DkMath.Analysis.centeredMellinSecondDifferenceWeight
DkMath.Analysis.tendsto_centeredMellinSecondDifferenceWeight_zero
DkMath.Analysis.differentiable_centeredMellinSecondDifferenceWeight

pascalCenteredXiZeroDiskWeightedMoment
pascalCenteredXiZeroDiskSecondMoment
pascalCenteredXiNormalizedWeightedOuterContourMass_eq

tendsto_pascalCenteredXiZeroDiskMellinSecondDifferenceMoment
pascalCenteredXiNormalizedMellinSecondDifferenceOuterContourMass_eq
tendsto_pascalCenteredXiNormalizedMellinSecondDifferenceOuterContourMass
pascalCenteredXiZeroDiskWeightedQuadraticMoment_eq_secondMoment_of_interpolates_one
```

名称・binder は repository head を正本とする。

既存 theorem を再証明しない。

---

# 2. 重要な数学的境界

## 2.1 global exact realization は要求しない

ordinary compact-support continuous Mellin data に対して

$$
H_h(z)=1
$$

を全 `z : ℂ` で exact に満たすことは要求しない。

XDP-007 が必要とするのは family `h_ε` に対する pointwise limit

$$
H_\varepsilon(z)\to1
$$

である。

finite Xi zero disk 上では pointwise convergence だけで finite sum limit に十分である。

## 2.2 joint two-parameter limit は要求しない

XDP-006 には `τ → 0` があり、XDP-007 には `ε → 0⁺` がある。

本 phase では

$$
(\varepsilon,\tau)\to(0,0)
$$

という joint limit を証明しない。

uniform estimate を証明していない状態で joint limit を主張してはならない。

採用するのは **iterated limit** である。

1. fixed `ε > 0` に対して XDP-006 の `τ → 0`。
2. その target で `ε → 0⁺`。

## 2.3 hard cutoff を Mellin transform と同一視しない

XDP-004/005 の境界を維持する。

```text
safe-radius fixed contour
→ finite spectral localization を担当

Mellin approximate identity
→ spectral weight realization を担当
```

hard radial indicator 自体の Mellin realizationは不要である。

---

# 3. primary approximate-identity family

第一候補は、`ε > 0` に対して `x = 1` の multiplicative neighborhood

$$
[e^{-\varepsilon},e^{\varepsilon}]
$$

に support を持つ centered multiplicative box である。

概念形:

$$
h_\varepsilon(x)
:=
\frac{1}{2\varepsilon}
 x^{-1/2}
 \mathbf 1_{[e^{-\varepsilon},e^{\varepsilon}]}(x).
$$

Lean では total function `ℝ → ℂ` として定義する。

候補名:

```lean
noncomputable def centeredMellinBoxApprox
    (ε : ℝ) (x : ℝ) : ℂ :=
  ...
```

`ε ≤ 0` 側は totalization のためだけに任意の canonical value、第一候補 `0` としてよい。

解析 theorem は `0 < ε` の仮定下だけで述べる。

### 実装上の注意

`x ^ (-1/2)` の表現は、pinned Mathlib で reciprocal algebra と Mellin integral が最も短くなるものを選ぶ。

候補:

```text
Complex.cpow on positive real cast
Real.rpow then cast to ℂ
1 / sqrt x then cast to ℂ
```

API を probe し、mirror/self-duality と integral の両方が最短になる表現を採用する。

推測した theorem 名を無理に使わない。

---

# 4. Gate A — support / continuity / admissibility

`0 < ε` に対して最低限次を Green にする。

候補 theorem:

```lean
centeredMellinBoxApprox_support_subset
```

目標:

```text
Function.support (centeredMellinBoxApprox ε)
⊆ Icc (exp (-ε)) (exp ε)
```

さらに

```lean
centeredMellinBoxApprox_continuousOn
```

として

```text
ContinuousOn (centeredMellinBoxApprox ε)
  (Icc (exp (-ε)) (exp ε))
```

を証明する。

グローバル continuity は要求しない。

box endpoint で outside value と jump があっても、XDP-004/005 が要求するのは support interval 上の `ContinuousOn` である。

その後、既存 compact-support provider から

```lean
MellinConvergent
  (centeredMellinBoxApprox ε) s
```

を任意 `s : ℂ` に対して得る薄い corollary を追加してよい。

### Gate A acceptance

`centeredMellinSpectralWeight (centeredMellinBoxApprox ε)` が XDP-005 の admissible centered spectral weight として使用可能であること。

---

# 5. Gate B — reciprocal mirror symmetry

この family は multiplicative critical mirror に適合するよう設計されている。

`0 < ε`、`0 < x` に対して概念的に

$$
\bigl(h_\varepsilon\bigr)^\vee(x)
=
x^{-1}\overline{h_\varepsilon(x^{-1})}
=
h_\varepsilon(x).
$$

候補 theorem:

```lean
centeredMellinBoxApprox_mellinCriticalMirror
```

statement 第一候補:

```lean
theorem centeredMellinBoxApprox_mellinCriticalMirror
    {ε x : ℝ} (hε : 0 < ε) (hx : 0 < x) :
    mellinCriticalMirror (centeredMellinBoxApprox ε) x =
      centeredMellinBoxApprox ε x := by
  ...
```

proof では次を明示的に処理する。

1. `x ∈ [e^{-ε}, e^ε]` と `x⁻¹ ∈ [e^{-ε}, e^ε]` の同値。
2. positive real 上の half-power reciprocal identity。
3. coefficient `1 / (2ε)` が real なので conjugation で不変。

### Gate B の扱い

mirror self-duality は重要な classical compatibility であるが、pinned Mathlib の half-power algebra が大きな standalone library を要求する場合、XDP-007 の主 realization endpointを阻害してはならない。

その場合は exact blocked theorem と必要 API を result report に残し、Gate C–G を先に Green 化する。

ただし簡単に閉じられるなら必ず実装する。

---

# 6. Gate C — centered Mellin transform の exact formula

数学的には `x = exp t` により

$$
H_\varepsilon(z)
:=
\mathcal M h_\varepsilon\!\left(\frac12+z\right)
=
\frac{1}{2\varepsilon}
\int_{-\varepsilon}^{\varepsilon}e^{zt}\,dt.
$$

これが XDP-007 の核心である。

## Route C1 — log change of variables

第一候補。

Mathlib の `x = exp t` substitution / interval integral API を probe し、Mellin set integral を log-variable interval integral へ変換する。

proof target 候補:

```lean
centeredMellinSpectralWeight_centeredMellinBoxApprox_eq_logAverage
```

概念形:

```text
centeredMellinSpectralWeight (centeredMellinBoxApprox ε) z
  = (2 * ε)⁻¹ * ∫ t in -ε..ε, exp ((t : ℂ) * z)
```

`exp (z * t)` との積順序は既存 coding style に合わせる。

## Route C2 — direct positive interval integral

log substitution API が高コストなら、positive interval で

$$
\frac1{2\varepsilon}
\int_{e^{-\varepsilon}}^{e^{\varepsilon}}x^{z-1}\,dx
$$

を直接扱ってよい。

## Route C3 — closed form

必要であれば `z ≠ 0` のとき

$$
H_\varepsilon(z)
=
\frac{e^{\varepsilon z}-e^{-\varepsilon z}}
{2\varepsilon z}
$$

を証明する。

`z = 0` では exact に

$$
H_\varepsilon(0)=1
$$

となる。

closed form は Gate D の limit が容易になる場合だけ必須とする。

### 禁止

Dirac delta、distribution、measure-valued test function を導入して ordinary compact-support function の proof を回避しない。

---

# 7. Gate D — approximate identity limit

主 theorem。

候補名:

```lean
tendsto_centeredMellinSpectralWeight_centeredMellinBoxApprox_one
```

目標:

```lean
theorem tendsto_centeredMellinSpectralWeight_centeredMellinBoxApprox_one
    (z : ℂ) :
    Tendsto
      (fun ε : ℝ =>
        centeredMellinSpectralWeight
          (centeredMellinBoxApprox ε) z)
      (𝓝[>] 0)
      (𝓝 1) := by
  ...
```

`𝓝[>] 0` は repository / Mathlib の notation に合わせる。

別 equivalent filter が標準ならそちらを採用してよい。

### 推奨 proof route

closed form を得た場合は、complex exponential の一次 Taylor limitを使う。

概念的 kernel

$$
\frac{e^{\varepsilon z}-e^{-\varepsilon z}}
{2\varepsilon z}
$$

を `z = 0` と `z ≠ 0` に分ける。

または log-average form から shrinking-interval average theorem を作ってもよい。

大規模 measure-theory abstraction より、今回の family に対する小さい lemma を優先する。

### Gate D acceptance

任意 fixed `z : ℂ` で `H_ε(z) → 1` が proof-hole なしで Green。

---

# 8. Gate E — quadratic realization

Gate D からただちに

$$
z^2H_\varepsilon(z)
\longrightarrow
z^2
$$

を得る。

候補 theorem:

```lean
tendsto_centeredMellinBoxApprox_quadraticWeight
```

概念形:

```lean
Tendsto
  (fun ε : ℝ =>
    z ^ 2 * centeredMellinSpectralWeight
      (centeredMellinBoxApprox ε) z)
  (𝓝[>] 0)
  (𝓝 (z ^ 2))
```

ここでは XDP-006 の `τ` はまだ使わない。

この theorem が named realization gap を pointwise に閉じる。

---

# 9. Gate F — finite centered-Xi second moment realization

finite zero disk に Gate E を lift する。

新規 CFBRC module 第一候補:

```text
DkMath/RH/CFBRC/PascalCenteredXiMellinQuadraticRealizationBridge.lean
```

主 theorem 候補:

```lean
tendsto_pascalCenteredXiZeroDiskMellinBoxQuadraticMoment_secondMoment
```

目標:

$$
\sum_{a\in Z_\Xi(R)}
 m_a a^2 H_\varepsilon(a)
\longrightarrow
\sum_{a\in Z_\Xi(R)}m_a a^2.
$$

Lean 概念形:

```lean
Tendsto
  (fun ε : ℝ =>
    pascalCenteredXiZeroDiskWeightedMoment
      (fun z =>
        z ^ 2 * centeredMellinSpectralWeight
          (centeredMellinBoxApprox ε) z)
      R)
  (𝓝[>] 0)
  (𝓝 (pascalCenteredXiZeroDiskSecondMoment R))
```

proof は finite sum なので

```text
tendsto_finsetSum
```

を第一選択にする。

uniform convergence は不要。

既存 `pascalCenteredXiZeroDiskWeightedQuadraticMoment_eq_secondMoment_of_interpolates_one` は exact interpolation 用 conditional theorem なので、極限 proof を無理にその theorem へ押し込まなくてよい。

---

# 10. Gate G — XDP-006 との iterated-limit bridge

fixed `ε > 0` では `centeredMellinBoxApprox ε` は XDP-006 の positive compact-support contract を満たす。

従って各 `ε > 0` に対して

$$
Q_{\tau,h_\varepsilon}(z)
\longrightarrow
z^2 H_\varepsilon(z)
$$

および finite Xi moment / normalized contour の `τ → 0` theorem が既存 API から得られる。

これを薄い specialization theorem として追加する。

候補:

```lean
tendsto_pascalCenteredXiNormalizedMellinBoxSecondDifferenceOuterContourMass_tau
```

statement は `ε > 0`、safe `R` を固定し、`τ → 0` の target を

```text
-negative finite moment of z² * H_ε(z)
```

とする。

次に Gate F と組み合わせ、研究上の iterated-limit statement を theorem / docstring で明示する。

可能なら二段階を separate theorem として表す。

```text
fixed ε > 0:
  τ → 0 contour family
      → -M_ε

then:
  ε → 0⁺ (-M_ε)
      → -M₂
```

### 重要

joint function

```text
(ε, τ) ↦ contour(ε, τ)
```

について product filter の limit は証明しない。

それを theorem 名や docstring で暗示しない。

---

# 11. Gate H — existing fixed second contour への帰還

既存 theorem により safe radius で

$$
(2\pi i)^{-1}
\operatorname{OuterContour}(z^2,R)
=
-M_{2,R}.
$$

Gate F/G の limit target がこの既存 second moment / fixed second contour と同じ scalar であることを薄い bridge で確認する。

新しい residue proof は行わない。

候補 endpoint:

```lean
pascalCenteredXiMellinBoxQuadraticLimit_eq_fixedSecondContourTarget
```

ただし `Tendsto` の target が既存 theorem を `rw` するだけで十分なら、新しい definition を増やさない。

### XDP-007 最終数学 endpoint

safe `R` について、ordinary positive compact-support Mellin family の iterated limit が既存 centered second contour target を回収すること。

概念的に

$$
\lim_{\varepsilon\to0^+}
\left[
\lim_{\tau\to0}
\operatorname{NormalizedOuterContour}
(Q_{\tau,h_\varepsilon},R)
\right]
=
-M_{2,R}.
$$

これは **iterated limit** の記述である。

---

# 12. mirror self-dual family から得る optional corollary

Gate B が Green の場合、XDP-003/005 reflection API と組み合わせて

$$
H_\varepsilon(z)
=
\overline{H_\varepsilon(-\bar z)}
$$

を証明する。

候補 theorem:

```lean
centeredMellinBoxApprox_spectral_mirror
```

これは classical critical-mirror compatible test family であることを示す useful API だが、quadratic realization proof の論理前提にはしない。

---

# 13. implementation module layout

Generic module 第一候補:

```text
DkMath/Analysis/MellinMultiplicativeApproxIdentity.lean
```

CFBRC bridge 第一候補:

```text
DkMath/RH/CFBRC/PascalCenteredXiMellinQuadraticRealizationBridge.lean
```

Generic Core は Xi、zeta、RH を import しない。

CFBRC module は generic approximate identity と XDP-006 fixed-Xi bridge を import する。

Green 後、必要なら

```text
DkMath/Analysis.lean
DkMath/RH.lean
```

へ public import を追加する。

---

# 14. proof strategy

優先:

```text
#check / source search
simp
rw
calc
ring
ring_nf
field_simp
fun_prop
filter_upwards
Tendsto.const_mul / mul_const / mul
Finset.sum_congr
tendsto_finsetSum
```

cpow / rpow / sqrt の branch-sensitive identity は positivity hypothesis を theorem statement に残し、暗黙 simplification に依存しない。

log substitution を行う場合は Jacobian `dx = exp t dt` と centered half-weight cancellation を exact に追跡する。

符号、`1/2`、`2ε` normalization を numerical intuition で省略しない。

---

# 15. circularity / safety guard

XDP-007 では次を使用禁止とする。

```lean
RiemannHypothesis
PascalCenteredXiFixedDefectVanishesOnSafeRadii
pascalCenteredXiFixedDefectVanishesOnSafeRadii_iff_riemannHypothesis
```

また、次を仮定してはならない。

```text
all Xi zeros lie on the critical line
fixed defect vanishes
horizontal energy vanishes
classical Weil positivity
Guinand-Weil explicit formula
prime-side sign
H_h(z) = 1 globally for an ordinary compact-support h
joint (ε,τ) convergence without proof
```

本 phase は realization / approximation theorem であり provider theorem ではない。

---

# 16. XDP-007 acceptance criteria

最低限次を Green にする。

```text
A. centered multiplicative box family is defined for ordinary functions
B. ε > 0 で positive compact support / ContinuousOn contract
C. centered Mellin spectral weight has an exact integral representation
D. H_ε(z) → 1 for every fixed z
E. z² H_ε(z) → z²
F. finite centered-Xi weighted moment → existing second moment
G. fixed ε で XDP-006 τ-limitを specialization できる
H. ε-limit targetが existing fixed second contour target と一致
```

可能なら追加:

```text
I. h_ε is mellinCriticalMirror self-dual on Ioi 0
J. H_ε(z) = conj(H_ε(-conj z))
```

I/J が half-power API の大規模不足で blocked でも A–H が Green なら XDP-007 の principal realization endpoint は達成扱いとしてよい。

---

# 17. validation

新 generic module:

```bash
cd lean/dk_math
lake env lean DkMath/Analysis/MellinMultiplicativeApproxIdentity.lean
```

CFBRC bridge:

```bash
lake env lean DkMath/RH/CFBRC/PascalCenteredXiMellinQuadraticRealizationBridge.lean
```

その後:

```bash
./lean-build.sh
./lean-test.sh
git diff --check
```

新規 code に次を残さない。

```text
sorry
admit
axiom
native_decide
```

必要な principal theorem は `#print axioms` で監査する。

---

# 18. 終了報告

Codex は終了時に次を report する。

1. 追加・変更 file
2. approximate identity の exact definition
3. support / continuity theorem
4. Mellin exact integral formula の proof route
5. `H_ε(z) → 1` theorem 名
6. finite Xi second-moment realization theorem 名
7. XDP-006 specialization / iterated-limit bridge
8. mirror self-duality Green / Blocked
9. build / test / diff result
10. proof shortcut audit
11. acceptance A–J の Green / Blocked
12. XDP-008 へ残る exact mathematical gap

---

# 19. XDP-008 への出口

XDP-007 が A–H を Green 化した場合、`z² realization gap` は ordinary compact-support Mellin family の極限として閉じる。

その後の frontier は、もはや zero-side quadratic weight の realization ではない。

次 phase では初めて

```text
fixed-Xi / Mellin weighted contour
→ zeta log-derivative / completed-zeta decomposition
→ existing PascalVonMangoldtLSeriesBridge
→ prime / prime-power side
```

という explicit-formula transport を監査する。

ただし XDP-008 でも classical explicit formula を仮定して輸入してはならない。

pole term、gamma / archimedean term、ordinary zeta log-derivative、prime-power termを別々に exact に追跡し、既存 DkMath / Mathlib API でどこまで Green にできるかを判定する。

XDP-007 ではそこへ進まない。

まず `H_ε → 1` と finite quadratic realization を Lean に判定させる。
