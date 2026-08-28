# XDP-001 — Weil mirror defect bridge Codex 実装指示書

作成日: 2026-08-12

## 0. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-fixed-Xi-defect-provider-260812-v0
Lean: v4.32.2
mathlib: pinned project revision
```

作業 directory:

```text
lean/dk_math
```

本指示書の目的は、PPW-023 で完成した fixed centered-Xi defect を、古典的な Weil 型の critical-mirror quadratic structure と **有限 window 上で exact に同一視する Lean bridge** を実装することである。

ここでは global Weil criterion、Li coefficient、Guinand–Weil explicit formula、Mellin/Fourier test-function class にはまだ進まない。

まず現在の Green Core だけを用いて、同じ有限 scalar defect が

```text
1. radial diagonal mass
2. critical-mirror twisted pairing
3. anti-mirror difference energy
```

の三つの表現を持つことを Lean で固定する。

この有限構造同一性を XDP phase の最初の Core とする。

---

# 1. 既存正本

必ず最初に次を読むこと。

```text
DkMath/RH/CFBRC/CriticalMirrorGeometry.lean
DkMath/RH/CFBRC/CriticalMirrorZeroBridge.lean
DkMath/RH/CFBRC/PascalCenteredXiGlobalZeroDiskBridge.lean
DkMath/RH/CFBRC/PascalCenteredXiOuterContourResidueBridge.lean
DkMath/RH/CFBRC/PascalCenteredXiRadialLayerCakeOuterCountBridge.lean
DkMath/RH/CFBRC/PascalCenteredXiFixedSecondMomentDefectBridge.lean
```

特に既存の次の定義・定理を再利用する。

```lean
criticalMirror
criticalMirror_re
criticalMirror_im
criticalMirror_involutive
criticalMirror_eq_self_iff_re_eq_half
centeredComplex
centeredComplex_re
centeredComplex_im
criticalMirror_nontrivialRiemannZetaZero

pascalCriticalMirrorZeroWindowFinset
pascalCriticalMirrorZeroWindowCenteredSecondMoment
pascalCriticalMirrorZeroWindowRadialSecondMoment
pascalCriticalMirrorZeroWindowHorizontalEnergy

pascalCenteredXiFixedRadialSecondMomentFunctional
pascalCenteredXiFixedHolomorphicSecondContourFunctional
pascalCenteredXiFixedSecondMomentDefectFunctional

pascalCenteredXiFixedRadialSecondMomentFunctional_eq_windowRadial
pascalCenteredXiFixedHolomorphicSecondContourFunctional_eq
pascalCenteredXiFixedSecondMomentDefectFunctional_eq_two_mul_horizontalEnergy
pascalCenteredXiFixedSecondMomentDefectFunctional_nonneg
```

名称・引数は実 repository の現 head を正本とし、この文書との差異があればコード側を優先する。

既存 Green theorem を再証明しない。

---

# 2. 数学的 target

非自明零点を `ρ` とし、critical-line centered coordinate を

$$
c(\rho):=\rho-\frac12
$$

と読む。

DkMath では新しい同義定義を増やすより、既存の

```lean
centeredComplex ρ
```

を優先して再利用する。

critical mirror を

$$
m(\rho):=1-\overline{\rho}
$$

と読むと、centered coordinate は

$$
c(m(\rho))=-\overline{c(\rho)}
$$

を満たす。

この identity が XDP-001 の最初の algebraic Core である。

## 2.1 finite mirror pairing

有限 zero window `W_R` 上で、centered coordinate に対する finite mirror pairing を概念的に

$$
W_R(c,c)
:=
\sum_{\rho\in W_R}
  m_\rho\,
  c(\rho)\,
  \overline{c(m(\rho))}
$$

と定義する。

ここで `m_ρ` は既存の zeta-zero multiplicity weight を使う。

上の centered mirror identity より termwise に

$$
c(\rho)\overline{c(m(\rho))}
=-c(\rho)^2
$$

なので、有限和として

$$
W_R(c,c)
=-M_{2,R}
$$

を得る。

ここで

$$
M_{2,R}
:=
\sum_{\rho\in W_R}m_\rho c(\rho)^2
$$

は既存の `pascalCriticalMirrorZeroWindowCenteredSecondMoment R` である。

PPW-023 では safe radius 上で fixed holomorphic second-contour functional が `-M₂` を読むので、最終的に

$$
W_R(c,c)
=
\operatorname{FixedHolomorphicSecondContour}(R)
$$

まで接続する。

## 2.2 diagonal radial mass

有限 diagonal norm を

$$
Q_R
:=
\sum_{\rho\in W_R}m_\rho |c(\rho)|^2
$$

と読む。

これは既存の

```lean
pascalCriticalMirrorZeroWindowRadialSecondMoment R
```

および safe radius 上の

```lean
pascalCenteredXiFixedRadialSecondMomentFunctional R
```

と exact に一致する。

## 2.3 fixed Xi defect as mirror-pairing defect

PPW-023 の fixed defect は safe radius 上で

$$
D_\Xi(R)
=Q_R+\operatorname{Re}M_{2,R}
$$

であり、`W_R(c,c)=-M₂,R` を用いると

$$
D_\Xi(R)
=Q_R-\operatorname{Re}W_R(c,c)
$$

となる。

これを Lean theorem として固定する。

## 2.4 anti-mirror difference energy

さらに termwise に

$$
c(\rho)-c(m(\rho))
=c(\rho)+\overline{c(\rho)}
$$

であり、右辺は実方向成分の二倍である。

したがって

$$
\frac12\left|c(\rho)-c(m(\rho))\right|^2
=2\left(\operatorname{Re}(\rho)-\frac12\right)^2
$$

となる。

有限和では

$$
D_\Xi(R)
=
\frac12
\sum_{\rho\in W_R}
 m_\rho
 \left|c(\rho)-c(m(\rho))\right|^2
$$

を得る。

これは既存 theorem

```lean
pascalCenteredXiFixedSecondMomentDefectFunctional_eq_two_mul_horizontalEnergy
```

と同じ量の別表現である。

XDP-001 ではこの equality を **RH を使わず** Green 化する。

---

# 3. 新規 module

第一候補:

```text
DkMath/RH/CFBRC/PascalCenteredXiWeilMirrorDefectBridge.lean
```

namespace は既存 PPW modules と合わせる。

```lean
namespace DkMath.RH.CFBRCProjection
```

import は最小化する。

第一候補:

```lean
import DkMath.RH.CFBRC.PascalCenteredXiFixedSecondMomentDefectBridge
import Mathlib.Tactic
```

`FixedSecondMomentDefectBridge` から既に必要な geometry / zero-window 層へ到達できる場合、不要な直接 import は追加しない。

---

# 4. 実装 Phase A — centered mirror algebra

まず Finset や Xi contour を使わない一零点 algebra を固定する。

候補 theorem 名:

```lean
centeredComplex_eq_sub_criticalLineCenter
centeredComplex_criticalMirror_eq_neg_conj
centeredComplex_sub_mirror_eq_two_horizontal
normSq_centeredComplex_sub_mirror_eq_four_horizontal_sq
```

最低限必要なのは次。

```lean
theorem centeredComplex_criticalMirror_eq_neg_conj (s : ℂ) :
    centeredComplex (criticalMirror s) =
      -(starRingEnd ℂ) (centeredComplex s) := by
  ...
```

ただし project 内で `star` / `conj` の標準形が別なら既存 coding style に合わせる。

その後、pairing term identity を置く。

概念形:

```lean
theorem centeredMirrorPairTerm_eq_neg_sq (s : ℂ) :
    centeredComplex s *
        (starRingEnd ℂ) (centeredComplex (criticalMirror s)) =
      -(centeredComplex s) ^ 2 := by
  ...
```

この theorem は純粋複素代数で閉じること。

RH、zero predicate、functional equation を使わない。

---

# 5. 実装 Phase B — finite Weil-style mirror pairing

古典的 Weil criterion そのものを実装したと主張しない。

本 module で定義するのは、既存 finite zero window 上の **Weil-style critical-mirror pairing** である。

名前候補:

```lean
pascalCriticalMirrorZeroWindowFiniteWeilMirrorPair
```

型の第一候補:

```lean
noncomputable def pascalCriticalMirrorZeroWindowFiniteWeilMirrorPair
    (R : ℝ) : ℂ :=
  ∑ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
    (riemannZetaZeroMultiplicity ρ : ℂ) *
      centeredComplex ρ *
        (starRingEnd ℂ) (centeredComplex (criticalMirror ρ))
```

multiplicity function の正確な既存名は repository を検索して合わせること。

同じ multiplicity を `pascalCriticalMirrorZeroWindowCenteredSecondMoment` が使用していることを確認する。

最重要 theorem:

```lean
theorem pascalCriticalMirrorZeroWindowFiniteWeilMirrorPair_eq_neg_centeredSecondMoment
    (R : ℝ) :
    pascalCriticalMirrorZeroWindowFiniteWeilMirrorPair R =
      -pascalCriticalMirrorZeroWindowCenteredSecondMoment R := by
  ...
```

この theorem は **termwise identity + Finset.sum_congr** で閉じるのを第一選択とする。

critical mirror が同じ window を置換するという reindexing は、この theorem には不要である。

不要な permutation / involution proof を持ち込まない。

---

# 6. 実装 Phase C — fixed Xi holomorphic observable との接続

boundary-safe radius では既存 theorem により

$$
\operatorname{FixedHolomorphicSecondContour}(R)
=-M_{2,R}
$$

が Green。

したがって新 pairing との equality を短い bridge として置く。

候補 theorem:

```lean
theorem pascalCenteredXiFixedHolomorphicSecondContourFunctional_eq_finiteWeilMirrorPair
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiFixedHolomorphicSecondContourFunctional R =
      pascalCriticalMirrorZeroWindowFiniteWeilMirrorPair R := by
  ...
```

既存 theorem と Phase B の theorem を `rw` / `calc` で合成する。

新しい contour 計算を行わない。

---

# 7. 実装 Phase D — diagonal radial form

必要なら有限 diagonal radial form を明示定義する。

ただし既存

```lean
pascalCriticalMirrorZeroWindowRadialSecondMoment
```

が目的に十分なら、新しい同義定義を増やさない。

必要な最終 equality は safe radius 上で

$$
D_\Xi(R)
=Q_R-\operatorname{Re}W_R(c,c)
$$

である。

候補 theorem:

```lean
theorem pascalCenteredXiFixedSecondMomentDefectFunctional_eq_radial_sub_finiteWeilMirrorPair_re
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiFixedSecondMomentDefectFunctional R =
      pascalCriticalMirrorZeroWindowRadialSecondMoment R -
        (pascalCriticalMirrorZeroWindowFiniteWeilMirrorPair R).re := by
  ...
```

別候補として fixed radial functional を左側に残してもよい。

```lean
... =
  pascalCenteredXiFixedRadialSecondMomentFunctional R -
    (pascalCriticalMirrorZeroWindowFiniteWeilMirrorPair R).re
```

既存 theorem surface と最も短く繋がる形を選ぶこと。

---

# 8. 実装 Phase E — anti-mirror difference energy

この Phase が XDP-001 の主 endpoint である。

有限 anti-mirror energy を real-valued functional として定義する。

候補:

```lean
noncomputable def pascalCriticalMirrorZeroWindowAntiMirrorEnergy
    (R : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    ∑ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
      (riemannZetaZeroMultiplicity ρ : ℝ) *
        Complex.normSq
          (centeredComplex ρ - centeredComplex (criticalMirror ρ))
```

係数 `1 / 2` を Finset 内へ入れるか外へ出すかは proof ergonomics で決めてよい。

最初に一項 identity を作る。

候補 theorem:

```lean
theorem half_normSq_centeredComplex_sub_criticalMirror_eq
    (s : ℂ) :
    (1 / 2 : ℝ) *
      Complex.normSq (centeredComplex s - centeredComplex (criticalMirror s)) =
        2 * (s.re - (1 : ℝ) / 2) ^ 2 := by
  ...
```

これを finite sum に上げて、既存 horizontal energy と接続する。

候補 theorem:

```lean
theorem pascalCriticalMirrorZeroWindowAntiMirrorEnergy_eq_two_mul_horizontalEnergy
    (R : ℝ) :
    pascalCriticalMirrorZeroWindowAntiMirrorEnergy R =
      2 * pascalCriticalMirrorZeroWindowHorizontalEnergy R := by
  ...
```

そして safe radius 上で fixed defect と exact に一致させる。

```lean
theorem pascalCenteredXiFixedSecondMomentDefectFunctional_eq_antiMirrorEnergy
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiFixedSecondMomentDefectFunctional R =
      pascalCriticalMirrorZeroWindowAntiMirrorEnergy R := by
  ...
```

この theorem は既存

```lean
pascalCenteredXiFixedSecondMomentDefectFunctional_eq_two_mul_horizontalEnergy
```

と新しい anti-mirror theorem を合成して閉じてよい。

別経路で同じ identity を一から展開し直さない。

---

# 9. XDP-001 の最終 theorem surface

最低限、次の鎖を Green にする。

```text
centered mirror algebra
  ↓
finite Weil-style mirror pair = - centered second moment
  ↓
finite Weil-style mirror pair = fixed Xi holomorphic second contour  [safe R]
  ↓
FixedXiDefect = radial - Re(finite mirror pair)               [safe R]
  ↓
anti-mirror difference energy = 2 * horizontal energy
  ↓
FixedXiDefect = anti-mirror difference energy                 [safe R]
```

数学的 endpoint:

$$
\boxed{
D_\Xi(R)
=
Q_R-\operatorname{Re}W_R(c,c)
=
\frac12\sum_{\rho\in W_R}
 m_\rho
 \left|c(\rho)-c(m(\rho))\right|^2
}
$$

boundary-safe `R` について成立させる。

---

# 10. 重要な logical boundary

XDP-001 は **representation / structure identity phase** である。

次を絶対に主張しない。

1. `PascalCenteredXiFixedDefectVanishesOnSafeRadii`
2. `RiemannHypothesis`
3. finite mirror pairing の positivity が classical Weil criterion から直ちに出ること
4. `centeredComplex` が classical Weil test-function class に属すること
5. hard radius cutoff が classical Weil / Guinand explicit formula の admissible test function であること
6. global infinite Weil sum と本 finite pairing が既に同一であること
7. Li coefficients が既に Mathlib / DkMath に formalized されていること

特に、次の循環は禁止する。

```text
FixedXiDefect = 0
all zeros critical
criticalMirror ρ = ρ
RiemannHypothesis
```

のいずれかを仮定して anti-mirror energy identity を証明してはならない。

XDP-001 の equality は **任意の window zero 配置について成立する algebraic identity** でなければならない。

---

# 11. classical terminology の扱い

module / doc comment では次のように慎重に表現する。

```text
finite Weil-style critical-mirror pairing
finite mirror quadratic form
anti-mirror defect energy
```

この phase では「Weil criterion を形式化した」と書かない。

古典的 Weil criterion との本格接続は、admissible test-function adapter を設計した後の別 XDP とする。

この命名境界は、後で先人の theorem と DkMath の finite identity を混同しないために重要である。

---

# 12. proof engineering 方針

1. まず一項 identity を `Complex.ext`, `simp`, `ring`, `ring_nf` で閉じる。
2. Finset theorem は一項 identity の `sum_congr` を優先する。
3. mirror reindexing が不要な theorem では `Finset.image` / permutation を導入しない。
4. `Complex.normSq` を abs/norm の平方へ変換しすぎない。既存 PPW/CF2D の正規形を尊重する。
5. `1 / 2` の型推論が不安定なら `(1 : ℝ) / 2` を明示する。
6. `starRingEnd ℂ` / `star` / conjugation は既存 file の標準形に揃える。
7. simplifier で数式の意味が見えなくなる場合は中間 lemma を置く。
8. theorem statement を build 都合で弱めない。
9. `sorry`, `admit`, `axiom` を追加しない。
10. 既存 theorem の statement を変更しない。

---

# 13. build / validation

まず新 module 単体を Green にする。

```bash
cd lean/dk_math
lake env lean DkMath/RH/CFBRC/PascalCenteredXiWeilMirrorDefectBridge.lean
```

Green 後、public root に import を追加する。

```text
DkMath/RH.lean
```

追加候補:

```lean
import DkMath.RH.CFBRC.PascalCenteredXiWeilMirrorDefectBridge
```

その後、project 正本の検証を実行する。

```bash
lake build DkMath.RH
./lean-build.sh
./lean-test.sh

git diff --check
```

利用可能な script / build command が branch head で変更されている場合は repository の現状を優先する。

主要 theorem について可能なら `#print axioms` 監査を追加または一時確認し、予期しない axiom dependency がないことを確認する。

---

# 14. 完了条件

XDP-001 完了条件は次のすべて。

```text
[ ] centeredComplex と criticalMirror の centered mirror identity Green
[ ] finite Weil-style mirror pairing 定義 Green
[ ] finite mirror pairing = - centered second moment Green
[ ] fixed Xi holomorphic second contour = finite mirror pairing Green
[ ] FixedXiDefect = radial - Re(finite mirror pairing) Green
[ ] anti-mirror difference energy 定義 Green
[ ] anti-mirror energy = 2 * horizontal energy Green
[ ] FixedXiDefect = anti-mirror energy Green
[ ] 新 module 単体 Green
[ ] DkMath.RH public import Green
[ ] lean-build.sh / lean-test.sh Green
[ ] git diff --check Green
[ ] sorry / admit / axiom 追加なし
```

---

# 15. 次 phase へ残すもの

XDP-001 が Green になった後、次の研究は初めて古典的 analytic machinery との adapter に進む。

候補順序:

```text
XDP-002:
  classical Weil / Li / Guinand theorem statement audit
  + Mathlib API inventory

XDP-003:
  admissible smooth centered test-function family
  hard finite window への approximation / limit design

XDP-004:
  zero-side finite defect と explicit-formula functional の bridge

XDP-005:
  prime / von Mangoldt side の sign or upper-bound audit
```

ただし番号・内容は XDP-001 実装結果を見て再評価する。

最終目的は新しい RH 同値条件を増やすことではない。

既に Green の

```lean
PascalCenteredXiFixedDefectVanishesOnSafeRadii ↔ RiemannHypothesis
```

に対して、先人の解析 machinery を引き継ぎながら **同じ fixed scalar defect へ RH-independent constraint を与える provider** を構成することである。

XDP-001 はそのための最初の構造同一性 bridge である。
