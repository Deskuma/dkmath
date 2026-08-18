# CFZP-0005 — CFZP-006 source completion geometry audit 実装指示書

## 0. 作業対象

Repository:

```text
Deskuma/dkmath
```

Working branch:

```text
wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0
```

この指示書作成直前に確認した Green checkpoint:

```text
42f8850c689b10a41b15b598a4107b0daca6936c
Add: CFZP-0004: CFZP-005 Mellin / functional-reflection source projection
```

CFZP-005 実装 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaMellinSourceProjection
```

CFZP-005 は次を exact に閉じている。

```text
functional-reflection mode difference
canonical functional-reflection linear source
canonical PHZ difference
CS37 finite symmetric Euler rate
actual Mellin symmetric Euler density
CS38 symmetric Euler mirror density
completed + Gamma + Euler projected mirror scalar density
TopZetaMismatchScalar の oriented half-interval recovery
```

今回 CFZP-006 では、これらを壊さない。

---

# 1. 今回の目的 — いきなり rectangle remainder を Gap と呼ばない

ROADMAP の CFZP-006 は、最終的に source side で Big / Body / Gap を同じ projection から回収することを目標としている。

しかし CFZP-005 までの実装を監査すると、ここで一つ重要な幾何学的差が露出した。

CFZP-003 / 004 の prime-mirror Gap は same-height critical reflection

```text
criticalMirror s
```

を使う。

一方 CS37 / CS38 の Euler source は functional reflection

```text
1 - s
```

を使う。

一般には

```text
criticalMirror s ≠ 1 - s
```

である。

両者は実部反射は同じだが、虚部について

```text
criticalMirror s :  Im = +Im(s)
1 - s            :  Im = -Im(s)
```

となる。

したがって functional-reflection source には、same-height mirror channel に加えて cycle-height reversal の成分が含まれる。

今回の第一目的は、この余剰成分を exact に分離することである。

第二目的は、既存 CS23 と CS30 の二つの source ledger を exact に比較し、rectangle remainder が何と等しいかを確定することである。

ただし、非負性や CFZP coordinate Gap との exact bridge が得られる前に rectangle remainder を `Gap` と命名してはならない。

今回の正本名は `CompletionRemainder` / `SourceRemainder` とする。

---

# 2. 新規 module

推奨 filename:

```text
lean/dk_math/DkMath/RH/CFBRC/
  CosmicFormulaZetaSourceCompletionGeometryAudit.lean
```

推奨 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaSourceCompletionGeometryAudit
```

推奨 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaMellinSourceProjection
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidualAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideIndependentRadialContactProviderAudit
import Mathlib.Tactic
```

不要な import は削ってよい。

既存 CS38 Core--Beam--Gap amendment を theorem reuse のため import してもよいが、そこにある frontier marker を解決済みとみなしてはならない。

---

# 3. Gate A — functional reflection と same-height mirror の差を定義する

一つの natural label mode に対して、cycle displacement を次で定義する。

概念形:

```text
CycleDisplacement_q(s)
  := q^(-(1-s)) - q^(-(criticalMirror s))
```

推奨名:

```lean
noncomputable def cfzpFunctionalVsSameHeightCycleDisplacementMode
    (q : ℕ) (s : ℂ) : ℂ :=
  (q : ℂ) ^ (-(1 - s)) -
    (q : ℂ) ^ (-(criticalMirror s))
```

そして必ず exact decomposition を証明する。

```text
FunctionalReflectionModeDifference
  = CycleDisplacementMode
    + SameHeightMirrorModeDifference
```

すなわち概念的には

```lean
theorem cfzpFunctionalReflectionModeDifference_eq_cycleDisplacement_add_sameHeight
    (q : ℕ) (s : ℂ) :
    cfzpFunctionalReflectionModeDifference q s =
      cfzpFunctionalVsSameHeightCycleDisplacementMode q s +
        cfzpSameHeightMirrorModeDifference q s
```

これは単なる ring identity でよいが、今回の source geometry の中心 theorem である。

---

# 4. Gate B — cycle displacement の polar factorization

CFZP-001 の二つの theorem を再利用する。

```text
natCpowNeg_one_sub_eq_commonRadial_mul_rightAmplitude_mul_cycle
natCpowNeg_criticalMirror_eq_commonRadial_mul_rightAmplitude_mul_cycle
```

両者は同じ radial carrier と同じ right amplitude を持ち、cycle state だけが

```text
-s.im
vs
+s.im
```

で異なる。

従って exact に

```text
CycleDisplacement_q(s)
  = commonRadial_q
    * rightAmplitude_q(centeredSigma s.re)
    * (cycle_q(-s.im) - cycle_q(s.im))
```

を得ること。

RHS の括弧順・cast は Lean に合わせて調整してよい。

この theorem は、functional-reflection source が pure horizontal mirror displacement ではないことを quantity level で固定する。

---

# 5. Gate C — zero-height coincidence

虚部が 0 なら functional reflection と same-height mirror は一致する。

最低限、次を証明する。

```lean
theorem cfzpFunctionalVsSameHeightCycleDisplacementMode_eq_zero_of_im_eq_zero
    {q : ℕ} {s : ℂ} (hs : s.im = 0) :
    cfzpFunctionalVsSameHeightCycleDisplacementMode q s = 0
```

可能なら幾何そのものも薄い helper として追加する。

```lean
theorem one_sub_eq_criticalMirror_iff_im_eq_zero (s : ℂ) :
    1 - s = criticalMirror s ↔ s.im = 0
```

ただし既存に同値 theorem があれば再利用する。

---

# 6. Gate D — critical real center では same-height channel が消える

`Re(s) = 1/2` なら `criticalMirror s = s` なので、same-height mirror difference は 0 になる。

最低限:

```lean
theorem cfzpSameHeightMirrorModeDifference_eq_zero_of_re_eq_half
    {q : ℕ} {s : ℂ}
    (hs : s.re = (1 : ℝ) / 2) :
    cfzpSameHeightMirrorModeDifference q s = 0
```

そして functional source は cycle displacement だけに退化する。

```lean
theorem cfzpFunctionalReflectionModeDifference_eq_cycleDisplacement_of_re_eq_half
    {q : ℕ} {s : ℂ}
    (hs : s.re = (1 : ℝ) / 2) :
    cfzpFunctionalReflectionModeDifference q s =
      cfzpFunctionalVsSameHeightCycleDisplacementMode q s
```

これは重要である。

critical real center で coordinate Gap が消えても、functional-reflection source 全体が自動的に消えるとは限らない。

残り得るのは cycle-height reversal 成分である。

ここで「一般に非零」を無理に証明しない。周期的 coincidence があり得るため、今回必要なのは exact decomposition だけである。

---

# 7. Gate E — canonical finite source decomposition

canonical prime-power support 上で cycle displacement source を finite aggregate する。

推奨定義:

```lean
noncomputable def cfzpCanonicalCycleDisplacementLinearSourceUpTo
    (X : ℕ) (s : ℂ) : ℂ :=
  ∑ q ∈ canonicalPrimePowerSupportUpTo X,
    (canonicalPrimePowerShadowCost q : ℂ) *
      cfzpFunctionalVsSameHeightCycleDisplacementMode q s
```

そして exact に

```text
CanonicalFunctionalReflectionSource
  = CanonicalCycleDisplacementSource
    + CanonicalSameHeightMirrorSource
```

を証明する。

CFZP-004 の既存

```text
cfzpCanonicalSameHeightMirrorLinearSourceUpTo
```

を再利用すること。

さらに cycle displacement source 自身を PHZ difference として読めることを証明する。

```text
CycleDisplacementSource
  = PHZ(1-s) - PHZ(criticalMirror s)
```

canonical/finite fold の既存 theorem を使い、prime-only sum を新設しない。

---

# 8. Gate F — Mellin Euler density の二成分分解

CFZP-005 の actual top Mellin weight を使い、same-height channel と cycle-displacement channel を別々に density 化する。

推奨定義:

```text
cfzpFiniteMellinSameHeightMirrorDensity
cfzpFiniteMellinCycleDisplacementDensity
```

どちらも

```text
Im(weight * source)
```

の形とする。

そして exact に

```text
cfzpFiniteMellinSymmetricEulerDensity
  = cfzpFiniteMellinCycleDisplacementDensity
    + cfzpFiniteMellinSameHeightMirrorDensity
```

を証明する。

従って既存 CS38 Euler channel についても

```text
CS38 SymmetricEulerMirrorDensity
  = cycle-displacement density
    + same-height mirror density
```

という theorem surface を得る。

この段階で completed-zeta / Gamma channel との cancellation を仮定しない。

---

# 9. Gate G — rectangle completion remainder を名前付きで回収する

次を `Gap` ではなく `CompletionRemainder` として定義する。

推奨:

```lean
noncomputable def cfzpFiniteRectangleCompletionRemainder
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℝ :=
  pascalCenteredXiPrimeSideFiniteRectangleBackground ε W X -
    pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar ε W X
```

まず代数的 completion を証明する。

```text
RectangleBackground
  = TopZetaMismatchScalar + CompletionRemainder
```

これは source-side recovery identity であり、まだ cosmic Gap projection theorem ではない。

---

# 10. Gate H — CS30 radial deficit と remainder の exact equality

CS30 の既存 theorem

```text
pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_pi_mul_background_sub_mismatch
```

を使い、exact に

```text
RadialContactDeficit
  = π * cfzpFiniteRectangleCompletionRemainder
```

を証明する。

可能なら次の normalized form も追加する。

```text
cfzpFiniteRectangleCompletionRemainder
  = RadialContactDeficit / π
```

`Real.pi_ne_zero` / `Real.pi_pos` を使う。

---

# 11. Gate I — CS23 source-complete ledger との exact bridge

CS23 の既存 theorem

```text
pascalCenteredXiPrimeSideIndependentCompleteSource_radialDeficit_eq
```

は

```text
RadialContactDeficit
  = π *
    (FixedRadialSecondMomentFunctional
      - IndependentCompleteSourceReal)
```

を与える。

Gate H と比較して、必ず exact に

```text
cfzpFiniteRectangleCompletionRemainder
  = pascalCenteredXiFixedRadialSecondMomentFunctional W.R
    - pascalCenteredXiPrimeSideIndependentCompleteSourceReal ε W X
```

を証明する。

これにより二つの source decomposition

```text
RectangleBackground - TopZetaMismatchScalar
```

と

```text
FixedRadialSecondMoment - IndependentCompleteSourceReal
```

が同じ remainder であることが初めて CFZP API 上に固定される。

これは今回の最重要 source-side theorem の一つである。

---

# 12. Gate J — sign frontier を明示する

今回、`CompletionRemainder` の非負性を勝手に証明しない。

代わりに既存 CS30 identity から exact に sign equivalence を取る。

例:

```lean
theorem cfzpFiniteRectangleCompletionRemainder_nonneg_iff_radialContactDeficit_nonneg
    ... :
    0 ≤ cfzpFiniteRectangleCompletionRemainder ε W X ↔
      0 ≤ pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X
```

または同値な向きの theorem でよい。

zero についても可能なら

```text
CompletionRemainder = 0
  ↔ RadialContactDeficit = 0
```

を追加する。

重要なのは、非負性 provider がまだ source から得られていないことを API 上で隠さないことである。

---

# 13. 今回の結論として許可されること / 禁止されること

今回許可される結論:

```text
functional source
  = cycle-height displacement
    + same-height mirror source

CS38 Euler density
  = cycle displacement density
    + same-height mirror density

RectangleBackground - TopZetaMismatchScalar
  = RadialContactDeficit / π
  = FixedRadialSecondMoment - IndependentCompleteSourceReal
```

今回禁止する結論:

```text
RectangleCompletionRemainder = cfzpAggregateMirrorGapUpTo
RectangleCompletionRemainder = coordinate Gap δ²
RectangleCompletionRemainder ≥ 0
RectangleCompletionRemainder is the cosmic Gap
TopZetaMismatchScalar = AggregateBody
RectangleBackground = AggregateBig
```

これらにはまだ exact projection theorem がない。

特に `criticalMirror` と `1-s` の差として cycle displacement が残るため、same-height coordinate Gap を functional-reflection source remainder と直接同一視しないこと。

---

# 14. Firewall

今回の module で禁止すること。

```text
- Rectangle remainder を名前だけで Gap に昇格しない
- source remainder の非負性を仮定しない
- functional reflection と same-height critical mirror を同一視しない
- cycle displacement を捨てない
- completed-zeta / Gamma channel が Euler channel を都合よく cancel すると仮定しない
- normSq を finite sum に分配しない
- infinite Euler product を導入しない
- Complex.arg / phase unwrapping を導入しない
- RH を主張しない
- sorry / admit / axiom を残さない
```

既存 source frontier marker を theorem の代用にしない。

---

# 15. 推奨 theorem surface

名前は repository style に合わせて調整してよいが、最低限次の意味を持つ API を残すこと。

```text
cfzpFunctionalVsSameHeightCycleDisplacementMode
cfzpFunctionalReflectionModeDifference_eq_cycleDisplacement_add_sameHeight
cfzpFunctionalVsSameHeightCycleDisplacementMode_eq_polar
cfzpFunctionalVsSameHeightCycleDisplacementMode_eq_zero_of_im_eq_zero
cfzpSameHeightMirrorModeDifference_eq_zero_of_re_eq_half
cfzpFunctionalReflectionModeDifference_eq_cycleDisplacement_of_re_eq_half

cfzpCanonicalCycleDisplacementLinearSourceUpTo
cfzpCanonicalFunctionalReflectionLinearSourceUpTo_eq_cycleDisplacement_add_sameHeight
cfzpCanonicalCycleDisplacementLinearSourceUpTo_eq_PHZ_difference

cfzpFiniteMellinSameHeightMirrorDensity
cfzpFiniteMellinCycleDisplacementDensity
cfzpFiniteMellinSymmetricEulerDensity_eq_cycleDisplacement_add_sameHeight

cfzpFiniteRectangleCompletionRemainder
cfzpFiniteRectangleBackground_eq_mismatch_add_completionRemainder
cfzpFiniteRadialContactDeficit_eq_pi_mul_completionRemainder
cfzpFiniteRectangleCompletionRemainder_eq_radialDeficit_div_pi
cfzpFiniteRectangleCompletionRemainder_eq_radialMoment_sub_completeSource
cfzpFiniteRectangleCompletionRemainder_nonneg_iff_radialDeficit_nonneg
```

exact identifier は既存名前空間との衝突を避けて調整してよい。

---

# 16. Build / export

新規 module 単体を Green にした後でのみ

```text
DkMath/RH.lean
```

へ public import を追加する。

最終確認:

```bash
cd lean/dk_math
lake build DkMath.RH
./lean-build.sh
./lean-test.sh
git diff --check
```

新規 module に

```text
sorry
admit
axiom
```

を残さない。

---

# 17. この Gate の成功判定

CFZP-006 の今回の audit は、rectangle remainder を cosmic Gap と同一視することが成功条件ではない。

成功条件は次である。

```text
1. functional reflection の cycle displacement を exact に分離できた
2. same-height mirror sourceとの finite decomposition が閉じた
3. Mellin Euler densityでも同じ decomposition が閉じた
4. rectangle remainder が CS30 radial deficit / π と exact に一致した
5. 同じ remainder が CS23 の radial moment - complete source と exact に一致した
6. remainder の sign が未提供であることを隠さなかった
```

ここまで Green になった時点で、次の判断を行う。

```text
A. cycle-displacement / completed / Gamma を含む same-projection Big を構成できる
   → CFZP-006B source Big / Body / Gap projection へ進む

B. source remainder の nonnegative quadratic representation が得られない
   → rectangle remainder を Gap と呼ばず、ROADMAP の Big candidate を再選定する
```

この分岐は Lean の exact theorem に決めさせること。

CFZP-007 以降には進まない。
