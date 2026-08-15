# CFZP-0015 — CFZP-006K forward polarized rectangle completion ledger 実装指示書

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
04466c9b968c4f2d94603f0671932cd41acf40c4
Add: CFZP-0014: CFZP-006J projected mirror three-channel polarization / TopMismatch recovery
```

CFZP-006J は projected completed / Gamma / Euler source に対して pointwise に

```text
M+ - M- = 4 * ProjectedMirrorScalarDensity
M+ + M- = 2 * (ProjectedWeightedQuadraticMass + 1)
```

を閉じ、既存 CFZP-005 hypotheses の下で

```text
TopZetaMismatchScalar
  = (1 / π) * ∫_{σ}^{1/2} (M+ - M-) / 4
```

を exact に得た。

今回の CFZP-006K では、この reverse-oriented polarization integral を正向き `1/2..σ` の signed interaction integral に直し、既存 completion geometry

```text
RectangleBackground
  = TopZetaMismatchScalar + CompletionRemainder

RadialContactDeficit
  = π * CompletionRemainder
```

へ exact に接続する。

**CompletionRemainder の非負性は証明しない。**

---

# 1. 今回の数学的核心

006J の pointwise masses を略記して

```text
M+(u) := cfzpProjectedMirrorPolarizedPlusMass ε X W u
M-(u) := cfzpProjectedMirrorPolarizedMinusMass ε X W u
```

とする。

既存 rectangle contract では `1/2 <= σ` なので、正向き interval を `1/2..σ` とする。

forward polarized interaction integral を

```text
I_pol(ε,X,W)
  := ∫ u in (1/2)..σ, (M-(u) - M+(u)) / 4
```

と置く。

006J の reverse-oriented theorem と `intervalIntegral.integral_symm` により exact に

```text
TopZetaMismatchScalar = (1 / π) * I_pol
```

となる。

符号に注意すること。forward interval では integrand は `M- - M+` である。

これを completion ledger へ入れると

```text
RectangleBackground
  = (1 / π) * I_pol + CompletionRemainder
```

従って

```text
CompletionRemainder
  = RectangleBackground - (1 / π) * I_pol
```

さらに

```text
RadialContactDeficit
  = π * RectangleBackground - I_pol
```

まで exact に得られる。

これは `CompletionRemainder` を Gap と呼ぶ theorem ではない。背景と polarized interaction の差として existing radial defect を再表示するだけである。

---

# 2. 新規 module

推奨 filename:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaForwardPolarizedRectangleCompletionAudit.lean
```

module:

```lean
DkMath.RH.CFBRC.CosmicFormulaZetaForwardPolarizedRectangleCompletionAudit
```

imports:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaProjectedMirrorPolarizationAudit
import DkMath.RH.CFBRC.CosmicFormulaZetaSourceCompletionGeometryAudit
import Mathlib.Tactic
```

`DkMath/RH.lean` に public import を追加する。

---

# 3. Gate A — forward polarized interaction integral

推奨 def:

```lean
noncomputable def cfzpProjectedMirrorForwardPolarizedInteractionIntegral
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  ∫ u in (1 / 2 : ℝ)..W.rectangle.σ,
    (cfzpProjectedMirrorPolarizedMinusMass ε X W u -
      cfzpProjectedMirrorPolarizedPlusMass ε X W u) / 4
```

この量は **signed interaction integral** であり、nonnegative mass と呼ばない。

006J theorem

```lean
pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar_eq_projectedPolarized_half_integral
```

と同じ hypotheses の下で、load-bearing theorem:

```text
TopZetaMismatchScalar
  = (1 / Real.pi) *
      cfzpProjectedMirrorForwardPolarizedInteractionIntegral ε X W
```

を証明する。

証明方針:

1. 006J theorem をそのまま取得。
2. `intervalIntegral.integral_symm` で `σ..1/2` を `1/2..σ` へ反転。
3. pointwise algebra で `-(M+ - M-) / 4 = (M- - M+) / 4`。

新しい integrability hypothesis は追加しない。

---

# 4. Gate B — RectangleBackground ledger

既存

```lean
cfzpFiniteRectangleBackground_eq_mismatch_add_completionRemainder
```

へ Gate A を代入し、同じ 006J hypotheses の下で

```text
pascalCenteredXiPrimeSideFiniteRectangleBackground ε W X
  = (1 / Real.pi) *
      cfzpProjectedMirrorForwardPolarizedInteractionIntegral ε X W
    + cfzpFiniteRectangleCompletionRemainder ε W X
```

を exact に証明する。

さらに rearrangement:

```text
cfzpFiniteRectangleCompletionRemainder ε W X
  = pascalCenteredXiPrimeSideFiniteRectangleBackground ε W X
    - (1 / Real.pi) *
        cfzpProjectedMirrorForwardPolarizedInteractionIntegral ε X W
```

も記録する。

ここで `CompletionRemainder` を `Gap`、`positive mass`、`quadratic mass` と rename しない。

---

# 5. Gate C — radial contact deficit direct ledger

既存 completion theorem

```lean
cfzpFiniteRadialContactDeficit_eq_pi_mul_completionRemainder
```

を使う。この theorem が要求する `hArch`, `hElem` と、Gate A が要求する 006J hypotheses を合わせてよい。

exact target:

```text
pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X
  = Real.pi *
      pascalCenteredXiPrimeSideFiniteRectangleBackground ε W X
    - cfzpProjectedMirrorForwardPolarizedInteractionIntegral ε X W
```

証明は

```text
RadialDeficit = π * CompletionRemainder
CompletionRemainder = Background - I_pol / π
```

の algebra のみにする。

`Real.pi_ne_zero` / `Real.pi_pos` は既存 API を使う。

---

# 6. Gate D — sign classification only, no sign provider

Gate C から cheap なら次を exact に記録する。

```text
0 <= CompletionRemainder
  ↔ I_pol <= π * RectangleBackground
```

および既存 radial-contact equivalence と整合する形で

```text
0 <= RadialContactDeficit
  ↔ I_pol <= π * RectangleBackground
```

または

```text
RadialContactDeficit <= 0
  ↔ π * RectangleBackground <= I_pol
```

のどちらか一方以上。

これは **classification theorem** であり、いずれの不等式側も実際に成立すると主張しない。

---

# 7. Gate E — independent complete source ledger（推奨）

既存

```lean
cfzpFiniteRectangleCompletionRemainder_eq_radialMoment_sub_completeSource
```

と Gate B を組み合わせ、安価なら

```text
RectangleBackground
  = (1 / π) * I_pol
    + pascalCenteredXiFixedRadialSecondMomentFunctional W.R
    - pascalCenteredXiPrimeSideIndependentCompleteSourceReal ε W X
```

を exact に記録する。

これにより current finite rectangle は

```text
forward polarized top interaction
+ independent completion ledger
```

として分類できる。

ただし independent completion ledger の符号は主張しない。

---

# 8. Integrated plus/minus mass について

今回、次の分離は必須にしない。

```text
I_pol
  = IntegratedMinusMass - IntegratedPlusMass
```

これを行うには `M+`, `M-` 各々の interval integrability を明示的に供給するのが望ましい。

006J までで得ているのは pointwise nonnegativity と difference integral であり、total completed/Gamma/Euler source の square-mass integrability certificate はまだ別 audit である。

従って今回も

```text
∫_{1/2}^{σ} M+
∫_{1/2}^{σ} M-
```

を無条件に「two nonnegative integrated masses」と宣言しない。

次 checkpoint で integrability を独立に監査してよい。

---

# 9. Firewall

禁止:

- `CompletionRemainder >= 0` の無条件主張
- `RadialContactDeficit >= 0` の無条件主張
- `CompletionRemainder = ProjectedWeightedQuadraticMass`
- `CompletionRemainder = cfzpAggregateMirrorGapUpTo`
- `CompletionRemainder = cfzpAggregateCarrierWeightedMirrorGapUpTo`
- forward interaction integral を nonnegative mass と呼ぶ
- `M+`, `M-` の各 forward integral の無条件非負性
- channel cross terms の除去
- `SourceBig / SourceBody / SourceGap` の premature naming
- complex source zero / zeta zero / RH への shortcut
- infinite Euler product
- `Complex.arg`
- 新しい global `Complex.log` branch
- `sorry` / `admit` / `axiom` / `native_decide`

---

# 10. 成功条件

最低限、次が Green なら CFZP-006K 完了とする。

```text
1. forward oriented 1/2..σ interaction integral を定義
2. integrand の符号が M- - M+ である
3. 006J hypotheses の下で TopMismatch = I_pol / π
4. RectangleBackground = I_pol / π + CompletionRemainder
5. CompletionRemainder = Background - I_pol / π
6. existing completion hypotheses を合わせて RadialContactDeficit = π*Background - I_pol
7. sign theorem を置く場合は iff/classification のみ
8. CompletionRemainder positivity を主張しない
9. individual integrated M± positivity を先取りしない
10. DkMath.RH public import
11. target module build Green
12. lake build DkMath.RH Green
13. nested ./lean-build.sh Green
14. nested ./lean-test.sh Green
15. git diff --check Green
16. 新規 module に sorry / admit / axiom / native_decide / Complex.arg / Complex.log なし
```

---

# 11. 次 Gate への判断材料

006K が Green になれば、次の第一候補は CFZP-006L integrated polarized mass audit。

そこで total projected source / quadratic mass の finite half-interval integrability を独立に証明できるか調べ、可能なら

```text
P+ := ∫_{1/2}^{σ} M+
P- := ∫_{1/2}^{σ} M-
```

を genuinely nonnegative integrated masses として確立し、

```text
I_pol = (P- - P+) / 4
```

へ分離する。

その時点で初めて whole rectangle ledger を

```text
Background
  = (P- - P+) / (4π)
    + CompletionRemainder
```

という two-mass balance form へ安全に昇格できる。
