# CFZP-0014 — CFZP-006J projected mirror three-channel polarization / TopMismatch recovery 実装指示書

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
5f33701811a9068ceb3b7cb36b90289bd886f75b
Add: CFZP-0013: CFZP-006I top-edge weighted polarization
```

CFZP-006I 実装 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaTopEdgeWeightedPolarizationAudit
```

006I は Euler channel について pointwise に

```text
A_E := TopMellinWeight * EulerSource
D_E := -i * A_E

Re(D_E) = EulerDensity
normSq(D_E) = WeightedEulerQuadraticMass

M_E+ - M_E- = 4 * EulerDensity
M_E+ + M_E- = 2 * (WeightedEulerQuadraticMass + 1)
```

を exact に閉じた。

さらに

```text
WeightedEulerQuadraticMass
  = normSq(TopMellinWeight) * TotalSourceMass
  = normSq(TopMellinWeight) * FullPairSum
```

であり、mass balance は Euler density zero と同値だが、complex source zero とはまだ同一視していない。

今回の CFZP-006J では、この pointwise polarization を completed / Gamma / Euler の三 channel 全体へ持ち上げ、CFZP-005 の

```text
cfzpProjectedMirrorScalarDensity
```

を二つの nonnegative square masses の差として exact に recover する。

さらに既存 CFZP-005 half-integral theorem を使い、`TopZetaMismatchScalar` をその polarized difference の oriented half-integralとして exact に書き直す。

---

# 1. 今回の数学的核心

Top edge point `u` で略記する。

```text
w := pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u

C := pascalCenteredXiPrimeSideFiniteCompletedZetaMirrorRate
       (pascalSymmetricRectangleTopEdge u W.rectangle.T)

G := pascalCenteredXiPrimeSideFiniteGammaMirrorRate
       (pascalSymmetricRectangleTopEdge u W.rectangle.T)

E := cfzpCanonicalFunctionalReflectionLinearSourceUpTo X
       (pascalSymmetricRectangleTopEdge u W.rectangle.T)
```

CFZP-005 の projected scalar density は exact に

```text
Im(w*C) + Im(w*G) + Im(w*E)
```

である。

そこで三 channel の weighted complex source を

```text
A := w*C + w*G + w*E
```

または distributivity を使って

```text
A := w * (C + G + E)
```

として定義する。

実装上は channel decomposition が見える前者を推奨する。

source orientation を揃えるため

```text
D := -i * A
```

と置けば

```text
Re(D) = cfzpProjectedMirrorScalarDensity ε X W u
```

が exact に成り立つ。

さらに

```text
M+ := normSq(D + 1)
M- := normSq(D - 1)
```

と置くと pointwise に

```text
M+ >= 0
M- >= 0

M+ - M- = 4 * cfzpProjectedMirrorScalarDensity ε X W u

M+ + M- = 2 * (normSq(D) + 1)
```

となる。

これにより actual projected mirror density 全体が一つの two-mass polarization に乗る。

---

# 2. 新規 module

推奨 filename:

```text
lean/dk_math/DkMath/RH/CFBRC/
  CosmicFormulaZetaProjectedMirrorPolarizationAudit.lean
```

module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaProjectedMirrorPolarizationAudit
```

推奨 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaTopEdgeWeightedPolarizationAudit
import DkMath.RH.CFBRC.CosmicFormulaZetaMellinSourceProjection
import Mathlib.Tactic
```

`DkMath/RH.lean` に public import を追加する。

---

# 3. Gate A — three-channel weighted complex source

completed / Gamma channel の complex source wrapper を置く。

概念形:

```lean
noncomputable def cfzpFiniteMellinCompletedMirrorComplexSource
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℂ :=
  pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u *
    pascalCenteredXiPrimeSideFiniteCompletedZetaMirrorRate
      (pascalSymmetricRectangleTopEdge u W.rectangle.T)

noncomputable def cfzpFiniteMellinGammaMirrorComplexSource
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℂ :=
  pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u *
    pascalCenteredXiPrimeSideFiniteGammaMirrorRate
      (pascalSymmetricRectangleTopEdge u W.rectangle.T)
```

Euler channel は 006I の既存

```lean
cfzpFiniteMellinSymmetricEulerComplexSource
```

を再利用する。

総 source を

```lean
noncomputable def cfzpProjectedMirrorComplexSource
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℂ :=
  cfzpFiniteMellinCompletedMirrorComplexSource ε W u +
    cfzpFiniteMellinGammaMirrorComplexSource ε W u +
    cfzpFiniteMellinSymmetricEulerComplexSource ε X W u
```

としてよい。

load-bearing theorem:

```text
Im(cfzpProjectedMirrorComplexSource ε X W u)
  = cfzpProjectedMirrorScalarDensity ε X W u
```

証明は existing density definitions と `Complex.add_im` の algebra だけにする。

completed / Gamma / Euler の channel semantics を混ぜない。

---

# 4. Gate B — total deorientation

```lean
noncomputable def cfzpProjectedMirrorDeorientedSource
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℂ :=
  -Complex.I * cfzpProjectedMirrorComplexSource ε X W u
```

exact に

```text
Re(DeorientedSource) = cfzpProjectedMirrorScalarDensity
```

を証明する。

さらに

```text
normSq(DeorientedSource) = normSq(ProjectedMirrorComplexSource)
```

も記録してよい。

三 channel の deoriented decomposition

```text
DeorientedTotal
  = DeorientedCompleted + DeorientedGamma + DeorientedEuler
```

が安価なら記録する。

ただし `normSq(total) = sum normSq(channel)` は絶対に置かない。channel cross terms が存在する。

---

# 5. Gate C — projected quadratic mass

総 weighted projected source の quadratic mass を

```lean
noncomputable def cfzpProjectedMirrorWeightedQuadraticMass
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℝ :=
  Complex.normSq (cfzpProjectedMirrorDeorientedSource ε X W u)
```

としてよい。

必須:

```text
0 <= cfzpProjectedMirrorWeightedQuadraticMass
```

Euler-only の `FullPairSum` factorization を total source へ誤って昇格させない。

つまり次は置かない。

```text
ProjectedMirrorWeightedQuadraticMass
  = normSq(weight) * FullPairSum
```

これは completed / Gamma channel を落としてしまうため誤り。

必要なら frontier marker:

```lean
inductive CfzpProjectedQuadraticMassToEulerFullPairSumGap : Prop
  | completedGammaChannelsPreventDirectIdentification
```

---

# 6. Gate D — two nonnegative projected masses

```lean
noncomputable def cfzpProjectedMirrorPolarizedPlusMass ... : ℝ :=
  Complex.normSq (cfzpProjectedMirrorDeorientedSource ... + 1)

noncomputable def cfzpProjectedMirrorPolarizedMinusMass ... : ℝ :=
  Complex.normSq (cfzpProjectedMirrorDeorientedSource ... - 1)
```

両方 nonnegative を証明する。

006I の algebraic pattern を再利用し、exact に

```text
ProjectedPlusMass - ProjectedMinusMass
  = 4 * cfzpProjectedMirrorScalarDensity
```

を閉じる。

さらに

```text
ProjectedPlusMass + ProjectedMinusMass
  = 2 * (ProjectedWeightedQuadraticMass + 1)
```

を閉じる。

個別形も安価なら記録する。

```text
ProjectedPlusMass
  = ProjectedWeightedQuadraticMass + 1
    + 2 * ProjectedMirrorScalarDensity

ProjectedMinusMass
  = ProjectedWeightedQuadraticMass + 1
    - 2 * ProjectedMirrorScalarDensity
```

---

# 7. Gate E — pointwise balance

exact に

```text
ProjectedPlusMass = ProjectedMinusMass
  ↔ cfzpProjectedMirrorScalarDensity ε X W u = 0
```

を証明する。

ここでも

```text
ProjectedPlusMass = ProjectedMinusMass
  ↔ ProjectedMirrorComplexSource = 0
```

や zeta zero への shortcut は禁止する。

必要なら marker:

```lean
inductive CfzpProjectedPolarizationBalanceToComplexSourceZeroGap : Prop
  | noExactComplexSourceZeroIdentificationProvided
```

---

# 8. Gate F — TopZetaMismatchScalar の oriented polarized half-integral

既存 CFZP-005 theorem

```lean
pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar_eq_cfzpProjected_half_integral
```

をそのまま再利用する。

この theorem の hypotheses を変更・再証明しない。

同じ hypotheses の下で、pointwise Gate D を入れて

```text
TopZetaMismatchScalar
  = (1 / π) * ∫_{σ}^{1/2} ProjectedMirrorScalarDensity(u) du
```

を

```text
TopZetaMismatchScalar
  = (1 / (4 * π)) *
      ∫_{σ}^{1/2}
        (ProjectedPlusMass(u) - ProjectedMinusMass(u)) du
```

へ exact に書き直す。

係数の exact syntax は Lean に合わせてよい。

例えば

```text
(1 / Real.pi) * ∫ ((M+ - M-) / 4)
```

という中間形でもよいが、最終的には factor `4` と orientation が明示される形を推奨する。

## 重要: interval orientation

既存 rectangle contract では一般に

```text
1/2 <= σ
```

であり、`σ..1/2` は reverse oriented interval である。

したがって、この Gate では

```text
∫_{σ}^{1/2} M+
∫_{σ}^{1/2} M-
```

を「nonnegative integrated masses」と呼ばない。

pointwise `M+`, `M-` の nonnegativity と、oriented difference integral は別物として扱う。

今回の最低成功条件は **integral of the difference** まででよい。

正向き `1/2..σ` へ反転して二つの integrated masses に分離するのは次 Gate へ回してよい。

---

# 9. Gate G — channel decomposition audit

安価なら total complex source の exact channel decomposition を first-class に記録する。

```text
ProjectedMirrorComplexSource
  = CompletedComplexSource
    + GammaComplexSource
    + EulerComplexSource
```

これにより scalar difference側は

```text
ProjectedDensity
  = CompletedDensity + GammaDensity + EulerDensity
```

であることが既存 CFZP-005 と整合する。

一方 quadratic sum側は

```text
normSq(C + G + E)
```

であり、一般には

```text
normSq C + normSq G + normSq E
```

ではない。

必要なら marker:

```lean
inductive CfzpProjectedChannelQuadraticAdditivityGap : Prop
  | crossChannelInterferenceNotDiscarded
```

これは impossibility theorem ではない。

---

# 10. Firewall

今回も以下を禁止する。

- `ProjectedWeightedQuadraticMass = CompletionRemainder`
- `ProjectedWeightedQuadraticMass = RectangleBackground`
- `ProjectedWeightedQuadraticMass = TopZetaMismatchScalar`
- total projected quadratic mass と Euler-only `FullPairSum` の直接同一視
- `normSq(C + G + E) = normSq C + normSq G + normSq E`
- oriented `σ..1/2` の plus/minus integral を nonnegative mass と呼ぶこと
- balance と complex source zero の同一視
- balance と zeta zero の同一視
- source remainder positivity
- `SourceBig / SourceBody / SourceGap` の premature naming
- infinite Euler product
- RH conclusion
- `Complex.arg`
- 新しい global `Complex.log` branch
- `sorry` / `admit` / `axiom` / `native_decide`

---

# 11. 成功条件

最低限、次が Green なら CFZP-006J 完了とする。

```text
1. completed / Gamma complex source wrappers
2. existing 006I Euler complex source と三 channel total source を構成
3. Im(total complex source) = cfzpProjectedMirrorScalarDensity
4. deorientation 後 Re = projected scalar density
5. total quadratic mass の nonnegativity
6. two polarized masses の pointwise nonnegativity
7. plus-minus difference = 4 * projected density
8. plus-minus sum = 2 * (projected quadratic mass + 1)
9. mass balance iff projected density = 0
10. balance -> complex source zero を主張しない
11. existing CFZP-005 hypotheses 下で TopZetaMismatchScalar を polarized difference の oriented half-integralへ exact rewrite
12. reverse oriented interval の integrated nonnegativityを主張しない
13. channel quadratic cross terms を捨てない
14. DkMath.RH public import
15. target module build Green
16. lake build DkMath.RH Green
17. nested ./lean-build.sh Green
18. nested ./lean-test.sh Green
19. git diff --check Green
20. 新規 module に sorry / admit / axiom / native_decide / Complex.arg / Complex.log なし
```

---

# 12. 次 Gate への判断材料

006J が Green になれば、次は CFZP-006K を検討する。

候補は二つある。

第一候補は、reverse oriented half-integral を正向き `1/2..σ` へ反転し、十分な integrability certificate の下で

```text
TopZetaMismatchScalar
  = PositiveIntegratedMinusMass - PositiveIntegratedPlusMass
```

のような **difference of two genuinely nonnegative integrated masses** へ変換すること。

第二候補は、006A/006B 以来残っている

```text
RectangleBackground
  = TopZetaMismatchScalar + CompletionRemainder
```

へ今回の polarized TopMismatch 表現を代入し、CompletionRemainder を独立に保ったまま whole rectangle ledger を three-element 的に再分類すること。

どちらを先に行うかは 006J の実装 surface を監査して決める。
