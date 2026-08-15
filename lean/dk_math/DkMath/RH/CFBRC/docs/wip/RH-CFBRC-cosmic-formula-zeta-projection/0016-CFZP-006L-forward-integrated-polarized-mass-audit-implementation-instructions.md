# CFZP-0016 — CFZP-006L forward integrated polarized mass audit 実装指示書

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
fb7014cd809dbc841db3675c5d93b97c2351f6b1
Add: CFZP-0015: CFZP-006K forward polarized rectangle completion ledger
```

CFZP-006K 実装 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaForwardPolarizedRectangleCompletionAudit
```

006K は forward signed interaction

```text
I_pol(ε,X,W)
  := ∫ u in (1/2)..σ,
       (ProjectedMinusMass(u) - ProjectedPlusMass(u)) / 4
```

を導入し、既存 hypotheses の下で exact に

```text
TopZetaMismatchScalar = I_pol / π

RectangleBackground
  = I_pol / π + CompletionRemainder

RadialContactDeficit
  = π * RectangleBackground - I_pol

RectangleBackground
  = I_pol / π
    + FixedRadialSecondMoment
    - IndependentCompleteSourceReal
```

まで接続した。

006K では意図的に `I_pol` を nonnegative mass と呼ばず、個別 `M+`, `M-` の積分も導入しなかった。

今回 CFZP-006L では、safe finite top interval 上の既存 continuity を使い、個別 polarized masses の forward interval-integrability を内部で構成する。その上で

```text
P+ := ∫_{1/2}^{σ} M+(u) du
P- := ∫_{1/2}^{σ} M-(u) du
```

を **genuine nonnegative integrated masses** として first-class に導入し、

```text
I_pol = (P- - P+) / 4
```

を exact に閉じる。

新しい zeta-free 仮定、global continuity 仮定、infinite limit は追加しない。

---

# 1. 推奨新規 module

```text
DkMath.RH.CFBRC.CosmicFormulaZetaForwardIntegratedPolarizedMassAudit
```

path:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaForwardIntegratedPolarizedMassAudit.lean
```

推奨 imports:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaForwardPolarizedRectangleCompletionAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideFiniteResidualIntervalLocalRegularityAudit
import Mathlib.Tactic
```

最後に

```text
DkMath/RH.lean
```

へ public import を追加する。

---

# 2. 既存 exact infrastructure

今回の重要な既存 theorem は CS34 の

```lean
pascalCenteredXiPrimeSideFiniteResidualLogRate_continuousOn_of_safe
```

である。

safe finite top interval

```text
Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)
```

上で residual log rate は continuous。

また CS35 には mirror map が safe interval を保存する

```lean
pascalCenteredXiPrimeSideFiniteResidual_top_safe_mirror
```

がある。

CS37 には exact に

```lean
pascalCenteredXiPrimeSideFiniteResidualMirrorRate_eq_functionalEquationRate
```

があり、safe point `u` で

```text
ResidualMirrorRate_X,W(u)
  = CompletedMirrorRate(topEdge u)
    + GammaMirrorRate(topEdge u)
    + SymmetricEulerRate_X(topEdge u)
```

を与える。

従って CFZP-006J の total projected complex source は safe interval 上で

```text
ProjectedMirrorComplexSource(ε,X,W,u)
  = TopMellinWeight(ε,W,u) * ResidualMirrorRate_X,W(u)
```

へ exact に戻せる。

この identity を continuity bridge として使う。

---

# 3. Gate A — forward interval geometry

既存 rectangle contract から

```text
1/2 <= W.rectangle.σ
```

を得る。

forward interval

```text
[1/2, σ]
```

は safe unoriented interval

```text
Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)
```

に含まれる。

cheap なら helper theorem を置く。

概念形:

```text
u ∈ Set.Icc (1/2) σ
  -> u ∈ Set.uIcc σ (1-σ)
```

または `Set.uIcc (1/2) σ` から safe `uIcc` への inclusion でもよい。

ここでは `σ..1/2` に戻さない。今回の individual masses は positive-direction interval `1/2..σ` 上で定義する。

---

# 4. Gate B — total projected source を residual mirror source に戻す

次の exact theorem を first-class に置くことを推奨する。

概念形:

```text
cfzpProjectedMirrorComplexSource ε X W u
  = pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u
    * pascalCenteredXiPrimeSideFiniteResidualMirrorRate X W u
```

仮定:

```text
hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W
hu    : u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)
```

証明は

```lean
pascalCenteredXiPrimeSideFiniteResidualMirrorRate_eq_functionalEquationRate
```

と 006J の three-channel source definitions の algebra だけで行う。

completed / Gamma / Euler 各 channel を個別に continuity 証明し直さない。

この bridge は今回の重要な dependency firewall である。

---

# 5. Gate C — safe interval continuity

## 5.1 Top Mellin weight

CS34 内には同趣旨の continuity proof があるが helper が private なら、新 module 側で最小限再構成してよい。

使う public infrastructure は

```lean
pascalCenteredXiMellinSecondDifferenceWeight_differentiable
```

と affine top-edge path の continuity。

`hε : 0 < ε` の下で

```text
ContinuousOn
  (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W)
  (Set.uIcc σ (1-σ))
```

または forward subinterval 上の continuity を得る。

private theorem のコピーではなく、同じ public facts から local proof を再構成する。

## 5.2 Residual mirror rate

既存

```lean
pascalCenteredXiPrimeSideFiniteResidualLogRate_continuousOn_of_safe
```

から

```text
ResidualMirrorRate(u)
  = ResidualLogRate(u)
    - conj(ResidualLogRate(1-u))
```

を使い、safe interval 上の `ContinuousOn` を証明する。

mirror map `u -> 1-u` が safe interval を保存することには

```lean
pascalCenteredXiPrimeSideFiniteResidual_top_safe_mirror
```

を使う。

## 5.3 Projected complex source / deoriented source

Gate B の exact source rewrite と 5.1 / 5.2 を使って

```text
ContinuousOn ProjectedMirrorComplexSource forwardInterval
ContinuousOn ProjectedMirrorDeorientedSource forwardInterval
```

を得る。

この段階で zeta / Gamma 各 channel の global continuity は導入しない。

---

# 6. Gate D — polarized pointwise masses の integrability

006J の

```text
cfzpProjectedMirrorPolarizedPlusMass
cfzpProjectedMirrorPolarizedMinusMass
```

はそれぞれ

```text
normSq(D + 1)
normSq(D - 1)
```

である。

Gate C から forward interval 上の continuity を得て、exact に

```text
IntervalIntegrable
  (cfzpProjectedMirrorPolarizedPlusMass ε X W)
  volume (1/2) σ

IntervalIntegrable
  (cfzpProjectedMirrorPolarizedMinusMass ε X W)
  volume (1/2) σ
```

を証明する。

これらは `hε : 0 < ε` と `hSafe` から内部で生成し、外部 `hPlus/hMinus` を新たな theorem argument として要求しないことを第一候補とする。

Lean API 上どうしても不自然に重い場合のみ、integrability certificate を別 theorem に分離してよいが、最終 integrated-mass theorem は既存 `hε,hSafe` から到達可能にする。

---

# 7. Gate E — genuine forward integrated masses

次を定義する。

```lean
noncomputable def cfzpProjectedMirrorForwardIntegratedPlusMass
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  ∫ u in (1 / 2 : ℝ)..W.rectangle.σ,
    cfzpProjectedMirrorPolarizedPlusMass ε X W u

noncomputable def cfzpProjectedMirrorForwardIntegratedMinusMass
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  ∫ u in (1 / 2 : ℝ)..W.rectangle.σ,
    cfzpProjectedMirrorPolarizedMinusMass ε X W u
```

短い aliases は naming style に合わせてよい。

既存 rectangle orientation から `1/2 <= σ` を使い、pointwise nonnegativity から

```text
0 <= ForwardIntegratedPlusMass
0 <= ForwardIntegratedMinusMass
```

を証明する。

この二つは今回初めて **integrated nonnegative masses** と呼んでよい。

なお equality zero の characterization は今回不要。

---

# 8. Gate F — signed interaction を二つの integrated masses の差へ fold

006K の

```lean
cfzpProjectedMirrorForwardPolarizedInteractionIntegral
```

について、Gate D の interval-integrability を使って exact に

```text
cfzpProjectedMirrorForwardPolarizedInteractionIntegral ε X W
  = (ForwardIntegratedMinusMass ε X W
      - ForwardIntegratedPlusMass ε X W) / 4
```

を証明する。

ここでは `intervalIntegral.integral_sub` / `integral_div` 等、現行 Mathlib v4.33.0 の API を使う。

factor `4` と minus/plus の順序を Lean に確認させる。

006K の forward integrand は

```text
(Mminus - Mplus) / 4
```

なので順序を逆転しない。

---

# 9. Gate G — TopMismatch / rectangle / radial defect の integrated-mass 表現

既存 006K theorem を Gate F で rewrite する。

## 9.1 TopMismatch

同じ CFZP-005/006J hypotheses の下で

```text
TopZetaMismatchScalar
  = (1 / π) * ((Pminus - Pplus) / 4)
```

を exact に得る。

等価な

```text
TopZetaMismatchScalar
  = (Pminus - Pplus) / (4 * π)
```

まで整形してもよいが、division normalization を無理に行う必要はない。

## 9.2 Rectangle background

```text
RectangleBackground
  = (1 / π) * ((Pminus - Pplus) / 4)
    + CompletionRemainder
```

## 9.3 Radial contact deficit

```text
RadialContactDeficit
  = π * RectangleBackground
    - (Pminus - Pplus) / 4
```

## 9.4 Independent complete source ledger

安価なら

```text
RectangleBackground
  = (1 / π) * ((Pminus - Pplus) / 4)
    + FixedRadialSecondMoment
    - IndependentCompleteSourceReal
```

まで exact に fold する。

これらの theorem は既存 006K hypotheses をそのまま継承し、仮定を弱めたように見せない。

---

# 10. Gate H — integrated balance（推奨）

純代数として安価なら

```text
ForwardIntegratedPlusMass = ForwardIntegratedMinusMass
  ↔ cfzpProjectedMirrorForwardPolarizedInteractionIntegral = 0
```

を証明してよい。

さらに既存 TopMismatch theorem の hypotheses 下では

```text
ForwardIntegratedPlusMass = ForwardIntegratedMinusMass
  ↔ TopZetaMismatchScalar = 0
```

も exact に得られる。

ただしこれは **net integrated balance** であり、次とは同一視しない。

```text
forall u, M+(u) = M-(u)
ProjectedMirrorScalarDensity(u) = 0 pointwise
ProjectedMirrorComplexSource(u) = 0 pointwise
riemannZeta(s) = 0
```

必要なら frontier marker を置く。

```lean
inductive CfzpIntegratedPolarizedBalanceToPointwiseBalanceGap : Prop
  | noPointwiseBalanceFromIntegratedCancellationProvided
```

---

# 11. Firewall

今回も以下を禁止する。

- `ForwardIntegratedPlusMass` / `ForwardIntegratedMinusMass` の pointwise zero characterization を無根拠に置く
- integrated balance から pointwise balance を推論する
- integrated balance から complex source zero を推論する
- integrated balance から zeta zero を推論する
- `CompletionRemainder >= 0` の新規 provider
- `RectangleBackground >= 0` の新規 provider
- `RadialContactDeficit >= 0` の新規 provider
- `Pminus >= Pplus` または逆向きの sign theorem
- total projected quadratic mass と Euler-only FullPairSum の同一視
- channel cross terms の消去
- `SourceBig / SourceBody / SourceGap` の premature naming
- infinite Euler product
- X -> infinity
- RH conclusion
- `Complex.arg`
- 新しい global `Complex.log` branch
- `sorry` / `admit` / `axiom` / `native_decide`

---

# 12. 成功条件

最低限、次が Green なら CFZP-006L 完了とする。

```text
1. forward interval 1/2..σ が safe top interval に含まれることを整理
2. safe point で ProjectedMirrorComplexSource = TopMellinWeight * ResidualMirrorRate を exact に証明
3. hε,hSafe から forward interval 上の total projected source continuity を得る
4. polarized plus/minus mass の forward IntervalIntegrable を内部生成
5. Pplus / Pminus を individual forward integrated masses として定義
6. 0 <= Pplus
7. 0 <= Pminus
8. ForwardPolarizedInteractionIntegral = (Pminus - Pplus)/4
9. TopMismatch を Pminus-Pplus で exact 表示
10. RectangleBackground / CompletionRemainder ledger を Pminus-Pplus へ fold
11. RadialContactDeficit ledger を Pminus-Pplus へ fold
12. integrated balance を pointwise/source/zeta zero と同一視しない
13. DkMath.RH public import
14. target module build Green
15. lake build DkMath.RH Green
16. nested ./lean-build.sh Green
17. nested ./lean-test.sh Green
18. git diff --check Green
19. 新規 module に sorry / admit / axiom / native_decide / Complex.arg / Complex.log なし
```

Gate H と independent complete-source fold は推奨だが、Lean API 上不自然に重い場合は次へ回してよい。

---

# 13. 次 Gate への判断材料

006L が Green になれば、whole rectangle ledger は概念的に

```text
Pplus >= 0
Pminus >= 0

TopMismatch = (Pminus - Pplus) / (4π)

RectangleBackground
  = (Pminus - Pplus) / (4π)
    + CompletionRemainder

RadialContactDeficit
  = π * RectangleBackground
    - (Pminus - Pplus) / 4
```

となる。

ここで初めて、actual completed/Gamma/Euler projected source から作った **二つの genuine nonnegative total masses** が rectangle completion ledger に入る。

次 CFZP-006M の候補は、

1. `RadialContactDeficit = 0` を integrated-mass balance threshold
   `Pminus - Pplus = 4π * RectangleBackground` と exact に分類する、
2. CompletionRemainder sign frontier を
   `Pminus - Pplus <= 4π * RectangleBackground`
   のような threshold statement へ exact に翻訳する、
3. source-zero / zero-set へは進まず、どの独立 sign provider が本当に不足しているかを明示する、

という **integrated balance threshold audit** を第一候補とする。
