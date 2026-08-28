# CFZP-0017 — CFZP-006M integrated polarized balance threshold audit 実装指示書

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
3b00f15bf91bd14d83f4019a8aea7269e0925d8b
Add: CFZP-0016: CFZP-006L forward integrated polarized mass audit
```

CFZP-006L 実装 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaForwardIntegratedPolarizedMassAudit
```

006L では、actual completed/Gamma/Euler projected source から作った pointwise polarized masses を forward interval `1/2 .. σ` 上で積分し、

```text
Pplus  := cfzpProjectedMirrorForwardIntegratedPlusMass
Pminus := cfzpProjectedMirrorForwardIntegratedMinusMass
```

として genuinely nonnegative な integrated masses を得た。

また exact に

```text
ForwardPolarizedInteractionIntegral
  = (Pminus - Pplus) / 4

TopMismatch
  = (1 / π) * ((Pminus - Pplus) / 4)

RectangleBackground
  = (1 / π) * ((Pminus - Pplus) / 4)
    + CompletionRemainder

RadialContactDeficit
  = π * RectangleBackground
    - (Pminus - Pplus) / 4
```

まで閉じている。

今回 CFZP-006M の目的は、ここで現れた二種類の balance を exact に分類することである。

---

# 1. 数学的核心 — 二種類の balance を分離する

略記:

```text
P+ := ForwardIntegratedPlusMass
P- := ForwardIntegratedMinusMass
B  := RectangleBackground
R  := CompletionRemainder
G  := RadialContactDeficit
Δ  := P- - P+
```

006L/006K により

```text
TopMismatch = Δ / (4π)
R = B - Δ / (4π)
G = π B - Δ / 4
```

である。

ここから二つの異なる balance が現れる。

## 1.1 polarized mass balance

```text
P- = P+
```

すなわち

```text
Δ = 0
```

これは exact に

```text
TopMismatch = 0
```

に対応する。

しかし一般には radial contact ではない。

この balance の下では

```text
R = B
G = π B
```

であり、背景量 `B` が残る。

## 1.2 radial-contact balance threshold

```text
Δ = 4π B
```

これは exact に

```text
R = 0
G = 0
```

に対応する。

したがって

```text
P- = P+
```

と

```text
P- - P+ = 4π B
```

は別の balance 条件である。

今回の最重要 semantic point はこの分離である。

---

# 2. 推奨 module

新規 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaIntegratedPolarizedBalanceThresholdAudit
```

path:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaIntegratedPolarizedBalanceThresholdAudit.lean
```

推奨 imports:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaForwardIntegratedPolarizedMassAudit
import Mathlib.Tactic
```

必要なら既存 source completion module を直接 import してもよいが、006L から十分に到達できるなら増やさない。

`DkMath/RH.lean` に public import を追加する。

---

# 3. Gate A — integrated polarization difference の補助記法（任意）

実装が読みやすくなるなら

```lean
noncomputable def cfzpProjectedMirrorForwardIntegratedPolarizationDifference
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  cfzpProjectedMirrorForwardIntegratedMinusMass ε X W -
    cfzpProjectedMirrorForwardIntegratedPlusMass ε X W
```

を置いてよい。

ただし既存 theorem の statement を unnecessary に wrapper だらけにしない。

今回の核心は definition 追加ではなく threshold classification である。

---

# 4. Gate B — integrated mass balance ↔ TopMismatch zero

006L の TopMismatch theorem と `Real.pi_ne_zero` を使う。

既存 CFZP-005/006J hypotheses をそのまま継承し、exact に

```text
Pminus = Pplus
  ↔ TopZetaMismatchScalar = 0
```

を証明する。

推奨 theorem 名:

```lean
pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar_eq_zero_iff_integratedPolarizedMass_balance
```

statement の向きは naming style に合わせてよい。

同様に安価なら order classification も記録する。

```text
Pplus <= Pminus
  ↔ 0 <= TopMismatch

Pminus <= Pplus
  ↔ TopMismatch <= 0
```

これは `π > 0` の純代数である。

ただしこの sign classification から zeta zero / RH へ進まない。

---

# 5. Gate C — CompletionRemainder zero threshold

006L rectangle ledger

```text
B = Δ/(4π) + R
```

または 006K の remainder rearrangement を使い、exact に

```text
R = 0
  ↔ Δ = 4 * π * B
```

を証明する。

factor normalization は Lean に合わせてよい。

例えば以下は数学的に同値:

```text
Δ / 4 = π * B
Δ = 4 * π * B
B = Δ / (4 * π)
```

最終 theorem では可能なら

```text
Pminus - Pplus = 4 * Real.pi * RectangleBackground
```

の形を一つ用意する。

これが **radial-contact balance threshold** の arithmetic form である。

---

# 6. Gate D — RadialContactDeficit zero threshold

006L の

```text
G = π * B - Δ / 4
```

から exact に

```text
G = 0
  ↔ Δ = 4 * π * B
```

を証明する。

さらに Gate C と合わせて

```text
R = 0 ↔ G = 0
```

も今回の surface 上で再提示してよい。

既存 source completion geometry にすでに `G = πR` があるので、重複証明ではなく threshold form への bridge として記録する。

---

# 7. Gate E — sign threshold classification

今回の第二 load-bearing result。

`π > 0` を使い、exact に

```text
0 <= R
  ↔ Δ <= 4 * π * B

R <= 0
  ↔ 4 * π * B <= Δ
```

を証明する。

RadialContactDeficit についても

```text
0 <= G
  ↔ Δ <= 4 * π * B

G <= 0
  ↔ 4 * π * B <= Δ
```

を証明する。

ここで大事なのは、これは **sign provider ではなく sign condition の exact translation** だということ。

次は絶対に主張しない。

```text
0 <= R
0 <= G
Δ <= 4πB
```

の無条件 theorem。

今回得るのは iff classification のみ。

---

# 8. Gate F — polarized mass balance の下で残る background

`hBal : Pminus = Pplus` を仮定し、exact に

```text
TopMismatch = 0
CompletionRemainder = RectangleBackground
RadialContactDeficit = π * RectangleBackground
```

を記録する。

特に

```text
hBal ->
  (RadialContactDeficit = 0 ↔ RectangleBackground = 0)
```

を証明する。

同様に

```text
hBal ->
  (CompletionRemainder = 0 ↔ RectangleBackground = 0)
```

も安価なら記録する。

これにより

```text
Pminus = Pplus
```

だけでは radial contact zero へ到達しない理由が formal surface に現れる。

ただし actual counterexample を構成したとは言わない。

これは implication gap の分類である。

---

# 9. Gate G — 二つの balance の同時成立条件（推奨）

純代数として安価なら、

```text
(Pminus = Pplus ∧
  Pminus - Pplus = 4 * π * RectangleBackground)
↔
(Pminus = Pplus ∧ RectangleBackground = 0)
```

を証明してよい。

または `hBal` の下で

```text
radialContactThreshold ↔ RectangleBackground = 0
```

の形でもよい。

これが「polarized balance」と「contact balance」が一致するために追加で必要な条件を明示する。

---

# 10. Frontier markers

今回も source zero / zeta zero へは進まない。

必要なら以下のような markers を置く。

```lean
inductive CfzpIntegratedMassBalanceToPointwiseProjectedDensityGap : Prop
  | noPointwiseVanishingFromIntegratedBalanceProvided

inductive CfzpIntegratedMassBalanceToZetaZeroGap : Prop
  | noZetaZeroIdentificationProvided

inductive CfzpRadialContactThresholdSignProviderGap : Prop
  | noIndependentThresholdInequalityProviderProvided
```

marker 名は既存 naming style に合わせて調整してよい。

重要なのは以下を区別すること。

```text
integrated mass balance
TopMismatch zero
radial-contact threshold
CompletionRemainder sign
pointwise projected density zero
complex source zero
zeta zero
```

---

# 11. Firewall

今回も以下を禁止する。

- `Pminus = Pplus -> RadialContactDeficit = 0` の無条件 shortcut
- `Pminus = Pplus -> CompletionRemainder = 0` の無条件 shortcut
- integrated balance から pointwise `Mplus=Mminus` を推論
- integrated balance から projected density pointwise zero を推論
- integrated balance から projected complex source zero を推論
- integrated balance / TopMismatch zero と zeta zero の同一視
- `CompletionRemainder >= 0` の無条件 provider
- `RadialContactDeficit >= 0` の無条件 provider
- `RectangleBackground >= 0` の無条件 provider
- `Pminus - Pplus <= 4πB` の無条件 provider
- `SourceBig / SourceBody / SourceGap` の premature naming
- total projected quadratic mass と Euler-only FullPairSum の同一視
- channel cross terms の消去
- infinite Euler product
- X -> infinity
- RH conclusion
- `Complex.arg`
- 新しい global `Complex.log` branch
- `sorry` / `admit` / `axiom` / `native_decide`

---

# 12. 成功条件

最低限、次が Green なら CFZP-006M 完了とする。

```text
1. Pminus = Pplus ↔ TopMismatch = 0
2. CompletionRemainder = 0 ↔ Pminus - Pplus = 4π * RectangleBackground
3. RadialContactDeficit = 0 ↔ Pminus - Pplus = 4π * RectangleBackground
4. 0 <= CompletionRemainder ↔ Pminus - Pplus <= 4π * RectangleBackground
5. 0 <= RadialContactDeficit ↔ Pminus - Pplus <= 4π * RectangleBackground
6. reverse sign versionsも可能なら記録
7. integrated mass balance 下で CompletionRemainder = RectangleBackground
8. integrated mass balance 下で RadialContactDeficit = π * RectangleBackground
9. integrated mass balance alone を radial contact zero と同一視しない
10. pointwise/source/zeta zero へ進まない
11. independent threshold sign provider を捏造しない
12. DkMath.RH public import
13. target module build Green
14. lake build DkMath.RH Green
15. nested ./lean-build.sh Green
16. nested ./lean-test.sh Green
17. git diff --check Green
18. 新規 module に sorry / admit / axiom / native_decide / Complex.arg / Complex.log なし
```

---

# 13. 次 Gate への判断材料

006M が Green になれば、CFZP source-side rectangle ledger は概念的に

```text
Pplus >= 0
Pminus >= 0

polarized balance:
  Pminus = Pplus
  ↔ TopMismatch = 0

contact balance:
  Pminus - Pplus = 4π * RectangleBackground
  ↔ CompletionRemainder = 0
  ↔ RadialContactDeficit = 0
```

まで exact に整理される。

ここで初めて「二つの非負総質量の balance」と「rectangle background に対する contact threshold」が明確に分離される。

次 CFZP-006N の第一候補は、

1. `RectangleBackground` 自体の algebraic decomposition を既存 CS30/CS23/CS24/CS25 から再監査し、
2. どの部分が fixed radial / archimedean / elementary / complement boundary / prime interaction なのかを source-side Big/Body/interaction 語彙を premature に使わず分類し、
3. contact threshold `Δ = 4πB` を満たすために不足している **独立 inequality / sign provider の正体**を frontier theorem として切り出す、

という background-provider audit とする。

006M でも RH や zero-set へは進まない。