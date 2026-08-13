# XDP-021 — Ordered arithmetic fixed-Xi defect representation 実装指示書

作成日: 2026-08-13

## 0. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-prime-side-explicit-formula-260813-v0
workdir: lean/dk_math
Lean / Mathlib: repository pinned toolchain
```

XDP-020 は `Ideal Green through Gate H` で閉じた。

現在、固定 finite residue window `W` に対して、各 fixed `ε > 0` で finite Pascal/von Mangoldt arithmetic approximant を先に `X → ∞` へ送り、その endpoint を `ε → 0+` へ送る ordered certificate が Green である。

主要 endpoint は次である。

```lean
pascalCenteredXiMellinQuadraticArithmeticApproximant
pascalCenteredXiMellinQuadraticArithmeticEndpoint
tendsto_pascalCenteredXiMellinQuadraticArithmeticApproximant
tendsto_pascalCenteredXiMellinQuadraticArithmeticEndpoint_secondContour
pascalCenteredXiMellinQuadraticIteratedLimitCertificate
```

XDP-020 の arithmetic endpoint は unnormalized fixed second contour mass へ収束する。

```text
A_ε  →  pascalCenteredXiSecondOuterContourMass W.R
```

一方、既存 fixed-Xi defect は normalized holomorphic second contour を用いる。

```lean
pascalCenteredXiFixedHolomorphicSecondContourFunctional R :=
  (2 * Real.pi * Complex.I)⁻¹ *
    pascalCenteredXiSecondOuterContourMass R

pascalCenteredXiFixedSecondMomentDefectFunctional R :=
  pascalCenteredXiFixedRadialSecondMomentFunctional R -
    (pascalCenteredXiFixedHolomorphicSecondContourFunctional R).re
```

従って XDP-021 の目的は、XDP-020 arithmetic observable を同じ normalization へ移し、fixed radial observable と差を取ることで、fixed-Xi defect 自体を ordered arithmetic endpoint として表現することである。

目標 chain は次である。

```text
fixed ε > 0
finite Pascal/von Mangoldt arithmetic approximant A(ε,X)
        ↓ normalize by (2πi)⁻¹
finite arithmetic holomorphic approximant H(ε,X)
        ↓ X → ∞
quadratic-Mellin holomorphic endpoint Hε
        ↓ ε → 0+
fixed holomorphic second-contour functional
        ↓ subtract real part from fixed radial observable
fixed Xi second-moment defect
```

本 phase は **representation phase** である。

次を証明してはならない。

```text
arithmetic defect approximant ≤ 0
arithmetic defect approximant ≥ 0
eventual sign of the approximants
fixed Xi defect = 0
fixed Xi defect ≤ 0
critical-line concentration
RH
```

既存 theorem により fixed defect の非負性や horizontal energy 表現は既知だが、それを prime-side から新たに導出したかのように扱わないこと。

また次も scope 外である。

```text
X ↔ ε の極限交換
joint/product-filter limit
uniform-in-ε prime cutoff convergence
right-edge / Gamma / elementary / top integral内部への ε → 0+
T → ∞
horizontal contributionの消去
R → ∞
```

---

## 1. 既存 Green API

### XDP-020

```lean
pascalCenteredXiMellinQuadraticZeroMoment
pascalCenteredXiMellinQuadraticArithmeticApproximant
pascalCenteredXiMellinQuadraticArithmeticEndpoint
tendsto_pascalCenteredXiMellinQuadraticArithmeticApproximant
pascalCenteredXiMellinQuadraticArithmeticApproximant_eq_vonMangoldt_sum
tendsto_pascalCenteredXiMellinQuadraticArithmeticEndpoint_epsilon
tendsto_pascalCenteredXiMellinQuadraticArithmeticEndpoint_secondContour
pascalCenteredXiMellinQuadraticIteratedLimitCertificate
```

XDP-020 endpoint definition:

```lean
pascalCenteredXiMellinQuadraticArithmeticEndpoint ε W :=
  -(2 * Real.pi * Complex.I) *
    pascalCenteredXiMellinQuadraticZeroMoment ε W
```

### fixed defect bridge

```lean
pascalCenteredXiFixedRadialSecondMomentFunctional
pascalCenteredXiFixedRadialSecondMomentFunctional_eq_cf2dRadial
pascalCenteredXiFixedHolomorphicSecondContourFunctional
pascalCenteredXiFixedSecondMomentDefectFunctional
pascalCenteredXiFixedSecondMomentDefectFunctional_eq_cf2d_sub_secondContour_re
pascalCenteredXiFixedSecondMomentDefectFunctional_eq_two_mul_horizontalEnergy
pascalCenteredXiFixedSecondMomentDefectFunctional_nonneg
```

`PascalCenteredXiResidueTransportWindow` は `circle_safe` を保持するため、`W.R` に対する safe-radius theorem は追加仮定なしで利用できる。

---

# Gate A — normalized arithmetic holomorphic observable

XDP-020 arithmetic approximant と endpoint を fixed contour convention と同じ `(2πi)⁻¹` で normalize する。

推奨 definition:

```lean
noncomputable def pascalCenteredXiMellinQuadraticNormalizedArithmeticApproximant
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ *
    pascalCenteredXiMellinQuadraticArithmeticApproximant ε W X

noncomputable def pascalCenteredXiMellinQuadraticNormalizedArithmeticEndpoint
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ *
    pascalCenteredXiMellinQuadraticArithmeticEndpoint ε W
```

endpoint は quadratic zero moment の負号付き値へ algebraically collapse する。

推奨 theorem:

```lean
theorem pascalCenteredXiMellinQuadraticNormalizedArithmeticEndpoint_eq
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiMellinQuadraticNormalizedArithmeticEndpoint ε W =
      -pascalCenteredXiMellinQuadraticZeroMoment ε W
```

ここでは `Real.pi ≠ 0` と `Complex.I ≠ 0` を明示してよい。

重要:

```text
(2πi)⁻¹ × (-(2πi) × Mε) = -Mε
```

という normalization の符号を誤らないこと。

---

# Gate B — fixed-ε normalized arithmetic convergence

XDP-020 の fixed-`ε` arithmetic Tendsto を continuous scalar multiplication で normalize する。

推奨 theorem:

```lean
theorem tendsto_pascalCenteredXiMellinQuadraticNormalizedArithmeticApproximant
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    Tendsto
      (fun X =>
        pascalCenteredXiMellinQuadraticNormalizedArithmeticApproximant ε W X)
      atTop
      (nhds
        (pascalCenteredXiMellinQuadraticNormalizedArithmeticEndpoint ε W))
```

この theorem は fixed `ε` のみを扱う。

`ε` についての uniformity を追加しない。

---

# Gate C — normalized endpoint の epsilon closure

XDP-020 の

```lean
tendsto_pascalCenteredXiMellinQuadraticArithmeticEndpoint_secondContour
```

を `(2πi)⁻¹` で normalize し、既存

```lean
pascalCenteredXiFixedHolomorphicSecondContourFunctional
```

へ接続する。

推奨 theorem:

```lean
theorem tendsto_pascalCenteredXiMellinQuadraticNormalizedArithmeticEndpoint_epsilon
    (W : PascalCenteredXiResidueTransportWindow) :
    Tendsto
      (fun ε : ℝ =>
        pascalCenteredXiMellinQuadraticNormalizedArithmeticEndpoint ε W)
      (𝓝[>] 0)
      (nhds
        (pascalCenteredXiFixedHolomorphicSecondContourFunctional W.R))
```

第一候補 proof route:

```text
XDP-020 secondContour Tendsto
→ continuous multiplication by constant (2πi)⁻¹
→ unfold pascalCenteredXiFixedHolomorphicSecondContourFunctional
```

zero-moment theoremを再展開する必要はない。

---

# Gate D — arithmetic defect approximant / endpoint

fixed radial observable を保持し、normalized arithmetic holomorphic observable の実部を引く。

推奨 definitions:

```lean
noncomputable def pascalCenteredXiMellinQuadraticArithmeticDefectApproximant
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℝ :=
  pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
    (pascalCenteredXiMellinQuadraticNormalizedArithmeticApproximant ε W X).re

noncomputable def pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
    (pascalCenteredXiMellinQuadraticNormalizedArithmeticEndpoint ε W).re
```

この definition では radial side を `ε` や `X` に依存させないこと。

radial side は既存 fixed observable のまま保持する。

### 禁止

arithmetic approximant の有限 `X` 値を、finite zero-window defect や horizontal energy と同一視しない。

有限 `X` ではあくまで prime cutoff approximant である。

---

# Gate E — fixed-ε arithmetic defect convergence

Gate B の complex Tendsto を `Complex.re` と固定実数差へ transport する。

推奨 theorem:

```lean
theorem tendsto_pascalCenteredXiMellinQuadraticArithmeticDefectApproximant
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    Tendsto
      (fun X =>
        pascalCenteredXiMellinQuadraticArithmeticDefectApproximant ε W X)
      atTop
      (nhds
        (pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W))
```

proof は概念的に次だけでよい。

```text
normalized complex approximant Tendsto
→ Complex.re の continuity
→ fixed radial constant minus real part
```

新しい analytic estimate は不要。

---

# Gate F — arithmetic defect endpoint の epsilon closure

Gate C の normalized holomorphic endpoint theorem を real part と fixed radial differenceへ transport する。

principal theorem:

```lean
theorem tendsto_pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint_epsilon
    (W : PascalCenteredXiResidueTransportWindow) :
    Tendsto
      (fun ε : ℝ =>
        pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W)
      (𝓝[>] 0)
      (nhds
        (pascalCenteredXiFixedSecondMomentDefectFunctional W.R))
```

これは XDP-021 の主要 endpoint である。

proof は

```text
normalized arithmetic endpoint
→ fixed holomorphic second contour
→ real part
→ fixed radial subtraction
→ unfold fixed defect
```

だけで閉じるべきである。

ここで `W.circle_safe` 以外の新規 provider assumption を導入しない。

---

# Gate G — ordered prime-side defect certificate

XDP-020 と同様に、二変数 Tendsto へ偽装せず conjunction で ordered chain を theorem 化する。

principal certificate:

```lean
theorem pascalCenteredXiMellinQuadraticArithmeticDefectIteratedLimitCertificate
    (W : PascalCenteredXiResidueTransportWindow) :
    (∀ ε : ℝ, 0 < ε →
      Tendsto
        (fun X =>
          pascalCenteredXiMellinQuadraticArithmeticDefectApproximant ε W X)
        atTop
        (nhds
          (pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W))) ∧
    Tendsto
      (fun ε : ℝ =>
        pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W)
      (𝓝[>] 0)
      (nhds
        (pascalCenteredXiFixedSecondMomentDefectFunctional W.R))
```

この theorem が意味するのは厳密に

```text
lim ε→0+ (lim X→∞ D(ε,X,W))
  = fixed Xi defect at W.R
```

という ordered representation である。

reverse order、joint limit、uniform convergence は含まない。

---

# Gate H — finite von Mangoldt defect surface

finite `X` の arithmetic defect approximant が、実際に XDP-020 の finite von Mangoldt surface から構成されていることを theorem として露出する。

第一候補は、XDP-020 の

```lean
pascalCenteredXiMellinQuadraticArithmeticApproximant_eq_vonMangoldt_sum
```

を normalized arithmetic approximantへ lift し、その実部を fixed radial observable から引くことである。

推奨 theorem shape:

```lean
theorem pascalCenteredXiMellinQuadraticArithmeticDefectApproximant_eq_vonMangoldt_surface
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinQuadraticArithmeticDefectApproximant ε W X =
      pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
        (((2 * Real.pi * Complex.I)⁻¹ *
          (
            2 * finiteVonMangoldtQuadraticRightEdgeSum ε W X +
            2 * archimedeanCorrection ε W +
            2 * elementaryCorrection ε W +
            2 * topHorizontalCorrection ε W
          )).re)
```

上の helper 名は説明用であり、実装では既存 exact RHS をそのまま使うか、必要最小限の named helper を導入すること。

巨大な重複式が可読性を壊す場合は、次のどちらかを選んでよい。

```text
1. normalized complex von Mangoldt surface theoremを先に作り、defect theoremはそれを使用
2. XDP-020 approximant theoremを rewrite して defect theoremを直接作る
```

重要なのは、finite defect approximant の arithmetic content が theorem surface から見えることである。

`Complex.cpow` は維持し、`Complex.arg`、偏角、三角関数展開へ崩さない。

---

# Gate I — CF2D compatibility / target ledger

可能なら Ideal Green として、fixed radial observable を既存 CF2D radial massへ rewrite した finite arithmetic defect surfaceを追加する。

概念形:

```text
D(ε,X,W)
  = CF2D radial q2 mass(W.R)
    - Re(normalized arithmetic holomorphic approximant)
```

使用 theorem:

```lean
pascalCenteredXiFixedRadialSecondMomentFunctional_eq_cf2dRadial
```

`W.circle_safe` から safe-radius obligation を discharge する。

ただし次の既存 target theorem は **監査用 reference** とし、XDP-021 の新しい arithmetic sign theorem と解釈しない。

```lean
pascalCenteredXiFixedSecondMomentDefectFunctional_eq_two_mul_horizontalEnergy
pascalCenteredXiFixedSecondMomentDefectFunctional_nonneg
```

XDP-021 の ordered endpoint target が既存 defect と同じであることは Green にしてよいが、approximant から非負性・非正性・vanishingを導いてはならない。

---

## 2. 推奨 implementation file

```text
DkMath/RH/CFBRC/PascalCenteredXiArithmeticDefectRepresentation.lean
```

推奨 imports:

```lean
import DkMath.RH.CFBRC.PascalCenteredXiMellinQuadraticArithmeticLimit
import DkMath.RH.CFBRC.PascalCenteredXiFixedSecondMomentDefectBridge
import Mathlib.Tactic
```

依存 cycle を作らないこと。

必要なら `DkMath/RH.lean` に公開 import を追加する。

---

## 3. Acceptance criteria

### Minimum Green

次が actual theorem として閉じる。

```text
normalized arithmetic approximant
normalized arithmetic endpoint
fixed-ε X→∞ normalized convergence
ε→0+ normalized endpoint → fixed holomorphic second contour functional
```

### Strong Green

Minimum に加えて次が閉じる。

```text
arithmetic defect approximant / endpoint
fixed-ε X→∞ defect convergence
ε→0+ defect endpoint → fixed Xi defect
ordered defect iterated-limit certificate
```

### Ideal Green

Strong に加えて次が閉じる。

```text
finite von Mangoldt defect surface
CF2D radial compatibility surface
scope / limit / sign ledger
public import
```

---

## 4. 禁止事項

新規 source に次を追加しない。

```text
sorry
admit
new axiom
native_decide
Complex.arg
```

また数学的 shortcut として次を仮定・主張しない。

```text
D(ε,X,W) has a fixed sign
D(ε,X,W) → 0
fixed defect ≤ 0
fixed defect = 0
X ↔ ε exchange
joint limit
uniform-in-ε prime convergence
T → ∞
top-horizontal term = 0
RH
```

特に既存

```lean
pascalCenteredXiFixedSecondMomentDefectFunctional_nonneg
```

を使って arithmetic approximant の sign を正当化しないこと。

これは endpoint の既知非負性であって、prime-side independent sign mechanism ではない。

---

## 5. Validation

少なくとも次を実行する。

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiArithmeticDefectRepresentation.lean
lake build DkMath.RH.CFBRC.PascalCenteredXiArithmeticDefectRepresentation
lake build DkMath.RH
./lb DkMath.RH
git diff --check
```

主要 theorem に対して `#print axioms` を監査する。

既存 unrelated warning は result ledger に分離して記録する。

---

## 6. Result document

作成先:

```text
DkMath/RH/CFBRC/docs/wip/RH-CFBRC-prime-side-explicit-formula/
XDP-021-Ordered-arithmetic-fixed-Xi-defect-representation-result.md
```

必須記載:

```text
phase verdict
actual definitions / theorem endpoints
normalization sign audit
ordered-limit shape
finite von Mangoldt surface status
CF2D compatibility status
approximant sign status: OPEN
fixed defect ≤ 0 provider status: OPEN
X ↔ ε exchange status: OPEN
horizontal/T∞ status: OPEN
validation commands and outcomes
axiom audit
```

---

## 7. XDP-021 完了後の frontier

Strong / Ideal Green なら、fixed Xi defect は

```text
Pascal/von Mangoldt finite arithmetic approximants
        ↓ X→∞ at fixed ε
arithmetic defect endpoint
        ↓ ε→0+
fixed Xi second-moment defect
```

という ordered prime-side representationを持つ。

その時点で次の本当の数学的 blocker は representation ではなく **independent sign mechanism** である。

既存 Green:

```text
0 ≤ fixed Xi defect
```

必要な独立側:

```text
fixed Xi defect ≤ 0
```

または同値な arithmetic obstruction / cancellation theorem。

ただし XDP-021 ではこの sign problemへ踏み込まず、prime-side representation が exact に閉じたところで止めること。
