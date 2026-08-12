# XDP-020 — Tau-zero quadratic arithmetic endpoint / epsilon iterated closure 実装指示書

作成日: 2026-08-13

## 0. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-prime-side-explicit-formula-260813-v0
workdir: lean/dk_math
Lean / Mathlib: repository pinned toolchain
```

XDP-019 は `Ideal Green through Gate H` で閉じた。

現在、固定 `ε > 0`、固定 `τ : ℝ`、固定 finite residue window `W` に対して、canonical Mellin second-difference weight

```lean
pascalCenteredXiMellinSecondDifferenceWeight ε τ
```

を用いた finite arithmetic explicit formula と、prime cutoff `X → ∞` の arithmetic approximant convergence が Green である。

また現行定義では `τ = 0` は removable-limit の後付け仮定ではなく、定義そのものが quadratic patch

```text
z² × centeredMellinSpectralWeight (centeredMellinBoxApprox ε) z
```

を返す。

したがって XDP-020 では `τ → 0` の integral limit exchange を行わない。

本 phase の目的は、XDP-019 を exact に `τ := 0` へ specialize し、各 fixed `ε > 0` について先に `X → ∞` を閉じ、その極限値だけを XDP-007 の有限 zero-sum theorem で `ε → 0+` へ送ることである。

目標は順序固定の iterated chain

```text
fixed ε > 0
finite Pascal/von Mangoldt arithmetic approximant
        ↓ X → ∞
quadratic-Mellin finite Xi zero moment
        ↓ ε → 0+
fixed centered Xi second moment
        ↓ existing contour theorem
fixed centered Xi second contour mass
```

である。

この phase では `X` と `ε` の極限交換、joint/product-filter limit、`T → ∞`、horizontal 項消去、defect sign / defect vanishing、critical-line concentration、RH を扱わない。

---

## 1. 既存 Green API

### XDP-019

```lean
pascalCenteredXiMellinSecondDifferenceWeight
pascalCenteredXiMellinSecondDifferenceWeight_differentiable
pascalCenteredXiMellinSecondDifferenceWeight_even
pascalCenteredXiMellinSecondDifferenceZeroMoment
pascalCenteredXiMellinFiniteExplicitFormula
pascalCenteredXiMellinFiniteArithmeticApproximant
tendsto_pascalCenteredXiMellinFiniteArithmeticExplicitFormula
pascalCenteredXiMellinFiniteArithmeticApproximant_eq_vonMangoldt_sum
pascalCenteredXiMellinSecondDifferenceWeight_tau_zero_eq_quadraticWeight
```

### XDP-007

```lean
tendsto_pascalCenteredXiZeroDiskMellinBoxQuadraticMoment_secondMoment
tendsto_pascalCenteredXiMellinBoxQuadraticNormalizedContourTarget
pascalCenteredXiMellinBoxQuadraticLimit_eq_fixedSecondContourTarget
```

特に既存 theorem

```lean
tendsto_pascalCenteredXiZeroDiskMellinBoxQuadraticMoment_secondMoment
```

は finite `Finset` sum に対する pointwise convergence であり、zero disk 上の uniform estimate を要求しない。

### fixed second contour

既存 theorem:

```lean
pascalCenteredXiSecondOuterContourMass_eq_zeroDiskSecondMoment
```

は boundary-safe radius `R` について

```text
pascalCenteredXiSecondOuterContourMass R
  = -(2πi) × pascalCenteredXiZeroDiskSecondMoment R
```

を与える。

`PascalCenteredXiResidueTransportWindow` は `circle_safe` を保持しているため、`W.R` に対してこの theorem を直接利用できる。

---

# Gate A — exact `τ = 0` zero-moment bridge

XDP-019 の named zero-moment observableを、XDP-007 の quadratic-Mellin weighted momentへ exact に接続する。

推奨 theorem:

```lean
theorem pascalCenteredXiMellinSecondDifferenceZeroMoment_tau_zero_eq
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiMellinSecondDifferenceZeroMoment ε 0 W =
      pascalCenteredXiZeroDiskWeightedMoment
        (fun z =>
          z ^ 2 * centeredMellinSpectralWeight
            (centeredMellinBoxApprox ε) z)
        W.R
```

この equality 自体には `0 < ε` は本質的に不要なはずである。現行 `τ = 0` patch を unfold / funext / simp して証明する。

必要なら canonical alias を導入してよい。

```lean
noncomputable def pascalCenteredXiMellinQuadraticZeroMoment
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℂ :=
  pascalCenteredXiMellinSecondDifferenceZeroMoment ε 0 W
```

ただし alias を増やすだけで既存 surface を隠さないこと。

---

# Gate B — fixed-ε exact quadratic finite explicit formula

`pascalCenteredXiMellinFiniteExplicitFormula` を `τ := 0` へ specialize する。

推奨 theorem:

```lean
theorem pascalCenteredXiMellinQuadraticFiniteExplicitFormula
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    -(2 * Real.pi * Complex.I) *
        pascalCenteredXiMellinQuadraticZeroMoment ε W =
      2 * pascalXiOrdinaryZetaRightEdgeIntegral
          (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
          W.rectangle.σ W.rectangle.T +
      2 * pascalXiArchimedeanRightEdgeIntegral
          (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
          W.rectangle.σ W.rectangle.T +
      2 * pascalXiElementaryRightEdgeIntegral
          (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
          W.rectangle.σ W.rectangle.T +
      2 * pascalCenteredXiTopHorizontalContribution
          (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
          W.toContourTransportWindow
```

さらに可能なら weight を pointwise quadratic-Mellin formへ expose した corollary を置く。

```text
weightε(z) = z² Hε(z)
```

ただし right-edge / top integral 内での rewrite は、既存 integrability を壊さない単純な congruence で済む場合だけ行う。不要なら named weight theoremを別に置くだけでよい。

---

# Gate C — fixed-ε quadratic arithmetic approximant

`τ := 0` 専用 alias を作る。

推奨 definition:

```lean
noncomputable def pascalCenteredXiMellinQuadraticArithmeticApproximant
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℂ :=
  pascalCenteredXiMellinFiniteArithmeticApproximant ε 0 W X
```

各 fixed `ε > 0` について XDP-019 の arithmetic Tendsto を specialize する。

推奨 theorem:

```lean
theorem tendsto_pascalCenteredXiMellinQuadraticArithmeticApproximant
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    Tendsto
      (fun X => pascalCenteredXiMellinQuadraticArithmeticApproximant ε W X)
      atTop
      (nhds (-(2 * Real.pi * Complex.I) *
        pascalCenteredXiMellinQuadraticZeroMoment ε W))
```

ここでは `ε` は固定である。

### 禁止

次のような theorem をこの Gate で主張しない。

```text
Tendsto (fun pair : ℕ × ℝ => ...)
```

また `X → ∞` と `ε → 0+` の交換を仮定しない。

---

# Gate D — finite von Mangoldt quadratic surface

XDP-019 の finite von Mangoldt expansion を `τ := 0` へ specialize する。

推奨 theorem:

```lean
theorem pascalCenteredXiMellinQuadraticArithmeticApproximant_eq_vonMangoldt_sum
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinQuadraticArithmeticApproximant ε W X =
      ...
```

右辺は既存 theorem の exact finite sum shape を維持する。

prime kernel 中の weight は可能なら

```text
z² × centeredMellinSpectralWeight (centeredMellinBoxApprox ε) z
```

へ rewrite した corollary を追加してよい。

ただし `centeredMellinSpectralWeight = 1` と置かないこと。

`Complex.cpow` を保持し、`Complex.arg`、偏角、三角関数展開は導入しない。

---

# Gate E — `ε → 0+` zero-side closure

Gate A と XDP-007 の

```lean
tendsto_pascalCenteredXiZeroDiskMellinBoxQuadraticMoment_secondMoment
```

を接続する。

推奨 theorem:

```lean
theorem tendsto_pascalCenteredXiMellinQuadraticZeroMoment_epsilon
    (W : PascalCenteredXiResidueTransportWindow) :
    Tendsto
      (fun ε : ℝ => pascalCenteredXiMellinQuadraticZeroMoment ε W)
      (𝓝[>] 0)
      (nhds (pascalCenteredXiZeroDiskSecondMoment W.R))
```

これは有限 zero-disk sum の theorem であり、right-edge integral や top-horizontal integral の `ε`-domination を新たに証明する必要はない。

この distinction を docstring に明記すること。

---

# Gate F — arithmetic endpoint の `ε → 0+`

inner `X → ∞` の極限値を named endpoint として明示する。

推奨 definition:

```lean
noncomputable def pascalCenteredXiMellinQuadraticArithmeticEndpoint
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℂ :=
  -(2 * Real.pi * Complex.I) *
    pascalCenteredXiMellinQuadraticZeroMoment ε W
```

Gate E から定数倍で

```lean
theorem tendsto_pascalCenteredXiMellinQuadraticArithmeticEndpoint_epsilon
    (W : PascalCenteredXiResidueTransportWindow) :
    Tendsto
      (fun ε : ℝ => pascalCenteredXiMellinQuadraticArithmeticEndpoint ε W)
      (𝓝[>] 0)
      (nhds (-(2 * Real.pi * Complex.I) *
        pascalCenteredXiZeroDiskSecondMoment W.R))
```

を得る。

この theorem が XDP-020 の主要 outer-limit theorem である。

---

# Gate G — fixed second Xi contour endpoint

`W.circle_safe` と既存

```lean
pascalCenteredXiSecondOuterContourMass_eq_zeroDiskSecondMoment
```

を用いて、Gate F の target を fixed second Xi contour mass に同定する。

推奨 theorem:

```lean
theorem tendsto_pascalCenteredXiMellinQuadraticArithmeticEndpoint_secondContour
    (W : PascalCenteredXiResidueTransportWindow) :
    Tendsto
      (fun ε : ℝ => pascalCenteredXiMellinQuadraticArithmeticEndpoint ε W)
      (𝓝[>] 0)
      (nhds (pascalCenteredXiSecondOuterContourMass W.R))
```

証明は Gate F と exact contour theorem の target rewrite に限定する。

新しい contour calculation を行わないこと。

---

# Gate H — ordered iterated-limit certificate

本 phase の最終 surface として、次の二段階を同時に読める named theorem / structure / conjunction を用意する。

概念的には:

```text
for every ε > 0:
  arithmeticApproximant(ε, X) → arithmeticEndpoint(ε) as X → ∞

and:
  arithmeticEndpoint(ε) → fixedSecondContourMass as ε → 0+
```

例えば theorem として:

```lean
theorem pascalCenteredXiMellinQuadraticIteratedLimitCertificate
    (W : PascalCenteredXiResidueTransportWindow) :
    (∀ ε : ℝ, 0 < ε →
      Tendsto
        (fun X => pascalCenteredXiMellinQuadraticArithmeticApproximant ε W X)
        atTop
        (nhds (pascalCenteredXiMellinQuadraticArithmeticEndpoint ε W))) ∧
    Tendsto
      (fun ε : ℝ => pascalCenteredXiMellinQuadraticArithmeticEndpoint ε W)
      (𝓝[>] 0)
      (nhds (pascalCenteredXiSecondOuterContourMass W.R))
```

同等の読みやすい API でもよい。

### 重要

これは

```text
lim ε→0+ (lim X→∞ A(ε,X))
```

の順序を記録する certificate である。

次のいずれも主張していない。

```text
lim X→∞ (lim ε→0+ A(ε,X))
joint limit in (X, ε)
interchange of X and ε limits
uniform convergence in ε
```

この distinction を theorem docstring と result report に必ず記録すること。

---

# Gate I — optional finite-window second-moment exposure

既存 zero-disk / critical-mirror-window bridge が straightforward に使える場合のみ、final target を window centered second momentへ expose する corollary を追加してよい。

既存候補 API:

```lean
pascalCenteredXiZeroDiskSecondMoment_eq_windowCenteredSecondMoment
```

目的は fixed finite window 上で spectral target を見やすくすることだけであり、horizontal energy や defect への変換はこの phase では行わない。

この Gate が typing / import 上の余計な負担になるなら延期してよい。

---

# 実装ファイル

推奨新規 source:

```text
DkMath/RH/CFBRC/PascalCenteredXiMellinQuadraticArithmeticLimit.lean
```

主要 import 候補:

```lean
import DkMath.RH.CFBRC.PascalCenteredXiMellinArithmeticSpecialization
import DkMath.RH.CFBRC.PascalCenteredXiMellinQuadraticRealizationBridge
import Mathlib.Tactic
```

公開 surface として適切なら `DkMath/RH.lean` に import を追加する。

---

# 禁止事項 / phase boundary

XDP-020 では次を行わない。

```text
τ → 0 integral transport
X ↔ ε limit exchange
joint/product-filter limit in (X, ε)
uniform-in-ε prime cutoff convergence
ε → 0 inside each right-edge integral
ε → 0 inside Gamma / elementary correction integral
ε → 0 inside top-horizontal contribution
T → ∞
horizontal contribution = 0
fixed same-zero-set window family for arbitrary T
prime-side sign theorem
defect ≤ 0
defect = 0
critical-line concentration
RiemannHypothesis
```

特に、Gate E/F は **zero-side finite sum endpoint を通るために成立する**のであって、arithmetic integrand 各項へ `ε → 0+` を交換したことを意味しない。

`Complex.arg`、偏角、三角関数展開は不要である。

`sorry`、`admit`、新規 `axiom`、`native_decide` は禁止。

---

# Acceptance

## Minimum Green

次が actual theorem として Green:

```text
Gate A exact τ=0 zero-moment bridge
Gate C fixed-ε X→∞ arithmetic Tendsto
Gate E ε→0+ zero-moment Tendsto
Gate F ε→0+ arithmetic-endpoint Tendsto
```

## Strong Green

Minimum に加えて:

```text
Gate B exact quadratic finite explicit formula
Gate D finite von Mangoldt quadratic surface
Gate G fixed second contour target
```

## Ideal Green

Strong に加えて:

```text
Gate H ordered iterated-limit certificate
Gate I finite-window second-moment exposure if straightforward
public import / docstrings / limit ledger
```

Gate I が既存 API の naming / typing mismatch だけで重くなる場合、Gate H までを `Ideal Green` としてよい。Gate I は本質 gate ではない。

---

# Validation

最低限:

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiMellinQuadraticArithmeticLimit.lean
lake build DkMath.RH.CFBRC.PascalCenteredXiMellinQuadraticArithmeticLimit
lake build DkMath.RH
./lb DkMath.RH
git diff --check
```

主要 theorem に対して `#print axioms` を確認する。

changed source / docs について以下を検索する。

```text
sorry
admit
axiom
native_decide
Complex.arg
```

既存 unrelated warning は result ledger に分離して記録する。

---

# 結果文書

作成:

```text
DkMath/RH/CFBRC/docs/wip/RH-CFBRC-prime-side-explicit-formula/XDP-020-Tau-zero-quadratic-arithmetic-endpoint-and-epsilon-iterated-closure-result.md
```

最低限記録する内容:

1. verdict: Minimum / Strong / Ideal / Partial Green
2. actual theorem / definition 一覧
3. `τ := 0` exact specialization の方法
4. finite von Mangoldt quadratic surface の shape
5. `ε → 0+` zero-side proof が finite sum だけで閉じたこと
6. arithmetic endpoint の outer limit
7. fixed second contour への exact identification
8. ordered iterated-limit certificate の有無
9. `X ↔ ε` exchange を主張していないこと
10. horizontal / `T → ∞` / defect / RH boundary
11. validation command 結果
12. `#print axioms`
13. forbidden declaration search
14. exact blocker が残った場合はその型と不足 API

---

# この phase の意味

XDP-020 が Strong / Ideal Green になれば、fixed finite residue window に対して

```text
Pascal / von Mangoldt finite arithmetic surfaces
        ↓ X → ∞
quadratic Mellin spectral endpoint
        ↓ ε → 0+
actual centered Xi second moment / second contour
```

という **順序固定の算術→二次 spectral observable bridge** が完成する。

これはまだ defect vanishing ではない。

ただし次 phase では、既存 fixed second-moment defect representation

```text
radial second moment - real part of normalized second contour
```

へこの arithmetic second-contour endpoint を接続し、defect の arithmetic representation を作る準備が整う。
