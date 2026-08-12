# XDP-019 — Fixed Mellin second-difference arithmetic specialization 実装指示書

作成日: 2026-08-13

## 0. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-prime-side-explicit-formula-260813-v0
workdir: lean/dk_math
Lean / Mathlib: repository pinned toolchain
```

XDP-018 は `Ideal Green through Gate I` で閉じた。

現在の generic arithmetic endpoint は次である。

```lean
pascalCenteredXiFiniteExplicitFormula_eq_zeta_archimedean_elementary_top
pascalCenteredXiFiniteArithmeticApproximant
tendsto_pascalCenteredXiFiniteArithmeticExplicitFormula
pascalCenteredXiFiniteArithmeticApproximant_eq_vonMangoldt_sum
```

すなわち、`Differentiable ℂ h` と `PascalCenteredEvenWeight h` を満たす generic centered weight `h` に対し、固定 finite residue window `W` 上で

```text
finite Xi weighted zero moment
← X → ∞
finite Pascal/von Mangoldt arithmetic approximant
```

が Green である。

XDP-019 の目的は、この generic theorem に canonical Mellin second-difference weight

```lean
centeredMellinSecondDifferenceWeight
  (centeredMellinBoxApprox ε) τ
```

を **固定 `ε > 0`、固定 `τ : ℝ`、固定 finite residue window `W`** の範囲で実代入し、Mellin spectral observable と finite Pascal/von Mangoldt kernel surface を同じ theorem chain に接続することである。

本 phase では次の極限を導入しない。

```text
τ → 0
ε → 0+
T → ∞
```

また horizontal term の消去、defect sign / defect vanishing、critical-line concentration、RH は扱わない。

---

# 重要な現行定義の確認

現行 `centeredMellinSecondDifferenceWeight` は `τ = 0` をゼロ関数へ totalize していない。

```lean
noncomputable def centeredMellinSecondDifferenceWeight
    (h : ℝ → ℂ) (τ : ℝ) (z : ℂ) : ℂ :=
  if τ = 0 then
    z ^ 2 * centeredMellinSpectralWeight h z
  else
    ...
```

従って `τ = 0` branch は canonical quadratic patch であり、

```text
z² × centered Mellin spectral weight
```

である。

XDP-019 ではこの patched branch を尊重すること。

### 禁止

```text
τ = 0 なら weight = 0
τ = 0 なら weight = z²
```

のどちらも誤りである。

正しくは fixed `ε` について

```text
weight(ε, 0, z)
= z² × Hε(z)
```

である。`Hε(z) → 1` は `ε → 0+` を扱う後続 phase の仕事である。

---

# Gate 0 — Pinned Mellin API audit

実装前に exact theorem signature を repository pinned source / `#check` で確認すること。

最低限確認する API:

```lean
centeredMellinBoxApprox
centeredMellinBoxApprox_endpoints_ordered
centeredMellinBoxApprox_support_subset
centeredMellinBoxApprox_continuousOn
centeredMellinSpectralWeight_centeredMellinBoxApprox_eq_logAverage

differentiable_centeredMellinSecondDifferenceWeight
centeredMellinSecondDifferenceWeight_eq_kernel_mul
centeredMellinSecondDifferenceWeight
centeredMellinSpectralWeight

centeredMellinSecondDifferenceWeight_centeredMellinBoxApprox_even
centeredMellinSpectralWeight_centeredMellinBoxApprox_even
```

compact-positive-support contract は box について既に次から直接供給できる。

```text
Real.exp_pos (-ε)
centeredMellinBoxApprox_endpoints_ordered hε
centeredMellinBoxApprox_support_subset hε
centeredMellinBoxApprox_continuousOn hε
```

一般 Mellin holomorphic theoremを再証明しないこと。

---

# Gate A — Canonical specialized weight と admissibility

新 module を推奨する。

```text
DkMath/RH/CFBRC/PascalCenteredXiMellinArithmeticSpecialization.lean
```

必要なら canonical alias を置いてよい。

```lean
noncomputable def pascalCenteredXiMellinSecondDifferenceWeight
    (ε τ : ℝ) : ℂ → ℂ :=
  centeredMellinSecondDifferenceWeight
    (centeredMellinBoxApprox ε) τ
```

ただし alias を追加する場合も underlying expression との simp / unfolding surface を明確に保つこと。

`hε : 0 < ε` から次を actual theorem にする。

```lean
Differentiable ℂ
  (centeredMellinSecondDifferenceWeight
    (centeredMellinBoxApprox ε) τ)
```

証明は既存

```lean
differentiable_centeredMellinSecondDifferenceWeight
```

へ box の positive compact-support data を供給する。

同時に既存 theorem

```lean
centeredMellinSecondDifferenceWeight_centeredMellinBoxApprox_even
```

を canonical admissibility surface として再利用する。

推奨 named theorem 例:

```lean
pascalCenteredXiMellinSecondDifferenceWeight_differentiable
pascalCenteredXiMellinSecondDifferenceWeight_even
```

Acceptance:

```text
Gate A Green:
固定 ε > 0, τ の Mellin second-difference weight が
XDP-018 generic theorem の differentiable / even hypotheses を
新しい provider assumption なしで満たす。
```

---

# Gate B — Named specialized zero-side observable

fixed `(ε, τ, W)` の zero-side endpoint を named API にする。

概念形:

```lean
pascalCenteredXiZeroDiskWeightedMoment
  (centeredMellinSecondDifferenceWeight
    (centeredMellinBoxApprox ε) τ)
  W.R
```

必要なら次のような alias を置いてよい。

```lean
noncomputable def pascalCenteredXiMellinSecondDifferenceZeroMoment
    (ε τ : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℂ :=
  pascalCenteredXiZeroDiskWeightedMoment
    (centeredMellinSecondDifferenceWeight
      (centeredMellinBoxApprox ε) τ)
    W.R
```

重要なのは名前よりも、後続 theorem の statement で generic `h` が消え、Mellin weight が actual に固定されていることである。

この Gate では zero moment を `z²` moment に置換してはならない。

---

# Gate C — Exact fixed Mellin four-term spectral identity

XDP-018 の

```lean
pascalCenteredXiFiniteExplicitFormula_eq_zeta_archimedean_elementary_top
```

へ Gate A の differentiability / evenness を渡し、fixed Mellin second-difference weight版を actual theorem にする。

概念形:

```text
-2πi × M_W(ε,τ)
=
2 I_zeta(ε,τ,W)
+ 2 I_arch(ε,τ,W)
+ 2 I_elem(ε,τ,W)
+ 2 I_top(ε,τ,W)
```

すべての correction / top term でも **同じ specialized weight** を使うこと。

Gamma / elementary / horizontal を generic weightのまま残した mixed theorem にしないこと。

---

# Gate D — Specialized arithmetic approximant

XDP-018 generic approximant

```lean
pascalCenteredXiFiniteArithmeticApproximant
```

へ canonical Mellin weight を代入した named surface を作る。

推奨形:

```lean
noncomputable def pascalCenteredXiMellinFiniteArithmeticApproximant
    (ε τ : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℂ :=
  pascalCenteredXiFiniteArithmeticApproximant
    (centeredMellinSecondDifferenceWeight
      (centeredMellinBoxApprox ε) τ)
    W X
```

alias を作らない場合でも principal theorem statement には specialization を明示する。

---

# Gate E — Fixed Mellin arithmetic Tendsto

XDP-018 principal convergence theoremをそのまま specializeする。

principal target:

```lean
Tendsto
  (fun X =>
    pascalCenteredXiFiniteArithmeticApproximant
      (centeredMellinSecondDifferenceWeight
        (centeredMellinBoxApprox ε) τ)
      W X)
  atTop
  (nhds
    (-(2 * Real.pi * Complex.I) *
      pascalCenteredXiZeroDiskWeightedMoment
        (centeredMellinSecondDifferenceWeight
          (centeredMellinBoxApprox ε) τ)
        W.R))
```

hypothesis は原則

```lean
hε : 0 < ε
```

だけでよい。`τ ≠ 0` を principal Tendsto に要求しないこと。現行 weight は `τ = 0` も canonical patch により entire / even である。

Acceptance:

```text
Gate E Green:
任意 fixed ε > 0, τ, finite W に対し、
Mellin-specialized Pascal/von Mangoldt approximant が
同じ Mellin weight の finite Xi zero moment endpointへ X → ∞ で収束する。
```

---

# Gate F — Specialized finite von Mangoldt surface

XDP-018 の

```lean
pascalCenteredXiFiniteArithmeticApproximant_eq_vonMangoldt_sum
```

を specializeし、有限 `X` の arithmetic surface を公開する。

概念形:

```text
A_X(ε,τ,W)
=
2 Σ_{n≤X} Λ(n)
  ∫_{-T}^{T}
    H_{ε,τ}(z_t)
    n^{-s_t} i dt
+ 2 I_arch(ε,τ,W)
+ 2 I_elem(ε,τ,W)
+ 2 I_top(ε,τ,W)
```

ここで

```text
s_t = σ + i t
z_t = s_t - 1/2
H_{ε,τ}(z)
= centeredMellinSecondDifferenceWeight
    (centeredMellinBoxApprox ε) τ z
```

である。

`Complex.cpow` はそのまま保持する。`Complex.arg`、偏角、三角関数展開を導入しない。

---

# Gate G — Nonzero τ exponential-kernel exposure

`hτ : τ ≠ 0` のときだけ、既存

```lean
centeredMellinSecondDifferenceWeight_eq_kernel_mul hτ
```

を使い、prime kernel weight を

```text
[(exp(τ z) - 2 + exp(-τ z)) / τ²]
× centeredMellinSpectralWeight (centeredMellinBoxApprox ε) z
```

として exact に露出してよい。

推奨 theorem は少なくとも pointwise specializationを持つ。

概念形:

```lean
centeredMellinSecondDifferenceWeight
    (centeredMellinBoxApprox ε) τ z
=
  ((Complex.exp ((τ : ℂ) * z) - 2 +
      Complex.exp (-(τ : ℂ) * z)) /
    (τ : ℂ) ^ 2) *
  centeredMellinSpectralWeight
    (centeredMellinBoxApprox ε) z
```

可能ならこの rewrite を Gate F の finite von Mangoldt integral surfaceにも反映した theorem を追加する。

ただし `hτ : τ ≠ 0` を使う theorem と、Gate E の all-τ principal theorem を混同しないこと。

### 禁止

`τ = 0` に division formula を適用しない。

---

# Gate H — Patched τ = 0 quadratic-Mellin surface

現行 definition の重要な boundary を named theorem として固定する。

fixed `ε > 0` で

```text
H_{ε,0}(z)
= z² × centeredMellinSpectralWeight
    (centeredMellinBoxApprox ε) z
```

を actual theorem / simp-friendly surface にする。

これにより XDP-019 終了時点で次の二つが明確に分かれる。

```text
τ ≠ 0:
exponential symmetric second-difference kernel × Hε(z)

τ = 0:
z² × Hε(z)
```

ここでも `Hε(z) = 1` とはしない。

---

# Gate I — Limit ledger / next-phase boundary

XDP-019 では次の既存 Mellin limit theorem を **監査・記録するだけ** とし、arithmetic formula の limit exchangeには使わない。

```lean
tendsto_centeredMellinSecondDifferenceWeight_zero
centeredMellinSpectralWeight_centeredMellinBoxApprox_eq_logAverage
tendsto_centeredMellinSpectralWeight_centeredMellinBoxApprox_one
tendsto_centeredMellinBoxApprox_quadraticWeight
```

これらは次 phase のための入力である。

特に次を XDP-019 で証明したことにしてはならない。

```text
lim_{τ→0} A_X(ε,τ,W) の integral / correction term 交換
lim_{ε→0+} arithmetic approximant = quadratic arithmetic formula
lim_{ε→0+} top-horizontal term の交換
Mellin limit と X→∞ の交換
```

XDP-019 は **fixed parameter specialization** で閉じる。

---

# 推奨 principal theorem set

命名は repository style に合わせて調整してよいが、概念的には次を揃える。

```lean
pascalCenteredXiMellinSecondDifferenceWeight_differentiable
pascalCenteredXiMellinSecondDifferenceWeight_even

pascalCenteredXiMellinFiniteExplicitFormula
pascalCenteredXiMellinFiniteArithmeticApproximant
tendsto_pascalCenteredXiMellinFiniteArithmeticExplicitFormula
pascalCenteredXiMellinFiniteArithmeticApproximant_eq_vonMangoldt_sum

pascalCenteredXiMellinSecondDifferenceWeight_eq_kernel_mul
pascalCenteredXiMellinSecondDifferenceWeight_zero
```

最後の `..._zero` は **zero function theorem という意味ではない**。`τ = 0` の patched quadratic-Mellin identity を表す命名である。誤解を避けるなら `..._tau_zero_eq_quadraticWeight` 等を推奨する。

---

# No-circularity / scope audit

新規 theorem の仮定・結論に次を入れない。

```text
RiemannHypothesis
PascalCenteredXiFixedDefectVanishesOnSafeRadii
defect = 0
defect ≤ 0
critical-line concentration
Weil / Li positivity
horizontal contribution = 0
T → ∞
```

また、Mellin weight specializationは zero setの情報を仮定してはならない。

`W` が持つ既存 finite same-zero-set / safety contract以上の zero-location assumptionを追加しないこと。

---

# 実装 discipline

- 新しい contour / residue theoremを追加しない。
- XDP-017 の majorant / dominated convergenceを再証明しない。
- XDP-018 の Gamma / elementary integrabilityを再証明しない。
- generic theoremを specializeできる箇所では必ず再利用する。
- `τ = 0` と `τ ≠ 0` branchを数学的に区別する。
- `Complex.arg`、偏角、三角関数を使わない。
- `sorry`、`admit`、新規 `axiom`、`native_decide` を使わない。
- theorem / definition に docstring を付ける。
- public surfaceが必要なら `DkMath/RH.lean` に import を追加する。

---

# Validation

最低限次を実行する。

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiMellinArithmeticSpecialization.lean
lake build DkMath.RH.CFBRC.PascalCenteredXiMellinArithmeticSpecialization
lake build DkMath.RH
./lb DkMath.RH
git diff --check
```

主要 theorem について `#print axioms` を確認する。

新規 source に対して禁止宣言検索も行う。

```text
sorry
admit
axiom
native_decide
```

既存 unrelated warning は別 ledger として記録する。

---

# Result report

次を作成する。

```text
XDP-019-Fixed-Mellin-second-difference-arithmetic-specialization-result.md
```

最低限記録する内容:

```text
phase classification
actual theorem names
box support / differentiability / evenness bridge
fixed Mellin spectral identity
fixed Mellin arithmetic Tendsto
finite von Mangoldt expansion
τ ≠ 0 exponential-kernel surface
τ = 0 patched quadratic-Mellin surface
build / axiom / shortcut audit
next exact blocker
```

---

# Acceptance levels

## Minimum Green

次が actual theorem になる。

```text
fixed ε > 0, fixed τ, fixed finite W
→ Mellin weight is differentiable and even
→ generic XDP-018 arithmetic Tendsto specializes successfully
```

## Strong Green

Minimum Green に加えて、

```text
finite von Mangoldt kernel expansion
τ ≠ 0 exponential second-difference kernel exposure
τ = 0 patched quadratic-Mellin identity
```

まで閉じる。

## Ideal Green

Strong Green に加えて、specialized four-term spectral identityと correction/top termsを含む named Mellin API が一貫して揃い、後続 phase が generic `h` を再展開せずに `(ε,τ)` parameter familyとして直接扱える状態にする。

---

# XDP-019 後の frontier

XDP-019 が Strong / Ideal Green なら、次は parameter limit phase へ進める。

自然な順序は

```text
fixed finite W
→ τ → 0
→ quadratic-Mellin weight z² Hε(z)
→ ε → 0+
→ finite zero set上で z² を回収
```

である。

ただし prime arithmetic terms、Gamma / elementary corrections、top-horizontal termの各 parameter limitを同時に自動交換してよいとは限らない。

次 phase では、zero-side finite sumの limitと arithmetic-side finite-height integralsの limitを別 ledgerとして監査し、必要な uniform / dominated boundsが揃ったものだけを Green にすること。