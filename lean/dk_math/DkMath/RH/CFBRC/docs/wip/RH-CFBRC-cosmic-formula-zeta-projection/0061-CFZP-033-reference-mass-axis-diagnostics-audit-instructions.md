# CFZP-0061 / CFZP-033

## reference-mass axis diagnostics and exact sigma-decay normalization — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-029: universal automatic Bad envelope
- CFZP-030: common critical carrier and exact prime-power critical scale
- CFZP-031: universal reference mass `μ(p,j)` and efficiency ledger
- CFZP-032: uniform ready-Good efficiency floor and weighted reference-mass coverage criterion

CFZP-032 correction により、large-cell threshold は内部で閉じた。

```text
k >= 1 -> LargeCellEfficiencyReady
j >= 3 -> 2ε <= phaseMagnitudeLeft
```

したがって fixed-prime irrational rotation の cofinal ready hit は、外部 threshold provider なしで cofinal uniformly-efficient ready hit へ強化できる。

ここから残る本質は

```text
Does the Good set capture enough reference mass μ?
```

である。

本段では weighted coverage provider をまだ作らない。まず reference mass 自体を prime-power logarithmic coordinate

```text
u = j * log p
```

へ完全に展開し、fixed-prime exponent axis と prime axis `j = 1` の decay structure を exact finite theorem として診断する。

重要な既存定義は

```lean
cfzpModePhaseAbscissa W = W.rectangle.σ - 1 / 2
cfzpModeCriticalScale n = exp (-(1 / 2) * log n)
```

である。

したがって reference mass に含まれる二つの exponential factor は prime-power coordinate `u` 上で exact に

```text
exp(-(1/2) * u) * exp(-a * (u - ε))
  = exp(a * ε) * exp(-σ * u)
```

へ再結合する。ここで

```text
a = cfzpModePhaseAbscissa W = σ - 1/2.
```

**CFZP-033 の最重要点は、reference mass の真の exponential decay exponent が `a + 1/2` という未整理な量ではなく、rectangle parameter `σ` そのものであることを Lean theorem として固定することである。**

本段では infinite sum、PNT、Mertens、prime-density theorem、limit exchange を導入しない。

---

## 1. 新規 module

候補:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaReferenceMassAxisDiagnosticsAudit
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaReferenceMassAxisDiagnosticsAudit.lean
```

主 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaUniformReadyGoodEfficiencyFloorAudit
import Mathlib.Tactic
```

---

## 2. Gate A — canonical prime-power logarithmic coordinate

first-class coordinate を導入する。

```lean
noncomputable def cfzp033PrimePowerLogCoordinate (p j : ℕ) : ℝ :=
  (j : ℝ) * Real.log (p : ℝ)
```

既存定義への exact adapters を証明する。

少なくとも:

```text
cfzpPrimePowerPhaseCenter p j = cfzp033PrimePowerLogCoordinate p j

cfzpPrimePowerPhaseMagnitudeLeft ε p j
  = cfzp033PrimePowerLogCoordinate p j - ε

cfzpPrimePowerPhaseMagnitudeRight ε p j
  = cfzp033PrimePowerLogCoordinate p j + ε

cfzpPrimePowerPhaseAngleRight ε W p j
  = W.rectangle.T * (cfzp033PrimePowerLogCoordinate p j + ε)
```

axis diagnostics:

```text
u(p,1) = log p
u(p,j+1) = u(p,j) + log p
```

を exact に閉じる。

必要なら `j > 0` / prime assumption は positivity theorem のみに付け、algebraic identities には不要な仮定を足さない。

---

## 3. Gate B — critical-scale / boundary-decay sigma recombination

`a := cfzpModePhaseAbscissa W`、`σ := W.rectangle.σ` とする。

中心 theorem を first-class にする。

推奨 shape:

```lean
theorem cfzp033CriticalBoundaryExp_recombine_sigma
    (ε u : ℝ) (W : PascalCenteredXiResidueTransportWindow) :
    Real.exp (-(1 / 2 : ℝ) * u) *
        Real.exp (-(cfzpModePhaseAbscissa W) * (u - ε)) =
      Real.exp ((cfzpModePhaseAbscissa W) * ε) *
        Real.exp (-(W.rectangle.σ) * u) := by
  ...
```

proof は `cfzpModePhaseAbscissa` を unfold し、`← Real.exp_add` と ring algebra で閉じる。

この theorem は prime/power に依存しない generic real-coordinate identity とすること。

さらに prime-power specialization を用意してよい。

```text
u = cfzp033PrimePowerLogCoordinate p j
```

を代入した adapter を置く。

ここでは `σ < 1`, `σ ≤ 1`, `σ = ...` のような新規 bounds は導入しない。

---

## 4. Gate C — reduced reference-mass shape

reference mass の exponential factor 以外を一個の finite shape にまとめる。

候補:

```lean
noncomputable def cfzp033ReferenceMassReducedShape
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) : ℝ :=
  cfzp029PhaseDerivativeCoreAbsEnvelope
      (cfzpModePhaseAspectRatio W)
      (W.rectangle.T * (u + ε)) /
    (u - ε) ^ 3
```

safe prime-power 条件の下で exact factorization:

```text
cfzp031PrimePowerReferenceMass ε W p j
  = 2 * log p
      * exp (a * ε)
      * exp (-σ * u(p,j))
      * cfzp033ReferenceMassReducedShape ε W (u(p,j))
```

を証明する。

proof spine:

1. `ReferenceMass = carrier * BadLocalShape`。
2. `carrier = 2 log p * exp(-(1/2)u)`。
3. Bad prefactor ceiling は `exp(-a(u-ε))/(u-ε)^3`。
4. phase-angle right は `T*(u+ε)`。
5. Gate B の exponential recombination。

parentheses / multiplication order は Lean が扱いやすい形へ調整してよいが、最終 theorem から

```text
2 log p
exp(a ε)
exp(-σ u)
ReducedShape(u)
```

の四要素が明瞭に読めること。

---

## 5. Gate D — subcritical polynomial normal form of the reduced shape

CFZP-032 の

```text
q(α) = 1 + 2α - α²
PhaseEnvelope α R
  = q(α) R² + 2(α+1)R + 2
```

を再利用する。

`α := cfzpModePhaseAspectRatio W`、`R := T*(u+ε)` として subcritical hypothesis

```text
Cfzp027SubcriticalPhaseAspect W
```

の下で reduced shape を exact に

```text
[q*T²*(u+ε)² + 2*(α+1)*T*(u+ε) + 2] / (u-ε)³
```

へ正規化する theorem を作る。

新しい envelope を再定義して重複させず、CFZP-032 theorem への adapter とする。

---

## 6. Gate E — large-coordinate two-sided reduced-shape bounds

目的は、prime/exponent axis の違いを carrier 部分だけでなく polynomial remainder も含めて finite comparison 可能にすること。

assumptions の目安:

```text
0 < ε
Cfzp027SubcriticalPhaseAspect W
2 * ε ≤ u
1 ≤ u
```

これらから

```text
u / 2 ≤ u - ε
u + ε ≤ 3 * u / 2
```

または Lean が簡単ならより粗く

```text
u + ε ≤ 2*u
```

を得る。

### Lower bound

subcritical では `q ≥ 1`、`T > 0` なので phase envelope は少なくとも quadratic term を持つ。

狙い:

```text
W.rectangle.T ^ 2 / u
  ≤ cfzp033ReferenceMassReducedShape ε W u
```

これが少し強すぎる場合は固定係数 `1/4`, `1/8` 等を付けてよい。
**重要なのは `c_lower(W) / u` という p,j-independent positive lower shape。**

### Upper bound

`0 < α < 1` から例えば `q ≤ 2` を証明し、linear terms を quadratic scale へ吸収する。

狙いの粗い bound:

```text
cfzp033ReferenceMassReducedShape ε W u
  ≤ 64 * (W.rectangle.T + 1)^2 / u
```

定数 64 は sharp でなくてよい。Lean proof を単純化するなら 128, 256 へ弱めてもよい。

completion condition:

```text
c₁(W) / u <= ReducedShape(u) <= c₂(W) / u
```

という finite two-sided comparison が explicit positive constants で閉じること。

`T`, `α`, `ε` に依存する定数でもよいが、**p と j に依存しない**こと。

---

## 7. Gate F — prime-axis `j = 1` diagnostic

定義候補:

```lean
noncomputable def cfzp033PrimeAxisReferenceMass
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p : ℕ) : ℝ :=
  cfzp031PrimePowerReferenceMass ε W p 1
```

Gate C から exact:

```text
PrimeAxisMass(p)
  = 2*log p * exp(aε) * exp(-σ log p)
      * ReducedShape(log p)
```

Gate E の large-coordinate hypotheses

```text
2ε ≤ log p
1 ≤ log p
```

の下では `log p` が numerator `2 log p` と reduced-shape `~1/log p` で cancel するため、

```text
C₁(W,ε) * exp(-σ log p)
  ≤ PrimeAxisMass(p)
  ≤ C₂(W,ε) * exp(-σ log p)
```

という **finite two-sided comparison** を証明する。

例えば lower constant は

```text
2 * T^2 * exp(aε)
```

相当、upper は

```text
128 * (T+1)^2 * exp(aε)
```

相当でよい。Gate E の実際の定数に合わせること。

ここで `exp(-σ log p) = p^{-σ}` という `rpow` 表記へ無理に変換しなくてよい。Lean の既存 exponential/log form を正本とする。

**prime-axis mass の infinite sum の収束・発散は本段では絶対に主張しない。**

---

## 8. Gate G — fixed-prime exponent-axis diagnostic

fixed prime `p`、positive exponent `j` について

```text
u = j * log p
```

なので Gate C + Gate E から

```text
ReferenceMass(p,j)
  ≍ [2/j] * exp(aε) * exp(-σ * j * log p)
```

という finite comparison が得られる。

Lean theorem は asymptotic notation `≍` を使わず、上下界で書く。

目標 shape:

```text
C₁(W,ε) / j * exp(-σ * j * log p)
  ≤ cfzp031PrimePowerReferenceMass ε W p j

cfzp031PrimePowerReferenceMass ε W p j
  ≤ C₂(W,ε) / j * exp(-σ * j * log p)
```

under:

```text
Nat.Prime p
0 < j
2ε ≤ j*log p
1 ≤ j*log p
subcritical W
```

理由は

```text
2*log p / (j*log p) = 2/j
```

である。

division cancellation には `Real.log p > 0` を prime assumption から使う。

可能なら axis-step exponential factorも記録する。

```lean
noncomputable def cfzp033FixedPrimeSigmaStep
    (W : PascalCenteredXiResidueTransportWindow) (p : ℕ) : ℝ :=
  Real.exp (-(W.rectangle.σ) * Real.log (p : ℝ))
```

そして prime `p` に対し `0 < step` は必ず証明する。
もし既存 window hypotheses から `0 < W.rectangle.σ` が clean に導けるなら `step < 1` も証明してよい。
ただし source にない `σ > 0` / `σ < 1` を推測で追加してはいけない。

---

## 9. Gate H — exact finite axis comparison summary

033 の数学診断を theorem/API と roadmap の双方で明示する。

### fixed-prime exponent axis

```text
u_j = j log p
exponential factor = exp(-σ j log p)
reduced shape ~ 1/(j log p)
carrier has log p
therefore finite mass comparison contains 1/j
```

### prime axis `j=1`

```text
u_p = log p
exponential factor = exp(-σ log p)
reduced shape ~ 1/log p
carrier has log p
therefore log p cancels in finite comparison
```

この差は次段の axis selection に使う。

033 自身では

- fixed-prime total mass is finite
- prime-axis total mass diverges
- prime axis dominates
- Good phase hits capture a positive fraction

のいずれも主張しない。

---

## 10. Optional finite tail/block diagnostics

実装が短く済む場合のみ、無限和を導入せず finite `Finset.range` で diagnostic sum を置いてよい。

例:

```text
FixedPrimeExponentMassBlock p J K
  = Σ j in Icc J K, μ(p,j)

PrimeAxisMassBlock P Q
  = Σ p in prime support between P and Q, μ(p,1)
```

ただし prime support の新しい重い API は作らない。
既存 support が clean に流用できないなら、この Gate は飛ばす。

本段の first priority は one-pair exact factorization と two-sided axis bounds である。

---

## 11. Firewall / Gap

少なくとも次を OPEN に保つ。

```text
noIndependentWeightedGoodReferenceMassCoverageProvider
noPrimeAxisWeightedMassAccumulationProvider
noPrimeAxisGoodPhaseCoverageProvider
noAutomaticSubcriticalWindowProvider
noIndependentPrimePhaseRotationIrrationalityProvider
```

また以下を導入しない。

- `σ < 1` / `σ ≤ 1` の未確認仮定を theorem のように扱うこと
- prime reciprocal divergence への接続
- PNT / Mertens / Chebyshev / zero-density theorem の新規導入
- infinite prime-power sums
- summability / nonsummability conclusion
- limit exchange / dominated convergence
- positive natural density -> weighted mass share shortcut
- CFZP-018 unconditional provider
- global RH conclusion

もし既存 rectangle/window source に `σ` の upper bound が実際に存在することを発見した場合は、**まず source theorem を明示引用できる exact adapter を作るだけ**に留め、mass accumulation theorem へは本段で進まない。

---

## 12. Roadmap に記録する数学的意味

CFZP-033 の核心診断:

```text
critical scale contributes        exp(-(1/2)u)
boundary profile contributes      exp(-(σ-1/2)(u-ε))
------------------------------------------------------
combined reference-mass decay     exp((σ-1/2)ε) * exp(-σu)
```

したがって reference mass の exponential exponent は exactly rectangle `σ`。

さらに reduced shape が finite large-coordinate region で `1/u` に挟まれるなら、

```text
fixed p, varying j:
  μ(p,j) = exponential-in-j factor × 1/j up to explicit constants

j = 1, varying p:
  μ(p,1) = exp(-σ log p) up to explicit constants
```

となる。

これにより CFZP-034 で初めて、どの axis が weighted Good coverage を供給し得るかを、必要なら既知数論 theorem と照合して選択できる。

---

## 13. Completion gate

Green 条件:

```text
prime-power logarithmic coordinate adapters: CLOSED
critical-scale/boundary exponential recombination to σ: CLOSED
exact reference-mass sigma-decay factorization: CLOSED
subcritical reduced-shape polynomial normal form: CLOSED
large-coordinate reduced-shape lower bound c1/u: CLOSED
large-coordinate reduced-shape upper bound c2/u: CLOSED
prime-axis finite two-sided mass comparison: CLOSED
fixed-prime exponent-axis finite two-sided mass comparison: CLOSED
axis diagnostic recorded without infinite-sum claims: CLOSED
weighted Good reference-mass coverage provider: OPEN / GAP
```

公開 import:

```text
DkMath/RH.lean
```

roadmap:

```text
0000-CFZP-roadmap.md
```

も更新すること。

証明定数は sharp でなくてよい。最優先は、`p,j` に依存しない positive finite constants で `ReducedShape ~ 1/u` を上下から挟み、prime axis と exponent axis の構造差を Lean theorem として明確化することである。
