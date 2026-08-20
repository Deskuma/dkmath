# CFZP-0085 / CFZP-055

## radial escape → exact prime-threshold crossing → finite-window criticality — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-051: standard PNT ratio provider → relative discrepancy decay
- CFZP-052: finite discrepancy analytic readiness auto
- CFZP-053: finite smooth-Abel readiness auto + one-cell eighth descent
- CFZP-054: explicit smooth margin `→ +∞` + unit descent + radial deficit `→ -∞` + cofinal natural-cutoff escape

CFZP-054 は **Green-A**。

---

## 0. 今回の狙い

CFZP-054 は、明示的な

```text
hPNT   : Cfzp051PrimeCountingPNTRatioAtTop
hstrip : Cfzp039PrimeAxisInteriorStrip W
hsub   : Cfzp027SubcriticalPhaseAspect W
```

の下で、任意の正の `epsilon < log 2` に対し、natural carrier cutoff 上で radial deficit を任意の実数 target 以下へ落とせるところまで閉じた。

特に `eta := 0` とすれば、任意の cutoff 下限 `N` より先に

```text
pascalCenteredXiPrimeSideFiniteRadialContactDeficit epsilon W X <= 0
```

を満たす natural cutoff `X` が存在する。

CFZP-018 には既に

```text
radial deficit <= 0
  <-> exact normalized prime-threshold crossing
```

がある。

したがって CFZP-055 では、CFZP-054 の radial escape を **approximate reach に弱める前に**、まず一段強い CFZP-017 exact crossing へ戻す。

主鎖は

```text
CFZP-054 radial deficit atBot / cofinal eta=0
  ↓
fixed-epsilon exact threshold crossing cofinally often
  ↓
Cfzp017CofinalPrimeThresholdCrossingAt epsilon W
  ↓
for all sufficiently small positive epsilon
  ↓
Cfzp017DoublyCofinalPrimeThresholdCrossing W
  ↓
existing CFZP-017 / CFZP-016 closure
  ↓
fixed defect = 0
  ↓
finite-window zeros lie on Re rho = 1/2
```

同時に、既存の 017 → 018 weakening を使い

```text
Cfzp018DoublyCofinalPrimeThresholdApproximateReach W
```

も閉じる。

**本 checkpoint では PNT 自体、window provider、global RH は証明しない。**

---

## 1. New module

推奨 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaRadialEscapePrimeThresholdCrossingClosureAudit
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaRadialEscapePrimeThresholdCrossingClosureAudit.lean
```

imports:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaExplicitSmoothMarginEscapeRadialAtBotAudit
import Mathlib.Tactic
```

`DkMath/RH.lean` に public import を追加する。

---

## 2. Existing API — exact current signatures を必ず再利用

### CFZP-054

```text
cfzp054_pntRatio_cofinal_naturalCutoff_radialDeficit_le
cfzp054_exists_phase_pntRatio_cofinal_naturalCutoff_radialDeficit_le
cfzp054_pntRatio_leftRadialDeficit_tendsto_atBot
cfzp054CarrierCellNaturalLeft_tendsto_atTop
```

### CFZP-018

```text
cfzp018PrimeThresholdCrossing_iff_radialContactDeficit_nonpos
cfzp018CofinalPrimeThresholdApproximateReachAt_iff_csf
cfzp018CofinalPrimeThresholdApproximateReachAt_iff_endpoint_nonpos
cfzp018CofinalPrimeThresholdApproximateReachAt_of_cfzp017
cfzp018DoublyCofinalPrimeThresholdApproximateReach_of_cfzp017
cfzp018FixedDefect_nonpos_of_doublyCofinalPrimeThresholdApproximateReach
cfzp018FixedDefect_eq_zero_of_doublyCofinalPrimeThresholdApproximateReach
cfzp018FiniteWindowZeros_critical_of_doublyCofinalPrimeThresholdApproximateReach
```

### CFZP-017

```text
Cfzp017CofinalPrimeThresholdCrossingAt
Cfzp017DoublyCofinalPrimeThresholdCrossing
cfzp017CofinalPrimeThresholdCrossingAt_iff_cfzp016
cfzp017DoublyCofinalPrimeThresholdCrossing_iff_cfzp016
cfzp017FiniteWindowZeros_critical_of_doublyCofinalPrimeThresholdCrossing
```

### CFZP-016 / CS22

```text
PascalCenteredXiPrimeSideCofinalRadialContactZeroAt
pascalCenteredXiPrimeSideCofinalRadialContactZeroAt_iff_endpoint_nonpos
cfzp016FixedDefect_eq_zero_of_doublyCofinalRadialDomination
```

Use repository declarations directly. Do not restate old definitions unless a tiny adapter makes the proof materially shorter.

---

## 3. Gate A — fixed-epsilon cofinal exact crossing in `∀ N, ∃ X` form

まず CFZP-054 を target `eta = 0` に specialize する。

Recommended theorem:

```lean
theorem cfzp055_pntRatio_cofinal_exactPrimeThresholdCrossing
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon2 : epsilon < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop) :
    ∀ N : ℕ, ∃ X : ℕ, N ≤ X ∧
      cfzp017NormalizedPrimeThreshold epsilon W ≤
        pascalCenteredXiMellinQuadraticNormalizedPrimeContribution epsilon W X := by
  ...
```

### Required route

1. use the positive-phase wrapper from CFZP-054 with `eta := 0`;
2. obtain `c`, `n`, positive transform, `N <= NaturalLeft n`, and radial deficit `<= 0`;
3. let

```text
X := cfzp040CarrierCellNaturalLeft W c n
```

4. convert radial deficit `<= 0` by

```text
cfzp018PrimeThresholdCrossing_iff_radialContactDeficit_nonpos hepsilon W X
```

No approximate slack is needed.

This theorem is stronger than the fixed-epsilon CFZP-018 target.

---

## 4. Gate B — package Gate A as `Cfzp017CofinalPrimeThresholdCrossingAt`

The existing definition is

```lean
Cfzp017CofinalPrimeThresholdCrossingAt epsilon W :=
  ∃ᶠ X : ℕ in Filter.atTop,
    cfzp017NormalizedPrimeThreshold epsilon W <=
      pascalCenteredXiMellinQuadraticNormalizedPrimeContribution epsilon W X
```

Required Green theorem:

```lean
theorem cfzp055_pntRatio_cfzp017CofinalPrimeThresholdCrossingAt
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon2 : epsilon < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop) :
    Cfzp017CofinalPrimeThresholdCrossingAt epsilon W := by
  ...
```

For `ℕ` with `atTop`, Gate A gives exactly the cofinal witness property needed for `Frequently`.

If the exact `Frequently` constructor API is awkward, introduce a tiny local lemma of the standard shape

```text
(∀ N, ∃ X, N <= X ∧ P X) -> ∃ᶠ X in atTop, P X
```

for `Nat`; keep it generic/local and finite-order only.

Do **not** replace exact crossing by approximate reach here.

---

## 5. Gate C — fixed-epsilon CFZP-018 approximate reach as a corollary

Now weaken exact crossing through the existing theorem:

```lean
theorem cfzp055_pntRatio_cfzp018ApproximateReachAt
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon2 : epsilon < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop) :
    Cfzp018CofinalPrimeThresholdApproximateReachAt epsilon W := by
  exact cfzp018CofinalPrimeThresholdApproximateReachAt_of_cfzp017
    hepsilon W
    (cfzp055_pntRatio_cfzp017CofinalPrimeThresholdCrossingAt
      hepsilon hepsilon2 W hstrip hsub hPNT)
```

Equivalent proof via CS22 cofinal radial contact is acceptable, but the public theorem should make clear that approximate reach is now a corollary of **exact** crossing.

---

## 6. Gate D — fixed-epsilon endpoint sign

Expose the arithmetic endpoint consequence at once:

```lean
theorem cfzp055_pntRatio_endpointArithmeticDefect_nonpos
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon2 : epsilon < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop) :
    pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint epsilon W <= 0 := by
  exact (cfzp018CofinalPrimeThresholdApproximateReachAt_iff_endpoint_nonpos
    hepsilon W).mp
    (cfzp055_pntRatio_cfzp018ApproximateReachAt
      hepsilon hepsilon2 W hstrip hsub hPNT)
```

This is useful for debugging the outer epsilon closure.

No limit exchange is being introduced: the endpoint equivalence already exists.

---

## 7. Gate E — sufficiently small positive epsilon package

We need the fixed-epsilon theorem for every sufficiently small point of `𝓝[>] 0`.

Prove/reuse:

```text
∀ᶠ epsilon : ℝ in 𝓝[>] 0, 0 < epsilon
```

from

```text
self_mem_nhdsWithin
```

and

```text
∀ᶠ epsilon : ℝ in 𝓝[>] 0, epsilon < Real.log 2
```

from

```text
Real.log_pos (show (1 : ℝ) < 2 by norm_num)
Iio_mem_nhds
```

transported from `𝓝 0` to `𝓝[>] 0` by filter monotonicity.

Recommended helper:

```lean
theorem cfzp055_eventually_positive_lt_log_two :
    ∀ᶠ epsilon : ℝ in 𝓝[>] 0,
      0 < epsilon ∧ epsilon < Real.log 2 := by
  ...
```

This theorem is pure topology/order. Do not introduce a new epsilon provider predicate.

---

## 8. Gate F — doubly cofinal exact CFZP-017 crossing

This is the main structural closure theorem.

```lean
theorem cfzp055_pntRatio_cfzp017DoublyCofinalPrimeThresholdCrossing
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop) :
    Cfzp017DoublyCofinalPrimeThresholdCrossing W := by
  ...
```

### Required construction

Build first an `Eventually` statement:

```text
∀ᶠ epsilon in 𝓝[>] 0,
  0 < epsilon ∧ Cfzp017CofinalPrimeThresholdCrossingAt epsilon W
```

using Gate E and Gate B.

Then use `.frequently`, exactly in the style already used in CFZP-016.

No new analytic limit is allowed here.

---

## 9. Gate G — doubly cofinal CFZP-018 approximate reach

Now reuse the existing hierarchy theorem:

```lean
theorem cfzp055_pntRatio_cfzp018DoublyCofinalPrimeThresholdApproximateReach
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop) :
    Cfzp018DoublyCofinalPrimeThresholdApproximateReach W := by
  exact cfzp018DoublyCofinalPrimeThresholdApproximateReach_of_cfzp017
    W
    (cfzp055_pntRatio_cfzp017DoublyCofinalPrimeThresholdCrossing
      W hstrip hsub hPNT)
```

This formally retires the CFZP-018 adapter frontier **conditionally on the three explicit providers**.

Do not claim an unconditional independent 018 provider.

---

## 10. Gate H — fixed second-moment defect sign and vanishing

Expose both routes if convenient.

### Through CFZP-018

```lean
theorem cfzp055_pntRatio_fixedDefect_nonpos
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop) :
    pascalCenteredXiFixedSecondMomentDefectFunctional W.R <= 0 := by
  exact cfzp018FixedDefect_nonpos_of_doublyCofinalPrimeThresholdApproximateReach
    W
    (cfzp055_pntRatio_cfzp018DoublyCofinalPrimeThresholdApproximateReach
      W hstrip hsub hPNT)
```

Then safe-radius nonnegativity gives equality:

```lean
theorem cfzp055_pntRatio_fixedDefect_eq_zero
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop) :
    pascalCenteredXiFixedSecondMomentDefectFunctional W.R = 0 := by
  exact cfzp018FixedDefect_eq_zero_of_doublyCofinalPrimeThresholdApproximateReach
    W
    (cfzp055_pntRatio_cfzp018DoublyCofinalPrimeThresholdApproximateReach
      W hstrip hsub hPNT)
```

### Optional exact-crossing route

It is also good to show the same equality via

```text
cfzp017DoublyCofinalPrimeThresholdCrossing_iff_cfzp016
```

as a cross-check, but do not duplicate long proofs.

---

## 11. Gate I — finite-window criticality

This is the principal Green-facing conclusion of CFZP-055.

```lean
theorem cfzp055_pntRatio_finiteWindowZeros_critical
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop) :
    ∀ rho ∈ pascalCriticalMirrorZeroWindowFinset W.R,
      rho.re = (1 : ℝ) / 2 := by
  exact cfzp017FiniteWindowZeros_critical_of_doublyCofinalPrimeThresholdCrossing
    W
    (cfzp055_pntRatio_cfzp017DoublyCofinalPrimeThresholdCrossing
      W hstrip hsub hPNT)
```

Equivalent use of the CFZP-018 criticality theorem is acceptable.

The public docstring must say explicitly:

- conditional on `hPNT`, `hstrip`, `hsub`;
- finite safe window only;
- no global RH claim.

---

## 12. Optional Gate J — a compact closure bundle

If useful for the next checkpoint, define a structure or theorem bundle containing:

```text
Cfzp017DoublyCofinalPrimeThresholdCrossing W
Cfzp018DoublyCofinalPrimeThresholdApproximateReach W
fixed defect <= 0
fixed defect = 0
finite-window criticality
```

Do not introduce a new mathematical hypothesis. This is API packaging only.

---

## 13. Roadmap update

Append CFZP-055 and mark:

```text
CFZP-054 cofinal natural-cutoff radial escape -> exact threshold crossing: CLOSED
fixed-epsilon PNT provider -> CFZP-017 cofinal exact crossing: CLOSED
fixed-epsilon exact crossing -> CFZP-018 approximate reach: CLOSED
small positive epsilon neighborhood synchronization: CLOSED
doubly cofinal CFZP-017 exact crossing: CLOSED under PNT + explicit window hypotheses
doubly cofinal CFZP-018 approximate reach: CLOSED under PNT + explicit window hypotheses
fixed second-moment defect <= 0: CLOSED under same hypotheses
safe-window fixed defect = 0: CLOSED under same hypotheses
finite-window criticality: CLOSED under same hypotheses
CFZP-018 adapter frontier: RETIRED conditionally on PNT + window hypotheses
standard PNT ratio theorem itself: OPEN / arithmetic provider
automatic interior-strip provider: OPEN / GAP
automatic subcritical-aspect provider: OPEN / GAP
globalization from finite safe windows / global RH: OPEN / later frontier
```

Do not mark PNT, automatic window construction, or global RH closed.

---

## 14. Gap firewall

Recommended:

```lean
inductive Cfzp055RadialEscapePrimeThresholdCrossingClosureGap : Prop
  | noPrimeCountingPNTRatioProvider
  | noAutomaticInteriorStripWindowProvider
  | noAutomaticSubcriticalAspectProvider
  | noGlobalFiniteWindowExhaustionProvider
```

Do not add constructors for:

- approximate reach adapter,
- cofinal exact crossing adapter,
- finite-window defect sign,
- finite-window criticality,

because these are the things CFZP-055 must close.

Historical gap types in CFZP-017/018 may remain; their wording is about an **independent/unconditional** provider, while 055 supplies a conditional provider from PNT + window hypotheses.

---

## 15. Firewall — forbidden imports / forbidden conclusions

CFZP-055 must **not**:

- prove or assume an extra form of PNT beyond `Cfzp051PrimeCountingPNTRatioAtTop`;
- add an external PNT repository dependency;
- use Mertens, Dirichlet, Bertrand, zero-density, or explicit error estimates;
- introduce an infinite prime sum;
- exchange any infinite limits;
- prove an automatic interior strip or subcritical aspect unless it falls out by trivial existing structure fields (if so, isolate that as a separate tiny theorem and document it);
- claim every nontrivial zeta zero is critical;
- claim global RH.

The finite-window theorem is already a major closure point; keep its scope exact.

---

## 16. Green criterion

CFZP-055 is Green only if the repository contains an actual theorem chain equivalent to

```text
CFZP-054 cofinal radial eta=0
  ↓
radial deficit <= 0
  ↓  existing iff
exact threshold crossing
  ↓
Cfzp017CofinalPrimeThresholdCrossingAt epsilon W
  ↓  epsilon in (0, log 2), near 0+
Cfzp017DoublyCofinalPrimeThresholdCrossing W
  ↓
Cfzp018DoublyCofinalPrimeThresholdApproximateReach W
  ↓
fixed defect <= 0
  ↓  safe-window nonnegativity
fixed defect = 0
  ↓
finite-window zeros critical
```

with only these substantive assumptions at the Green-facing top theorem:

```text
hPNT   : Cfzp051PrimeCountingPNTRatioAtTop
hstrip : Cfzp039PrimeAxisInteriorStrip W
hsub   : Cfzp027SubcriticalPhaseAspect W
```

No caller-supplied `epsilon`, phase `c`, radial target, finite analytic readiness, discrepancy bound, smooth-Abel bridge, remainder split, higher-power bound, or radial budget may remain in the final finite-window theorem.

---

## 17. Strategic note for CFZP-056

If CFZP-055 closes, the long prime-side finite-cell chain has returned to the original zero-side theorem spine.

At that point the main conditional statement becomes:

```text
PNT ratio
+ interior strip sigma < 1
+ subcritical aspect (sigma - 1/2) / T < 1
    ⇒ finite-window criticality.
```

The next checkpoint should therefore inspect the exact construction of `PascalCenteredXiResidueTransportWindow` and determine whether `hstrip` and `hsub` are:

1. already derivable from existing window fields,
2. achievable by an explicit window-construction theorem,
3. or genuinely independent geometric providers.

Only after that audit should the project decide whether the remaining arithmetic PNT provider or the window construction is the final major external boundary.