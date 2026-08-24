# GWSS-003A finite arithmetic control audit report

Date: 2026-08-21
Repository: `Deskuma/dkmath`
Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`

## 1. Orientation and bounded scope

The implementation was performed at the repository checkout
`/home/deskuma/develop/lean/dkmath/lean/dk_math`.

```text
branch:     wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0
HEAD:       24e5475e4ab06ea5a62ea350238d93d0fb639a0a
toolchain:  leanprover/lean4:v4.32.2
stage:      GWSS-003A
```

The working tree was clean before this stage.  The bounded documents read
before editing were the corrected GWSS-002 report, the GWSS-002D correction
instructions and report, and the four source modules named by the GWSS-003A
instructions.  The global objective remains:

```text
zero configuration -> independent source -> off-critical detector
  -> arithmetic control -> centered-coordinate uniqueness -> RH
```

The load-bearing boundary is unchanged.  GWSS-002D supplies an admissible,
target-dependent finite Mellin witness with

```text
zeroMoment(h) = ((z^2).im : ℂ) * orbitMass(z^2) != 0.
```

GWSS-003A may use that fact to identify the value of an already-proved finite
explicit formula, but it may not call the rewritten value an independent
arithmetic provider.  No RH, Weil positivity, Li criterion, functional
equation as a new source, limit exchange, or horizontal removal is used.

## 2. Implemented Lean API

The focused module is:

`DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessArithmeticControlAudit.lean`

It contains the following compact pieces.

### A. Named finite RHS and witness substitution

`pascalCenteredXiFiniteArithmeticRHS` names the exact finite sum

```text
2 ordinary-zeta right-edge
+ 2 archimedean right-edge
+ 2 elementary right-edge
+ 2 top-horizontal.
```

The top-horizontal term is not absorbed into another term.  The theorem
`pascalCenteredXiFiniteArithmeticRHS_eq_zeroMoment_factor` identifies this
RHS with `-(2 * π * I) * zeroMoment` for an arbitrary differentiable even
weight.  The requested specialized theorem
`pascalCenteredXiMellinWitnessFiniteExplicitFormula` applies this generic
identity to `pascalCenteredXiMellinWitnessWeight` using only the existing
differentiability and evenness lemmas.

### B. Detector-forced phase

`exists_pascalCenteredXiMellinWitness_finiteArithmeticRHS_phase` combines the
corrected global witness with the named finite RHS.  For an off-critical zero
`z`, it records exactly

```text
finiteArithmeticRHS(h, W)
  = -(2 * π * I) * (((z^2).im : ℂ) * orbitMass(z^2)).
```

This is a bookkeeping consequence of the zero-side detector equality.  It is
not an independent arithmetic-control theorem and does not assert that the
arithmetic RHS vanishes or has a forbidden phase.

### C. Finite-linearity bridges

`pascalCenteredXiMellinWitnessWeight_mul_eq_sum` proves the basic finite
linearity identity.  Its arithmetic-surface instances cover:

```text
pascalCenteredXiMellinWitnessOrdinaryZetaIntegrand_eq_sum
pascalCenteredXiMellinWitnessPrimeCutoffIntegrand_eq_sum
pascalCenteredXiMellinWitnessArchimedeanIntegrand_eq_sum
pascalCenteredXiMellinWitnessElementaryIntegrand_eq_sum
pascalCenteredXiMellinWitnessTopHorizontalIntegrand_eq_sum
```

These are pointwise identities, so they do not smuggle new integrability
assumptions into the API.  The finite interval integrals already have their
own integrability and convergence theorems.  A general integral-level finite
functional-linear-algebra framework was intentionally not introduced: the
remaining step is a routine, but term-specific, `intervalIntegral` lifting
requiring the corresponding integrability hypotheses.  The pointwise
bridges already show where the target-dependent coefficients enter every
arithmetic surface.

## 3. Existing independent-control inventory

The audit found the following relevant existing results.

| Surface | Existing theorem/API | Exact strength | Independent control? |
|---|---|---|---|
| prime / von Mangoldt cutoff | `pascalPrimePowerRightEdgeCutoffIntegral_eq_vonMangoldt_sum` | finite von Mangoldt expansion for fixed `σ`, `T`, `X` and differentiable `h` | identity only |
| prime / ordinary-zeta limit | `tendsto_pascalPrimePowerRightEdgeCutoffIntegral` and `tendsto_pascalPrimePowerRightEdgeCutoffIntegral_of_residueTransportWindow` | cutoff convergence at fixed finite height/window | convergence only; its endpoint is identified through the finite explicit formula |
| ordinary-zeta term | `pascalXiOrdinaryZetaRightEdgeIntegral` and `intervalIntegrable_pascalXiOrdinaryZetaRightEdgeIntegrand_of_residueWindow` | named finite integral and interval integrability | no sign, phase, vanishing, or useful norm obstruction |
| archimedean term | `pascalXiArchimedeanRightEdgeIntegral` and `intervalIntegrable_pascalXiArchimedeanRightEdgeIntegrand` | named finite integral and interval integrability | no sign, phase, vanishing, or useful norm obstruction |
| elementary term | `pascalXiElementaryRightEdgeIntegral` and `intervalIntegrable_pascalXiElementaryRightEdgeIntegrand` | named finite integral and interval integrability | no sign, phase, vanishing, or useful norm obstruction |
| combined finite surface | `pascalCenteredXiFiniteExplicitFormula_eq_zeta_archimedean_elementary_top` | exact four-term finite identity | not independent arithmetic control |
| fixed Mellin approximant | `tendsto_pascalCenteredXiMellinFiniteArithmeticExplicitFormula` and `pascalCenteredXiMellinFiniteArithmeticApproximant_eq_vonMangoldt_sum` | fixed `ε > 0`, `τ`, finite window, and `X → ∞` / finite von Mangoldt form | no sign, phase, or zero-exclusion estimate |

No audited theorem supplies a finite norm bound, phase restriction, sign
theorem, or vanishing statement strong enough to contradict the nonzero
detector.  In particular, convergence to the detector-forced endpoint is not
counted as independent control because the endpoint is obtained by the
zero-side witness identity.

## 4. Mandatory top-horizontal audit

The existing horizontal module provides:

```text
pascalCenteredXiHorizontalPair_eq_two_top
pascalCenteredXiTopHorizontalContribution
PascalCenteredXiMellinWeightVerticalDecayProvider
not_same_zero_set_window_of_zero_outside_ball_inside_rectangle
```

The first two are finite pairing/definition results.  The provider structure
controls only the Mellin weight on the top edge; it does not contain the Xi
logarithmic derivative.  The last theorem records the fixed-window
localization obstruction.

The audit found none of the following:

```text
A  exact top-horizontal vanishing at the existing finite W
B  a finite top-horizontal bound with a useful phase/sign consequence
C  T -> infinity decay for the full Xi-weighted horizontal integrand
D  zero-avoidance heights plus Xi growth sufficient to prove C
```

Therefore weight-only decay is not promoted to horizontal-integrand decay,
and the finite top term remains in every identity in this stage.

## 5. Target-dependent coefficient audit

The witness coefficients are produced by the actual-window Mellin inverse and
are scaled by the target factor `(z^2).im`.  The new pointwise linearity
bridges make this dependence explicit.  No theorem was found or assumed that
uniformly bounds

```text
sum_i |c_i|, max_i |c_i|, the inverse matrix, its condition number,
the selected dilations, or |(z^2).im|^{-1}.
```

Thus the present API does not support an unconditional quantitative estimate
that is uniform over the target-dependent witness family.  This is recorded
as an unresolved control issue, not as a hidden hypothesis.

## 6. Minimal contradiction-provider audit

For the exact normalization used here, any independent provider of one of the
following shapes would be semantically sufficient for the relevant
off-critical exclusion:

```text
finiteArithmeticRHS(h, W).im = 0
finiteArithmeticRHS(h, W) = 0
```

or a justified limit theorem forcing the RHS to zero while preserving the
fixed nonzero detector.  Current evidence classifies these as:

```text
finite RHS identity:                         AVAILABLE, but not independent
finite RHS phase from the detector:           AVAILABLE as bookkeeping only
finite RHS imaginary-part obstruction:       MISSING
full top-horizontal decay/vanishing:         REQUIRES-TOP-HORIZONTAL-CONTROL
uniform target-coefficient estimate:         REQUIRES-TARGET-COEFFICIENT-CONTROL
prime-side sign/phase theorem:               REQUIRES-NEW-PRIME-SIDE-SIGN/PHASE-THEOREM
```

No current justification for these providers is accepted from RH, classical
Weil positivity, Li, a functional-equation reindexing, or the zero-side
detector itself.

## 7. Stop classification

```text
MELLIN-WITNESS-FINITE-ARITHMETIC-IDENTITY-FOUND-CONTROL-GAP
```

The exact witness substitution, detector-forced phase, and finite pointwise
linearity are closed.  No independent arithmetic control has been found, and
the top-horizontal term remains an explicit load-bearing gap.  GWSS-004 and
all height-limit or RH-oriented developments remain outside this assignment.

## 8. Verification

Focused verification completed:

```text
lake build DkMath.RH.CFBRC.PascalCenteredXiMellinWitnessArithmeticControlAudit
```

The focused target built successfully under Lean 4.32.2.  The ordinary-zeta
bridge now exposes only the variables it uses.  `git diff --check` and the
final axiom audit report the expected foundational dependencies only:
`propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, `admit`, or
`native_decide` was introduced.
