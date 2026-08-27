# GWSS-000 variable-weight inventory report

Date: 2026-08-20

Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`

HEAD at audit start: `a46d90911c62ea061d284272a824bbd29e6d1902`

Working tree at audit start: clean.

Toolchain: `leanprover/lean4:v4.32.2`

Roadmap: `0000-GWSS-roadmap.md`

## Orientation

Global objective:

```text
zero / zero configuration
  -> independent source information
  -> off-critical detector
  -> independent arithmetic sign/upper control
  -> shrinking centered coordinate
  -> existing DkReal uniqueness
  -> RiemannHypothesis
```

Current GWSS stage: GWSS-000, followed by the authorized GWSS-001 audit.

Load-bearing provider boundary: no RH-equivalent positivity, fixed-Xi defect
vanishing, prime-side sign after cancellation, unproved `T -> ∞` horizontal
decay, or limit exchange may be introduced as a provider.

Next unresolved Gap: after GWSS-001, determine whether the actual finite Xi
zero-window evaluation map has source rank beyond the existing fixed and
Mellin observables.  The abstract finite model is not an actual-zero theorem.

## Decision

```text
VARIABLE-WEIGHT-SOURCE-ALREADY-PRESENT
```

The checked-out API already contains a variable centered weight.  No duplicate
test-function abstraction was added.

## Zero-side source

The exact declaration is

```lean
pascalCenteredXiZeroDiskWeightedMoment
    (h : ℂ → ℂ) (R : ℝ) : ℂ
```

from `PascalCenteredXiOuterContourResidueBridge.lean`.  Its definition is

```lean
∑ a ∈ pascalCenteredXiZeroDiskFinset R,
  (pascalCenteredXiZeroMultiplicity a : ℂ) * h a
```

Therefore it is literally a finite evaluation sum.  The carrier is
`pascalCenteredXiZeroDiskFinset R`, obtained from the finite set

```text
{z | z ∈ Metric.closedBall 0 R ∧ z ∈ pascalCenteredXiZeros}
```

and the coefficient is the existing Xi-zero multiplicity.  No quotient by
`z ↔ -z` is built into the finset: the carrier stores centered Xi zeros as
points.  The existing centered/ordinary window bridge identifies this carrier
with the translated finite critical-mirror zero window.

The existing specializations
`pascalCenteredXiZeroDiskWeightedMoment_one` and
`pascalCenteredXiZeroDiskWeightedMoment_second` recover the disk multiplicity
and centered holomorphic second moment.

## Weight freedom

The exact evenness contract is

```lean
def PascalCenteredEvenWeight (h : ℂ → ℂ) : Prop :=
  ∀ z, h (-z) = h z
```

The generic finite formula requires both

```text
Differentiable ℂ h
PascalCenteredEvenWeight h
```

The arithmetic approximant expansion requires differentiability; its cutoff
convergence requires both hypotheses.  The Mellin specialization proves both
contracts from `ε > 0` for the existing canonical Mellin second-difference
weight.

The focused audit module checks the polynomial examples `1`, `z^2`, `z^4`,
and `z^6` as even differentiable weights.  This is a small API inventory
extension, not a compact-support, Schwartz, Fourier, or classical Weil layer.

## Arithmetic-side dependence on `h`

The exact finite formula is

```lean
pascalCenteredXiFiniteExplicitFormula_eq_zeta_archimedean_elementary_top
```

with the schematic decomposition

```text
-2πi * weighted zero moment h
  = 2 * ordinary-zeta right-edge integral h
  + 2 * archimedean right-edge integral h
  + 2 * elementary right-edge integral h
  + 2 * top-horizontal contribution h.
```

Each term evaluates `h` at the relevant centered edge point and multiplies it
by the corresponding fixed-Xi or ordinary-coordinate term.  Thus all four
terms are linear in the supplied weight by definition and interval-integral
algebra.  No correction term is discarded.

The finite arithmetic approximant is
`pascalCenteredXiFiniteArithmeticApproximant h W X`.  The theorem
`tendsto_pascalCenteredXiFiniteArithmeticExplicitFormula` proves `X -> ∞`
convergence at a fixed finite residue window `W`, while
`pascalCenteredXiFiniteArithmeticApproximant_eq_vonMangoldt_sum` retains the
archimedean, elementary, and top-horizontal terms next to the finite
von Mangoldt sum.

## Height-limit audit

No inspected theorem removes the top-horizontal contribution by a rectangle
height limit.  The horizontal-pairing module contains
`PascalCenteredXiMellinWeightVerticalDecayProvider` as a weight-only provider
contract.  Its documentation explicitly separates weight decay from decay of
the Xi-weighted integrand, so it cannot be promoted to a horizontal-decay or
`T -> ∞` theorem.

The two limits remain distinct:

```text
X -> ∞ at fixed W       proved
T -> ∞                  not supplied here
```

## GWSS-000 closeout

The current stack has genuine variable-weight finite source data, so GWSS-001
is authorized.  The finite formula remains fixed-window and finite-height; it
is not a classical Guinand--Weil positivity implementation.
