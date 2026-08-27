# GWSS-001 variable-weight source-rank audit report

Date: 2026-08-20

Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`

HEAD at audit start: `a46d90911c62ea061d284272a824bbd29e6d1902`

Working tree at audit start: clean.

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

Current GWSS stage: GWSS-001 variable-weight source-rank audit.

Load-bearing provider boundary: this report introduces no Weil positivity, Li
criterion, RH assumption, fixed-Xi defect vanishing, prime-side sign, or
unproved horizontal decay. The finite model below is abstract and is not a
claim about actual zeta zeros.

Next unresolved Gap: prove or refute, for the actual finite centered Xi
zero-window carrier and its multiplicities, a finite evaluation-map rank
theorem modulo the supported zero symmetries that also accounts for the
parameterized Mellin second-difference family. The current API has no theorem
transferring the abstract fourth-moment separation below to the actual window.

## Classification

```text
VARIABLE-WEIGHT-RANK-UNRESOLVED
```

The variable source is real, and the finite algebra below proves a concrete
non-recoverability fact against the fixed second-moment observables. The
classification remains unresolved because that fact is an abstract finite
configuration audit, not an actual-zero-window separation theorem, and no
finite/invertible reduction of the full existing Mellin family has been
formalized.

## Source map and symmetry

For a fixed radius `R`, the actual source map is

```text
h ↦ pascalCenteredXiZeroDiskWeightedMoment h R
```

and its definition is the finite multiplicity-weighted evaluation sum from
GWSS-000. Evenness imposes `h (-z) = h z`, so the weight family cannot
distinguish a point from its negative by itself. The actual disk finset is not
quotiented by this relation; any orbit pairing and multiplicity accounting must
be established from the actual Xi-zero symmetry API rather than assumed from
the name of the weight.

## Formal finite countermodel

`PascalCenteredXiVariableWeightSourceRankAudit.lean` defines
`gwssEvenOrbitMoment`, `gwssEvenOrbitRadialSecondMoment`, and
`gwssEvenOrbitHorizontalSecondMoment` for two weighted even orbits. The
configurations are

```text
A = {+1, -1, +7, -7}
B = {+5, -5, +5, -5}
```

where the repeated orbit in `B` is represented by the two orbit slots. Lean
proves `gwssEvenOrbitConfigurationA_second_eq_configurationB`,
`gwssEvenOrbitConfigurationA_radial_eq_configurationB`,
`gwssEvenOrbitConfigurationA_horizontal_eq_configurationB`, and
`gwssEvenOrbitConfigurationA_fourth_ne_configurationB`.

Numerically, both configurations have equal multiplicity, second moment,
radial second moment, and horizontal second moment:

```text
2(1^2 + 7^2) = 2(5^2 + 5^2) = 100.
```

Their fourth moments differ:

```text
2(1^4 + 7^4) = 4804,
2(5^4 + 5^4) = 2500.
```

This is a finite non-recoverability/model audit. It does not assert that
`±1`, `±7`, or `±5` are zeta zeros.

## Comparison with existing fixed observables

The model separates a `z^4` weighted moment from constant/multiplicity mass,
the holomorphic `z^2` moment, radial second moment, and horizontal second
moment. It therefore rules out a blanket claim that every even variable-weight
moment is recoverable from fixed quadratic geometry by finite algebra.

It does not yet rule out recovery from the entire parameterized Mellin
second-difference family. That family is even and differentiable, but the
repository has no theorem giving its exact finite evaluation-map rank or an
invertible reduction to the fixed observables. This is the reason for the
unresolved classification rather than a positive source-rank claim.

The finite Weil-style bridge remains only a representation of the existing
fixed defect:

```text
finite Weil-style mirror pairing = negative centered second moment
fixed defect = anti-mirror energy = 2 * horizontal energy
```

It is not promoted to the classical Weil criterion or a Guinand--Weil
positivity provider.

## Arithmetic and height boundary

The variable-weight identity still has four finite-height terms:

```text
von Mangoldt / ordinary-zeta term
archimedean term
elementary term
top-horizontal term
```

`tendsto_pascalCenteredXiFiniteArithmeticExplicitFormula` takes only the
arithmetic cutoff `X -> ∞` at a fixed finite residue window. No `T -> ∞`
limit or top-horizontal elimination is used in this audit.

## GWSS-001 closeout

The source-rank gate is not closed positively. Since the actual-window and
full-Mellin-family transfer theorem is missing, the safe classification is
`VARIABLE-WEIGHT-RANK-UNRESOLVED`. GWSS-002 is not authorized; the assignment
stops at GWSS-001.

## Axiom/build note

The new module contains only finite algebra and standard differentiability
facts. It adds no `sorry`, `admit`, axiom placeholder, positivity provider, or
public root import.
