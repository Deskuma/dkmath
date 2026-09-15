# Gnomon / MultiGauge Primitive Transition 260915 v0

Status: ACTIVE

Repository: `Deskuma/dkmath`

Branch:

```text
wip/number-theory-gnomon-multigauge-primitive-transition-260915-v0
```

Base:

```text
develop @ 8b0e62cccdbbe978d89b57d878398101f29368d9
```

## Purpose

PR #98 promoted neutral gnomon algebra and proved the multiplicative Petal law

```text
oddGnomon (petalMul a b) = oddGnomon a * oddGnomon b.
```

PR #99 proved exact adjacent-square-shell support turnover in the lower and upper regions.

The previous MultiGauge provider audit stopped at:

```text
NO UNCONDITIONAL PRIMITIVE PROVIDER FOUND
```

because no existing application supplied two genuinely different coprime GN stages with an independently meaningful balance coefficient.

The promoted Petal law changes that conclusion in degree two.  With the canonical stage

```text
P(n) := GNGaugeStage 2 with x = 1, u = n
```

we have

```text
P(n).value = oddGnomon n.
```

Hence

```text
P(a) -> P(petalMul a b)
```

admits the exact MultiGauge balance

```text
second.value * 1 = first.value * oddGnomon b.
```

The numerator `oddGnomon b` is an independent Petal factor, not an endpoint-copy coefficient.  This is the first intended unconditional primitive-shape provider in the campaign.

## Current production targets

```text
DkMath/NumberTheory/MultiGauge/GnomonPetalTransition.lean
DkMath/NumberTheory/MultiGauge/GnomonPetalPath.lean
DkMath/NumberTheory/Legendre/GnomonPetalTurnover.lean
```

The first module owns the generic degree-two provider; the path module
composes it through the generic `GNGaugePath` API; and the Legendre module is
application-side only, connecting the provider to the exact lower
adjacent-shell turnover theorem.

## Current checkpoint

Implemented and validated in the branch:

```text
oddGnomonGaugeStage
gnomonPetalTransition
primeEscapes_gnomonPetalTransition_second_of_first
prime_dvd_oddGnomon_factor_of_petal_new_capture
petalFold
petalPathTransitions
gnomonPetalPath
gnomonPetalPath_balance_value
oddGnomon_petalFold
primeEscapes_all_stages_gnomonPetalPath
exists_petalFactor_dvd_of_start_escape_of_captured_stage
exists_petalFactor_dvd_of_start_escape_of_end_caught

mem_reindexed_primeSupport_inter_lower_petalMul_iff
common_lower_dvd_gnomonPetalTransition_numerator_of_not_dvd_first
disjoint_reindexed_primeSupport_lower_petalMul_of_factor_avoid
```

Interpretation:

```text
Petal multiplication
    -> genuine degree-two primitive transition
    -> transition numerator carries new prime support
    -> lower adjacent-shell common support factors through Petal support
    -> non-inherited common support is localized to the transition numerator
```

## Scope discipline

This branch does not claim:

```text
Legendre's conjecture;
a prime in every square interval;
full-cover failure;
a quantitative turnover capacity bound;
a general primitive transition for arbitrary degree;
prime existence or global coverage derived from Petal atomicity;
Norm/lattice consequences beyond already merged MultiGauge/TraceOne work.
```

## Validation status

Focused Lean builds for `DkMath.Gnomon.PetalPrime`,
`DkMath.NumberTheory.Legendre.GnomonPetalTurnover`,
`DkMath.NumberTheory.MultiGauge.GnomonPetalPath`, and the
`DkMath.NumberTheory.MultiGauge` facade pass.  The GMPT-000/001/002/003
declarations above are therefore **IMPLEMENTED / VALIDATED** at the checked
module boundary.  This does not extend the scope to Legendre's conjecture,
prime existence, or a quantitative capacity result.
