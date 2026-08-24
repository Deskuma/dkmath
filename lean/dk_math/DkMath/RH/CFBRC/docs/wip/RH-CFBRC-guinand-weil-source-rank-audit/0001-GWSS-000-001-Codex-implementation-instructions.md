# GWSS-000 / GWSS-001 Codex implementation instructions

Date: 2026-08-20

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`

Base: `develop` at `8646c3f56591aa04a35b49d5e01ce107caf8cc3b`

Roadmap:

`lean/dk_math/DkMath/RH/CFBRC/docs/wip/RH-CFBRC-guinand-weil-source-rank-audit/0000-GWSS-roadmap.md`

## 0. Mission

Implement and audit only:

```text
GWSS-000  existing variable-weight explicit-formula inventory
GWSS-001  variable-weight source-rank audit
```

Do not proceed automatically to GWSS-002 or later stages.

This branch begins after CKSS closed with:

```text
FUNCTIONAL-EQUATION-TRANSPORT-ONLY
```

The objective is to determine whether DkMath's already-existing variable centered weight

```text
h : ℂ -> ℂ
```

supplies genuinely more spectral/source information than the fixed Xi second-moment, finite Weil-style mirror defect, horizontal energy, and other fixed observables.

This is not yet a classical Guinand--Weil positivity implementation.

## 1. Mandatory repository orientation

Before editing, report:

```text
current branch
current HEAD
working-tree status
Lean toolchain
GWSS roadmap path
global RH objective
current GWSS stage
load-bearing provider boundary
next unresolved Gap
```

Read repository source first. Do not substitute conversation summaries for the checked-out tree.

The global objective is still:

```text
zero / zero configuration
  -> independent source information
  -> off-critical detector
  -> independent arithmetic sign/upper control
  -> shrinking centered coordinate
  -> existing DkReal uniqueness
  -> RiemannHypothesis
```

The load-bearing boundary is that no RH-equivalent positivity or vanishing theorem may be introduced as a provider.

## 2. First critical fact to verify

The existing explicit-formula stack already contains a variable weight.

Inspect at minimum:

```text
DkMath.RH.CFBRC.PascalCenteredXiExplicitFormulaFunctionalEquationReflection
DkMath.RH.CFBRC.PascalCenteredXiExplicitFormulaHorizontalPairing
DkMath.RH.CFBRC.PascalCenteredXiFiniteRectangleResidueAssembly
DkMath.RH.CFBRC.PascalCenteredXiFiniteArithmeticExplicitFormula
DkMath.RH.CFBRC.PascalCenteredXiWeilMirrorDefectBridge
```

Verify the exact current declarations rather than relying on the names below.

Expected important declarations include:

```text
PascalCenteredEvenWeight
pascalCenteredXiWeightedNegLogDeriv
pascalCenteredXiZeroDiskWeightedMoment
pascalCenteredXiFiniteExplicitFormula_eq_zeta_archimedean_elementary_top
pascalCenteredXiFiniteArithmeticApproximant
tendsto_pascalCenteredXiFiniteArithmeticExplicitFormula
pascalCenteredXiFiniteArithmeticApproximant_eq_vonMangoldt_sum
PascalCenteredXiMellinWeightVerticalDecayProvider
```

The currently observed definition of evenness is:

```text
PascalCenteredEvenWeight h := forall z, h (-z) = h z
```

Confirm it in the checked-out source.

## 3. Do not misclassify the existing `h`

The finite explicit formula presently has the schematic form

```text
weighted finite Xi zero moment h
  = right-edge ordinary-zeta term h
  + archimedean term h
  + elementary term h
  + top-horizontal term h
```

for differentiable even centered weights and a finite residue-transport window.

It also has a finite von Mangoldt cutoff approximant whose cutoff limit, at a **fixed finite residue window**, converges to the same weighted zero moment.

This means the first audit question is not "can we add a test function?".

It is:

```text
What information does the already-existing weight family carry,
and is that information strictly richer than the fixed observables?
```

Do not create a duplicate test-function abstraction unless the inventory proves the present API inadequate.

## 4. GWSS-000 — inventory requirements

Produce a report:

`0002-GWSS-000-variable-weight-inventory-report.md`

### 4.1 Trace the zero-side source

Find the exact definition of:

```text
pascalCenteredXiZeroDiskWeightedMoment
```

Record:

```text
its type
its finite set / finset source
its multiplicity weighting
how h enters
whether it is literally a finite evaluation sum
which zero symmetry/window facts are built into the carrier
```

Do not infer these from theorem names.

### 4.2 Trace admissible weight freedom

Record exact hypotheses on `h` in each relevant theorem:

```text
Differentiable ℂ h
PascalCenteredEvenWeight h
other hidden/local assumptions if any
```

Determine whether the API supports arbitrary even polynomials such as:

```text
1
z^2
z^4
z^6
```

or otherwise an evidently nontrivial family.

If these examples compile only after helper lemmas, focused non-load-bearing helper lemmas are allowed.

Do not yet introduce compact support, Schwartz, Fourier transform, positivity, or classical Weil admissibility unless the current theorem actually requires them.

### 4.3 Trace arithmetic-side dependence on h

For each term in the finite formula, record how `h` appears:

```text
von Mangoldt / ordinary-zeta right-edge term
archimedean correction
elementary correction
top-horizontal contribution
```

Determine which are linear in `h` by definition or existing theorem.

If simple linearity lemmas are missing and useful for GWSS-001, they may be implemented in one focused audit module. Do not build a large functional-analysis layer.

### 4.4 Keep the two limits separate

The theorem

```text
tendsto_pascalCenteredXiFiniteArithmeticExplicitFormula
```

uses arithmetic cutoff `X -> infinity` at a fixed residue window.

This is not the same as:

```text
rectangle height T -> infinity.
```

Check explicitly whether any current source theorem removes the top-horizontal term by an infinite-height limit.

The existing horizontal-pairing module contains a weight-only vertical-decay provider marker. Its own documentation says weight decay alone is not decay of the Xi-weighted integrand.

Do not promote that provider marker to an actual horizontal-decay theorem.

### 4.5 GWSS-000 decision

Choose exactly one:

```text
VARIABLE-WEIGHT-SOURCE-ALREADY-PRESENT
FIXED-OBSERVABLE-ONLY
VARIABLE-WEIGHT-API-GAP
```

Expected but not pre-assumed result: the current explicit formula appears variable-weight, but the repository must decide.

If the result is not `VARIABLE-WEIGHT-SOURCE-ALREADY-PRESENT`, stop after GWSS-000 and do not start GWSS-001.

## 5. GWSS-001 — source-rank audit

Proceed only after `VARIABLE-WEIGHT-SOURCE-ALREADY-PRESENT`.

Produce a report:

`0003-GWSS-001-variable-weight-source-rank-audit-report.md`

A focused Lean audit module may be added only if it proves a concrete source-rank or non-recoverability fact.

Suggested module name if needed:

```text
DkMath.RH.CFBRC.PascalCenteredXiVariableWeightSourceRankAudit
```

Do not create the module merely to hold marker propositions.

## 6. What "source-rank increase" means here

A family of syntactically different `h` is not enough.

The audit must determine whether the map

```text
h |-> pascalCenteredXiZeroDiskWeightedMoment h R
```

contains information not recoverable from the already-existing fixed scalar observables by finite/invertible algebra.

Compare against at least:

```text
pascalCenteredXiFixedSecondMomentDefectFunctional
pascalCriticalMirrorZeroWindowFiniteWeilMirrorPair
pascalCriticalMirrorZeroWindowHorizontalEnergy
existing centered second moment / radial second moment
existing Mellin second-difference fixed observables
finite arithmetic defect representation
```

The fixed finite Weil-style bridge itself states that it is not the classical Weil criterion or Guinand--Weil formula. Preserve that firewall.

## 7. Preferred finite-algebra audit

Stay finite first.

If the weighted zero moment is a finite evaluation sum, test whether admissible even weights separate more finite spectral configurations than the fixed quadratic observable.

Valid strategies include:

```text
A. explicit even polynomial moments
B. finite interpolation modulo z <-> -z symmetry
C. Vandermonde / power-moment rank
D. finite evaluation-map linear independence
E. an abstract countermodel showing equal fixed second moment but unequal higher weighted moment
```

A countermodel must be labeled as a non-recoverability/model audit. Do not claim hypothetical points are actual zeta zeros.

If source-rank increase can only be demonstrated for an abstract finite configuration and cannot yet be transferred to the actual zero-window API, classify carefully as unresolved rather than overclaiming.

## 8. Symmetry audit is mandatory

Because admissible weights are even,

```text
h (-z) = h z.
```

Therefore the family cannot distinguish `z` from `-z` by itself.

Trace how centered Xi zero symmetries act on the finite window:

```text
z -> -z
z -> conjugate z
z -> -conjugate z
```

where supported by existing source.

Do not assume that evenness alone distinguishes the off-critical horizontal coordinate.

Record exactly which orbit information survives the weighted moment after the actual zero-window symmetries and multiplicities are included.

This symmetry audit is load-bearing for the source-rank conclusion.

## 9. Do not jump from rank to RH

Even if variable-weight source rank increases, that is not yet an RH proof.

The next unresolved structure would still be:

```text
variable spectral source
  -> choose an off-critical witness weight
  -> arithmetic side must independently constrain that witness
```

The finite formula currently includes the top-horizontal contribution, so a prime-only interpretation is not automatic.

Do not discard:

```text
archimedean term
elementary term
top-horizontal term
```

by calling them corrections.

## 10. Positivity firewall

Forbidden as load-bearing assumptions/providers in GWSS-000/001:

```text
classical Weil positivity for all test functions
Li criterion
RH
fixed-Xi defect vanishing
prime-side sign after cancellation
reverse Cauchy--Schwarz
unproved T -> infinity horizontal decay
unproved limit exchange
```

If a theorem found in Mathlib/DkMath is equivalent to RH, record that fact and stop using it as a provider.

## 11. No classical Guinand-Weil implementation yet

Do not add a new classical explicit-formula development in GWSS-000/001.

Do not start building:

```text
Schwartz-space infrastructure
Fourier-transform admissibility
Paley-Wiener theory
full Weil quadratic form
Li coefficients
infinite zero sum
```

unless the source-rank audit proves that the existing finite variable-weight stack is insufficient for a very specific reason. Such a finding belongs in the report and authorizes a later branch decision, not immediate implementation.

## 12. Required GWSS-001 classification

Choose exactly one:

```text
VARIABLE-WEIGHT-SOURCE-RANK-INCREASE
VARIABLE-WEIGHT-REDUNDANT
VARIABLE-WEIGHT-RANK-UNRESOLVED
```

For `VARIABLE-WEIGHT-SOURCE-RANK-INCREASE`, the report must name the exact theorem or finite countermodel proving non-recoverability from the fixed observables.

For `VARIABLE-WEIGHT-REDUNDANT`, identify the exact reduction.

For `VARIABLE-WEIGHT-RANK-UNRESOLVED`, identify the smallest missing theorem.

## 13. Stop conditions

Stop immediately if work begins turning into:

```text
another Eta endpoint normalization
completed-zeta reciprocal transport
fixed-Xi defect renaming
unbounded chains of polynomial helper modules
classical Weil positivity assumed as a theorem provider
T -> infinity work before source rank is decided
prime-side sign search before an off-critical witness exists
```

Do not proceed to GWSS-002 in this assignment.

## 14. Verification

For every modified or added Lean module:

```text
lake build <focused module>
```

Then run at least the relevant root build if the public import surface changes.

Also run:

```text
git diff --check
```

Check that no new:

```text
sorry
admit
axiom placeholder
```

was introduced.

Use `#print axioms` on any new load-bearing theorem.

Documentation-only audit results do not require artificial theorem creation solely to satisfy this step.

## 15. Final report format

The final response must begin with:

```text
Global objective:
Current GWSS stage:
Load-bearing boundary:
Next unresolved Gap:
```

Then state GWSS-000 and GWSS-001 classifications separately, list changed files, exact build commands/results, and whether GWSS-002 is authorized.

Unless GWSS-001 returns a rigorously supported source-rank increase, GWSS-002 is not authorized.
