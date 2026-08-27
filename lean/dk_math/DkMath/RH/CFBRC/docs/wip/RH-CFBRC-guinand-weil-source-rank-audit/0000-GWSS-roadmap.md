# RH-CFBRC Guinand-Weil Source-Rank Audit Roadmap

Date: 2026-08-20

Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`

Base: `develop` at `8646c3f56591aa04a35b49d5e01ce107caf8cc3b`

## 0. Route identity

GWSS starts after CKSS closed with:

```text
FUNCTIONAL-EQUATION-TRANSPORT-ONLY
```

The route changes source family. It must not continue the Eta endpoint-tail or completed-zeta reciprocal-transport routes.

The name `Guinand-Weil Source-Rank Audit` is intentionally provisional. This branch does **not** begin by importing or assuming the classical Weil positivity criterion. It begins by auditing the variable test-function machinery already present in DkMath's finite centered-Xi explicit-formula stack.

The central question is:

```text
Does the existing variable weight h provide genuinely higher source rank
than the fixed Xi / finite mirror observables already audited?
```

Only after this is answered may the project ask whether a classical Guinand--Weil-style witness family or positivity statement is needed.

## 1. Global RH objective

The global proof architecture remains:

```text
standard nontrivial zeta zero / zero configuration
  -> independent arithmetic/spectral information
  -> off-critical detector
  -> source-derived upper/sign control
  -> shrinking centered coordinate
  -> existing DkReal uniqueness
  -> Mathlib RiemannHypothesis
```

Do not count an RH-equivalent positivity criterion as the missing provider.

## 2. Trusted closed frontiers

Do not re-open by repackaging:

```text
ZDI finite-certificate scalar bridge          O-INFORMATION
Eta endpoint pair                             FOUND
endpoint positive scalar upper side           FOUND
endpoint exact normalized rates               FOUND
raw common-scale dichotomy                    FOUND
raw frequent-upper global provider            RH-EQUIVALENT
CKSS completed-zeta common-kernel candidate   TRANSPORT-ONLY
DkReal completion                              READY / INACTIVE
```

The next source must add information not obtainable by invertible transport or post-processing from these objects.

## 3. Critical repository fact discovered before GWSS

The current DkMath explicit-formula stack is **not fixed-weight only**.

`PascalCenteredXiFiniteArithmeticExplicitFormula.lean` already works with a variable

```text
h : ℂ -> ℂ
```

under contracts including

```text
Differentiable ℂ h
PascalCenteredEvenWeight h
```

and proves, for a fixed finite residue window, an exact spectral/arithmetic identity of the schematic form

```text
weighted zero moment h
  = ordinary-zeta right edge h
  + archimedean correction h
  + elementary correction h
  + top-horizontal contribution h.
```

It also defines finite von Mangoldt arithmetic approximants depending on `h` and proves their cutoff convergence to the finite weighted zero moment for each fixed window.

Therefore GWSS must **not** start by building a new abstract test-function API unless the existing one is proved insufficient.

## 4. Existing fixed-Weil firewall

`PascalCenteredXiWeilMirrorDefectBridge.lean` explicitly states that its object is only a finite *Weil-style* mirror pairing. It is not:

```text
classical Weil criterion
Li coefficient identity
Guinand--Weil explicit formula
```

It contains no admissible test-function family and no defect-vanishing provider.

GWSS must preserve this distinction.

## 5. GWSS-000 — existing variable-weight explicit-formula inventory

### Mission

Determine exactly what source freedom DkMath already has before adding new mathematics.

### Required inventory

Trace the declaration chain containing at least:

```text
PascalCenteredEvenWeight
pascalCenteredXiZeroDiskWeightedMoment
pascalCenteredXiWeightedNegLogDeriv
pascalCenteredXiFiniteExplicitFormula_eq_zeta_archimedean_elementary_top
pascalCenteredXiFiniteArithmeticApproximant
tendsto_pascalCenteredXiFiniteArithmeticExplicitFormula
pascalCenteredXiFiniteArithmeticApproximant_eq_vonMangoldt_sum
```

Also inspect the contour/residue modules that define the zero-side weighted moment and the horizontal-pairing modules that impose evenness.

### Questions

1. Is `h` genuinely arbitrary inside a useful infinite-dimensional class, or already restricted to a fixed generated family?
2. Which exact symmetry is imposed by `PascalCenteredEvenWeight`?
3. Does the zero-side map depend on `h` only through evaluations `h ρ` at finitely many centered Xi zeros?
4. Which pieces of the arithmetic side are linear in `h`?
5. Which terms prevent a direct prime-only source interpretation?
6. Is the top-horizontal contribution an independent unresolved term for each finite window?
7. Does any current theorem take `T -> ∞` or eliminate that term? Do not infer such a theorem from weight-only decay providers.

### Classification

End GWSS-000 with exactly one primary classification:

```text
VARIABLE-WEIGHT-SOURCE-ALREADY-PRESENT
FIXED-OBSERVABLE-ONLY
VARIABLE-WEIGHT-API-GAP
```

If the first classification holds, do not add a duplicate test-function abstraction.

## 6. GWSS-001 — variable-weight source-rank audit

Proceed only if GWSS-000 finds a genuine variable-weight source.

### Mission

Determine whether the family

```text
h |-> pascalCenteredXiZeroDiskWeightedMoment h R
```

contains strictly more spectral information than the fixed second-moment / fixed Weil-style defect observables.

The question is source rank, not positivity.

### Preferred audit strategy

Use finite-window mathematics first.

Because the zero disk is finite, audit whether admissible even holomorphic/differentiable weights can separate distinct centered-zero configurations modulo the symmetry forced by evenness.

Possible proof styles include:

```text
explicit polynomial weights
finite interpolation
Vandermonde / moment separation
finite-dimensional evaluation-map rank
countermodel showing collapse to an existing finite moment family
```

Do not assume a full classical test-function theorem if finite algebra suffices.

### Required source-rank comparison

Compare against at least:

```text
fixed centered Xi second-moment defect
finite Weil-style mirror pairing
horizontal energy
existing Mellin second-difference fixed families
prime-side finite arithmetic representation
```

A variable family counts as genuinely higher rank only if it is not recoverable from finitely many existing fixed scalar observables by invertible algebra.

### Classification

End GWSS-001 with one of:

```text
VARIABLE-WEIGHT-SOURCE-RANK-INCREASE
VARIABLE-WEIGHT-REDUNDANT
VARIABLE-WEIGHT-RANK-UNRESOLVED
```

Do not start positivity or witness implementation before this Gate closes.

## 7. GWSS-002 — off-critical witness family

Only after `VARIABLE-WEIGHT-SOURCE-RANK-INCREASE`.

Goal: given an off-critical zero or a finite window containing horizontal displacement, construct an admissible weight whose zero-side observable detects that displacement in a way not equivalent to the fixed quadratic defect.

This stage should seek a one-way witness theorem, not the full Weil criterion.

Potential target shape:

```text
off-critical zero in window
  -> exists admissible h,
       detector(h, window) has certified nonzero / sign behavior.
```

Do not assume positivity for all test functions.

## 8. GWSS-003 — arithmetic control firewall

Only after an off-critical witness exists.

Audit whether the finite arithmetic explicit formula gives an **independent source-derived** sign or upper bound for that witness.

The existing finite formula includes:

```text
prime/von-Mangoldt term
archimedean term
elementary term
top-horizontal term
```

The top-horizontal term must not be silently discarded.

If removing it requires an unavailable `T -> ∞` theorem, zero-avoidance sequence, Xi growth bound, or exchange of limits, name that Gap explicitly.

If the required sign theorem is equivalent to a classical Weil positivity criterion or to RH, close the route with:

```text
RH-EQUIVALENT-PROVIDER
```

## 9. GWSS-004 — classical Guinand-Weil infrastructure decision

Only after GWSS-003 identifies a precise missing analytic theorem.

At that point decide whether to:

```text
A. formalize a minimal classical Guinand--Weil explicit-formula fragment;
B. build a finite-window substitute sufficient for the witness;
C. close because the missing positivity/control is RH-equivalent;
D. close because the required Mathlib analytic infrastructure is absent.
```

Do not build a large classical theory before this decision Gate.

## 10. Source-rank firewall

Reject as non-new any candidate obtained solely by:

```text
critical-mirror reindexing
conjugation
evenness rewrite
functional-equation reflection
invertible change of variables
nonzero scalar multiplication
fixed finite linear combination of already-audited observables
post-hoc norm-square / Gram quadraticization
```

The existence of many syntactic weights is not sufficient; the evaluation/source map must carry genuinely more information.

## 11. Positivity firewall

Do not use any of the following as an unexplained provider:

```text
Weil positivity for all admissible test functions
Li criterion
fixed-Xi defect vanishing
RH itself
reverse Cauchy--Schwarz
prime-side positivity after cancellation has already occurred
```

A theorem may be named and audited as RH-equivalent, but must not be counted as progress toward a proof.

## 12. Finite-window discipline

The existing explicit formula is finite-height and finite-window. Preserve that distinction.

In particular, do not conflate:

```text
cutoff X -> ∞ at fixed residue window
```

with

```text
rectangle height T -> ∞
```

The former is already formalized. The latter remains a separate analytic problem where applicable.

## 13. Immediate authorized scope

Start only:

```text
GWSS-000
GWSS-001
```

No GWSS-002 witness construction, classical Weil criterion, global positivity theorem, or infinite-height limit is authorized until source rank is classified.

## 14. Mandatory orientation in every report

Every implementation report must restate:

```text
global objective
current GWSS stage
load-bearing assumption/provider boundary
next unresolved Gap
```

If the module count begins increasing without changing one of these four items, stop and perform a route-drift audit.
