# RH-CFBRC CKSS closeout report

Date: 2026-08-20

Branch: `wip/RH-CFBRC-common-kernel-second-source-260820-v0`

## Decision

```text
CKSS: CLOSED — FUNCTIONAL-EQUATION-TRANSPORT-ONLY
```

CKSS-000 consolidated the ZDSS-005 frontier into the public `DkMath.RH` import surface.

CKSS-001 audited the pinned Mathlib/DkMath completed-zeta functional-equation source chain and found no independent pre-reflection common source carrying the original and critical-mirror zero-derived amplitudes on one source variable, measure/kernel, and scale.

Therefore:

```text
CKSS-002 MUST NOT START
```

## Global objective

The global RH formalization objective remains unchanged:

```text
standard nontrivial zeta zero
  -> independent zero-derived information
  -> centered-coordinate detector
  -> shrinking centered coordinate
  -> existing DkReal uniqueness
  -> Mathlib RiemannHypothesis
```

CKSS tested whether completed-zeta functional-equation infrastructure supplied the missing independent same-scale coupling. It does not, in the current pinned stack.

## Trusted result carried forward

The following frontier is now fixed and should not be re-opened by renaming or further endpoint normalization:

```text
endpoint source pair                    FOUND
endpoint positive scalar upper side     FOUND
exact individual endpoint rates         FOUND
raw common-scale dichotomy              FOUND
same-scale independent coupling          MISSING
global frequent-upper provider          RH-EQUIVALENT
DkReal completion                        READY / INACTIVE
completed-zeta common-kernel candidate  TRANSPORT-ONLY
```

## Why CKSS closes

The audited source chain is structurally:

```text
jacobiTheta₂
  -> evenKernel / cosKernel
  -> reciprocal-variable kernel functional equation
  -> WeakFEPair
  -> WeakFEPair.symm
  -> completed transforms
  -> completed-zeta functional equation
```

The second member is related through reciprocal-variable functional-equation transport and an invertible pair swap. Rewriting both sides into a visually common integral does not create new source rank when that common form is obtained only by this invertible transport.

At the Riemann specialization the symmetry is stronger still. Consequently this family cannot be counted as a new independent zero-derived second source.

## Positivity firewall

The audit also found no source-derived reverse inequality that would turn smallness of a whole oscillatory Mellin integral into an upper bound on a positive diagonal energy.

The ordinary direction remains schematically:

```text
norm(whole integral)^2 <= integral(pointwise norm-square)
```

Therefore post-processing by squaring, Gram formation, or fixed-Xi defect construction does not repair the missing information direction.

## Closed sub-routes

Do not continue CKSS by adding:

```text
more Eta-tail terms
endpoint-specific re-normalizations
subsequence/cofinal wrappers
reciprocal-variable rewrites presented as new sources
WeakFEPair/symm repackaging
post-hoc Gram or norm-square constructions
fixed-Xi vanishing providers
moving-frame / positive-density residual estimates
```

## Next source family

The next investigation should change source family rather than refine the same functional equation.

Recommended route:

```text
GWSS — Guinand-Weil Source-Rank Audit
```

The initial question is not whether the full Weil positivity criterion proves RH. That would risk importing an RH-equivalent provider.

The initial question is narrower:

```text
Does a variable admissible test-function explicit formula provide genuinely
higher source rank than the existing fixed Xi / finite mirror observables?
```

Only if that source-rank question is answered positively should an off-critical witness or positivity/sign analysis begin.

## Handoff Gate

The next branch should begin with:

```text
GWSS-000 existing explicit-formula / fixed-Xi inventory
GWSS-001 variable test-function source-rank audit
```

Do not authorize a Weil-positivity theorem, Li criterion, or RH-equivalent positivity provider at branch start.

## Verification inherited from implementation

The implementation report records successful checks:

```text
lake build DkMath.RH.CFBRC.ZeroDerivedSameScaleCrossEndpointCouplingAudit
lake build DkMath.RH
# final root build: 9097 jobs
git diff --check
```

No new `sorry`, `admit`, axiom placeholder, or load-bearing CKSS theorem was introduced.

## Closeout

CKSS is a successful negative audit: it eliminates the completed-zeta functional-equation common-kernel idea as a source-rank increase in the current formalization stack.

The next research branch must seek genuinely new information coordinates rather than another invertible presentation of the same endpoint data.
