# CKSS-000 / CKSS-001 Codex implementation instructions

Date: 2026-08-20

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-common-kernel-second-source-260820-v0`

Base line: `develop` at `c29de6da5a6c180483fea6b216ad6281402396fb`

Roadmap: `lean/dk_math/DkMath/RH/CFBRC/docs/wip/RH-CFBRC-common-kernel-second-source/0000-CKSS-roadmap.md`

## 0. Mission

Implement only the first two CKSS stages:

```text
CKSS-000  frontier consolidation
CKSS-001  common-kernel source API audit
```

Do not continue automatically to CKSS-002 or later stages.

The mathematical objective is not to add another Eta-tail estimate. ZDSS has already isolated the exact missing relation:

```text
same nontrivial zeta zero
  -> separately zero-derived original / critical-mirror endpoint sources
  -> exact endpoint rates
  -> raw common-scale horizontal power survives
  -> independent same-scale cross-endpoint coupling still missing
```

CKSS asks whether the completed-zeta functional-equation infrastructure exposes a genuinely common source object before the final reflection identity is formed.

The desired source, if it exists, must couple the original and reflected sides through the same source variable, measure/kernel, and scale.

No theorem equivalent to RH may be introduced as a provider.

## 1. Global orientation before editing

Before making changes, verify and report all of the following:

1. current branch is exactly `wip/RH-CFBRC-common-kernel-second-source-260820-v0`;
2. current HEAD and working tree status;
3. Lean toolchain from `lean/dk_math/lean-toolchain`;
4. the CKSS roadmap file above;
5. the current implementation of
   `DkMath.RH.CFBRC.ZeroDerivedSameScaleCrossEndpointCouplingAudit`;
6. the public import surface in `lean/dk_math/DkMath/RH.lean`.

Do not trust conversation summaries over repository contents.

At every stage keep this four-item orientation explicit in the report:

```text
global objective
current CKSS stage
load-bearing assumption/provider boundary
next unresolved Gap
```

If the work starts branching into unrelated Eta asymptotics, moving frames, prime-density estimates, or already-closed Gram routes, stop and return to this orientation.

## 2. Trusted Core — do not re-prove

Treat the following as established repository facts unless the current source contradicts them.

### 2.1 ZDSS-005 raw-ratio frontier

The module

`lean/dk_math/DkMath/RH/CFBRC/ZeroDerivedSameScaleCrossEndpointCouplingAudit.lean`

already proves the sharp common-scale frontier. Important declarations include:

```text
etaDualEndpointRawNormRatio_tendsto_atTop_of_centeredSigma_pos
etaDualEndpointRawNormRatio_tendsto_zero_of_centeredSigma_neg
EtaDualEndpointRawNormRatioFrequentlyBoundedAboveAt
EtaDualEndpointRawNormRatioEventuallyBoundedAwayFromZeroAt
centeredSigma_nonpos_of_rawNormRatio_frequently_boundedAbove
centeredSigma_nonneg_of_rawNormRatio_eventually_boundedAwayFromZero
re_eq_half_of_rawNormRatio_twoSided_comparability
re_eq_half_of_rawNormRatio_frequently_boundedAbove_at_zero_and_mirror
EtaDualEndpointRawNormRatioFrequentlyBoundedAboveOnZeros
riemannHypothesis_of_rawNormRatio_frequently_boundedAboveOnZeros
rawNormRatio_frequently_boundedAboveOnZeros_iff_riemannHypothesis
```

The final iff theorem is a firewall: a global frequent-upper provider is RH-equivalent. Do not construct a wrapper around this proposition and call it new source information.

### 2.2 Previous endpoint facts

The existing ZDSS modules already provide:

```text
endpoint source pair                  FOUND
endpoint positive scalar upper side  FOUND
exact individual endpoint rates      FOUND
raw common-scale dichotomy            FOUND
same-scale independent coupling       MISSING
```

Do not spend this branch refining endpoint-specific normalization or tail asymptotics.

### 2.3 DkReal completion

The shrinking-interval / DkReal uniqueness layer is already available and is intentionally inactive in CKSS-000/001.

Do not modify it.

## 3. CKSS-000 — frontier consolidation

### 3.1 Required source change

Audit `lean/dk_math/DkMath/RH.lean`.

At the time this instruction was written, the root file imports:

```text
DkMath.RH.CFBRC.ZeroDerivedPrimeCoordinateSourceRankAudit
DkMath.RH.CFBRC.ZeroDerivedDualEndpointPositiveScalarCoercivityAudit
DkMath.RH.CFBRC.ZeroDerivedDualTailRateNormalizedModeBridgeAudit
```

but does not yet publicly import:

```text
DkMath.RH.CFBRC.ZeroDerivedSameScaleCrossEndpointCouplingAudit
```

If that remains true in the current checkout, add exactly that import adjacent to the preceding ZDSS imports.

If another commit has already added it, do not duplicate it; record that CKSS-000 item as already satisfied.

No theorem statements in `DkMath.RH.lean` should be changed for CKSS-000.

### 3.2 Build verification

Use the repository's actual Lean environment. At minimum verify the focused module and root import surface, for example with the project's normal `lake env lean` / `lake build` workflow.

Required checks:

```text
ZeroDerivedSameScaleCrossEndpointCouplingAudit builds
DkMath.RH builds after the public import change
no new sorry / admit / axiom placeholders are introduced
```

Do not change the Lean toolchain merely to make this stage compile.

### 3.3 CKSS-000 report

Create:

`lean/dk_math/DkMath/RH/CFBRC/docs/wip/RH-CFBRC-common-kernel-second-source/0002-CKSS-000-frontier-consolidation-report.md`

Record:

- branch / HEAD used;
- exact import change or `already present` result;
- build commands and results;
- frontier ledger;
- explicit statement that no new RH mathematics was claimed.

Use the decision label:

```text
CKSS-000-FRONTIER-CONSOLIDATED
```

only if the public import and build checks pass.

## 4. CKSS-001 — source API audit

This is the main research task of this Codex run.

### 4.1 Question to answer

Determine which exact theorem(s) and definitions in the installed Mathlib version underlie the completed Riemann-zeta functional equation, and whether they expose an exact common source object before the final reflected equality.

The target is not merely a theorem of the schematic form

```text
completedZeta s = completedZeta (1 - s)
```

Such an equality may be only invertible transport and carries no new source rank by itself.

Instead search for a representation schematically resembling

```text
C(s) = integral W(x) * Phi(x,s) dx
```

or an exact split/paired representation in which, after centering

```text
s = 1/2 + delta + i*t,
```

both mirror amplitudes are present inside one source expression using the same integration/summation variable and the same normalization.

### 4.2 Inspect the installed source, not current Mathlib master

The repository toolchain is authoritative.

Inspect the actual `.lake/packages/mathlib/Mathlib/...` source corresponding to the pinned toolchain and dependency revision.

Priority families:

```text
NumberTheory / ZetaFunction / RiemannZeta
Hurwitz zeta even infrastructure
Mellin transform infrastructure
Jacobi theta / theta inversion infrastructure
completed zeta definitions and functional equations
Gamma / Mellin bridge definitions used by those theorems
```

Also audit existing DkMath source before adding anything new, especially:

```text
DkMath.Analysis.MellinQuadraticGramKernel
DkMath.RH.CFBRC.MellinCenteredMirrorAdapter
DkMath.RH.CFBRC.PascalCenteredXiMellinQuadraticRealizationBridge
DkMath.RH.CFBRC.PascalCenteredXiWeilMirrorDefectBridge
CosmicFormulaZeta* Mellin / Gram audit modules
```

The purpose of this cross-check is to prevent renaming an already-closed Gram or fixed-Xi representation route as a new source.

### 4.3 Required evidence ledger

For every serious candidate theorem, record:

```text
source file
exact declaration name
exact type / theorem statement
upstream definitions it depends on
whether the source object exists before reflection
whether original and mirror use the same source variable
whether the relation is invertible transport only
whether positivity is native or introduced only after squaring
whether the candidate duplicates an existing DkMath route
```

Do not classify from theorem names alone. Read definitions and proof dependencies far enough to identify the mathematical source.

### 4.4 Source-rank firewall

Reject a candidate as independent source if the second side is obtained only by any combination of:

```text
critical-mirror substitution
complex conjugation
nonzero scalar multiplication
functional-equation rewrite
invertible linear change of coordinates
endpoint pair post-processing
fixed-Xi defect representation
```

A useful common-kernel source must expose information prior to these transports.

### 4.5 Positivity-direction firewall

Do not claim progress merely because a positive quantity can be formed after the fact.

In particular, if zero-derived information gives only smallness of a whole oscillatory integral while positivity appears in a diagonal square/energy, check the inequality direction.

The route must stop if the only available general estimate has the shape

```text
norm(whole integral)^2 <= integral of pointwise norm-square
```

because smallness of the left side does not upper-control the positive energy on the right.

Never silently reverse Cauchy-Schwarz, triangle, Parseval/Bessel-type, or Gram inequalities.

### 4.6 No heuristic replacement

Do not invent or formalize a heuristic approximate functional equation merely because Mathlib lacks the desired exact common-kernel theorem.

Do not add axioms, assumptions, `sorry`, or an RH-equivalent source hypothesis.

An API gap is an acceptable and useful CKSS-001 result.

## 5. CKSS-001 implementation policy

Prefer an audit-first result over a large new formalization.

### Case A — exact common-kernel source found

Classify:

```text
COMMON-KERNEL-SOURCE-FOUND
```

Then create one focused Lean audit module only, tentatively:

`lean/dk_math/DkMath/RH/CFBRC/ZeroDerivedCommonKernelSourceApiAudit.lean`

The module should do only enough to:

1. import the exact source theorem;
2. expose the relevant source representation in DkMath naming;
3. prove exact type-correct access / centered rewriting facts;
4. document which part is genuinely common-source information;
5. stop before positivity/quadraticization.

Do not implement CKSS-002 factorization beyond the minimal access lemmas needed to establish the classification.

Add the module to `DkMath.RH` only if it contains a stable reusable theorem, not merely `#check` experiments.

### Case B — only final reflection transport exists

Classify:

```text
FUNCTIONAL-EQUATION-TRANSPORT-ONLY
```

Do not create a fake source module. A documentation report plus, if useful, a tiny compilation audit file is enough.

### Case C — lower source exists mathematically but is not exposed by current API

Classify:

```text
COMMON-KERNEL-API-GAP
```

Identify the smallest missing infrastructure theorem/definition and where it should live, but do not immediately implement a large Mathlib replacement in this run.

Distinguish clearly between:

```text
mathematical source absent
source present in dependency internals but inaccessible
source conceptually available but formal infrastructure missing
```

## 6. CKSS-001 report

Create:

`lean/dk_math/DkMath/RH/CFBRC/docs/wip/RH-CFBRC-common-kernel-second-source/0003-CKSS-001-common-kernel-source-api-audit-report.md`

The report must contain:

1. executive decision using exactly one primary classification;
2. exact Mathlib/DkMath declaration inventory;
3. dependency/source chain;
4. source-rank analysis;
5. positivity-direction analysis;
6. duplicate-route analysis against Mellin/Gram/fixed-Xi modules;
7. what was implemented in Lean, if anything;
8. build results;
9. smallest next unresolved Gap;
10. explicit recommendation whether CKSS-002 is authorized mathematically.

If the answer is not `COMMON-KERNEL-SOURCE-FOUND`, state explicitly:

```text
CKSS-002 MUST NOT START
```

## 7. Hard stop list

Stop the current line immediately if you find yourself doing any of the following:

```text
refining Eta endpoint tail asymptotics
adding higher tail terms
choosing new endpoint-specific normalizations
inventing subsequence/cofinal wrappers for the raw ratio
reopening moving-frame / positive-density residual estimates
reopening prime-side sign searches without new source rank
repackaging an existing Gram kernel
assuming a frequent raw-ratio bound
assuming fixed-Xi defect vanishing
adding a theorem whose provider is equivalent to RH
```

A named obstruction is a successful result when it closes a false route.

## 8. Build and quality requirements

Use focused builds during development and a root build for the final state.

Requirements:

```text
no sorry
no admit
no new axioms
no theorem renamed to overstate its information content
no hidden change of Lean/Mathlib version
no unrelated refactors
```

Run `#print axioms` for any new load-bearing theorem created in CKSS-001.

If a new Lean file is created, include the standard DkMath copyright header and a module-level comment explaining that it is an audit, not an RH proof.

## 9. Git discipline

Keep commits small and semantically separated where practical:

```text
1. CKSS-000 public import / consolidation
2. CKSS-001 audit implementation
3. CKSS-001 report / roadmap update
```

Do not merge into `develop`.

Push only to:

`wip/RH-CFBRC-common-kernel-second-source-260820-v0`

At completion report the final commit SHA(s), changed files, build commands/results, and primary CKSS-001 classification.

## 10. Success criterion for this run

The run is successful if it answers, with exact source evidence, the following question:

```text
Does the current pinned Mathlib/DkMath stack expose a genuinely independent completed-zeta common-kernel source before functional-equation transport?
```

The acceptable answers are exactly:

```text
COMMON-KERNEL-SOURCE-FOUND
FUNCTIONAL-EQUATION-TRANSPORT-ONLY
COMMON-KERNEL-API-GAP
```

Do not manufacture a fourth answer by weakening the meaning of `source`.
