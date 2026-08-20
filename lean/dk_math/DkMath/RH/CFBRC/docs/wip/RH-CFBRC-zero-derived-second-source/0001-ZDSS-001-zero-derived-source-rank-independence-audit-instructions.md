# ZDSS-001 — zero-derived source rank / independence audit instructions

Branch: `wip/RH-CFBRC-zero-derived-second-source-260820-v0`

Parent roadmap: `0000-RH-CFBRC-zero-derived-second-source-roadmap.md`

Depends on:

- `RH-CFBRC-zeta-dkreal-zero-interval/0023-ZDI-route-closeout-report.md`
- `RH-CFBRC-zeta-dkreal-zero-interval/0022-ZDI-011-prime-factor-coordinate-certificate-reentry-audit-report.md`
- `EtaCriticalMirrorPrimeFactorFiniteSourceBridge.lean`
- `EtaCriticalMirrorPrimeFactorCoercivityAudit.lean`
- `EtaCriticalMirrorPrimeFactorCoordinateCertificateReentryAudit.lean`

## 0. Purpose

Implement the first narrow audit of the new ZDSS route.

The task is **not** to prove RH, not to construct a positive energy immediately, and not to sharpen the old Eta estimate.

The task is to determine whether the same standard nontrivial zeta-zero hypothesis already supplies more than one genuinely independent finite zero-derived source after all exact symmetries and invertible transports are accounted for.

The result must answer:

```text
Does the available source family contain genuine information rank >= 2,
or is every currently available source only a duplicate transport of P2-F?
```

Do not introduce an abstract rank definition before the actual concrete source maps are aligned.

## 1. Fixed inherited facts

### 1.1 P2-F source

Retain the existing genuine zero-derived identity for nonreal nontrivial zeros:

```lean
etaPrimeFactorMirrorDefectPairedPartial K s
  = -etaCriticalMirrorDefectPairTail K s
```

This source has finite prime-factor provenance and converges to zero by ZDI-006.

### 1.2 Whole-sum firewall

Retain the ZDI-011 theorem

```lean
congrArg_of_etaPrimeFactorMirrorDefectPairedPartial_eq_etaDefect
```

and its zero-derived version.

Therefore the following do **not** count as new sources:

```text
norm of P2-F
norm-square of P2-F
real or imaginary projection of P2-F
unit rotation of P2-F
conjugation followed by known inverse
any function of the single whole P2-F value
```

Do not add a theorem merely restating this firewall under a new name unless it is required as a local helper for a more concrete source comparison.

### 1.3 Positive energy remains only a target

`primeMirrorEnergy`, `primeMirrorEnergyAt`, and aggregate mirror Gap may be imported only as candidate C-side objects if useful for classification.

ZDSS-001 must not assume or derive their zero-smallness by post-processing P2-F.

## 2. Repository audit before coding

Before creating a new Lean module, search the current branch / `develop` source tree for all declarations that transport a standard nontrivial zeta zero to another zero or to another finite Eta source.

At minimum inspect declarations related to:

```text
NontrivialRiemannZetaZero
criticalMirror
riemannZeta functional equation
completed zeta / Xi zero transport
complex conjugation
etaPairedValue / etaPairTerm
etaCriticalMirrorDefectPairTerm
etaCriticalMirrorDefectPairedPartial
etaPrimeFactorMirrorDefectPairedPartial
finite-plus-tail zero identities
consecutive-cutoff identities
```

Do not infer theorem names from memory. Use repository search and inspect exact types.

Create a short source ledger in the report containing:

```text
candidate name
exact theorem / definition
input hypotheses
finite object produced
whether the transport is invertible
dependence on P2-F
classification
```

## 3. Concrete source alignment

The first implementation goal is to place all viable source candidates on comparable concrete objects.

Preferred base object:

```lean
etaPrimeFactorMirrorDefectPairedPartial K s : ℂ
```

or, if the candidate naturally preserves separate endpoint data, an explicit finite pair such as

```text
(mirror endpoint partial, original endpoint partial)
```

using already existing definitions.

Do not create a new pair representation unless a characterization theorem immediately proves it equals existing source components.

For each candidate source `S₂`, prove the strongest available exact relation to the baseline `S₁`.

Examples of acceptable classifications:

### SAME

```lean
S₂ K s = S₁ K s
```

### SCALAR-DUPLICATE

```lean
S₂ K s = c K s * S₁ K s
```

with the scalar characterized and, if used to claim information equivalence, proved nonzero under the actual hypotheses.

### CONJUGATE-DUPLICATE

```lean
S₂ K s = conj (S₁ K s)
```

or an exact equivalent relation with an explicit inverse.

### MIRROR-DUPLICATE

The source at `criticalMirror s` is exactly recoverable from the source at `s` by already certified mirror/conjugate/sign transport.

### INVERTIBLE-TRANSPORT-DUPLICATE

There is an explicit invertible linear or algebraic transport between the two candidate source values with no additional zero-derived datum.

### GENUINELY-INDEPENDENT

Use this label only if the candidate cannot be reconstructed from the baseline by the certified source-free transports above and a concrete theorem exhibits extra zero-derived coordinate information.

### UNKNOWN-GAP

Use this when no equality/duplication theorem is known and genuine independence also cannot be proved. Do not silently promote UNKNOWN to INDEPENDENT.

## 4. Endpoint information audit

ZDI-011 already exposes the exact finite decomposition

```lean
etaPrimeFactorMirrorDefectPairedPartial K s
  = mirrorEndpointPartial K s - originalEndpointPartial K s.
```

Audit whether the standard zero hypothesis supplies separate zero-derived relations for the two endpoint pieces.

Required questions:

1. Is there an existing theorem giving a finite-plus-tail identity at `s` alone?
2. Is there an existing theorem giving a finite-plus-tail identity at `criticalMirror s` alone?
3. Are these two endpoint equations genuinely separate, or does one follow from the other by conjugation/mirror symmetry?
4. Do their tails provide two independently controlled complex coordinates, or only a rewritten difference identity?

If separate endpoint identities exist, expose them with thin theorems only if necessary and prove their exact dependence relation.

If no separate upper control exists, record that explicitly. Do not construct endpoint energies from uncontrolled components.

## 5. Critical-mirror / conjugation audit

Trace the exact definition of `criticalMirror` and all zero-preserving theorems involving it.

Determine whether evaluating the finite source at

```text
s
criticalMirror s
conj s
criticalMirror (conj s)
```

produces additional information or merely the same source under sign/conjugation/mirror transport.

The audit must distinguish:

```text
same-height critical mirror
functional reflection 1 - s
complex conjugation
completed-zeta symmetry
```

if these are distinct in the current codebase.

Do not identify them based on notation alone.

A useful Lean result is a small family of exact comparison theorems reducing these transformed sources to a canonical source whenever possible.

## 6. Functional-equation / completed-zeta audit

Inspect existing DkMath and Mathlib APIs that follow from a standard nontrivial zero without RH.

The goal is to determine whether functional-equation or completed-zeta zero transport yields a second finite arithmetic identity rather than merely another zero location.

Questions to answer:

1. Does a transported zero instantiate an already existing Eta finite-plus-tail theorem?
2. After rewriting by symmetry, is that finite identity algebraically determined by the original P2-F identity?
3. Does the coefficient/normalization introduce a known nonzero scalar only, or a genuinely new finite arithmetic piece?
4. Is any needed theorem conditional on an RH-equivalent frontier?

Do not add a new functional equation, approximate functional equation, derivative identity, or Xi construction in ZDSS-001.

This phase inventories existing exact source consequences only.

## 7. Multi-cutoff audit

The source identity is available at every cutoff `K`.

It is legitimate to compare

```text
P K
P (K + 1)
P (K + 2)
```

and exact differences.

However, classify these as additional information only if the zero hypothesis imposes a relation not already valid for arbitrary open-strip points.

Recovering an individual Eta pair term by subtraction does not by itself count as a second zero-derived source if the recovered term is simply its unconditional definition and decay.

If useful, prove a theorem showing that consecutive-cutoff subtraction recovers the corresponding source term, then state clearly whether this adds zero-specific information.

Do not restart block schedules, moving frames, or positive-density geometry.

## 8. Information-equivalence theorem policy

Do not over-formalize linear algebra unless necessary.

Prefer concrete theorems such as:

```lean
candidateSource_eq_baseline
candidateSource_eq_neg_baseline
candidateSource_eq_conj_baseline
candidateSource_eq_nonzeroScalar_mul_baseline
```

or explicit equivalences on a finite source pair.

Only introduce a reusable structure such as

```text
ZeroDerivedSourceTransport
SourceInformationEquiv
```

if at least two real candidate families require the same abstraction and every field has a meaning theorem.

Do not define

```text
sourceRank := 2
```

or any proposition whose constructor already assumes the desired independence.

## 9. Candidate new Lean module

Create a new module only if the repository audit yields concrete theorems worth preserving.

Preferred name:

```text
DkMath.RH.CFBRC.ZeroDerivedPrimeCoordinateSourceRankAudit
```

Suggested path:

```text
lean/dk_math/DkMath/RH/CFBRC/ZeroDerivedPrimeCoordinateSourceRankAudit.lean
```

The module should remain narrow. Expected contents:

```text
source comparison theorems
endpoint dependence theorems
mirror/conjugate dependence theorems
functional-equation source classification helpers
optional cutoff-difference theorem
one explicit final audit proposition/theorem if natural
```

Do not import unrelated growth-route, DkReal, or moving-frame modules.

If no new Lean theorem is needed because the existing declarations already settle the classification, produce only the report and do not create ceremonial code.

## 10. Decision gate

At the end of ZDSS-001, choose exactly one of the following outcomes.

### GATE-A — INDEPENDENT-SOURCE-FOUND

Use only if a concrete second finite source is certified to carry additional zero-derived information beyond invertible transports of P2-F.

The report must identify:

```text
S1
S2
common zero hypothesis
finite arithmetic provenance of both
exact reason S2 is not reconstructible from S1
next candidate positive scalar
```

Then ZDSS-002 may proceed directly to source-matched quadraticization if the source pair is already suitable, or to a narrow dual-source normalization step.

### GATE-B — RANK-ONE-CLOSED

Use if all currently available transformed sources reduce to P2-F information.

Record exact duplication theorems and stop. The next phase must seek a genuinely new finite source family, not another symmetry transform.

### GATE-C — UNKNOWN-SOURCE-GAP

Use if the repository lacks enough theorems to prove duplication or independence for the best candidate.

State the single smallest missing theorem needed to decide the rank question. Do not build quadratic energy on top of an UNKNOWN source pair.

## 11. Explicit forbidden work

ZDSS-001 must not:

```text
reopen ZDI-007..010
create a new positive-density schedule
sharpen the current Eta residual majorant
prove another whole-sum norm estimate
square mode coordinates and call the result zero-derived
assume primeMirrorEnergy -> 0
assume fixed Xi defect vanishing
introduce an RH-equivalent provider
create DkReal intervals
claim RH
invent an approximate functional equation API
introduce new shifted zeros or twisted L-functions without an existing source theorem
```

## 12. Certification requirements

For every new load-bearing theorem:

- prove from current repository source objects;
- preserve the exact standard-zero hypotheses;
- prove nonzero conditions for scalars used to claim invertibility;
- audit realizability / non-vacuity where applicable;
- run `#print axioms` on accepted theorems;
- reject `sorryAx`;
- run focused build of the new module;
- if `DkMath.RH.lean` is changed, run the public/root RH build;
- run `git diff --check`;
- do not weaken the namespace/import discipline merely to make proof search easier.

## 13. Deliverables

Produce:

1. `ZeroDerivedPrimeCoordinateSourceRankAudit.lean` only if concrete reusable Lean facts are found.
2. Add the module to the public `DkMath.RH` import surface only if it contains accepted reusable Core.
3. A report:

```text
0002-ZDSS-001-zero-derived-source-rank-independence-audit-report.md
```

containing:

- exact starting commit and branch;
- P2-F/Q2-F recap;
- source inventory table;
- endpoint source audit;
- mirror/conjugate audit;
- functional-equation/completed-zeta audit;
- multi-cutoff audit;
- exact duplication or independence theorems;
- axiom/build validation;
- one final classification:
  - `INDEPENDENT-SOURCE-FOUND`,
  - `RANK-ONE-CLOSED`, or
  - `UNKNOWN-SOURCE-GAP`;
- the single smallest next mathematical obligation.

Do not append ZDSS-002 implementation work in the same task.

## 14. Research interpretation

The core principle of this audit is:

```text
Two formulas are not two sources.
Two source values related by an invertible symmetry are still one information channel.
Only after genuine extra zero-derived information is certified may positivity be built from it.
```

This phase should be short. If the current source family is rank one, prove that cleanly and stop rather than growing another long branch.
