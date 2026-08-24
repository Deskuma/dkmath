# FPF-000 current finite source provenance inventory — Codex implementation instructions

Date: 2026-08-25
Branch: `wip/RH-CFBRC-finite-provider-frontier-260825-v0`
Base route documents:

```text
0000-FPF-strategy.md
0001-FPF-roadmap.md
```

Expected closeout report:

```text
0003-FPF-000-current-finite-source-provenance-inventory-report.md
```

## 0. Mission

FPF begins after the merged GWSS/H-series route closed the finite Mellin detector, actual general-`τ` source representation, critical-mirror transport, shifted-energy polarization, and paired-collapse mechanism, while leaving one load-bearing gap:

```text
independent finite canonical P1 provider: NOT FOUND
```

FPF-000 does **not** attempt to prove P1.

Its task is to determine exactly how much finite source structure is already exposed in the current `develop`-derived tree before introducing any new `cover`, `escape`, `obstruction`, `support`, or incidence-ledger abstraction.

For the exact synthesized canonical witness, determine whether the real WholeSource channel can already be atomized into named finite arithmetic/source contributions with sufficiently explicit provenance to support a later finite-provider frontier.

The target remains conceptually

```text
CanonicalP1(j):
  E1-(c_j) <= E1+(c_j)
```

with

```text
c_j := pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j
```

and the already proved readout

```text
CanonicalP1(j)
  <-> 0 <= (pascalCenteredXiMellinGeneralTauWitnessWholeSource ε τ c_j W X).re.
```

Do not prove or assume that sign in FPF-000.

## 1. Source of truth

Use the current branch and repository files as the source of truth.  Do not rely on historical conversation summaries when they disagree with the current tree.

Read at least the following current modules:

```text
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessGeneralTauSourceBridgeAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessShiftedEnergyDominanceAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessCriticalMirrorWholeSourceAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessCriticalMirrorShiftedEnergyAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessArithmeticControlAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiFiniteArithmeticExplicitFormula.lean
DkMath/RH/CFBRC/PascalCenteredXiPrimeRightEdgeTransport.lean
DkMath/RH/CFBRC/PascalCenteredXiPrimeSideQuadraticizationAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiPrimeSideWholeSurfaceEnergyAudit.lean
```

Inspect any directly imported module needed to resolve exact definitions or theorem hypotheses.

For methodological comparison only, read the following Legendre modules already present on `develop`:

```text
DkMath/NumberTheory/Legendre/Frontier.lean
DkMath/NumberTheory/Legendre/LocalizedObstruction.lean
DkMath/NumberTheory/Legendre/PacketUnitResidue.lean
DkMath/NumberTheory/Legendre/SmallCofactor.lean
```

Do **not** import Legendre modules into RH-CFBRC.  Their role is architectural only: provider/frontier separation, finite support localization, incidence ledgers, and exact distinction between a provider and an equivalence.

## 2. Trusted finite identities already present

Treat the following current API as trusted starting points, but verify their exact names and hypotheses in the current tree.

### 2.1 WholeSource definition

The actual general-`τ` source is assembled as

```text
WholeSource
  = VerticalSource - I * TopHorizontalContribution.
```

The current definition is

```text
pascalCenteredXiMellinGeneralTauWitnessWholeSource
```

with the corresponding finite whole-feature representation

```text
pascalCenteredXiMellinGeneralTauWitness_whole_source_eq_normalized_aggregate
```

for nonzero `τ` coordinates.

### 2.2 Finite arithmetic approximant

The current finite approximant is the exact four-term finite expression

```text
2 * PrimePowerRightEdgeCutoffIntegral
+ 2 * ArchimedeanRightEdgeIntegral
+ 2 * ElementaryRightEdgeIntegral
+ 2 * TopHorizontalContribution.
```

The definition is

```text
pascalCenteredXiFiniteArithmeticApproximant
```

and the explicit finite von-Mangoldt expansion is exposed by

```text
pascalCenteredXiFiniteArithmeticApproximant_eq_vonMangoldt_sum.
```

The cutoff `X` is finite throughout FPF-000.

### 2.3 Exact WholeSource/approximant orientation

The general-`τ` bridge proves

```text
pascalCenteredXiMellinFiniteArithmeticApproximant_eq_two_mul_I_mul_wholeSource
```

with exact finite shape

```text
FiniteApproximant = 2 * I * WholeSource.
```

Hence the relevant channels satisfy algebraically

```text
FiniteApproximant.im = 2 * WholeSource.re
FiniteApproximant.re = -2 * WholeSource.im.
```

Do not add duplicate wrappers unless a genuinely missing projection theorem is required downstream and cannot be handled cleanly by `simp`/`ring`/existing readout theorems.

### 2.4 Vertical ledger

The current source bridge already contains an arbitrary differentiable-weight vertical ledger and its synthesized-witness specialization:

```text
pascalCenteredXiMellinGeneralTau_vertical_source_ledger
pascalCenteredXiMellinGeneralTauWitness_vertical_source_ledger
```

This identifies the three retained right-edge finite terms

```text
prime cutoff
archimedean correction
elementary correction
```

with the oriented vertical source.

The top-horizontal term remains an explicit fourth finite source contribution.

## 3. FPF-000 audit questions

Answer all of the following from the current source tree.

### Q1. Exact real-channel atomization

Starting from

```text
WholeSource.re
```

or equivalently

```text
FiniteApproximant.im / 2,
```

can the relevant real channel be expanded **exactly and finitely** into named contributions corresponding to the current arithmetic source decomposition?

The preferred provenance partition is whatever the repository actually exposes.  It may be schematically

```text
prime-power cutoff contribution
archimedean contribution
elementary contribution
top-horizontal contribution
```

but do not force this partition if a more canonical exact decomposition exists.

Record the exact theorem chain.

### Q2. Prime-power atomization depth

The theorem

```text
pascalCenteredXiFiniteArithmeticApproximant_eq_vonMangoldt_sum
```

expands the prime cutoff into a finite sum over `Finset.range (X + 1)` of interval integrals involving `ArithmeticFunction.vonMangoldt n`.

Determine whether the current API goes further and exposes any of the following without new limit arguments:

```text
termwise real/imaginary coordinate formula
prime-power-only indexing
prime-vs-prime-power support classification
termwise sign theorem
finite support/disjointness theorem
finite cancellation theorem between distinct n terms
```

If not present, state exactly where atomization stops.

### Q3. Sign inventory

For every exact finite source component found in Q1/Q2, classify its current sign information separately:

```text
TERM-WISE-SIGN-FOUND
AGGREGATE-SIGN-FOUND
NORM-BOUND-ONLY
IDENTITY-ONLY
NO-SIGN-API
```

Do not infer sign from positivity of a norm unless the target component itself is that nonnegative norm.

Do not infer order between two nonnegative shifted energies.

### Q4. Cancellation inventory

Identify exact current cancellation/recombination identities between source components.

Distinguish carefully between:

```text
algebraic recombination
orientation identity
conjugation/mirror transport
true source-side cancellation with sign content
```

A theorem that merely rewrites four terms as `2 * I * WholeSource` is representation, not a sign provider.

### Q5. Canonical-witness specialization

Check which exact source decomposition theorems apply directly to

```text
pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j
```

under the standard hypotheses

```text
hε : 0 < ε
hτ : ∀ i, τ i ≠ 0
hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0.
```

If a theorem is stated for arbitrary differentiable/even `h`, record the exact existing theorem that discharges those hypotheses for the synthesized canonical witness.

Do not construct a second canonical witness API.

### Q6. Finite-provider suitability

Based only on existing exact finite identities, decide whether there is a natural non-metaphorical candidate carrier for a later `cover/escape` formulation.

A candidate is suitable only if its elements correspond to actual source atoms, obstruction directions, or finite incidences already visible in the formula.

Examples of acceptable evidence would be:

```text
finite indexed source atoms
finite support sets
finite divisibility/incidence data
finite sign-obstruction classes
finite pair-overlap structure
```

Pure interval points, arbitrary decomposition choices, or invented labels do not count as a finite carrier.

### Q7. First genuine adapter gap

If the current tree nearly exposes a useful finite atomization but lacks one small canonical adapter, identify the **first** missing theorem only.

Examples:

```text
imaginary coordinate of the four-term approximant equals the sum of the four imaginary coordinates
canonical witness specialization of an already arbitrary-weight decomposition
finite von-Mangoldt source term packaged as a named Finset function
```

Do not implement a large abstraction layer in FPF-000.

## 4. Implementation policy

FPF-000 is inventory-first.

### Case A — report-only

If the current API already exposes enough exact finite decomposition to answer Q1–Q7, add **no Lean module**.  Produce only the closeout report.

This is the preferred result when no missing adapter is mathematically necessary.

### Case B — one focused adapter module

If one small canonical decomposition adapter is genuinely missing and materially improves the provenance audit, add exactly one focused module, suggested name:

```text
DkMath/RH/CFBRC/PascalCenteredXiFiniteProviderSourceAtomizationAudit.lean
```

The module may contain only exact finite decomposition/projection adapters.

It must not define `cover`, `escape`, `obstruction`, `support`, `seat`, `budget`, or a P1 provider.

Do not modify upstream theorem statements unless required to repair an actual compile/API defect.

### Case C — aggregate-only closeout

If the current source cannot be atomized beyond aggregate interval-integral expressions in a provenance-preserving way, do not manufacture atoms.  Report

```text
WHOLESOURCE-REMAINS-AGGREGATE-ONLY
```

and stop FPF-001 authorization.

## 5. Forbidden shortcuts and firewalls

FPF-000 must obey all of the following.

1. **No P1 assumption or proof.**
   Do not assume or prove `0 <= WholeSource.re`.

2. **No RH-equivalent provider.**
   No RiemannHypothesis assumption, Weil positivity criterion, Li criterion, or equivalent raw-ratio/zero-exclusion theorem.

3. **No mirror-as-provider.**
   Critical mirror transport is already closed and is dependent information.

4. **No P0-to-P1 jump.**
   Nonnegativity of shifted norm-square energies does not order them.

5. **No limit route.**
   No `X -> ∞`, `T -> ∞`, `ε -> 0`, exchange of limits, dominated convergence, or horizontal-decay completion for provider purposes.
   Existing limit theorems may be inventoried historically, but they are not admissible FPF-000 providers.

6. **No zero-side rewrite counted as independence.**
   Rewriting the source through the zero moment or detector does not create independent provenance.

7. **No Legendre theorem import.**
   Legendre is a design reference only.

8. **No metaphor-only carrier.**
   Do not define `cover`, `escape`, or `support` unless FPF-000 first proves that actual finite source atoms support such a definition.  In practice FPF-000 itself should not define them.

9. **No new axioms or placeholders.**
   No `sorry`, `admit`, `native_decide`, or new axiom.

10. **Do not reopen closed GWSS/H routes.**
    Do not add new mirror wrappers, individual-energy mirror identities, or alternate coefficient conjugation packages unless required to repair a concrete source-decomposition gap.

## 6. Required report structure

Create

```text
DkMath/RH/CFBRC/docs/wip/RH-CFBRC-finite-provider-frontier/0003-FPF-000-current-finite-source-provenance-inventory-report.md
```

The report must contain at least:

### 6.1 Repository state

Record branch, starting HEAD, and whether any Lean file was added.

### 6.2 Exact source ledger

Give the exact current finite chain from canonical witness to WholeSource and finite approximant.

Include theorem names, not only schematic equations.

### 6.3 Atomization table

For each source class, record:

```text
component
exact declaration/theorem
finite index/carrier, if any
current sign information
current norm/majorant information
cancellation/recombination role
canonical-witness compatibility
```

### 6.4 Prime/von-Mangoldt depth

State exactly how far the current finite prime source is decomposed and where the API stops.

### 6.5 Sign provenance ledger

Explicitly identify whether any component already carries source-side one-sided sign information relevant to `WholeSource.re`.

If none does, say so directly.

### 6.6 Legendre architecture comparison

Briefly compare the current RH source structure to the Legendre `Frontier` architecture.

State only architectural correspondences actually supported by the current RH source API.

Do not claim that RH already has a cover/escape theorem.

### 6.7 First missing interface

Name the smallest genuine missing interface needed for FPF-001, or state that FPF-001 can proceed using existing APIs.

### 6.8 Classification

Choose exactly one primary classification:

```text
FINITE-SOURCE-ATOMIZATION-AVAILABLE
FINITE-SOURCE-ATOMIZATION-ADAPTER-GAP
WHOLESOURCE-REMAINS-AGGREGATE-ONLY
```

Secondary findings may include, when justified:

```text
FINITE-VON-MANGOLDT-INDEX-CARRIER-AVAILABLE
PRIME-SOURCE-TERM-SIGN-NOT-FOUND
CORRECTION-TERM-SIGN-NOT-FOUND
TOP-HORIZONTAL-SIGN-NOT-FOUND
FINITE-REPRESENTATION-NOT-P1
LEGENDRE-STYLE-COVER-CARRIER-NOT-YET-JUSTIFIED
```

### 6.9 Next authorization

Authorize FPF-001 only if the classification supplies a usable exact finite normal-form route.

Do not authorize FPF-002 or any cover/escape definition directly from FPF-000.

## 7. Verification

If FPF-000 is report-only, run at least the existing focused checks needed to verify the load-bearing current modules still compile, for example:

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessGeneralTauSourceBridgeAudit.lean
lake env lean DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessShiftedEnergyDominanceAudit.lean
git diff --check
```

If a focused adapter module is added, also run:

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiFiniteProviderSourceAtomizationAudit.lean
lake build DkMath.RH.CFBRC.PascalCenteredXiFiniteProviderSourceAtomizationAudit
git diff --check
```

Run `#print axioms` on every new load-bearing theorem.  Expected footprint is at most the existing baseline:

```text
[propext, Classical.choice, Quot.sound]
```

The closeout report must distinguish local focused verification from CI.  Do not claim CI, PR, or downstream FPF stages unless actually performed.

## 8. Success criterion

FPF-000 succeeds when the next stage no longer has to ask vaguely what `WholeSource.re` is made of.

A successful closeout must produce one of two useful outcomes:

```text
A. exact finite provenance atoms are available and FPF-001 can normalize them;
```

or

```text
B. the current representation remains too aggregate for a genuine finite-provider frontier, and the first missing adapter is precisely identified.
```

Either outcome is progress.  Do not manufacture a P1 provider in order to avoid the second classification.
