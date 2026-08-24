# RH-CFBRC Finite Provider Frontier Roadmap

Date: 2026-08-25

Branch: `wip/RH-CFBRC-finite-provider-frontier-260825-v0`

Base: `develop` at `570a61c478b7a3aa5138fadbbe39e7b0f9e8ee22`

Strategy: `0000-FPF-strategy.md`

## 0. Starting state

FPF starts after the merged GWSS/H-series closeout.

Trusted current endpoint:

```text
actual canonical Mellin witness              READY
finite WholeSource representation            READY
finite arithmetic approximant                READY
actual shifted-energy polarization           READY
critical-mirror transport                    READY
paired 1-channel collapse                    READY
independent canonical P1 provider             MISSING
```

The roadmap is deliberately finite-first.  No stage is authorized to introduce an infinite-height or infinite-cutoff argument merely because a finite sign theorem is difficult.

## 1. Global target

For a canonical index `j`, let schematically

```text
c_j := pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R epsilon tau j
```

and define the existing target proposition conceptually by

```text
CanonicalP1(j) : E1-(c_j) <= E1+(c_j).
```

The existing API gives

```text
CanonicalP1(j)
  <-> 0 <= (WholeSource epsilon tau c_j W X).re.
```

FPF's job is to find a source-side provider for this proposition, not another equivalent formulation.

## 2. FPF-000 — current finite source provenance inventory

### Mission

Re-read the merged `develop` source tree and construct an exact provenance ledger for the real WholeSource channel of the canonical witness.

### Required modules

Inspect at least:

```text
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessGeneralTauSourceBridgeAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessShiftedEnergyDominanceAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessCriticalMirrorWholeSourceAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessCriticalMirrorShiftedEnergyAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessArithmeticControlAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiFiniteArithmeticExplicitFormula.lean
DkMath/RH/CFBRC/PascalCenteredXiPrimeSideQuadraticizationAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiPrimeSideWholeSurfaceEnergyAudit.lean
```

Also inspect the exact von-Mangoldt / finite-prime representation used by the current finite approximant.

### Questions

1. Can `WholeSource.re` be expanded exactly into named finite source components?
2. Can the finite approximant's relevant coordinate be expanded into prime-power, archimedean, elementary, and top-horizontal pieces without a limit?
3. Which terms are finite sums and which are interval integrals?
4. Which terms have termwise real sign information?
5. Which terms have only norm bounds?
6. Which pieces are linked by exact cancellation identities?
7. Is there already an overlooked finite source decomposition suitable for a cover/escape formulation?

### Deliverable

Prefer a report first.  Add Lean only if a missing exact decomposition adapter is small, canonical, and genuinely useful downstream.

### Gate classification

Choose one primary classification:

```text
FINITE-SOURCE-ATOMIZATION-AVAILABLE
FINITE-SOURCE-ATOMIZATION-ADAPTER-GAP
WHOLESOURCE-REMAINS-AGGREGATE-ONLY
```

Do not define source-cover structures before this gate closes.

## 3. FPF-001 — canonical real-channel normal form

Proceed only if FPF-000 finds or can close a usable finite atomization.

### Mission

Produce a canonical normal form for the real WholeSource channel or the equivalent imaginary coordinate of the finite arithmetic approximant.

The normal form should separate provenance classes such as:

```text
prime-power finite terms
archimedean corrections
elementary corrections
top-horizontal contribution
other finite residue/source corrections actually present in the API
```

Do not force the decomposition into these labels if the source tree uses a different exact partition.

### Required output

A theorem or small theorem family of the schematic form

```text
canonical real source channel
  = finite sum/source class A
  + finite sum/source class B
  + ...
```

with every term already defined or newly defined from exact existing expressions.

### Gate

```text
CANONICAL-REAL-SOURCE-NORMAL-FORM-CLOSED
NORMAL-FORM-NOT-FINITE-COMPATIBLE
NORMAL-FORM-INFORMATION-NEUTRAL
```

The third classification applies if the decomposition exists but exposes no new finite combinatorial/support structure beyond a restatement of the aggregate.

## 4. FPF-002 — bad-sign obstruction carrier

Proceed only after a nontrivial normal form.

### Mission

Study the negation of P1:

```text
(WholeSource ...).re < 0
```

or the exact order-negation corresponding to the current real channel.

Seek a finite necessary condition for this bad-sign state.

Preferred shape:

```text
not CanonicalP1(j)
  -> every candidate source escape is obstructed
```

or, if the mathematics supports it,

```text
not CanonicalP1(j) <-> SourceFullyCovered(j).
```

### Rules

- `SourceFullyCovered` must be derived from the actual finite atomization.
- It must not be defined as `not CanonicalP1` under another name.
- The cover relation must expose independently checkable finite source structure.
- No mirror theorem may appear in the definition of the provider.

### Gate

```text
BAD-SIGN-FINITE-COVER-NORMAL-FORM-FOUND
BAD-SIGN-COVER-RESTATEMENT-ONLY
NO-FINITE-COVER-CARRIER
```

If the second or third result holds, do not continue to incidence combinatorics.

## 5. FPF-003 — source escape frontier

Proceed only if FPF-002 produces a genuine cover relation.

### Mission

Define the complement/escape frontier and prove the provider boundary separately from provider existence.

Target shapes include:

```text
SourceEscape(j) -> CanonicalP1(j)
```

or ideally

```text
CanonicalP1(j) <-> SourceEscape(j).
```

This is analogous only in architecture to
`legendreConjecture_iff_squareAnchoredSupportEscape`.

### Critical distinction

A theorem

```text
CanonicalP1 <-> SourceEscape
```

is not a proof of P1 unless `SourceEscape` is independently established.

### Gate

```text
FINITE-P1-ESCAPE-FRONTIER-CLOSED
ESCAPE-IMPLIES-P1-ONLY
ESCAPE-FRONTIER-NOT-INDEPENDENT
```

## 6. FPF-004 — localized obstruction ledgers

Proceed only if a genuine finite escape/cover frontier exists.

### Mission

Localize the obstruction burden in the style of the Legendre finite incidence machinery, but only using RH source atoms actually established in FPF-001/002.

Potential ledger classes:

```text
obstruction depth per source atom
number of distinct obstruction directions
pairwise overlap count
higher overlap only if pair data is insufficient
finite support multiplicity
transpose / double-count identities
```

### Preferred theorem shapes

```text
sum over obstruction directions = sum of local multiplicities
pair-overlap count = sum over atoms of choose(localMultiplicity, 2)
local obstruction budget <= global obstruction budget
```

These shapes are references from `LocalizedObstruction`; they are not requirements if the RH source geometry differs.

### Gate

```text
LOCAL-OBSTRUCTION-LEDGER-CLOSED
LOCAL-LEDGER-HOMOGENEOUS-NO-GAIN
LOCAL-LEDGER-NOT-DEFINED
```

## 7. FPF-005 — finite escape existence / budget decision

Proceed only if FPF-004 yields a nontrivial finite ledger.

### Mission

Attempt to prove that complete obstruction is impossible for the canonical finite source configuration.

Possible mechanisms:

```text
strict cardinality deficit
strict weighted budget deficit
coprimality/residue incompatibility if such arithmetic structure genuinely appears
small residual/cofactor normal form if the prime-side atomization produces one
pair-overlap overload
incompatible simultaneous local constraints
```

Do not import the Legendre proof obligations themselves.  Only reuse a mechanism when the RH source has the corresponding exact finite structure.

### Success target

```text
SourceEscape(j)
```

from source-side finite hypotheses already available for the canonical witness.

### Gate

```text
INDEPENDENT-FINITE-P1-PROVIDER-FOUND
FINITE-COVER-PROVIDER-GAP
FINITE-PROVIDER-NO-GO
```

`FINITE-PROVIDER-NO-GO` is a valid endpoint and should close this route.

## 8. FPF-006 — mirror activation and detector-coupling audit

Proceed only after `INDEPENDENT-FINITE-P1-PROVIDER-FOUND`.

### Mission A — activate the already-proved H8 machinery

Apply the provider independently to both canonical endpoints `j` and `mirrorIndex j`.

Use existing H8, do not reprove mirror algebra.

Expected immediate consequence:

```text
paired canonical P1
  -> E1+(j) = E1-(j)
  -> (WholeSource ... c_j ...).re = 0.
```

### Mission B — audit coupling to the off-critical detector

Now ask a separate question:

```text
Does this real-source equality force the canonical off-critical detector scalar to vanish?
```

Do not assume the answer is yes.

Inventory exact existing bridges among:

```text
WholeSource real channel
finite arithmetic approximant
zero-side weighted moment
canonical detector scalar
q.im
canonical orbit mass
```

### Gate

```text
P1-COLLAPSE-COUPLES-TO-DETECTOR
P1-COLLAPSE-NEEDS-P2-P3
P1-COLLAPSE-INFORMATION-INSUFFICIENT
```

Only the first classification authorizes an off-critical exclusion theorem.

## 9. FPF-007 — off-critical exclusion decision

Proceed only after a successful detector-coupling gate.

### Mission

Construct the smallest theorem excluding a canonical off-critical target from the finite source/provider package.

No global RH theorem yet unless all quantifier/window/coverage requirements are already discharged.

### Gate

```text
FINITE-OFFCRITICAL-EXCLUSION-CLOSED
WINDOW-UNIFORMITY-GAP
GLOBALIZATION-GAP
```

## 10. FPF-008 — route closeout / next authorization

At the end of the route, produce one consolidated report containing:

```text
what new finite information was found
which provider theorem is genuinely independent
which old GWSS identities were reused
which Legendre ideas transferred structurally
which Legendre ideas did not transfer
whether P1 was proved
whether P1 couples to the detector
whether off-critical exclusion was reached
what exact next theorem is missing
```

No next RH branch should be authorized by momentum alone.

## 11. Immediate next action

The first implementation task is **FPF-000 only**.

Do not begin with new cover/support definitions.

First inventory the exact merged finite source decomposition on `develop` and decide whether `WholeSource.re` / finite-approximant `.im` already exposes a finite atomization suitable for a genuinely independent provider frontier.