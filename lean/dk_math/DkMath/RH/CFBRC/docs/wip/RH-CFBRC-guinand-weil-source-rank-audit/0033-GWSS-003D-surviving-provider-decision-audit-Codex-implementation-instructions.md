# GWSS-003D surviving-provider decision audit — Codex implementation instructions

Date: 2026-08-21

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`

## 0. Mission

Continue only from the verified GWSS-003C frontier.

Trusted state:

```text
GWSS-001 source rank                         CLOSED
GWSS-002 finite off-critical Mellin witness CLOSED
GWSS-003A finite arithmetic identity        FOUND
GWSS-003B universal complex-linear phase    NOGO
GWSS-003C first-order homogeneous norm      NOGO
current obstruction                         OFF-CRITICAL-SCALAR-HOMOGENEITY-OBSTRUCTION
```

The current branch was 31 commits ahead and 0 behind `develop` immediately before this instruction file was added. Reconfirm the exact HEAD and working-tree state before editing; the repository is the source of truth.

Implement only the next bounded decision stage:

```text
GWSS-003D-A  audit independent vanishing-scale / strictly-sublinear providers
GWSS-003D-B  audit restricted real/conjugation-compatible witness providers
GWSS-003D-C  audit nonlinear positivity / quadratic provider candidates
GWSS-003D-D  compare the surviving information content
GWSS-003D-E  select exactly one primary next-provider classification
```

This stage is an inventory/decision audit. It is not authorization to build a large new analytic theory.

Do not start:

```text
full classical Guinand--Weil theorem
full Weil positivity criterion
Li criterion
unproved T -> infinity passage
new zero-avoidance-height theory
new Xi growth theory
new source-rank family
new interpolation family
DkReal shrinking-window uniqueness
RiemannHypothesis deduction
```

## 1. Mandatory orientation before editing

Before any edit, report:

```text
current branch
current HEAD
working-tree status
Lean toolchain
0029 instructions read
0030 report read
0031 instructions read
0032 report read
PascalCenteredXiMellinOffCriticalWitnessAudit.lean read
PascalCenteredXiMellinWitnessArithmeticControlAudit.lean read
PascalCenteredXiMellinWitnessPhaseNoGoAudit.lean read
PascalCenteredXiMellinWitnessQuantitativeHomogeneityAudit.lean read
PascalCenteredXiMellinArithmeticSpecialization.lean read
PascalCenteredXiPrimeRightEdgeTransport.lean read
PascalCenteredXiExplicitFormulaHorizontalPairing.lean read
relevant existing conjugation / positivity modules inventoried
global objective
current GWSS stage
load-bearing provider boundary
next unresolved Gap
```

Global objective:

```text
zero configuration
  -> independent source
  -> off-critical detector
  -> arithmetic control
  -> centered-coordinate uniqueness
  -> RiemannHypothesis
```

Current stage:

```text
GWSS-003D
```

Load-bearing boundary:

```text
The existing GWSS-002 detector is a target-dependent finite Mellin witness.
GWSS-003C proved that its off-critical factor q0.im is an overall scalar of
that witness and therefore transports through every current linear finite
arithmetic term with the same first-order homogeneity.

Hence additional H1 norm/majorant estimates cannot recover q0.im = 0.
The next viable provider must add information that is not equivalent to the
same scalar rescaling.
```

Forbidden shortcuts:

```text
RH
classical Weil positivity imported as a black box
Li criterion
functional-equation reflection promoted to a new independent source
conjugation promoted to a new independent source
fixed-Xi zero-side identity repackaged as arithmetic control
unproved horizontal decay
unproved limit exchange
reverse triangle inequality
reverse Cauchy--Schwarz
reverse Parseval/Bessel/Gram arguments
assuming inverse-matrix conditioning
assuming q0.im is uniformly separated from zero
calling weight-only decay full Xi-weighted decay
calling X -> infinity prime convergence a vanishing theorem
```

## 2. The only three provider classes to audit

After GWSS-003C, do not branch into arbitrary estimates. Audit exactly these three classes.

```text
A. independent vanishing-scale / strictly-sublinear provider
B. restricted real/conjugation-compatible witness provider
C. genuinely nonlinear positivity / quadratic provider
```

The purpose is to determine which class is actually alive in the current DkMath API, not which class sounds promising informally.

## 3. GWSS-003D-A — independent vanishing-scale audit

### A1. Required semantic shape

A useful vanishing-scale provider must contain genuinely independent information of schematic form

```text
arithmeticQuantity(parameter, targetWitness) -> 0
```

while the corresponding off-critical detector remains fixed and nonzero, or at least decays at a strictly slower scale.

The useful information must not arise by rewriting the zero-side moment through the already-proved finite explicit formula.

A tiny generic contradiction lemma is allowed if useful, for example:

```text
fixed nonzero complex value
  + independent sequence converging to that value
  + same sequence converging to zero
  -> contradiction
```

Do not build a broad filter library merely for this marker.

### A2. Mandatory existing-provider audit

Audit the existing theorem surfaces carefully.

#### Mellin spectral factor as ε -> 0+

Existing C2 uses pointwise convergence

```text
centeredMellinSpectralWeight(centeredMellinBoxApprox ε, z) -> 1.
```

This is a nonvanishing/full-rank column-scaling fact. It is not a vanishing arithmetic provider.

Do not classify convergence to `1` as HS control.

#### Prime cutoff as X -> infinity

`PascalCenteredXiPrimeRightEdgeTransport.lean` and `PascalCenteredXiMellinArithmeticSpecialization.lean` provide finite-interval convergence of the prime cutoff to the ordinary-zeta right-edge integral / finite explicit-formula endpoint.

Audit the exact limit. If the limit is generally a nonzero right-edge integral or the already-known finite endpoint, classify this as convergence/representation, not vanishing.

Do not infer any `X -> infinity` smallness unless a theorem explicitly states convergence to `0` for the needed independent difference.

#### Horizontal height

`PascalCenteredXiExplicitFormulaHorizontalPairing.lean` explicitly separates weight-only decay from the full Xi-weighted horizontal integrand. It also records the fixed-window localization obstruction.

The existing provider structure

```text
PascalCenteredXiMellinWeightVerticalDecayProvider
```

contains only weight decay. Its existence, even if supplied, does not by itself prove decay of

```text
weight * pascalCenteredXiNegLogDeriv
```

or of the top-horizontal contribution.

Do not cross this boundary.

No `T -> infinity` passage is allowed under a fixed same-zero-set window unless the repository already contains the exact compatible theorem. If it does, cite the exact declaration and dependencies. Otherwise classify it as absent.

### A3. A-provider success criterion

Classify A as FOUND only if the repository already supplies, or a very small local bridge proves from existing unconditional theorems, an independent vanishing-scale statement compatible with the target witness and finite arithmetic surface.

The statement must be strong enough in principle to survive the GWSS-003C scalar-homogeneity normalization.

If no such theorem exists, record:

```text
independent vanishing-scale provider: NOT FOUND
```

Do not turn this audit into new Gamma/zeta-growth analysis.

## 4. GWSS-003D-B — restricted real/conjugation structure audit

GWSS-003B already defined

```lean
PascalCenteredXiConjugationRealWeight h
```

and proved that this real form is not closed under multiplication by `I`, except at zero. Thus it escapes the universal complex-linear phase no-go structurally.

The unresolved question is whether a useful off-critical detector survives inside such a restricted class.

### B1. Audit the actual zero-carrier conjugation API

Search the current repository for exact theorems establishing any of:

```text
1. centered-Xi zero closure under complex conjugation
2. finite zero-window closure under conjugation
3. multiplicity equality under conjugation
4. squared orbit q maps to conj(q)
5. squared-orbit mass equality between q and conj(q)
```

Do not assume these facts merely from classical zeta theory. Reuse existing theorems if present.

Conjugation is only a witness-class symmetry audit here. It is not an independent RH source.

### B2. Audit canonical Mellin basis conjugation compatibility

For real `ε` and `τ`, determine whether the current API proves

```text
H_{ε,τ}(conj z) = conj(H_{ε,τ}(z)).
```

or the exact equivalent predicate used in 003B.

Do not infer this only from real parameters. If the proof is a short consequence of existing exponential/integral conjugation theorems, a compact local bridge is allowed. If it requires a new integration/conjugation library, stop and record an API gap.

### B3. Audit synthesized coefficient structure

The target extractor coefficients come from `Matrix.nonsingInv` of an actual complex evaluation matrix.

Determine whether anything currently proves the coefficient vector is:

```text
real
conjugate-paired
fixed by an involution compatible with the actual carrier
```

Determinant nonvanishing alone is insufficient.

Do not add such a property as an assumption merely to keep the route alive.

### B4. Audit detector survival

If both `q` and `conj(q)` occur with conjugate/equal masses, determine what a conjugation-real weight can observe from their combined contribution.

The present single-orbit detector is proportional to

```text
q.im * mass(q).
```

Audit whether restricting to a real/conjugation-compatible class:

```text
preserves a nonzero antisymmetric off-critical observable,
or
forces conjugate-pair cancellation / loss of single-orbit isolation,
or
cannot be decided because the actual carrier/multiplicity API is missing.
```

A minimal finite abstract two-orbit model is allowed only to classify structural compatibility. Do not promote an abstract model to an actual zeta theorem.

### B5. B-provider outcomes

Legitimate outcomes include:

```text
REAL-STRUCTURE-DETECTOR-ROUTE-OPEN
REAL-STRUCTURE-DETECTOR-CANCELLATION-OBSTRUCTION
CONJUGATION-SYMMETRY-API-GAP
```

Use only what the repository proves.

## 5. GWSS-003D-C — nonlinear positivity / quadratic provider audit

This route is logically different from the closed H1 linear norm route.

### C1. Search only for genuinely independent nonlinear observables

Inventory existing CFBRC / RH modules for a theorem or structure resembling:

```text
positive quadratic form
normSq / energy identity with arithmetic-side meaning
positive kernel pairing
Gram-type positive observable
Weil-like test-function functional
sum of nonnegative prime-side contributions
```

The candidate must not be merely the norm of the same exact linear identity from GWSS-003C.

### C2. Strict rejection rules

Reject as a viable independent provider any candidate whose load-bearing proof is only:

```text
zero-side positivity rewritten through the explicit formula
fixed-Xi representation / rename
functional-equation reflection
reverse Cauchy--Schwarz / reverse triangle
an unproved sign of a complex arithmetic sum
an RH assumption
Li criterion
full classical Weil positivity theorem imported without local development
```

Do not use a quadratic notation to disguise an H1 norm estimate. If scaling by `q` merely produces `|q|^2` on both sides with no independent lower/upper asymmetry, note that the same information issue remains.

### C3. Minimal positivity fragment

If the repository already contains a genuinely independent nonlinear positivity theorem that could discriminate off-critical geometry, identify the smallest exact fragment needed.

The report must state:

```text
exact theorem / definition name
input weight class
arithmetic-side content
scaling behavior
why it is not the zero-side identity in disguise
what additional bridge to the current Mellin witness is still missing
whether using it would be RH-equivalent
```

Do not implement full Guinand--Weil or Weil criterion in this assignment.

If no such current theorem exists, distinguish:

```text
nonlinear positivity conceptually remains possible
```

from

```text
nonlinear positivity provider already exists
```

These are not the same conclusion.

## 6. GWSS-003D-D — compare information content

At the end of A/B/C, make a compact ledger.

Required rows:

```text
provider class
current exact theorem/API
independent of zeroMoment rewrite? yes/no
survives scalar-homogeneity obstruction? yes/no/unknown
compatible with synthesized witness? yes/no/gap
would require T -> infinity? yes/no
would require RH-equivalent input? yes/no/unknown
status
```

The purpose is to prevent route drift. Do not award a provider merely because many auxiliary lemmas exist.

### D1. Mandatory interpretation of existing routes

The following should remain explicit unless the repository genuinely changed them:

```text
H1 finite norm route: CLOSED by GWSS-003C
universal full complex-class phase route: CLOSED by GWSS-003B
finite prime vertical majorant: FOUND but H1-only
weight-only horizontal decay provider: insufficient for full horizontal term
fixed-window T -> infinity: not available automatically
```

## 7. GWSS-003D-E — choose exactly one primary classification

End with exactly one primary classification from:

```text
INDEPENDENT-VANISHING-SCALE-PROVIDER-FOUND
REAL-STRUCTURE-DETECTOR-ROUTE-OPEN
NONLINEAR-POSITIVITY-MINIMAL-PROVIDER-IDENTIFIED
NONLINEAR-POSITIVITY-PROVIDER-DECISION-REQUIRED
GWSS-003D-NO-SURVIVING-INDEPENDENT-PROVIDER
GWSS-003D-IMPLEMENTATION-API-GAP
```

Secondary findings may include:

```text
independent vanishing-scale provider: FOUND / NOT FOUND / API GAP
canonical Mellin conjugation-realness: FOUND / NOT FOUND / API GAP
actual zero-window conjugation symmetry: FOUND / NOT FOUND / API GAP
synthesized coefficient real structure: FOUND / NOT FOUND / API GAP
detector survival under real structure: FOUND / OBSTRUCTED / UNRESOLVED
independent nonlinear positivity: FOUND / NOT FOUND / RH-EQUIVALENT
```

Do not list several co-primary classifications.

## 8. GWSS-004 authorization rule

GWSS-004 remains unauthorized by default.

Authorize GWSS-004 only if GWSS-003D identifies a precise nonlinear/classical positivity fragment as the minimal surviving provider after the vanishing-scale and real-structure routes have been ruled out or bounded by exact API gaps.

Even then, GWSS-004 authorization means only a bounded decision/bridge audit. It does not authorize importing or proving the full Weil criterion.

If the primary result is:

```text
INDEPENDENT-VANISHING-SCALE-PROVIDER-FOUND
```

remain within GWSS-003 and name the exact next bridge.

If the primary result is:

```text
REAL-STRUCTURE-DETECTOR-ROUTE-OPEN
```

remain within GWSS-003 and name the exact real-structure arithmetic theorem needed next.

If the primary result is:

```text
NONLINEAR-POSITIVITY-MINIMAL-PROVIDER-IDENTIFIED
```

GWSS-004 may be authorized as the next bounded stage, with the exact identified fragment as its only target.

If the result is only:

```text
NONLINEAR-POSITIVITY-PROVIDER-DECISION-REQUIRED
```

GWSS-004 is not yet authorized; name what must be decided first.

## 9. Preferred focused Lean output

Prefer one small focused module:

```text
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessProviderDecisionAudit.lean
```

The module may contain only compact reusable facts needed to certify the provider ledger. An audit whose result is mostly negative may legitimately be short.

Do not create hundreds of lines of exploratory estimates merely to make the stage look substantial.

Required report:

```text
docs/wip/RH-CFBRC-guinand-weil-source-rank-audit/
0034-GWSS-003D-surviving-provider-decision-audit-report.md
```

The report is load-bearing. If a candidate is rejected, state the exact reason and theorem boundary.

## 10. Suggested tiny Lean certificates

Only if useful and cheap, formalize one or more of:

```text
1. a generic uniqueness-of-limit contradiction for fixed nonzero value versus zero
2. a small conjugation identity for squared coordinates
3. a finite two-coordinate conjugation-real cancellation model
4. a scaling sanity lemma showing a quadratic norm identity alone still carries |q|^2 homogeneity
```

These are decision certificates, not new provider families.

If they become larger than the audit itself, stop and record the missing API instead.

## 11. Mandatory report orientation

The 0034 report must state:

```text
global objective
current GWSS stage
branch and HEAD audited
load-bearing provider boundary
003C homogeneity obstruction status
A: vanishing-scale provider inventory and verdict
B: real/conjugation provider inventory and verdict
C: nonlinear positivity inventory and verdict
finite prime majorant status
top-horizontal status
provider comparison ledger
exact primary classification
secondary findings
next unresolved Gap
GWSS-004 authorization status
verification
```

## 12. Verification

At minimum run:

```text
lake build DkMath.RH.CFBRC.PascalCenteredXiMellinWitnessProviderDecisionAudit
git diff --check
```

Inspect `#print axioms` for every new load-bearing certificate theorem.

Requirements:

```text
NO sorry
NO admit
NO native_decide proof shortcut
NO new axiom
```

Expected axiom footprint remains:

```text
propext
Classical.choice
Quot.sound
```

Report any deviation.

## 13. Route-drift firewall

Stop the assignment if it begins expanding into any of:

```text
large Gamma estimates
large zeta growth theory
new arbitrary-height zero-avoidance construction
full Guinand--Weil explicit formula
full Weil criterion
Li coefficients
DkReal shrinking windows
new spectral operator theory
```

without first obtaining one of the exact classifications in Section 7.

The point of GWSS-003D is to decide which kind of genuinely new information can still survive the two proved no-go results: universal complex-linear phase no-go and off-critical scalar homogeneity obstruction.