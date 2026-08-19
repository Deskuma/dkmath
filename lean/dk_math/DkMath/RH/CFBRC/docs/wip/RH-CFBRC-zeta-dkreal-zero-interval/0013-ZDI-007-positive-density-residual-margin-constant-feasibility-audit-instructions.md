# ZDI-007 — positive-density residual/margin constant feasibility audit instructions

Branch: `wip/RH-CFBRC-zeta-dkreal-zero-interval-260819-v0`

Parent roadmap: `0000-RH-CFBRC-zeta-dkreal-zero-interval-roadmap.md`

Depends on:

- `0010-ZDI-005-eta-prime-factor-finite-source-bridge-report.md`
- `0012-ZDI-006-P2F-coercivity-cancellation-feasibility-audit-report.md`

## Goal

Resolve the smallest concrete live branch left by ZDI-006 before introducing any abstract global no-cancellation or coercivity provider.

ZDI-006 established that:

- P2-F is an exact prime-factor re-encoding of the existing Eta finite partial, so it does not itself add no-cancellation rigidity;
- the Q2-F power majorant tends to zero;
- the actual Eta tail norm tends to zero;
- the P2-F finite source norm tends to zero at a nonreal nontrivial zeta zero;
- for sublinear growing-block schedules, the currently available residual-tail majorant and block-margin lower bound have incompatible asymptotic rates for proving residual domination;
- for positive-density schedules, the rates are balanced, but strict constant domination has not been proved.

The present task is therefore a **constant-feasibility audit for an explicit positive-density schedule**.

Do not start by postulating a generic `GlobalLowerBound`, `NoCancellation`, `Coercive`, `Dominated`, `PositiveEnergy`, or RH-closing provider. First determine whether the existing explicit formulas already settle the positive-density case.

## Global RH boundary

The final standard target remains Mathlib `RiemannHypothesis`.

The already audited CFBRC geometry proves the critical-line zero locus. The missing mathematical content is still the standard-zeta-zero forcing step.

A theorem that excludes every off-critical `NontrivialRiemannZetaZero` is an RH-closing theorem. Such a theorem is allowed only if its proof contains genuinely independent mathematics; it must not be introduced as an assumed structure field or newly named predicate.

## Mandatory distinction from ZDI-006 obstruction

Preserve the following distinction in both code and report.

For a sublinear schedule, ZDI-006 found an obstruction for the **current proof route using the explicit residual upper majorant and explicit block-margin lower bound**. It did not prove that the exact residual tail can never be dominated by the exact block margin.

Do not upgrade this proof-route obstruction into an unconditional mathematical impossibility claim.

Similarly, positive-density rate balance is only a feasibility signal. Matching exponents do not prove the required strict inequality; constants must be audited.

## Preferred first schedule

Begin with the simplest explicit positive-density choice compatible with the existing block-start geometry. Prefer

```text
N(K) = K
```

or the closest Lean-friendly schedule already represented in the repository.

Only generalize to

```text
N(K) approximately c * K
```

if the `N(K) = K` case reveals a genuine reason that a density parameter is necessary.

Before using an existing schedule structure, prove or cite all of its required fields. If a new schedule definition is introduced, immediately provide characterization and realizability theorems. Do not assume a schedule field merely because it would make the desired inequality true.

## Exact objects to compare

Trace the primitive definitions and proved bounds for at least:

```lean
etaCriticalMirrorDefectPairTailPowerBound
etaCriticalMirrorBlockStartResidualTailPowerBound
etaCriticalMirrorRightPairMargin
etaCriticalMirrorLeftPairMargin
etaCriticalMirrorRightBlockMarginSum
etaCriticalMirrorLeftBlockMarginSum
EtaPairGrowingBlockSchedule.RightResidualTailDominated
EtaPairGrowingBlockSchedule.LeftResidualTailDominated
```

Use the exact repository definitions rather than an asymptotic paraphrase when proving Lean statements.

The target inequalities are the existing load-bearing shapes:

```text
etaCriticalMirrorBlockStartResidualTailPowerBound s K N(K)
  < (1 / 2) * etaCriticalMirrorRightBlockMarginSum s K N(K)
```

for the right side, and

```text
etaCriticalMirrorBlockStartResidualTailPowerBound s K N(K)
  < (1 / 2) * etaCriticalMirrorLeftBlockMarginSum s K N(K)
```

for the left side.

Audit the right and left sides separately.

## Do not begin from a hypothetical zero

Wherever possible, perform the constant comparison for a general complex point `s` satisfying explicit strip and nonreal hypotheses such as

```text
0 < s.re
s.re < 1
s.im != 0
```

plus the appropriate side condition

```text
1 / 2 < s.re
```

or

```text
s.re < 1 / 2.
```

Do not assume that an off-critical `NontrivialRiemannZetaZero s` is realizable. That existence is precisely what RH denies.

Only attach the zero hypothesis at the final interface if an already audited zero-derived tail equality is actually required.

This separation is mandatory for avoiding vacuity.

## Constant extraction

For the explicit positive-density schedule, reduce the residual/margin comparison to elementary inequalities as far as possible.

The report must identify:

1. the exact decay exponent of every residual-majorant term;
2. the exact or proved lower-bound contribution of the block margin;
3. the normalized constants after the common power of `K` is removed;
4. every dependence on `s.re`, `|s.im|`, `‖s‖`, and `‖criticalMirror s‖`;
5. whether one residual component is asymptotically negligible relative to the matching slow component;
6. whether the remaining strict inequality is uniform on an off-critical side, pointwise in `s`, or false under the current bounds.

Prefer exact inequalities over informal `O(...)` notation in Lean. Asymptotic notation may be used in the report only after the exact formulas are stated.

## Margin lower-bound discipline

Do not infer a block lower bound merely because each pair margin is positive.

A positive sum can still be too small compared with the residual majorant. Any useful lower bound must retain the correct dependence on block length and on `s.re`.

If the existing integral definitions admit direct monotonicity or interval-integral estimates, derive those explicitly.

Do not replace the exact margin by an arbitrarily chosen smaller expression unless the inequality from the primitive margin to that expression is Lean-proved.

## Residual upper-bound discipline

The present task audits the existing explicit residual **majorant**, not the exact residual tail unless a stronger exact estimate falls out naturally.

If the power majorant is too coarse for constant domination, say so explicitly. Distinguish:

```text
exact domination may still be possible
```

from

```text
the current majorant cannot prove it.
```

If one can prove that the current majorant is intrinsically too large compared with every lower bound available from the current margin estimates, classify that as a bound-route obstruction, not as a theorem about the exact tail.

## Fixed-frame compatibility

Any positive-density schedule must still satisfy every geometric condition used to transport local pair signs into one block-start frame.

In particular, audit compatibility with the hypotheses behind:

```text
EtaPairGrowingBlockSchedule
etaPairFrameBlockSpan
```

and the growing-block quantitative certificate.

Do not sacrifice shrinking frame-span control in order to make the block longer. If `N(K) = K` violates the existing relative-length-to-zero requirement, record that immediately.

This is a critical branch point:

- if positive density is incompatible with the existing `EtaPairGrowingBlockSchedule`, then the rate-balanced candidate cannot be plugged into the old block-start theorem without new geometry;
- if a different fixed-frame theorem supports positive density, identify and audit it;
- otherwise classify the route as structurally blocked rather than silently changing the schedule contract.

## Important anticipated consistency check

ZDI-006 described positive-density schedules as rate-balanced. The existing `EtaPairGrowingBlockSchedule` definition may require

```text
blockLength K / etaPairFrameLeftEndpoint K -> 0.
```

Since `etaPairFrameLeftEndpoint K` is linear in `K`, a genuinely positive-density choice `blockLength K` proportional to `K` would not satisfy such a sublinear relative-length condition.

Therefore the first implementation task is to verify this compatibility directly from the actual definitions.

If positive density is incompatible with the schedule type, do not construct an impossible instance and do not introduce contradictory hypotheses. Instead:

1. formalize the incompatibility if a small clean theorem is available;
2. identify exactly which prior block-start estimate uses the relative-length-to-zero field;
3. determine whether a weaker bounded-relative-span geometry could replace it without assuming the desired conclusion.

This compatibility audit takes priority over constant algebra.

## Candidate outcomes

Classify the result into one of the following:

- **C2-CONSTANT** — an explicit independently realizable schedule and existing primitive estimates prove strict residual/margin domination without RH-equivalent assumptions;
- **C1-CONSTANT** — the comparison is reduced to one explicit elementary constant inequality whose truth is not yet proved;
- **O-SCHEDULE** — positive density is incompatible with the current growing-block schedule or fixed-frame transport contract;
- **O-BOUND** — the current explicit residual majorant and available margin lower bound cannot yield strict domination, even though exact-tail domination is not ruled out;
- **RED** — the only surviving hypothesis is equivalent to off-critical exclusion / RH or simply names the missing domination conclusion;
- **UNTRUSTED** — the candidate requires `sorryAx`, an unsupported semantic identification, or an excluded provider.

Do not count a newly defined predicate as C2-CONSTANT.

## If positive density is schedule-incompatible

If the audit returns **O-SCHEDULE**, do not immediately invent a new moving-frame architecture.

Instead report the smallest precise geometry obligation needed to permit a block of length comparable to `K` while retaining a single globally useful projection.

Possible forms to investigate only at the audit level include:

```text
bounded frame span instead of frame span -> 0
```

or a truly fixed real-linear functional whose sign does not rotate with `K`.

Do not implement a long replacement geometry chain in ZDI-007.

## If constants remain C1

If the schedule is realizable and the comparison becomes one elementary inequality in the parameters of `s`, isolate that inequality as the single next obligation.

Before proposing it for ZDI-008, test whether it is even plausible across both off-critical sides. A numerical sanity check may be reported as heuristic evidence, but it is not Lean proof and must be clearly labeled as such.

Do not tune a free parameter after seeing `s` unless that dependency is explicitly allowed and independently realizable in the schedule construction.

## No generic global lower-bound provider yet

ZDI-006 recommended an independent global lower bound / no-cancellation theorem conceptually. That remains the likely ultimate need, but ZDI-007 must not package it abstractly yet.

Reason: any theorem of the form

```text
off-critical standard zero -> positive global lower bound
```

combined with the zero-derived vanishing source may already contain the entire RH-closing mathematics.

First exhaust the concrete explicit positive-density constant route. Only if this route is certified blocked should a later task formulate a new global observable, and then its provenance and RH-equivalence must be audited before implementation.

## Allowed implementation

A small Lean audit module may be created if it proves one or more of the following without circular assumptions:

- the explicit `N(K) = K` schedule is incompatible with the current `EtaPairGrowingBlockSchedule` fields;
- a generic positive-density lower bound on `blockLength K / etaPairFrameLeftEndpoint K` contradicts the required limit to zero;
- an exact elementary lower bound for one block margin;
- an exact normalized residual upper bound;
- a clean reduction of residual domination to one elementary parameter inequality.

Documentation-only completion is acceptable if the existing definitions already settle the feasibility question and no new theorem adds useful certification.

Every new public `def` must have an immediate characterization theorem and realizability audit.

## Required report

Create:

`0014-ZDI-007-positive-density-residual-margin-constant-feasibility-audit-report.md`

The report must contain:

1. exact positive-density schedule candidate;
2. schedule realizability / compatibility with the existing growing-block type;
3. exact right-side residual and margin formulas or certified bounds;
4. exact left-side residual and margin formulas or certified bounds;
5. normalized rate and constant comparison;
6. distinction between exact tail and current residual majorant;
7. candidate classification as C2-CONSTANT / C1-CONSTANT / O-SCHEDULE / O-BOUND / RED / UNTRUSTED;
8. any new Lean theorem and its axiom audit;
9. whether the global RH frontier has actually moved;
10. exactly one smallest next obligation for ZDI-008, or a stop recommendation.

## Verification

For every changed Lean module, run the narrowest relevant `./lean-build.sh` target.

Run `#print axioms` on every theorem promoted as a load-bearing feasibility, obstruction, or constant-reduction fact.

Run `git diff --check`.

Do not add `sorry`.

## Completion condition

ZDI-007 is complete when the repository has a mechanically grounded answer to this question:

> Can a realizable positive-density block, under the actual existing fixed-frame geometry, make the explicit residual-tail majorant strictly smaller than the explicit off-critical block margin; or is the apparent rate balance unusable because of schedule incompatibility, constants, or bound coarseness?

Do not proceed to a generic no-cancellation theorem until this concrete question is resolved.