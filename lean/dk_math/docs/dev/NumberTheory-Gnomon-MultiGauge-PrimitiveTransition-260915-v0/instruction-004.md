# GMPT-004 — Petal-path turnover capacity audit

## Branch

```text
wip/number-theory-gnomon-multigauge-primitive-transition-260915-v0
```

## Status entering this task

GMPT-000 through GMPT-003 are implemented and focused-build validated.

Available production ingredients include:

```text
DkMath.Gnomon.PetalPrime
DkMath.NumberTheory.MultiGauge.GnomonPetalTransition
DkMath.NumberTheory.MultiGauge.GnomonPetalPath
DkMath.NumberTheory.Legendre.GnomonSupportTurnover
DkMath.NumberTheory.Legendre.GnomonPetalTurnover
```

In particular, for the canonical finite Petal path, the endpoint observer is

```text
oddGnomon (petalFold a bs)
  = oddGnomon a * (bs.map oddGnomon).prod
```

and every prime newly captured after start escape is localized to an actual input factor `b ∈ bs`.

The adjacent-shell lower-turnover theorem already gives the exact one-step criterion

```text
common lower support
<->
old support and q | oddGnomon n.
```

For `n = petalMul a b`, GMPT-001 refines this to the exact two-factor split.

The current Legendre full-cover frontier is still expressed through the existing parity-safe incidence/capacity ledger, e.g. `ParitySafeFullCoverCapacityFrontier.lean`.  No Petal-path term has yet produced a strict cardinality improvement there.

## Objective

Determine whether the finite Petal primitive-transition path yields a **strict quantitative/cardinality improvement** to the existing Legendre support-turnover / full-cover capacity frontier.

This is an audit first, not an implementation-by-default task.

Allowed outcomes:

```text
Outcome A — strict gain found and formalized
Outcome B — only structural normalization / no strict gain
Outcome P — promising but one explicit provider/inequality remains missing
```

Do not manufacture a new capacity API if the result merely restates divisibility through a product factorization.

## Phase 1 — exact path-to-turnover consequences

For an endpoint address

```text
n = petalFold a bs
```

combine

```text
oddGnomon n = oddGnomon a * (bs.map oddGnomon).prod
```

with `mem_reindexed_primeSupport_inter_lower_iff`.

Determine the strongest exact theorem available without new hypotheses.  Candidate shape:

```text
q ∈ lowerCommonSupport n r
<->
q ∈ oldSupport n r ∧
  (q ∣ oddGnomon a ∨ ∃ b ∈ bs, q ∣ oddGnomon b)
```

for prime `q`, with the correct existing support expressions rather than introducing a duplicate `lowerCommonSupport` unless it materially simplifies repeated statements.

If start-factor avoidance is assumed, derive localization entirely to an actual `b ∈ bs`.

This phase is deterministic and may be formalized if useful.

## Phase 2 — cardinality test

Ask whether the path decomposition gives a bound on the lower common-support cardinality that is **strictly stronger** than filtering by divisors of `oddGnomon n`.

Possible objects to compare:

```text
(squareOffsetPrimeSupport n r).filter (fun q => q ∣ oddGnomon n)
```

versus a union/sum of factor-local support channels associated with

```text
oddGnomon a
oddGnomon b,  b ∈ bs.
```

A plain union bound such as

```text
card common ≤ sum of factor-support cards
```

is not sufficient if it is only a weaker or equivalent restatement of prime divisibility of the product.

For any proposed quantitative theorem, explicitly show one of:

- a strict smaller RHS under a natural production hypothesis;
- a deleted support channel;
- a non-overlap/disjointness theorem that reduces a previous capacity term;
- a new injection that lowers an existing full-cover capacity bound;
- a concrete regression family where the new bound is strictly sharper than the pre-GMPT bound.

Without one of these, classify the result as structural only.

## Phase 3 — atomic endpoint test

Use

```text
prime_oddGnomon_iff_petalAtom
```

and the already existing theorem

```text
disjoint_reindexed_primeSupport_lower_of_prime_oddGnomon
```

to determine whether Petal atomicity yields anything quantitatively new beyond the existing lower disjointness theorem.

Expected caution:

```text
PetalAtom n
<-> Prime (oddGnomon n)
```

may merely repackage the hypothesis of an already-proved disjointness theorem.  If so, record that as normalization, not as a capacity gain.

Check whether the path language adds a genuinely stronger statement, for example by ruling out a family of composite endpoint decompositions or forcing mutually disjoint factor channels.  Do not assume such disjointness; prove it or report it missing.

## Phase 4 — interface with the existing full-cover frontier

Audit at least the following existing layers before claiming progress:

```text
DkMath.NumberTheory.Legendre.GnomonSupportTurnover
DkMath.NumberTheory.Legendre.ParitySafeFullCoverCapacityFrontier
DkMath.NumberTheory.Legendre.ParitySafeLowCostCapacitySlack
DkMath.NumberTheory.Legendre.ParitySafeCollisionPairOverlapCancellation
DkMath.NumberTheory.Legendre.ParitySafeActualFiberCancellation
```

Identify exactly which existing quantity could be reduced by the Petal-path information.

Candidate targets include:

```text
paritySafePrimePairOverlapCount
paritySafeSupportExcess
paritySafeLowCostResidualCapacity
paritySafeRechargeExactDepthResidualPairCapacityExcess
```

but do not modify any of them unless there is a proved containment, injection, disjointness, or strict numerical bound linking the Petal-path support to that quantity.

The report must state whether the new path information touches:

```text
local support only
pair-overlap ledger
incidence count
residual capacity
full-cover candidate balance
```

and give exact theorem names supporting the answer.

## Phase 5 — small numerical / theorem regressions

Use existing Lean-decidable examples or a small external numeric scratch only as diagnostics.

Suggested cases:

```text
n = 30, oddGnomon n = 61 (atomic/prime)
composite oddGnomon endpoints with at least two Petal factors
one endpoint represented by a two- or three-factor `petalFold`
```

Compare:

```text
old lower-common support bound
Petal-factor-localized bound
```

If no example exhibits a strict reduction in the relevant production cardinality, treat that as evidence for Outcome B, not as proof of impossibility.

Do not use numeric evidence as a theorem.

## Production rule

### If strict gain exists

Create the smallest application-owned Legendre module needed, for example:

```text
DkMath/NumberTheory/Legendre/GnomonPetalCapacity.lean
```

Only if it contains an actual strict/new capacity theorem.

Update `DkMath.NumberTheory.Legendre` facade and the campaign docs.

### If no strict gain exists

Do **not** add decorative production modules.

Write only:

```text
report-004.md
```

with:

- exact theorems audited;
- strongest derived consequence;
- why it is equivalent/weaker than current support filtering;
- the precise missing theorem needed for a strict gain;
- recommendation: continue / stop / switch provider.

This is a valid Outcome B.

### If one precise missing bridge remains

Use Outcome P only when it can be stated as a compact mathematical target, for example:

```text
pairwise disjointness of factor support channels under hypothesis H
```

or

```text
an injection from surviving overlap seats into a strictly smaller Petal-factor support space.
```

Avoid vague requests such as “need stronger sparsity”.

## Explicit non-goals

Do not claim or attempt in this task:

```text
Legendre's conjecture;
prime existence between consecutive squares;
ABC / FLT consequences;
arbitrary-degree primitive transitions;
Norm/lattice extensions;
new analytic prime estimates;
new axioms;
large speculative refactors.
```

## Validation if production Lean is added

Run focused builds for every changed/new module, then:

```text
lake build DkMath.NumberTheory.MultiGauge
lake build DkMath.NumberTheory.Legendre
```

Run the repository-standard forbidden scan on changed production Lean files. Required zero:

```text
sorry
admit
axiom
abc_main_axiom
native_decide
unsafe
```

Run `#print axioms` for every new main theorem. Expected kernel assumptions only; document them.

Run `git diff --check`.

## Deliverable

Always produce:

```text
report-004.md
```

The report must end with exactly one judgment:

```text
Outcome A — STRICT CAPACITY GAIN
Outcome B — STRUCTURAL NORMALIZATION ONLY
Outcome P — PRECISE CAPACITY BRIDGE REMAINS
```

The purpose of GMPT-004 is to decide whether GMPT-000..003 actually move the Legendre quantitative frontier, not to maximize theorem count.
