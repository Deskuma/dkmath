# Gnomon / MultiGauge Primitive Transition Roadmap 260915 v0

## GMPT-000 — degree-two provider

Status: IMPLEMENTED / VALIDATED

Target:

```text
DkMath.NumberTheory.MultiGauge.GnomonPetalTransition
```

Goals:

- package `oddGnomonGaugeStage n : GNGaugeStage 2`;
- prove its observer equals `oddGnomon n`;
- construct `gnomonPetalTransition a b` with
  - first = `P(a)`,
  - second = `P(petalMul a b)`,
  - numerator = `oddGnomon b`,
  - denominator = `1`;
- reuse generic prime transport to localize every genuinely new captured prime to the Petal factor.

This checkpoint updates the previous MG-003C audit only in degree two.  No arbitrary-degree provider is claimed.

## GMPT-001 — Legendre lower-turnover bridge

Status: IMPLEMENTED / VALIDATED

Target:

```text
DkMath.NumberTheory.Legendre.GnomonPetalTurnover
```

For `n = petalMul a b`, combine

```text
common lower support <-> old support and q | oddGnomon n
```

with

```text
oddGnomon n = oddGnomon a * oddGnomon b
```

to obtain the exact prime split

```text
common lower support
<->
old support and (q | oddGnomon a or q | oddGnomon b).
```

Then identify the second alternative with the numerator support of `gnomonPetalTransition a b`.

## GMPT-002 — Petal atomicity

Status: IMPLEMENTED / VALIDATED

Candidate production home:

```text
DkMath/Gnomon/PetalPrime.lean
```

Targets:

```text
PetalAtom
prime_oddGnomon_iff_petalAtom
odd_prime_existsUnique_gnomonAddress
```

Research meaning:

```text
odd prime gnomon
<->
no non-unit Petal multiplication decomposition
<->
no nontrivial Petal primitive transition decomposition of its address.
```

This should be treated as algebraic factorization/transport, not as a new prime-existence theorem.

## GMPT-003 — finite Petal transition paths

Status: IMPLEMENTED / VALIDATED

Production home:

```text
DkMath/NumberTheory/MultiGauge/GnomonPetalPath.lean
```

The canonical `petalFold` address sequence and `gnomonPetalPath` reuse the
existing `GNGaugePath` linked-list framework.  The validated API proves the
exact numerator/denominator products, endpoint observer/telescoping law,
all-stage escape preservation under factor avoidance, and localization of a
first or endpoint capture to an actual factor in the input list.

The finite path uses canonical `gnomonPetalTransition`s and the existing
`GNGaugePath` theorems; no second path framework is introduced.

Desired consequences:

- endpoint observer equals start odd gnomon times the product of Petal-factor odd gnomons;
- a prime absent at the start can first appear only in an actual Petal transition numerator;
- avoidance of all Petal factors preserves escape throughout the path.

Do not add a second path framework if existing `GNGaugePath` is sufficient.

## GMPT-004 — turnover capacity audit

Status: RESEARCH FRONTIER

Return to the Legendre adjacent-shell problem only after GMPT-000/001 are validated and GMPT-002 is available.

Questions:

1. Can lower common support be charged to a bounded number of Petal factors rather than to the whole `oddGnomon n`?
2. Does Petal atomicity force complete lower turnover at prime gnomon addresses in a way useful to simultaneous full-cover counting?
3. Can lower disjointness and the upper `{2}` channel be combined into a nontrivial quantitative turnover ledger?
4. Does such a ledger reduce the existing full-cover capacity frontier rather than merely restate local divisibility?

Only open a new capacity module if an actual inequality/cardinality improvement is obtained.

## Stop conditions

Stop and report Outcome B rather than adding decorative APIs if:

- the Petal provider compiles but yields only already-known one-stage divisibility;
- the Legendre bridge does not improve support localization beyond the existing exact turnover theorem;
- a proposed path is merely endpoint-copy balance;
- a capacity theorem has no strict numerical/cardinality gain.

## Proof discipline

- reuse `DkMath.Gnomon.Algebra` and `DkMath.Gnomon.CosmicBridge`;
- reuse generic `MultiGauge.PrimeTransport` / `Path`;
- keep generic MultiGauge independent of Legendre;
- keep Legendre bridges application-owned;
- no `sorry`, `admit`, or new axioms;
- distinguish IMPLEMENTED / UNVALIDATED from PRODUCTION-PROVED for future
  work until its focused builds pass.
