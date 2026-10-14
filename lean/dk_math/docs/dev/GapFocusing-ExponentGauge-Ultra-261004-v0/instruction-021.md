# Instruction 021 - Exact deletion carrier and kernel capacity certificates

## Mission

Continue from Instruction 020.

Instruction 020 produced the first genuinely new bounded full-cover obstructions from the coarse PrimeWorld route.

Two mechanisms now exist:

1. Full-period vertical capacity.
2. Actual old-support collision packing routed through the existing OldSupportCapacity consumer.

The generic packing theorem already constructs a concrete remainder internally:

  E = supportCollisionEdges V f
  D = image Prod.fst E
  R = V minus D

and proves R is pairwise support-disjoint.

However the public theorem currently keeps only the weaker estimate:

  V.card <= R.card + E.card.

The diagnostic scan shows that the actual deletion carrier D can be dramatically smaller than E.

At n=1031 with the operational initial world:

  S = primeScalesUpTo 10
  M = 210
  V.card = 432
  old prime count = 173
  E.card = 2565
  diagnostic first-endpoint remainder R.card = 216

Thus the edge-count consumer fails badly, while the actual constructed remainder would exceed the old-prime capacity if its exact deletion cardinality is kernel-certified.

Instruction 021 must expose the deletion carrier used by the existing proof, prove its exact partition and cardinality API, connect it to OldSupportCapacity, and then kernelize selected finite capacity certificates.

The priority endpoint is n=1031 through the symbolic production deletion carrier, not through a manually chosen prime witness.

The second priority is an explicit certificate checker capable of validating discovered support-disjoint families such as the n=297 initial-world family of size 63 against 62 old primes.

Do not confuse finite endpoint certification with a universal Legendre proof.

All new instruction, findings, logs, and report artifacts must remain parser-safe plain text. Avoid backslash notation and LaTeX control sequences.

## Phase 0 - source and proof-path audit

Audit at minimum:

DkMath.Combinatorics.FinsetSupportPacking
DkMath.NumberTheory.Legendre.CoarseTownSupportPacking
DkMath.NumberTheory.Legendre.CoarsePrimeWorldFullTown
DkMath.NumberTheory.Legendre.CoarsePrimeWorldVerticalCapacity
DkMath.NumberTheory.Legendre.OldSupportCapacity
DkMath.NumberTheory.Legendre.OldSupportGcd
DkMath.NumberTheory.Legendre.Frontier

Audit Mathlib for:

- Finset image subset
- card image
- card set difference
- card union
- exact card partition theorems
- decidability of pairwise disjoint finite support families
- kernel-safe finite decision tactics
- sorted-list or Finset literal normalization

Search repository-wide for existing certificate-checker patterns used for large finite arithmetic regressions.

Record exact theorem names and any trust-boundary issues in source-inventory-021.md.

## Phase 1 - expose the generic deletion carrier

In DkMath.Combinatorics.FinsetSupportPacking, expose the carrier currently hidden inside exists_supportPacking.

Suggested definitions:

  supportCollisionDeletionVertices V f
  =
  image Prod.fst of supportCollisionEdges V f

  supportPackingRemainder V f
  =
  V minus supportCollisionDeletionVertices V f

Names may differ if a clearer repository convention exists.

The definitions must be generic in the existing alpha and beta types.

Do not change the semantics of supportCollisionEdges.

## Phase 2 - exact deletion membership and subset API

Prove exact membership characterizations.

For deletion vertices:

  a in D
  iff
  exists b,
    (a,b) in supportCollisionEdges V f.

For the remainder:

  a in R
  iff
  a in V and a notin D.

Prove:

  D subset V
  R subset V
  Disjoint R D
  R union D = V

The union orientation may be whichever is most convenient.

Do not use cardinality alone where exact set equality is available.

## Phase 3 - exact partition cardinality

From the exact partition prove:

  V.card = R.card + D.card.

This is stronger than the existing:

  V.card <= R.card + E.card.

Also retain:

  D.card <= E.card

as a corollary of image cardinality.

Then recover the old weak bound from the exact partition plus D.card <= E.card.

Refactor exists_supportPacking to delegate to the new public deletion API rather than duplicating the old local definitions.

Its public proposition should remain unchanged unless a stronger companion theorem is added.

## Phase 4 - pairwise disjointness of the exact remainder

Prove as a named public theorem:

  the supportPackingRemainder is PairwiseDisjoint for f.

The proof should be the existing first-endpoint deletion argument.

Also provide a bundled theorem containing:

  R subset V
  PairwiseDisjoint
  V.card = R.card + D.card.

This becomes the exact generic certificate packet.

Do not claim maximality or optimality of R.

## Phase 5 - optional second-endpoint deletion audit

Because collision edges are oriented by a<b, deleting all first endpoints is arbitrary.

Audit the equally valid carrier:

  Dright = image Prod.snd E
  Rright = V minus Dright.

If cheap, prove the symmetric exact partition and pairwise-disjointness theorem.

Then compare:

  Dleft.card
  Dright.card.

Optionally define a better-of-two endpoint deletion only if it remains simple and transparent.

Do not introduce a greedy algorithm in this phase.

The required route remains the existing first-endpoint deletion.

## Phase 6 - Legendre-specific exact deletion carrier

In CoarseTownSupportPacking or a focused new module, define thin abbreviations:

  coarseTownDeletionVertices S n
  coarseTownPackingRemainder S n

by specializing the generic deletion definitions to:

  V = coarsePrimeWorldFullTown S n
  f = squareOffsetPrimeSupport n.

Expose exact membership and subset theorems as needed.

Prove:

  coarseTownPackingRemainder S n
  is a PairwiseOldSupportDisjointSquareSeatFamily n.

Use the existing fullTown subset of squareOffsets theorem for the seat condition.

## Phase 7 - exact coarse-town cardinality packet

Prove:

  fullTown.card
  =
  remainder.card + deletion.card.

Combine with the existing fullTown formula:

  fullTown.card
  =
  periodCount * totient(M).

Expose a useful rewriting theorem:

  remainder.card
  =
  fullTown.card - deletion.card

only if Nat subtraction hypotheses and rewriting are clean.

The additive exact partition is the primary theorem.

## Phase 8 - deletion-deficit full-cover obstruction

Derive the stronger existing-consumer criterion:

If:

  (primeScalesUpTo n).card + deletion.card < fullTown.card

then:

  not SquareOffsetsFullyCovered n.

The proof should use:

  oldPrimeCard < remainder.card

obtained from the exact partition, then delegate to:

  not_fullyCovered_of_primeWorld_card_lt_pairwiseOldSupportDisjointSquareSeatFamilies.

Do not duplicate the capacity proof.

Also provide the positive-anchor endpoint:

If:

  0 < n
  and
  oldPrimeCard + deletion.card < fullTown.card

then:

  exists p, Nat.Prime p and SquareCell n p.

Delegate to the existing OldSupportCapacity prime consumer.

## Phase 9 - relation to the edge-deficit theorem

Prove that the new deletion-deficit criterion is at least as strong as the old edge-deficit criterion because:

  deletion.card <= edge.card.

Prefer a theorem-level implication between hypotheses or between resulting non-full-cover statements.

Preserve a finite strictness witness where:

  deletion deficit succeeds
  edge deficit fails.

The primary target is n=1031 initial world if kernel computation closes.

If a smaller anchor gives a cheaper strictness calibration, preserve that too.

## Phase 10 - kernel certification of n=1031 initial world

Use:

  n = 1031
  S = primeScalesUpTo 10.

Expected already-proved symbolic facts include:

  primeWorldModulus S = 210
  periodCount = 9
  base.card = 48
  fullTown.card = 432
  (primeScalesUpTo 1031).card = 173.

The diagnostic report predicts:

  coarseTownPackingRemainder S 1031 has card 216

equivalently:

  coarseTownDeletionVertices S 1031 has card 216.

Kernel-certify the smallest sufficient finite fact.

Preferred route:

  deletion.card = 216

then use the exact symbolic partition to derive remainder.card = 216.

Do not manually prove pairwise disjointness of 216 seats if the generic remainder theorem already supplies it.

Do not use the Python diagnostic as proof.

For the finite cardinality evaluation:

- prefer decide +kernel, norm_num, simp, or repository-approved kernel reduction
- if another evaluation mechanism is needed, audit its theorem dependencies explicitly
- do not allow sorryAx
- document runtime and memory if the check is expensive

Then prove a named endpoint theorem, for example:

  exists_prime_squareCell_1031_of_coarseTownDeletion

with conclusion:

  exists p, Nat.Prime p and SquareCell 1031 p.

Do not choose or expose a concrete prime unless it falls out naturally.

## Phase 11 - preserve route provenance at n=1031

The repository already has a different n=1031 endpoint from the earlier quotient and rejection route.

Audit its exact declaration name.

Do not merge the proofs into one opaque theorem.

Preserve the new full-period deletion endpoint as an independently named theorem.

Add a regression or documentation statement that both routes reach the same existential square-cell conclusion through different theorem dependencies.

A dependency comparison is welcome.

Do not claim formal proof independence in a stronger logical sense unless actually established.

## Phase 12 - generic explicit capacity certificate predicate

Define a small reusable certificate proposition for a supplied seat family R.

Preferred semantic content:

  R is a PairwiseOldSupportDisjointSquareSeatFamily n
  and
  (primeScalesUpTo n).card < R.card.

If a named Prop is unnecessary, a theorem wrapper around the existing predicate is acceptable.

The key requirement is a stable checker-facing API.

Suggested theorem:

  exists_prime_squareCell_of_oldSupportCapacityCertificate

taking:

  0 < n
  certificate n R

and delegating to the existing consumer.

Avoid duplicating OldSupportCapacity semantics.

## Phase 13 - computable certificate checker

Audit whether the certificate predicate is already Decidable with current Finset definitions.

If so, provide a simple Boolean or decidable checker only if it materially simplifies large finite calibrations.

Possible form:

  checkOldSupportCapacityCertificate n R : Bool

with theorem:

  checkOldSupportCapacityCertificate n R = true
  iff
  certificate n R.

The checker must verify actual mathematics:

- every r is a square offset
- pairwise actual old-support disjointness
- cardinality exceeds old-prime count

Do not encode precomputed support labels as trusted input.

The checker may optimize by using:

  disjoint_squareOffsetPrimeSupport_iff_no_bounded_prime_dividing_offset_gap

or gcd criteria, but the final theorem must imply the existing family predicate.

If a Boolean wrapper adds no value over direct decide +kernel on the Prop, keep the Prop-only interface and document that choice.

## Phase 14 - import discovered n=297 certificate

Read the exact n=297 initial-world discovered family from:

  logs/discovery-020.json

or regenerate it deterministically from the documented search.

The report predicts:

  family size = 63
  old prime count = 62.

Do not trust these numbers without kernel checking.

Represent the family as a Finset literal or compact reproducible construction.

Kernel-check:

  PairwiseOldSupportDisjointSquareSeatFamily 297 R
  (primeScalesUpTo 297).card < R.card.

Then route through the existing consumer to prove:

  exists p, Nat.Prime p and SquareCell 297 p.

The checker must certify the family; Python is only a discovery source.

If the exact diagnostic family is awkward, a different explicit 63-or-larger family is acceptable.

## Phase 15 - optional explicit n=1031 discovered family

The diagnostic greedy family has size 233 versus 173 old primes.

This is stronger numerically than the first-endpoint remainder size 216.

Only after the symbolic deletion endpoint is complete, try to kernel-certify an explicit discovered n=1031 family if runtime is reasonable.

This is optional because it proves the same anchor endpoint.

Its value is to validate the general certificate checker on a large witness and compare a search-found packing with the deterministic deletion packing.

Do not block Outcome A if this optional calibration is expensive.

## Phase 16 - certificate encoding audit

For large explicit families compare at least:

- Finset literal
- sorted List converted to Finset
- range/filter predicate when a compact arithmetic description exists
- image of a smaller index set

Prefer the representation with:

- smallest source size
- predictable kernel reduction
- no duplicate-element ambiguity
- simple membership proof

Do not optimize for pretty printing at the cost of proof transparency.

Record the chosen encoding.

## Phase 17 - large finite check performance

Record approximate build behavior for:

- n=1031 deletion-card certificate
- n=297 explicit family certificate
- optional n=1031 explicit family

If direct kernel decision becomes too expensive, seek a structural compression before using a less trusted evaluator.

Possible structural compression:

- partition by columns
- use exact column support-disjointness
- prove only cross-column disjointness for the retained family
- use gcd gap criteria instead of expanding full support Finsets

The goal is kernel evidence, not fastest Python confirmation.

## Phase 18 - deletion family structure discovery

Once the n=1031 first-endpoint remainder is kernelized, inspect its structure.

Record:

- seats per column
- which columns lose most seats
- which primes cause deleted first endpoints
- whether the retained set has a simple arithmetic description
- whether the 216-card family is close to half the full town for a structural reason

Do not infer a universal theorem from one anchor.

If a simple structural selector emerges, state it as a candidate for the next checkpoint.

## Phase 19 - compare deterministic deletion and greedy certificate

For bounded diagnostics compare:

  deterministic first-endpoint remainder
  optional second-endpoint remainder
  greedy support-disjoint family
  old prime count.

Record how often each exceeds the capacity threshold in the existing 602-row dataset.

This is diagnostic only.

The purpose is to decide whether the next theorem should improve:

- deletion orientation
- prime-fiber deletion
- cross-column symbolic packing
- or canonical world selection.

## Phase 20 - prime-fiber deletion audit

Report 020 proposed another generic strategy:

For each nonempty prime fiber, retain one chosen seat and delete the others.

Do not implement a complicated global union algorithm unless necessary.

First determine exact semantics and whether a simple neutral theorem can bound a deletion union by:

  sum over q of max(fiber.card - 1,0).

Remember that one seat may lie in several prime fibers, so union-counting can improve the raw sum.

Classify this route:

A. cheap useful strengthening
B. equivalent to existing endpoint deletion
C. too weak in current diagnostics
D. requires a nontrivial hitting-set theorem

Only implement production code if it improves a current certificate or yields a reusable theorem.

## Phase 21 - do not return to valuation yet

The Instruction 018 prime-power floor-sum theorem remains deferred.

Instruction 020 identified cross-support packing, not valuation precision, as the active frontier.

Do not implement the floor-sum theorem unless a deletion or certificate theorem in this checkpoint requires it.

## Phase 22 - bounded regression set

At minimum preserve kernel checks for:

- a tiny collision-free case
- a case with multiple edges sharing one first endpoint, showing D.card < E.card
- the n=11 edge-packing endpoint from 020
- a strict deletion-vs-edge improvement
- n=1031 initial deletion endpoint if successful
- n=297 explicit certificate endpoint if successful
- one invalid certificate rejected by the checker or direct decidability

The invalid certificate should fail for a real mathematical reason such as shared old support, not malformed syntax.

## Phase 23 - exact next-provider judgment

After the finite endpoints are kernelized, determine the narrowest symbolic frontier.

Possible next directions:

1. Structural deletion bound

Prove a uniform upper bound on deletion.card using prime fibers and full-period geometry.

2. Cross-column retained-family selector

Construct R directly from phased columns with a symbolic disjointness theorem.

3. Better endpoint orientation

Use left or right endpoint deletion, or a simple canonical orientation, to reduce deletion cost uniformly.

4. Canonical fitting world

Choose S as a function of n only after a symbolic packing theorem makes the choice useful.

Do not propose a universal Legendre theorem unless the report actually closes the required inequalities.

## Possible outcomes

Outcome A - EXACT DELETION CARRIER ADDS NEW KERNEL ENDPOINTS

The exact deletion API is proved and at least one previously diagnostic-only large endpoint, preferably n=1031 or n=297, is kernel-certified through the existing capacity consumer.

Outcome B - EXACT DELETION CARRIER STRENGTHENS THE FRONTIER

The exact deletion theorem and stronger consumer are proved, but large diagnostic endpoints remain computationally or arithmetically unkernelized.

Outcome C - EDGE COMPRESSION GIVES NO PRACTICAL NEW CERTIFICATE

The deletion carrier is exact but does not improve the usable capacity frontier after kernel evaluation.

Outcome P - ONE FINITE CERTIFICATE CHECK REMAINS

The generic deletion mathematics is complete and a specific large endpoint is reduced to one explicit finite kernel certificate.

## Non-goals

Do not claim:

- Legendre conjecture
- optimality of the deletion remainder
- maximum independent set
- that the greedy family is canonical
- that Python diagnostics are proofs
- that n=1031 has only one proof route
- that finite endpoint success implies asymptotic success
- random independence of supports
- PNT, RH, Bertrand, or analytic sieve bounds

Do not introduce a second old-support capacity consumer.

Do not replace exact actual support with precomputed labels.

## Suggested implementation surface

Extend:

DkMath/Combinatorics/FinsetSupportPacking.lean

with the exact generic deletion carrier.

Add a focused Legendre module if useful, for example:

DkMath/NumberTheory/Legendre/CoarseTownDeletionCapacity.lean

Put large finite endpoint certificates under DkMathTest when they are calibration-only.

If an endpoint theorem is intended as public mathematical API, keep a small production theorem that consumes a checked certificate, while the large literal witness may remain in a test or calibration module according to current repository conventions.

Do not bloat the main Legendre facade with raw certificate data.

## Validation

For all new production declarations:

- focused builds
- lake build DkMath.NumberTheory.Legendre
- lake build DkMath
- forbidden-token scan
- print axioms for every new public declaration
- git diff --check

For certificate endpoints:

- record the exact proof method
- record whether the check is pure kernel reduction
- inspect declaration dependencies
- reject any endpoint carrying sorryAx

The existing unrelated root sorry warnings may remain, but do not add new ones.

Preserve current file-header and file-marker conventions.

## Durable checkpoint protocol

Update findings after:

- generic deletion carrier
- exact partition
- exact remainder pairwise-disjointness
- deletion-deficit consumer
- edge-deficit comparison
- n=1031 kernel attempt
- certificate API
- n=297 explicit certificate
- optional n=1031 explicit certificate
- finite-check performance audit
- deterministic versus greedy comparison
- next symbolic frontier
- final A/B/C/P judgment

Preserve failed kernel strategies and counterexamples when informative.

## Final report

Answer explicitly:

1. What are the exact public definitions of deletion vertices and the packing remainder?
2. Is D subset V proved exactly?
3. Is V = R union D with disjoint union semantics proved?
4. Is V.card = R.card + D.card proved exactly?
5. Is R pairwise support-disjoint by construction?
6. What is the specialized coarse-town deletion carrier?
7. What exact deletion-deficit theorem routes to OldSupportCapacity?
8. Is it formally stronger than the edge-deficit theorem?
9. Was n=1031 with S=primeScalesUpTo 10 kernel-certified through the deletion route?
10. What exact deletion and remainder cards were kernel-proved there?
11. What prior n=1031 endpoint exists, and how does the new route differ?
12. What certificate-checker API was implemented?
13. Was an explicit n=297 family of size greater than the old-prime count kernel-certified?
14. Was the optional n=1031 explicit greedy family kernel-certified?
15. Which representation and proof method were used for large finite certificates?
16. Did second-endpoint or prime-fiber deletion improve the frontier?
17. What is the narrowest symbolic theorem worth attempting next?

End with exactly one judgment:

Outcome A - EXACT DELETION CARRIER ADDS NEW KERNEL ENDPOINTS
Outcome B - EXACT DELETION CARRIER STRENGTHENS THE FRONTIER
Outcome C - EDGE COMPRESSION GIVES NO PRACTICAL NEW CERTIFICATE
Outcome P - ONE FINITE CERTIFICATE CHECK REMAINS
