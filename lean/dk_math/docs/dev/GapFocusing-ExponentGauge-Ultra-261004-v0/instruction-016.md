# Instruction 016 - Legendre gnomon / primorial residue-cover counterexample packet

## Mission

Continue from Instruction 015, but change viewpoint.

The current Legendre development already has two strong descriptions of the same square shell.

Residue and primorial-wheel side:
- SquareOffsetCovered n r
- squareAnchorForbiddenResidue n q
- PrimorialWheelBridge
- projected wheel survivor and reservation semantics

Sqrt-rough factorization side:
- exact support strata
- complete factorization census:
  R = U + Cube + Cross + Repeated + Triple
- corrected quotient conservation:
  Qtotal = Cross + Cube + 2*Repeated + 3*Triple + Rejected

Instruction 016 should not begin by adding another ad-hoc capacity argument.

Its primary task is to formalize the hypothetical counterexample object itself.

If a Legendre counterexample shell existed, then every gnomon seat would be covered by a bounded-prime forbidden residue, there would be no projected primorial-wheel survivor, the sqrt-rough zero stratum would vanish, and the complete factorization and quotient-conservation identities would hold simultaneously.

Build the exact bridge first. Then search for a new obstruction in that combined state.

The desired result is not predetermined. A precise negative result or a new invariant is acceptable.

## Important gnomon indexing audit

Do not blur these three quantities.

For anchor n:

- consecutive-square difference:
  (n+1)^2 - n^2 = 2*n + 1

- open Legendre shell offsets:
  1 <= r <= 2*n

  The final point at offset 2*n+1 is (n+1)^2, so it is a square boundary and is not an open-shell seat.

- next outward gnomon:
  (n+2)^2 - (n+1)^2 = 2*n + 3

Thus the consecutive odd gnomon states are:

  2*n - 1
  2*n + 1
  2*n + 3

with successor law:

  G(n+1) = G(n) + 2

while the prime-search interior has exactly 2*n seats.

Audit the existing declarations:
- DkMath.Gnomon.oddGnomon
- squareOffsets
- GnomonSuccessor
- GnomonSupportTurnover

Preserve their current indexing.

If useful, add a small neutral theorem packet stating:
- oddGnomon(n+1) = oddGnomon(n) + 2
- relation between odd gnomon size 2*n+1 and open-shell seat count 2*n

Do not redefine existing gnomon vocabulary only to change notation.

## Required source audit

Audit at minimum:

DkMath.NumberTheory.Legendre.Basic
DkMath.NumberTheory.Legendre.Wave
DkMath.NumberTheory.Legendre.Frontier
DkMath.NumberTheory.Legendre.PrimorialWheelBridge
DkMath.NumberTheory.Legendre.PrimorialWheelSuccessor
DkMath.NumberTheory.Legendre.GnomonSuccessor
DkMath.NumberTheory.Legendre.GnomonSupportTurnover
DkMath.NumberTheory.Legendre.ParitySafeFullCoverCapacityFrontier
DkMath.NumberTheory.Legendre.ParitySafeSqrtRoughCensus
DkMath.NumberTheory.Legendre.ParitySafeSqrtQuotientConservation
DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOrbit
DkMath.NumberTheory.PrimorialUniverse.WheelProjection

Also inspect existing CRT, finite prime-basis, and primorial-product declarations before introducing any residue-vector abstraction.

Record exact reusable theorem names in the source inventory.

## Phase 1 - exact residue-cover fibers on the gnomon shell

For each bounded prime q <= n, expose the finite shell fiber:

  CoverFiber(n,q)
  =
  { r in squareOffsets(n) : r mod q = squareAnchorForbiddenResidue(n,q) }

Prefer a definition as a filter of the existing squareOffsets n.

Prove exact membership equivalence to:

  q divides n^2 + r

Reuse squareOffsetForbiddenBy_iff_mod_eq_forbiddenResidue.
Do not reprove modular arithmetic.

Then prove a finite union theorem equivalent to:

  coveredSquareOffsets(n)
  =
  union over q in primeScalesUpTo(n) of CoverFiber(n,q)

This is the explicit theorem that overlays prime residue classes on the gnomon shell.

## Phase 2 - full cover as a residue-class cover

Prove an exact theorem equivalent to:

  SquareOffsetsFullyCovered(n)
  iff
  squareOffsets(n)
  =
  union over prime q <= n of CoverFiber(n,q)

Also expose the pointwise form:

  for every r in squareOffsets(n),
  there exists q in primeScalesUpTo(n)
  such that
  r mod q = squareAnchorForbiddenResidue(n,q)

This should be a rewrite of existing semantics, not a new conjecture.

## Phase 3 - wheel image of the whole square shell

Let:

  S_n = primeScalesUpTo(n)
  M_n = finitePrimeBasisProduct(S_n)

If there is no existing equivalent object, define:

  ShellWheelImage(n)
  =
  image of squareShellWheelProjection(S_n,n,r)
  for r in squareOffsets(n)

Prove:

- each projected seat is the square-anchor coordinate advanced by r modulo M_n
- full cover iff every projected shell point is reserved
- failure of full cover iff the image contains a wheel survivor

Reuse not_squareOffsetCovered_iff_projection_survivor.

Do not assume the projection is injective.

## Phase 4 - projection multiplicity and injectivity audit

Determine exactly when the map

  r -> squareShellWheelProjection(S_n,n,r)

is injective on:

  1 <= r <= 2*n

A sufficient condition is expected to be:

  2*n < M_n

or a nearby no-wrap condition.

Prove the strongest clean theorem available.

Audit finite thresholds:
- n = 2
- n = 3
- n = 4
- the first n from which the primorial period exceeds the shell width
- prime-threshold and composite-threshold transitions

Do not assume a global inequality without proof.

If the map is not injective in small cases, preserve exact collisions.

## Phase 5 - canonical residue-cover owner

A covered seat may have several covering primes.

If useful, define a canonical cover owner using the least actual support prime, or reuse an existing canonical support-prime mechanism if it applies exactly.

For a covered square offset r, target a packet:

  owner(n,r) = q

with:
- q is prime
- q <= n
- q divides n^2+r
- r mod q = squareAnchorForbiddenResidue(n,q)
- q is minimal among covering primes

Then obtain a disjoint owner-fiber partition of the covered shell.

This phase is optional if an existing canonical owner already supplies exactly the same object.

Do not duplicate the sqrt-rough canonical-root ledger.

## Phase 6 - counterexample packet

Create one production theorem bundle for the hypothesis:

  hfull : SquareOffsetsFullyCovered(n)

For n > 0, derive simultaneously:

1. every shell seat has nonempty old-prime support

2. the projected primorial-wheel shell has no survivor

3. paritySafeUncoveredCandidates n = empty

4. the sqrt-rough zero stratum has cardinality 0

5. the complete sqrt-rough census collapses to:

   R = Cube + Cross + Repeated + Triple

6. corrected quotient conservation remains:

   Qtotal = Cross + Cube + 2*Repeated + 3*Triple + Rejected

7. therefore the counterexample balance is:

   Qtotal = R + Repeated + 2*Triple + Rejected

Prefer additive Nat-safe equalities.

This is a necessary-condition package for a hypothetical counterexample. It does not assert that such a counterexample exists.

## Phase 7 - exact converse where valid

Audit which parts of the counterexample packet are actually equivalent to full cover.

In particular:
- U = 0 on the parity-safe or sqrt-rough carrier may require explicit positivity and carrier hypotheses before it is equivalent to full cover
- no projected wheel survivor in the whole square shell should be equivalent to full cover for n >= 2
- the numerical balance alone may be weaker

Prove equivalences only when exact.

Record one-way implications as one-way implications.

## Phase 8 - residue-cover owner versus factorization type

For each covered sqrt-rough seat, connect its canonical residue owner prime to its factorization type:

- Cube: p^3
- Cross: p*q
- Repeated: p^2*q or p*q^2
- Triple: p*q*s

Determine whether the residue owner is:
- the repeated prime
- the least support prime
- any support prime
- or type-dependent

Do not guess a universal owner rule.

Produce exact owner/type packets and preserve the smallest counterexample to any false simple rule.

## Phase 9 - CRT and primorial state formulation

The wheel projection modulo

  M_n = product of primes p <= n

already encodes all bounded-prime residues.

Investigate whether a hypothetical full-cover shell can be expressed by the finite square-anchor state:

  a_n = n^2 mod M_n

with positions:

  a_n + 1
  ...
  a_n + 2*n

taken modulo M_n and all reserved by at least one prime-basis coordinate.

Formalize the exact theorem if supported:

  SquareOffsetsFullyCovered(n)
  iff
  every offset r with 1 <= r <= 2*n
  gives a reserved state at a_n + r modulo M_n

Handle modular projection exactly.

This is the square-anchored wheel-cover statement.

Do not replace it by an arbitrary Jacobsthal or maximum-gap statement.

## Phase 10 - square-anchor restriction versus generic wheel gaps

If useful, introduce a square-anchored local predicate such as:

  SquareAnchorWheelFullyReserved(n)

The relevant question is not:

  Does the primorial wheel contain any reserved run of length 2*n?

The relevant question is:

  Does the specific run beginning at a_n = n^2 mod M_n contain 2*n reserved states?

Prove the new predicate equivalent to SquareOffsetsFullyCovered n if introduced.

Do not implement a generic Jacobsthal bound unless it becomes genuinely necessary.

## Phase 11 - gnomon successor transport

Use the exact fixed-old-basis successor law:

  a_(n+1) = a_n + (2*n+1) mod M

and the existing fresh-prime wheel enlargement when n+1 is prime.

Combine this with GnomonSupportTurnover:

- lower reindexed common support is controlled by divisors of 2*n+1
- upper common support is controlled by divisors of 2*(n+1)
- at a prime threshold the upper common old support is only prime 2

Search for an exact theorem saying that a hypothetical full-cover state at n and or n+1 imposes a rigid residue-owner transition.

Do not assume that full cover propagates or fails to propagate.

A precise transition obstruction is a valid result.

## Phase 12 - three consecutive odd gnomons

Make the local geometry explicit if useful:

  G_(n-1) = 2*n - 1
  G_n     = 2*n + 1
  G_(n+1) = 2*n + 3

Investigate the support-turnover equations across:

  n-1 -> n -> n+1

Possible exact signals:
- a residue owner that persists across shells can persist only when it divides the corresponding gnomon displacement
- prime-threshold transitions reduce upper persistence to 2
- lower persistence forces divisors of the odd gnomon

Do not infer a contradiction from parity alone.

Formalize only exact persistence statements.

## Phase 13 - Primorial and sqrt-Primorial address audit

This phase is exploratory and must not block the core counterexample packet.

Let:

  M_n = finitePrimeBasisProduct(primeScalesUpTo(n))

Audit the integer neighborhood of sqrt(M_n).

Possible finite definitions:

  a = Nat.sqrt M_n
  L = M_n - a^2
  U = (a+1)^2 - M_n

When M_n is not itself a square, prove elementary identities such as:

  L + U = 2*a + 1

Compare the gnomon address of M_n with:
- the Legendre anchor n
- the wheel period M_n

The purpose is to test whether the primorial body has a useful square-shell address.

Do not assert relevance to Legendre without a proved bridge.

Also audit existing Primitive and PrimorialUniverse objects before inventing a new primitive primorial.

## Phase 14 - search for the first genuinely new obstruction

After the exact counterexample packet exists, search structurally for one of these outcomes.

A. Residue-cover impossibility

A theorem showing that the square-anchored run of length 2*n cannot be fully reserved.

B. Owner-transition impossibility

A successor or three-gnomon theorem incompatible with full cover.

C. Census-residue incompatibility

The residue-owner partition cannot realize the required Cube, Cross, Repeated, and Triple counts under the counterexample balance.

D. Primorial-period incompatibility

The square-anchor orbit and wheel enlargement prevent the required cover pattern.

E. Corrected negative result

None of these gives new leverage. Identify the exact missing arithmetic theorem.

Search is encouraged.
Do not manufacture a desired conclusion.

## Phase 15 - finite counterexample-pattern search

For a bounded range compatible with runtime, enumerate the necessary residue-cover pattern, not merely prime existence.

For each n, record:
- square-anchor wheel coordinate
- primorial period M_n
- shell width 2*n
- number of projected shell survivors
- canonical cover-owner fiber sizes
- support-overlap distribution
- first escaping offset when full cover fails
- counterexample-balance quantities R, Repeated, Triple, Rejected, Qtotal when available

Search especially for near-miss shells with the fewest survivors.

These are the best stress tests for any proposed structural obstruction.

Do not infer asymptotics.

## Phase 16 - relation to rejection and the small-prime quotient wheel

Instruction 015 Rejected detects quotient values with a prime factor:

  u <= Nat.sqrt n

Compare this with shell-level primorial residue cover by primes:

  p <= n

Prove the exact map or exact separation.

Keep the levels distinct:

- shell residue cover acts on n^2+r
- quotient rejection acts on the complementary quotient q

Determine whether the following two-level wheel picture is mathematically exact:

  shell wheel uses primes p <= n
  quotient wheel uses primes u <= Nat.sqrt n

Do not identify these two reservations without a theorem.

A clean two-level reservation diagram is valuable even if it does not yield a new prime theorem.

## Phase 17 - candidate contradiction theorem contract

At the end, state exactly one next theorem which, if proved, would rule out full cover.

Preferred forms include:

  SquareAnchorWheelFullyReserved(n) -> False

under a clearly stated structural hypothesis already proved for all n,

or:

  hfull
  -> counterexample invariant
  -> numerical or structural contradiction

If no unconditional contract is supported, state the narrowest missing provider.

Do not hide a prime-distribution assumption inside a helper theorem.

## Calibration and regressions

At minimum preserve and connect:
- existing wheel regression n=4 with basis {2,3}
- rejected quotient counterexample n=11, p=5, q=27
- one repeated-support multiowner case
- one triple-support case
- structural endpoint n=1031
- at least one near-miss shell from the new bounded residue-cover search

If the new packet proves only equivalences and reductions, calibrate those exact objects instead of forcing a new prime endpoint.

## Possible outcomes

Outcome A - SQUARE-ANCHORED RESIDUE/CENSUS OBSTRUCTION FOUND

The counterexample packet is complete and a new exact incompatibility rules out a nontrivial class of hypothetical full covers or yields new unconditional square-cell prime endpoints.

Outcome B - COUNTEREXAMPLE PACKET COMPLETE, TRANSITION LEVERAGE PARTIAL

Residue cover, wheel, census, quotient, and successor statements are unified exactly, but no uniform contradiction is obtained.

Outcome P - PRECISE CRT/OWNER BRIDGE REMAINS

The necessary counterexample conditions are formalized, but one explicit residue-owner or successor-transport theorem blocks the combined obstruction.

Outcome C - COMBINED VIEWS ARE EQUIVALENT BOOKKEEPING ONLY

The new maps add no structural leverage beyond existing full-cover, wheel, and census equivalences. Preserve the exact equivalence theorem and identify the next genuinely arithmetic provider.

## Non-goals

Do not claim:
- Legendre conjecture
- a generic Jacobsthal bound
- PNT or RH
- Bertrand
- analytic sieve estimates
- random or equidistribution heuristics as proof
- FLT or ABC consequences

Do not build a new CRT framework if the existing primorial wheel projection already supplies the needed state.

Do not conflate:
- odd gnomon size 2*n+1
- open shell seat count 2*n
- successor odd gnomon 2*n+3

Do not replace exact shell anchoring by an arbitrary wheel interval.

Do not use sorryAx-bearing endpoints in production.

## Implementation guidance

A focused module split is reasonable, for example:

DkMath/NumberTheory/Legendre/GnomonResidueCover.lean
DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean
DkMath/NumberTheory/Legendre/GnomonPrimorialTransition.lean

Use PrimorialWheelBridge as the wheel dictionary.

Use the existing sqrt-rough census and quotient conservation as the arithmetic dictionary.

If the counterexample packet is cleanly expressible as theorem bundles, prefer theorem bundles over a large record.

## Validation

For all new production declarations:
- focused builds
- lake build DkMath.NumberTheory.Legendre
- lake build DkMath
- forbidden-token scan
- print axioms for every new public declaration
- git diff --check

All new production declarations must remain free of sorryAx.

Preserve the existing file-header and import-adjacent file marker convention.

## Durable checkpoint protocol

Update findings after:
- gnomon indexing audit
- explicit residue-cover fibers
- full-cover union equivalence
- whole-shell wheel image
- projection injectivity threshold
- counterexample packet
- residue-owner partition
- square-anchor CRT formulation
- successor and three-gnomon transition search
- two-level shell and quotient wheel comparison
- near-miss finite search
- final A/B/P/C judgment

Preserve false conjectures and smallest counterexamples.

## Final report

Answer explicitly:

1. What exact residue-class cover theorem describes SquareOffsetsFullyCovered n?
2. How is the whole shell represented in the primorial wheel?
3. When is the shell projection injective, and what are the small exceptions?
4. What exact necessary-condition packet does a hypothetical Legendre counterexample satisfy?
5. Which parts of that packet are equivalent to full cover and which are only consequences?
6. How do residue-cover owners relate to Cube, Cross, Repeated, and Triple factorization types?
7. What exact square-anchor CRT or wheel-cover formulation was proved?
8. Does the 2*n-1, 2*n+1, 2*n+3 successor geometry impose any new support-transition obstruction?
9. Is there a mathematically exact two-level shell-wheel and quotient-wheel picture?
10. What is the narrowest remaining theorem needed to rule out a fully covered gnomon shell?

End with exactly one judgment:

Outcome A - SQUARE-ANCHORED RESIDUE/CENSUS OBSTRUCTION FOUND
Outcome B - COUNTEREXAMPLE PACKET COMPLETE, TRANSITION LEVERAGE PARTIAL
Outcome P - PRECISE CRT/OWNER BRIDGE REMAINS
Outcome C - COMBINED VIEWS ARE EQUIVALENT BOOKKEEPING ONLY
