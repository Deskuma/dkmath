# Instruction 016 — Legendre gnomon / primorial residue-cover counterexample packet

## Mission

Continue from Instruction 015, but change viewpoint.

The current Legendre development already has two independently strong descriptions of the same square shell:

1. **residue / primorial-wheel side**
   - `SquareOffsetCovered n r`
   - `squareAnchorForbiddenResidue n q`
   - `PrimorialWheelBridge`
   - projected wheel survivor / reservation semantics;

2. **sqrt-rough factorization side**
   - exact support strata;
   - complete factorization census
     [
       R = U + Cube + Cross + Repeated + Triple;
     ]
   - corrected quotient conservation
     [
       Qtotal = Cross + Cube + 2,Repeated + 3,Triple + Rejected.
     ]

Instruction 016 should not add another ad-hoc capacity argument first.

Its primary task is to formalize the **counterexample object itself**:

> If a Legendre counterexample shell existed, then every gnomon seat would be covered by a bounded-prime forbidden residue, there would be no projected primorial-wheel survivor, the sqrt-rough zero stratum would vanish, and the complete factorization / quotient conservation identities would hold simultaneously.

Build the exact bridge and then let the implementation search for a new obstruction in that combined state.

The desired result is not predetermined. A precise negative result or a new invariant is acceptable.

---

## Important gnomon indexing audit

Do not blur three different quantities.

For anchor (n):

- consecutive-square difference:
  [
    (n+1)^2-n^2 = 2n+1;
  ]
- the open Legendre shell contains only offsets
  [
    1le rle 2n,
  ]
  because the final (+1) point is ((n+1)^2), a square boundary;
- the next outward gnomon has size
  [
    (n+2)^2-(n+1)^2 = 2n+3.
  ]

Thus the odd gnomon states form

[
  2n-1,quad 2n+1,quad 2n+3,
]

with successor law (G(n+1)=G(n)+2), while the prime-search interior has (2n) seats.

Audit existing `DkMath.Gnomon.oddGnomon`, `squareOffsets`, `GnomonSuccessor`, and `GnomonSupportTurnover` and preserve their current indexing.

If useful, add a small neutral theorem packet exposing:

[
  oddGnomon(n+1)=oddGnomon(n)+2
]

and the relation between the odd gnomon cardinality and the open-shell seat count.

Do not redefine existing gnomon vocabulary merely to change notation.

---

## Required source audit

Audit at minimum:

```text
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
```

Also inspect any existing CRT / finite prime-basis / primorial product declarations before introducing new residue-vector abstractions.

Record exact reusable theorem names in the source inventory.

---

## Phase 1 — exact residue-cover fibers on the gnomon shell

For each bounded prime (qle n), expose the finite shell fiber

[
  CoverFiber(n,q)
  =
  {rin squareOffsets(n):
       rmod q = squareAnchorForbiddenResidue(n,q)}.
]

Prefer a definition as a filter of existing `squareOffsets n`.

Prove exact membership equivalence to

[
  qmid n^2+r.
]

Use `squareOffsetForbiddenBy_iff_mod_eq_forbiddenResidue`; do not reprove modular arithmetic.

Then prove

[
  coveredSquareOffsets(n)
  =
  igcup_{qin primeScalesUpTo(n)} CoverFiber(n,q)
]

in a suitable Finset form.

This is the explicit "overlay the prime residue classes on the gnomon" theorem.

---

## Phase 2 — full-cover equivalence as a residue-class cover

Prove an exact theorem:

[
SquareOffsetsFullyCovered(n)
iff
squareOffsets(n)
=
igcup_{qle n, q prime} CoverFiber(n,q).
]

A pointwise equivalent form is also useful:

[
orall rin squareOffsets(n),;
exists qin primeScalesUpTo(n),;
rmod q = forbiddenResidue(n,q).
]

This should be a rewrite of existing semantics, not a new conjecture.

---

## Phase 3 — wheel image of the whole square shell

Using the existing prime basis

[
S_n = primeScalesUpTo(n)
]

and period

[
M_n = finitePrimeBasisProduct(S_n),
]

define the finite projected shell image if no equivalent object already exists:

[
  ShellWheelImage(n)
  =
  { squareShellWheelProjection(S_n,n,r):
       rin squareOffsets(n)}.
]

Prove:

- each projected seat is obtained by advancing the square-anchor coordinate by (r) modulo (M_n);
- full cover iff every projected shell point is reserved;
- failure of full cover iff the image contains a wheel survivor.

Reuse `not_squareOffsetCovered_iff_projection_survivor`.

Do not assume the projection is injective.

---

## Phase 4 — projection multiplicity / injectivity audit

Determine exactly when

[
rmapsto squareShellWheelProjection(S_n,n,r)
]

is injective on (1le rle2n).

A sufficient condition is expected to be

[
2n < M_n
]

or a nearby non-wrapping condition.

Prove the strongest clean statement available.

Then audit finite thresholds:

- (n=2,3,4);
- the first (n) from which the primorial period exceeds the shell width;
- prime-threshold and composite-threshold transitions.

Do not assume a global inequality without proof.

If the map is not injective in small cases, preserve the exact collisions.

---

## Phase 5 — canonical residue-cover owner

Under a covered seat, there may be several covering primes.

Define, if useful, a canonical cover owner using the least actual support prime, or reuse an existing canonical support-prime mechanism if it applies without changing semantics.

Target packet for a covered square offset (r):

[
owner(n,r)=q
]

with

- (q) prime;
- (qle n);
- (qmid n^2+r);
- (rmod q=forbiddenResidue(n,q));
- (q) is minimal among covering primes.

Then obtain a disjoint owner-fiber partition of the covered shell.

This is optional if an existing canonical owner already supplies the same object exactly.

Do not duplicate the sqrt-rough canonical-root ledger.

---

## Phase 6 — counterexample packet

Create one production theorem / structure / theorem bundle for the hypothesis

[
hfull : SquareOffsetsFullyCovered(n).
]

For (n>0), derive simultaneously:

1. every shell seat has nonempty old-prime support;
2. the projected primorial-wheel shell has no survivor;
3. `paritySafeUncoveredCandidates n = ∅`;
4. the sqrt-rough zero stratum has cardinality (0);
5. the complete sqrt-rough census collapses to
   [
     R = Cube + Cross + Repeated + Triple;
   ]
6. corrected quotient conservation remains
   [
     Qtotal
     =
     Cross + Cube + 2Repeated + 3Triple + Rejected;
   ]
7. hence the counterexample balance
   [
     Qtotal
     =
     R + Repeated + 2Triple + Rejected.
   ]

Prefer additive Nat-safe equalities.

This packet is a necessary-condition package for a hypothetical counterexample, not a proof that one exists.

---

## Phase 7 — exact converse where valid

Audit which parts of the counterexample packet are actually equivalent to full cover.

In particular:

- (U=0) on the parity-safe / sqrt-rough carrier may be equivalent to full cover only under explicit positivity and carrier hypotheses;
- "no projected wheel survivor in the whole square shell" should be equivalent to full cover for (nge2);
- the numerical balance alone may be weaker.

Prove equivalences only when exact.

Record implications that are one-way only.

---

## Phase 8 — residue-cover / factorization-type map

For each covered sqrt-rough seat, connect:

[
	ext{canonical residue owner prime}
]

to its factorization type:

- Cube (p^3);
- Cross (pq);
- Repeated (p^2q) or (pq^2);
- Triple (pqs).

Determine whether the residue owner is:

- the repeated prime;
- the least support prime;
- any support prime;
- or type-dependent.

Do not guess a universal owner rule.

Produce exact owner/type packets and preserve the smallest counterexample to any false simple rule.

---

## Phase 9 — CRT / primorial state formulation

The existing wheel projection modulo

[
M_n=prod_{ple n}p
]

already encodes all bounded-prime residues.

Investigate whether a hypothetical full-cover shell can be expressed as a finite CRT state:

[
a_n = n^2 mod M_n,
]

with interval positions

[
a_n+1,ldots,a_n+2n pmod{M_n}
]

all reserved by at least one prime basis coordinate.

Formalize the exact theorem if supported:

[
SquareOffsetsFullyCovered(n)
iff
orall rin[1,2n],;
ReservedByPrimeBasis(S_n,a_n+r)
]

with modular projection handled correctly.

This is the square-anchored wheel-cover statement.

Do not replace it by an arbitrary Jacobsthal/max-gap assertion.

---

## Phase 10 — square-anchor restriction versus generic wheel gaps

Define, only if useful, a square-anchored local gap/escape predicate rather than a global Jacobsthal function.

The relevant question is not:

> does the primorial wheel contain any run of (2n) reserved residues?

but:

> does the run starting at the specific square-anchor state (a_n=n^2mod M_n) contain (2n) reserved residues?

If a compact finite predicate helps, introduce something like:

[
SquareAnchorWheelFullyReserved(n).
]

Prove it equivalent to `SquareOffsetsFullyCovered n`.

Do **not** claim or implement a general Jacobsthal bound unless it is genuinely needed by the discovered proof.

---

## Phase 11 — gnomon successor transport

Use the exact square-anchor successor law

[
a_{n+1}
=
a_n+(2n+1)
pmod{M}
]

for a fixed old basis, and the existing fresh-prime wheel enlargement when (n+1) is prime.

Combine with `GnomonSupportTurnover`:

- lower reindexed common support is controlled by divisors of (2n+1);
- upper common support by divisors of (2(n+1));
- at a prime threshold the upper common old support is only (2).

Search for a theorem saying that a hypothetical full-cover state at (n) and/or (n+1) imposes a rigid residue-owner transition.

Do not assume full cover propagates or fails to propagate.

A precise transition obstruction is a valid outcome.

---

## Phase 12 — three consecutive odd gnomons

Make the local geometric state explicit if it helps:

[
G_{n-1}=2n-1,quad
G_n=2n+1,quad
G_{n+1}=2n+3.
]

Investigate whether the support-turnover equations across (n-1	o n	o n+1) yield a finite incompatibility for full cover.

Possible signals:

- a residue owner must persist across shells but can persist only if it divides the corresponding gnomon displacement;
- prime-threshold transitions reduce upper persistence to (2);
- lower persistence forces divisors of the odd gnomon.

Do not infer a contradiction from parity alone.

Formalize only exact persistence statements.

---

## Phase 13 — Primorial / sqrt-Primorial address audit

This phase is exploratory and must not block the core counterexample packet.

Let

[
M_n = finitePrimeBasisProduct(primeScalesUpTo(n)).
]

Audit the integer neighborhood of

[
sqrt{M_n}.
]

Possible finite definitions:

[
a=lfloorsqrt{M_n}floor,
quad
L=M_n-a^2,
quad
U=(a+1)^2-M_n.
]

Prove only elementary identities such as

[
L+U=2a+1
]

when (M_n) is not itself a square.

Compare the gnomon address of (M_n) with the Legendre anchor (n) and with the wheel period.

The purpose is to see whether the primorial body has a useful square-shell address; no relevance to Legendre should be asserted without a proved bridge.

Also audit any existing Primitive / PrimorialUniverse "primitive prime product" objects before inventing a new primitive primorial.

---

## Phase 14 — search for the first genuinely new obstruction

After the exact counterexample packet exists, let Codex search structurally for one of the following:

### A. residue-cover impossibility
A theorem showing the square-anchored length-(2n) run cannot be fully reserved.

### B. owner-transition impossibility
A successor / three-gnomon theorem incompatible with full cover.

### C. census-residue incompatibility
The residue-owner partition cannot realize the required
Cube/Cross/Repeated/Triple counts under the counterexample balance.

### D. primorial-period incompatibility
The square-anchor orbit and wheel enlargement prevent the necessary cover pattern.

### E. corrected negative result
None of the above yields new leverage; identify the exact missing theorem.

Search is encouraged. Do not manufacture a desired conclusion.

---

## Phase 15 — finite counterexample-pattern search

For a bounded range compatible with runtime, enumerate the **necessary residue-cover pattern**, not merely prime existence.

For each (n), record:

- square anchor wheel coordinate;
- primorial period (M_n);
- shell width (2n);
- number of projected shell survivors;
- canonical cover-owner fiber sizes;
- support-overlap distribution;
- if full cover is impossible, the first escaping offset;
- counterexample-balance quantities (R,Repeated,Triple,Rejected,Qtotal) when available.

Search specifically for near-miss shells with the fewest survivors.

These are the best stress tests for any proposed structural obstruction.

Do not infer asymptotics.

---

## Phase 16 — relation to the current rejection / small-prime wheel

Instruction 015's `Rejected` term detects quotient values having a prime factor

[
ulesqrt n.
]

Compare this with the shell-level primorial residue cover by primes (ple n).

Prove the exact map or separation:

- shell residue cover acts on (n^2+r);
- quotient rejection acts on the complementary quotient (q).

Determine whether a two-level wheel picture is mathematically exact:

[
	ext{shell wheel at }ple n
quad	ext{and}quad
	ext{quotient wheel at }ulesqrt n.
]

Do not identify the two reservations without a theorem.

A clean two-level reservation diagram would be valuable even without a new prime theorem.

---

## Phase 17 — candidate contradiction theorem contract

At the end, state exactly one next theorem which, if proved, would rule out full cover.

Preferred examples:

[
SquareAnchorWheelFullyReserved(n)	o False,
]

under a clearly stated structural hypothesis already proved for all (n), or

[
hfull
	o
	ext{counterexample invariant}
	o
	ext{numerical/structural contradiction}.
]

If no unconditional contract is yet supported, state the narrowest missing provider.

Do not hide a prime-distribution assumption inside a helper theorem.

---

## Calibration / regressions

At minimum preserve and connect:

- existing wheel regression (n=4), basis ({2,3});
- the rejected quotient counterexample (n=11,p=5,q=27);
- one repeated-support multiowner case;
- one triple-support case;
- the structural endpoint (n=1031);
- at least one near-miss shell from the new bounded residue-cover search.

If the new packet proves only equivalences/reductions, calibrate those exact objects rather than forcing a new prime endpoint.

---

## Possible outcomes

### Outcome A — square-anchored residue/census obstruction found

The counterexample packet is complete and a new exact incompatibility rules out a nontrivial class of hypothetical full covers or yields new unconditional square-cell prime endpoints.

### Outcome B — counterexample packet complete, transition leverage partial

Residue cover, wheel, census, quotient, and successor statements are unified exactly, but no uniform contradiction is obtained.

### Outcome P — one precise CRT/owner bridge remains

The necessary counterexample conditions are formalized, but one explicit residue-owner or successor transport theorem blocks the combined obstruction.

### Outcome C — combined views are equivalent bookkeeping only

The new maps add no structural leverage beyond existing full-cover / wheel / census equivalences. Preserve the exact equivalence theorem and identify the next genuinely arithmetic provider.

---

## Non-goals

Do not claim:

- Legendre's conjecture;
- a generic Jacobsthal bound;
- PNT/RH;
- Bertrand;
- analytic sieve estimates;
- random/equidistribution heuristics as proof;
- FLT/ABC consequences.

Do not build a new CRT framework if the existing primorial wheel projection already supplies the needed state.

Do not conflate:

- odd gnomon size (2n+1);
- open shell seat count (2n);
- successor odd gnomon (2n+3).

Do not replace exact shell anchoring by an arbitrary wheel interval.

Do not use `sorryAx`-bearing endpoints in production.

---

## Implementation guidance

A focused module split is reasonable, for example:

```text
DkMath/NumberTheory/Legendre/GnomonResidueCover.lean
DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean
DkMath/NumberTheory/Legendre/GnomonPrimorialTransition.lean
```

Use the existing `PrimorialWheelBridge` as the wheel dictionary and the existing sqrt-rough census / quotient conservation as the arithmetic dictionary.

If the counterexample packet can be expressed cleanly as theorems rather than a structure, prefer theorem bundles over a large record.

---

## Validation

For all new production declarations:

- focused builds;
- `lake build DkMath.NumberTheory.Legendre`;
- `lake build DkMath`;
- forbidden-token scan;
- `#print axioms` for every new public declaration;
- `git diff --check`.

All new production declarations must remain free of `sorryAx`.

Preserve the existing file-header and import-adjacent

```lean
#print "file: ..."
```

conventions.

---

## Durable checkpoint protocol

Update findings after:

- gnomon indexing audit;
- explicit residue-cover fibers;
- full-cover / union equivalence;
- whole-shell wheel image;
- projection injectivity threshold;
- counterexample packet;
- residue-owner partition;
- square-anchor CRT formulation;
- successor / three-gnomon transition search;
- two-level shell/quotient wheel comparison;
- near-miss finite search;
- final A/B/P/C judgment.

Preserve false conjectures and smallest counterexamples.

---

## Final report

Answer explicitly:

1. What exact residue-class cover theorem describes `SquareOffsetsFullyCovered n`?
2. How is the whole shell represented in the primorial wheel?
3. When is the shell projection injective, and what are the small exceptions?
4. What exact necessary-condition packet does a hypothetical Legendre counterexample satisfy?
5. Which parts of that packet are equivalent to full cover and which are only consequences?
6. How do residue-cover owners relate to Cube/Cross/Repeated/Triple factorization types?
7. What exact square-anchor CRT / wheel-cover formulation was proved?
8. Does the (2n-1,2n+1,2n+3) successor geometry impose any new support-transition obstruction?
9. Is there a mathematically exact two-level shell-wheel / quotient-wheel picture?
10. What is the narrowest remaining theorem needed to rule out a fully covered gnomon shell?

End with exactly one judgment:

```text
Outcome A — SQUARE-ANCHORED RESIDUE/CENSUS OBSTRUCTION FOUND
Outcome B — COUNTEREXAMPLE PACKET COMPLETE, TRANSITION LEVERAGE PARTIAL
Outcome P — PRECISE CRT/OWNER BRIDGE REMAINS
Outcome C — COMBINED VIEWS ARE EQUIVALENT BOOKKEEPING ONLY
```
