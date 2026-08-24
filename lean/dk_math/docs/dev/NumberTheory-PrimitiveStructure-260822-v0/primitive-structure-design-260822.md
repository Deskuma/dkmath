# DkMath Primitive Structure — Architecture Design

Date: 2026-08-22

Last synchronized: 2026-08-24

Status: implemented architecture through PRIM-C002 / PRIM-L022

## 1. Design objective

The objective is to expose a reusable Primitive Structure without making any
single conjecture the owner of the abstraction.

The project still follows the original dependency direction:

```text
CosmicFormula / generic algebraic identities
                ↓
NumberTheory Primitive Structure
                ↓
finite prime-world / residue / valuation observers
                ↓
application geometry
                ↓
Legendre / ABC / FLT / RH / Erdos / Pascal / Collatz
```

Legendre remains the first application, not the owner of the Primitive layer.
The project has now passed the initial architecture phase and has a substantial
Lean implementation.  This document records the architecture that actually
emerged from those proofs.

The central design rule remains:

> Put identities at the highest algebraic layer.  Add order, discreteness,
> divisibility, primality, residue structure, and application geometry only in
> lower layers.

## 2. Layer A — algebraic Cosmic source

The highest layer contains no primality or order assumptions.

For square degree,

$$
(x+u)^2=x(x+2u)+u^2.
$$

The unit-one specialization is

$$
(P+1)^2=P(P+2)+1.
$$

The generic DkMath source remains

$$
(x+u)^d=x\,GN_d(x,u)+u^d.
$$

Primitive and Legendre modules do not redefine `GN`, `Big`, `Body`, or `Gap`.
They specialize existing CosmicFormula identities only where arithmetic order
or divisibility becomes relevant.

The variable `u` must not be conflated with the natural-number unit `1` at the
algebraic layer.  The current Legendre application intentionally works in the
unit-one specialization; later finite-difference or variable-unit work belongs
above the Legendre-specific modules.

## 3. Layer B — Primitive support semantics

The natural-number finite-support specialization now uses three distinct
notions:

```text
PrimeScaleGeneratedBy S n
FreshPrimeDirection S n q
SupportDisjointFrom S n
```

They answer different questions.

### 3.1 Generated world

`PrimeScaleGeneratedBy S n` means every prime divisor of `n` belongs to `S`.
All multiplicative support is already explained by the old world.

### 3.2 Fresh direction

`FreshPrimeDirection S n q` means `q` is a prime divisor of `n` and `q ∉ S`.
At least one new direction is visible.

### 3.3 Support disjointness

`SupportDisjointFrom S n` means no prime divisor of `n` belongs to `S`.
All old directions are absent.

These notions must never be collapsed:

```text
FreshPrimeDirection
  some new direction exists

SupportDisjointFrom
  every old direction is absent

PrimeScaleGeneratedBy
  every direction is old
```

A number may contain both old and fresh directions.

## 4. Layer C — four Primitive coordinates

The public conceptual API is still organized around four orthogonal
coordinates.

### C1. Direction

Which base-prime direction is present, known, fresh, or absent?

Primary owners include the StructuralArithmetic PrimitiveDirection API and the
new Primitive finite-world modules.

### C2. Depth

How deep does a fixed prime direction occur?

The canonical ray is

$$
p,p^2,p^3,\ldots,p^k.
$$

Depth is valuation/exponent information and is not the same as distinct support.
The Legendre obstruction layers deliberately keep these separate.

### C3. Origin

Where did a direction first become visible?

`PrimitiveBeam` continues to own first-occurrence semantics across difference
powers.  Finite-world freshness is not identified with Zsigmondy or
`PrimitiveBeam` origin.

### C4. Mass

How much arithmetic load belongs to a direction?

Examples include valuation depth, radical support, valuation excess, and
logarithmic / von-Mangoldt-style channel costs.

A later parity layer may use the Depth coordinate, but parity is not currently
part of the Primitive core theorem surface.

## 5. Layer D — generic natural-number square Body

The generic square Body is

$$
\operatorname{squareBody}(P)=P^2+2P=(P+1)^2-1.
$$

This layer is independent of Legendre.

### 5.1 Composite-detection closure

For a composite `m` with

$$
1<m\le P^2+2P,
$$

there is a prime divisor `q ≤ P`.

Consequently, if every prime divisor at most `P` is absent, then `m` is prime.
This is the generic bridge from bounded support escape to primality.

### 5.2 Unique-fresh theorem inside the square Body

PRIM-C001 strengthened the square Body from a mere prime-closure region to a
factor-normal-form region.

For a positive point `m ≤ squareBody P`, any prime divisor `ℓ > P` satisfies:

```text
ℓ is the unique fresh prime direction above P;
ℓ^2 does not divide m;
m = ℓ * (m / ℓ);
ℓ is coprime to m / ℓ;
all prime support of m / ℓ lies in primeScalesUpTo P.
```

Two distinct primes greater than `P` cannot both divide such an `m`, because
their product would already reach `(P+1)^2`.

### 5.3 Bounded fresh cofactor

PRIM-C002 sharpened the cofactor itself:

$$
0<k=\frac m\ell\le P.
$$

Thus every positive square-Body point has the exact finite-world alternative

```text
old-generated
or
unique fresh prime ℓ > P × small old-generated cofactor k ≤ P.
```

The old support transfers exactly to the small cofactor.  For every old prime
`q ≤ P`, under the fresh split,

$$
q\mid m\iff q\mid k.
$$

Moreover,

```text
m prime      ↔ k = 1
m composite  → 2 ≤ k ≤ P
```

This `small × unique-fresh` normal form is now a central Primitive theorem, not
a Legendre-local observation.

## 6. Layer E — finite prime worlds and periodic observers

The Primitive implementation now contains a concrete finite-prime observer
stack:

```text
FinitePrimeWorld
PeriodicPrimeWorld
PrimeWorldRefinement
PHZ30
PrimeWorldResidues
PrimeWorldCardinality
EulerTotientBridge
```

The semantic separation is:

```text
Primitive support semantics
        ↓
finite prime world
        ↓
periodic prime-wave observer
        ↓
residue/cardinality/totient coordinates
```

A wheel survivor is only a candidate relative to the observer.  It becomes a
certified prime only when it is additionally placed inside an arithmetic region
such as the square Body where bounded composite detection is valid.

Prime-world refinement has an exact child-seat interpretation: adding a fresh
prime direction reserves one child phase and leaves the other `q-1` phases.
The resulting residue cardinality is expressed both as a product of `(p-1)`
and through Euler's totient.

## 7. Layer F — exact Legendre reduction

For positive `n`, a square-cell point is written

$$
m=n^2+r,\qquad 1\le r\le2n.
$$

The old finite world is

```text
primeScalesUpTo n = { prime q | q ≤ n }.
```

A prime `q ≤ n` covers the offset `r` when

$$
q\mid n^2+r.
$$

The current facade proves the exact frontier

$$
\operatorname{LegendreConjecture}
\iff
\forall n>0,\;\neg\operatorname{SquareOffsetsFullyCovered}(n).
$$

Equivalently, Legendre is exactly the assertion that every square shell has at
least one offset whose point is support-disjoint from all old prime directions.
The project does not assume or hide this provider.

## 8. Layer G — local wave and obstruction geometry

After the exact reduction, the application was developed as finite arithmetic
rather than by analytic prime estimates.

### 8.1 Exact waves and carry

For a modulus `m`, the square-wave hit count is exact:

$$
|\operatorname{squareWaveOffsets}(n,m)|
=
\left\lfloor\frac{n^2+2n}{m}\right\rfloor
-
\left\lfloor\frac{n^2}{m}\right\rfloor.
$$

It is decomposed into a baseline plus a deterministic `0/1` carry.  Carry is a
boundary correction, not a probability.

### 8.2 Pair overlap

Distinct old prime directions are tracked by unordered pair multiplicity.
Near and far pairs are split by the product threshold.  The pair ledger counts
distinct direction pairs, not valuation depth.

### 8.3 Anchor-divisor split and coprime packets

Prime directions dividing the anchor `n` are separated from nondivisor
directions.  On coprime offsets, divisor directions disappear completely.

The canonical coprime window contains exactly

$$
2\varphi(n)
$$

seats and splits into `φ(n)` packets

$$
(r,n+r).
$$

The old nondivisor supports of the two packet sides are disjoint.

### 8.4 Quotient geometry

Selecting an old support prime `p ≤ n` gives

$$
p\,Q=n^2+r,
$$

with `Q > n`.  Quotient collisions from distinct selected primes are rigid;
for `n ≥ 4` the global quotient projection is injective on the relevant
incidences.

PRIM-L015/L016 identify the exact quotient obstruction:

```text
Q is prime
↔ selected old support is singleton
   and p^2 does not divide the square point.
```

Thus distinct support and selected-prime depth are the two ways the large
quotient can remain composite.

## 9. Layer H — localized obstruction and packet coupling

### 9.1 Seat partition

Covered coprime seats are partitioned into three disjoint classes:

```text
simple/fresh
singleton-depth
multi-support
```

The corresponding cardinality identity is exact under full cover.

### 9.2 Localized ledgers

Depth and pair budgets were then restricted to the same coprime/nondivisor
region as the seat classification.  This removes global overcount without
claiming a contradiction.

### 9.3 Packet cross pairs

A packet is treated as a two-seat object.  Left and right old supports are
disjoint, and the ordered cross-pair count transposes exactly to

$$
\sum_r |A_r|\,|B_r|.
$$

For a fixed ordered pair `(p,q)`, two packet hits force `p*q` to divide the
representative difference.  Since the base packet window has length `n`,

$$
n<pq
$$

implies that the ordered pair hits at most one packet.

### 9.4 Full factor rectangle

For a coprime packet, the two square points themselves are coprime.  Hence all
prime factors on opposite sides are separated, not merely the old support.

Writing

$$
p a=n^2+r,
$$

$$
q b=n^2+n+r,
$$

gives the exact rectangle relation

$$
p a+n=q b,
$$

with cross-side coprimality.

Modulo the anchor,

$$
p a\equiv q b\equiv r\pmod n,
$$

and all four factors are coprime to `n`.  This is the current reduced-residue
factor rectangle.

## 10. Layer I — small-cofactor / quotient duality

PRIM-L022 connects the generic C002 factorization to the Legendre quotient
factorization.

Fix a coprime square seat with a fresh split

$$
\ell k=n^2+r,
$$

where

$$
\ell>n,
\qquad
0<k\le n.
$$

The small cofactor returns to the canonical base packet:

```text
k ∈ squareAnchorCoprimeBaseOffsets n.
```

If an old support prime `p ≤ n` is selected, then

$$
p\mid k.
$$

The large Legendre quotient therefore has the dual normal form

$$
\operatorname{squareOffsetSupportQuotient}(n,p,r)
=
\ell\left(\frac{k}{p}\right).
$$

This compresses PRIM-L016 to

$$
Q\text{ prime}
\iff
k=p.
$$

Equivalently,

```text
singleton old support + selected-prime depth one
↔ the entire bounded old cofactor is exactly p.
```

Under full cover, each coprime seat is now known to satisfy the necessary
normal form

```text
old-generated
or
unique fresh ℓ > n × nontrivial small cofactor 2 ≤ k ≤ n.
```

The old-generated branch remains a genuine branch and is not eliminated.

## 11. Current module ownership

The implemented Primitive core is currently centered on:

```text
DkMath/NumberTheory/Primitive/
  FinitePrimeWorld.lean
  PeriodicPrimeWorld.lean
  PrimeWorldRefinement.lean
  PHZ30.lean
  PrimeWorldResidues.lean
  PrimeWorldCardinality.lean
  EulerTotientBridge.lean
  SquareBody.lean

DkMath/NumberTheory/Primitive.lean
```

The Legendre application has been decomposed into application-owned layers:

```text
DkMath/NumberTheory/Legendre/
  Basic.lean
  Wave.lean
  PairOverlap.lean
  CoprimePacket.lean
  Quotient.lean
  QuotientSupport.lean
  Obstruction.lean
  LocalizedObstruction.lean
  PacketCross.lean
  PacketCoprimality.lean
  PacketUnitResidue.lean
  SmallCofactor.lean
  Frontier.lean
  Internal/PairCombinatorics.lean

DkMath/NumberTheory/Legendre.lean
```

`Legendre.lean` remains a thin historical facade.  Generic theorems discovered
from the application are promoted only when their theorem ownership is truly
Primitive-generic, as happened with PRIM-C001/C002 in `SquareBody.lean`.

## 12. Next structural frontier

The project has not proved the universal square escape provider.  The remaining
frontier is not another missing rewrite of the Legendre statement.

The current finite information includes:

```text
old/fresh support
valuation depth
localized overlap
coprime packet separation
cross-factor rectangle
reduced-residue coordinates
small × unique-fresh normal form
```

A likely next research phase is to retain prime-power parity information rather
than discard exponent depth after support detection.  For a prime direction
with finite valuation `v`, the prospective normalization is

$$
v=2j+\varepsilon,
\qquad
\varepsilon\in\{0,1\}.
$$

Here `j` records complete two-layer packets and `ε` is a terminal parity gap.
Existing DkMath `padicValNat`, exponent-slot, and half-phase APIs should be
reconnoitered before introducing any new abstraction.

This is a candidate information-preservation layer, not a claim that the
classical sieve parity problem has been solved.

A second independent research route remains the finite-difference viewpoint:
keep a nonzero unit/difference parameter before extracting invariants, rather
than setting the discrete step to zero prematurely.  That route should remain
above or beside the current exact unit-one Legendre application until a genuine
bridge theorem is identified.

## 13. Non-goals and hard boundary

The following remain explicit non-goals of the current implementation:

- no proof of Legendre's conjecture;
- no hidden provider asserting a support-free square seat;
- no elimination of the old-generated branch;
- no claim that finite-world freshness is Zsigmondy/PrimitiveBeam origin;
- no third-order inclusion-exclusion merely by escalation;
- no analytic PNT/Mertens/prime-gap input in the current finite route;
- no RH/CFBRC dependency in Primitive core;
- no category-theory layer before concrete map/naturality needs appear;
- no claim that retaining valuation parity alone distinguishes primes from all
  odd-`Ω` composites.

The architecture remains successful only if every new theorem says exactly
what new information Lean certified and keeps conjecture-equivalent providers
visible at the application frontier.
