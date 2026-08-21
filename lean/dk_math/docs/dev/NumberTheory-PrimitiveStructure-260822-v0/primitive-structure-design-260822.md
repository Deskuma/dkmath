# DkMath Primitive Structure — Architecture Design

Date: 2026-08-22

Status: design / documentation phase

## 1. Design objective

The objective is to expose a reusable Primitive Structure without making any
single conjecture the owner of the abstraction.

The project starts from two facts already present in DkMath:

1. Cosmic Formula identities are algebraic and are not intrinsically about
   primes or even natural numbers.
2. Several NumberTheory subprojects already encode different aspects of
   primitive arithmetic information: fresh prime directions, first occurrence
   in difference powers, exponent depth, valuation mass, and finite escape.

Legendre's conjecture is chosen as the first application because a
consecutive-square window supplies a particularly sharp bridge from support
escape to primality.

## 2. Layer A — algebraic Cosmic source

The highest layer must contain no primality or order assumptions.

For a suitable commutative semiring, the square family is

$$
\operatorname{Big}_2(x,u)=(x+u)^2,
$$

$$
\operatorname{Gap}_2(u)=u^2,
$$

$$
\operatorname{Body}_2(x,u)=x(x+2u),
$$

with

$$
\operatorname{Big}_2(x,u)=\operatorname{Body}_2(x,u)+\operatorname{Gap}_2(u).
$$

The unit-one specialization is

$$
(P+1)^2=P(P+2)+1.
$$

The generic DkMath source is the higher-degree identity

$$
(x+u)^d=x\,GN_d(x,u)+u^d.
$$

### Design requirement A1

Do not define a new Legendre-local version of `GN`, `Big`, `Body`, or `Gap`.
Use existing CosmicFormula definitions and prove only thin specializations or
bridges when a missing API is identified.

### Design requirement A2

Prepare algebraic map-compatibility lemmas before any future category-theory
layer is attempted.

The desired pattern is conceptually:

```text
map Big  = Big of mapped inputs
map Body = Body of mapped inputs
map Gap  = Gap of mapped inputs
map GN   = GN of mapped inputs
```

These lemmas are the practical naturality certificates needed for later
abstraction.

### Design requirement A3 — unit transport

For square degree, if `x = u*y`, then

$$
(uy+u)^2=u^2(y+1)^2,
$$

$$
uy(uy+2u)=u^2y(y+2).
$$

Hence the `u`-world is a scaled image of the normalized unit-one world whenever
such a factorization is available.  This transport should remain algebraic and
must not be tied to natural-number divisibility.

## 3. Layer B — Primitive semantics

Primitive Structure is not identified with one theorem such as Zsigmondy or
Euclid escape.  It is a vocabulary for describing what information is new
relative to a known world.

For the natural-number prime-support specialization, the existing notions are:

```text
KnownPrimeScales S
PrimeScaleGeneratedBy S n
FreshPrimeDirection S n q
```

The project adds a missing dual viewpoint:

```text
SupportDisjointFrom S n
```

with intended semantics:

```text
n != 0
and every prime divisor q of n satisfies q ∉ S
```

The exact final Lean name is intentionally not fixed during documentation.
The important point is the logical separation.

### 3.1 Generated world

`PrimeScaleGeneratedBy S n` means every prime divisor of `n` belongs to `S`.

This answers:

> Is all multiplicative support already explained by the old world?

### 3.2 Fresh direction

`FreshPrimeDirection S n q` means one prime divisor `q` lies outside `S`.

This answers:

> Is there at least one new direction?

### 3.3 Support disjointness

`SupportDisjointFrom S n` should mean no prime divisor of `n` belongs to `S`.

This answers:

> Have all old directions disappeared?

The implications are intentionally asymmetric:

```text
SupportDisjointFrom + n > 1
  → some fresh direction exists

FreshDirection
  ↛ SupportDisjointFrom
```

The second non-implication is essential.  A number can contain both old and new
prime directions.

## 4. Layer C — the four Primitive coordinates

The public conceptual API is organized around four orthogonal questions.

### C1. Direction

Which base prime direction is present, known, or fresh?

Primary current assets:

```text
StructuralArithmetic.PrimitiveDirection
Hackathon.FinitePrimeEscape
StructuralArithmetic.FinitePrimeEscapeBridge
```

### C2. Depth

How many exponent slots exist above a fixed base prime?

The canonical model is

$$
p,p^2,p^3,\ldots,p^k.
$$

Primary current assets include the `PrimitiveSet.FullExponentSlot` family and
other prime-power channel APIs.

### C3. Origin

At which structural boundary or degree did the direction first appear?

For difference powers the current model is
`PrimitiveBeam.PrimitivePrimeFactorOfDiffPow`.
A primitive prime witness is absent from all lower difference powers, cannot
come from the first boundary `a-b`, and therefore appears on the `GN` / Beam
side of

$$
a^d-b^d=(a-b)\,GN_d(a-b,b).
$$

### C4. Mass

How much arithmetic load is carried by that direction?

Examples include:

```text
padic valuation
factorization exponent
radical support
valuation excess
log / von-Mangoldt-style channel cost
```

Direction existence and direction mass must not be conflated.

## 5. Layer D — generic natural-number square Body

The first important arithmetic theorem suggested by the project does **not**
need primorials.

Let `P : ℕ`.  The unit-one square Body is

$$
B(P):=P^2+2P=(P+1)^2-1.
$$

For any composite `m` satisfying

$$
1<m\le B(P),
$$

there exists a prime divisor `q` with

$$
q\le P.
$$

Reason: a composite `m < (P+1)^2` has a prime divisor at most `sqrt(m)`, hence
strictly below `P+1`.

This gives the key closure principle:

$$
1<m\le P^2+2P
$$

and

$$
\forall q\le P,\ q\text{ prime}\Rightarrow q\nmid m
$$

imply

$$
m\text{ prime}.
$$

This theorem is a major bridge between the generic Cosmic Body and Primitive
support semantics.

### Sharp boundary when `P+1` is prime

If `P+1` is prime, then

$$
(P+1)^2
$$

is composite but has no prime divisor at most `P`.  Therefore the Body endpoint

$$
P^2+2P
$$

is sharp for the `≤ P` composite-detection world.

This explains the examples

$$
30^2+2\cdot30=960,
$$

with the next point

$$
961=31^2,
$$

and

$$
210^2+2\cdot210=44520,
$$

with the next point

$$
44521=211^2.
$$

No primorial hypothesis is required for the closure theorem itself.  A
primorial or wheel becomes relevant only when one chooses a periodic residue
observer for the bounded prime directions.

## 6. Layer E — finite prime worlds and PHZ observers

A finite prime world chooses a finite set of base prime directions and observes
which integer positions they reserve by divisibility.

A primorial or wheel modulus is one convenient periodic coordinate system, not
the definition of Primitive Structure.

For example the base set `{2,3,5}` has period `30` and the unreserved residue
classes

$$
1,7,11,13,17,19,23,29\pmod{30}.
$$

These positions are **candidates relative to the current observer**, not
intrinsically prime positions.

As further prime directions are learned, their multiples reserve additional
positions.  The observer can remain on a convenient base coordinate system
while the active set of prime waves grows.

### Design separation

```text
Primitive Structure
  abstract support / direction / depth / origin / mass

Finite prime world
  finite natural-number specialization

PHZ
  periodic residue-wave observer of that finite world
```

The PHZ layer must therefore depend on Primitive semantics, not the reverse.

## 7. Layer F — Legendre first application

For positive `n`, define the open consecutive-square shell by

$$
n^2<m<(n+1)^2.
$$

Equivalently,

$$
m=n^2+r,\qquad1\le r\le2n.
$$

The Layer-D closure theorem specializes with `P=n`:

> Any shell point disjoint from every prime direction `p ≤ n` is prime.

Thus Legendre is equivalent to a local support-escape provider:

$$
\forall n>0,\ \exists r,\ 1\le r\le2n\ \land\
\forall p\le n,\ p\text{ prime}\Rightarrow p\nmid n^2+r.
$$

Suggested conceptual name:

```text
SquareAnchoredPrimeEscape
```

or

```text
SquareAnchoredSupportEscape
```

The final Lean name will be chosen after existing naming conventions are
reviewed.

### Critical boundary

The following must remain separate:

```text
provable framework
  square Body closure
  finite support semantics
  residue equivalences
  periodic observer facts

hard provider
  every square shell contains a support-disjoint point
```

The hard provider is Legendre-equivalent.  It must not be hidden inside a
definition, typeclass, or imported assumption.

## 8. Relation to existing finite-prime escape

`DkMath.Hackathon.FinitePrimeEscape` proves a Euclidean product-plus-offset
escape theorem.  Its key local theorem says that a prime divisor of the
product-plus-offset boundary cannot belong to the finite source set under the
coprimality hypothesis.

This is stronger than a mere existential statement **for a selected prime
divisor**, but the existing public bridge currently packages the result mainly
as `FreshPrimeDirection`: at least one fresh direction exists.

Legendre requires a different property:

```text
all old directions absent
```

and also a localization condition:

```text
the escape point lies inside a specified square shell
```

Therefore the finite-prime escape theorem is a reusable Primitive provider but
is not by itself a Legendre provider.

## 9. Relation to PrimitiveBeam

`PrimitiveBeam` supplies a different origin coordinate.

Its primitive witness is defined by first occurrence across difference-power
exponents.  Existing theorems show that such a witness:

- does not divide the boundary `a-b` when `d > 1`;
- divides the `GN` factor;
- has difference-power valuation equal to the `GN` valuation.

This should be exposed through the Primitive facade as an **Origin** family,
not merged definitionally with finite-set freshness.

The two notions answer different questions:

```text
finite-world fresh direction
  new relative to a finite support set

primitive difference-power direction
  new relative to all lower exponents
```

A future bridge may relate them in concrete settings, but the core definitions
should stay distinct.

## 10. Future categorical preparation

The current project should not introduce abstract category theory merely for
future-proofing.

Instead it should preserve the following structure boundaries:

1. algebraic identities independent of order;
2. order/shell notions independent of primality;
3. support/divisibility notions independent of analytic mass;
4. observer-specific residue coordinates separate from semantic support;
5. target conjectures implemented as thin application bridges.

If map-compatibility and unit-transport theorems are available at the algebraic
layer, a later categorical formulation can treat those theorems as naturality
data rather than forcing a rewrite of the NumberTheory API.

## 11. Proposed future module direction

This is a design sketch, not an implementation instruction yet.

```text
DkMath/NumberTheory/Primitive/
  Basic.lean
  Direction.lean
  Support.lean
  Depth.lean
  Origin.lean
  Mass.lean
  Escape.lean
  SquareBody.lean

DkMath/NumberTheory/Primitive.lean

DkMath/NumberTheory/Legendre/
  Basic.lean
  SquareEscape.lean
  ResidueObserver.lean
  Frontier.lean
```

The first implementation should be significantly smaller than this full tree.
Files should be created only when theorem ownership becomes clear.

## 12. Non-goals for the initial project phase

- Do not prove Legendre's conjecture by declaration or hidden provider.
- Do not import RH/CFBRC into the Primitive core.
- Do not move or rename existing PrimitiveBeam / PrimitiveSet modules yet.
- Do not duplicate finite-prime escape arithmetic.
- Do not introduce category theory before the algebraic map API exists.
- Do not treat a wheel residue survivor as automatically prime outside a
  certified arithmetic Body.
- Do not identify `FreshPrimeDirection` with support disjointness.

The immediate goal is a stable conceptual and dependency architecture from
which small Lean checkpoints can later be derived.
