# DkMath NumberTheory Primitive Structure

Project branch: `wip/number-theory-primitive-structure-260822-v0`

Base branch: `develop`

Base commit at project start: `8646c3f56591aa04a35b49d5e01ce107caf8cc3b`

## 1. Project position

This project does **not** start as a proof project for Legendre's conjecture.

The main subject is a reusable **Primitive Structure** layer for DkMath.
Legendre's conjecture is the first application because its consecutive-square
window turns a support-escape statement into a prime witness with unusually
little extra machinery.

The intended dependency direction is:

```text
CosmicFormula / generic algebraic identities
                ↓
DkMath NumberTheory Primitive Structure
                ↓
finite prime-scale / residue / valuation observers
                ↓
applications
  Legendre / ABC / FLT / RH / Erdos / Pascal / Collatz
```

The project begins with documentation and architecture only.  No Lean
implementation is required during the initial documentation phase.

## 2. Algebraic source layer

The Primitive project must not hard-code primorials or even natural numbers
into the Cosmic Formula source layer.

The square identity is the specialization

$$
(x+u)^2=x(x+2u)+u^2.
$$

Its unit-one specialization is

$$
(P+1)^2=P(P+2)+1.
$$

Thus

$$
N+1=(P+1)^2,\qquad N=P^2+2P=P(P+2)
$$

is an arithmetic specialization of a more general algebraic identity.  The
variable `P` is not intrinsically a primorial and need not even be an integer.
The identity is meaningful over suitable commutative semirings, including
`ℕ`, `ℤ`, `ℚ`, `ℝ`, and `ℂ`.

The existing generic DkMath direction is still more general:

$$
(x+u)^d=x\,GN_d(x,u)+u^d.
$$

Therefore later NumberTheory modules should specialize existing CosmicFormula
and GN APIs rather than rebuild the algebra from a prime-specific definition.

## 3. Primitive core intuition

The working interpretation is:

> A primitive direction is information that cannot be generated entirely from
> the currently known finite support world.

For natural-number prime support this becomes particularly concrete.
Given a finite set `S` of known prime directions, DkMath already distinguishes:

- all prime divisors of `n` lie in `S`;
- a prime divisor `q` of `n` lies outside `S`.

These are represented today by
`PrimeScaleGeneratedBy` and `FreshPrimeDirection` in
`DkMath.NumberTheory.StructuralArithmetic.PrimitiveDirection`.

A central design requirement of this project is to add, or expose through a
facade, the stronger dual notion:

```text
SupportDisjointFrom S n
```

meaning that **no** prime divisor of `n` lies in `S`.

This must remain distinct from `FreshPrimeDirection`:

```text
FreshPrimeDirection
  some new direction exists

SupportDisjointFrom
  every old direction is absent
```

This distinction is essential for the Legendre entry route.

## 4. Four Primitive coordinates

The project organizes existing DkMath arithmetic through four coordinates.

### 4.1 Direction

Which prime direction is new relative to the current finite support world?

Existing anchors:

- `KnownPrimeScales`
- `PrimeScaleGeneratedBy`
- `FreshPrimeDirection`
- `FreshPrimeFactor`
- finite-prime escape bridges

### 4.2 Depth

How deep does one fixed prime direction occur?

The model is the prime-power ray

$$
p,p^2,p^3,\ldots
$$

Existing anchors include exponent-slot and prime-power channel APIs such as
`FullExponentSlotChannelSet` and `FullExponentSlotCoverage`.

### 4.3 Origin

Where did a new direction first become visible?

For difference powers, the existing `PrimitiveBeam` layer records first
occurrence across exponents.  A primitive prime cannot come from the lower
boundary and is transported to the `GN` / Beam factor.

### 4.4 Mass

How much arithmetic load belongs to one direction?

This coordinate includes valuation depth, support mass, radical information,
and logarithmic / von-Mangoldt style costs.  It is intentionally separated
from the binary question of whether a prime direction exists.

## 5. Existing assets are not to be moved initially

This project is an integration and facade project first, not a repository-wide
refactor.

Existing modules remain the owners of their current theorems, including:

```text
DkMath.NumberTheory.StructuralArithmetic.PrimitiveDirection
DkMath.NumberTheory.StructuralArithmetic.FinitePrimeEscapeBridge
DkMath.NumberTheory.PrimitiveBeam
DkMath.NumberTheory.PrimitiveSet.*
DkMath.NumberTheory.ValuationFlow.*
DkMath.Hackathon.FinitePrimeEscape
DkMath.Hackathon.FinitePrimeEscapeGN5
```

The first implementation goal, after documentation, is a thin reusable public
surface rather than copying proofs.

## 6. Legendre as the first Primitive application

For `n > 0`, consider the consecutive-square interior

$$
n^2<m<(n+1)^2.
$$

If `m` is composite, one of its prime divisors is at most `n`.  Therefore a
point in this window that is disjoint from all prime directions at most `n`
is automatically prime.

Equivalently, writing

$$
m=n^2+r,\qquad 1\le r\le 2n,
$$

Legendre's conjecture becomes the existence of an offset whose value avoids all
old prime directions:

$$
\exists r,\ 1\le r\le 2n\ \land\
\forall p\le n,\ p\text{ prime}\Rightarrow p\nmid n^2+r.
$$

This is the first target for the Primitive facade because it separates cleanly
into:

```text
Primitive framework
  support semantics
  finite prime worlds
  square-body prime closure
  residue / PHZ observation

Legendre-specific provider
  a support-disjoint point always exists in the square shell
```

The first group is expected to be reusable and provable without resolving the
conjecture.  The final provider is the hard Legendre-equivalent frontier and
must remain explicit.

## 7. PHZ position

PHZ is treated as an observer, not as the definition of Primitive Structure.

A finite family of prime waves marks divisibility-reserved positions.  The
unreserved residue classes are Primitive candidates relative to that observer.
As new prime directions become available, further seats become reserved.

The square identity supplies a natural arithmetic observation body.  In the
unit-one square world,

$$
P^2+2P=(P+1)^2-1.
$$

Inside an appropriate natural-number specialization, this Body is the region
whose composite points can be certified by bounded prime directions.  The
precise arithmetic horizon and its relation to the next required prime wave
will be separated from the generic algebraic identity in the design documents.

## 8. Design rule for future abstraction

The project should prepare for later abstraction without importing category
theory prematurely.

The rule is:

> Put the identity at the highest algebraic layer; add order, discreteness,
> divisibility, primality, and residue observations only in lower layers.

In particular, future generic APIs should prefer map/naturality lemmas for
`Big`, `Body`, `Gap`, `GN`, and unit transport.  If those are stable under
semiring homomorphisms, a later categorical formulation can be added without
redesigning the arithmetic applications.

## 9. Initial documents

- `README.md` — project scope and architecture
- `primitive-structure-design-260822.md` — detailed layer design
- `primitive-asset-map-260822.md` — current DkMath theorem/module inventory
- `primitive-roadmap-260822.md` — documentation and implementation checkpoints

## 10. Current boundary

At project start:

- no claim is made that Legendre's conjecture has been proved;
- no claim is made that finite-prime escape alone supplies the required square
  localization;
- no current RH/CFBRC module is a dependency of the Primitive core;
- RH prime-power observations may motivate generic NumberTheory abstractions,
  but reusable statements should live below RH-specific code before Legendre
  consumes them.

The immediate objective is to make the Primitive vocabulary and dependency
boundaries precise enough that later Lean implementation can proceed one thin
checkpoint at a time.
