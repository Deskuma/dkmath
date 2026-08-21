# DkMath Primitive Structure — Roadmap

Date: 2026-08-22

Branch: `wip/number-theory-primitive-structure-260822-v0`

Base: `develop` at `8646c3f56591aa04a35b49d5e01ce107caf8cc3b`

## 0. Project rule

The project is **Primitive Structure first, Legendre first application**.

The project is not allowed to hide a conjecture-equivalent provider inside a
framework theorem.

The intended development order is:

```text
documentation
  ↓
reconnaissance
  ↓
small generic Primitive API
  ↓
generic square-Body arithmetic closure
  ↓
finite-prime / PHZ observer bridge
  ↓
Legendre exact reduction
  ↓
only then investigate the hard localization provider
```

The current phase is documentation only.

---

# Phase P0 — project architecture

## PRIM-000 — project scope

Status: **complete in docs**

Deliverables:

```text
README.md
primitive-structure-design-260822.md
primitive-asset-map-260822.md
primitive-roadmap-260822.md
```

Fixed decisions:

1. Primitive Structure is the main subject.
2. Legendre is the first application, not the owner of the abstraction.
3. Cosmic Formula identities stay above NumberTheory.
4. Primorial / PHZ structures are observers or arithmetic specializations.
5. Existing theorem owners are reused rather than moved initially.
6. RH/CFBRC is not imported into the Primitive core.
7. Category theory is deferred; map/naturality lemmas are the preparation.

Exit gate:

- architecture and dependency direction are explicit;
- hard Legendre provider is visibly separated from provable framework layers.

## PRIM-001 — current-source reconnaissance

Status: **initial inventory complete in docs**

Current inspected assets:

```text
CosmicFormula.CosmicFormulaBinom
StructuralArithmetic.PrimitiveDirection
Hackathon.FinitePrimeEscape
StructuralArithmetic.FinitePrimeEscapeBridge
StructuralArithmetic.PrimeCoordinates
PrimitiveBeam
PrimitiveSet.FullExponentSlot
ValuationFlow.Basic
StructuralArithmetic aggregator
```

Before Lean implementation begins, perform one focused reconnaissance pass for:

```text
StructuralArithmetic.GNBridge
PrimitiveSet public aggregators
existing support-disjoint / coprime-support predicates under other names
existing square-bound / least-prime-factor lemmas in Mathlib or DkMath
existing map lemmas for GN / GZ / Body / Gap
```

Outcome choices:

```text
A. existing theorem already provides the desired API
   → reuse / alias / facade only

B. equivalent theorem exists in a lower layer
   → add thin bridge

C. semantic concept is genuinely missing
   → add minimal new definition/theorem
```

---

# Phase P1 — algebraic square facade

This phase is intentionally independent of primality.

## PRIM-010 — square specialization audit

Goal:

Identify the smallest existing theorem path for

$$
(x+u)^2=x(x+2u)+u^2.
$$

Do not create a new theory if `CosmicFormulaBinom` / `GZ` already provides the
necessary normal form.

Candidate theorem surface, subject to reconnaissance:

```text
squareBig
squareBody
squareGap
square_big_eq_body_add_gap
square_body_eq_mul_add
```

These are conceptual targets, not fixed Lean names.

Exit gate:

- a downstream module can use the square identity without unfolding a long
  generic binomial sum;
- no NumberTheory import is required.

## PRIM-011 — unit-one square Body

Goal:

Expose the specialization

$$
(P+1)^2=P(P+2)+1.
$$

and

$$
P^2+2P=(P+1)^2-1
$$

in a form usable by natural-number applications while retaining the generic
source theorem.

Exit gate:

- the expression `P^2 + 2*P` is identified as a square Body specialization,
  not as a Legendre-local definition.

## PRIM-012 — unit transport / map reconnaissance

Goal:

Determine which of the following already exist and which require thin wrappers:

```text
map Big
map Body / GZ
map Gap
map GN
unit scaling x = u*y
```

No category-theory imports.

Exit gate:

- later `ℕ`, `ℝ`, and `ℂ` applications can share the same algebraic theorem
  family without re-proving the decomposition.

---

# Phase P2 — Primitive semantic core

## PRIM-020 — support-disjoint semantic gap

Goal:

Add or expose a predicate representing:

> no prime divisor of `n` belongs to the old finite prime world `S`.

Working documentation name:

```text
SupportDisjointFrom S n
```

Required relation to current APIs:

```text
PrimeScaleGeneratedBy
FreshPrimeDirection
SupportDisjointFrom
```

must remain three distinct notions.

Minimum theorem goals:

```text
supportDisjointFrom_iff_no_old_prime_dvd
supportDisjointFrom_of_all_prime_dvd_not_mem
freshPrimeDirection_of_supportDisjointFrom
  -- with nontriviality / prime-factor existence assumptions as needed
```

Do not over-generalize before the natural-number API is stable.

Exit gate:

- Legendre can state "all old directions absent" without ad hoc quantified
  formulas in every theorem.

## PRIM-021 — finite-prime escape bridge upgrade

Goal:

Audit whether `prime_dvd_product_add_coprime_not_mem` can feed the new
support-disjoint predicate directly for suitable product-plus-offset targets.

Important:

The arithmetic proof remains owned by `DkMath.Hackathon.FinitePrimeEscape`
unless a later refactor is separately justified.

Exit gate:

- the Primitive facade can express both existential fresh escape and full old
  support exclusion when the provider theorem genuinely supplies it.

---

# Phase P3 — generic square-Body arithmetic closure

## PRIM-030 — composite divisor bound inside the Body

Target mathematical statement:

For natural `P` and `m`, if

$$
1<m\le P^2+2P
$$

and `m` is composite, then

$$
\exists q,\ q\text{ prime}\land q\mid m\land q\le P.
$$

This theorem must not mention Legendre or primorials.

Preferred proof source:

- existing least-prime-factor / prime-divisor bound in Mathlib if available;
- otherwise a thin theorem built from existing prime-factor and square-order
  lemmas.

Exit gate:

- the Cosmic square Body has a precise natural-number composite-detection
  interpretation.

## PRIM-031 — Primitive prime closure inside the Body

Target statement:

Inside

$$
1<m\le P^2+2P,
$$

if `m` is support-disjoint from every prime direction `q ≤ P`, then `m` is
prime.

This should be a direct wrapper over PRIM-030 plus Primitive support semantics.

Exit gate:

- an arithmetic Primitive escape becomes a prime witness inside the certified
  square Body.

## PRIM-032 — sharp boundary certificate

Target statement:

If `P+1` is prime, then `(P+1)^2` is the first obvious boundary point showing
that the `≤ P` prime-direction detector cannot be extended through the next
square without adding the new direction `P+1`.

Example certificates:

```text
P = 30   → Body endpoint 960, next point 31² = 961
P = 210  → Body endpoint 44520, next point 211² = 44521
```

This theorem is explanatory infrastructure; keep it separate from the core
closure theorem.

---

# Phase P4 — finite prime worlds and PHZ observer

## PRIM-040 — finite active prime world

Goal:

Define or reuse a finite active set of prime directions and the notion that a
position is reserved by at least one active prime wave.

Conceptual API:

```text
ReservedBy S m
UnreservedBy S m
```

Prefer reusing `SupportDisjointFrom` instead of duplicating semantics:

```text
UnreservedBy S m
  ≈ SupportDisjointFrom S m
```

when `S` is a genuine prime set.

Exit gate:

- PHZ can be defined as an observer on top of semantic support.

## PRIM-041 — periodic residue observer

Goal:

For a finite prime base with product modulus `M`, formalize the periodicity of
reserved/unreserved positions.

Example observation:

```text
S = {2,3,5}
M = 30
unreserved residues = {1,7,11,13,17,19,23,29}
```

The observer theorem must not say that every unreserved residue instance is
prime.

Exit gate:

- candidate seats and prime seats are formally distinguished.

## PRIM-042 — observer update rule

Goal:

Describe how adding a new prime direction refines the reserved seats of a
periodic observer.

This checkpoint should expose the sieve update mechanism without claiming a
Legendre result.

Possible later theorem family:

```text
old seat → q translated child seats
exactly one child reserved by q modulo q
remaining q-1 children survive the new q-wave
```

Only implement after the required CRT / Finset API is assessed.

---

# Phase P5 — Legendre first application

## PRIM-L001 — square shell

Define the natural-number consecutive-square interior independently of primes.

Conceptual forms:

```text
SquareCell n m
SquareOffset n r
```

with exact conversion

$$
n^2<m<(n+1)^2
\Longleftrightarrow
m=n^2+r,\ 1\le r\le2n.
$$

## PRIM-L002 — support-free shell point implies prime

Use PRIM-031 with `P=n`.

Target:

```text
SquareCell n m
+ no prime q ≤ n divides m
→ Nat.Prime m
```

This theorem is framework, not conjecture.

## PRIM-L003 — residue-cover equivalence

For offsets `1 ≤ r ≤ 2n`, express the forbidden wave of prime `p ≤ n` as

$$
p\mid n^2+r
$$

or equivalently the residue class

$$
r\equiv-n^2\pmod p.
$$

Target result:

```text
support-disjoint square offset
↔ offset not covered by any old prime wave
```

## PRIM-L004 — exact Legendre reduction

Define the hard provider explicitly.

Working name:

```text
SquareAnchoredSupportEscape
```

with meaning

$$
\forall n>0,\ \exists r,\ 1\le r\le2n
$$

such that no prime `p ≤ n` divides `n²+r`.

Then prove the exact equivalence to the usual Legendre statement.

Exit gate:

- the conjecture has been transformed into one finite local support-escape
  obligation;
- no provider is assumed or smuggled into the framework.

### Mandatory stop after PRIM-L004

Stop and review the mathematics before attempting to prove the universal
escape provider.

At this point classify all available routes:

```text
PHZ / periodic reservation
square-anchor residue constraints
finite-prime escape localization
prime-power depth / mass
other Primitive application theorems
```

Only then choose the next research branch.

---

# Phase P6 — broader Primitive facade

This phase comes after the first Legendre reduction is stable.

## PRIM-060 — Depth facade

Index/re-export the reusable part of prime-power exponent-slot APIs.

Do not move `PrimitiveSet.FullExponentSlot` initially.

## PRIM-061 — Origin facade

Expose the reusable semantic role of
`PrimitiveBeam.PrimitivePrimeFactorOfDiffPow` and its GN transport theorems.

Keep finite-set freshness and exponent-first-occurrence definitions distinct.

## PRIM-062 — Mass facade

Index valuation / radical / logarithmic mass APIs without inventing a universal
mass structure prematurely.

Candidate owners to bridge:

```text
ValuationFlow
ABC valuation/radical APIs
PrimitiveSet channel cost APIs
```

## PRIM-063 — application map

Document and, only where useful, add thin bridges for:

```text
Legendre
ABC
FLT
RH
Erdos #1196
Pascal
Collatz
```

The goal is a coherent public map, not forced unification of mathematically
different primitive predicates.

---

# Naming policy

During documentation, conceptual names are allowed.

Before implementation, every proposed public name must be checked against:

```text
existing DkMath declarations
Mathlib vocabulary
current namespace ownership
```

Avoid creating aliases merely for aesthetic uniformity unless they materially
improve the public Primitive facade.

---

# Dependency policy

The desired dependency graph is:

```text
CosmicFormula
     ↓
NumberTheory generic arithmetic
     ↓
Primitive facade
     ↓
observer/application bridges
```

Forbidden initial direction:

```text
RH/CFBRC → Primitive core
ABC       → Primitive core
FLT       → Primitive core
Legendre  → Primitive core
```

If a reusable theorem is discovered in an application module, first determine
whether it should be promoted to an appropriate lower NumberTheory owner.

---

# Verification policy for later Lean phases

Each Lean checkpoint should be small enough to answer one question:

```text
What new semantic fact did Lean certify?
```

Build success alone is not the project metric.  The review should check:

1. theorem meaning;
2. dependency direction;
3. whether an existing theorem was duplicated;
4. whether a hard provider was hidden in assumptions;
5. what Primitive coordinate the theorem belongs to;
6. whether the result is reusable outside Legendre.

The documentation phase intentionally ends before any of these Lean
checkpoints are started.
