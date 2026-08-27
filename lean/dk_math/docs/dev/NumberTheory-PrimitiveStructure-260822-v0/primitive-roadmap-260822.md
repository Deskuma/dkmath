# DkMath Primitive Structure — Roadmap

Date: 2026-08-22

Last synchronized: 2026-08-24

Branch: `wip/number-theory-primitive-structure-260822-v0`

Base: `develop` at `8646c3f56591aa04a35b49d5e01ce107caf8cc3b`

## 0. Project rule

The project is **Primitive Structure first, Legendre first application**.

The project is not allowed to hide a conjecture-equivalent provider inside a
framework theorem.

The current dependency direction is:

```text
CosmicFormula
     ↓
generic NumberTheory / Primitive
     ↓
finite prime-world observers
     ↓
Legendre application geometry
     ↓
explicit Legendre frontier
```

Application discoveries may be promoted downward only when their theorem owner
is genuinely generic.  PRIM-C001/C002 are the model example: they were
motivated by Legendre quotient geometry but belong in `Primitive/SquareBody`.

---

# 1. Current summit map

The initial documentation-only phase is long past.  The project has completed a
large finite-arithmetic spine without proving Legendre's conjecture.

Current main result chain:

```text
finite prime support semantics
        ↓
periodic prime worlds / exact residue refinement
        ↓
generic square-Body composite detection
        ↓
exact Legendre reduction to non-full-cover
        ↓
wave / carry / overlap geometry
        ↓
coprime packet geometry
        ↓
quotient Direction/Depth classification
        ↓
localized obstruction ledgers
        ↓
packet cross-factor geometry
        ↓
Primitive square-Body unique-fresh factor theorem
        ↓
small-cofactor / large-quotient dual normal form
```

The hard frontier remains:

$$
\forall n>0,\quad
\neg\operatorname{SquareOffsetsFullyCovered}(n).
$$

No theorem below this line is currently claimed.

---

# 2. Completed architecture and Primitive core

## PRIM-000 / PRIM-001 — project architecture and reconnaissance

Status: **complete**

Persistent decisions:

1. Primitive Structure is the main subject.
2. Legendre is the first application, not the abstraction owner.
3. Cosmic Formula identities remain above NumberTheory.
4. Finite prime worlds and PHZ are observers/specializations.
5. `FreshPrimeDirection`, `PrimeScaleGeneratedBy`, and
   `SupportDisjointFrom` remain distinct.
6. RH/CFBRC is not a Primitive-core dependency.
7. Category theory remains deferred.

## PRIM-020 family — support semantics

Status: **complete for the current natural-number use**

The public semantics support:

```text
old-generated
some fresh direction
all old directions absent
```

without conflating them.

## PRIM-030 / PRIM-031 — square-Body arithmetic closure

Status: **complete**

Implemented in:

```text
DkMath.NumberTheory.Primitive.SquareBody
```

Key certified fact:

```text
1 < m ≤ P^2 + 2P
+ no prime q ≤ P divides m
→ Nat.Prime m
```

The bound is the arithmetic interior below `(P+1)^2` and does not require a
primorial hypothesis.

---

# 3. Completed finite-prime observer stack

## PRIM-040–047 — finite prime world / periodic refinement

Status: **complete**

Implemented modules:

```text
FinitePrimeWorld
PeriodicPrimeWorld
PrimeWorldRefinement
PHZ30
PrimeWorldResidues
PrimeWorldCardinality
EulerTotientBridge
```

Main outcomes:

- `primeScalesUpTo P` gives the exact old prime world;
- prime-wave divisibility is periodic modulo the finite-world modulus;
- adding a new prime direction refines each old residue fiber by one reserved
  child and `q-1` surviving children;
- the surviving residue set is exact;
- cardinality is the product of `(p-1)` and agrees with Euler totient.

These theorems describe observer geometry.  They do not claim that a local
short interval contains a survivor.

---

# 4. Completed exact Legendre reduction

## PRIM-L001–L004 — square shell and exact frontier

Status: **complete**

Core definitions:

```text
SquareCell
SquareOffset
SquareOffsetCovered
SquareOffsetsFullyCovered
SquareAnchoredSupportEscape
LegendreConjecture
```

The central equivalence is complete:

$$
\operatorname{LegendreConjecture}
\iff
\forall n>0,\;\neg\operatorname{SquareOffsetsFullyCovered}(n).
$$

This is a reduction theorem, not a proof that full cover is impossible.

---

# 5. Completed local wave / overlap program

## PRIM-L005 — exact support on one seat

Status: **complete**

- finite prime support of `n^2+r` inside `primeScalesUpTo n`;
- support overlap cardinality;
- pair divisibility equivalence.

## PRIM-L006 — wave cardinality / far-pair uniqueness

Status: **complete**

- generic `squareWaveOffsets`;
- pair overlaps as product waves;
- long-modulus waves have cardinality at most one;
- incidence transpose.

## PRIM-L007 / L008 — exact wave count and carry

Status: **complete**

Exact count:

$$
|W_m|
=
\left\lfloor\frac{n^2+2n}{m}\right\rfloor
-
\left\lfloor\frac{n^2}{m}\right\rfloor.
$$

Then:

```text
wave count = baseline + 0/1 carry
```

Carry is deterministic arithmetic boundary data, not a probabilistic term.

## PRIM-L009 / L010 — pair ledger and near/far split

Status: **complete**

- unordered distinct-prime pair multiplicity;
- exact pair-overlap transpose;
- near/far split by `p*q ≤ 2*n` versus `2*n < p*q`;
- far pair contribution becomes a finite active-pair count.

No third-order inclusion-exclusion was introduced.

---

# 6. Completed coprime-packet / quotient program

## PRIM-L011 — anchor divisor/nondivisor split

Status: **complete**

On coprime offsets, all anchor-divisor prime waves disappear and coverage is
exactly nondivisor coverage.  The coprime window has cardinality

$$
2\varphi(n).
$$

## PRIM-L012 — canonical packets

Status: **complete**

The coprime window splits into `φ(n)` packets

$$
(r,n+r).
$$

The old nondivisor supports of the two packet sides are disjoint.

## PRIM-L013 — support quotient

Status: **complete**

For an old support prime `p`,

$$
p\,Q=n^2+r,
$$

with `Q > n`, and coprimality with the anchor transfers to `Q`.

## PRIM-L014 — global quotient rigidity

Status: **complete**

Distinct selected primes cannot produce the same quotient once `n ≥ 4`.
The global quotient projection is injective on the relevant incidence set.

## PRIM-L015 / L016 — quotient support and Direction/Depth trichotomy

Status: **complete**

The quotient is prime exactly in the simple case:

$$
Q\text{ prime}
\iff
\operatorname{support}=\{p\}
\land
p^2\nmid n^2+r.
$$

Composite quotient obstruction is completely classified as:

```text
selected-prime self-depth
or
a distinct old support direction.
```

Finite-world freshness obtained here is not `PrimitiveBeam` origin.

---

# 7. Completed obstruction bookkeeping

## PRIM-L017 — three seat classes

Status: **complete**

Covered coprime seats split disjointly into:

```text
simple/fresh
singleton-depth
multi-support
```

Under full cover:

$$
2\varphi(n)
=
\#\text{Simple}
+
\#\text{Depth}
+
\#\text{Multi}.
$$

A coarse depth-wave budget and global pair ledger yield a necessary full-cover
frontier, not a contradiction.

## PRIM-L018 — localized obstruction ledgers

Status: **complete**

The depth and pair ledgers were restricted to the same coprime/nondivisor
region as the seat partition.

Main outcome:

```text
localized budget ≤ previous global budget
```

and the full-cover frontier now uses the localized quantities.

This removed avoidable overcount but did not by itself force a simple seat.

---

# 8. Completed packet cross-geometry

## PRIM-L019 — packet cross-pair ledger

Status: **complete**

Ordered left/right old-prime pairs are counted exactly by

$$
\sum_r |A_r|\,|B_r|.
$$

Full cover implies

$$
\varphi(n)
\le
\operatorname{PacketCrossPairCount}(n).
$$

For a fixed ordered `(p,q)`, two packet hits imply product-period divisibility;
therefore

$$
n<pq
$$

forces at most one packet hit.  The packet threshold is `n`, sharper than the
single-seat `2*n` threshold.

## PRIM-L020 — packet coprimality

Status: **complete**

For a coprime base offset, the two complete packet points are coprime.  Hence
all cross-side prime factors are separated, not only old support primes.

The factor rectangle satisfies

$$
p a+n=q b.
$$

Same-side relations `p ⟂ a` and `q ⟂ b` are intentionally not asserted;
selected-prime depth may remain there.

## PRIM-L021 — reduced-residue rectangle

Status: **complete**

The rectangle satisfies

$$
p a\equiv q b\equiv r\pmod n,
$$

and all four factors are coprime to the anchor.  The exact additive gap remains

$$
q b-p a=n.
$$

No `ZMod`, inverse-selection, matching argument, or contradiction was added.

---

# 9. Completed refactor

## PRIM-R001 — Legendre module decomposition

Status: **complete**

The former monolithic `Legendre.lean` was decomposed into theorem-owner modules:

```text
Basic
Wave
PairOverlap
CoprimePacket
Quotient
QuotientSupport
Obstruction
LocalizedObstruction
PacketCross
PacketCoprimality
PacketUnitResidue
SmallCofactor
Frontier
Internal/PairCombinatorics
```

`DkMath.NumberTheory.Legendre` remains a thin historical facade.

The two application branches remain structurally distinct until `Frontier`:

```text
within-seat obstruction
packet cross-coupling
```

---

# 10. Primitive theorem promotion from the Legendre investigation

## PRIM-C001 — unique fresh factor inside square Body

Status: **complete**

For positive `m ≤ squareBody P`, a fresh prime divisor `ℓ > P` is unique and
occurs only to depth one.  Removing it leaves an old-generated cofactor.

## PRIM-C002 — bounded fresh cofactor

Status: **complete**

The cofactor is not merely old-generated:

$$
0<k=\frac m\ell\le P.
$$

Old support transfers exactly from `m` to `k`, and

```text
m prime ↔ k = 1.
```

Thus the generic square-Body normal form is now:

```text
old-generated
or
unique fresh ℓ > P × small old-generated k ≤ P.
```

This is a Primitive-core theorem and is reusable outside Legendre.

---

# 11. Completed dual normal form

## PRIM-L022 — SmallCofactor bridge

Status: **complete**

Implemented in:

```text
DkMath.NumberTheory.Legendre.SmallCofactor
```

For a coprime square seat with fresh split

$$
\ell k=n^2+r,
\qquad
\ell>n,
\qquad
0<k\le n,
$$

the small cofactor returns to the canonical base packet world:

```text
k ∈ squareAnchorCoprimeBaseOffsets n.
```

If an old support prime `p ≤ n` is selected, then `p ∣ k`, and the large
quotient is exactly

$$
Q=\ell\left(\frac{k}{p}\right).
$$

Therefore

$$
Q\text{ prime}
\iff
k=p,
$$

and equivalently

```text
singleton old support + selected-prime depth one
↔ small cofactor equals the selected prime.
```

Under full cover every coprime seat has the necessary normal form:

```text
old-generated
or
unique fresh ℓ > n × nontrivial small cofactor 2 ≤ k ≤ n.
```

The old-generated branch is still explicit and unresolved.

---

# 12. Documentation synchronization checkpoint

Status: **complete after PRIM-L022**

Updated:

```text
primitive-structure-design-260822.md
primitive-roadmap-260822.md
```

Purpose:

- replace the original documentation-only status with the theorem graph that
  Lean has actually certified;
- promote C001/C002 into the Primitive core architecture;
- record L022 as the bridge between the generic small cofactor and the
  application large quotient;
- identify the next research frontier without prematurely issuing another
  implementation instruction.

---

# 13. Candidate next phase — valuation tower parity retention

Status: **reconnaissance candidate; not yet an implementation checkpoint**

The next expected obstruction is loss of parity information in prime-power
exponent towers.

For a fixed prime direction with valuation `v`, the desired finite
normalization is

$$
v=2j+\varepsilon,
\qquad
\varepsilon\in\{0,1\}.
$$

Interpretation:

```text
j
  number of complete two-depth packets

ε
  terminal unpaired depth / parity Gap
```

Before adding new definitions, inspect and reuse existing DkMath assets:

```text
padicValNat divisibility-height API
padicValNat first-layer/deep-layer split
PrimitiveSet exponent-slot / prime-power channel APIs
NPUnit half-phase / two-step return API
existing finite factorization support sums
```

### Reconnaissance questions

1. Is there already an exact theorem equivalent to
   `v = 2 * (v / 2) + v % 2` in the desired valuation-facing namespace?
2. Can membership of the finite `p^k` tower be rewritten directly through
   `padicValNat` without introducing a second depth notion?
3. Is an existing finite-support definition of `Ω` available, or should the
   first checkpoint stop at local prime-direction parity?
4. Can parity information be transported through the C002 split
   `m = ℓ * k` without rebuilding factorization theory?
5. Does the resulting information constrain the unresolved old-generated/full-
   cover branch, or is it merely a lossless coordinate rewrite?

### Required stop condition

Do not claim that a parity-retention API solves the classical sieve parity
problem.

In particular,

```text
Ω(m) odd
```

does not distinguish `Ω(m)=1` from `Ω(m)=3,5,...` by itself.

The value of this phase is information preservation: keep Direction and Depth
available long enough that later square-shell arguments do not throw parity
away prematurely.

If reconnaissance shows that the proposed parity layer is only a repackaging
with no new leverage on the Legendre frontier, stop before building a large
abstraction.

---

# 14. Parallel research route — finite-difference invariant extraction

Status: **background / not active in the current exact square checkpoint**

A separate DkMath route keeps a nonzero discrete unit/difference parameter
before extracting invariant information.  Conceptually:

```text
u ≠ 0 finite-difference world
        ↓
extract invariant / conserved quantity
        ↓
specialize or pass to differential observation
```

The current Legendre implementation is the exact unit-one natural-number
specialization.  Do not mix the continuous/differential route into the current
modules until a concrete bridge theorem is identified.

---

# 15. Broader Primitive facade — deferred but still valid

Later work may expose reusable Depth / Origin / Mass families across DkMath:

```text
Depth
  prime-power exponent slots / valuation

Origin
  PrimitiveBeam first occurrence across exponents

Mass
  valuation / radical / logarithmic channel cost
```

Application map targets remain:

```text
Legendre
ABC
FLT
RH
Erdos #1196
Pascal
Collatz
```

The goal is a coherent public map, not forced identification of mathematically
different primitive predicates.

---

# 16. Verification and review policy

Each future Lean checkpoint must answer one question:

```text
What new semantic fact did Lean certify?
```

Review should continue to check:

1. theorem meaning;
2. dependency direction;
3. whether a lower theorem owner exists;
4. whether support and valuation depth were conflated;
5. whether a conjecture-equivalent provider was hidden in an assumption;
6. whether a new counting layer adds information or only notation;
7. whether the result is reusable outside Legendre;
8. whether the remaining frontier is stated explicitly.

Build success is a gate, not the mathematical project metric.
