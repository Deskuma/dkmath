# Multi-Gauge Divisibility / Prime Escape 260914 v0

cid: `6aa763a7-1a14-83e8-9041-1029d978663c`

Status: ACTIVE

## Purpose

This directory is the implementation hub for the first production phase of the generic DkMath multi-gauge divisibility theory.

The motivating question is:

> If a prime `q` escapes divisibility in unit system `u₁`, does it still escape after transport to unit system `u₂`?
>
> Along a finite chain `u₀ -> u₁ -> ... -> uₖ`, where can a previously invisible prime first become visible, and how far can it keep escaping?

The goal is not merely to place the existing one-stage GN gcd firewall side by side. The new object is **prime visibility transport across a gauge transition**.

This branch implements only the arithmetic front half of the broader research plan recorded in:

```text
docs/not_implements/260912-MultiGauge-Divisibility-Norm-Lattice-Landing.md
```

Norm / Eisenstein / TraceOne / power-image landing are deliberately out of scope for the first checkpoints.

---

## Repository / branch

```text
repository: Deskuma/dkmath
branch:     wip/number-theory-multi-gauge-divisibility-260914-v0
base:       develop
```

Development documents:

```text
lean/dk_math/docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/
```

Expected production surface:

```text
DkMath/NumberTheory/MultiGauge/Basic.lean
DkMath/NumberTheory/MultiGauge/PrimeTransport.lean
DkMath/NumberTheory/MultiGauge/Path.lean        -- later checkpoint
DkMath/NumberTheory/MultiGauge.lean             -- facade
```

The exact file split may be adjusted if the existing library architecture makes a smaller ownership boundary preferable.

---

## Existing production facts — do not re-prove

The one-stage arithmetic firewall already exists in:

```text
DkMath.Lib.Cosmic.GTailBoundary
```

with the production theorems:

```text
gcd_GTail_eq_gcd_boundary
gcd_GTail_eq_gcd_choose
gcd_GN_eq_gcd_of_one_le
gcd_GN_prime_eq_one_of_not_dvd
gcd_GN_prime_eq_prime_of_dvd
```

For `1 <= d` and `Coprime x u`, the canonical GN boundary state is:

$$
\gcd(x,GTail(d,1,x,u))=\gcd(x,d).
$$

Hence a prime `q` with `q ∤ d` cannot simultaneously occupy both the boundary channel `x` and the GN channel `GTail d 1 x u`.

The fixed-Big gauge layer also already contains arithmetic-unit transport facts in:

```text
DkMath.NumberTheory.FixedBigGauge.Basic
```

including:

```text
fixedBigUnit_transport
fixedBigUnit_refinement
freshPrime_fixedBigUnit_refinement
```

These are useful application bridges, but the generic multi-gauge arithmetic layer must not depend on the real-valued fixed-Big presentation unless a later bridge explicitly needs it.

---

## Canonical stage observer

For the first implementation, use the GN stage value

```text
stageGN    := GTail d 1 x u
stageValue := x * stageGN
```

Conceptually this is the divisibility observer for one gauge stage.

The minimal stage packet should preserve the data needed by the existing gcd firewall:

```lean
structure GNGaugeStage (d : ℕ) where
  x : ℕ
  u : ℕ
  coprime : Nat.Coprime x u
```

Suggested derived definitions:

```lean
def GNGaugeStage.gnValue ... : ℕ := GTail d 1 s.x s.u

def GNGaugeStage.value ... : ℕ := s.x * s.gnValue

def PrimeEscapes (q : ℕ) (s : GNGaugeStage d) : Prop := ¬ q ∣ s.value

def PrimeCaught (q : ℕ) (s : GNGaugeStage d) : Prop := q ∣ s.value
```

Boundary and GN-channel predicates may be introduced if they reduce theorem statements:

```text
q | s.x
q | s.gnValue
```

Do not add a large state-machine API before the two-stage transport theorems justify it.

---

## Concrete gauge transition

The original research note left `transition : Prop` abstract. This branch makes the first arithmetic transition concrete enough to support prime transport.

A transition from `first` to `second` carries a positive numerator / denominator pair satisfying a cross-multiplication law:

$$
A_2\,\delta=A_1\,\nu,
$$

where

```text
A₁ = first.value
A₂ = second.value
ν  = numerator   -- prime support injected by the transition
δ  = denominator -- prime support removable by normalization/division
```

Suggested packet:

```lean
structure GNGaugeTransition (d : ℕ) where
  first : GNGaugeStage d
  second : GNGaugeStage d
  numerator : ℕ
  denominator : ℕ
  numerator_pos : 0 < numerator
  denominator_pos : 0 < denominator
  balance : second.value * denominator = first.value * numerator
```

The cross-multiplication law is intentionally weaker than committing to a particular quotient representation. It supports exact natural-number divisibility reasoning without introducing rational arithmetic.

Application-specific transitions may later prove this law from normalization, quotient, rescaling, fixed-Big refinement, FLT descent, ABC factorization, or another concrete mechanism.

---

## Prime transport semantics

The first new theorem family should formalize the following elementary but reusable facts.

For prime `q`, if `q` is caught at the second stage, then the balance law forces:

$$
q\mid A_2
\Longrightarrow
q\mid A_1\;\lor\;q\mid\nu.
$$

Therefore:

$$
q\nmid A_1
\land
q\nmid\nu
\Longrightarrow
q\nmid A_2.
$$

This is the forward **prime escape transport theorem**.

Dually:

$$
q\mid A_1
\Longrightarrow
q\mid A_2\;\lor\;q\mid\delta,
$$

and hence:

$$
q\nmid A_2
\land
q\nmid\delta
\Longrightarrow
q\nmid A_1.
$$

If `q` divides neither transition coefficient, prime visibility is conserved:

$$
q\mid A_1
\iff
q\mid A_2.
$$

Equivalently:

$$
q\nmid A_1
\iff
q\nmid A_2.
$$

Interpretation:

```text
numerator support
  = the only place where a previously escaping prime may newly enter;

denominator support
  = the only place where a previously visible prime may disappear.
```

This localization is the core new invariant of v0.

---

## One-stage GN channel refinement

For a prime `q`, the stage product gives:

```text
q | stageValue
<->
q | x OR q | gnValue.
```

Under:

```text
q prime
q ∤ d
Coprime x u
```

the existing GN gcd firewall excludes simultaneous boundary/GN capture.

Thus the off-exponent prime has only three semantic states at one stage:

```text
escape
boundary-only
gn-only
```

The forbidden fourth state `boundary + gn` is pushed into the exceptional exponent support `q | d`.

This theorem should be obtained from existing production facts; do not reproduce the gcd proof.

---

## Finite path objective — later checkpoint

After the two-stage API is stable, generalize to a finite transition path:

```text
s₀ -> s₁ -> ... -> sₖ.
```

The intended path theorem is:

```text
q escapes at s₀
and q divides no transition numerator
->
q escapes at every stage.
```

A complementary first-capture theorem should localize the first newly visible occurrence to the corresponding transition numerator.

In product language:

$$
q\nmid A_0
\land
q\mid A_j
\Longrightarrow
q\mid\prod_{i<j}\nu_i.
$$

Do not implement this path layer in the first checkpoint unless the two-stage implementation makes it immediate and remains small.

---

## Legendre checkpoint

The immediate downstream consumer is the existing Legendre / PrimorialUnitUniverse frontier.

Production already proves for a tied successor-square pair that a fresh prime capable of delaying both minima must satisfy:

```text
q | 2*n + 1.
```

In degree two this successor increment is the GN boundary object:

```text
GN₂(n,1) = 2*n + 1
```

up to the repository's canonical `GTail d 1` notation.

After Phase 0/1, create a separate Legendre bridge rather than importing Legendre into the generic MultiGauge core.

The research question will then become:

```text
Can the L036 fresh-prime obstruction be restated as a d=2 multi-gauge
prime-capture localization theorem, and does transition-aware pruning also
control the currently open untied case?
```

No Legendre proof is claimed by this branch.

---

## Explicit non-goals for the first phase

Do not implement or claim:

```text
Norm divisibility
Eisenstein quotient landing
TraceOne lattice landing
power/Core-image landing
ABC closure
FLT closure
Legendre conjecture proof
a general automaton framework
an abstract category of gauge transitions
```

Do not introduce provider assumptions merely to make escape transport true. The two-stage transport statements must follow from the explicit transition balance law and ordinary prime divisibility.

---

## Proof discipline

Production code must:

```text
reuse existing GTail/GN gcd theorems;
use explicit hypotheses rather than hidden global assumptions;
introduce no sorry/admit/new axiom declarations;
keep generic MultiGauge independent of ABC/FLT/Legendre;
build focused modules before facade integration;
record theorem names and build results in report files.
```

A theorem that is only a restatement of an existing fact should be marked as a bridge/transport theorem rather than described as new mathematics.

---

## Current status

```text
branch:
  CREATED

design:
  prime escape / capture transport fixed

existing one-stage GN gcd firewall:
  PRODUCTION-PROVED

two-stage gauge packet:
  NOT IMPLEMENTED

prime escape transport:
  NOT IMPLEMENTED

finite path escape theorem:
  NOT IMPLEMENTED

Legendre d=2 application bridge:
  NOT IMPLEMENTED

Norm / lattice landing:
  DEFERRED
```
