# Finite-Prime Escape GN5 Demo Contract

## Demo Goal

Show that existing DkMath arithmetic verifies an explicit clean prime channel
for `GN 5 1 1`, and that the channel obstructs this target from being a fifth
power.

## Audience

The presentation is intended for mathematical and Lean reviewers. It assumes
only familiarity with prime divisibility and `#check` / `#print axioms`.

## Public Import

```lean
import DkMath.Hackathon.FinitePrimeEscapeGN5Demo
```

This module is intentionally not imported from root `DkMath.lean` in BMV-005.

## Ordered Theorem Surface

```lean
#check DkMath.Hackathon.finitePrimeEscape_hits_GN5
#check DkMath.Hackathon.freshPrimeFactor_GN5_eq_31
#check DkMath.Hackathon.finitePrimeEscapeGN5Demo_prime
#check DkMath.Hackathon.finitePrimeEscapeGN5Demo_divides
#check DkMath.Hackathon.finitePrimeEscapeGN5Demo_noLift
#check DkMath.Hackathon.finitePrimeEscapeGN5Demo_notFifthPower
#check DkMath.Hackathon.finitePrimeEscapeGN5DemoCertificate
#print axioms DkMath.Hackathon.finitePrimeEscapeGN5DemoCertificate
```

## What Each Theorem Establishes

| Order | Theorem | Meaning |
| --- | --- | --- |
| 1 | `finitePrimeEscape_hits_GN5` | A prime channel exists outside `{2,3,5}`. |
| 2 | `freshPrimeFactor_GN5_eq_31` | That fresh prime is exactly `31`. |
| 3 | `finitePrimeEscapeGN5Demo_prime` | `31` is prime. |
| 4 | `finitePrimeEscapeGN5Demo_divides` | `31` divides `GN 5 1 1`. |
| 5 | `finitePrimeEscapeGN5Demo_noLift` | `31²` does not divide the target. |
| 6 | `finitePrimeEscapeGN5Demo_notFifthPower` | The target is not a fifth power. |
| 7 | `finitePrimeEscapeGN5DemoCertificate` | All selected facts form one summit. |

Demo theorems are projections or direct aliases of completed arithmetic.

## Trust and Axiom Statement

Exact summit audit:

```text
depends on axioms: [propext, Classical.choice, Quot.sound]
```

The presentation may say that Lean checks the displayed finite arithmetic
certificate. It must not turn this into a source-history or review claim.

## Presentation Sequence

1. Display `GN 5 1 1` and the starting set `{2,3,5}`.
2. Show existence of a fresh prime and its exact identification as `31`.
3. Show that `31` divides while `31²` does not divide.
4. Show the concrete non-fifth-power conclusion.
5. Show the summit theorem and axiom audit.

## Claims Allowed

- Lean verifies the exact displayed divisibility and no-lift propositions.
- Lean verifies that this concrete natural number is not a fifth power.
- The summit and Demo are packaging of existing DkMath arithmetic.

## Claims Not Allowed

- This proves FLT5.
- This proves a corresponding statement for every GN value.
- This is an externally published or peer-reviewed breaking-news result.
- A later Cosmic Formula interpretation is part of the finite certificate.

## Build or Check Commands

```sh
lake build DkMath.Hackathon.FinitePrimeEscapeGN5Certificate
lake build DkMath.Hackathon.FinitePrimeEscapeGN5Demo
lake build DkMathTest.Hackathon.FinitePrimeEscapeGN5.CheckAxioms
```

If a theorem name changes, resolve the replacement from the source and Demo
modules, verify its exact proposition, then rerun the focused build and audit.
