# Finite-Prime Escape GN5 Verification

## Title and Status

- **Project:** Finite-Prime Escape GN5 Verification
- **Status:** verified
- **Role:** second-domain validation of the DkMath verification contracts
- **Date:** 2026-07-21

This is an existing DkMath finite arithmetic result packaged as a focused
verification case. It is not an external breaking-news claim.

## Exact Lean Target

```lean
#check DkMath.Hackathon.finitePrimeEscapeGN5Certificate
```

The summit theorem states:

```text
31 is prime
∧ 31 divides GN 5 1 1
∧ 31 is outside {2,3,5}
∧ 31² does not divide GN 5 1 1
∧ GN 5 1 1 is not a fifth power in ℕ.
```

## Arithmetic Object

The domain-specific object is
`DkMath.CosmicFormulaBinom.GN 5 1 1`. Existing DkMath arithmetic supplies a
fresh prime factor outside `{2,3,5}` and identifies that factor exactly as
`31`.

## Explicit Prime Witness

Exact Lean identifiers:

```text
finitePrimeEscape_hits_GN5
freshPrimeFactor_GN5_eq_31
finitePrimeEscape_hits_clean_GN5_channel
```

The explicit witness is `31`.

## Local No-Lift Obstruction

The clean-channel theorem establishes that the prime divides the target while
its square does not. The general existing bridge
`not_fifth_power_of_prime_dvd_of_not_sq_dvd` turns such a channel into a
non-fifth-power obstruction.

## Global Non-Fifth-Power Consequence

```lean
#check DkMath.Hackathon.GN_five_one_one_not_fifth_power
```

The conclusion is restricted to this concrete natural-number target.

## Summit Theorem

```lean
#check DkMath.Hackathon.finitePrimeEscapeGN5Certificate
#check DkMath.Hackathon.finitePrimeEscapeGN5DemoCertificate
```

The first theorem is a thin conjunction of existing arithmetic. The second is
a direct Demo alias.

## Module Map

```text
DkMath/Hackathon/FinitePrimeEscapeGN5.lean
    ↓
DkMath/Hackathon/FinitePrimeEscapeGN5Certificate.lean
    ↓
DkMath/Hackathon/FinitePrimeEscapeGN5Demo.lean
    ↓
DkMathTest/Hackathon/FinitePrimeEscapeGN5/CheckAxioms.lean
```

This case does not depend on `DkMath.Verification.Collision`.

## Build Commands

Run from `lean/dk_math`:

```sh
lake build DkMath.Hackathon.FinitePrimeEscapeGN5Certificate
lake build DkMath.Hackathon.FinitePrimeEscapeGN5Demo
lake build DkMathTest.Hackathon.FinitePrimeEscapeGN5.CheckAxioms
```

## Axiom Audit Target

```lean
#print axioms DkMath.Hackathon.finitePrimeEscapeGN5Certificate
#print axioms DkMath.Hackathon.finitePrimeEscapeGN5DemoCertificate
```

Exact output for both selected theorems:

```text
depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx` or DkMath-specific axiom occurs in either result.

## Trust Boundary

Lean 4 + Mathlib checks the exact arithmetic propositions encoded by the named
theorems. This package does not establish publication history, priority, peer
review, or an external authorship claim. The source and packaging boundary is
recorded in [`PROVENANCE.md`](PROVENANCE.md).

## Demo Contract

The ordered public presentation and allowed claims are recorded in
[`DEMO_CONTRACT.md`](DEMO_CONTRACT.md).

## Scope and Non-Goals

In scope:

- the explicit prime channel `31` for `GN 5 1 1`;
- its divisibility and no-square-lift properties;
- the resulting concrete non-fifth-power theorem;
- summit, Demo, audit, and documentation packaging.

Not in scope:

- FLT5;
- a general theorem about all GN values;
- a universal verification bundle;
- collision-certificate integration;
- a new proof of the existing finite arithmetic.

## Deferred Work

- Any broader Cosmic Formula interpretation remains separate from this finite
  verification certificate.
