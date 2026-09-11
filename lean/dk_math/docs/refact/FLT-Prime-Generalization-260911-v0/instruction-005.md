# FLT prime-generalization Phase 5 — Gauss cyclotomic form to TraceOne adapter

## Goal

Phase 4 proved the neutral discriminant-axis API and explicit `p = 11,13`
quadratic norm identities.  Phase 5 must **not** claim or attempt a full
arbitrary-prime cyclotomic coordinate construction at once.

The bounded goal is to isolate the exact algebraic adapter between the
classical quadratic-form shape

```text
4 * shell = R^2 - D * S^2
```

and the DkMath `TraceOneInt s` norm, where

```text
D = discr s = 1 + 4*s.
```

The key neutral identity already available is

```text
4 * norm (⟨A,B⟩ : TraceOneInt s)
  = (2*A + B)^2 - discr s * B^2.
```

Thus the intended coordinate conversion is

```text
R = 2*A + B
S = B
```

or conversely, when `R - S` is even,

```text
A = (R - S) / 2
B = S.
```

This phase should prove the adapter and verify that the existing `p=11,13`
probes are instances of it.  The existence of suitable `R_p,S_p` for every
odd prime remains a separate future theorem unless Lean formalization in the
pinned Mathlib makes it immediate.

## Part A — neutral Gauss-form adapter

Add a production theorem in the neutral TraceOne layer (preferably
`DkMath.NumberTheory.TraceOneDiscriminantAxis`, unless a smaller new generic
module is cleaner):

```lean
theorem norm_eq_of_discriminant_form
    {s A B V : ℤ}
    (h : 4 * V = (2*A + B)^2 - discr s * B^2) :
    norm (⟨A,B⟩ : TraceOneInt s) = V := by
  ...
```

Use `four_mul_traceOneNorm_eq_discriminant` and exact integer cancellation;
do not use positivity.

Also prove a converse packaging theorem:

```lean
theorem discriminant_form_of_norm_eq
    {s A B V : ℤ}
    (h : norm (⟨A,B⟩ : TraceOneInt s) = V) :
    4 * V = (2*A + B)^2 - discr s * B^2 := by
  ...
```

Then add an `R,S` adapter with an explicit integral half-coordinate rather
than hidden rational division.  One acceptable theorem shape is:

```lean
theorem norm_eq_of_gauss_coordinates
    {s A R S V : ℤ}
    (hR : R = 2*A + S)
    (hForm : 4*V = R^2 - discr s * S^2) :
    norm (⟨A,S⟩ : TraceOneInt s) = V := by
  ...
```

Optionally add an existence wrapper from an evenness/parity hypothesis on
`R-S`, but do not force it if it creates unnecessary integer-division noise.
The primary API should remain division-free.

## Part B — signed prime discriminant packet

Connect `PrimeDiscriminantPacket p s` to the signed discriminant used by the
cyclotomic quadratic form.  Do not encode the sign by an unsafe Nat formula.
Prove or package a clean theorem that the packet gives

```text
discr s = +p  or  discr s = -p.
```

This already exists as `PrimeDiscriminantPacket.discr_eq_or_neg`; reuse it.

For concrete prime-cyclotomic probes record the expected sign

```text
D_p = (-1)^((p-1)/2) * p
```

only where Lean can state it cleanly over `ℤ`.  A generic proof of this signed
formula is not required in this phase unless it follows from a small parity
lemma.  The packet itself intentionally knows only `|D| = p`.

## Part C — refactor p=11 and p=13 probes through the adapter

In `DkMathTest.FLT.Prime.QuadraticCyclotomicBridgeProbe`, retain the proved
`A11,B11,A13,B13` coordinates and define the associated Gauss-form
coordinates

```text
R11 := 2*A11 + B11
S11 := B11
R13 := 2*A13 + B13
S13 := B13
```

Prove the quadratic-form identities

```text
4 * GTailCyclotomicShell 11 (z-y) y
  = R11(z,y)^2 - (-11) * S11(z,y)^2

4 * GTailCyclotomicShell 13 (z-y) y
  = R13(z,y)^2 - 13 * S13(z,y)^2
```

and then rederive `norm11` and `norm13` through the generic adapter.

The old direct `ring` identities may remain as regression checks, but the
main theorem path should demonstrate that the TraceOne norm bridge is exactly
the quadratic discriminant-form bridge.

Also check the parity/integrality relation implicitly built into the chosen
coordinates:

```text
R11 - S11 = 2*A11
R13 - S13 = 2*A13.
```

## Part D — audit p=3,5,7 in the same form

Do not rewrite the completed FLT3/5/7 towers.  Add focused tests that expose
existing bridge coordinates in the same shape wherever practical:

```text
4 * shell = R^2 - D*S^2
```

with `D = -3, 5, -7` respectively.

The minimum acceptable result is to use the existing TraceOne bridge theorem
for each case and derive its discriminant-form identity by
`four_mul_traceOneNorm_eq_discriminant`.

This is a normalization audit, not a proof-tower refactor.

## Part E — arbitrary-prime bridge boundary

Inspect the pinned Mathlib for a theorem equivalent to the classical Gauss
cyclotomic quadratic-form identity for an odd prime.  Relevant audited areas
from Phase 4 include Gauss sums, Legendre/quadratic characters, and cyclotomic
polynomials.

Classify the result precisely:

- `PGEN-GAUSS-AVAILABLE`: Mathlib already exposes enough to construct the
  homogeneous integral `R_p,S_p` and prove the form identity with modest glue.
- `PGEN-GAUSS-DERIVABLE`: required Gauss-sum/character theorems exist, but an
  integral polynomial-coordinate construction must still be written.
- `PGEN-GAUSS-MISSING`: the necessary construction is absent and would require
  substantial new number-theory formalization.

Do **not** synthesize a fake generic coordinate definition merely to obtain a
statement.  A definition whose field is already the desired norm equality is
not progress.

If the general construction is missing, document the exact missing theorem in
mathematical form.  The desired endpoint is essentially a family of integral
homogeneous polynomials `R_p,S_p` such that, for odd prime `p`,

```text
4 * GTailCyclotomicShell p (z-y) y
  = R_p(z,y)^2 - D_p * S_p(z,y)^2,
D_p = (-1)^((p-1)/2) * p,
```

plus the parity condition needed to recover integral TraceOne coordinates

```text
R_p - S_p = 2*A_p.
```

## Part F — verification

At minimum run:

```text
lake build DkMath.NumberTheory.TraceOneDiscriminantAxis
lake build DkMathTest.FLT.Prime.TraceOneDiscriminantAxisCompatibility
lake build DkMathTest.FLT.Prime.QuadraticCyclotomicBridgeProbe
lake build DkMathTest.FLT.Prime.TraceOneDiscriminantAxisAxiomAudit
```

Add a focused axiom audit for the new generic adapter if it is not already
covered.

Requirements:

- no `sorry`;
- no new `axiom`;
- no `sorryAx` in checked declarations;
- `git diff --check` green.

## Report

Write

```text
docs/refact/FLT-Prime-Generalization-260911-v0/report-005.md
```

The report must distinguish clearly:

1. proved neutral TraceOne algebra;
2. proved finite `p=3,5,7,11,13` instances;
3. classical/general mathematical target;
4. what the pinned Mathlib actually supplies;
5. the exact remaining formalization gap.

Do not claim general FLT or an arbitrary-prime cyclotomic bridge unless Lean
actually proves the generic coordinate construction.