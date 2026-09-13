# FLT prime-generalization Phase 6 — Gaussian-period factorization frontier

## Goal

Phase 5 established the neutral adapter

```text
4 * V = R^2 - discr(s) * S^2
  -> norm (⟨A,S⟩ : TraceOneInt s) = V
```

once `R = 2*A + S` is available.  The remaining gap is no longer on the
`TraceOneInt` side.  It is the arbitrary-odd-prime construction of integral
Gauss coordinates attached to the quadratic residue / nonresidue split of the
prime cyclotomic shell.

This phase must locate that frontier precisely.  Do not claim a general FLT
theorem and do not force a full arbitrary-prime integral-coordinate theorem if
Mathlib support is insufficient.

## Scope discipline

Work on the existing branch

```text
refact/FLT-Prime-Generalization-260911-v0
```

Do not change the proved FLT3, FLT5, or FLT7 endpoints.

Prefer new neutral/test modules under

```text
DkMath/NumberTheory/
DkMathTest/FLT/Prime/
```

Do not introduce `sorry`, `axiom`, or opaque trust assumptions.

## Part A — neutral conjugate-factor algebra

Add a small neutral API, preferably in a new module such as

```text
DkMath/NumberTheory/QuadraticConjugateFactor.lean
```

or another clearly named NumberTheory module.

For a commutative ring, prove the algebraic identity behind the Gauss form.
At minimum establish a theorem equivalent to

```text
R = U + V
C = U * V
(U - V)^2 = D * S^2
--------------------------------
4 * C = R^2 - D * S^2
```

with the weakest practical assumptions.

Also prove the raw identity

```text
(U + V)^2 - 4*(U*V) = (U - V)^2.
```

This theorem is independent of cyclotomic fields and should be reusable.

Then connect the result to the Phase-5
`norm_eq_of_gauss_coordinates` adapter in a small test: once the Gauss form and
`R = 2*A + S` are supplied, recover the `TraceOneInt` norm.

## Part B — canonical signed prime discriminant audit

Audit pinned Mathlib for an existing theorem/API expressing the sign

```text
D_p = (-1)^((p-1)/2) * p
```

for odd prime `p`, preferably through the quadratic character / Legendre symbol
at `-1` rather than by unsafe Nat-to-Int exponent tricks.

If a clean existing theorem is available, wrap it minimally.  Otherwise define
only a bounded local/test representation, for example by `p % 4`, and prove
what is needed for the probes.

Required facts to seek/prove in the bounded setting:

```text
D_p = p or D_p = -p
Int.natAbs D_p = p
D_p % 4 = 1
```

The final congruence is what makes

```text
s_p = (D_p - 1) / 4
```

an integral TraceOne parameter with `discr s_p = D_p`.

Do not promote a canonical `s_p` to production unless the integer division and
sign proof are clean and kernel-checked.

## Part C — quadratic-residue / nonresidue factorization probe

The main experiment is to determine how far Mathlib lets us formalize the
standard index-two factorization before integrality becomes the obstacle.

For an odd prime `p`, conceptually split the nonzero exponents modulo `p` into
quadratic residues and nonresidues.  In a ring containing a primitive p-th root
`ζ`, the target objects are the two conjugate factors

```text
P_plus (X,Y)  = ∏_{a quadratic residue}    (X - ζ^a * Y)
P_minus(X,Y)  = ∏_{a quadratic nonresidue} (X - ζ^a * Y)
```

whose product is the homogeneous prime cyclotomic shell.

Do not assume these exact definitions if Mathlib has a better representation.
First audit the available APIs for:

- cyclotomic fields / primitive roots of unity;
- finite products over `(ZMod p)ˣ` or nonzero residues;
- quadratic characters and residue/nonresidue partition;
- Galois/conjugation action sending `ζ` to `ζ^a`;
- fixed-subring / coefficient descent support.

Attempt the following in increasing order of difficulty.

### Probe C1 — combinatorial exponent partition

Prove that the nonzero residue classes mod `p` split into the QR and QNR sets,
with the expected cardinalities `(p-1)/2` and disjoint union.

### Probe C2 — product recombination

In the weakest practical abstract setting, prove that the product over QR times
the product over QNR recombines to the product over all nonzero exponents.

A fully identified cyclotomic polynomial is not yet required for C2; a finite
product identity is enough.

### Probe C3 — cyclotomic shell identification

If Mathlib support permits, identify the full nonzero-exponent product with
`GTailCyclotomicShell p (z-y) y` or the corresponding homogeneous prime
cyclotomic polynomial after evaluation.

### Probe C4 — conjugation swap

If practical, prove that the relevant quadratic conjugation swaps the QR/QNR
factors.  This is the conceptual source of

```text
R = P_plus + P_minus
P_plus - P_minus = sqrt(D_p) * S.
```

Do not claim integral `R,S` from C4 unless coefficient descent is actually
proved.

## Part D — integrality frontier

The main deliverable is a precise classification of the first missing theorem.
Distinguish at least these possible frontiers:

```text
PGEN-GAUSS-QR-PARTITION
  QR/QNR finite combinatorics is formalized, but cyclotomic product is not.

PGEN-GAUSS-FACTOR-GREEN
  QR/QNR factors and their product = cyclotomic shell are formalized, but
  coefficient descent / integrality is missing.

PGEN-GAUSS-CONJ-GREEN
  factorization and conjugation swap are formalized, but integral R_p,S_p are
  missing.

PGEN-GAUSS-INTEGRAL-GREEN
  integral homogeneous R_p,S_p and the Gauss form are fully constructed for
  arbitrary odd prime p.
```

If the last outcome is not reached, report exactly why: missing Mathlib API,
coefficient descent theorem, square-root normalization, parity/integrality, or
another concrete obstruction.

## Part E — finite regression anchors

Keep `p = 11` and `p = 13` as exact anchors.

If C1–C4 produces abstract `P_plus/P_minus` objects, show as much compatibility
as practical with the already-proved

```text
R11, S11, A11, B11
R13, S13, A13, B13
```

without replacing the direct regression proofs.

Also keep the known `p = 3,5,7` discriminant samples green.

## Part F — FLT relevance boundary

The report must explicitly separate three layers:

```text
1. generic odd-prime GTail / PrimeAdicPowerSplit          [already GREEN]
2. generic prime-discriminant TraceOne axis / Gauss form [already GREEN]
3. arbitrary-prime Gaussian-period integral coordinates  [this phase]
```

Explain that even a GREEN result for layer 3 would not by itself prove general
FLT.  It would only generalize the quadratic cyclotomic front-end.  Any later
unit-class, ideal-factorization, class-group, descent, or contradiction layer
must be audited separately.

## Suggested builds

Run focused builds for every new module/test plus at least:

```text
lake build DkMath.NumberTheory.TraceOneDiscriminantAxis
lake build DkMath.FLT.Prime.AdicPowerSplit
lake build DkMathTest.FLT.Prime.QuadraticCyclotomicBridgeProbe
lake build DkMath.FLT.Seven
```

If a new production NumberTheory module is added, add a focused axiom audit.

## Deliverable

Create

```text
docs/refact/FLT-Prime-Generalization-260911-v0/report-006.md
```

with:

- exact theorem/declaration names added;
- Mathlib APIs actually used;
- highest successful C1/C2/C3/C4 stage;
- precise first missing theorem if arbitrary-prime integrality remains open;
- p=11/13 regression status;
- focused build results;
- axiom audit results;
- explicit statement that no general FLT theorem is claimed.
