# FLT prime-generalization Phase 8 — QR/QNR polynomial lift and abstract Galois action

## Status entering this phase

Phase 7 reached:

```text
PGEN-GAUSS-FACTOR-GREEN
```

Production now proves, for a field `K`, prime `p`, primitive `p`-th root `ζ`, and endpoints `(x,u)`,

```text
QRProduct(ζ,x+u,u) * QNRProduct(ζ,x+u,u)
  = GTailCyclotomicShell p x u.
```

The first open layer is C4: conjugation/Galois action and coefficient descent.

This phase is deliberately bounded.  Do **not** attempt full integral Gaussian-period coordinates, full arbitrary-prime TraceOne coordinates, class-group arguments, or an FLT contradiction.

## Goal

Promote the QR/QNR factors from evaluated field elements to homogeneous two-variable polynomials, then prove the abstract automorphism action law

```text
σ(ζ) = ζ^t
```

on those factors.

The target structural result is:

```text
square t     -> QR and QNR factors are each preserved,
nonsquare t  -> QR and QNR factors are swapped.
```

Consequently the symmetric sum is invariant under either case, while the difference transforms by the quadratic character sign.

The existence/surjectivity of cyclotomic Galois automorphisms realizing every nonzero `t` is **not** required in this phase.  Treat that as the next instantiation layer.

---

## Part A — polynomial lift of the existing factors

Prefer a new neutral production module, for example:

```text
DkMath/NumberTheory/CyclotomicQRGaloisAction.lean
```

It may import `DkMath.NumberTheory.CyclotomicQRProduct` plus the minimum Mathlib polynomial/automorphism API required.  It must not import `DkMath.FLT.*`.

Use a genuine two-variable polynomial representation, preferably

```lean
MvPolynomial (Fin 2) K
```

with variable 0 for `X` and variable 1 for `Y`.

Define a polynomial analogue of the existing factor:

```text
rootFactorPoly ζ a
  = X₀ - C(ζ^a.val) * X₁.
```

Then define

```text
qrFactorPoly  ζ := ∏ a in qrFinset  p, rootFactorPoly ζ a
qnrFactorPoly ζ := ∏ a in qnrFinset p, rootFactorPoly ζ a
```

Prove evaluation compatibility with the existing production API:

```text
eval(X,Y) (rootFactorPoly ζ a) = rootFactor ζ a X Y

eval(X,Y) (qrFactorPoly ζ) = existing QR product

eval(X,Y) (qnrFactorPoly ζ) = existing QNR product.
```

If a different polynomial representation is substantially easier in the pinned Mathlib checkout, document the choice and preserve a clean two-variable evaluation theorem.

### A1 — polynomial C3 compatibility

If straightforward, prove the polynomial-level product identity

```text
qrFactorPoly ζ * qnrFactorPoly ζ
  = homogeneous prime cyclotomic polynomial
```

or an equivalent polynomial object whose evaluation is already known to be `GTailCyclotomicShell`.

Do not block the phase on A1 if the existing evaluated C3 bridge is the cleaner compatibility route.  The mandatory target is the polynomial lift plus automorphism action below.

---

## Part B — exponent multiplication on `ZMod p`

Let

```text
t : ZMod p
```

with `t ≠ 0`.

Prove the finite permutation facts needed for the action law:

```text
mulBy_t_nonzero_bijective
mulBy_t_permutes_nonzeroResidues
```

and the quadratic-class behavior:

```text
IsSquare t -> multiplication by t preserves qrFinset
IsSquare t -> multiplication by t preserves qnrFinset
¬ IsSquare t -> multiplication by t sends qrFinset to qnrFinset
¬ IsSquare t -> multiplication by t sends qnrFinset to qrFinset.
```

Use the existing pinned quadratic-character API when it shortens the nonsquare proof.  Avoid ad hoc enumeration or finite-field computation tied to small primes.

The result must hold for arbitrary prime `p`; any oddness requirement should be stated explicitly and justified.  If `p=2` is the unique obstruction, record that boundary rather than silently strengthening assumptions.

---

## Part C — abstract automorphism action on primitive-root factors

Let

```text
σ : K ≃+* K
```

and assume

```text
hσζ : σ ζ = ζ ^ t.val
```

for nonzero `t : ZMod p`.

Prove the root-factor coefficient action.  The exact Lean statement may use `MvPolynomial.map σ.toRingHom` or the appropriate pinned API:

```text
map σ (rootFactorPoly ζ a)
  = rootFactorPoly ζ (t * a)
```

up to the canonical `ZMod p` representative/exponent normalization required by Lean.

The proof must explicitly justify the exponent reduction modulo `p` from primitive-root periodicity.  Do not hide a representative mismatch behind unchecked simp assumptions.

Then lift this to the finite products.

### C1 — square action

Under `IsSquare t`, prove

```text
map σ (qrFactorPoly ζ)  = qrFactorPoly ζ
map σ (qnrFactorPoly ζ) = qnrFactorPoly ζ.
```

### C2 — nonsquare action

Under `¬ IsSquare t`, prove

```text
map σ (qrFactorPoly ζ)  = qnrFactorPoly ζ
map σ (qnrFactorPoly ζ) = qrFactorPoly ζ.
```

This is the primary Phase-8 theorem family.

---

## Part D — symmetric and antisymmetric combinations

Define or use local abbreviations

```text
Rpoly := qrFactorPoly ζ + qnrFactorPoly ζ
Dpoly := qrFactorPoly ζ - qnrFactorPoly ζ.
```

Prove:

```text
map σ Rpoly = Rpoly
```

for both square and nonsquare `t`.

For the difference prove the exact sign law:

```text
IsSquare t   -> map σ Dpoly =  Dpoly
¬ IsSquare t -> map σ Dpoly = -Dpoly.
```

If convenient and well-supported by the pinned API, package this with the quadratic character as a single theorem.  A two-case theorem is fully acceptable and preferable to introducing brittle coercions.

Corollary:

```text
map σ (Dpoly^2) = Dpoly^2
```

for every automorphism satisfying the stated primitive-root power condition.

This square invariance is the exact bridge needed before coefficient descent.

---

## Part E — finite compatibility / regression

Add focused tests for at least

```text
p = 3, 5, 7, 11, 13
```

using an ambient field and concrete primitive root already available in the existing probes.

For `p = 11` and `p = 13`, connect evaluation of the new polynomial factors back to the Phase-7 C3 product and the Phase-5 TraceOne norm regressions.  Do not attempt to identify individual QR/QNR factors with the explicit `A11/B11` or `A13/B13` coordinates yet unless it falls out essentially for free.

The regression target is only that the polynomial lift has not changed the already-proved shell/product identities.

---

## Part F — pinned Mathlib audit for the next layer

Audit the **pinned repository checkout** for the following capabilities and report exact declaration names when present:

1. `IsPrimitiveRoot.autToPow` and related automorphism-to-exponent APIs;
2. cyclotomic extension / Galois group equivalences that realize a prescribed nonzero power `t`;
3. fixed-field or coefficient-fixedness tools sufficient to descend a polynomial fixed by every `ℚ`-automorphism to `ℚ` coefficients;
4. ring-of-integers / integrality tools sufficient to upgrade rational fixed coefficients to integers.

Current public Mathlib documentation suggests relevant APIs exist around primitive roots and cyclotomic number fields, but the pinned checkout is authoritative.

Do **not** use these APIs to force the full descent in this phase unless it is genuinely short and stable.  Record the exact next missing theorem instead.

Expected next boundary after a successful Phase 8:

```text
abstract QR/QNR Galois action       [GREEN]
existence of all cyclotomic actions [NEXT]
coefficient descent to ℚ/ℤ          [OPEN]
integral Gaussian coordinates       [OPEN]
```

---

## Part G — classifications

Use one of the following outcome labels.

```text
PGEN-GAUSS-ACTION-GREEN
```

if the arbitrary-prime polynomial lift and square/nonsquare automorphism action are proved.

```text
PGEN-GAUSS-ACTION-EVAL-ONLY
```

if the action is obtained only after evaluation and a stable polynomial-level theorem cannot be proved.

```text
PGEN-GAUSS-ACTION-BLOCKED
```

if the first missing theorem lies before the square/nonsquare swap law; identify the exact API or mathematical obstruction.

Do not claim coefficient descent, integral Gaussian coordinates, or general FLT from `PGEN-GAUSS-ACTION-GREEN` alone.

---

## Required verification

At minimum run focused builds for:

```text
DkMath.NumberTheory.CyclotomicQRProduct
DkMath.NumberTheory.CyclotomicQRGaloisAction
DkMath.NumberTheory.QuadraticConjugateFactor
DkMath.NumberTheory.TraceOneDiscriminantAxis
```

plus new probe/compatibility/audit modules and existing `p=11/13` compatibility tests.

Also run:

```text
lake build DkMath.FLT.Seven
```

if dependency cost remains reasonable after the Phase-2 import split.

For new public declarations:

- `#print axioms`;
- no `sorryAx`;
- no new `sorry`;
- no explicit `axiom`;
- `git diff --check`.

Write the implementation report to:

```text
docs/refact/FLT-Prime-Generalization-260911-v0/report-008.md
```

The report must distinguish clearly between:

1. source-supported Lean results actually proved in this phase;
2. pinned-Mathlib API observations;
3. hypotheses/future coefficient-descent work.
