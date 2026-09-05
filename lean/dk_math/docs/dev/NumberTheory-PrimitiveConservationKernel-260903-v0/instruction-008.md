# PCK-006 — Primorial coarse anchor to fine square world bridge

Date: 2026-09-04  
Branch: `wip/number-theory-primitive-conservation-kernel-260903-v0`  
Predecessor: `report-007.md` / PCK-005

## 0. Authorization

Implement the generic bridge from a finite prime basis to its product as a
coarse arithmetic anchor, while keeping the generating basis distinct from
the complete prime closure at that anchor.

This checkpoint must formalize the chain

```text
finite prime basis S
  ↓
A := finitePrimeBasisProduct S
  ↓
S ⊆ primeScalesUpTo A
  ↓
complete closure primeScalesUpTo A
  ↓
every fine square world q ≤ A is certified by that same complete closure
```

Do not identify `S` with `primeScalesUpTo A`. In general they are not
equal.

The canonical example `S = {2,3,5}`, `A = 30` is deferred to PCK-007.

## 1. Reuse inventory

Inspect and reuse:

```text
DkMath/NumberTheory/PrimorialUniverse/FiniteReservationEscape.lean
DkMath/NumberTheory/PrimorialUniverse/FinitePrimeSynchronization.lean
DkMath/NumberTheory/Primitive/FinitePrimeWorld.lean
DkMath/NumberTheory/Primitive/SquareBody.lean
DkMath/NumberTheory/Primitive/SquarePrimeExpansion.lean
```

Required existing surfaces include:

```lean
IsFinitePrimeBasis
finitePrimeBasisProduct
finitePrimeBasisProduct_ne_zero
mem_dvd_finitePrimeBasisProduct

primeScalesUpTo
mem_primeScalesUpTo
SupportDisjointFrom

prime_of_supportDisjointFrom_primeScalesUpTo_coarse_of_le_fine_squareBody

squarePrimeExpansion
squarePrimeExpansion_eq_primeScalesUpTo_squareBody
```

Do not duplicate any of these.

## 2. Preferred owner

Preferred new file:

```text
DkMath/NumberTheory/PrimorialUniverse/SquareBodyBridge.lean
```

Preferred namespace:

```text
DkMath.NumberTheory.PrimorialUniverse
```

Import only:

```text
FinitePrimeSynchronization
DkMath.NumberTheory.Primitive.SquarePrimeExpansion
```

plus minimal Mathlib imports if genuinely needed.

Open or qualify the Primitive namespace explicitly. Do not introduce a
dependency from Primitive back into PrimorialUniverse.

No public aggregator change in this checkpoint.

## 3. The first required theorem: basis inclusion into product closure

Prove:

```lean
/--
Every member of a finite prime basis belongs to the canonical complete prime
world at the basis-product anchor.
-/
theorem finitePrimeBasis_subset_primeScalesUpTo_product
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S) :
    S ⊆
      DkMath.NumberTheory.Primitive.primeScalesUpTo
        (finitePrimeBasisProduct S) := by
  ...
```

Preferred proof route for `p ∈ S`:

1. `hS p hp` gives `Nat.Prime p`;
2. `mem_dvd_finitePrimeBasisProduct hp` gives
   `p ∣ finitePrimeBasisProduct S`;
3. `finitePrimeBasisProduct_ne_zero hS` gives positivity of the product;
4. `Nat.le_of_dvd` gives
   `p ≤ finitePrimeBasisProduct S`;
5. package with `mem_primeScalesUpTo`.

This theorem is semantically load-bearing because it fixes:

> generating prime basis ⊆ complete closure at the product anchor.

It does NOT assert equality.

## 4. The second required theorem: product anchor certifies fine worlds

Let

$$
A=
\operatorname{finitePrimeBasisProduct}(S).
$$

Prove a thin wrapper of PCK-003:

```lean
/--
The complete prime closure at a finite-basis product anchor certifies every
fine square world below that anchor.
-/
theorem prime_of_supportDisjointFrom_productClosure_of_le_fine_squareBody
    {S : Finset ℕ} {q m : ℕ}
    (hq :
      q ≤ finitePrimeBasisProduct S)
    (hm : 1 < m)
    (hmUpper :
      m ≤ DkMath.NumberTheory.Primitive.squareBody q)
    (hdisj :
      DkMath.NumberTheory.StructuralArithmetic.SupportDisjointFrom
        (DkMath.NumberTheory.Primitive.primeScalesUpTo
          (finitePrimeBasisProduct S))
        m) :
    Nat.Prime m := by
  ...
```

Preferred proof: one exact application of

```lean
prime_of_supportDisjointFrom_primeScalesUpTo_coarse_of_le_fine_squareBody
```

with coarse anchor `finitePrimeBasisProduct S`.

### Important hypothesis policy

Do NOT add `hS : IsFinitePrimeBasis S` to this theorem merely for naming
semantics if the proof does not need it.

Mathematically, the theorem is true for any finite set `S` because only its
natural-number product is used as the coarse anchor.

The finite-prime-basis semantics are supplied separately by theorem 3 above.

This separation is deliberate:
- theorem 3 says when the product really comes from a prime basis;
- theorem 4 says any resulting numeric anchor can drive the already-proved
  coarse-to-fine certification.

## 5. Optional packaged bridge

Only if it remains genuinely useful and very small, MAY add one theorem that
combines the two facts under `hS`:

```lean
theorem finitePrimeBasis_product_coarseAnchor_packet
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q m : ℕ}
    (hq : q ≤ finitePrimeBasisProduct S)
    (hm : 1 < m)
    (hmUpper : m ≤ Primitive.squareBody q)
    (hdisj :
      SupportDisjointFrom
        (Primitive.primeScalesUpTo (finitePrimeBasisProduct S)) m) :
    S ⊆ Primitive.primeScalesUpTo (finitePrimeBasisProduct S) ∧
      Nat.Prime m := by
  ...
```

This is optional. Do not add it if it merely duplicates the two required
theorems without improving downstream use.

## 6. PCK-005 expansion specialization

A one-line specialization of PCK-005 is useful but optional:

```lean
theorem squarePrimeExpansion_product_eq_complete_squareClosure
    (S : Finset ℕ) :
    Primitive.squarePrimeExpansion (finitePrimeBasisProduct S) =
      Primitive.primeScalesUpTo
        (Primitive.squareBody (finitePrimeBasisProduct S)) := by
  exact
    Primitive.squarePrimeExpansion_eq_primeScalesUpTo_squareBody
      (finitePrimeBasisProduct S)
```

Add this only if it improves the bridge narrative. It is not the main theorem.

Do not define a new expansion operator parameterized by `S`.

## 7. Mathematical meaning

This checkpoint must make the following distinction explicit in module
docstring and report.

For a finite prime basis `S`,

$$
A=\prod_{p\in S}p
$$

is a synchronization/product anchor.

But the complete prime support at that anchor is

$$
\mathcal P_{\le A}
=
\operatorname{primeScalesUpTo}(A).
$$

In general,

$$
S\ne\mathcal P_{\le A}.
$$

For example, the later canonical case is

$$
S=\{2,3,5\},
\qquad
A=30,
$$

while

$$
\mathcal P_{\le30}
=
\{2,3,5,7,11,13,17,19,23,29\}.
$$

PCK-006 itself should not hard-code this example; PCK-007 will.

The generic theorem says that once the complete closure at `A` is available,
that single coarse support certifies every fine square anchor

$$
q\le A.
$$

Thus

$$
\boxed{
A\text{ coarse world}
\supset
\text{all fine square worlds }q\le A
}
$$

in the precise certification sense.

## 8. Relation to PCK-005

PCK-005 already proves

$$
\operatorname{squarePrimeExpansion}(A)
=
\operatorname{primeScalesUpTo}(\operatorname{squareBody}(A)).
$$

Therefore after PCK-006 the formal architecture is:

```text
S
  -> finitePrimeBasisProduct S = A
  -> complete support primeScalesUpTo A
  -> all q ≤ A fine worlds certified
  -> squarePrimeExpansion A
  -> complete support through squareBody A
```

Do not claim that `S` alone certifies the square Body.

The complete closure `primeScalesUpTo A` is essential.

## 9. Firewalls

PCK-006 must not:

- assert `S = primeScalesUpTo (finitePrimeBasisProduct S)`;
- use basis survivor / wheel coprimality as a primality criterion;
- add `PrimeCompleteUpTo` or equivalent;
- define a new primorial function;
- implement `30 → 960` numeric regressions;
- implement fresh-prime lift or wheel refinement;
- add Gnomon resolution/projective theorems;
- add RH, zeta, Xi, PHZ, CFBRC, or analytic dependencies;
- introduce a generic `PrimitiveKernel` abstraction;
- use `sorry`, `admit`, `native_decide`, or a project axiom.

## 10. Verification

Run at least:

```text
lake build DkMath.NumberTheory.PrimorialUniverse.SquareBodyBridge
git diff --check
```

Run axiom checks on the two required theorems.

If the optional PCK-005 specialization is added, axiom-check it as well.

Audit:
- no forbidden imports;
- no accidental basis/closure equality;
- no unused semantic hypothesis added merely to make a theorem look
  primorial-specific.

## 11. Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveConservationKernel-260903-v0/report-008.md
```

Record:

- Outcome
- starting HEAD
- changed files
- exact owner/imports
- basis-inclusion theorem and proof route
- product-anchor fine-certification theorem and proof route
- whether the optional packet was added
- whether the PCK-005 specialization was added
- explicit basis/product/complete-closure distinction
- build result
- `git diff --check`
- axiom/sorry audit
- next authorization

## 12. Next authorization

If PCK-006 is green, authorize only:

> PCK-007 — canonical `{2,3,5} → 30 → primeScalesUpTo 30 → 960 → 31²`
> regression, including representative fine anchors below 30.

Do not implement PCK-007 in this checkpoint.
