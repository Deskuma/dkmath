# PUU-L011 — Legendre Square-Offset / Primorial Wheel Bridge

## Status

Implementation instruction for the next checkpoint on branch
`wip/number-theory-primorial-unit-universe-260827-v0`.

PUU-L010 completed the provider-side square-anchor / square-shell projection
inside `DkMath.NumberTheory.PrimorialUniverse`, deliberately without importing
Legendre.  PUU-L011 is the consumer bridge: reuse the existing Legendre square
shell API and identify its bounded-prime cover exactly with the new finite
prime-basis reservation / wheel-survivor language.

Do not move Legendre definitions into `PrimorialUniverse` and do not make the
PrimorialUniverse facade depend on Legendre.

## Preferred module

Create

```text
DkMath/NumberTheory/Legendre/PrimorialWheelBridge.lean
```

Preferred imports:

```lean
import DkMath.NumberTheory.Legendre.Frontier
import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOrbit
```

Export the new bridge from `DkMath.NumberTheory.Legendre` facade.  The
provider dependency direction must remain

```text
PrimorialUniverse.SquareAnchorOrbit
          ↓
Legendre.PrimorialWheelBridge
```

and never the reverse.

Use namespaces / `open` declarations as needed, but preserve the existing
public terminology from both sides.

## Existing APIs to reuse

Legendre side already provides:

```lean
SquareOffset n r
SquareOffsetForbiddenBy n q r
SquareOffsetCovered n r
squareOffsetCovered_iff_exists_prime_dvd
supportDisjointFrom_primeScalesUpTo_square_add_iff_not_covered
prime_of_squareAnchoredSupportEscape
LegendreConjecture
legendreConjecture_iff_squareAnchoredSupportEscape
```

Primitive side provides `primeScalesUpTo n` and its membership theorem.

PrimorialUniverse side already provides:

```lean
IsFinitePrimeBasis
ReservedByPrimeBasis
IsPrimeBasisWheelSurvivor
squareShellWheelProjection
reservedByPrimeBasis_projection_iff
squareShell_not_reserved_iff_projection_survivor
```

Do not duplicate these definitions.

## 1. Bounded-prime set is a finite prime basis

Prove the direct adapter

```lean
theorem primeScalesUpTo_isFinitePrimeBasis (n : ℕ) :
    IsFinitePrimeBasis (primeScalesUpTo n)
```

using the existing `mem_primeScalesUpTo` theorem.

Also provide the nonempty adapter for the range where the current open-period
wheel survivor is meaningful:

```lean
theorem primeScalesUpTo_nonempty_of_two_le
    {n : ℕ} (hn : 2 ≤ n) :
    (primeScalesUpTo n).Nonempty
```

The intended witness is `2`.

Do not hide the `n = 1` edge case.  It is semantically real because
`primeScalesUpTo 1 = ∅`, the finite product is `1`, and the current survivor
predicate uses `0 < r < M`.

## 2. Exact cover / reservation dictionary

Prove that the old Legendre cover predicate is exactly the new reservation
predicate:

```lean
theorem squareOffsetCovered_iff_reservedByPrimeBasis
    {n r : ℕ} :
    SquareOffsetCovered n r ↔
      ReservedByPrimeBasis (primeScalesUpTo n) (n ^ 2 + r)
```

This should be a definitional / elementary bridge, not a new counting proof.

Also expose the negated form:

```lean
theorem not_squareOffsetCovered_iff_not_reservedByPrimeBasis
    {n r : ℕ} :
    ¬ SquareOffsetCovered n r ↔
      ¬ ReservedByPrimeBasis (primeScalesUpTo n) (n ^ 2 + r)
```

If useful, add the support-disjoint form as a corollary, reusing
`supportDisjointFrom_primeScalesUpTo_square_add_iff_not_covered` rather than
reproving support semantics.

## 3. Projected survivor dictionary for `2 ≤ n`

For `2 ≤ n`, combine the adapters above with PUU-L010:

```lean
theorem not_squareOffsetCovered_iff_projection_survivor
    {n r : ℕ} (hn : 2 ≤ n) :
    ¬ SquareOffsetCovered n r ↔
      IsPrimeBasisWheelSurvivor (primeScalesUpTo n)
        (squareShellWheelProjection (primeScalesUpTo n) n r)
```

This is the exact bridge from the old Legendre finite-wave language to the new
primorial-wheel seat language.

The theorem itself does not require `SquareOffset n r`; it is only a statement
about bounded-prime reservation of the absolute point `n^2+r`.

## 4. Square-shell primality equivalence

Now add the geometric shell hypothesis.  Reuse the existing Frontier theorem
for the difficult direction; do not rebuild the small-prime-factor argument
unless a tiny converse helper is needed.

Preferred theorem:

```lean
theorem squareOffset_prime_iff_not_covered
    {n r : ℕ}
    (hn : 0 < n)
    (hr : SquareOffset n r) :
    Nat.Prime (n ^ 2 + r) ↔
      ¬ SquareOffsetCovered n r
```

For `¬ covered → prime`, pass through
`supportDisjointFrom_primeScalesUpTo_square_add_iff_not_covered` and
`prime_of_squareAnchoredSupportEscape`.

For `prime → ¬ covered`, use the existing bounded-prime semantics: a covering
prime `q ≤ n` dividing the prime point must equal that point, contradicting
that a square-cell point is strictly above `n`.

Keep this proof local and small.

Then combine with the projected-survivor bridge:

```lean
theorem squareOffset_prime_iff_projection_survivor
    {n r : ℕ}
    (hn : 2 ≤ n)
    (hr : SquareOffset n r) :
    Nat.Prime (n ^ 2 + r) ↔
      IsPrimeBasisWheelSurvivor (primeScalesUpTo n)
        (squareShellWheelProjection (primeScalesUpTo n) n r)
```

This theorem is important semantically:

- a generic finite-basis survivor is **not** a primality predicate;
- inside the consecutive-square shell, with the full bounded-prime basis
  `primeScalesUpTo n`, survivor status **is** equivalent to primality.

State this distinction clearly in docstrings and the report.

## 5. Optional global reduction theorem

If the local bridge is clean, package the Legendre conjecture itself as a
wheel-escape reduction from `n ≥ 2`:

```lean
theorem legendreConjecture_iff_projectedWheelEscape_from_two :
    LegendreConjecture ↔
      ∀ n : ℕ, 2 ≤ n →
        ∃ r : ℕ,
          SquareOffset n r ∧
          IsPrimeBasisWheelSurvivor (primeScalesUpTo n)
            (squareShellWheelProjection (primeScalesUpTo n) n r)
```

The reverse direction must handle `n = 1` separately with the explicit prime
witness `2`; for `n ≥ 2`, use the local primality equivalence.

This is a reduction theorem only.  It must not be presented as a proof of
Legendre's conjecture.

If packaging the global iff introduces disproportionate engineering, stop
with the local exact theorem from section 4 and report the global packaging as
remaining optional work.  The local theorem is the required mathematical
checkpoint.

## 6. Visible regressions

Include at least one small bridge regression around `n = 4`:

```text
n = 4
primeScalesUpTo 4 = {2,3}
4^2 + 1 = 17
17 mod 6 = 5
5 is a {2,3}-wheel survivor
17 is prime
```

A theorem packet may record the cover/reservation/projected-survivor/primality
agreement for this point.

Also include an explicit `n = 1` boundary regression if useful, showing why the
projected-survivor formulation starts from `2 ≤ n` rather than silently
pretending the empty-basis wheel has the same recurrence semantics.

## 7. Report

Create

```text
lean/dk_math/docs/dev/NumberTheory-PrimorialUnitUniverse-260827-v0/
  primorial-unit-universe-legendre-wheel-bridge-260827.md
```

The report must explicitly state:

1. `SquareOffsetCovered` is exactly finite-prime-basis reservation.
2. For `2 ≤ n`, non-cover is exactly projected wheel-survivor status.
3. Under `SquareOffset n r`, this becomes exact primality.
4. Generic wheel survivor is not globally synonymous with prime; the
   square-shell bound is what upgrades it to primality.
5. `n = 1` is a genuine empty-basis boundary of the current wheel survivor
   representation.
6. This checkpoint is a bridge / reduction, not a proof of the existence of an
   escaping offset for every square shell.

## STOP boundary

Do **not** implement in PUU-L011:

- square-hole propagation to later anchors;
- full-cover contradiction;
- Jacobsthal or maximum-gap bounds;
- new parity-safe ledgers or resurrection of the closed L043–L073 route;
- wheel-gap recursion;
- PowerSwap;
- GN/CosmicFormula;
- PNT/RH/analytic sieve arguments;
- a proof of Legendre's conjecture.

The next checkpoint after this bridge will audit the genuinely new question:
what structural statement about the square-anchor orbit would force a survivor
inside every shell, or propagate a hypothetical square hole across the nested
primorial tower.

## Outcome A+ target

PUU-L011 is Outcome A+ when the implementation provides:

1. `primeScalesUpTo` → `IsFinitePrimeBasis` adapter;
2. nonempty adapter for `2 ≤ n`;
3. cover ↔ reservation;
4. non-cover ↔ projected survivor for `2 ≤ n`;
5. square-shell prime ↔ non-cover;
6. square-shell prime ↔ projected survivor;
7. provider/consumer dependency direction preserved;
8. explicit `n = 1` semantic boundary;
9. visible regression;
10. report with no overclaim beyond reduction / bridge semantics.
