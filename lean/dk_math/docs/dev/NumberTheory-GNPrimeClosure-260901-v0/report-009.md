# GNPC-009 report

## Outcome

Outcome A — the verified GNPC-001 through GNPC-008 theory is now available
through one public NumberTheory facade and through the repository root.

Downstream code can use either:

```lean
import DkMath.NumberTheory.GNPrime
```

or:

```lean
import DkMath
```

without importing the internal GNPC owners individually.

## Public facade

Facade path and import name:

```text
DkMath/NumberTheory/GNPrime.lean
import DkMath.NumberTheory.GNPrime
```

The facade is import-only apart from its module documentation. It contains no
copied theorem, alias, namespace wrapper, or additional mathematical proof.

The exact eight explicit owner imports are:

```lean
import DkMath.NumberTheory.GNPrimeClosure
import DkMath.NumberTheory.GNRepresentationBounds
import DkMath.NumberTheory.GNDegreeFactorization
import DkMath.NumberTheory.GNPrimeTargetResidue
import DkMath.NumberTheory.GNThreeQuadratic
import DkMath.NumberTheory.GNThreePrimeArithmetic
import DkMath.NumberTheory.GNThreeHenselLift
import DkMath.NumberTheory.GNThreeHenselDepth
```

The logical grouping is:

```text
General GN prime layer:
  GNPrimeClosure
  GNRepresentationBounds
  GNDegreeFactorization
  GNPrimeTargetResidue

Degree-three shell/local layer:
  GNThreeQuadratic
  GNThreePrimeArithmetic
  GNThreeHenselLift
  GNThreeHenselDepth
```

## Root integration

`DkMath.lean` now imports exactly one GN public facade at the requested point,
immediately after `DkMath.NumberTheory.WeightedGNBridge`:

```lean
import DkMath.NumberTheory.GNPrime
  -- NumberTheory.GNPrime: GN prime closure, prime representations, cubic shell, and finite Hensel-depth API
```

The eight owner imports were not added individually to the root. No existing
owner import was changed, and no owner imports the new facade.

## Dependency and ownership audit

The dependency direction remains:

```text
GNPrimeClosure

GNRepresentationBounds
  -> GNDegreeFactorization
  -> GNPrimeTargetResidue
     -> WeightedGNBridge

GNThreeQuadratic
  -> GNThreePrimeArithmetic
  -> GNThreeHenselLift
  -> GNThreeHenselDepth

GNPrime imports all eight owners.
DkMath imports GNPrime.
```

The facade introduces no FLT, Zsigmondy, Kummer, completion, or p-adic owner
dependency. The existing `GNPrimeTargetResidue -> WeightedGNBridge` and
`GNThreeQuadratic -> TraceOneQuadratic` dependencies are unchanged.

## Public reachability smoke test

A temporary file importing only `DkMath.NumberTheory.GNPrime` successfully
checked representative declarations from every layer:

```lean
DkMath.NumberTheory.prime_boundary_mul_GN_iff
DkMath.NumberTheory.GNPositiveRepresentation
DkMath.NumberTheory.GN_mul_degree
DkMath.NumberTheory.GNPositiveRepresentation.prime_degree_constraints
DkMath.NumberTheory.GN_three_eq_target_iff_centered_square
DkMath.NumberTheory.three_dvd_prime_sub_one_of_square_lift_GN_three
DkMath.NumberTheory.existsUnique_GN_three_sqLift_digit
DkMath.NumberTheory.existsUnique_GN_three_powLift_digit
```

The temporary smoke-test file was removed.

## Documentation update

`docs/dev/NumberTheory-GNPrimeClosure-260901-v0/README.md` now records the
public facade, root availability, the two owner layers, and the intentional
deferral of application-specific FLT3 integration.

## Validation

Dedicated facade build:

```text
lake build DkMath.NumberTheory.GNPrime
Build completed successfully (8681 jobs).
```

Root public-surface build:

```text
lake build DkMath
Build completed successfully (9788 jobs).
```

The new facade contains no `sorry` or `axiom`. `git diff --check` passes. No
new warning was introduced by the facade; any existing axiom-dependency or
research-placeholder information in unrelated root modules remains outside
this checkpoint.

## Scope boundary

GNPC-009 changes only public architecture and documentation. GNPC-001 through
GNPC-008 mathematics was not modified. FLT3 integration, replacement of
`hS0_not_sq`, infinite Hensel sequences, and p-adic completion remain deferred
to a later branch/checkpoint. The public GN Prime surface is ready for PR
review; this checkpoint does not open or merge a PR.
