# instruction-002 — GNIP-002 Collatz gnomon compatibility recovery

## Goal

Recover the application-independent square-gnomon facts currently owned by
`DkMath.Collatz.GnomonEvaluation` onto the approved neutral source
`DkMath.Gnomon.Algebra`, while preserving the existing Collatz public API.

This checkpoint is a **compatibility refactor**, not new Collatz mathematics.

Do not touch Legendre, MultiGauge, GTail/Cosmic bridge logic, Pascal,
Polyomino, FLT, or ABC except to read for compatibility.

## Read first

```text
DkMath/Gnomon/Algebra.lean
DkMath/Gnomon/CosmicBridge.lean
DkMath/Collatz/GnomonEvaluation.lean
review-001.md
report-001.md
```

## Target production file

Primary target:

```text
DkMath/Collatz/GnomonEvaluation.lean
```

No new Collatz module is required unless a genuinely cleaner compatibility
layer is necessary. Prefer the smallest change.

---

## 1. Dependency direction

Add the neutral import:

```lean
import DkMath.Gnomon.Algebra
```

The required direction is:

```text
DkMath.Gnomon.Algebra
        ↓
DkMath.Collatz.GnomonEvaluation
```

Never import Collatz from `DkMath.Gnomon.Algebra`.

---

## 2. Make `OddGnomonLayer` reuse the neutral source

Preferred form:

```lean
def OddGnomonLayer (n : ℕ) : ℕ :=
  DkMath.Gnomon.oddGnomon n
```

If changing the definition body causes avoidable compatibility problems, it is
acceptable to retain the current definition and instead add an exact bridge:

```lean
@[simp] theorem oddGnomonLayer_eq_oddGnomon (n : ℕ) :
  OddGnomonLayer n = DkMath.Gnomon.oddGnomon n
```

But the preferred outcome is for the neutral definition to become the actual
source of truth.

All existing public names must remain available.

---

## 3. Refactor generic square facts through `DkMath.Gnomon`

Preserve the existing theorem names:

```text
square_succ_eq_square_add_oddGnomonLayer
sum_oddGnomonLayer_eq_square
sum_odd_eq_square
square_add_eq_square_add_gnomon_sum
```

Refactor their proofs to reuse the approved neutral theorems where practical:

```text
DkMath.Gnomon.square_add_oddGnomon
DkMath.Gnomon.sum_oddGnomon_eq_square
DkMath.Gnomon.sum_odd_eq_square
DkMath.Gnomon.squareGnomonBand_eq_sum_shifted_oddGnomon
DkMath.Gnomon.square_add_squareGnomonBand
```

Do not duplicate the same polynomial arguments in Collatz merely to preserve
old proof text.

For the shifted theorem, the intended compatibility statement remains:

```text
(P + u)^2
=
P^2 + Σ i<u, (2*(P+i)+1).
```

It should now be sourced from the generic band decomposition.

---

## 4. Preserve Collatz-specific dynamics unchanged

The following remain Collatz-owned and must not be moved into `DkMath.Gnomon`:

```text
RawGnomonStep
RawGnomonHeight
RawGnomonResidualShape
RawGnomonRemainderAtDepth
FirstFailedPow2Depth
rawGnomonHeight_eq_s
rawGnomonResidualShape_eq_T_val
rawGnomonResidualShape_odd
rawGnomonStep_eq_pow_height_mul_residualShape
two_pow_succ_rawGnomonHeight_not_dvd
rawGnomonRemainderAtDepth_eq_zero_of_le_height
rawGnomonRemainderAtDepth_firstFailed_ne_zero
```

The refactor must not change their statements or mathematical semantics.

`RawGnomonStep n` should still compute to

```text
n + (2*n+1) = 3*n+1.
```

Existing bridges to `threeNPlusOne`, `s`, and `T` must continue to build.

---

## 5. Compatibility theorems

If useful, add a small explicit bridge such as:

```lean
@[simp] theorem oddGnomonLayer_eq_oddGnomon (n : ℕ) :
  OddGnomonLayer n = DkMath.Gnomon.oddGnomon n := rfl
```

when definitional equality permits it.

Also consider, only if it materially helps later Legendre reuse:

```lean
theorem rawGnomonStep_eq_self_add_oddGnomon (n : ℕ) :
  RawGnomonStep n = n + DkMath.Gnomon.oddGnomon n
```

Do not add decorative aliases that are never used.

---

## 6. Regression requirements

Kernel-check that the existing Collatz identities still hold, including at
least:

```text
OddGnomonLayer 0 = 1
OddGnomonLayer 1 = 3
OddGnomonLayer 30 = 61
RawGnomonStep n = 3*n+1
(P+u)^2 = P^2 + Σ i<u, OddGnomonLayer (P+i)
```

These are compatibility regressions only.

---

## 7. Scope exclusions

Do **not** implement in GNIP-002:

```text
Legendre SquareOffset bridge
prime support / cover theorems
GTail bridge changes
new Collatz convergence claims
new valuation theory
Pascal / PetalAtom
Polyomino geometry
30 -> 31 projection law
```

The purpose is to remove duplicate ownership before Legendre is connected.

---

## 8. Validation

Run from `lean/dk_math`:

```text
lake build DkMath.Collatz.GnomonEvaluation
lake build DkMath.Collatz
lake build DkMath.Gnomon

git diff --check
```

Scan changed Lean source for:

```text
sorry
admit
axiom
```

No new axiom declarations.

Because this modifies an established Collatz module, report any downstream
build regression explicitly rather than hiding it with local rewrites.

---

## 9. Deliverable report

Create:

```text
docs/dev/NumberTheory-Gnomon-Inversion-Projection-260914-v0/report-002.md
```

Report:

1. Outcome.
2. Exact changed files.
3. Whether `OddGnomonLayer` now has neutral `oddGnomon` as source of truth.
4. Which old square/odd-sum theorems were refactored through neutral API.
5. Whether all Collatz-specific public theorem statements remained unchanged.
6. Whether `RawGnomonStep`, `s`, and `T` bridges still build unchanged.
7. Build results and warnings.
8. Any compatibility issue encountered.
9. Whether GNIP-003 Legendre bridge is now cleanly justified.

Outcome policy:

```text
A — COMPATIBILITY RECOVERY COMPLETE
    Neutral source is reused, old public API preserved, Collatz builds cleanly.

B — BRIDGE ADDED / FULL REFACTOR DEFERRED
    Exact neutral equality is proved but changing source ownership would cause
    nontrivial compatibility churn. Preserve behavior and document blocker.

C — NO SAFE REFACTOR
    A real dependency or semantic mismatch prevents neutral reuse. Do not force
    the refactor; record the exact mismatch.
```
