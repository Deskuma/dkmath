# GNIP-000 report — neutral gnomon algebra recovery

## 1. Outcome

**A — RECOVERY + GENERALIZATION COMPLETE.**

The neutral natural-number gnomon layer, arbitrary-thickness square growth,
composition, shifted unit decomposition, and square reconstruction are all
implemented and kernel-checked.

## 2. Files added

```text
DkMath/Gnomon/Algebra.lean
DkMath/Gnomon.lean
docs/dev/NumberTheory-Gnomon-Inversion-Projection-260914-v0/report-000.md
```

No existing Collatz, Cosmic, Legendre, or other application file was changed.

## 3. Final exported theorem names

Definitions:

```text
DkMath.Gnomon.oddGnomon
DkMath.Gnomon.squareGnomonBand
DkMath.Gnomon.petalMul
```

Odd-gnomon API:

```text
oddGnomon_zero
oddGnomon_succ
oddGnomon_pos
oddGnomon_odd
oddGnomon_injective
oddGnomon_eq_one_iff
```

Petal multiplication API:

```text
petalMul_zero_left
petalMul_zero_right
petalMul_comm
petalMul_assoc
oddGnomon_petalMul
```

Square-growth and reconstruction API:

```text
square_add_oddGnomon
square_add_squareGnomonBand
squareGnomonBand_zero
squareGnomonBand_unit
squareGnomonBand_zero_anchor
squareGnomonBand_add
squareGnomonBand_eq_sum_shifted_oddGnomon
sum_oddGnomon_eq_square
sum_odd_eq_square
```

## 4. Checkpoint A recovery

The pure algebra requested by the old Checkpoint A is recovered in the
neutral `DkMath.Gnomon` namespace: zero laws, commutativity, associativity,
and multiplicative transport through odd-gnomon addresses are proved.

## 5. Arbitrary-thickness growth and composition

For side-thickness `u`, the implementation proves

```text
x^2 + squareGnomonBand x u = (x+u)^2
```

and the exact path-composition law

```text
squareGnomonBand x (u+v)
  = squareGnomonBand x u + squareGnomonBand (x+u) v.
```

The unit specialization is proved as
`squareGnomonBand x 1 = oddGnomon x`, and the zero-anchor specialization as
`squareGnomonBand 0 u = u^2`.

## 6. Shifted decomposition and reconstruction

The shifted unit decomposition is proved:

```text
squareGnomonBand x u
  = (Finset.range u).sum (fun i => oddGnomon (x+i)).
```

The classical reconstruction is also proved:

```text
(Finset.range n).sum oddGnomon = n^2.
```

The requested concrete regressions, including
`oddGnomon 30 = 61`, `oddGnomon 31 = 63`, and
`squareGnomonBand 30 2 = 124 = 61 + 63`, are kernel-checked examples.

## 7. Dependency imports

`DkMath.Gnomon.Algebra` imports exactly:

```text
Mathlib.Algebra.Ring.Parity
Mathlib.Data.Finset.Interval
Mathlib.Tactic
```

`DkMath.Gnomon` imports only `DkMath.Gnomon.Algebra`.

No forbidden application import is present: no Collatz, Legendre, MultiGauge,
GTail/Cosmic Formula, Polyomino, FLT, ABC, or duplicate `GTail`/`GN`
definition was introduced.

## 8. Validation

Run from `lean/dk_math`:

```text
lake build DkMath.Gnomon.Algebra
Build completed successfully (3000 jobs).

lake build DkMath.Gnomon
Build completed successfully (3001 jobs).

git diff --check
passed with no diagnostics.

The three untracked files were also checked with `git diff --no-index --check`
against `/dev/null`; all produced no whitespace diagnostics (exit status 1 is
the expected untracked-file diff result).
```

The changed Lean files were scanned for `sorry`, `admit`, and `axiom`; no
matches were found.

## 9. Scope deviations

None within GNIP-000.  The root `DkMath.lean` aggregate was not modified;
the requested public facade is available as `DkMath.Gnomon` and was built
directly.  Existing Collatz names remain untouched, as required for the
deferred GNIP-002 compatibility refactor.

GNIP-001, GNIP-002, GNIP-003, and GNIP-004 were not implemented in this
checkpoint.  In particular, this report makes no Legendre, prime-existence,
Cosmic/GTail bridge, inversion, or projection claim.

## 10. GNIP-001 status

No production Cosmic/GTail bridge is justified or added by GNIP-000 itself.
The neutral layer is intentionally dependency-clean, so any degree-two
`GTail` identities belong to the separately planned GNIP-001 bridge after
this API has been reviewed.
