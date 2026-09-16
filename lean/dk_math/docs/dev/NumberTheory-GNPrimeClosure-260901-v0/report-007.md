# GNPC-007 report

## Outcome

Outcome A — the one-step simple-root lift from modulus `q` to modulus `q^2`
is implemented and kernel-checked for the primitive, non-ramified degree-three
GN shell.

The verified mechanism is:

```text
q | GN 3 u x
q ∤ (2*u + 3*x)
      ↓
GN 3 (u + q*t) x = GN 3 u x + q*t*(2*u + 3*x) + q^2*t^2
      ↓
one linear congruence modulo q
      ↓
one unique t : Fin q
      ↓
q^2 | GN 3 (u + q*t) x
```

This confirms that square lifting is the unique continuation of a simple
non-ramified root, not a universal obstruction.

## Reconnaissance and selected route

The repository contains larger FLT-local Hensel sketches, but they depend on
heavy application-specific material and include abstract/infinite lift
boundaries. No thin Mathlib theorem matching this natural-number quadratic
step was found. The new owner therefore uses the elementary exact shift
identity plus `ZMod q` linear algebra.

The exact Mathlib APIs used are:

```lean
Nat.mul_div_cancel'
Nat.dvd_of_mul_dvd_mul_left
Nat.dvd_add_iff_left
ZMod.natCast_eq_zero_iff
ZMod.natCast_zmod_val
ZMod.val_lt
mul_right_cancel₀
```

The modular digit is represented by the canonical `ZMod q` value's `.val`,
which is directly a `Fin q` representative. The inverse of the nonzero
derivative supplies the linear solution.

## Owner and imports

New thin owner:

```text
DkMath/NumberTheory/GNThreeHenselLift.lean
```

Imports:

```lean
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import DkMath.NumberTheory.GNThreePrimeArithmetic
```

The GNPC-006 theorem
`prime_not_dvd_cubic_boundary_derivative` is reused directly. No FLT,
Zsigmondy, completion, or p-adic module is imported.

## Final theorem surface

P0 and P1 are public exact shift identities:

```lean
GN_three_add_boundary_shift
GN_three_add_prime_mul_digit
```

P2 is intentionally private because the quotient criterion is only an
internal normalization device:

```lean
private sq_dvd_GN_three_add_prime_mul_digit_iff
    (hqpos : 0 < q)
    (hqGN : q ∣ GN 3 u x) :
    q ^ 2 ∣ GN 3 (u + q * t) x ↔
      q ∣ GN 3 u x / q + t * (2 * u + 3 * x)
```

P3 is the required unique digit theorem:

```lean
existsUnique_GN_three_sqLift_digit
    (hq : Nat.Prime q)
    (hcop : Nat.Coprime u x)
    (hqGN : q ∣ GN 3 u x)
    (hq3 : q ≠ 3) :
    ∃! t : Fin q,
      q ^ 2 ∣ GN 3 (u + q * (t : ℕ)) x
```

P4 was added as the explicit modular correction API and its correctness
theorem:

```lean
GNThreeNextLiftDigitZMod
GNThreeNextLiftDigitZMod_eq_cast_of_sqLift
```

The formula is

```text
- (GN 3 u x / q) * (2*u + 3*x)^(-1)  in ZMod q.
```

P5 is the derivative stability theorem:

```lean
prime_not_dvd_cubic_boundary_derivative_add_prime_mul
    (hqder : ¬ q ∣ 2 * u + 3 * x) :
    ¬ q ∣ 2 * (u + q * t) + 3 * x
```

## `q = 7`, `x = 1` regressions

The required base roots and lifts are verified:

```text
7 | GN 3 1 1
7^2 | GN 3 29 1       -- digit 4: 1 + 7*4 = 29
7 | GN 3 3 1
7^2 | GN 3 17 1       -- digit 2: 3 + 7*2 = 17
GN 3 17 1 = 7^3
```

Additional anonymous examples use the generic uniqueness theorem to prove
that every `Fin 7` digit producing the first lift is `4`, and every digit
producing the second lift is `2`.

The last equality is retained as the GNPC-006 interpretation: the second
branch's representative happens to have valuation at least three. No exact
valuation classification is inferred.

## Optional arbitrary-depth extension

The general `q^k → q^(k+1)` theorem was not added. The validated checkpoint
stops at the required `q → q^2` step; extending the same proof requires a
separate natural-number power-divisibility normalization layer. No infinite
`q`-adic sequence is constructed.

## Interpretation boundary

GNPC-006 established simple roots in the non-ramified primitive sector.
GNPC-007 establishes one unique next base-`q` digit. Thus `q^2` divisibility
is expected branch continuation, not a generic contradiction. This does not
remove `hS0_not_sq`, prove FLT3, or classify all prime-power valuations.

## Validation

Command:

```text
lake build DkMath.NumberTheory.GNThreeHenselLift
```

Result: success (`Build completed successfully (8678 jobs).`) with no Lean
warnings. The new owner contains no `sorry` or `axiom`; `git diff --check`
passes.

## Deferred scope

- arbitrary-depth prime-power lifts;
- p-adic completions and infinite Hensel sequences;
- full valuation classification;
- Eisenstein/UFD descent and cyclotomic refactors;
- FLT endpoint changes or replacement of `hS0_not_sq`;
- full repository build, commit, push, and CI.
