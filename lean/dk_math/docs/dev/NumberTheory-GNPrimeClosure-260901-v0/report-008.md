# GNPC-008 report

## Outcome

Outcome A — the finite arbitrary-depth simple-root lift is implemented and
kernel-checked.

For `k >= 1`, the verified result is:

```text
q^k | GN 3 u x
q ∤ (2*u + 3*x)
        ↓
∃! t : Fin q,
  q^(k+1) | GN 3 (u + q^k*t) x
```

The construction is finite and elementary. It does not construct an infinite
`q`-adic branch or a completion-valued root.

## Reconnaissance and route

No thin generic Mathlib Hensel theorem matching this natural-number quadratic
step was found. The implementation reuses GNPC-007's exact shift and `ZMod`
linear-congruence pattern, then factors and cancels the positive natural
factor `q^k`.

The exact Mathlib divisibility/power APIs reused are:

```lean
pow_succ
pow_mul
dvd_pow_self
Nat.pow_pos
Nat.mul_div_cancel'
Nat.dvd_of_mul_dvd_mul_left
Nat.mul_dvd_mul_left
Nat.dvd_add_iff_left
ZMod.natCast_eq_zero_iff
ZMod.natCast_zmod_val
ZMod.val_lt
mul_right_cancel₀
```

The GNPC-007 declarations reused are:

```lean
GN_three_add_boundary_shift
prime_not_dvd_cubic_boundary_derivative
prime_not_dvd_cubic_boundary_derivative_add_prime_mul
GN_three_dual_explicit
```

No FLT, Zsigmondy, Kummer, completion, or p-adic application module is
imported.

## Owner and imports

The thin owner is:

```text
DkMath/NumberTheory/GNThreeHenselDepth.lean
```

Imports:

```lean
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import DkMath.NumberTheory.GNThreeHenselLift
```

## Final theorem surface

P0 — power-sized exact shift:

```lean
GN_three_add_prime_pow_mul_digit
    (q k u x t : ℕ) :
    GN 3 (u + q ^ k * t) x =
      GN 3 u x + q ^ k * t * (2 * u + 3 * x) +
        q ^ (2 * k) * t ^ 2
```

P1 — arbitrary-depth linearized criterion:

```lean
pow_succ_dvd_GN_three_add_prime_pow_mul_digit_iff
    (hqpos : 0 < q)
    (hk : 1 ≤ k)
    (hqkGN : q ^ k ∣ GN 3 u x) :
    q ^ (k + 1) ∣ GN 3 (u + q ^ k * t) x ↔
      q ∣ GN 3 u x / q ^ k + t * (2 * u + 3 * x)
```

P1 is public. It is the useful finite-depth reduction, so keeping it private
would unnecessarily hide the exact quotient criterion.

P2 — generic unique next digit:

```lean
existsUnique_GN_three_powLift_digit
    (hq : Nat.Prime q)
    (hk : 1 ≤ k)
    (hqkGN : q ^ k ∣ GN 3 u x)
    (hqder : ¬ q ∣ 2 * u + 3 * x) :
    ∃! t : Fin q,
      q ^ (k + 1) ∣ GN 3 (u + q ^ k * (t : ℕ)) x
```

P3 — primitive non-ramified wrapper:

```lean
existsUnique_GN_three_powLift_digit_of_primitive_nonramified
    (hq : Nat.Prime q)
    (hk : 1 ≤ k)
    (hcop : Nat.Coprime u x)
    (hq3 : q ≠ 3)
    (hqkGN : q ^ k ∣ GN 3 u x) :
    ∃! t : Fin q,
      q ^ (k + 1) ∣ GN 3 (u + q ^ k * (t : ℕ)) x
```

The wrapper derives `q | GN 3 u x` from `dvd_pow_self`, then reuses the
GNPC-006 derivative exclusion before invoking P2.

P4 — arbitrary-depth derivative stability:

```lean
prime_not_dvd_cubic_boundary_derivative_add_prime_pow_mul
    (hk : 1 ≤ k)
    (hqder : ¬ q ∣ 2 * u + 3 * x) :
    ¬ q ∣ 2 * (u + q ^ k * t) + 3 * x
```

P5 — explicit correction digit and correctness theorem:

```lean
GNThreeNextPowLiftDigitZMod
GNThreeNextPowLiftDigitZMod_eq_cast_of_powLift
```

The definition is the finite-depth formula

```text
-(GN 3 u x / q^k) * (2*u + 3*x)^(-1)  in ZMod q.
```

The correctness theorem shows that every `Fin q` digit satisfying the
`q^(k+1)` lift is equal to this formula after casting to `ZMod q`.

P6 is a concrete `k = 1` specialization example, proved through the generic
arbitrary-depth theorem rather than by copying GNPC-007's proof.

## Depth-3 regressions for `q = 7`, `x = 1`

The required depth-3 lifts are verified:

```text
7^3 | GN 3 323 1       -- 29 + 49*6 = 323
7^3 | GN 3 17 1        -- 17 + 49*0 = 17
```

The uniqueness examples additionally prove:

```text
from u = 29 at k = 2: only t = 6 works;
from u = 17 at k = 2: only t = 0 works.
```

The second branch is consistent with the retained GNPC-006 fact
`GN 3 17 1 = 7^3`; it does not imply that later digits remain zero.

## Optional finite-branch layer

The bounded recursive finite-branch constructor was not added. P0–P6 already
provide the one-step engine needed to build such a layer later. No uniqueness
modulo `q^n` beyond the proved one-step statement is claimed here.

## Interpretation boundary

GNPC-006 proves that primitive non-ramified cubic roots are simple.
GNPC-007 proves the unique `q → q^2` digit.
GNPC-008 proves the same mechanism at every finite positive depth. Prime-power
divisibility therefore corresponds to following a finite base-`q` branch; it
does not by itself classify the valuation of an arbitrary fixed coordinate.

This checkpoint does not prove FLT3, remove or replace `hS0_not_sq`, classify
all valuations, or construct an infinite p-adic completion.

## Validation

Command:

```text
lake build DkMath.NumberTheory.GNThreeHenselDepth
```

Result: success (`Build completed successfully (8679 jobs).`) with no Lean
warnings. The new owner contains no `sorry` or `axiom`; `git diff --check`
passes.

## Deferred scope

- infinite Hensel sequences and p-adic completions;
- full valuation equalities for arbitrary coordinates;
- recursive finite-branch packaging;
- Eisenstein/UFD descent and FLT endpoint changes;
- replacement of `hS0_not_sq`;
- generic-degree Hensel theory;
- full repository build, commit, push, and CI.
