# FLT7 magic-core foundation

Status: implementation checkpoint FLT7-001 (Outcome A).

This feature realizes the first finite algebraic layer behind the seventh-power
kernel.  It does **not** prove FLT7.  The implemented path is

```text
seventh cyclotomic growth
  -> two integral cubic coordinates
  -> TraceOneInt (-2)
  -> positive-definite quadratic norm
```

## Central scale axis

In `TraceOneInt (-2)` the element

```lean
sevenAxis = 2 * tau (-2) - 1 = (-1, 2)
```

is the central quadratic scale axis (also denoted kappa in the design
interpretation).  The proved identities are

```text
sevenAxis ^ 2 = -7
conj sevenAxis = -sevenAxis
norm sevenAxis = 7
```

It is not a ring unit: its norm is `7`, not `±1`.

## Integral norm shells

For coordinates `(a,b)` the norm is

```text
a^2 + a*b + 2*b^2
```

and its completed-square identity is

```text
4 * norm(a,b) = (2*a+b)^2 + 7*b^2.
```

Consequently zero occurs only for the zero element.  Zero is absence of the
core, not an inner norm shell.  Every nonzero integral core has norm at least
one, and the norm-one shell is exactly `1` and `-1`.

## Seventh cyclotomic coordinates

The homogeneous kernel

```text
Phi7(z,y) = z^6 + z^5*y + ... + z*y^5 + y^6
```

is represented by cubic coordinates

```text
A = z^3 + z^2*y - y^3
B = -z^2*y - z*y^2
```

with the exact identity

```text
Phi7(z,y) = norm (A,B)  in TraceOneInt (-2).
```

Both coordinates, and hence the kernel, vanish exactly at `(z,y)=(0,0)`.
In the positive natural chamber the seven positive monomials also give the
sharper elementary floor `7`.

The generic GN convention is `GN 7 g y` with endpoint `z=g+y`.  Therefore the
implemented subtraction bridge assumes `b ≤ a`, substitutes

```text
g = a-b,  y = b,  z = (a-b)+b = a,
```

and evaluates the trace-one package at the endpoint pair `(a,b)`.

## Public theorem surface

Neutral core:

- `sevenAxis`, `sevenAxis_eq`, `sevenAxis_sq`, `conj_sevenAxis`, `sevenAxis_norm`
- `traceOneNorm_neg_two`, `four_mul_traceOneNorm_negTwo_eq_sum_sq`
- `traceOneNorm_negTwo_eq_zero_iff`, `norm_eq_zero_iff_of_negTwo`
- `one_le_traceOneNorm_negTwo_of_ne_zero`
- `traceOneNorm_negTwo_eq_one_iff`, `norm_eq_one_iff_of_negTwo`

FLT7 bridge:

- `cyclotomicSeven`, `cyclotomicSevenFst`, `cyclotomicSevenSnd`
- `cyclotomicSevenToTraceOne`
- `cyclotomicSeven_eq_traceOneNorm_negTwo`
- `seventh_pow_sub_pow_eq_sub_mul_cyclotomicSeven`
- `GN_seven_sub_eq_traceOneNorm_negTwo`
- `cyclotomicSeven_coordinates_eq_zero_iff`, `cyclotomicSeven_eq_zero_iff`
- `seven_le_cyclotomicSeven_nat`

## Explicit non-goals

This checkpoint adds no FLT7 proof, counterexample packet, descent, unit-sector
analysis, Euclidean/PID/UFD/class-number-one instance, irreducible or prime
classification, general odd-prime theorem, or standalone FLT7 artifact.  It
does not modify the completed FLT3 or FLT5 theorem stacks.
