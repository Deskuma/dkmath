# S0: the cubic Petal kernel

短く言えば、`S0` は `c^3 - b^3` から境界因子 `c - b` を剥がした後に残る
degree-three `GN` / Petal observation kernel です。

```text
S0(c, b) = c^2 + c*b + b^2

c^3 - b^3 = (c - b) * S0(c, b)

S0(c, b) = GN 3 (c - b) b
```

The name `S0` is historical.  It appears in many FLT, Petal, and descent files,
so the implementation keeps the name stable.  This document gives the intended
meaning behind the name.

## Lean definitions

The original definitions live in:

```text
lean/dk_math/DkMath/FLT/PetalDetect.lean
```

Important names:

```lean
def S0 (α : Type*) [Ring α] (a b : α) : α := a^2 + a*b + b^2
def S0_nat (a b : ℕ) : ℕ := a^2 + a*b + b^2
```

The Petal package keeps a stable Petal-facing import path:

```text
lean/dk_math/DkMath/Petal/Basic.lean
```

Important alias:

```lean
abbrev S0Nat (a b : ℕ) : ℕ := S0_nat a b
```

## Mathematical meaning

The basic cubic factorization is:

```text
c^3 - b^3 = (c - b) * (c^2 + c*b + b^2)
```

Therefore:

```text
S0(c, b) = (c^3 - b^3) / (c - b)
```

whenever one reads the expression as the quotient after removing the boundary
factor `c - b`.

In DkMath terms, this is exactly the degree-three `GN` kernel after the
substitution:

```text
x = c - b
u = b
```

For degree `3`, the GN kernel is:

```text
GN 3 x u = x^2 + 3*x*u + 3*u^2
```

Substituting `x = c - b`, `u = b` gives:

```text
GN 3 (c - b) b
  = (c - b)^2 + 3*(c - b)*b + 3*b^2
  = c^2 + c*b + b^2
  = S0(c, b)
```

This is implemented as:

```lean
DkMath.FLT.GN_three_sub_eq_S0_nat
DkMath.Petal.S0_nat_eq_GN_three_sub
```

## Why it matters

`S0` is not just an arbitrary quadratic form.  It is the cubic difference
quotient kernel.

For Zsigmondy-style and primitive-prime arguments, the boundary factor
`c - b` is old information.  Primitive prime candidates are expected to live
after the boundary has been removed.  In the cubic Petal layer, that remaining
kernel is `S0_nat c b`.

The central reading is:

```text
c^3 - b^3
  = boundary * kernel
  = (c - b) * S0(c, b)

S0(c, b)
  = cubic GN face
  = degree-three Petal kernel
  = boundary-removed quotient of the cubic difference
```

## Common implementation surfaces

`S0_nat` is used in several layers:

```text
DkMath.FLT.PetalDetect
DkMath.FLT.CounterexamplePattern
DkMath.FLT.GEisensteinBridge
DkMath.Petal.GNBridge
DkMath.Petal.GcdBridge
DkMath.Petal.PadicBridge
DkMath.Petal.PrimitiveBridge
```

Important bridge names:

```lean
S0_nat_eq_GN_three_sub
gcd_sub_S0_nat_eq_gcd_sub_three
padicValNat_cube_sub_eq_padicValNat_S0_nat_of_not_dvd_sub
primitive_prime_dvd_S0_nat
primitive_prime_padicValNat_cube_sub_eq_S0_nat
primitiveOnS0_of_prime_dvd_cube_sub_not_dvd_sub
```

These names should be read as a chain:

```text
cubic difference
  -> remove boundary c - b
  -> S0 / GN3 Petal face
  -> gcd, p-adic, primitive-prime observations
```

## Suggested descriptive aliases

The core name `S0_nat` should remain stable because it is already widely used.
When explanatory names are useful in future APIs or docs, these phrases are
recommended:

```text
cubic Petal kernel
degree-three GN face
cubic difference quotient kernel
boundary-removed cubic kernel
```

Possible Lean alias names, if needed later:

```lean
cubicPetalKernelNat
GN3PetalFaceNat
cubicDifferenceQuotientKernelNat
```

For now, the recommended practice is to keep theorem statements in terms of
`S0_nat`, and use docstrings to mention:

```text
S0_nat c b = GN 3 (c - b) b
```
