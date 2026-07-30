# FLT7-008 — Discriminant -7 Euclidean foundation and coprime seventh-power extraction

Work on branch:

```text
feature/FLT7-magic-core-260722-v0
```

Use the current branch HEAD after completed FLT7-007.

## Objective

Equip `TraceOneInt (-2)` with the algebraic infrastructure required for
factorization:

1. prove it is an integral domain directly from the positive norm;
2. construct explicit norm-Euclidean division using skew nearest-lattice
   rounding;
3. classify all units as `±1`;
4. prove that coprime factors of a seventh power are themselves seventh powers,
   not merely seventh powers up to a unit.

This checkpoint is independent ring infrastructure. Do not yet apply the
factor theorem to `SevenQuadraticResidualPacket`; conjugate coprimality belongs
to FLT7-009.

## Mathematical heart

For rational error coordinates `(u,v)`, the discriminant `-7` norm is

```text
u^2 + u*v + 2*v^2
  = (u + v/2)^2 + (7/4)*v^2.
```

Do not round the two original coordinates independently.

Given rational quotient coordinates `(A,B)`:

1. choose `n = round B`;
2. put `v = B-n`;
3. choose `m = round (A + v/2)`;
4. put `u = A-m`.

Then

```text
|v| ≤ 1/2,
|u+v/2| ≤ 1/2,
```

and therefore

```text
0 ≤ u^2+u*v+2*v^2 ≤ 11/16 < 1.
```

This strict contraction avoids all corner/tie exceptions and is the required
Euclidean division algorithm.

## New modules

Create:

```text
DkMath/FLT/Seven/QuadraticEuclidean.lean
DkMath/FLT/Seven/QuadraticUnits.lean
DkMath/FLT/Seven/QuadraticCoprimeFactor.lean
```

Suggested imports:

```lean
-- QuadraticEuclidean.lean
import DkMath.FLT.Seven.QuadraticResidualPacket
import Mathlib.Algebra.Order.Round
import Mathlib.RingTheory.EuclideanDomain

-- QuadraticUnits.lean
import DkMath.FLT.Seven.QuadraticEuclidean

-- QuadraticCoprimeFactor.lean
import DkMath.FLT.Seven.QuadraticUnits
```

Update:

```text
DkMath/FLT/Seven.lean
```

Add focused tests:

```text
DkMathTest/FLT/SevenQuadraticEuclidean.lean
DkMathTest/FLT/SevenQuadraticCoprimeFactor.lean
```

Create:

```text
docs/feature/FLT7-magic-core-260722/report-flt7-008.md
```

Use the existing namespace:

```lean
namespace DkMath.FLT.Seven
```

Open or abbreviate `DkMath.NumberTheory.TraceOneQuadratic` locally as needed.
Do not duplicate the underlying `TraceOneInt` definition.

# Part A — Integral-domain foundation

The generic `TraceOneInt s` is currently only a commutative ring. Prove the
`-2` specialization has no zero divisors using norm multiplicativity and the
existing zero fiber.

Required theorem:

```lean
theorem traceOneNegTwo_eq_zero_or_eq_zero_of_mul_eq_zero
    {x y : TraceOneInt (-2)}
    (h : x * y = 0) :
    x = 0 ∨ y = 0
```

Suggested proof:

```text
norm(x*y)=norm x * norm y,
norm 0=0,
integer product zero,
norm x=0 or norm y=0,
norm_eq_zero_iff_of_negTwo.
```

Install instances with narrow scope and clear names:

```lean
instance traceOneNegTwoNoZeroDivisors :
    NoZeroDivisors (TraceOneInt (-2))

instance traceOneNegTwoNontrivial :
    Nontrivial (TraceOneInt (-2))

instance traceOneNegTwoIsDomain :
    IsDomain (TraceOneInt (-2))
```

Do not attempt a generic `IsDomain (TraceOneInt s)` instance.

# Part B — Rational quotient coordinates

Define:

```lean
abbrev SevenRat := ℚ × ℚ
```

```lean
def sevenRatNorm (x : SevenRat) : ℚ :=
  x.1 ^ 2 + x.1 * x.2 + 2 * x.2 ^ 2
```

Prove the completed-square identity:

```lean
theorem sevenRatNorm_completed_square (u v : ℚ) :
    sevenRatNorm (u,v) =
      (u + v / 2) ^ 2 + (7 / 4 : ℚ) * v ^ 2
```

Prove the skew-cell bound:

```lean
theorem sevenRatNorm_le_eleven_sixteen
    {u v : ℚ}
    (hv : |v| ≤ (1 : ℚ) / 2)
    (hu : |u + v / 2| ≤ (1 : ℚ) / 2) :
    sevenRatNorm (u,v) ≤ (11 : ℚ) / 16
```

and strict contraction:

```lean
theorem sevenRatNorm_lt_one
    {u v : ℚ}
    (hv : |v| ≤ (1 : ℚ) / 2)
    (hu : |u + v / 2| ≤ (1 : ℚ) / 2) :
    sevenRatNorm (u,v) < 1
```

Also retain nonnegativity:

```lean
theorem sevenRatNorm_nonneg (u v : ℚ) :
    0 ≤ sevenRatNorm (u,v)
```

# Part C — Quotient and remainder

Define the numerator:

```lean
def sevenQuotientNumerator
    (x y : TraceOneInt (-2)) : TraceOneInt (-2) :=
  x * conj y
```

Define rational quotient coordinates:

```lean
def sevenQuotientCoords
    (x y : TraceOneInt (-2)) : SevenRat :=
  (((sevenQuotientNumerator x y).fst : ℚ) / norm y,
   ((sevenQuotientNumerator x y).snd : ℚ) / norm y)
```

Define skew rounding. An acceptable transparent design is:

```lean
def sevenRoundedSnd (x y : TraceOneInt (-2)) : ℤ :=
  round (sevenQuotientCoords x y).2


def sevenRoundedFst (x y : TraceOneInt (-2)) : ℤ :=
  let B := (sevenQuotientCoords x y).2
  let n := sevenRoundedSnd x y
  round ((sevenQuotientCoords x y).1 + (B - n) / 2)
```

Then:

```lean
def sevenQuotient (x y : TraceOneInt (-2)) : TraceOneInt (-2) :=
  ⟨sevenRoundedFst x y, sevenRoundedSnd x y⟩
```

```lean
def sevenRemainder (x y : TraceOneInt (-2)) : TraceOneInt (-2) :=
  x - sevenQuotient x y * y
```

Prove:

```lean
theorem sevenQuotient_zero (x : TraceOneInt (-2)) :
    sevenQuotient x 0 = 0
```

```lean
theorem seven_quotient_mul_add_remainder
    (x y : TraceOneInt (-2)) :
    y * sevenQuotient x y + sevenRemainder x y = x
```

A quotient orientation with `q*y+r=x` is equally acceptable; align the
EuclideanDomain fields consistently.

# Part D — Euclidean size and strict remainder decrease

Define:

```lean
def sevenEuclideanSize (x : TraceOneInt (-2)) : ℕ :=
  Int.natAbs (norm x)
```

Prove:

```lean
theorem sevenEuclideanSize_pos_of_ne_zero
    {x : TraceOneInt (-2)} (hx : x ≠ 0) :
    0 < sevenEuclideanSize x
```

```lean
theorem sevenEuclideanSize_mul
    (x y : TraceOneInt (-2)) :
    sevenEuclideanSize (x*y) =
      sevenEuclideanSize x * sevenEuclideanSize y
```

Establish the rational remainder identity analogous to the existing golden
implementation:

```lean
private theorem sevenRemainder_norm_rat_identity
    (x y : TraceOneInt (-2)) (hy : y ≠ 0) :
    (norm (sevenRemainder x y) : ℚ) =
      (norm y : ℚ) * sevenRatNorm (u,v)
```

where `u,v` are the quotient-coordinate errors induced by
`sevenRoundedFst/sevenRoundedSnd`. State them explicitly or use local lets.

Prove the two rounding bounds:

```text
|v| ≤ 1/2,
|u+v/2| ≤ 1/2.
```

Then prove:

```lean
theorem seven_remainder_size_lt
    (x : TraceOneInt (-2))
    {y : TraceOneInt (-2)} (hy : y ≠ 0) :
    sevenEuclideanSize (sevenRemainder x y) <
      sevenEuclideanSize y
```

Since the norm is nonnegative, the proof may avoid some absolute-value work,
but preserve a reliable integer-to-rational comparison. Do not use floating
point approximations.

Install:

```lean
noncomputable instance traceOneNegTwoEuclideanDomain :
    EuclideanDomain (TraceOneInt (-2))
```

Use `sevenEuclideanSize` as the well-founded measure and follow the established
`GoldenEuclidean.lean` instance pattern where appropriate.

# Part E — Unit classification

The existing norm-one theorem says the norm-one shell is exactly `±1`. Connect
this to the standard `IsUnit` predicate.

Prove:

```lean
theorem isUnit_iff_norm_eq_one
    {x : TraceOneInt (-2)} :
    IsUnit x ↔ norm x = 1
```

Forward direction:

- extract an inverse `y`;
- apply norm multiplicativity to `x*y=1`;
- use positivity of nonzero norms to force `norm x=1`.

Reverse direction:

- use `norm_eq_one_iff_of_negTwo`;
- rewrite `x=1` or `x=-1`;
- conclude `IsUnit` by simp.

Then prove the explicit classification:

```lean
theorem isUnit_iff_eq_one_or_neg_one
    {x : TraceOneInt (-2)} :
    IsUnit x ↔ x = 1 ∨ x = -1
```

The crucial odd-exponent absorption theorem is:

```lean
theorem exists_seventh_power_eq_of_isUnit
    {u : TraceOneInt (-2)} (hu : IsUnit u) :
    ∃ e : TraceOneInt (-2), u = e ^ 7
```

Use only the classification `u=±1` and the odd exponent `7`.

# Part F — Coprime seventh-power factor extraction

With the Euclidean domain installed, obtain its gcd monoid locally:

```lean
letI : GCDMonoid (TraceOneInt (-2)) :=
  EuclideanDomain.gcdMonoid (TraceOneInt (-2))
```

Prove the up-to-unit form:

```lean
theorem associated_seventh_power_of_coprime_mul_eq_pow
    {x y z : TraceOneInt (-2)}
    (hcop : IsUnit (gcd x y))
    (hpow : x * y = z ^ 7) :
    ∃ gamma : TraceOneInt (-2),
      Associated x (gamma ^ 7)
```

Use `exists_associated_pow_of_mul_eq_pow` or the closest current Mathlib API.

Then absorb the unit, exploiting that every unit is a seventh power:

```lean
theorem exists_eq_seventh_power_of_coprime_mul_eq_pow
    {x y z : TraceOneInt (-2)}
    (hcop : IsUnit (gcd x y))
    (hpow : x * y = z ^ 7) :
    ∃ gamma : TraceOneInt (-2),
      x = gamma ^ 7
```

Also provide the symmetric pair form:

```lean
theorem seventh_power_factor_split_traceOneNegTwo
    {x y z : TraceOneInt (-2)}
    (hcop : IsUnit (gcd x y))
    (hpow : x * y = z ^ 7) :
    (∃ a, x = a ^ 7) ∧
    (∃ b, y = b ^ 7)
```

If the Mathlib theorem naturally returns a unit and power rather than
`Associated`, retain a small auxiliary theorem matching that API and prove the
public exact form afterward.

# Tests

Focused tests must cover:

- norm zero implies element zero and domain cancellation;
- skew rounding bounds on symbolic quotient errors;
- quotient/remainder reconstruction;
- strict remainder size on several explicit nonzero divisors;
- gcd computation is available through the Euclidean instance;
- units `1,-1` and exclusion of a simple nonunit such as `sevenAxis`;
- both units are seventh powers;
- abstract coprime factor split wiring.

Do not use `native_decide`.

# Required report

Record:

- exact definition/theorem/instance surface;
- direct no-zero-divisor proof;
- why independent coordinate rounding is insufficient at discriminant `-7`;
- the skew rounding rule;
- the completed-square `11/16` contraction;
- quotient/remainder and strict norm decrease;
- EuclideanDomain construction;
- exact unit classification;
- why odd exponent seven absorbs every unit;
- coprime seventh-power factor extraction;
- recommended FLT7-009 boundary.

The recommended FLT7-009 boundary should prove coprimality of the terminal
quadratic residual and its conjugate, or isolate the exact exceptional divisor
support. Only after that bridge is complete may the residual packet be promoted
to an element-level seventh power.

# Non-goals

Do not add:

- application to `SevenQuadraticResidualPacket`;
- a claim that its residual core is already a seventh power;
- conjugate coprimality;
- finite unit sectors beyond the explicit `±1` classification;
- FLT7 descent or no-solution theorem;
- ideal or class-number theory;
- a generic Euclidean instance for `TraceOneInt s`;
- changes to FLT3 or FLT5.

# Outcome classification

- Outcome A: domain, Euclidean division, unit classification, and exact
  coprime seventh-power extraction are complete.
- Outcome B: domain and Euclidean division are complete, but unit absorption or
  the exact factor theorem requires a clearly identified Mathlib API follow-up.
- Outcome C: the skew rounding contraction or Euclidean instance fails; report
  the exact rational cell obstruction and preserve FLT7-007.

Commit with a focused message and push to the current feature branch.
