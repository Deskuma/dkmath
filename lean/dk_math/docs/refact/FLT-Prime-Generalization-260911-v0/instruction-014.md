# FLT prime-generalization Phase 14 — arithmetic frontier audit after the TraceOne prime bridge

## Goal

Phase 13 closed the quadratic-cyclotomic front-end for every odd prime `p`:

```text
GTail / prime cyclotomic shell
  -> QR/QNR factorization
  -> full Galois action
  -> Q/Z coefficient descent
  -> discriminant-square normalization
  -> integral TraceOne coordinates
```

The next task is **not** to force another arbitrary-prime theorem immediately.  Instead, audit the existing FLT7 arithmetic layer and identify the exact point where the arbitrary-prime `TraceOneInt (signedPrimeParameter p)` bridge ceases to specialize cleanly.

The expected boundary is the arithmetic of the quadratic order itself:

```text
TraceOne quadratic front-end      [generic odd-prime: GREEN]
---------------------------------------------------------------
Euclidean/PID/UFD/GCD arithmetic  [audit]
unit p-th-power absorption        [audit]
conjugate coprimality             [audit]
principalization / class group    [audit]
FLT descent / contradiction       [out of scope]
```

Do not claim a general FLT theorem.

## A. Audit the FLT7 modules in dependency order

Inspect at least:

```text
DkMath/FLT/Seven/QuadraticResidualPacket.lean
DkMath/FLT/Seven/QuadraticEuclidean.lean
DkMath/FLT/Seven/QuadraticUnits.lean
DkMath/FLT/Seven/QuadraticCoprimeFactor.lean
DkMath/FLT/Seven/QuadraticConjugateCoprime.lean
DkMath/FLT/Seven/QuadraticSeventhPowerNormalForm.lean
```

For every public declaration that is used downstream, classify it as one of:

```text
PGEN-TRACEONE-SPECIALIZATION
  already follows from / can be rebuilt from the Phase-13 generic endpoint

PGEN-ABSTRACT-RING
  exponent-independent after replacing `TraceOneInt (-2)` by an abstract ring
  with explicit typeclass hypotheses

PGEN-UNIT-SECTOR
  generic only up to an associated p-th power; equality requires unit classes
  modulo p-th powers

PGEN-GCD-UFD
  relies on GCDMonoid / UFD / Euclidean/PID structure

PGEN-CLASSGROUP
  the natural generic replacement is ideal factorization / class-group control

P7-ARITHMETIC
  genuinely uses special arithmetic of discriminant `-7`
```

Record the classification in `report-014.md`.

## B. Probe the generic coprime-power extraction theorem

The existing Seven theorem

```lean
exists_eq_seventh_power_of_coprime_mul_eq_pow
```

bundles two logically distinct steps:

1. coprime factor extraction gives `Associated x (gamma ^ p)`;
2. the unit is absorbed because every unit of `TraceOneInt (-2)` is a seventh power.

Create a test-first probe under the weakest practical abstract hypotheses.

Target shape:

```lean
theorem associated_prime_power_of_coprime_mul_eq_pow
    {R : Type*} [CommCancelMonoidWithZero R] [GCDMonoid R]
    {p : ℕ} {x y z : R}
    (hcop : IsUnit (gcd x y))
    (hpow : x * y = z ^ p) :
    ∃ gamma : R, Associated x (gamma ^ p)
```

Do not insist on this exact typeclass list if Mathlib's existing theorem has a cleaner or stronger contract. Prefer a thin wrapper over the pinned theorem already used by FLT7.

Classify the result `PGEN-ABSTRACT-RING` if it is exponent-independent.

Then isolate the exact extra hypothesis needed to strengthen `Associated` to equality:

```lean
(∀ u : R, IsUnit u -> ∃ e : R, u = e ^ p)
```

or an equivalent unit-class statement.

Do **not** assume this hypothesis for arbitrary `TraceOneInt (signedPrimeParameter p)`.

## C. Separate unit absorption from factor extraction

Audit `QuadraticUnits.lean`.

For `TraceOneInt (-2)` the current proof uses:

```text
units = {+1,-1}
every unit is a seventh power
```

This is special to the `-7` quadratic order and the odd exponent.

Create a neutral helper, test-side first, of the form:

```lean
theorem eq_pow_of_associated_pow_of_unit_pow_surjective ...
```

or the shortest equivalent statement:

```text
Associated x (gamma ^ p)
+ unit p-th-power surjectivity
=> ∃ delta, x = delta ^ p
```

The purpose is to make the **unit-sector boundary explicit**.

Do not attempt to prove unit p-th-power surjectivity for all prime discriminants.
For real quadratic specializations (`D_p > 0`) the unit group is not expected to collapse to `{±1}`.

## D. Audit the Euclidean/GCD dependency

`QuadraticEuclidean.lean` constructs a norm-Euclidean algorithm specifically for `TraceOneInt (-2)`.

Determine exactly which later FLT7 declarations need:

```text
EuclideanDomain
GCDMonoid
UniqueFactorizationMonoid
PrincipalIdealDomain
```

and which only need a much weaker statement.

In particular audit:

```text
irreducible_sevenAxis
prime_sevenAxis
isUnit_of_dvd_sevenAxis_of_dvd_terminal
gcd_residual_conj_isUnit
associated_seventh_power_of_coprime_mul_eq_pow
exists_eq_seventh_power_of_coprime_mul_eq_pow
```

Do not attempt to prove `EuclideanDomain (TraceOneInt (signedPrimeParameter p))` for arbitrary odd prime `p`.

The expected generic replacement should be recorded even if not implemented:

```text
GCD/UFD route when available
or
ideal-theoretic coprime factorization + class-group control
```

## E. Generalize the discriminant-axis part only where justified

Phase 4 already provides generic discriminant-axis arithmetic:

```text
discrAxis s
discrAxis_sq
norm_discrAxis
PrimeDiscriminantPacket
discrAxis_pow_dvd_iff_pow_prime_dvd_natAbs_norm
exists_terminal_discrAxis_core
```

Compare this with the Seven-specific use of `sevenAxis` in:

```text
QuadraticResidualPacket
QuadraticConjugateCoprime
```

Identify statements that are now merely `p=7` specializations of the generic discriminant-axis API.

Do not rewrite a theorem unless the replacement is low-risk and preserves the existing Seven public API.

## F. Identify the class-group frontier

Write a short mathematical/Lean design note in the report explaining the natural arbitrary-prime replacement for the Seven Euclidean argument:

If `alpha` and `conj alpha` generate coprime ideals and

```text
(alpha) * (conj alpha) = (beta)^p,
```

then coprime ideal factorization suggests

```text
(alpha) = A^p
```

for an ideal `A`.

To conclude `alpha = unit * gamma^p`, one must principalize `A`; the obstruction is a p-torsion class in the relevant class group.  Unit classes modulo p-th powers then remain as a separate obstruction.

This section is an **audit/design result**, not a new theorem unless the pinned Mathlib API makes a tiny neutral lemma cheap to prove.

Audit relevant pinned APIs for:

```text
FractionalIdeal / Ideal factorization
class group / ClassGroup
IsPrincipal
UniqueFactorizationMonoid of ideals
associated powers / ideal powers
```

Use the actual pinned declaration names in `report-014.md`.

## G. Finite specialization audit

Use `p = 3,5,7,11,13` only as probes.

For each of

```text
s_3  = -1
s_5  =  1
s_7  = -2
s_11 = -3
s_13 =  3
```

record, based on existing DkMath instances/theorems and the pinned Mathlib API, whether the following are currently available, missing, or intentionally not attempted:

```text
IsDomain
EuclideanDomain
GCDMonoid / UFD
unit classification modulo p-th powers
discrAxis irreducible / prime
conjugate-coprime extraction
```

Do not infer GREEN from mathematical folklore alone.  If Lean/DkMath does not contain the instance/theorem, mark it `NOT FORMALIZED`.

## H. Required report conclusion

`report-014.md` must give one of these main outcomes:

```text
Outcome A — ABSTRACT-ARITHMETIC-FRONTIER
  Coprime-power extraction is generalized abstractly, and the first genuine
  prime-dependent obstruction is isolated as unit/class-group arithmetic.

Outcome B — GCD-FRONTIER
  The first missing reusable layer is GCD/UFD structure for the prime-
  discriminant TraceOne order.

Outcome C — EARLIER-SPECIALIZATION
  A theorem thought generic still contains an essential p=7 assumption;
  identify the exact theorem and assumption.
```

Preferred classification if supported by the implementation:

```text
PGEN-ARITHMETIC-FRONTIER-AUDITED
```

## I. Verification

At minimum build:

```bash
lake build DkMath.NumberTheory.CyclotomicQRTraceOneBridge
lake build DkMath.FLT.Seven.QuadraticResidualPacket
lake build DkMath.FLT.Seven.QuadraticEuclidean
lake build DkMath.FLT.Seven.QuadraticUnits
lake build DkMath.FLT.Seven.QuadraticCoprimeFactor
lake build DkMath.FLT.Seven.QuadraticConjugateCoprime
lake build DkMath.FLT.Seven.QuadraticSeventhPowerNormalForm
lake build DkMath.FLT.Seven
```

If new neutral production declarations are added, provide focused `#print axioms` coverage.

No new `sorry`, `sorryAx`, or explicit `axiom`.
Run `git diff --check`.

## Non-goals

Do not attempt in this phase to prove:

- every prime-discriminant TraceOne order is Euclidean/PID/UFD;
- every unit is a p-th power;
- vanishing of arbitrary class groups or p-torsion;
- Kummer regular-prime theory;
- a general FLT contradiction.

The purpose of Phase 14 is to expose the **first arithmetic obstruction after the now-generic quadratic-cyclotomic front-end**.