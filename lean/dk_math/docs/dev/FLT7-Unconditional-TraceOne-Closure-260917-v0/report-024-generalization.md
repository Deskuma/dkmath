# FLT7TC-005R24 — Homogeneous power quotient common-prime kernel

## Scope

Instruction-024 requested a reusable homogeneous power quotient layer, its
gap congruence, a weakest clean common-prime localization statement, and a
small FLT7 calibration. The generic module was kept independent of every
`DkMath.FLT.*` module.

## Reuse audit

The repository already owns the canonical quotient in
`DkMath.Algebra.DiffPow.diffPowSum`:

```text
diffPowSum x y n = ∑ i ∈ range n, x^(n - 1 - i) * y^i.
```

Its existing factorization theorem and sum-minus-constant identity were
reused. No competing quotient definition was introduced. The new neutral
alias is `DkMath.Lib.NumberTheory.homogeneousPowerQuotient`.

The other requested modules were inspected before editing. Their APIs are
specialized to cyclotomic shells, Nat/Int gcd calculations, or power-factor
support, so none was copied into the new layer.

## Implemented kernel

`DkMath.Lib.NumberTheory.HomogeneousPowerQuotient` now provides, for a
commutative ring and arbitrary `n : ℕ`:

- `pow_sub_pow_eq_gap_mul_homogeneous`;
- `gap_dvd_homogeneous_sub_natCast_mul`;
- `prime_dvd_exponent_cast_of_dvd_gap_and_homogeneous` under
  `Prime q`, `q ∣ x - y`, `q ∣ homogeneousPowerQuotient x y n`, and
  `¬ q ∣ y`;
- `prime_dvd_exponent_cast_of_coprime_gap_and_homogeneous`, deriving the last
  nondivisibility condition from `IsCoprime x y`.

The proof uses only the generic gap congruence and prime divisibility of a
product. No number-field or exponent-7 assumption occurs in the reusable
theorems.

## Calibration and audits

`DkMathTest/NumberTheory/HomogeneousPowerQuotient.lean` checks exponents 3,
5, and 7 and an integer common-prime example. The FLT7 bridge
`DkMathTest/FLT/SevenHomogeneousPowerQuotientCalibration.lean` proves that
the generic quotient at exponent 7 equals the existing
`SevenRealCubicInt.seventhQuotient`, then replays the existing seventh-power
factorization and gap congruence on that type.

`HomogeneousPowerQuotientAxiom.lean` reports only the standard
`propext`, `Classical.choice`, and `Quot.sound` dependencies. The generic
source has no `DkMath.FLT` import and no forbidden `sorry`, `sorryAx`,
`admit`, `unsafe`, or project `axiom` construct.

The optional generic AM-GM inequality was not added; it is outside this
quotient/localization kernel and remains deferred.

## Verification log

The following Lean commands were run sequentially:

```text
lake env lean DkMath/Lib/NumberTheory/HomogeneousPowerQuotient.lean
lake build DkMath.Lib.NumberTheory.HomogeneousPowerQuotient
lake env lean DkMathTest/NumberTheory/HomogeneousPowerQuotient.lean
lake env lean DkMathTest/NumberTheory/HomogeneousPowerQuotientAxiom.lean
lake env lean DkMathTest/FLT/SevenHomogeneousPowerQuotientCalibration.lean
lake build DkMath.Lib
lake build DkMathTest.NumberTheory.HomogeneousPowerQuotient
lake build DkMathTest.NumberTheory.HomogeneousPowerQuotientAxiom
lake build DkMathTest.FLT.SevenHomogeneousPowerQuotientCalibration
```

All commands completed successfully. The generic module was also added to
`DkMath.Lib` as a public import.

## Boundary

This promotes a generic algebraic/common-prime kernel and a checked FLT7
reexport/calibration only. It does not provide prime existence, a universal
FLT7 contradiction, or unconditional FLT closure.
