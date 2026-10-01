# GCNB-003 implementation report

## Result

Outcome B — a neutral integer ring-of-integers Norm bridge was extracted with
the explicit hypothesis `u ≠ 0` in gap/base coordinates.

The public carrier and theorem are:

```lean
cyclotomicLinearFactorInRingOfIntegers hζ x u
cyclotomicLinearFactor_norm_eq_GN_ratCast hζ hu0
cyclotomicLinearFactor_norm_eq_GN hζ hu0
```

The carrier is the ring-of-integers image of

```text
(x + u) - ζ * u
```

and the exported conclusion is the integer norm identity

```text
Algebra.norm ℤ carrier = ((GN p x u : Nat) : Int).
```

The corresponding rational field norm is used internally through
`Algebra.coe_norm_int`; the final public API is the integral theorem requested
by the checkpoint.

## Proof and dependency boundary

The proof was added to `DkMath/CFBRC/CyclotomicNorm.lean`. It uses only the
neutral CFBRC/cyclotomic and Mathlib NumberField APIs. In particular, it does
not import `DkMath.FLT.Kummer.CyclotomicPrincipalization`.

The proof route is:

1. evaluate the prime cyclotomic polynomial at the rational ratio
   `(x + u) / u`;
2. transport the shifted homogeneous evaluation to `GN` using the existing
   CFBRC prime-core bridge;
3. compute the field norm of the chosen linear factor;
4. descend to the integer norm with `Algebra.coe_norm_int`.

No `x ≠ 0`, endpoint inequality, or natural subtraction hypothesis is used.
The current ratio/evaluation API requires `u ≠ 0`; this is the exact remaining
boundary for Outcome B. The `u = 0` boundary was not manufactured into the
Norm theorem.

The theorem remains prime-only. No composite-degree identification with a
single cyclotomic polynomial was added.

## Compatibility and regressions

`DkMathTest/CFBRC/CyclotomicNorm.lean` checks:

- the generic integer Norm theorem for the canonical fields
  `CyclotomicField 3 ℚ`, `CyclotomicField 5 ℚ`, and `CyclotomicField 7 ℚ`;
- `cyclotomicRootProduct = GTailCyclotomicShell`;
- `cyclotomicRootProduct = ((GN p x u : Nat) : K)`;
- the existing boundary `GTail d 1 0 u = GTailCyclotomicShell d 0 u`;
- `#print axioms` for the new public Norm theorems and the compatibility
  theorems.

The new theorem axiom surface is the ordinary imported Mathlib/classical
surface (`propext`, `Classical.choice`, `Quot.sound`); no `sorryAx` is
introduced.

## Validation

The following commands completed successfully:

```text
lake build DkMath.CFBRC.CyclotomicNorm
lake build DkMathTest.CFBRC.CyclotomicNorm
lake build DkMath.CFBRC
lake build DkMath
git diff --check
```

The full `DkMath` build still reports the pre-existing
`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147` `sorry` warning;
that file is outside this checkpoint.

Changed production and test files were scanned for `sorry`, `admit`, `sorryAx`,
`unsafe`, and `axiom`. The proof files contain no forbidden proof token; the
only `axiom` matches are the required `#print axioms` audit commands in the
test file. The report itself mentions the scan terms and the pre-existing
full-build warning above.
