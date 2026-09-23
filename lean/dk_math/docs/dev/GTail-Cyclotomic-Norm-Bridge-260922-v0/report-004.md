# GCNB-006 implementation report

## Result

Outcome A for the norm-level cyclotomic/TraceOne compatibility checkpoint.
The canonical cyclotomic ideal absolute norm and the TraceOne coordinate norm
are now connected by the same scalar `GTail`/`GN` value, including the
nonnegative and rational-prime valuation/divisibility forms.

The new production module is:

```text
DkMath/FLT/Prime/PrimeCyclotomicTraceOne.lean
```

It is exported through `DkMath.FLT.Prime`.

## Unconditional shell bridge

`DkMath.CosmicFormula.natCast_GTail_one_eq_GTailCyclotomicShell` is now
unconditional in `g`. Its proof uses the existing cancellation-free
`GTail_one_eq_GTailCyclotomicShell` directly over `ℤ`; it does not pass through
`ℚ` or use field cancellation.

The former conditional proof path remains available as
`natCast_GTail_one_eq_GTailCyclotomicShell_of_ne_zero`.

The `g = 0`, `u = 0`, and `g = u = 0` boundaries are covered by the focused
test module.

## Scalar TraceOne compatibility

The `TraceOneScalar` API provides:

```lean
coord_norm_eq_cyclotomicIdeal_absNorm
coord_natAbs_norm_eq_cyclotomicIdeal_absNorm
padicValNat_coord_natAbs_norm_eq_ideal_absNorm
dvd_coord_natAbs_norm_iff_dvd_ideal_absNorm
```

The central equality is the integer-valued identity

```text
norm (P.coord (g + u) u) = (Ideal.absNorm I_alpha : ℤ),
```

and the natural-valued form is

```text
Int.natAbs (norm (P.coord (g + u) u)) = Ideal.absNorm I_alpha.
```

The proof reuses `P.coord_norm_eq`, the unconditional Nat/Int shell bridge,
and `cyclotomicLinearFactorIdeal_absNorm_eq_GN`. It does not recompute
QR/QNR products or field norms.

## FLT packet specializations

The adapter provides:

```lean
PrimeAdicFactorPacket.coord_norm_eq_cyclotomicIdeal_absNorm
PrimeAdicFactorPacket.gap_mul_coord_natAbs_norm_eq_pow
PrimeAdicPowerSplit.coord_natAbs_norm_eq_prime_mul_pow
PrimeAdicPowerSplit.padicValNat_coord_natAbs_norm_eq_one
```

Therefore the existing packet equations can be read through the TraceOne
scalar without changing their arithmetic content. In particular, the
ramified normal form remains `p * S.b^p` and the valuation remains `1`.

The canonical adapter uses the standard `NumberField`/`Algebra ℚ L` instance
of the cyclotomic field. The older `PrimeTraceOneStrippedIdeal` module keeps
its explicit arbitrary Algebra parameter and continues to use its local
shell conversion; no Algebra-instance identification or representation map
was introduced.

## Firewall

This checkpoint proves scalar norm identities only. It does not identify the
cyclotomic element or ideal with a TraceOne coordinate, construct an
isomorphism of rings, match prime ideals on the two sides, preserve
class-group data, or infer ideal p-th-power roots.

## Regression coverage

`DkMathTest/FLT/Prime/PrimeCyclotomicTraceOne.lean` checks:

- unconditional Nat/Int bridge at zero and boundary coordinates;
- canonical CyclotomicField calibrations at `p = 3, 5, 7`;
- integer norm, `natAbs` norm, rational-prime valuation, and divisibility;
- the `PrimeAdicFactorPacket` complete-power identity;
- the `PrimeAdicPowerSplit` `p * b^p` and valuation forms;
- `#print axioms` for all new public adapter theorems.

No test constructs a counterexample or asserts an FLT conclusion.

## Validation

The required builds completed successfully:

```text
lake build DkMath.Lib.Cosmic.GTailCyclotomic
lake build DkMath.FLT.Prime.PrimeCyclotomicTraceOne
lake build DkMathTest.FLT.Prime.PrimeCyclotomicTraceOne
lake build DkMath.FLT.Prime.PrimeTraceOneStrippedIdeal
lake build DkMath.FLT.Prime
lake build DkMath.CFBRC
lake build DkMath
git diff --check
```

The new implementation files contain no `sorry`, `admit`, `sorryAx`,
`unsafe`, or new `axiom`. The known pre-existing warning at
`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147` and
`DkMath/FLT/Kummer/CyclotomicPrincipalization.lean:5389` remain outside this
checkpoint.
