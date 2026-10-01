# GCNB-004 implementation report

## Result

Outcome A for the required neutral bridge: the canonical cyclotomic carrier
now has a principal ideal, an exact absolute ideal norm, complete gap
transport, divisibility rewrites, and global rational-prime valuation
transport.

The new production module is:

```text
DkMath/CFBRC/CyclotomicIdeal.lean
```

and it is exported from `DkMath.CFBRC`.

## Principal ideal and absolute norm

The principal ideal is defined by

```lean
cyclotomicLinearFactorIdeal hζ x u
```

as the ideal span of
`cyclotomicLinearFactorInRingOfIntegers hζ x u`.

The canonical theorem is:

```lean
cyclotomicLinearFactorIdeal_absNorm_eq_GN hζ
```

Its proof uses only `Ideal.absNorm_span_singleton`, the unconditional
GCNB-003R integer Norm = GN theorem, and `Int.natAbs_natCast`. No field norm
is recomputed in this checkpoint.

## Complete gap and divisibility transport

The complete factor is retained by:

```lean
gap_mul_cyclotomicLinearFactorIdeal_absNorm_eq_sub_pow hζ
```

which states

```text
x * Ideal.absNorm I = (x + u)^p - u^p.
```

This is explicitly an ideal absolute-norm identity. It does not claim that the
field norm of `x * alpha` is `x * GN`; the latter would have the degree factor
`x^(p-1)`.

The exact divisibility rewrites are:

```lean
dvd_cyclotomicLinearFactorIdeal_absNorm_iff_dvd_GN hζ
dvd_sub_pow_iff_dvd_gap_mul_cyclotomicLinearFactorIdeal_absNorm hζ
```

They do not choose a prime ideal above a rational prime.

## Global valuation transport

The unconditional global rewrite is:

```lean
padicValNat_cyclotomicLinearFactorIdeal_absNorm_eq_GN hζ
```

Under the existing Bridge hypotheses (`2 ≤ p`, positive `x` and `u`, prime
`q`, and `q ∤ x`), the carrier-level complete-difference theorem is:

```lean
padicValNat_cyclotomicLinearFactorIdeal_absNorm_eq_sub_pow_of_not_dvd_boundary
  hζ hp2 hx hu hqP hq_not_dvd_x
```

It delegates the arithmetic valuation step to the existing
`DkMath.CFBRC.Bridge` theorem.

## Aggregate ideal-factor audit and firewall

The pinned Dedekind API confirms the relevant factorization shape:

```text
I ≠ 0
  -> finprod over HeightOneSpectrum of P^(multiplicity P I) = I
  -> count_normalizedFactors_eq_multiplicity
```

The API also requires a chosen height-one prime ideal and nonzero-ideal
hypotheses for the multiplicity conversion. It does not provide an immediate
theorem identifying

```text
padicValNat q (Ideal.absNorm I)
```

with the multiplicity of one selected prime ideal `P` above `q`. Such a result
would require the aggregate residue-degree/ideal-norm contribution over all
prime ideals above `q`. No aggregate theorem is forced into this checkpoint;
that layer is deferred to a possible GCNB-004L follow-up.

In particular, this implementation does not claim an individual local ideal
valuation, a principal-ideal p-th-power result, principalization, unit-sector
control, TraceOne compatibility, or an FLT consequence.

## Regression coverage

`DkMathTest/CFBRC/CyclotomicIdeal.lean` checks:

- absolute ideal Norm = GN at `p = 3, 5, 7` with `u = 1`;
- the `u = 0` ideal-norm boundary at `p = 3, 5, 7`;
- the complete gap identity for generic prime `p`;
- divisibility rewrites for the ideal norm and complete difference;
- unconditional global valuation rewrite;
- valuation transport to the complete difference at `p = 3`, `q = 2`;
- `#print axioms` for the new public theorems.

## Validation

The focused module and test builds completed successfully:

```text
lake build DkMath.CFBRC.CyclotomicIdeal
lake build DkMathTest.CFBRC.CyclotomicIdeal
lake build DkMath.CFBRC
lake build DkMath
git diff --check
git diff --no-index --check /dev/null DkMath/CFBRC/CyclotomicIdeal.lean  # exit 1: differences present, no whitespace error
git diff --no-index --check /dev/null DkMathTest/CFBRC/CyclotomicIdeal.lean  # exit 1: differences present, no whitespace error
git diff --no-index --check /dev/null docs/dev/GTail-Cyclotomic-Norm-Bridge-260922-v0/report-002.md  # exit 1: differences present, no whitespace error
```

The changed proof files have no `sorry`, `admit`, `sorryAx`, `unsafe`, or
`axiom` matches. The three `git diff --no-index --check` commands return the
normal nonzero status because the compared paths differ from `/dev/null`; they
emit no whitespace error. The known pre-existing full-build warning at
`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147` remains outside
this checkpoint.
