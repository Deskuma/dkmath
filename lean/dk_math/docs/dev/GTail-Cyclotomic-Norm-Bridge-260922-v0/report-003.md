# GCNB-005 implementation report

## Result

Outcome A for the required generic packet-to-carrier adapter: the generic
prime-adic factor packet now reaches the canonical cyclotomic ideal carrier,
and the ramified `PrimeAdicPowerSplit` normal form is available at the ideal
norm level.

The new production module is:

```text
DkMath/FLT/Prime/PrimeCyclotomicIdeal.lean
```

It is exported by `DkMath.FLT.Prime`. The CFBRC layer remains independent of
the FLT layer: the adapter imports the existing CFBRC ideal API, while
`DkMath.CFBRC` does not import FLT.

## Generic prime-adic packet

For a `PrimeAdicFactorPacket p g u x` and a primitive `p`-th root in the
cyclotomic field, the adapter provides:

```lean
PrimeAdicFactorPacket.cyclotomicIdeal_absNorm_eq_residual
PrimeAdicFactorPacket.gap_mul_cyclotomicIdeal_absNorm_eq_pow
PrimeAdicFactorPacket.padicValNat_cyclotomicIdeal_absNorm_eq_one
PrimeAdicFactorPacket.prime_dvd_cyclotomicIdeal_absNorm
PrimeAdicFactorPacket.prime_sq_not_dvd_cyclotomicIdeal_absNorm
```

Thus the ideal absolute norm is `GTail p 1 g u` (equivalently the existing
`GN`), the packet equation is transported as

```text
g * Ideal.absNorm I = x^p,
```

and the exact rational-prime valuation information is transported as
`padicValNat p (Ideal.absNorm I) = 1`, `p ∣ Ideal.absNorm I`, and
`¬ p^2 ∣ Ideal.absNorm I`.

## Ramified and counterexample routes

The ramified split has the normal form

```lean
PrimeAdicPowerSplit.cyclotomicIdeal_absNorm_eq_prime_mul_pow
```

which states `Ideal.absNorm I = p * S.b^p`; the pre-existing `S.gap_eq`
remains available separately.

For every `PrimeGe5CounterexamplePack`, the generic carrier identity is:

```lean
PrimeGe5CounterexamplePack.gap_mul_cyclotomicIdeal_absNorm_eq_pow
```

It does not assume `p ∣ gap`, so it covers both away and ramified branches at
the carrier level. The thin constructor

```lean
PrimeGe5CounterexamplePack.toPrimeAdicFactorPacket_of_prime_dvd_gap
```

adds `p ∣ gap` only when constructing the ramified `PrimeAdicFactorPacket`.
The branch distinction is therefore retained rather than promoted to a
global divisibility hypothesis.

No local prime-ideal aggregation, principalization, ideal p-th-power
inference, TraceOne production import, or FLT conclusion is introduced by
this checkpoint.

## Regression coverage

`DkMathTest/FLT/Prime/PrimeCyclotomicIdeal.lean` checks:

- the generic packet carrier, gap, valuation, divisibility, and square-free
  consequences;
- the ramified `p * b^p` ideal-norm normal form and `S.gap_eq`;
- the generic `PrimeGe5CounterexamplePack` carrier identity;
- the local ramified constructor requiring `p ∣ gap`;
- the existing `p = 7` compatibility constructor;
- `#print axioms` for every new public theorem.

The new declarations introduce no `sorry`, `admit`, `sorryAx`, `unsafe`, or
new `axiom`. Their axiom reports contain only the ordinary logical axioms
already used by the surrounding development.

## Validation

The required builds and whitespace audit completed successfully:

```text
lake build DkMath.FLT.Prime.PrimeCyclotomicIdeal
lake build DkMathTest.FLT.Prime.PrimeCyclotomicIdeal
lake build DkMath.FLT.Prime
lake build DkMath.CFBRC
lake build DkMath
git diff --check
```

The known pre-existing full-build warning at
`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147` remains outside
this checkpoint.
