# Generalization handoff from the closed FLT7 branch

This branch is not continuing as R65/R66 FLT7 work.  The next branch belongs
in the generic FLT/GN/cyclotomic/norm layer.  FLT7 may consume that machinery
only after it supplies a new theorem that specializes to a deferred local
obligation.

## Existing generic base

The production infrastructure to reuse is:

- GN is the exponent-generated factor in `x^p = u * GN p u y` after the FLT
  gap substitution.
- For prime `p`, `GN p (z-y) y` is the homogeneous cyclotomic factor.
- `DkMath.CFBRC.CyclotomicProduct` contains
  `cyclotomicDivisorsProductShifted_eq_GN_of_ne_zero`.
- `DkMath.CFBRC.Bridge` exposes valuation and primitive-prime bridges.
- `DkMath.FLT.Kummer.CyclotomicPrincipalization` consumes the
  `cyclotomicDivisorsProductShifted = GN` bridge.
- The generic FLT Prime / TraceOne route reaches coprime ideal `p`-th powers
  in the quadratic TraceOne shadow.
- `TraceOnePowerLanding` and lattice landing are the natural output-side
  receivers.

These facts do not by themselves provide the missing norm bridge.

## Required new general bridge

The target shape is:

```text
FLT gap packet
    x^p = u * GN p u y
        |
        v
homogeneous cyclotomic / cyclotomic-field carrier
        |
        v
Norm / ideal / valuation / p-power preserving bridge
```

The missing theorem family must connect the complete product `x` or
`u * GN`, not `GN` alone, to a cyclotomic algebraic carrier whose norm
recovers the integer-side quantity in a form useful for FLT.

Candidate signatures for investigation, not assertions in this branch, are:

```text
norm_cyclotomicCarrier_eq_gap_mul_GN
norm_cyclotomicCarrier_eq_sub_pow_quotient
```

Alternatively, use a packet carrying simultaneously:

- a field element;
- a norm identity;
- a principal ideal identity;
- `p`-power and valuation transport;
- compatibility with the existing TraceOne shadow.

Do not implement these candidates in the closed FLT7 branch.

## CFBRC dependency and re-entry gate

CFBRC already has cyclotomic product = GN, valuation bridge, and
primitive-prime/Zsigmondy bridge.  The next prerequisite is the norm-aware
layer required by the generalized FLT packet.  Treat “CFBRC norm lemmas are
ready” as a re-entry gate, not as work to construct here.

## Generalization priority

Proceed in this order:

1. `x * GN` / FLT-gap packet to cyclotomic-carrier bridge.
2. Cyclotomic-carrier Norm identity and ideal-level transport.
3. Compatibility with generic Prime/TraceOne residual `p`-th-power packets.
4. Generic power landing / class-group / unit-sector consequences.
5. Regression and specialization at `p = 3, 5, 7`.
6. Only then revisit the deferred FLT7 carrier cutoff and global aggregation.

## Future FLT7 input

The general machinery should eventually supply one or both of:

- a generic norm/ideal theorem strong enough to lift the R64 selected-factor
  multiplicity `14 * eQ` to the degree-six carrier cutoff;
- a generic principal-ideal / `p`-th-power aggregation theorem combining the
  local oriented factors across common primes.

If either input becomes available, specialize it to `p = 7` and resume the
mathematical endpoint in a new branch.  Do not continue this branch.
