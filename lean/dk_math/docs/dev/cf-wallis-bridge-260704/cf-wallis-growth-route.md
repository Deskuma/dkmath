# Wallis-Cosmic Growth Route

This note records the growth route after the Wallis-Cosmic finite and limit
bridges.

The goal is not to use Stirling's approximation as the conceptual source.
Instead, DkMath reads the central binomial growth from exact finite products.

## Exact identity

The Lean module `DkMath.Pascal.WallisGrowthBridge` now proves:

```text
centralRatioQ m ^ 2
  = (2*m + 1) * wallisPartialQ m
```

and the cosmic version:

```text
centralRatioQ m ^ 2
  = (2*m + 1) * cosmicPartialQ m
```

This comes from two exact finite facts:

```text
centralRatioQ m * mirrorOddRatioPartialQ m = wallisPartialQ m
centralRatioQ m / mirrorOddRatioPartialQ m = 2*m + 1
```

The second identity is the telescoping mirror ratio.

## Growth reading

The limit module already proves:

```text
wallisPartialQ m -> pi / 2
```

The growth module now proves the squared normalized limit:

```lean
theorem tendsto_real_centralRatioQ_sq_div_nat_pi :
  Filter.Tendsto
    (fun m : Nat => (((centralRatioQ m : Q) : R) ^ 2 / (m : R)))
    Filter.atTop
    (nhds Real.pi)
```

It also proves the square-root form:

```lean
theorem isEquivalent_real_centralRatioQ_sqrt_pi_mul_nat :
  (fun m : Nat => ((centralRatioQ m : Q) : R)) ~[Filter.atTop]
    (fun m : Nat => Real.sqrt (Real.pi * (m : R)))
```

Finally, the growth module now inverts the definition of `centralRatioQ` and
proves the central-binomial coefficient form:

```lean
theorem isEquivalent_real_centralBinomial_sqrt_pi_mul_nat :
  (fun m : Nat => ((Nat.choose (2 * m) m : Nat) : R)) ~[Filter.atTop]
    (fun m : Nat => (4 : R) ^ m / Real.sqrt (Real.pi * (m : R)))
```

Therefore the squared central ratio has the growth line:

```text
centralRatioQ m ^ 2 ~ pi * m
```

and hence:

```text
centralRatioQ m ~ sqrt (pi * m)
```

Since:

```text
centralRatioQ m = 4^m / Nat.choose (2*m) m
```

inverting gives the central-binomial growth law:

```text
Nat.choose (2*m) m ~ 4^m / sqrt (pi * m)
```

## Formal checkpoints just closed

The first closed theorem is:

```lean
Filter.Tendsto
  (fun m : Nat => (((centralRatioQ m : Q) : R) ^ 2 / (m : R)))
  Filter.atTop
  (nhds Real.pi)
```

This should use:

```text
centralRatioQ m ^ 2 = (2*m + 1) * wallisPartialQ m
wallisPartialQ m -> pi / 2
(2*m + 1) / m -> 2
```

The `m = 0` issue is only an `atTop` bookkeeping problem.  The Lean proof
handles it with the finite rewrite under `m ≠ 0` and the eventual fact
`eventually_gt_atTop 0`.

The second closed theorem is:

```lean
theorem isEquivalent_real_centralRatioQ_sqrt_pi_mul_nat :
  (fun m : Nat => ((centralRatioQ m : Q) : R)) ~[Filter.atTop]
    (fun m : Nat => Real.sqrt (Real.pi * (m : R)))
```

This uses the operational limit:

```lean
theorem tendsto_real_centralRatioQ_div_sqrt_pi_mul_nat_one :
  Filter.Tendsto
    (fun m : Nat =>
      ((centralRatioQ m : Q) : R) / Real.sqrt (Real.pi * (m : R)))
    Filter.atTop
    (nhds 1)
```

The proof takes the square root of the squared normalized growth theorem and
uses positivity of `centralRatioQ m`.

The third closed theorem is:

```lean
theorem isEquivalent_real_centralBinomial_sqrt_pi_mul_nat :
  (fun m : Nat => ((Nat.choose (2 * m) m : Nat) : R)) ~[Filter.atTop]
    (fun m : Nat => (4 : R) ^ m / Real.sqrt (Real.pi * (m : R)))
```

It also has a more explicit searchable alias:

```lean
theorem isEquivalent_real_centralBinomial_four_pow_div_sqrt_pi_mul_nat
```

This uses the finite inversion identities:

```lean
theorem nat_choose_two_mul_self_cast_eq_pow_four_div_centralRatioQ
theorem real_nat_choose_two_mul_self_eq_pow_four_div_centralRatioQ
```

and then divides `4^m ~ 4^m` by
`centralRatioQ m ~ sqrt (Real.pi * m)`.

The fourth closed theorem packages the same statement as an operational ratio
limit:

```lean
theorem tendsto_real_centralBinomial_div_four_pow_div_sqrt_pi_mul_nat_one :
  Filter.Tendsto
    (fun m : Nat =>
      ((Nat.choose (2 * m) m : Nat) : R) /
        ((4 : R) ^ m / Real.sqrt (Real.pi * (m : R))))
    Filter.atTop
    (nhds 1)
```

This is equivalent to the `IsEquivalent` theorem above, but it is often easier
for downstream users who want a direct `Tendsto` surface.

## Next formal checkpoint

The remaining work is presentation and downstream usability: expose a
conventional Stirling-style theorem name while keeping the proof source
explicitly Wallis-derived.  A useful follow-up is also to add short aliases
for common RHS spellings, if downstream files expect a different arrangement
of `4^m`, division, or square root.
