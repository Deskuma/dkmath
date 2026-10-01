# FLT7TC-005R19 — Stripped-core seventh-power extraction

## Scope

Instruction-025 asked for the current-provenance direct-orbit stripped-core
upgrade.  The implementation stays algebraic: it does not introduce a
receiver, a successor state, an Archimedean estimate, or a historical axis
drop packet.

## Implemented results

1. `directOrbit_commonPrime_associated_theta` now uses the neutral
   `prime_dvd_exponent_cast_of_coprime_gap_and_homogeneous` theorem from
   `DkMath.Lib.NumberTheory.HomogeneousPowerQuotient`.  The remaining
   specialization is the checked factorization
   `7 = eisensteinAxis^3 * thetaSevenUnit`, followed by the existing
   associatedness result for a prime divisor of `7`.

2. `directOrbit_stripped_cores_product_eq` proves the literal identity

   ```text
   gapCore * quotientCore =
     orbitUnit01 *
       (thetaSevenUnit^(1 + 2*k) * (a : SevenRealCubicInt)^2)^7.
   ```

   The proof records the right-hand theta depth `35 + 42*k` and cancels it
   against the stripped left-hand depth `(32 + 42*k) + 3`.

3. The two coprime cores are each extracted as associated seventh powers by
   `exists_associated_pow_of_associated_pow_mul`.  The associatedness
   orientation is then converted explicitly to

   ```text
   gapCore      = (gapUnit : O) * gapRoot^7
   quotientCore = (quotientUnit : O) * quotientRoot^7.
   ```

4. `DirectOrbitPowerSplitPacket` and
   `directOrbitPowerSplit_nonempty` retain the direct base provenance, gap
   split, exact depth equations, theta nondivisibility, coprimality, literal
   product identity, roots, units, and both unit-times-seventh-power
   equations.  The public facade `DkMath.FLT.Seven` exports the new module.

## Report questions and boundary

- The neutral common-prime kernel refactor is green.
- The exact theta-cancelled product identity is green.
- Both associated seventh-power extraction theorems are green.
- Explicit unit witnesses `gapUnit` and `quotientUnit` are green.
- The exact projective classes `(2,4)` and `(5,1)` were not added to the
  packet.  The current direct API does not yet expose the normalized local
  quotient-core congruence and its generator-invariance bridge required to
  prove those classes without an unsupported assumption.  Thus this
  checkpoint is **Outcome C** rather than Outcome A or B.
- No useful current-route axis-absorption equation was added; the optional
  historical exponent-3/exponent-7 audit was not used to instantiate a
  historical packet.
- Before the smaller-norm theorem, the remaining algebraic boundary is the
  kernel-checked projective-log identification for both extracted units.
  The Archimedean smaller-norm argument itself remains a subsequent
  checkpoint.

## Verification log

The following Lean commands were run sequentially:

```text
lake env lean DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicOrbitSplit.lean
lake env lean DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicOrbitPowerSplit.lean
lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicOrbitPowerSplit
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicOrbitPowerSplitApi
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicOrbitPowerSplitAxiom
lake build DkMath.FLT.Seven
```

All commands completed successfully.  The axiom audit for the product,
associated-power, packet-constructor, and public choice declarations reports
only `propext`, `Classical.choice`, and `Quot.sound`.

The decisive production source and tests contain no `sorry`, `sorryAx`,
`admit`, `unsafe`, or project `axiom`; the production module does not import
the historical `SevenRealCubicAxisDrop` packet.

## Mathematical boundary

This is a checked exact product and unit-times-seventh-power packet, not a
descent theorem or an unconditional FLT7 closure.  Units are retained and no
norm equality is used to infer element equality or coprimality.
