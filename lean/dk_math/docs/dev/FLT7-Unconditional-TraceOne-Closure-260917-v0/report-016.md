# FLT7TC-005R11 — Chosen-factor/tail nonramified coprimality and direct ideal extraction

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

The attached `instruction-016.md` was treated as the bounded implementation
contract, separately from the user's request.  The implementation remains on
the current `PrimitiveCounterexampleRamifiedProvenance` direct cyclotomic
route.  It does not use `RamifiedSignedRootRoutingPacket`, a receiver
assumption, or a theorem carrying `sorryAx`.

## Results

The new module is
`DkMath/FLT/Seven/PrimeTraceOneDirectCyclotomicChosenTail.lean`.

1. **Common phase quotient: green.**  For every natural `j`, the module
   defines

   ```text
   F_j = ofReal L - zeta^j * ofReal R
   S_j = sum_{k < j} zeta^k
   Q_j = directRamifiedGapTail + S_j * ofReal R
   ```

   and proves `F_j = ramifiedUniformizer * Q_j`.  The `j=1` quotient is
   definitionally calibrated by a proved equality to
   `directRamifiedQuotient`.

2. **Exact ramified residue: green.**  The kernel-checked formula is

   ```text
   ramifiedEval Q_j = (j : ZMod 7) * (R : ZMod 7).
   ```

   Therefore `Q_j` is not in `ramifiedPrime`, and `F_j` is not in
   `ramifiedPrime^2`, for `1 ≤ j < 7`; membership of `F_j` in
   `ramifiedPrime` is proved from the explicit factorization.

3. **Chosen/other common-prime classification: green.**  For `2 ≤ j < 7`,
   a prime ideal containing `F_1` and `F_j` equals `ramifiedPrime`.  The
   `(zeta - 1)` branch uses the concrete maximal ramified kernel.  The `R`
   branch uses the stored integer endpoint Bezout relation to derive
   `1 ∈ P`, hence contradicts properness.

4. **Chosen quotient versus tail: green.**  The singleton ideals generated
   by `Q_1` and `Q_j` are coprime for `2 ≤ j < 7`.  The explicit five-element
   tail indexed by `{2,3,4,5,6}` is coprime to `Q_1` using the finite-product
   coprimality helper.  No all-pairs coprimality claim is made.

5. **Products and phase correspondence: green.**  The module proves the
   five-phase factorization, the six-phase factorization, and the correspondence
   with the existing `sixPhaseProduct` through the checked rotation/star
   formulas.  In particular,

   ```text
   Q_1 * T = ramifiedSevenUnit * ofReal(B)^7.
   ```

   The unit is used only as a unit; it is not asserted to be a seventh power.

6. **Ideal extraction: green.**  Unit removal at the principal-ideal level
   gives

   ```text
   span {Q_1} * span {T} = span {ofReal B}^7.
   ```

   The two-factor Dedekind theorem then yields `span {Q_1} = I^7`, and the
   final direct target is kernel-checked:

   ```text
   ∃ I, span {directLinearFactor r} = ramifiedPrime * I^7.
   ```

7. **Optional PID/unit normalization: not attempted.**  The associated-unit
   element equation and its `mu_7` phase normalization remain downstream
   work.  No FLT7 contradiction or receiver existence is claimed.

## Outcome

**Outcome A — CHOSEN/TAIL COPRIMALITY AND DIRECT RAMIFIED-IDEAL SEVENTH-POWER EXTRACTION GREEN**

The primary success theorem is kernel-checked from the current counterexample
provenance.  The remaining frontier is strictly after ideal extraction:
PID associated-unit handling and the `mu_7` phase, followed by any separate
descent argument.

## Validation

The following commands completed successfully:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicChosenTail
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectCyclotomicChosenTailApi
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectCyclotomicChosenTailAxiom
```

The API audit checks the `j=1` calibration, `j=2` common-prime theorem,
chosen/tail coprimality, quotient ideal product, and final ideal packet.  The
axiom audit for all decisive new theorems reports only
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` occurs.  The
public `DkMath.FLT.Seven` facade was not extended.
