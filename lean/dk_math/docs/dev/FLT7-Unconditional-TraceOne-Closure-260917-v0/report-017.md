# FLT7TC-005R12 — Direct chosen-quotient unit congruence and p=7 Kummer-unit frontier

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

The attached `instruction-017.md` was treated as the bounded implementation
contract, separately from the user's request.  This checkpoint stays on the
current `PrimitiveCounterexampleRamifiedProvenance` direct cyclotomic route.
It does not use `RamifiedSignedRootRoutingPacket`,
`CubicGapSeventhShapeReceiver`, or a theorem with `sorryAx` in the decisive
new declarations.

## Implementation

The new module is
`DkMath/FLT/Seven/PrimeTraceOneDirectCyclotomicUnitCongruence.lean`.

It defines `sevenIdeal`, the element-level
`DirectCyclotomicChosenQuotientPowerPacket`, and the exact specification
`DegreeSixKummerUnitLemmaAtSeven` for the remaining unit-theory target.  From
the R11 ideal extraction and the concrete PID generator theorem it proves the
following current-provenance facts:

1. `Q₁ = unit * beta^7` is checked, with `unit_isUnit`, `span_beta`, and the
   same stored `r` retained in the packet.
2. The R11 tail is in `(7)`, and hence
   `Q₁ - ofReal(endpointRight) ∈ sevenIdeal`.
3. For every degree-six carrier element `a`, there is an integer `n` with
   `a^7 - n ∈ sevenIdeal`.  The proof uses `adjoin_zeta_eq_top`, the explicit
   `zeta^7 = 1` relation, and characteristic-seven binomial identities; it
   does not assume that the quotient by `(7)` is reduced.
4. The packet unit is congruent modulo `(7)` to an integer not divisible by
   seven.  The scalar attached to `beta` is shown nonzero using
   `Q₁ ∉ ramifiedPrime`, not an integer norm shortcut.
5. The quadratic norm is kernel-checked as
   `directChosenQuotientRealSource r`, namely
   `L*R - eisensteinAxis^35 * thetaSevenUnit^12 * A^14`.
   Its mod-seven coordinates are `(nonzero, 0, 0)`.  Consequently the
   associated real-cubic norm unit has zero projective logarithm and is a
   seventh power in `SevenRealCubicIntˣ`.

## Ten checkpoint questions

1. **Is `Q₁ = unit * beta^7` checked?** Yes, directly from the R11 ideal
   seventh-power theorem and `unitMulPowOfSpanEqPow`.

2. **Is `Q₁ ≡ endpointRight (mod 7)` checked?** Yes.  The explicit tail has
   `ramifiedUniformizer^35`; total ramification converts it to an element of
   the principal ideal `(7)`.

3. **Is arbitrary degree-six seventh-power scalarization modulo `(7)` checked?**
   Yes: `degreeSix_pow_seven_scalarized_mod_seven`.

4. **Is the actual associated unit congruent to a nonzero rational integer?**
   Yes: `unit_congruentToRationalModSeven`, with the integer proved not
   divisible by seven.

5. **Is the relative real-cubic unit class a seventh power?** Yes.  The
   quadratic norm of the packet unit has zero projective logarithm, and
   `exists_realNormUnit_seventhPower` supplies the real-cubic seventh root.

6. **Is the remaining degree-six class reduced to a pure `mu_7` /
   relative-norm-kernel phase?** Not yet.  The real norm class is killed, but
   a checked lift of its real-cubic root, or an equivalent classification of
   the relative norm-one unit quotient, is absent.

7. **Is the full p=7 Kummer unit lemma proved?** No.  The exact unproved
   target is `DegreeSixKummerUnitLemmaAtSeven`.

8. **Is `Q₁` an exact seventh power and is
   `directLinearFactor = ramifiedUniformizer * gamma^7` checked?** No.  Those
   conclusions require item 7 and are deliberately not asserted.

9. **What first theorem remains?** Prove the concrete degree-six unit bridge:
   either establish the required ring-of-integers/rank-six unit transport and
   the p=7 Kummer unit lemma, or directly classify the relative norm-one
   units modulo seventh powers and show that the mod-seven rational congruence
   kills the residual phase.

10. **What do the decisive axiom audits contain?** The focused axiom audit
    reports only `propext`, `Classical.choice`, and `Quot.sound` for the new
    scalarization, packet, congruence, norm, projective-log, and real-root
    theorems.  No `sorryAx` occurs in those outputs.

## Outcome

**Outcome C — ELEMENT PACKET AND MOD-SEVEN RATIONAL CONGRUENCE GREEN; FULL
KUMMER UNIT LEMMA BLOCKED ON A CONCRETE UNIT-THEORY BRIDGE.**

The real free unit class is independently removed by the norm/projective-log
audit.  This is not an unconditional FLT7 result and does not provide a
receiver or contradiction.

## Validation

The following focused builds completed successfully:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicUnitCongruence
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectCyclotomicUnitCongruenceApi
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectCyclotomicUnitCongruenceAxiom
```

The new production module and focused audit sources contain no `sorry`,
`admit`, `unsafe`, project `axiom`, or `sorryAx` token.  The public
`DkMath.FLT.Seven` facade was not extended because the remaining full-unit
bridge is not yet a stable theorem surface.
