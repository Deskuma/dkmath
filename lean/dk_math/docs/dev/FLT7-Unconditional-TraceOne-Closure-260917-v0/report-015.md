# FLT7TC-005R10 — Direct cyclotomic ideal ownership from the six-phase orbit

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

The attached `instruction-015.md` was treated as the bounded implementation
contract, separately from the user's request.  This checkpoint extends the
R9 direct factor without using the historical
`RamifiedSignedRootRoutingPacket` as a bypass.

## Results

1. **Exact ramified multiplicity one: yes.**  From the current summit gap
   equation
   `L-R = 7^6 * gapRoot^7`, the explicit uniformizer identity for `7`, and
   `endpointRight_not_seven_dvd`, the module proves:

   ```text
   eta ∈ ramifiedPrime
   eta ∉ ramifiedPrime^2.
   ```

   The quotient is explicit:

   ```text
   eta = ramifiedUniformizer * directRamifiedQuotient r.
   ```

   Its ramified residue is exactly `endpointRight` modulo `7`.

2. **Six-phase product: yes.**  The existing general `sixPhaseProduct`
   theorem is specialized directly to the R9 factor, giving the exact ring
   identity

   ```text
   sixPhaseProduct eta = (7 * residualRoot^7 : Ring).
   ```

3. **Six stripped factors/ideals: no.**  The current implementation does not
   construct six phase-indexed stripped elements or ideals.

4. **Stripped product as a seventh-power principal ideal: no.**  No such
   product identity is asserted.

5. **Pairwise coprimality: no.**  The nonramified common-prime argument for
   distinct rotated/conjugate phases remains open.

6. **Direct ideal identity: no.**  In particular, the theorem

   ```text
   Ideal.span {eta} = ramifiedPrime * I^7
   ```

   is not claimed.  The norm and exact local multiplicity are not promoted to
   global ideal ownership.

7. **PID element equation / unit: not applicable.**  Since the direct ideal
   packet is not established, no PID extraction or associated-unit equation is
   produced.

8. **TraceOne receiver comparison: no checked implication or equivalence.**
   The direct local factor and six-phase norm remain upstream data, with no
   proved bridge to `CubicGapSeventhShapeReceiver`.

9. **Axiom audit: clean.**  The decisive new theorem surfaces use only
   ordinary foundations among `propext`, `Classical.choice`, and `Quot.sound`;
   no `sorryAx` occurs.  No quarantined default/legacy Kummer theorem was used
   as a proof step.

## Outcome

**Outcome D — DIRECT NORM REMAINS GREEN, BUT ONE EARLIER IDEAL/GALOIS BRIDGE IS
STILL MISSING.**

The exact local uniformizer ownership of the original direct factor and the
global six-phase product are now kernel-checked.  The next missing bridge is
the transport of exact local ownership to every rotated/conjugate phase,
followed by pairwise nonramified coprimality and seventh-power ideal
extraction.  No PID/unit phase or unconditional FLT7 conclusion follows.

## Validation

The following builds completed successfully:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicIdealOwnership
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectCyclotomicIdealOwnershipApi
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectCyclotomicIdealOwnershipAxiom
```

The new production and audit sources contain no `sorry`, `admit`, `unsafe`, or
project `axiom` declarations.  The public facade was not extended.
