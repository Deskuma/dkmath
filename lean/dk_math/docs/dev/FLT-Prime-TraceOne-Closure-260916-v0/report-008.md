# FPTC-008 report — real `Fin p` sector receiver and obstruction frontier

## 1. Outcome

```text
Outcome B — REAL SECTOR RECEIVER GREEN; P5 BRIDGE FRONTIER ISOLATED
```

The generic real sector factorization now lands in explicit TraceOne power
coordinates, and the terminal-axis invariant yields the corresponding
prime-to-`p` base-norm condition.  The p=5 Golden coordinate receiver is also
green.  The specialized nonzero-sector elimination theorem is not applied to a
generic packet because the required generic-to-specialized stripped-packet
correspondence is not present.

The class-number frontier from FPTC-007 was not reopened.

## 2. Generic real receiver

The new production theorem is:

The theorem's result (with the repeated representative expression abbreviated
below as `sectorRep i`) is:

```text
∃ i : Fin p, ∃ m n : ℤ,
  (Q.residual * conj (sectorRep i)).fst =
    norm (sectorRep i) * (traceOnePowCoords (signedPrimeParameter p) m n p).1 ∧
  (Q.residual * conj (sectorRep i)).snd =
    norm (sectorRep i) * (traceOnePowCoords (signedPrimeParameter p) m n p).2
```

Here `sectorRep i` means exactly
`(traceOnePrimeRealFinSectorSystem P0.prime hmod).rep i` coerced to
`TraceOneInt (signedPrimeParameter p)`.  The complete kernel-checked theorem
in the source includes the following explicit hypotheses and conclusion:

```lean
exists_realSector_powCoords_of_primeTraceOneStrippedIdealPacket
    (P0 : PrimeAdicFactorPacket p g u x)
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ)
    (Q : PrimeTraceOneStrippedIdealPacket L P0 P)
    (hmod : p % 4 = 1) :
  let : Fact (∀ r : ℚ,
      r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) := ...
  let : Field (TraceOneRat (signedPrimeParameter p)) := ...
  let : NumberField (TraceOneRat (signedPrimeParameter p)) := ...
  let : IsDomain (TraceOneInt (signedPrimeParameter p)) := ...
  let : IsDedekindDomain (TraceOneInt (signedPrimeParameter p)) := ...
  classGroupPTorsionFreeAt (TraceOneInt (signedPrimeParameter p)) p →
    <the explicit two coordinate equations above>
```

The actual theorem retains the required local `Fact`, `Field`,
`NumberField`, `IsDomain`, and `IsDedekindDomain` bindings.

The proof composes
`exists_sector_mul_pow_of_primeTraceOneRealStrippedIdealPacket` with
`traceOne_pow_core_landing_iff`.  The recurrence is not re-proved and the
sector index `i` is retained.

## 3. Representative norm obligation

The only extra landing obligation is `norm beta ≠ 0`.  The new helper

```lean
traceOne_norm_ne_zero_of_isUnit
```

obtains an inverse from `IsUnit beta`, applies `traceOne_norm_mul`, and uses
the resulting integer identity `norm beta * norm beta⁻¹ = 1`.  Thus the
representative's unit property is sufficient; no unit classification is
unfolded in the FLT consumer.

## 4. Terminal-axis and base norm

The packet theorem

```lean
PrimeTraceOneStrippedIdealPacket.residual_natAbs_norm_not_dvd
```

proves

```text
¬ p ∣ Int.natAbs (norm Q.residual)
```

from `Q.residual_axis_terminal` through
`signedPrimeDiscriminantPacket` and
`PrimeDiscriminantPacket.discrAxis_dvd_iff_prime_dvd_natAbs_norm`.

For a sector factorization
`residual = beta * delta ^ p`, the theorem

```lean
primeTraceOne_base_norm_not_dvd_of_sector_factor
```

uses `traceOne_norm_mul`, `traceOne_norm_pow`, `Int.natAbs_mul`, and
`Int.natAbs_pow`.  If `p` divided `natAbs (norm delta)`, it would divide the
residual norm, contradicting terminality.  The combined real theorem

```lean
exists_realSector_mul_pow_with_baseNorm_not_dvd
```

therefore returns the sector factorization together with
`¬ p ∣ Int.natAbs (norm delta)`.

This is a p-th-power-base obstruction only.  It does not eliminate a nonzero
sector.

## 5. p=5 Golden receiver

The explicit p=5 calibration is green.  The new theorem

```lean
exists_goldenSector_powCoords_of_primeTraceOneStrippedIdealPacket_five
```

uses the existing
`exists_goldenSector_mul_fifth_of_primeTraceOneStrippedIdealPacket_five`
endpoint and `traceOne_pow_core_landing_iff`, producing exact coordinate
equations for the Golden representatives and `traceOnePowCoords 1 _ _ 5`.

Because `signedPrimeParameter 5 = 1` is not treated as a definitional equality
by elaboration in the dependent carrier, the residual is transported by the
small explicit definition

```lean
traceOneFiveResidualToGolden
```

using the checked equality `signedPrimeParameter_five`.  No equality between
the generic Dirichlet sector system and the explicit Golden sector system is
asserted.

The audit also checks the existing representative compatibility:

```lean
goldenTraceOneFifthUnitPowerSectorSystem.rep i
  = goldenToTraceOne (goldenPhi ^ i.val)
```

The generic real system is built from a Dirichlet fundamental unit, whereas the
Golden system is built from `goldenPhi`.  No checked permutation/reindexing
theorem between these systems was found.

## 6. p=5 nonzero-sector obstruction

The specialized theorem

```lean
signedGolden_nonzero_unitSector_false
```

remains available and was audited, but it cannot be applied to
`PrimeTraceOneStrippedIdealPacket` directly.  Its hypotheses refer to
`SignedGoldenRamifierStrippedPacket`, including the specialized `beta.snd`,
the power-split base, and Golden norm identities.

The missing bridge is a checked correspondence that transports a generic p=5
TraceOne residual to a `SignedGoldenRamifierStrippedPacket.beta`, together with
the required identities relating its `adicSplit`, `parent`, `residual`, axis
factorization, second coordinate, and base norm.  The association of the
generic axis `discrAxis 1 = <-1, 2>` with the Golden ramifier
`goldenTau = <2, 1>` also cannot be assumed without a checked theorem.

Accordingly, no generic p=5 nonzero-sector elimination theorem was added.

## 7. p=13 regression

The audit checks:

```text
13 % 4 = 1
signedPrimeParameter 13 = 3
```

Under the explicit hypothesis

```text
classGroupPTorsionFreeAt (TraceOneInt (signedPrimeParameter 13)) 13
```

the generic receiver returns exact `Fin 13` coordinate equations, and the
combined theorem returns the base-norm condition

```text
¬ 13 ∣ Int.natAbs (norm delta).
```

No class-number theorem for `TraceOneInt 3` was introduced, and no sector
index was discarded.

## 8. Packet invariant audit

The API audit pins the current fields:

```text
Q.adicSplit
Q.parent
Q.residual
Q.axis_eq
Q.residual_axis_terminal
Q.residual_coordinate_coprime
Q.residual_norm_pow
```

They suffice for the terminal/base-norm result and the generic coordinate
receiver.  They do not by themselves provide the Golden specialized packet
data required by `signedGolden_nonzero_unitSector_false`.

## 9. Focused builds and axiom audit

The following focused builds passed under Lean 4.34:

```text
lake build DkMath.Lib.NumberTheory.TraceOnePowerLanding
lake build DkMath.NumberTheory.TraceOnePrimeUnitSectors
lake build DkMath.FLT.Prime.PrimeTraceOneConditionalDescent
lake build DkMath.FLT.Prime.PrimeTraceOneFiveSectorClosure
lake build DkMath.FLT.Prime.PrimeTraceOneRealSectorReceiver
lake build DkMathTest.FLT.Prime.PrimeTraceOneRealSectorReceiverApiAudit
lake build DkMathTest.FLT.Prime.PrimeTraceOneRealSectorReceiverAxiomAudit
```

The new theorem axiom audit reports only the standard dependencies
`propext`, `Classical.choice`, and `Quot.sound` as applicable.  No new
`sorry`, `sorryAx`, `admit`, explicit project axiom, or `unsafe` declaration
was added.

## 10. Remaining frontier

The next theorem-shaped target is the generic-to-Golden p=5 stripped-packet
bridge, not a new sector elimination claim.  Until that bridge is checked,
the strongest valid result is the real-sector coordinate receiver together
with the terminal-axis base-norm obstruction.
