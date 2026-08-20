# Golden-unit Red Ribbon bridge implementation report

## Scope and baseline

This report closes the Phase G acceptance set in
`CODEX-GOLDEN-UNIT-RED-RIBBON-BRIDGE-DIRECTIVE-260820.md`.  The implementation
started from checkpoint `9d96dcfd1b35ffc5213249f42f4458b001a378eb` and is
confined to the StructuralArithmetic bridge, aggregate, README, and this
report.  The completed FLT5 proof route was not modified.

The inspected source includes the A--F StructuralArithmetic modules and the
golden-order files `GoldenOrder`, `GoldenDivisibility`,
`GoldenCoprimeFactor`, `SignedGoldenFifthPower`, `GoldenFifthPowerCoordinates`,
`SignedGoldenUnitClasses`, `GoldenUnitClassification`,
`SignedGoldenSectorArithmetic`, and `Main`, together with the historical
red-ribbon contract.

## Representation and theorem list

`GoldenUnitBridge.lean` defines the small relation-valued predicate
`GoldenFifthSector i x`.  It records existence of a hidden fifth-power factor
behind the visible representative `goldenPhi ^ i`; it does not select a
canonical `i` and does not assert sector uniqueness.

The public bridge declarations are:

- `goldenUnitFifthClass_iff_exists_sector`, a thin exact unpacking of the
  existing `GoldenUnitFifthClass` predicate;
- `goldenUnit_has_fifthSector`, which consumes the certified
  `goldenUnitFifthClass_of_unit` classification;
- `GoldenFifthSector.mul_fifthPower`, the Red Ribbon absorption law, proved by
  `mul_pow` in the existing commutative golden-order ring;
- `goldenPhiPow_mem_fifthSector`, anchoring every visible representative in
  its named sector with gauge witness `goldenOne`;
- `signedGoldenPacket_has_fifthSector`, which consumes
  `signedGoldenFiniteUnitSectorCore_of_unitClasses goldenUnitClassesModFifth`
  for an actual stripped FLT5 packet.

The golden fifth-power observer is intentionally separate from the natural
prime-exponent period-five projection and from ordinary additive congruence
modulo five.  The common statement is only that complete fifth-power gauge
motion is invisible to the chosen observer.

## Verification

Focused builds completed successfully:

```text
lake build DkMath.NumberTheory.StructuralArithmetic.GoldenUnitBridge
lake build DkMath.NumberTheory.StructuralArithmetic
lake build DkMath.FLT.Five.GoldenUnitClassification
```

`git diff --check` passed, and the new source contains no `sorry`, `admit`,
`axiom`, or `unsafe`.  `#print axioms` on
`goldenUnit_has_fifthSector`, `GoldenFifthSector.mul_fifthPower`, and
`signedGoldenPacket_has_fifthSector` reports only the standard
`propext`, `Classical.choice`, and `Quot.sound` dependencies inherited from
the existing development.  The transitive build warning at
`ZsigmondyCyclotomicResearch.lean:147` is pre-existing.

No quotient-group hierarchy, FLT5 refactor, canonical sector selector, or
uniqueness claim was introduced.  The next gap should be selected from the
remaining A--G integration state rather than by opening a generic quotient
project.
