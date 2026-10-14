# FLT7TC-005R8 — Receiver-bypass audit via cyclotomic PID / clean Kummer p=7 specialization

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

The attached `instruction-013.md` was treated as the bounded implementation
contract, separately from the user's request. This checkpoint audits the clean
p=7 cyclotomic/PID and generic Kummer surfaces. It does not claim a primitive
contradiction or unconditional FLT7.

## Clean p=7 class-group adapters

The cyclotomic-seven Minkowski proof supplies:

```text
CyclotomicSeven.ringOfIntegers_isPrincipalIdealRing
CyclotomicSeven.classNumber_eq_one
```

The new audit theorem
`CyclotomicSeven.classGroupPTorsionFreeAt_ringOfIntegers_seven` specializes
this to `classGroupPTorsionFreeAt (𝓞 K) 7`. The concrete degree-six carrier
also has the clean adapter
`SevenCyclotomicDegreeSixInt.classGroupPTorsionFreeAt_seven`.

The generic Kummer target is stronger:

```text
CyclotomicClassGroupPTorsionFreeTarget
  = ∀ R n, ∀ a : ClassGroup R, a^n = 1 → a = 1.
```

Therefore p=7 class number one closes only the concrete cyclotomic
specialization, not the repository-wide generic target. No theorem was added
that silently upgrades the specialization to the generic target.

## Unit-normalization boundary

The concrete PID extraction is clean and exact, but its output is:

```text
∃ u, IsUnit u ∧ a = u * generator(I)^n.
```

This is exposed by
`SevenCyclotomicDegreeSixInt.unitMulPowOfSpanEqPow_audit`. The exact missing
statement is the degree-six unit receiver:

```text
∀ u : Ringˣ, ∃ v : Ringˣ, u = v^7.
```

No such theorem is currently constructed. The checked real-cubic theorem
`unit_isSeventhPower_iff_projectiveLog_eq_zero` was not transported to the
degree-six cyclotomic carrier; no real-cubic/degree-six unit-class bridge is
available in this checkpoint.

## Direct PID route

The existing clean theorem `exists_orientedElementLevelPowerWitness` reaches
the old `RamifiedSignedRootRoutingPacket` and gives an exact element equation
with a loaded factor and a seventh-power residual factor. The audit wrapper
`directPid_orientedElementLevelPower_audit` confirms this surface.

This does not bypass the current TraceOne receiver: its input is downstream of
the older signed routing layer, and the existing equation does not imply any
of:

```text
CubicGapSeventhShapeReceiver
compensationCore = c^7
residualRoot = b^7
root = innerRoot^7
False.
```

In particular, principality does not make the associated load/unit a seventh
power. No circular import or old packet was used to manufacture the current
receiver.

## Generic Kummer/provider audit

The following selected theorem surfaces have axiom output limited to
`[propext, Classical.choice, Quot.sound]`:

- p=7 PID and class-group adapters;
- concrete PID unit-bearing extraction;
- `cyclotomicPTorsionAnnihilation_of_classGroupPTorsionFree`;
- clean first-case unit/norm wrappers;
- `triominoNoWieferichBridge_of_provider`.

No `TriominoSquarefreeGNBridgeProvider` was constructed from the p=7 data.
The clean provider route remains conditional. In particular, `GN = s^7` was
not used as a squarefree proof.

The following legacy/default surfaces are explicitly quarantined because their
axiom audits contain `sorryAx`:

```text
triominoCosmicNoPowOnGN_default
cyclotomicNormDescentNonFirstCaseGNPowerReceiver_of_classGroupPTorsionFree
```

## Outcome

**Outcome D — CLEAN KUMMER NEEDS AN UNAVAILABLE PROVIDER; DIRECT PID NEEDS A
NEW UNIT/LINEAR-FACTOR BRIDGE.**

The precise remaining global conditions are:

1. a genuine clean p=7 linear-factor/ramified-load packet starting from
   `CounterexamplePack` or `PrimitiveCounterexampleRamifiedProvenance`, not
   from the downstream signed routing packet;
2. a degree-six unit-class statement sufficient to remove the associated
   unit/load factor, or an explicit proof that its non-seventh-power part is
   confined to the ramified load;
3. alternatively, an inhabited clean squarefree/no-lift GN provider for the
   generic Kummer route.

No equivalence with the current cubic receiver is claimed, because the checked
repository contains no bridge between these remaining conditions.

## Validation

Focused builds completed successfully for:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneCyclotomicPidBypassAudit
lake build DkMathTest.FLT.SevenPrimeTraceOneCyclotomicPidBypassAuditApi
lake build DkMathTest.FLT.SevenPrimeTraceOneCyclotomicPidBypassAuditAxiom
```

The axiom audit shows no `sorryAx` for the new audit/adapters or selected clean
Kummer/PID theorems, and shows `sorryAx` for the two quarantined legacy/default
surfaces above. The public facade was not extended with speculative bypass
APIs. No `sorry`, `admit`, `unsafe`, project `axiom`, or new elliptic-curve
development was added.
