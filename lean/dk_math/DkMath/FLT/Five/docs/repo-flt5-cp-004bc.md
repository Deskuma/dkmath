# FLT5 cp-004b/c implementation report

## Outcome

- cp-004b recovery: complete.
- cp-004c power split: **Outcome A**.

No descent candidate is constructed at this checkpoint.

## cp-004b

`SignedFiveAdic.lean` was rebuilt as one coherent module. In particular:

- `SignedFiveAdicPacket` is now data-bearing (`Type`).
- `SumGN5` has explicit factorization and positivity theorems.
- both mod-25 residual results are kernel-checked without `native_decide`;
- both orientations produce `residual % 25 = 5` and
  `padicValNat 5 residual = 1`;
- the carrier valuation has shape `4 + 5*m`;
- the public packet constructor is a noncomputable choice from a proved
  `Nonempty` packet, because eliminating a Prop-valued orientation directly
  into a data type is forbidden by Lean.

The cp-004b repair is committed separately as `d08fe86e`.

## cp-004c

`SignedFiveAdicPowerSplit.lean` proves the exact common gcd theorem:

```text
gcd carrier residual = 5.
```

For the difference source this uses
`GN5(g,v) = g*(...) + 5*v^4` and `Coprime g v`. For the sum source it reduces
`SumGN5 u v` modulo `u+v` in `ZMod (u+v)`, substitutes `v=-u`, and obtains the
same exceptional term `5*u^4`.

After dividing the common five layer, the proof establishes:

```text
Coprime carrierCore residualCore
not (5 divides residualCore)
(25*carrierCore)*residualCore = (5*distinguishedCore)^5.
```

Mathlib's coprime fifth-power split then yields positive `a,b` with:

```text
carrier       = 5^4 * a^5
residual      = 5 * b^5
distinguished = 5 * a * b.
```

The public endpoints are:

```text
signedFiveAdicPacket_gcd_eq_five
signedFiveAdicPowerSplit_of_packet
signedFiveAdicPowerSplit_of_normalForm
signedBranchARefuter_of_powerSplitCore
branchB_false_of_powerSplitCore
```

## Verification

The targeted FLT5 module, public tower, and `DkMathTest.FLT.Five.CheckAxioms`
all build. The new declarations use only the expected standard axioms:
`propext`, `Classical.choice`, and `Quot.sound`. There is no `sorryAx`.
