# FLT7-FUSION-003 cyclic-phase report

Date: 2026-07-30

## Result

FUSION-003C reaches **Outcome C-mu3: both cyclic phase systems are formalized,
but their action-level alignment is still an explicit obligation**.

Lean now proves the routing cycle normal form, its exact squared relation to
the FUSION slope, the order-three real-cubic rotation law, and the
sign-forgetting relative real index. These results compress the remaining
ambiguity to a ternary phase plus the already retained binary orientation.

No source-plane chart, Kummer factor, or descent object is selected.

## 1. Abstract active-board normal form

For an arbitrary active `2 x 3` unit board, the five margins and two cycle
ratios satisfy

```text
kappa12 / kappa23 = (row1 / row2) / column2^3
kappa12^3         = (column1 / column2)^3
kappa23^3         = (column2 / column3)^3.
```

The proofs use the exponent-six theorem for `(ZMod 7)^x`; they do not
enumerate the six units.

Three gauge actions are now explicit:

- a visible ternary cycle twist preserving all margins and multiplying both
  cycle ratios by the same `omega`;
- a hidden ternary row twist preserving both margins and cycles;
- a product-one columnwise binary sign gauge preserving both margins and
  cycles.

Concrete witnesses prove:

```text
margins do not determine cycle phase
margins plus both cycles do not determine the whole unit-shadow board.
```

This is an information-boundary result about reconstruction from the unit
shadow. The exact natural gcd routing itself remains canonical.

## 2. Coherent routing-to-slope bridge

For a coherent `RamifiedFusionRoutingAuditPacket`, Lean combines

```text
quotientRoot = 1 mod 7
innerSnd = 0 mod 7
gapRoot * quotientRoot = a * (a+n) * m^7
```

with the routing margins and proves

```text
kappa12 / kappa23 = |m| / |a|
(kappa12 / kappa23)^2 = tau^2.
```

The first equality is deliberately unsigned because the routing constructor
uses `Int.natAbs`. Squaring removes exactly that sign loss and yields the
signed jet slope `tau = m/a`. No orientation is silently assigned.

## 3. Real-cubic order-three phase

Writing `theta = eisensteinAxis`, Lean proves

```text
rotateEquiv theta = theta^2 + 4*theta = theta*(theta+4).
```

The theta residue is invariant under `rotateEquiv`, while division by the
depth-ten theta factor contributes

```text
thetaResidue(rotatedCore) = 4^10 * thetaResidue(core)
                          = 4 * thetaResidue(core).
```

Applied twice to the paired root gap, the canonical rotation packet records

```text
-2*m, -m, 3*m.
```

These are residual core sectors. They are not yet identified with routing
columns or reconstructed source-plane charts.

## 4. Relative real conjugate-pair index

The sign-forgetting coordinate is implemented as

```text
relativeRealIndex(k) = (k / fusionSlopeUnit)^2
  : SevenTernarySector.
```

Lean proves the exact fibre:

```text
relativeRealIndex(k) = 1
  iff k = fusionSlopeUnit or k = -fusionSlopeUnit.
```

Thus the current data canonically identifies the conjugate pair
`{tau,-tau}`, but not one oriented member.

## 5. Alignment audit and stopping point

Two order-three systems now exist:

1. the visible routing cycle twist on the active unit board;
2. the real-cubic rotation on depth-ten residual cores.

They have compatible cardinality and both are explicit, but no theorem in the
current packet chain says that rotating the algebraic roots induces the
visible cycle twist on the canonical natural routing board. The routing board
is built from gcd/natural-absolute-value data, whereas the rotation acts on
signed cubic roots. Equality of their abstract `mu3` labels would only rename
the three phases; it would not prove that the actions intertwine.

For that reason `RamifiedFusionCyclicPhasePacket` is intentionally not
declared inhabited. Its missing mathematical field is the action-level
comparison:

```text
rotate algebraic roots
  -> recompute the coherent signed routing shadow
  -> prove this equals the visible cyclePhaseTwist orbit
```

The retained Y/Z provenance must then be compared separately with the binary
FUSION sector. Neither comparison follows from the present residue equations.

## 6. Predicted next checkpoint

The narrowest productive continuation is a **rotation-routing naturality
packet**. It should retain the three rotated signed root pairs before
`Int.natAbs`, construct or transport their coherent routing boards, and prove
whether the induced board action is:

- the visible cycle-phase twist;
- the hidden row twist; or
- neither, forcing the full cyclotomic equivariant route.

Only the first alternative permits real-cubic chart reconstruction up to
cyclic rotation. Selection of only `{tau,-tau}` leads instead to a
conjugate-pair-equivariant Kummer packet.

## 7. Excluded claims

This checkpoint does not prove:

- that one routing cycle ratio alone equals `tau`;
- that the real-cubic rotation is already the visible board action;
- that relative real index one distinguishes a signed factor;
- a selected routing cell or cyclotomic factor;
- a primitive reconstructed Fermat chart;
- a strict decrease or descent provider;
- FLT7.
