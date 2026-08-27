# FLT7-018 — Base seven-layer quotient system and terminal arithmetic audit

Work on branch:

```text
feature/FLT7-magic-core-260722-v0
```

Use the current branch HEAD after completed FLT7-017.

## Status to preserve

- FLT7-015 remains Outcome C: generic prime-address uniqueness for arbitrary
  `CoprimeTripleRouting` is false. Preserve the diagonal counterexample.
- FLT7-015R proves specialized address uniqueness and exact valuation isolation.
- FLT7-015P and FLT7-016 completely classify every non-seven addressed cell at
  its full `q^e` depth as a weight-(3,7) unit orbit.
- FLT7-017 completely classifies the unique seven-primary pivot at depth
  `k = 1 + v7(vPart)`, including the signed ramified kernel and the honest
  terminal/lifted audit boundary.
- Do not reopen those completed local classifications.

## Central boundary

This checkpoint concerns only the terminal seven layer

```text
k = 1.
```

Then:

```text
v7(pivot) = v7(carrier) = 1,
v7(vPart) = 0.
```

Thus the addressed endpoint factor is exactly `7 * unit`, while the root second
coordinate is seven-adically a unit. A depth-zero next away packet must not be
fabricated.

The mod-7 base sector alone is not expected to contain the terminal
contradiction. The next information is the first-order quotient obtained by
**dividing exact integer identities by the single visible factor 7 before
reducing modulo 7**.

Never cancel `7` inside `ZMod 49`; it is a zero divisor there.

## Objective

Construct a stable terminal quotient packet from an actual
`AwaySevenBaseLayerPacket` and its source `CounterexamplePack`.

The packet must preserve:

1. the selected pivot row;
2. the endpoint carrier divided exactly once by seven;
3. the fact that this quotient is not divisible by seven;
4. the signed root second-coordinate unit;
5. the exact residual quotient of `seventhPowerFst`;
6. the exact row-specific endpoint quotient identity;
7. the quotient of the cubic load product;
8. the resulting first-order congruence modulo seven.

Then determine whether these exact quotient constraints exclude all three base
sectors. If not, isolate the smallest additional global integer statement still
missing.

## New modules and tests

Create:

```text
DkMath/FLT/Seven/SevenBaseLayerQuotient.lean
DkMath/FLT/Seven/SevenBaseTerminalAudit.lean
DkMathTest/FLT/SevenSevenBaseLayerQuotient.lean
DkMathTest/FLT/SevenSevenBaseTerminalAudit.lean
```

Update:

```text
DkMath/FLT/Seven.lean
```

Create report:

```text
docs/feature/FLT7-magic-core-260722/report-flt7-018.md
```

Suggested import:

```lean
import DkMath.FLT.Seven.SevenPivotDescentAudit
```

Use namespace:

```lean
namespace DkMath.FLT.Seven
```

# Part A — Exact terminal carrier quotient

For a base packet `p` with `p.exponent = 1`, define the selected natural endpoint
factor:

```text
row Y:    y
row Z:    z
row Sum:  y + z.
```

Construct a positive quotient `carrierUnit : Nat` satisfying:

```text
endpointRoutingFactorNat y z p.row = 7 * carrierUnit,
not (7 divides carrierUnit).
```

Do not define this only by `Nat / 7` and leave its exactness implicit. Package the
multiplication equality and nondivisibility proof.

Suggested structure:

```lean
structure AwaySevenBaseCarrierQuotient ... where
  carrierUnit : Nat
  carrier_eq : endpointRoutingFactorNat y z p.row = 7 * carrierUnit
  carrierUnit_pos : 0 < carrierUnit
  seven_not_dvd_carrierUnit : not 7 ∣ carrierUnit
```

Use exact valuation `1`, positivity, and standard `padicValNat` extraction APIs.

# Part B — Signed root unit at the base layer

Specialize `AwaySevenRamifiedKernelPacket` at `k = 1` and expose:

```text
root.snd = unitPart,
not (7 : Int) divides unitPart.
```

Preserve the sign. Do not replace this by `natAbs` alone.

# Part C — Exact residual quotient

From the existing identity prove the exact factorization:

```text
seventhPowerFst u v - (u^7 + 4*v^7)
  = 7 * (-2*v^2*(u+v)*sevenRamifiedResidualPolynomial u v).
```

Name the quotient polynomial, for example:

```lean
def sevenRamifiedResidualQuotient (u v : Int) : Int :=
  -2*v^2*(u+v)*sevenRamifiedResidualPolynomial u v
```

and prove a stable exact theorem, not merely divisibility.

# Part D — Row-specific endpoint quotient identities

Let `A = cyclotomicSevenFst z y`.

Using the exact terminal carrier quotient, prove:

```text
row Y, y = 7*c:
  A - z^3 = 7 * (c * (z-y) * (z+y)).

row Z, z = 7*c:
  A + y^3 = 7 * (c * z * (z+y)).

row Sum, y+z = 7*c:
  A + y^3 = 7 * (c * z^2).
```

All equalities are in `Int`. Keep signs explicit.

# Part E — First-order terminal equation

Use `normal.fst_eq : A = seventhPowerFst u v` and Parts C-D.

Define the exact integer quotient of the core equation:

```text
row Y:
  (u^7 + 4*v^7 - z^3) / 7

row Z/Sum:
  (u^7 + 4*v^7 + y^3) / 7.
```

Prefer a witness/equality formulation over integer division if that gives a
cleaner theorem.

Prove that the quotient equals:

```text
endpointQuotient - sevenRamifiedResidualQuotient u v.
```

Reduce this exact equality modulo seven to obtain the stable first-order base
system.

The theorem must retain enough provenance to distinguish the three rows.

# Part F — Quotient of the cubic load

Use `r.cubic.product_eq` and the exact row carrier equality to cancel the visible
factor seven in `Nat`, where cancellation is valid.

Prove row-specific quotient product equalities. Schematically:

```text
carrierUnit * the two nonaddressed endpoint factors
  = vPart * leftPart * rightPart.
```

Do not lose the correspondence to the routing row or the signed root kernel.
Expose both the natural absolute-value equality and any signed equality already
available from the existing normal form.

# Part G — Terminal quotient packet

Package Parts A-F, the base residue sector, root-linear nonvanishing, endpoint
coprimality, root-factor coprimality, and the actual source counterexample.

Suggested surface:

```lean
structure AwaySevenBaseTerminalQuotientPacket
    (source : CounterexamplePack x y z)
    (routing : AwayCubicRoutingPacket x y z)
    (pivot : AwaySevenPivotDepthPacket routing) : Type where
  depth_eq_one : pivot.exponent = 1
  baseLayer : AwaySevenBaseLayerPacket pivot
  carrier : AwaySevenBaseCarrierQuotient ...
  kernel : AwaySevenRamifiedKernelPacket pivot
  residual_quotient_eq : ...
  endpoint_quotient_eq : ...
  first_order_eq_mod_seven : ...
  load_quotient_eq : ...
```

Construct it from every terminal-open branch of FLT7-017.

# Part H — Reject a false naive mod-49 obstruction

Before claiming terminal exclusion from one-step congruences alone, test the
following row-Y residue candidate in the exact formulas modulo 49:

```text
u = -24,
v = -24,
y = 7,
z = 40.
```

Verify or refute, in Lean, the following candidate properties:

```text
y has exact seven-adic depth 1 modulo 49,
z and y+z are units modulo 7,
v is a unit modulo 7,
u + 4*v is a unit modulo 7,
left and right cubic factors are nonzero modulo 7,
cyclotomicSevenFst z y = seventhPowerFst u v modulo 49,
y*z*(y+z) = 7*|v|*|P(u,v)|*|Q(u,v)| modulo 49.
```

This is only a residue-shadow regression candidate, not an integral
`CounterexamplePack`.

- If it verifies, preserve it as a permanent test showing that the naive mod-49
  shadow alone cannot prove terminal exclusion.
- If it fails, record exactly which property fails and search for the correct
  smallest shadow witness before asserting a universal mod-49 theorem.

Do not use `native_decide`.

# Part I — Terminal arithmetic attack

Using the full quotient packet, attempt the actual terminal exclusion:

```lean
¬ Nonempty (CounterexamplePack x y z)
```

for all three pivot rows.

Attack order:

1. classify the first-order quotient system over `ZMod 7`;
2. combine it with the quotient load equality;
3. use pairwise coprimality and unique prime ownership from the specialized
   routing packet;
4. substitute the signed root unit and normalized cubic data;
5. identify incompatible exponent ownership, sign, or primitive-factor data;
6. if no contradiction appears, isolate the exact additional integer theorem
   needed, rather than adding another weak local congruence layer.

Finite computation may be used to reject false conjectures, but surviving facts
must be kernel-checked Lean theorems.

# Part J — Honest terminal audit result

Define an audit type with honest outcomes, for example:

```lean
inductive AwaySevenBaseTerminalAuditResult ...
  | excluded (refutation : not Nonempty (CounterexamplePack x y z))
  | quotientOpen
      (packet : AwaySevenBaseTerminalQuotientPacket ...)
      (missing : exact remaining proposition)
```

If terminal exclusion is proved, connect it back to
`AwaySevenTerminalExclusionStatement` and close the `terminalOpen` branch.

If not, replace the current generic placeholder by the exact smallest missing
arithmetic proposition exposed by the quotient analysis.

# Summit

Update the FLT7 summit route so that the base branch carries the new terminal
audit result. Preserve:

```text
- complete non-seven unit-orbit classification,
- complete seven-pivot full-depth solution,
- lifted branch data,
- the generic diagonal counterexample.
```

Do not modify the lifted reconstruction obligation in this checkpoint.

# Required tests

Include:

1. all three carrier quotient rows;
2. exact depth-one quotient and nondivisibility;
3. signed base kernel specialization;
4. exact residual quotient identity;
5. all three endpoint quotient identities;
6. all three first-order equations;
7. all three load quotient equalities;
8. the mod-49 shadow candidate audit;
9. terminal excluded/open constructors;
10. summit route;
11. public axiom audit.

# Non-goals

Do not:

- reopen non-seven local/orbit classification;
- construct a depth-zero away packet;
- cancel seven inside `ZMod 49`;
- assume a mod-49 contradiction without a checked theorem;
- replace signed data by absolute values when signs matter;
- modify the lifted reconstruction obligation;
- claim recursive descent or FLT7 unless the terminal branch is genuinely
  excluded and the lifted closure provider is also constructed.

# Outcome classification

- Outcome A: all three base sectors are arithmetically excluded and the terminal
  branch is closed.
- Outcome B: the exact quotient packet and first-order classification are
  complete, but one named global integer proposition remains.
- Outcome C: a proposed quotient/local obstruction is false; preserve a concrete
  checked residue or arithmetic counterexample and expose the corrected next
  boundary.

Commit with a focused message and push to the current feature branch.