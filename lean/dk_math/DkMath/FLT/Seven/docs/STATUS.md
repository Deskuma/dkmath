# FLT7 seven-primary terminal route: current status

Updated: 2026-07-28
Repository: `Deskuma/dkmath`  
Pull request: `#65`  
Base branch: `feature/FLT7-magic-core-260722-v0`  
Work branch: `wip/FLT7-magic-core-260722-WiseWolf`  
Reviewed implementation baseline: `a635593391f4444a4c75d640b784189112ca7b36`

## 1. Purpose of this document

This document is the handoff state for the remaining FLT7 work.

The current branch has already built a large exact local theory around the unique seven-primary terminal cell. The next implementation must continue from the proved packet hierarchy rather than restart from the original Fermat equation.

The central rule is:

```text
Use the current Lean packets as the source of truth.
Do not replace exact quotient, routing, depth, orbit, or scale data with a weaker informal model.
```

## 2. Current mathematical boundary

The current terminal route begins with an actual FLT7 counterexample packet and an away cubic routing packet. At seven-primary depth one it extracts the exact terminal quotient data, freezes one routing board, transports every prime of the terminal cubic-root load back to its unique original routing cell, lifts that cell to its complete prime-power depth, classifies the resulting local solution, and extracts a local weight-`(3,7)` unit scale.

The proved pipeline is:

```text
actual FLT7 counterexample packet
        ↓
away cubic routing packet
        ↓
seven-primary pivot with exponent = 1
        ↓
exact terminal quotient core
        ↓
row-sensitive unit sector over ZMod 7
        ↓
one fixed 3 × 3 coprime routing board
        ↓
unique terminal prime coordinate
        ↓
unique original routing-cell address
        ↓
complete original q-adic cell depth q^e
        ↓
explicit prime-power family and unit orbit
        ↓
column-independent local scale s_q
        ↓
pairwise CRT gluing of two local scales
```

This is a local-to-finite synchronization route. It is not yet an FLT7 contradiction.

## 3. Exact terminal quotient core

The current integer-side terminal object is:

```lean
AwaySevenBaseTerminalQuotientCorePacket
```

It contains the exact data currently available at seven-primary depth one:

```text
p.exponent = 1
base-layer packet
endpoint factor = 7 * carrierUnit
7 ∤ carrierUnit
positive carrierUnit
signed root kernel
endpoint quotient equation
first-order integer quotient identity
cubic-root load quotient identity
```

The packet deliberately stops before terminal exclusion.

The key source module is:

```text
SevenBaseTerminalPacket.lean
```

## 4. Unit-sector and row normal forms

The integer quotient core is joined to the `ZMod 7` first-order unit equation by:

```lean
AwaySevenBaseTerminalUnitSectorPacket
```

The normalized unit sector resolves the terminal row exactly as follows:

```text
row Y   ↔ normalized sign +1
row Z   ↔ normalized sign -1
row Sum ↔ normalized sign -1
```

For each row the packet simultaneously records:

```text
selected endpoint = 7 * carrierUnit
normalized unit sign
the exact cubic-root load quotient
```

The negative `Z` and `Sum` branches also collapse to one weighted endpoint/load identity. These normal forms are proved data and should be reused directly.

## 5. Bare congruence obstruction is insufficient

The theorem:

```lean
sevenBase_rowY_mod49_shadow
```

constructs a checked row-`Y` shadow satisfying the visible primitive, nonvanishing, and mod-`49` congruence conditions.

Therefore the remaining terminal attack must not be designed as a bare mod-`49` contradiction. It must use the exact quotient packet, the complete prime-power information, or a stronger global compatibility condition.

## 6. Fixed routing board and prime ownership

The structure:

```lean
AwaySevenBaseTerminalRoutingPacket
```

freezes one exact `3 × 3` coprime routing board for the terminal quotient core.

This is essential. Later prime arguments must refer to the same board. They must not choose a new routing independently for each prime.

On the fixed board, a prime carried by any of the three terminal row factors occupies exactly one cell in that row and enters exactly one cubic-root-load column. The relevant row factors are:

```text
carrierUnit
row-sensitive unselected endpoint
row-sensitive companion endpoint
```

The unique-cell theorems provide both positive divisibility in one cell and negative divisibility in the other two cells.

## 7. Terminal coordinates and original addresses

The terminal coordinate layer packages the row and column location visible on the fixed terminal board.

The original-address layer then transports that coordinate back to the specialized original routing grid:

```lean
AwaySevenBaseTerminalRoutingPacket.originalPrimeAddressOfCoordinate
```

For every prime `q` dividing the terminal cubic-root load, Lean currently proves the existence of an original specialized address:

```lean
AwaySevenBaseTerminalRoutingPacket.exists_originalPrimeAddress_of_dvd_cubicRootLoad
```

The resulting prime is also proved to satisfy `q ≠ 7`.

## 8. Complete original prime-power depth

The structure:

```lean
AwaySevenBaseTerminalOriginalPrimeDepthPacket
```

contains:

```text
terminal coordinate
terminal prime-cell certificate
original non-seven depth packet
q identity
row projection identity
column projection identity
```

Its modulus is:

$$m_q=q^{e_q}$$

where `e_q` is the complete `q`-adic depth of the unique original routing cell.

The current API proves:

```text
m_q divides the original routing cell
q^(e_q + 1) does not divide the original routing cell
```

Thus the exponent is exact for that original cell, not merely a lower bound.

## 9. Prime-power classification and orbit

Every terminal prime depth is connected to the existing explicit prime-power classification:

```lean
AwaySevenBaseTerminalPrimePowerClassificationPacket
```

The row selects one of the three endpoint forms and the column selects one of:

```text
sevenV
leftCubic
rightCubic
```

Together these give the nine explicit routing families.

The orbit layer then proves that the actual local solution is a weight-`(3,7)` unit scaling of a canonical local model.

Root coordinates have weight `3`; endpoint coordinates have weight `7`:

```text
u ↦ u * s^3
v ↦ v * s^3
y ↦ y * s^7
z ↦ z * s^7
```

## 10. Column-independent local scale projection

The three orbit constructors contain different auxiliary data. The module:

```text
SevenBaseTerminalPrimePowerScaleProjection.lean
```

forgets those constructor-specific fields and retains only the common orbit core:

```lean
structure AwayNonSevenPrimePowerOrbitProjection where
  actual
  model
  scale
  scale_isUnit
  actual_eq
```

The terminal wrapper is:

```lean
AwaySevenBaseTerminalPrimePowerScaleProjectionPacket
```

For each prime `q` dividing the terminal cubic-root load, the theorem:

```lean
AwaySevenBaseTerminalRoutingPacket
  .nonempty_primePowerScaleProjectionPacket_of_dvd_cubicRootLoad
```

produces a local scale:

$$s_q\in\operatorname{ZMod}(q^{e_q})$$

with:

```text
IsUnit s_q
actual = scalePrimePowerSolution model s_q
```

## 11. Pairwise CRT gluing

The latest completed module is:

```text
SevenBaseTerminalPrimePowerPairScaleGluing.lean
```

It defines:

```lean
AwaySevenBaseTerminalPrimePowerPairScaleGluingPacket
```

For two distinct terminal primes `q₁ ≠ q₂`, the exact local moduli are coprime:

$$\gcd(q_1^{e_1},q_2^{e_2})=1$$

The packet contains one combined residue scale:

$$s_{12}\in\operatorname{ZMod}(q_1^{e_1}q_2^{e_2})$$

whose two Chinese-remainder reductions recover the original local scales.

The public existence theorem is:

```lean
AwaySevenBaseTerminalRoutingPacket
  .nonempty_pairScaleGluingPacket_of_dvd_cubicRootLoad
```

This is a proved two-prime synchronization theorem.

## 12. What pairwise CRT does not prove

The pair packet glues only the scale residues.

It does not yet prove any of the following:

```text
all terminal primes are simultaneously glued
product of local moduli equals the complete cubic-root load
the local canonical models are reductions of one global model
the combined scale lifts to one signed integral scale
the local weighted equations reconstruct one integral solution
one terminal row is arithmetically impossible
recursive descent closes
FLT7 follows
```

In particular, each local projection still contains its own `model`. Gluing the `scale` fields does not automatically glue those local models.

This model-compatibility gap is one of the main remaining mathematical boundaries.

## 13. Explicit open obligations

The public facade currently leaves the following obligations open:

1. finite or global simultaneous scale gluing;
2. canonical-model compatibility across prime-power cells;
3. lifted signed reconstruction from local residue data;
4. terminal arithmetic exclusion;
5. unconditional away-depth descent closure;
6. recursive closure;
7. the final FLT7 contradiction.

The existing strict away-depth drop still depends on an explicit:

```lean
AwayDescentClosureProvider
```

No new implementation should silently assume this provider.

## 14. Current implementation policy

Codex should preserve the following rules.

```text
Keep checkpoints small.
Reuse existing packet fields and theorem names.
Do not weaken exact depth to mere divisibility.
Do not choose a fresh routing per prime.
Separate residue synchronization from integral reconstruction.
Separate scale compatibility from model compatibility.
Do not claim terminal exclusion until an exact contradiction is proved.
Do not claim recursive closure or FLT7 from a finite CRT packet alone.
```

## 15. Immediate starting point for Codex

Start from:

```text
SevenBaseTerminalPrimePowerScaleProjection.lean
SevenBaseTerminalPrimePowerPairScaleGluing.lean
```

The immediate next question is:

```text
Can the two-prime scale packet be extended to the finite support of the
terminal cubic-root load while preserving exact reductions and without
silently assuming compatibility of the local canonical models?
```

The accompanying `ROADMAP.md` and `IMPLEMENTATION_DESIGN.md` specify the staged implementation.

## 16. TERM-004--006 implementation state

The terminal route now reaches three further checked layers.

```text
TERM-004
  global universal coordinate equations
  exact signed integer equation carries

TERM-005
  3 x 3 cell prime-support partition
  exact reconstruction of every cell modulus

TERM-006
  reduction of the global CRT candidate to every exact cell modulus
  row-resolved coordinate and equation carries
  explicit final fixed-system compatibility obligation
```

The global model satisfies both universal seventh-power/cyclotomic coordinate
equations.  Homogeneity gives the same scale weight `21` on both sides, so the
unit combined scale can be cancelled.  Signed representatives then give exact
integer multiples of the full modulus for both equation defects.

For every cell coordinate, the product of all supported exact prime powers in
that fiber is proved equal to the original routing cell.  The full CRT model,
scale, weighted coordinates, and universal equations therefore reduce to each
of the nine exact cell quotients.

The remaining gap is deliberately stronger than mere local solubility:

```lean
AwaySevenBaseTerminalCellwiseFixedSystemObligation candidate
```

requires, for every cell, a solution of its fixed endpoint-row/root-column
prime-power system whose forgotten four coordinates are exactly the reduced
global CRT model.  Existing APIs prove the universal equations after reduction
and prove the fixed system at each individual prime power, but do not yet glue
all certificates in one cell while preserving this coordinate equality.

Consequently no terminal contradiction and no
`AwayDescentClosureProvider` is currently constructed.  The public
`AwaySevenBaseTerminalCarryDecision` records the honest three-way boundary:
contradiction, descent provider, or the concrete carry packet plus this exact
open obligation.

## 17. TERM-007 fixed cell-system closure

`AwaySevenBaseTerminalCellwiseFixedSystemObligation` is now proved
unconditionally.

```lean
candidate.cellwiseFixedSystemObligation
```

The proof does not rebuild a second CRT inside each cell.  It uses the fact
that `AwayRoutingPrimePowerSolution M row column` accepts an arbitrary natural
modulus `M`.

For each whole routing cell:

```text
routing cell divides its original endpoint factor
routing cell divides its terminal root-column factor
  ↓
original weighted coordinates form a fixed row/column solution
  ↓
universal first equation decodes to the matching one of nine local equations
  ↓
inverse action of the cell unit scale
  ↓
the reduced cell model itself is a fixed-system solution
```

The decoder is:

```lean
AwayFirstCoordinatePrimePowerEquation.of_universal
```

It derives all nine first-coordinate branches from the endpoint equation, root
equation, and universal first coordinate equation using the exact left/right
cubic division identities.

TERM-007 closes the model-compatibility obligation only.  The remaining
terminal problem is now genuinely integral: use the nine proved fixed-system
solutions together with coordinate windings, equation carries, and row modulus
factorization to produce either a contradiction or an
`AwayDescentClosureProvider`.

## 18. TERM-008 cell-carry dependency audit

The full-modulus signed representatives are now reused, without choosing new
representatives in each cell:

```lean
signed.signedModel_cast_cell coordinate
```

For every one of the nine fixed row/column cells, Lean constructs exact
endpoint, root, and first-coordinate integer carries in
`AwaySevenBaseTerminalCellIntegerCarryPacket`.  The underlying polynomial
identity is exposed independently as:

```lean
fixedFirstResidual_decomposition
```

It writes the fixed first-coordinate residual as an explicit integer linear
combination of the universal first residual, the endpoint residual, and the
root residual.  After substituting the corresponding carry equations and the
factorization of the full modulus by the cell modulus, cancellation gives:

```lean
AwaySevenBaseTerminalCellIntegerCarryPacket.firstCarry_eq
```

Thus TERM-008 has Outcome A in the sense predicted by its design document:
the first-coordinate carry of every cell is completely determined by the
global universal first carry and that cell's endpoint and root carries.  The
nine first-coordinate carries add no independent arithmetic constraint.

The packaged audit is:

```lean
signed.cellCarryDependencyAuditPacket
```

This closes the first-carry route, not the terminal theorem.  The independent
data still available for descent are the endpoint/root carries, the exact
cell and full-modulus factorization, unit/nondegeneracy hypotheses, and their
common origin in the canonical composite orbit.  No terminal contradiction
and no `AwayDescentClosureProvider` has been constructed.

## 19. DESCENT-001 provider-construction boundary

The provider construction now factors through the exact integral seed:

```lean
AwayDescentReconstructionSeed p
```

The seed contains new natural coordinates, a new away coordinate normal form
(hence a positive primitive exponent-seven `CounterexamplePack`), and proof
that the old `|root.snd|` is its exceptional endpoint carrier.

From this data Lean constructs the complete next valuation-transfer packet and
the original recursive provider:

```lean
AwayDescentReconstructionSeed.nextRoute
AwayDescentReconstructionSeed.toClosureProvider
```

The reverse conversion is also implemented. The theorem:

```lean
nonempty_descentReconstructionSeed_iff_closureProvider
```

proves that the seed is exactly equivalent to the existing provider contract.
It immediately gives the strict seven-adic depth decrease through
`away_depth_descent_of_reconstructionSeed`.

The current unconditional result is packaged by
`signed.descentDecisionOpen`. It retains the complete TERM-008 carry audit and
records `Nonempty (AwayDescentReconstructionSeed r.cubic.transfer)` as the
remaining obligation. A supplied seed closes the decision through
`signed.descentDecisionOfSeed`.

DESCENT-001 therefore has Outcome C, not an unconditional closure result.
Neither the composite local solutions nor their carry identities construct a
new natural Fermat triple. The remaining theorem must reconstruct a positive
primitive `CounterexamplePack` whose away exceptional carrier is the old
root-second-coordinate absolute value. No such seed, provider, recursive
descent closure, or FLT7 contradiction is currently proved.

## 20. DESCENT-002 terminal seed exclusion

The attempt to inhabit the reconstruction seed at the terminal layer has a
definitive negative result.

For any pivot packet and any seed targeting its old root second coordinate:

```lean
AwayDescentReconstructionSeed.two_le_pivotExponent
```

proves `2 ≤ p.exponent`. The reason is exact:

```text
new AwayValuationTransferPacket
  → new exceptional carrier has seven-adic depth at least 1
carrier_match
  → new carrier = old |root.snd|
old pivot depth equation
  → valuation(old |root.snd|) = p.exponent - 1
```

The same condition is exported directly for
`AwayDescentClosureProvider.two_le_pivotExponent`.

Therefore terminal depth one gives:

```lean
no_descentReconstructionSeed_of_exponent_eq_one
no_descentClosureProvider_of_exponent_eq_one
```

For the DESCENT-001 open packet, Lean also proves:

```lean
AwaySevenBaseTerminalDescentOpenPacket.not_reconstructionObligation
```

Thus DESCENT-002 has Outcome D: the requested terminal seed cannot be
inhabited. This does not yet contradict the original terminal
`CounterexamplePack`; it proves that recursive descent is unavailable from
this branch. The route must return to direct terminal arithmetic exclusion.
The seed/provider construction problem remains open only for lifted pivots
with `1 < p.exponent`.

## 21. TERM-009 terminal Fermat chart resolution

TERM-009 implements and checks the coordinate-chart reconstruction in
`SevenBaseTerminalFermatChartResolution.lean`.

The natural exchange API

```lean
CounterexamplePack.swapXY
```

preserves positivity, primitivity, and the Fermat-seven equation.  It gives
the following two unconditional terminal results:

```lean
AwaySevenBaseTerminalRowYProfile.to_swapped_ramified
AwaySevenBaseTerminalRowSumProfile.false_of_swapped_away
```

For Row Y, the mod-seven Fermat equation makes the exchanged gap `z - x`
divisible by seven, so the existing coordinate route must be ramified.  For
Row Sum, the exact residue sector is `awaySum`; after exchange, `x`, `z`, and
`x + z` are all seven-units while every away chart requires
`7 ∣ x * z * (x + z)`, a contradiction.

For Row Z, Lean verifies the signed odd-power transport:

```lean
CounterexamplePack.signedOddPermutation
AwaySevenBaseTerminalRowZProfile.seven_dvd_signed_gap
```

Thus `(z,-y,x)` is a nonzero primitive integer Fermat-seven chart and its gap
`x - (-y)` is divisible by seven.  The complete terminal decision is:

```lean
AwaySevenBaseTerminalUnitSectorPacket.fermatChartResolution
```

Its only constructors are a natural Row-Y ramified packet and a signed Row-Z
packet.  Row Sum has been eliminated.

The attempted thin reuse of the natural ramified extractor stops at a genuine
domain boundary.  The existing construction proceeds through natural
subtraction and `GN`, positivity, natural coprime factor splitting, and
`padicValNat` before building `SevenQuadraticResidualPacket`; it cannot accept
the negative endpoint `-y`.  TERM-009 records the exact missing conclusion as:

```lean
AwaySevenBaseTerminalRowZSignedRamifiedArithmeticObligation
```

and proves that this receiver constructs
`SignedRamifiedCoordinateNormalForm`.  TERM-009 therefore has Outcome C:
terminal chart resolution is complete, Row Sum is excluded, and signed
Row-Z quadratic seventh-power extraction is the sole remaining direct
arithmetic obligation.  This does not close the natural ramified summit or
prove FLT7.

## 22. TERM-010 Row-Z alternating cyclotomic extraction

TERM-010 closes the arithmetic receiver isolated by TERM-009.

`SevenBaseTerminalRowZAlternatingPowerSplit.lean` defines

```lean
alternatingCyclotomicSeven x y = (x ^ 7 + y ^ 7) / (x + y)
```

and proves its exact factorization and signed cyclotomic interpretation:

```lean
add_mul_alternatingCyclotomicSeven
alternatingCyclotomicSeven_intCast
```

For primitive endpoints its gcd with `x + y` divides seven; on the Row-Z
channel it is exactly seven.  The signed terminal-core theorem excludes a
second factor of seven.  The normalized coprime product argument then
constructs:

```lean
AwaySevenBaseTerminalRowZAlternatingPowerSplit
```

with exact fields

```text
x + y = 7^6 * a^7
alternatingCyclotomicSeven x y = 7 * b^7
z = 7 * a * b
```

`SevenBaseTerminalRowZSignedResidualCore.lean` proves the signed cubic
coordinate pair is coprime, applies `exists_cyclotomicSeven_terminal_core`,
and identifies the peeled residual norm with `b^7`.  The residual and its
conjugate have unit gcd, so the existing TraceOne UFD theorem produces a root
whose seventh power is the residual core.

The TERM-009 receiver is now inhabited by:

```lean
AwaySevenBaseTerminalRowZProfile.signedRamifiedArithmeticObligation
```

and the complete signed normal form is:

```lean
AwaySevenBaseTerminalRowZProfile.signedRamified
```

Finally,

```lean
AwaySevenBaseTerminalUnitSectorPacket.ramifiedChartResolution
```

states that every surviving terminal away packet reaches either the natural
Row-Y ramified chart or the signed Row-Z ramified chart.  Row Sum remains
impossible.

TERM-010 has Outcome A.  It does not prove a contradiction in either
ramified chart.  The common ramified summit is the next independent proof
boundary.

## 23. RAMIFIED-001 common summit and exact second-coordinate depth

`SevenBaseTerminalRamifiedSummit.lean` defines
`PrimitiveRamifiedSummitPacket` and constructs it from both surviving
terminal rows:

```lean
AwaySevenBaseTerminalRowYProfile.ramifiedSummit
AwaySevenBaseTerminalRowZProfile.ramifiedSummit
AwaySevenBaseTerminalUnitSectorPacket.ramifiedSummit
```

The common packet retains the primitive integer endpoints, Fermat equation,
exact `7^6` gap split, exact cyclotomic residual split, distinguished factor,
quadratic coordinate equation, root norm, and the needed seven-unit facts.

`SevenBaseTerminalRamifiedDepth.lean` proves the predicted gap quotient
identity and exact transfer:

```lean
PrimitiveRamifiedSummitPacket.rootSnd_padicValNat
```

```text
padicValNat 7 (Int.natAbs root.snd)
  = 5 + 7 * padicValNat 7 gapRoot
```

The second coordinate also splits as `ramifiedLinear * ramifiedLeftCubic *
ramifiedRightCubic`; its cubic sum and difference identities and the common
endpoint-product equation are exported.

RAMIFIED-001 has Outcome A.  The common summit and its exact depth invariant
are closed, but no smaller Fermat solution or recursive descent is claimed.

## 24. RAMIFIED-002 formal coprime routing and gap synchronization

`SevenBaseTerminalRamifiedRouting.lean` strengthens the common summit with
the endpoint nonvanishing and cyclotomic-coordinate coprimality needed to
recover primitive root coordinates.  It proves:

```lean
PrimitiveRamifiedSummitPacket.root_coordinates_isCoprime
PrimitiveRamifiedSummitPacket.coprime_linear_left
PrimitiveRamifiedSummitPacket.coprime_linear_right
PrimitiveRamifiedSummitPacket.coprime_left_right
```

All endpoint and root factors are nonzero.  Both triples are pairwise
coprime, their `natAbs` products agree, and therefore:

```lean
RamifiedCubicRoutingPacket
AwaySevenBaseTerminalUnitSectorPacket.ramifiedCubicRouting
```

inhabit the existing formal `CoprimeTripleRouting` grid.

The exact depth calculations give:

```lean
PrimitiveRamifiedSummitPacket.cubicGap_padicValNat
PrimitiveRamifiedSummitPacket.endpointGap_padicValNat
PrimitiveRamifiedSummitPacket.cubicGap_depth_eq_endpointGap_depth
```

Both gaps have depth `6 + 7 * padicValNat 7 gapRoot`.  RAMIFIED-002 has
Outcome A.  No smaller Fermat solution or descent provider is constructed.

## 25. RAMIFIED-003 exact ramified gap-unit bridge

`SevenBaseTerminalRamifiedGapUnitBridge.lean` proves the division-free
integer identity:

```text
(R - L) * seventhPowerSndCore
  = (endpointLeft - endpointRight) * ramifiedGapQuotient.snd * norm(root)
```

The three bridge factors other than the gaps are proved to be seven-units and
are packaged by:

```lean
RamifiedGapUnitBridgePacket
PrimitiveRamifiedSummitPacket.ramifiedGapUnitBridge
```

For every natural `k`, including `k = 0`, the packet exports an explicit unit
and the exact equality:

```lean
cubicGap = endpointGap * explicitUnit  in ZMod (7^k)
```

RAMIFIED-003 has Outcome A.  This is an exact local unit equivalence, not a
smaller Fermat solution, reconstruction seed, or descent provider.

## 26. RAMIFIED-004 explicit ramified unit-class audit

`SevenBaseTerminalRamifiedUnitClassAudit.lean` defines the canonical reduction
map:

```lean
sevenPowerReductionHom k :
  ZMod (7^(k+1)) →+* ZMod (7^k)
```

and proves that the explicit bridge units form a coherent tower:

```lean
RamifiedGapUnitBridgePacket.explicitUnit_reduction
```

At the first nontrivial classifying modulus it defines:

```lean
RamifiedGapUnitBridgePacket.IsSeventhPowerMod49
```

For every bridge packet, Lean proves:

```text
IsSeventhPowerMod49
  ↔ U^7 = U
  ↔ U ∈ {1, 18, 19, 30, 31, 48}  in ZMod 49
```

RAMIFIED-004 has Outcome C.  The finite classifier is complete, but the
current common-summit fields do not yet select one of its two branches.
Turning a non-seventh-power branch into contradiction would additionally
require a theorem that the root-cubic gap has seventh-power shape.

## 27. RAMIFIED-005 canonical residual-root class reduction

`SevenBaseTerminalRamifiedResidualRootClass.lean` proves the complete canonical
normalization on the mod-`49` plane:

```text
root.snd = 0
Q = -endpointRight^2
residualRoot = root.fst^2
sndCore = residualRoot^3
explicitUnit = -endpointRight^2 * residualRoot⁻²
```

The inverse in the last display is implemented by the explicit unit witness
`residualRootInverseMod49`.

The first-coordinate ramified expansion additionally gives:

```text
root.fst^7 = -endpointRight^3
residualRoot mod 7 = 1
residualRoot^7 = 1 mod 49
```

Consequently:

```text
residualRoot ∈ {1, 8, 15, 22, 29, 36, 43}

IsSeventhPowerMod49 ↔ residualRoot = 1
```

In the seventh-power branch the canonical explicit unit belongs precisely to
the reduced candidate set `{19, 31, 48}`.

RAMIFIED-005 has Outcome A.  It does not yet construct compatible seventh
roots at every higher `7^k`, an integral seventh root, or a root-cubic
seventh-power-shape receiver.

## 28. RAMIFIED-006 terminal second-coordinate compensation routing

`SevenBaseTerminalRamifiedCompensationRouting.lean` restores the selected
terminal carrier in `TerminalPrimitiveRamifiedSummitPacket` and proves:

```text
carrierUnit = gapRoot * residualRoot
7 ∤ gapRoot
gcd(gapRoot, residualRoot) = 1

v7(|root.snd|) = 5
v7(|endpoint gap|) = 6
v7(|cubic gap|) = 6
```

After cancelling the visible factor seven, Lean fixes the integer equation:

```text
v * sndCore = 7^5 * gapRoot^7 * gapQuotient
```

The polynomial certificate and gcd ledger establish:

```text
gcd(|v|, |sndCore|) = 1
gcd(residualRoot, |v|) = 1
gcd(residualRoot, |sndCore|) = 1
gcd(gapRoot, |endpointRight|) = 1
gcd(gapRoot, |gapQuotient|) = 1
```

Thus `RamifiedSecondCoordinateRoutingPacket` formally supplies the 2 x 3
coprime routing board. The compensation core and remaining receiver are:

```lean
ramifiedCompensationCore = gcd |v| |gapQuotient|

RamifiedCubicGapSeventhShapeReceiver :=
  ∃ w, ramifiedCompensationCore * residualRoot = w^7
```

Lean also proves that if the compensation core is `1`, this receiver forces
`residualRoot = 1` modulo `49`.

RAMIFIED-006 had Outcome C at its last normalization step. The terminal depth
collapse, integer equation, gcd ledger, routing board, and receiver were
complete; RAMIFIED-007 discharges that precise normalization obligation.

## 29. RAMIFIED-007 canonical routing split

`CoprimeTripleRouting.lean` now exposes all nine canonical cell equations

```text
cᵢⱼ = gcd(source-leftᵢ, source-rightⱼ).
```

The API explicitly requires pairwise coprimality of both source columns;
the routing product equations alone do not imply these equalities.

`SevenBaseTerminalRamifiedCanonicalSplit.lean` applies that API to the
terminal second-coordinate board and constructs witnesses satisfying:

```text
gapRoot = X * Y
|v| = 7^5 * X^7 * C
sndCore = Y^7 * D
|gapQuotient| = C * D
C = gcd(|v|, |gapQuotient|)
```

Together with the existing ramified cubic identity this gives:

```text
|R - L| = 7^6 * X^7 * (C * residualRoot).
```

Lean proves the exact equivalences

```text
RamifiedCubicGapSeventhShapeReceiver
  ↔ ∃ w, |R-L| = 7^6 * (X*w)^7
  ↔ (∃ c, C = c^7) ∧ (∃ b, residualRoot = b^7).
```

RAMIFIED-007 has Outcome A. The routing normalization and advertised
cubic-gap factor display are complete. It does not prove that `gapRoot`
itself has an internal seventh root, construct a smaller Fermat solution, or
close descent. Root-internal extraction begins only at RAMIFIED-008.

## 30. RAMIFIED-008 receiver-induced quadratic inner root

`SevenBaseTerminalRamifiedQuadraticInnerRoot.lean` first proves that the
primitive, seven-unit-norm summit root is coprime to its conjugate:

```text
IsUnit (gcd root (conj root)).
```

On the receiver branch, RAMIFIED-007 supplies
`compensationCore = c^7` and `residualRoot = b^7`. The latter is the norm key,
so the coprime-product extractor constructs an inner quadratic integer
`gamma` with:

```text
root = gamma^7
norm gamma = b
gcd(gamma.fst, gamma.snd) = 1

cyclotomicSevenToTraceOne(endpointLeft, endpointRight)
  = sevenAxis * gamma^49.
```

Lean then transfers the outer depth-five second-coordinate equation through
`root = gamma^7` and proves:

```text
v7(|gamma.snd|) = 4

|gamma.snd| = 7^4 * M^7
|seventhPowerSndCore(gamma)| = N^7.
```

The core factorization is also separated, including signs:

```text
seventhPowerSndLeftCubic(gamma) = l^7
seventhPowerSndRightCubic(gamma) = r^7
```

for some integers `l` and `r`.

RAMIFIED-008 has Outcome A for the receiver branch. It is a strict internal
quadratic depth drop, not yet a descent of Fermat counterexamples. The
receiver remains a branch hypothesis; its failure is still the explicit
residual/compensation obstruction from RAMIFIED-007. Inverse cyclotomic
reconstruction and the real-cubic norm interpretation remain open.
