# FLT7 seven-primary terminal route: current status

Updated: 2026-07-24  
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
