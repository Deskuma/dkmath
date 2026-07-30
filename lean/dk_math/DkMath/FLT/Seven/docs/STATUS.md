# FLT7 seven-primary terminal route: current status

Updated: 2026-07-30
Repository: `Deskuma/dkmath`  
Pull request: `#73`
Base branch: `feature/FLT7-magic-core-260722-v1`
Work branch: `wip/FLT7-fusion-260729`
Reviewed implementation baseline: `a635593391f4444a4c75d640b784189112ca7b36`

FUSION-001B is complete locally. The signed roots are definitionally tied
back to the balanced norm packet, `gapRoot` and `quotientRoot` are coprime,
their canonical `2 × 3` routing board is inhabited, and the coordinate norm
expansion identifies the depth-four coefficient with the same signed
`gapRoot`. FUSION-002 has begun: source-plane return of
a seventh power is reduced exactly to an explicit homogeneous degree-seven
integer equation. Its integral zero-locus classification remains open.

FUSION-002A/B/C and the independent integer-sector part of 002E are now
implemented locally. Integral theta coordinates reconstruct the cubic
integer, both nonconstant coordinates of its seventh power are divided by
seven, and their exact triangular factors have the predicted residues
`A^6`, `-3*A^5`, `A^6`, and `3*A^5` modulo seven. Independently,
`quotientRoot = 1` and `gapRoot = a^2*m` modulo seven are proved.

FUSION-002 exact theta jets are now complete locally. A reusable
division-free step advances `(k,2k)` to `(k+1,2k+2)` and three iterations
produce exact nonzero `(3,6)` cores for both algebraic roots. The paired
packet proves the roots are not in the source plane and identifies the common
projective invariant

```text
tau = m/a = gapRoot/a^3,
left jet = (-tau,-3*tau^2),
right jet = (tau,-3*tau^2).
```

FUSION-003 pre-bridge is now implemented locally. The paired theta-root gap
is connected back to the depth-ten ledger with the exact leading formula

```text
thetaResidue(gapCore) = -2*m.
```

The six-sector address is upgraded to the explicit group equivalence
`(ZMod 7)ˣ ≃ μ₂ × μ₃`; the left and right roots have opposite binary
coordinates and the same ternary coordinate. The signed routing audit proves
its neutral third row is `(1,1,1)`, all six active cells are seven-units,
retains signed margin orientation, and records the two independent
`K_{2,3}` cycle ratios.

The old common summit erased Row-Y/Row-Z provenance. A thin provenance packet
now preserves that label before commonization, without duplicating the summit.
No theorem equating the retained row sign with `tau^3` is claimed: the
required normalized-unit equality is still absent.

FUSION-003C cyclic phase is now implemented locally. The abstract active unit
board satisfies the three cycle/margin normal-form identities. A visible
ternary cycle twist, a hidden ternary row twist, and the columnwise binary
gauge are formalized, with concrete nonuniqueness witnesses proving the exact
information boundary of the unit shadow.

For a coherent routing audit, the normalized equation now gives the stronger
bridge

```text
kappa12 / kappa23 = |m| / |a|
(kappa12 / kappa23)^2 = tau^2.
```

The real-cubic rotation is also explicit:

```text
sigma(theta) = theta*(theta+4)
thetaResidue(rotated depth-ten core) = 4 * thetaResidue(core),
```

and the paired gap supplies the three residues `-2*m`, `-m`, and `3*m`.
Finally,

```text
relativeRealIndex(k) = (k/tau)^2 = 1
  iff k = tau or k = -tau.
```

Thus the conjugate pair `{tau,-tau}` is fixed, but its signed member is not.
The remaining gate is not another scalar identity: it is an action-level
naturality theorem proving how real-cubic rotation transports the canonical
signed routing shadow. Until that comparison is proved, no
`RamifiedFusionCyclicPhasePacket` is claimed inhabited and no factor is
declared distinguished or a seventh power.

FUSION-003D real-pair carrier is now implemented locally. It avoids the
unsupported action comparison and instead factors the signed seventh quotient
into its three real conjugate-pair carriers. Lean proves each carrier has
exact theta depth one, reconstructs the quotient root from the three
theta-unit cores, and derives the positive quotient sector again from that
factor geometry.

The ternary phases `1,4,2` are an explicit `Fin 3` equivalence. The phase
`tau^2` selects the unordered pair `{tau,-tau}`, and both normalized quadratic
jets equal three times the selected core residue. The three axis-unit
differences are global units with norms `-1,-1,1`.

FUSION-003E closes the normalized-core coprimality gap by a direct Bezout
route. Lean proves `IsCoprime (r*l) gapRoot`, maps it into the real cubic
order, proves every pair core coprime to the scalar `r*l`, and then proves
the three cores pairwise coprime from their unit-multiple differences.

The carriers cycle under the cubic Galois automorphism, the cores form the
corresponding unit-twisted orbit, and every core has exact norm
`-quotientRoot`. The pure seventh-power routing column splits cellwise.
The exact remaining gate is now:

```text
quotientRoot is a signed seventh power
  iff
c21 and c22 are natural seventh powers.
```

Conditional on this gate, PID associated-power extraction is complete for
all three cores. The two cells are canonical gcd addresses, but current
provenance does not force their seventh-power status. No oriented factor,
primitive chart, strict decrease, descent provider, or FLT7 theorem is
claimed.

FUSION-003F is now complete locally with Outcome A. Every quotient prime has
a canonical signed-root ratio of exact order seven, hence is `1 mod 14`.
The induced real-pair coordinate defines an explicit residue-field evaluation
which kills the zeroth pair core and does not kill the Eisenstein axis.

The row-two scalar cells are no longer treated as missing seventh powers.
They are mapped into the real cubic PID and allocated by canonical gcd
projections:

```text
load21_i = gcd(c21,C_i)
load22_i = gcd(c22,C_i)
C_i = load21_i*load22_i*D_i.
```

The stripped cores are pairwise coprime and each is a seventh power up to a
unit. Both load families multiply back to their scalar cells up to association
and satisfy complete associated Galois cycles. The sign-preserving norm ledger
is exact:

```text
|norm(load21_i)| = c21
|norm(load22_i)| = c22
c21*c22*|norm(D_i)| = |quotientRoot|.
```

Consequently all `|norm(D_i)|` equal one natural seventh power. Under the old
Branch A hypotheses that `c21,c22` are seventh powers, each individual load
is extracted and absorbed into the residual root, recovering the existing
three-core power split. The unconditional loaded packet itself needs no such
hypotheses.

The first post-checkpoint local refinement is also implemented.
`QuotientPrimeGCDLoadAddress` takes `q | c21` or `q | c22`, reconstructs the
canonical `mu_7` evaluation, and proves that the selected gcd load belongs to
its maximal kernel while the competing coprime load does not. The kernel
contracts to `(q)` in `ℤ` and its residue quotient has cardinality `q`.
Because one load may contain several primes or prime powers, only
`span(load) ≤ kernel` is claimed, not equality.
The kernel multiplicity in that principal ideal is now defined exactly.
The three cyclic real-cubic evaluation kernels split `(q)` completely, which
upgrades the former upper bound to

```text
count = padicValNat q cell.
```

Over the finite support of the addressed load, the product of these exact
kernel powers is the principal load ideal itself.

The direct signed-root chart is now excluded, rather than left as a vague
candidate:

```text
signedRightRoot^7 - signedLeftRoot^7
  = 7^5*gapRoot*quotientRoot
7^6 ∤ signedRightRoot^7 - signedLeftRoot^7.
```

Thus this difference is not an integer seventh power and no
`SignedFermatSevenChart signedRightRoot (-signedLeftRoot) c` exists. This is
Outcome D for that shortcut.

The degree-six orientation layer is now implemented. A concrete quadratic
algebra over `SevenRealCubicInt` has rank six over `ℤ`, explicit conjugate
seventh roots, local evaluations extending every ratio address, and the
factor identity whose conjugate product is `realPairCarrier 0`. The two
oriented evaluation kernels are distinct maximal comaximal primes, with their
common real contraction, rational contraction `(q)`, and quotient cardinality
`q` proved.

The reverse containment is now proved by the explicit quadratic-coordinate
calculation, so the extended common real prime equals the product of the two
conjugate degree-one primes.

NORMAL/N2 is also complete. The canonical finite real-prime support now
selects a degree-six oriented address at every supported rational prime. Each
exact real kernel power maps to the product of the oriented and conjugate
kernel powers at the unchanged `padicValNat` exponent. Distinct pair powers
are comaximal, and their finite product is exactly the principal ideal of the
embedded zeroth load. The public packet is
`DegreeSixOrientedLoadFactorizationPacket`.

ULTRA/U1.1 is complete. `GlobalOrientedPrimeFactorizationPacket` adds an
explicit order-three automorphism of the degree-six carrier above the real
rotation. It sends `zeta` to `zeta^2`, commutes with quadratic conjugation,
cycles all six phase-indexed primes, and preserves their exact real
contractions and fibre powers. The finite factor product at each phase is
exactly the principal ideal of the corresponding Galois-positioned load.

ULTRA/U1.2 is complete.  The concrete degree-six carrier has a proved
integral-domain instance.  Its ramified prime above seven is explicitly the
span of `1-zeta`; both linear carriers lie in that prime but not its square.
For every rational prime in the full `quotientRoot` support, the oriented or
conjugate carrier lies in the selected kernel power exactly through exponent
`padicValNat q |quotientRoot|`, while the competing orientation is excluded.
The complete ramified-times-unramified factor ideals satisfy

```text
globalOrientedCarrierFactorIdeal
  = span {cyclotomicDegreeSixCarrier}
globalConjugateCarrierFactorIdeal
  = span {cyclotomicDegreeSixCarrierConj}.
```

ULTRA/U1.3 is complete.  The natural identity

```text
|quotientRoot| = c21*c22*row2ResidualNormRoot^7
```

is transported prime by prime to the full oriented support.  The two
routed-load support products are proved equal to their zero-extended
full-support products.  Defining the residual oriented and conjugate halves
with exponent `padicValNat q row2ResidualNormRoot`, Lean obtains

```text
span {carrier}
  = globalOrientedLoadedCarrierIdeal
      * globalOrientedResidualIdeal^7
span {conjugateCarrier}
  = globalConjugateLoadedCarrierIdeal
      * globalConjugateResidualIdeal^7.
```

Quadratic conjugation exchanges the loaded and residual halves.

ULTRA/U1.4 is complete.  The abstract seventh cyclotomic ring of integers is
proved principal by an explicit Minkowski class-bound calculation.  The
concrete carrier is generated over `ℤ` by `zeta`, giving a surjective algebra
map from that abstract ring of integers and hence a concrete
`IsPrincipalIdealRing` instance.  Choosing generators in the two U1.3 ideal
identities and absorbing the associated unit into the loaded generator gives

```text
carrier = orientedLoadElement * orientedResidualRoot^7
conjugateCarrier = star(orientedLoadElement)
  * star(orientedResidualRoot)^7.
```

All four generator ideals retain their exact U1.3 provenance.  No unit is
assumed to be a seventh power.

ULTRA/U1.5 is complete with Outcome C.  The actual U1.4 equation gives the
six sparse integral coordinate equalities and the exact integral norm ledger,
but no additive Fermat identity.  The six Galois phases collapse to that norm,
each coordinate projection is nonmultiplicative, and there is no unital ring
homomorphism from the concrete carrier to `ℤ`.  The visible signed-root chart
is already impossible at exact seven-adic depth five.

The chosen residual generator is also not coordinate-canonical:
`orientedResidualRoot` and `zeta*orientedResidualRoot` generate the same
ideal, have the same seventh power, and satisfy the same loaded carrier
equation, but their complete integer-coordinate vectors differ.  Thus the
active U1.6 frontier begins without a primitive additive chart.  A sound
continuation needs a `mu_7`-invariant extractor or an extra phase
normalization, plus an independent additive identity, before any strict
global decrease can be formulated from these witnesses.

ULTRA/U1.6 is complete with Outcome C.  Independently of an additive chart,
the inherited ramified extraction already proves that the internal quadratic
root carrier has seven-adic depth four while the preceding summit carrier has
depth five.  The strict depth inequality is unconditional.

The exact missing receiver is
`InternalDepthFourCounterexampleReconstructionObligation`: it asks for an
actual `AwayValuationTransferPacket` whose exceptional carrier is the
depth-four coordinate.  Lean proves this obligation equivalent to the same
data plus the strict comparison and extracts the packet's positive primitive
natural counterexample conditionally.  No inhabitant is constructed.
Furthermore this is not `AwayDescentClosureProvider` or recursive closure:
an indexed transition identifying successive values of one well-founded
counterexample measure is still absent.  ULTRA/U1 therefore ends without a
primitive additive chart, descent closure, terminal contradiction, or FLT7.

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

## 31. RAMIFIED-009 discriminant-49 real-cubic norm carrier

`SevenRealCubicInt.lean` defines integral coordinates
`a + b*alpha + c*alpha^2` with:

```text
alpha^3 = 2*alpha^2 + alpha - 1.
```

The coordinate multiplication is proved to form a commutative ring. Its
explicit determinant norm is multiplicative and satisfies:

```text
Norm(a - alpha*n) = leftCubic(a,n)
Norm(a + (1 + alpha)*n) = rightCubic(a,n).
```

The two defining monic cubics have discriminant `49`. For
`pi = 1 + 2*alpha` and
`epsilon = -1 + 2*alpha + 4*alpha^2 = alpha*(1+alpha)^2`, Lean proves:

```text
Norm(pi) = -7
pi^3 = 7*epsilon
Norm(epsilon) = -1
epsilon * (-9 + 22*alpha - 8*alpha^2) = 1.
```

Writing `varpi = epsilon^4*pi`, the unit-free normalization is:

```text
pi * (7^4*m^7) =
  varpi^6 * (epsilon^(-8)*varpi*m)^7,
```

where the negative exponent is represented by the explicit integral inverse.

`SevenBaseTerminalRamifiedRealCubicNorm.lean` connects this carrier to the
RAMIFIED-008 receiver packet. It absorbs the sign in
`innerRoot.snd = 7^4*m^7`, retains the signed roots `l,r`, and proves:

```text
Norm(etaL) = l^7
Norm(etaR) = r^7
r^7 - l^7 = 7*a*n*(a+n)
etaR - etaL = varpi^6*Z^7.
```

RAMIFIED-009 has Outcome A. This is a norm/source-difference theorem in an
explicit cubic order. It does not prove that the order is maximal, that its
class number is one, that the displayed units generate the full unit group,
or that a norm which is a seventh power makes the source element itself a
seventh power. Those are the separate RAMIFIED-010 through RAMIFIED-012
obligations.

## 32. RAMIFIED-010 Eisenstein maximal order and class number one

`SevenRealCubicEisenstein.lean` introduces
`theta = alpha - 3` and proves the exact translated identities:

```text
theta^3 + 7*theta^2 + 14*theta + 7 = 0
theta^3 = -7*(theta + 1)^2
IsUnit (theta + 1)
pi = -theta*alpha*(1 + alpha)
Associated pi theta.
```

The monic polynomial
`X^3 + 7*X^2 + 14*X + 7` has degree three, discriminant `49`, is
Eisenstein at `7`, and is irreducible over both `Z` and `Q`. The explicit
cyclic rotation satisfies:

```text
sigma(alpha) = alpha^2 - 2*alpha
sigma^2(alpha) = -alpha^2 + alpha + 2
sigma^3 = id.
```

`SevenRealCubicNumberField.lean` constructs the corresponding cubic number
field and its rational power basis. The power-basis discriminant is `49`.
Using the Eisenstein prime-power membership theorem, Lean proves:

```text
IsIntegralClosure Z[theta] Z K
Z[theta] ≃ₐ[Z] O_K.
```

The resulting integral power basis transports the discriminant calculation
to the field:

```text
disc K = 49
nrComplexPlaces K = 0
IsTotallyReal K
Minkowski class bound = 14/9 < 2
IsPrincipalIdealRing O_K
classNumber K = 1.
```

The original coordinate order is not merely abstractly related to this
field. The generator map is proved bijective:

```text
modelEquivRingOfIntegers :
  SevenRealCubicInt ≃+* O_K.
```

Consequently `SevenRealCubicInt` receives an `IsDomain` instance, and the
order-three rotation is transported to an automorphism of `O_K` with the
same formulas and cube equal to the identity.

RAMIFIED-010 has Outcome A. No source-conjugate ideal coprimality or ideal
seventh-power extraction is asserted here. The displayed units are not yet
proved to generate the full unit group, and local-to-global seventh-power
injectivity is not claimed. These are the exact RAMIFIED-011 and
RAMIFIED-011U inputs; element-level extraction and the later ramified depth
drop remain separate.

## 33. RAMIFIED-011A cyclic coprimality and extraction up to units

`SevenRealCubicCoprimeExtraction.lean` first transports
`IsPrincipalIdealRing` from the full ring of integers through
`modelEquivRingOfIntegers`. Thus the concrete `SevenRealCubicInt` model has
the PID/Bezout surface needed by Mathlib's coprime-power extractor.

For the linear source `x = a + b*alpha`, Lean proves:

```text
sigma(x) - x = theta*alpha*b
x*sigma(x)*sigma^2(x) = Norm(x).
```

Assuming `IsCoprime a b` and `7 | b`, a prime common divisor of `x` and
`sigma(x)` must divide `theta*alpha*b`. The `alpha` branch is impossible
because `alpha` is a unit. In the `theta` branch,
`theta^3 = -7*(theta+1)^2` and `theta+1` is a unit, so the prime divides
`7`, hence also `b`. In every surviving branch it divides both integer
coordinates, contradicting primitivity. Applying `sigma` twice gives:

```text
IsCoprime x (sigma x)
IsCoprime (sigma x) (sigma^2 x)
IsCoprime x (sigma^2 x).
```

The first source is represented by coordinates `(a,-n)` and the second by
`(a+n,n)`. The RAMIFIED-008 primitive-coordinate theorem supplies both
coprimality hypotheses, while `n = 7^4*m^7` supplies `7 | n`. Therefore the
two signed norm equations yield:

```text
etaL = uL*xiL^7
etaR = uR*xiR^7.
```

These witnesses inhabit `RamifiedRealCubicUpToUnitPacket`, which also
retains the exact equation:

```text
uR*xiR^7 - uL*xiL^7 =
  normalizedAxis^6*normalizedWitness^7.
```

RAMIFIED-011A has Outcome A. This bypasses prime-ideal exponent bookkeeping,
but it does not bypass units. Neither `uL` nor `uR`, nor their ratio, is
proved to be a seventh power. The proposed mod-`7` scalar criterion and the
claim that `alpha` and `1+alpha` exhaust all `49` unit classes belong to
RAMIFIED-011U and remain unproved. Exact element seventh powers and the
axis-depth `6 -> 3` descent are not claimed.

## 34. RAMIFIED-011U / 012 projective unit classes and exact powers

`SevenRealCubicUnitClass.lean` implements the theta-coordinate reduction:

```text
A = fst + 3*snd + 9*thd
B = snd + 6*thd
C = thd
```

over `ZMod 7`. The multiplication laws are those of
`F_7[tau]/(tau^3)`. For a unit, `A` is nonzero, so the normalized nilpotent
coordinates `x = B/A`, `y = C/A` define the truncated logarithm

```text
Lambda(u) = (x, y - x^2/2).
```

Lean proves:

```text
Lambda(u*v) = Lambda(u) + Lambda(v)
Lambda(u^7) = 0
Lambda(-1) = 0
Lambda(alpha) = (5,5)
Lambda(1+alpha) = (2,5)
5*5 - 2*5 = 1  in ZMod 7.
```

The logarithm descends through torsion and seven multiples. Dirichlet unit
rank is computed as two, the odd-degree torsion theorem identifies torsion
with `±1`, and:

```text
Nat.card UnitClassModSeven = 49.
```

The two displayed logarithms make the descended map surjective; equal finite
cardinality makes it bijective. Unpacking a zero `ModN` class and absorbing
the possible torsion sign proves the global criterion:

```text
(exists v, u = v^7) <-> Lambda(u) = 0.
```

For every primitive loaded linear source `a+b*alpha = u*root^7`, the
seventh power has zero nilpotent theta coordinates. Primitivity and `7 | b`
make the source scalar coordinate nonzero, so both nilpotent coordinates of
`u` vanish. Applied to the two RAMIFIED sources, this proves both units are
seventh powers and constructs:

```text
RamifiedRealCubicExactPowerPacket

etaL = leftRoot^7
etaR = rightRoot^7
rightRoot^7 - leftRoot^7 =
  normalizedAxis^6*normalizedWitness^7.
```

RAMIFIED-011U and RAMIFIED-012 have Outcome A. This is the pure real-cubic
second-case equation, but not a terminal FLT7 contradiction. The next
section records the now-completed RAMIFIED-013 depth split and axis drop.
The independent signed-root-gap routing and recursive descent closure remain
separate obligations.

## 35. RAMIFIED-013 exact depth ledger and real-cubic axis drop

`SevenRealCubicAxisDrop.lean` completes both internal halves of
RAMIFIED-013.

The Eisenstein axis `theta = alpha - 3` is proved prime, and its divisibility
is detected by the scalar theta coordinate in `ZMod 7`. Lean then fixes:

```text
HasExactThetaDepth (normalizedAxis^6 * normalizedWitness^7) 13
HasExactThetaDepth Phi_7(XR,XL) 3
HasExactThetaDepth (XR-XL) 10.
```

The depth-three quotient proof uses the checked expansion

```text
Phi_7(XL+d,XL)
  = 7*XL^6 + 21*XL^5*d + ... + d^6
```

and the fact that `XL` is a theta-unit. The resulting
`RamifiedRealCubicDepthLedgerPacket` retains explicit axis-free cores:

```text
XR - XL       = theta^10 * gapCore
Phi_7(XR,XL)  = theta^3  * quotientCore
theta ∤ gapCore
theta ∤ quotientCore.
```

Lean proves the two sources, hence `XL` and `XR`, are coprime. A common prime
of the two normalized cores would divide `7*XL^6`; root coprimality excludes
the `XL` branch, while the remaining branch is associated to `theta` and
contradicts axis-freeness. Therefore:

```text
IsCoprime gapCore quotientCore.
```

Their product is associated to the seventh power of the signed inner
second-coordinate root. Mathlib's PID coprime-power extractor gives:

```text
exists T, Associated (T^7) gapCore.
```

For the resulting unit `u`, Lean uses the explicit Bezout exponent split:

```text
droppedAxis    = u^(-2) * theta
descentWitness = u * theta * T

XR - XL = droppedAxis^3 * descentWitness^7
Associated droppedAxis theta
Prime droppedAxis.
```

Thus RAMIFIED-013 has **Outcome A**, and the ramified algebraic phase is
complete at its advertised boundary. The exact algebraic-root norms also
recover the signed integer roots, but the nonlinear identity
`Norm(XR)-Norm(XL)` is not `Norm(XR-XL)`. Consequently the proposed
RAMIFIED-009B signed integer gap depth does not follow merely by applying
the norm to the axis-drop equation.

The next phase is reconstruction/fusion: connect this real-cubic descent seed
back to a new primitive integer/quadratic Fermat chart with a strict global
measure decrease. No such counterexample constructor, recursive descent
provider, terminal contradiction, or unconditional FLT7 theorem is claimed
here.

## 36. FUSION-001 balanced exit and signed integer depth

`SevenRealCubicAxisDrop.lean` now closes the symmetric RAMIFIED epilogue:
the quotient core is also a seventh power up to association, and
`RamifiedRealCubicBalancedAxisSplitPacket` records

```text
XR - XL      = axis1^3 * witness1^7
Phi_7(XR,XL) = axis2^3 * witness2^7
axis1 ~ theta, axis2 ~ theta.
```

`SevenRamifiedSignedRootDepth.lean` independently factors the signed integer
seventh-power difference. It proves the signed roots coprime and constructs
7-unit cores `d,E` with

```text
r - l = 7^4*d
Phi_7(r,l) = 7*E
d*E = a*(a+n)*m^7
7 ∤ d, 7 ∤ E.
```

This is the requested integer depth-four shadow on the same balanced packet;
it does not use the false identity `Norm(XR-XL)=Norm(XR)-Norm(XL)`.
This paragraph records the boundary as it stood at FUSION-001 and is now
**superseded**. Coprimality of `d,E`, the signed `2 × 3` routing, norm first
variation, and controlled source-plane classification were completed in the
subsequent FUSION-001B and FUSION-002 checkpoints. The current boundary is
the FUSION-003 routing-cycle/cyclotomic bridge described at the top of this
document.
