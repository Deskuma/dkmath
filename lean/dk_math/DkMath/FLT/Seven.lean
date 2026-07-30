/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.QuadraticBridge
import DkMath.FLT.Seven.AxisDivisibility
import DkMath.FLT.Seven.AxisPowerRoll
import DkMath.FLT.Seven.AxisDepth
import DkMath.FLT.Seven.PrimitiveCyclotomicDepth
import DkMath.FLT.Seven.CounterexampleRouting
import DkMath.FLT.Seven.QuadraticResidualPacket
import DkMath.FLT.Seven.QuadraticCoprimeFactor
import DkMath.FLT.Seven.QuadraticSeventhPowerNormalForm
import DkMath.FLT.Seven.SeventhPowerCoordinates
import DkMath.FLT.Seven.CoordinateNormalForm
import DkMath.FLT.Seven.ModSevenSectors
import DkMath.FLT.Seven.AwaySecondCoordinateLoad
import DkMath.FLT.Seven.AwayValuationTransfer
import DkMath.FLT.Seven.CubicSecondCoordinateSplit
import DkMath.FLT.Seven.CoprimeTripleRouting
import DkMath.FLT.Seven.DescentClosureAudit
import DkMath.FLT.Seven.FirstCoordinateRemainders
import DkMath.FLT.Seven.RoutingSevenPivot
import DkMath.FLT.Seven.FirstCoordinateRoutingAudit
import DkMath.FLT.Seven.RoutingLocalSystems
import DkMath.FLT.Seven.RoutingLocalSolubility
import DkMath.FLT.Seven.LocalObstructionAudit
import DkMath.FLT.Seven.SpecializedPrimeAddress
import DkMath.FLT.Seven.PrimePowerCellSystems
import DkMath.FLT.Seven.PrimePowerCellSolubility
import DkMath.FLT.Seven.PrimePowerCellAudit
import DkMath.FLT.Seven.PrimePowerUnitOrbit
import DkMath.FLT.Seven.PrimePowerOrbitAudit
import DkMath.FLT.Seven.SevenPivotDescentAudit
import DkMath.FLT.Seven.SevenBaseLayerQuotient
import DkMath.FLT.Seven.SevenBaseFirstOrderModSeven
import DkMath.FLT.Seven.SevenBaseFirstOrderLinearization
import DkMath.FLT.Seven.SevenBaseUnitSectorClassification
import DkMath.FLT.Seven.SevenBaseLoadQuotient
import DkMath.FLT.Seven.SevenBaseTerminalPacket
import DkMath.FLT.Seven.SevenBaseTerminalWeightedBridge
import DkMath.FLT.Seven.SevenBaseTerminalLoadDivisibility
import DkMath.FLT.Seven.SevenBaseTerminalEndpointSeparation
import DkMath.FLT.Seven.SevenBaseTerminalCarrierRouting
import DkMath.FLT.Seven.SevenBaseTerminalFixedRouting
import DkMath.FLT.Seven.SevenBaseTerminalPrimeAddress
import DkMath.FLT.Seven.SevenBaseTerminalRootLoadAddress
import DkMath.FLT.Seven.SevenBaseTerminalPrimeCoordinate
import DkMath.FLT.Seven.SevenBaseTerminalPrimeCellCoordinate
import DkMath.FLT.Seven.SevenBaseTerminalOriginalRoutingProjection
import DkMath.FLT.Seven.SevenBaseTerminalOriginalPrimeAddress
import DkMath.FLT.Seven.SevenBaseTerminalOriginalPrimeDepth
import DkMath.FLT.Seven.SevenBaseTerminalPrimePowerClassification
import DkMath.FLT.Seven.SevenBaseTerminalPrimePowerOrbit
import DkMath.FLT.Seven.SevenBaseTerminalPrimePowerScaleProjection
import DkMath.FLT.Seven.SevenBaseTerminalPrimePowerPairScaleGluing
import DkMath.FLT.Seven.SevenBaseTerminalPrimeSupport
import DkMath.FLT.Seven.SevenBaseTerminalPrimeScaleFamily
import DkMath.FLT.Seven.SevenBaseTerminalPrimePowerFiniteScaleGluing
import DkMath.FLT.Seven.SevenBaseTerminalPrimePowerFiniteScaleReduction
import DkMath.FLT.Seven.SevenBaseTerminalCubicRootLoadModulus
import DkMath.FLT.Seven.SevenBaseTerminalGlobalCoordinates
import DkMath.FLT.Seven.SevenBaseTerminalGlobalModel
import DkMath.FLT.Seven.SevenBaseTerminalLiftedReconstruction
import DkMath.FLT.Seven.SevenBaseTerminalGlobalCoordinateEquations
import DkMath.FLT.Seven.SevenBaseTerminalCellPrimePartition
import DkMath.FLT.Seven.SevenBaseTerminalExclusion
import DkMath.FLT.Seven.SevenBaseTerminalFermatChartResolution
import DkMath.FLT.Seven.SevenBaseTerminalRowZAlternatingPowerSplit
import DkMath.FLT.Seven.SevenBaseTerminalRowZSignedResidualCore
import DkMath.FLT.Seven.SevenBaseTerminalRamifiedSummit
import DkMath.FLT.Seven.SevenBaseTerminalRamifiedDepth
import DkMath.FLT.Seven.SevenBaseTerminalRamifiedRouting
import DkMath.FLT.Seven.SevenBaseTerminalRamifiedGapUnitBridge
import DkMath.FLT.Seven.SevenBaseTerminalRamifiedUnitClassAudit
import DkMath.FLT.Seven.SevenBaseTerminalRamifiedResidualRootClass
import DkMath.FLT.Seven.SevenBaseTerminalRamifiedCompensationRouting
import DkMath.FLT.Seven.SevenBaseTerminalRamifiedCanonicalSplit
import DkMath.FLT.Seven.SevenBaseTerminalRamifiedQuadraticInnerRoot
import DkMath.FLT.Seven.SevenBaseTerminalRamifiedRealCubicNorm
import DkMath.FLT.Seven.SevenRealCubicEisenstein
import DkMath.FLT.Seven.SevenRealCubicNumberField
import DkMath.FLT.Seven.SevenRealCubicCoprimeExtraction
import DkMath.FLT.Seven.SevenRealCubicUnitClass
import DkMath.FLT.Seven.SevenRealCubicAxisDrop
import DkMath.FLT.Seven.SevenRamifiedSignedRootDepth
import DkMath.FLT.Seven.SevenRamifiedSignedRootRouting
import DkMath.FLT.Seven.SevenRealCubicNormFirstVariation
import DkMath.FLT.Seven.SevenRealCubicSourcePlane
import DkMath.FLT.Seven.SevenRealCubicThetaCoordinates
import DkMath.FLT.Seven.SevenRealCubicThetaSeventhPower
import DkMath.FLT.Seven.SevenRamifiedFusionUnitSector
import DkMath.FLT.Seven.SevenRamifiedThetaJetLifting
import DkMath.FLT.Seven.SevenRamifiedPairedThetaRootJet
import DkMath.FLT.Seven.SevenRamifiedFusionSectorEquiv
import DkMath.FLT.Seven.SevenRamifiedFusionRoutingAudit
import DkMath.FLT.Seven.SevenRamifiedFusionCycleNormalForm
import DkMath.FLT.Seven.SevenRamifiedFusionCyclicBridge
import DkMath.FLT.Seven.SevenRamifiedFusionRotationPhase
import DkMath.FLT.Seven.SevenRamifiedFusionRelativeRealIndex
import DkMath.FLT.Seven.SevenRamifiedFusionRealPairCarrier
import DkMath.FLT.Seven.SevenRamifiedFusionRealPairCoprimalityNormGate
import DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicPrimeAddress
import DkMath.FLT.Seven.SevenRamifiedFusionRealPairLoadAllocation
import DkMath.FLT.Seven.SevenRamifiedFusionLoadedBranchRecovery
import DkMath.FLT.Seven.SevenRamifiedFusionLoadNorm
import DkMath.FLT.Seven.SevenRamifiedFusionLoadedCore
import DkMath.FLT.Seven.SevenRamifiedFusionPrimeLoadAddress
import DkMath.FLT.Seven.SevenRamifiedFusionPrimeLoadValuation
import DkMath.FLT.Seven.SevenRamifiedFusionPrimeLoadGalois
import DkMath.FLT.Seven.SevenRamifiedFusionPrimeLoadExactValuation
import DkMath.FLT.Seven.SevenRamifiedFusionPrimeLoadGlobalFactorization
import DkMath.FLT.Seven.SevenRamifiedFusionDirectChartObstruction
import DkMath.FLT.Seven.SevenRamifiedFusionAdditiveChartFrontier
import DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicDegreeSixCarrier
import DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicLinearPrimeAddress
import DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicConjugatePrimePair
import DkMath.FLT.Seven.SevenRamifiedFusionDegreeSixOrientedLoadFactorization
import DkMath.FLT.Seven.SevenRamifiedFusionGlobalOrientedPrimeFactorization
import DkMath.FLT.Seven.SevenRamifiedFusionOrientedCarrierValuationOwnership
import DkMath.FLT.Seven.SevenRamifiedFusionSeventhPowerResidualIdealExtraction
import DkMath.FLT.Seven.SevenRamifiedFusionElementLevelOrientedPower
import DkMath.FLT.Seven.SevenBaseTerminalCellwiseCRTDecision
import DkMath.FLT.Seven.SevenBaseTerminalCellwiseFixedSystem
import DkMath.FLT.Seven.SevenBaseTerminalCellCarryDependency
import DkMath.FLT.Seven.SevenBaseTerminalDescentProvider
import DkMath.FLT.Seven.SevenBaseTerminalDescentSeedExclusion
import DkMath.FLT.Seven.SevenBaseTerminalAudit

#print "file: DkMath.FLT.Seven"

/-!
# FLT7 quadratic magic core

This facade exposes the proved discriminant `-7` norm, seventh cyclotomic
coordinate bridge, cubic second-coordinate split, the resulting coprime
routing, and the first-residue local-solubility audit.  Every actual non-seven
local witness is classified into an explicitly soluble model family; this does
not rule out stronger local or global obstructions.  On actual away packets,
outer factor coprimality also gives each prime a unique cell address and
isolates its exact row and column depth.  Every such address is classified at
its complete non-seven prime-power cell depth using unit-based
local systems over `ZMod (q^e)` and nine explicit soluble families.  This
prime-power classification is still local to one specialized address and does
not provide simultaneous signed reconstruction.  Moreover, every actual
full-depth solution is exactly a weight-(3,7) unit scaling of its canonical
explicit model.  Independently obtained local scales are not claimed to glue
globally.  The facade canonically indexes the finite support of primes dividing
the terminal cubic-root load and chooses one complete local scale packet over
every supported prime.  Their complete local moduli are pairwise coprime, and
the full and partial product-modulus APIs needed for finite induction are
available.  Finite CRT synchronizes all local scale residues into one unit
modulo their product, with explicit local reduction maps compatible with the
weight-three and weight-seven coordinate operations.  Compatibility of the
local models is not claimed.  Their four residues now have a column-independent
coordinate carrier, while an audit packet retains each model's exact
column-indexed orbit source and its constructor-specific root data.  No
single global polynomial system is claimed.  Coordinatewise finite CRT does
produce one product-modulus residue tuple reducing exactly to every projected
local model; a strengthened packet keeps local orbit coherence as an explicit
additional proof.  Combining that global residue model with the simultaneous
unit scale gives a product-modulus weight-(3,7) coordinate candidate whose
reduction recovers every actual local coordinate tuple.  Centered signed
integer representatives of the scale, model, and weighted tuple are available,
with exact cast-back and local congruence theorems.  No equality between the
independently centered integer weighted tuple and the integer weighted scaling
of the centered model is claimed unconditionally.  Their exact four-coordinate
defect is proved divisible by the combined modulus, and the signed lift is
classified as either an integer reconstruction or an explicit nonzero defect
obstruction.  Vanishing still requires a separate strict size bound.  Each
terminal row is retained as an exact `Y`, `Z`, or `Sum` arithmetic profile
together with the signed reconstruction outcome.  Natural chart exchange
excludes the `Sum` row and moves the `Y` row into the existing ramified chart;
the `Z` row has a primitive signed odd-power chart with seven-divisible gap.
Its alternating natural factor now has the exact `7^6`/`7` seventh-power
split, and its signed quadratic residual core is extracted as a seventh power.
Thus every surviving terminal away row reaches a natural or signed ramified
chart.  Both charts now inhabit one primitive integer ramified summit.  Its
second root coordinate has the exact depth
`5 + 7 * padicValNat 7 gapRoot`, and its ramified second coordinate splits
into one linear and two explicit cubic factors.  This common summit does not
by itself supply a smaller Fermat solution.  The endpoint triple and ramified
root triple are now nonzero and pairwise coprime, so they inhabit a formal
`CoprimeTripleRouting`.  The endpoint gap and root-cubic gap also have equal
complete seven-adic depth.  More strongly, an exact division-free integer
identity exhibits the two gaps as differing by explicit seven-units, and over
every `ZMod (7^k)` the root-cubic gap is the endpoint gap times a displayed
unit.  These units are coherent under adjacent seven-power reductions.  At
the first nontrivial level `ZMod 49`, their seventh-power class is equivalent
to the fixed-point test `U^7 = U` and hence to membership in the six-residue
set `{1, 18, 19, 30, 31, 48}`.  The common summit does not yet determine
which residue occurs.  Canonical summit normalization sharpens this further:
the bridge unit is the negative endpoint square times the inverse residual-root
square, the residual root lies in `{1, 8, 15, 22, 29, 36, 43}` modulo `49`,
and the bridge unit is a seventh power exactly when that residual root is `1`.
In that branch the generic six unit residues reduce to `{19, 31, 48}`.
Compatible seventh-root lifting through all higher `7^k` levels is not yet
constructed.  This bridge still does not construct a descent provider or a
smaller Fermat solution.  Each local complete exponent is also
identified with the corresponding prime's exact adic exponent in the full
terminal cubic-root load, and the product of all complete local moduli is
proved equal to that full load.
The unique seven-primary cell is reduced at its complete `7^k`
depth, including its nonzero top ramified kernel and base/lifted split.  At
terminal depth one, the facade also exports the exact carrier, residual,
endpoint, first-order, signed-kernel, and cubic-load quotient layers, together
with their row-sensitive `ZMod 7` linearization and the checked row-`Y`
mod-`49` shadow showing that a bare local congruence obstruction is insufficient.
Lifted signed reconstruction remains an explicit open obligation.  The exact integral
`AwayDescentReconstructionSeed` is proved equivalent to the existing
`AwayDescentClosureProvider` contract and constructs the strict away depth
drop when inhabited.  Such a seed or provider forces pivot exponent at least
two and is therefore impossible in the terminal exponent-one branch.  Direct
terminal exclusion, lifted-branch seed construction, an FLT7 contradiction,
and recursive closure remain unproved.  Conditional on the ramified receiver,
the extracted quadratic inner root now enters an explicit discriminant-49
cubic order.  Its two cubic forms are determinant norms, their source
difference is the ramified axis times the depth-four coordinate, and an
explicit unit normalization rewrites that difference as a sixth power of the
normalized axis times a seventh power.  Translating by `theta = alpha - 3`
gives a degree-three Eisenstein polynomial of discriminant `49`; the resulting
power-basis order is proved to be the full ring of integers.  The original
coordinate ring is explicitly ring-equivalent to that maximal order, hence is
an integral domain.  The cubic field is totally real with discriminant `49`,
Minkowski class bound `14/9`, principal ring of integers, and class number one.
Its explicit order-three cyclic rotation is also transported to the maximal
order.  The coordinate ring inherits the principal-ideal property.  For every
primitive linear source with seven-divisible second coordinate, its three
cyclic conjugates are pairwise coprime and their product is its determinant
norm.  Hence each RAMIFIED real-cubic source whose norm is a signed seventh
power is itself a seventh power up to an explicit unit.  The two remaining
units are first retained in an exact unit-weighted seventh-power difference.
The theta-coordinate reduction modulo seven then supplies a two-coordinate
truncated projective logarithm on global units.  The explicit units `alpha`
and `1+alpha` have logarithms `(5,5)` and `(2,5)`, so they span the target.
Dirichlet rank two and torsion `±1` show that the global unit quotient modulo
torsion and seventh powers has exactly `49` elements; consequently the
projective logarithm is a bijective class criterion.  A primitive loaded
linear source forces its extracted unit to have zero logarithm, hence both
RAMIFIED sources are exact seventh powers.  The facade exports the pure
equation `rightRoot^7 - leftRoot^7 = normalizedAxis^6 *
normalizedWitness^7`.  Its right side has exact theta depth `13`; the
homogeneous seventh quotient has exact depth `3`; and the algebraic root gap
has exact depth `10`.  Removing these exact theta powers leaves coprime cores,
so PID coprime-power extraction and the coprime exponents `3` and `7` absorb
the remaining unit.  The facade therefore exports a prime axis associate
`droppedAxis` and witness with
`rightRoot - leftRoot = droppedAxis^3 * descentWitness^7`.
This completes the ramified algebraic axis drop.  It does not yet construct
a new primitive Fermat counterexample, the independent signed-root depth-four
routing, an inhabited recursive descent provider, or FLT7.  The subsequent
FUSION layer now proves that every prime divisor of the signed quotient root
is one modulo fourteen and constructs its canonical primitive-seventh-root
residue address.  Independently, the two unresolved scalar routing cells are
allocated integrally among the three pair cores by PID gcd projections.
After those loads are removed, the three pairwise-coprime residual cores are
seventh powers up to units.  The load families form associated Galois cycles,
and each projected load has absolute cubic norm exactly equal to its scalar
routing cell.  If the two scalar cells are themselves seventh powers, the
load roots are absorbed and the previous conditional core-power packet is
recovered.  At every prime divisor of a scalar cell, the canonical residue
evaluation places the addressed gcd load in its maximal degree-one kernel and
excludes the competing coprime load.  The three cyclic real-cubic kernels
split `(q)` completely, so the exact kernel factor count equals the scalar
cell's rational adic exponent; their finite supported product reconstructs the
principal load ideal.  A concrete rank-six quadratic carrier now supplies
conjugate seventh roots, every local ratio evaluation, and the oriented
factorization of the zeroth real-pair carrier.  At each address the two
conjugate degree-one kernels are distinct maximal and comaximal ideals with
the same real contraction and residue cardinality `q`.  The extension of the
common real prime is exactly their product.  Mapping the finite real-cubic
load factorization therefore gives an exact finite product of oriented and
conjugate prime powers, with the original rational-prime support and
`padicValNat` exponents unchanged; distinct supported pairs remain comaximal,
and the product equals the principal ideal of the embedded load.  These
The valuation ownership of both linear carriers is now exact.  The ramified
prime above seven occurs once in each carrier, every prime on the full
quotient-root support occurs in exactly its `padicValNat` exponent on its
selected orientation, and the competing orientation is excluded.  Multiplying
the two predicted full factor ideals recovers the carrier-pair principal
ideal; integral-domain cancellation then proves that each predicted factor
ideal is exactly the corresponding carrier principal ideal.  The complete
quotient exponent is now split pointwise into the two routed-load exponents
plus seven times an explicit residual exponent.  Extending the two cell
supports by zero exponents to the full support yields exact oriented and
conjugate carrier-ideal identities of the form
`ramified loaded ideal * residual ideal ^ 7`.  The concrete carrier is now
also proved to be a principal ideal ring via a surjective integral
power-basis map from the abstract seventh cyclotomic ring of integers.  Its
principal generators give exact element equations
`carrier = loadElement * residualRoot ^ 7`; the associated unit is absorbed
into the load generator, and conjugate witnesses are chosen by literal
quadratic star.  The loaded factor is not proved to be a seventh power.
A primitive reconstructed chart and the strict global decrease required
before descent are the next separate obligations.
The direct signed-root candidate is ruled out: its seventh-power difference
has exact seven-adic depth five and therefore is not an integer seventh power.
-/
