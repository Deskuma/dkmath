# FLT7 Unconditional TraceOne Closure Roadmap

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

Base: `develop` at `65642ab38e9110609db407913969c86c786ec662`

This roadmap begins at the exact p=7 endpoint established by the completed
`FLT-Prime-TraceOne-Closure-260916-v0` campaign.  General-prime work is paused;
this branch is a fixed-exponent attack on FLT7.

## FLT7TC-000 — Exact p=7 TraceOne closure reconnaissance

Read-only audit of the current checked surface.

Determine exactly how the following layers meet:

```text
PrimeAdicFactorPacket 7
PrimeTraceOneCoordinatePacket
PrimeTraceOneStrippedIdealPacket
exists_powCoords_of_primeTraceOneImaginaryStrippedIdealPacket_seven
TraceOneInt (-2)
seventhPowerFst / seventhPowerSnd
sevenAxis / discrAxis (-2)
cyclotomicSevenToTraceOne
```

In particular, distinguish two bridges:

1. the expected easy identity between
   `traceOnePowCoords (-2) m n 7` and the existing explicit seventh-power
   polynomials;
2. the much stronger and currently unproved identification/orientation bridge
   between an arbitrary generic p=7 `PrimeTraceOneCoordinatePacket` parent and
   the specialized `cyclotomicSevenToTraceOne` coordinates.

Inventory all packet invariants that survive at the exact seventh-power
endpoint and classify which existing specialized FLT7 lemmas can consume them
without importing a final contradiction.

Deliverable: `report-000.md` only.

Status: **completed — Outcome B**.

## FLT7TC-001 — Seventh-power coordinate bridge and 7-unit consequences

If FLT7TC-000 confirms the expected theorem surface, add the smallest honest
bridge from the generic recurrence coordinates to the existing specialized
p=7 polynomial API.

Expected neutral/specialized identities include the conceptual forms:

```text
(traceOnePowCoords (-2) m n 7).1 = seventhPowerFst m n
(traceOnePowCoords (-2) m n 7).2 = seventhPowerSnd m n
```

Then expose consequences of an exact residual seventh power together with
`residual_axis_terminal`, for example the checked root-side 7-unit facts needed
to invoke existing lemmas such as
`seven_not_dvd_seventhPowerSndCore_of_norm`.

Do not claim a contradiction in this checkpoint unless it follows immediately
from already checked packet data.

Status: **completed — Outcome B**.  Two distinct primes above a common norm
prime are green; the field-level Galois and complete-splitting bridge is the
next checkpoint.  See `report-035.md`.

## FLT7TC-002 — Generic-parent to specialized p=7 coordinate bridge

Resolve the parent-coordinate provenance question found in FLT7TC-000.

The target is not merely a norm equality.  Determine the strongest checked
relation available between

```text
P.coord (g+u) u
```

for a p=7 generic `PrimeTraceOneCoordinatePacket` and

```text
cyclotomicSevenToTraceOne (g+u) u.
```

Acceptable outcomes include:

- exact equality for a canonical p=7 coordinate packet;
- equality after a proved conjugation/sign/orientation transform;
- a theorem showing that only the packet invariants needed by the obstruction
  are orientation-invariant;
- a precise proof that the current generic packet API is too noncanonical and
  a dedicated p=7 constructor/bridge is required.

Do not infer element equality from equality of norms.

Status: **completed — Outcome B**.

## FLT7TC-003 — Direct ramified seventh-power obstruction

Combine the strongest checked data from FLT7TC-001/002:

```text
parent = sevenAxis * residual
residual = delta^7
primitive/coprime residual coordinates
axis terminality
exact norm power
PrimeAdicPowerSplit at p=7
explicit seventh-power coordinate factorization
p=7 modular / valuation lemmas
```

Attempt a direct contradiction entirely inside the quadratic
`TraceOneInt (-2)` world.

Priority consumers include the existing p=7 facts around:

```text
seventhPowerSnd = 7 * v * seventhPowerSndCore
seven_not_dvd_seventhPowerSndCore_of_norm
fortyNine_dvd_seventhPowerSnd_iff
seventhPowerFst_mod_seven
sevenAxis_dvd_iff_seven_dvd_norm
```

If the data are arithmetically consistent, stop and isolate the exact missing
invariant instead of manufacturing a descent assumption.

Success milestone:

```text
ramified primitive FLT7 counterexample -> False
```

This milestone alone is not yet FLT7 unconditionality.

Status: **completed — Outcome B**.

## FLT7TC-004 — Ramified fallback bridge to the existing specialized tower

Open this checkpoint only if FLT7TC-003 shows that the quadratic packet lacks a
terminal contradiction but can be connected honestly to an already developed
specialized FLT7 intermediate packet.

Find the **nearest** reusable specialized endpoint, not the broadest import.
Prefer bridge targets around the existing quadratic seventh-root / primitive
ramified layers before the large real-cubic and degree-six fusion machinery.

The purpose is to determine whether the new exact seventh-power receiver closes
an old missing provider and thereby bypasses the historical reconstruction
obligation.

Do not import a theorem whose conclusion is already the desired FLT7
contradiction.

Status: **completed — Outcome B**.

The direct specialized-packet adapter reaches the common
`PrimitiveRamifiedSummitPacket` and recovers the exact ramified depth formula,
but it does not provide the terminal carrier/provenance retained by
`TerminalPrimitiveRamifiedSummitPacket`.  The next focused ramified frontier is
therefore an honest carrier/provenance bridge, if one can be constructed from
the specialized packet; no such bridge is assumed here.  FLT7TC-005 is now the
current named checkpoint for the separate away-branch audit.

## FLT7TC-005 — Away-branch closure

Return to the other branch of the honest front-end route:

```text
7 ∤ (z-y)
  -> z-y = a^7
  -> GTail 7 1 (z-y) y = b^7.
```

Audit the existing specialized `AwaySeven*` tower and determine whether this
new simultaneous seventh-power split supplies a stronger entry point than the
historical route.

Possible strategies are:

- direct arithmetic contradiction from the simultaneous seventh powers;
- a checked transition from the away branch to a smaller/ramified packet;
- reuse of the existing terminal away machinery if its missing input is now
  supplied by the generic route.

No well-founded descent may be assumed without a checked decreasing measure.

Success milestone:

```text
away primitive FLT7 counterexample -> False
```

Status: **completed — Outcome B**.

The generic p = 7 away split is definitionally the existing specialized
`GN 7` split and adds no new endpoint, primitive counterexample, carrier
match, or away packet.  The existing `AwayDescentClosureProvider` remains the
exact reconstruction boundary; no direct contradiction or closure provider
was constructed in this checkpoint.

## FLT7TC-005R — Common counterexample-carrier reconstruction kernel

Normalize the two remaining reconstruction boundaries against the smallest
honest receiver:

```text
there exists an actual AwayValuationTransferPacket
whose selected carrier is a prescribed natural number.
```

Status: **completed — Outcome B**.

The new `AwayCarrierReconstruction` predicate is definitionally independent
of the degree-six tower.  The away closure provider is equivalent to this
predicate at the old root second coordinate, and the U1.6 internal-depth-four
obligation is equivalent to the same predicate at its prescribed carrier.
Actual reconstruction is still not proved.  Depth one is terminal: the
candidate root second coordinate has depth zero, so neither a new away packet
nor an away closure provider can exist there.  At depth at least two, only the
necessary local divisibility gate is proved.  U1.6's depth-four carrier is
positive and locally admissible, but remains an unresolved reconstruction
receiver.  FLT7TC-006 therefore remains blocked.

## FLT7TC-005R2 — Prescribed-carrier additive Fermat chart normalization

Remove the route/root packaging from the common reconstruction statement by
normalizing it to one of three actual primitive Fermat charts:

```text
carrier = y, carrier = z, or carrier = y + z.
```

Status: **completed — Outcome B**.

`AwayCarrierReconstruction carrier` is equivalent to the inductive
`AwayCarrierFermatChart carrier`.  The reverse direction uses the existing
coordinate route and `nonempty_awayValuationTransferPacket`; the ramified
branch is excluded by the checked one-hot mod-seven/divisibility facts.  The
three positions remain distinct as prescribed-carrier data.  The `z` chart
and `y+z` chart have all coordinates strictly below the fixed carrier; the
`y` chart exposes only `carrier < z` and `x < z`.  No chart/provider is
constructed, so FLT7TC-006 remains blocked.

## FLT7TC-005R3 — Prescribed-carrier chart to common ramified summit resolution

Starting from an actual `AwayCarrierFermatChart carrier`, resolve every
prescribed position into a common `PrimitiveRamifiedSummitPacket` with
`distinguished = carrier`.  The endpoint-sum chart is now unconditionally
impossible at the finite counterexample level; the right chart reaches a
natural ramified coordinate form after summand exchange; and the left chart
has a generalized alternating split, signed residual core, and exact
quadratic seventh-power root.

Status: **completed — Outcome A for FLT7TC-005R3**.

The public wrapper is `PrescribedCarrierRamifiedSummit carrier`, with main
theorem `nonempty_prescribedCarrierRamifiedSummit_of_fermatChart` and the
corollary `nonempty_prescribedCarrierRamifiedSummit_of_awayCarrierReconstruction`.
U1.6 receives the same conditional wrapper at `internalDepthFourCarrier`
under its existing named reconstruction obligation.  The implementation does
not infer a chart from `7 ∣ carrier`, does not construct a new counterexample
or provider, and does not complete the recursive state bridge.  FLT7TC-006
therefore remains blocked.

## FLT7TC-005R4 — Primitive second-case classification and global ramified resolution

The primitive natural counterexample surface is now normalized directly:

```text
CounterexamplePack x y z
  -> exactly one of x, y, z is divisible by 7
  -> provenance-preserving PrimitiveCounterexampleRamifiedResolution
  -> PrimitiveRamifiedSummitPacket.
```

Status: **completed — Outcome A for FLT7TC-005R4**.

`primitiveSevenDivisibleEndpoint_of_counterexample` obtains the one-hot
classification from the existing mod-seven sectors.  The putative `y + z`
sector is eliminated by `no_counterexample_of_seven_dvd_y_add_z`.  The
`x`-divisible sector uses the ordinary quadratic seventh-power packet; the
`y`- and `z`-divisible sectors reuse the two public 005R3 chart resolutions.
The resulting resolution retains the original source endpoint, its
divisibility witness, and the exact equality to the summit distinguished
coordinate.

The common summit now has the exact generic laws

```text
v7(|distinguished|) = 1 + v7(gapRoot)
v7(|root.snd|) + 2 = 7 * v7(|distinguished|).
```

Consequently, under the existing U1.6 reconstruction obligation only, its
depth-four carrier gives `v7(gapRoot) = 3`, `v7(|root.snd|) = 26`, and
`7 ∣ gapRoot`.  This is not a contradiction and does not construct that
obligation.

## FLT7TC-005R5 — Counterexample-origin ramified provenance and terminalization criterion

The common summit is now refined only when it originates from an actual
primitive counterexample:

```text
CounterexamplePack
  -> PrimitiveCounterexampleRamifiedProvenance
  -> same-summit PrimitiveCounterexampleRamifiedResolution.
```

Status: **Outcome B — COUNTEREXAMPLE PROVENANCE GREEN; TERMINALIZATION IFF DEPTH ONE;
HIGHER-DEPTH RAMIFIED BRANCH IS THE PRECISE OPEN FRONTIER**.

The new provenance packet retains the three branch orientations and
`Nat.Coprime gapRoot residualRoot`; it also proves that both oriented endpoints
and their oriented sum are seven-units.  It does not choose a second summit:
`toResolution_summit` identifies the adapter's summit with the stored one.

For this provenance packet alone, terminalization means that a
`TerminalPrimitiveRamifiedSummitPacket` has exactly the same summit.  The
kernel-checked criterion is

```text
terminalizable
  <-> 7 ∤ gapRoot
  <-> v7(distinguishedEndpoint) = 1.
```

The forward implication transports `gapRoot_not_seven_dvd` through the
same-summit equality.  Conversely the terminal carrier is explicitly
`gapRoot * residualRoot`, using retained root coprimality and both unit facts.
Thus depth one reaches the historical
`RamifiedSecondCoordinateRoutingPacket` API.  Its first additional missing
input remains the old `RamifiedCubicGapSeventhShapeReceiver`; no receiver or
contradiction is constructed here.

Every counterexample-origin endpoint has positive depth, hence it is either
depth one or at least two.  In the higher-depth branch, `7 ∣ gapRoot` and
same-summit terminalization is impossible.  This branch cannot enter the old
terminal packet, and no direct contradiction follows from the newly retained
orientation, endpoint-unit, and root-coprimality facts.

## FLT7TC-005R6 — Higher-depth primary ramified routing

Status: **Outcome B — HIGHER-DEPTH PRIMARY ROUTING GREEN;
RECEIVER/INNER-ROOT BOUNDARY REMAINS OPEN**.

The positive gap root is now factored as
`gapRoot = 7^k * gapUnit`, with `k = v7(gapRoot)` and `7 ∤ gapUnit`.  The
terminal-independent second-coordinate product and coprimality lemmas are
exposed for `PrimitiveRamifiedSummitPacket`, and they construct a generalized
`CoprimeTripleRouting` board with columns
`7^(5 + 7*k)`, `gapUnit^7`, and the gap quotient coordinate.  Depth zero
calibrates back to the historical columns, while depth at least two proves
`7 ∣ gapRoot`.  Counterexample provenance also receives the exact relation
`primaryDepth + 1 = v7(|distinguishedEndpoint|)` and a same-summit routing
entry point.

The normalized routing board does not by itself provide the
`RamifiedCubicGapSeventhShapeReceiver` or the expected quadratic inner-root
extraction.  Those remain the next boundary; no contradiction or unconditional
FLT7 theorem is claimed.  See `report-011.md`.

## FLT7TC-005R7 — Higher-depth canonical split and unified receiver frontier

Status: **Outcome B — GENERALIZED CANONICAL SPLIT / RECEIVER EQUIVALENCES
GREEN; CONDITIONAL INNER-ROOT GENERALIZATION GREEN; RECEIVER EXISTENCE REMAINS
THE PRECISE GLOBAL FRONTIER**.

The R6 normalized routing board now has a canonical split with
`c31 = c32 = c33 = c21 = 1`, `c11 = 7^(5+7*k)`, and terminal-independent
compensation core `gcd(|root.snd|, |Q|)`.  The exact generalized cubic-gap
formula and receiver equivalences are proved, including depth-zero calibration
to the historical same-summit terminal receiver.

Under an explicit receiver hypothesis, the conditional quadratic inner-root
packet is generalized.  It proves the inner product in `7^4 * seventh-power`
form and exact depth `4 + 7*k`.  The historical downstream consumers that
require exact depth four therefore remain terminal-depth APIs.  The gap-unit
bridge does not derive a global receiver from counterexample provenance, so no
receiver existence, descent, contradiction, or unconditional FLT7 result is
claimed.  See `report-012.md`.

## FLT7TC-005R8 — Receiver-bypass audit via cyclotomic PID / clean Kummer p=7 specialization

Status: **Outcome D — CLEAN KUMMER NEEDS AN UNAVAILABLE PROVIDER; DIRECT PID
NEEDS A NEW UNIT/LINEAR-FACTOR BRIDGE**.

The seventh cyclotomic Minkowski/PID development now supplies clean
`classGroupPTorsionFreeAt` adapters for the abstract ring of integers and the
concrete degree-six carrier at `p = 7`. This closes only the concrete
specialization, not the generic Kummer target quantified over all domains and
exponents. Concrete principalization still returns an associated unit/load
factor; no degree-six unit seventh-power theorem or real-cubic transport bridge
is available.

The existing oriented PID element packet is clean but starts from the older
`RamifiedSignedRootRoutingPacket`, downstream of the current TraceOne receiver.
It therefore does not bypass or prove equivalent to
`CubicGapSeventhShapeReceiver`. No squarefree/no-lift GN provider is constructed
from `GN = s^7`, and default/legacy Kummer surfaces containing `sorryAx` remain
quarantined. See `report-013.md`.

## FLT7TC-005R9 — Direct second-case cyclotomic launchpad and μ₇-unit phase frontier

Status: **Outcome C — DIRECT NORM GREEN; IDEAL RAMIFIED-LOAD OWNERSHIP IS THE
PRECISE FRONTIER**.

The new audit module
`PrimeTraceOneDirectCyclotomicSecondCaseAudit` starts directly from
`PrimitiveCounterexampleRamifiedProvenance` and reuses its stored summit.  It
defines the concrete factor
`η = endpointLeft - ζ * endpointRight`, proves its explicit relative-quadratic
and real-cubic norm expansion, and specializes the result to
`N(η) = 7 * residualRoot^7` together with the division-free seventh-power
product identities.

No direct ideal identity
`Ideal.span {η} = ramifiedPrime * I^7` is proved.  Therefore no PID element
equation, associated-load unit, μ₇ phase normal form, phase-selection
congruence, or checked bridge to `CubicGapSeventhShapeReceiver` is claimed.
The public facade remains unchanged.  See `report-014.md`.

## FLT7TC-005R10 — Direct cyclotomic ideal ownership from the six-phase orbit

Status: **Outcome D — DIRECT NORM REMAINS GREEN, BUT ONE EARLIER IDEAL/GALOIS
BRIDGE IS STILL MISSING**.

The direct R9 factor now has a kernel-checked explicit factorization by the
ramified uniformizer.  Its membership in `ramifiedPrime` and exclusion from
`ramifiedPrime^2` use the current summit gap equation and
`endpointRight_not_seven_dvd`, proving exact local multiplicity one.  The
existing general six-phase product also specializes directly to
`7 * residualRoot^7`.

The six rotated/conjugate stripped factors, their pairwise nonramified
coprimality, and the seventh-power ideal extraction are not yet proved.  Hence
no direct ideal packet, PID element equation, unit phase reduction, or bridge
to `CubicGapSeventhShapeReceiver` is claimed.  See `report-015.md`.

## FLT7TC-005R11 — Chosen-factor/tail nonramified coprimality and direct ideal extraction

Status: **Outcome A — CHOSEN/TAIL COPRIMALITY AND DIRECT RAMIFIED-IDEAL
SEVENTH-POWER EXTRACTION GREEN**.

The direct `PrimitiveCounterexampleRamifiedProvenance` cyclotomic route now
defines all six phase factors and their explicit common-uniformizer quotients.
For `1 ≤ j < 7`, the quotient residue is `j * endpointRight` modulo seven,
which proves nonramified quotient support and exact first ramified multiplicity
without using the integer norm as an ideal argument.  For `2 ≤ j < 7`, the
generic common-prime disjunction is closed concretely: the ramified branch is
the unique maximal ramified prime, while the endpoint-right branch contradicts
the stored integer Bezout relation.

Only chosen-vs-other coprimality is used.  The five-phase tail is coprime to
the chosen quotient, its product has the expected `pi^5` factor, and the
rotation/star formulas identify the resulting six-factor product with
`sixPhaseProduct`.  After cancelling `pi^6`, the unit-weighted residual
seventh-power identity is converted to an ideal product identity; the
two-factor Dedekind extraction proves the direct target

```text
∃ I, Ideal.span {directLinearFactor r} = ramifiedPrime * I^7.
```

The unit is not treated as a seventh power.  PID associated-unit exposure,
`mu_7` phase normalization, receiver construction, contradiction, and
unconditional FLT7 remain outside this checkpoint.  See `report-016.md`.

## FLT7TC-005R12 — Direct chosen-quotient unit congruence and p=7 Kummer-unit frontier

Status: **Outcome C — ELEMENT PACKET AND MOD-SEVEN RATIONAL CONGRUENCE GREEN;
FULL KUMMER UNIT LEMMA BLOCKED ON A CONCRETE UNIT-THEORY BRIDGE**.

The new module
`PrimeTraceOneDirectCyclotomicUnitCongruence` extracts an honest element
packet from the R11 ideal identity:

```text
Q₁ = unit * beta^7,
directLinearFactor = ramifiedUniformizer * unit * beta^7.
```

The explicit R11 tail is proved to lie in `(7)`, so the chosen quotient is
congruent to `endpointRight` modulo `(7)`.  A characteristic-seven
scalarization theorem holds for every element of the concrete degree-six
carrier, without assuming that the quotient by `(7)` is reduced.  Applying
it to `beta` and using the nonramified chosen quotient proves that the actual
associated unit is congruent to a seven-nondivisible rational integer.

The quadratic norm audit is also green.  Its exact source is
`L*R - eisensteinAxis^35 * thetaSevenUnit^12 * A^14`; its mod-seven
coordinates are `(nonzero, 0, 0)`.  Therefore the associated real-cubic norm
unit has zero projective logarithm and is a seventh power in the real-cubic
unit group.

The degree-six unit itself is not absorbed.  The remaining first theorem is
the concrete `DegreeSixKummerUnitLemmaAtSeven`, requiring either a checked
ring-of-integers/rank-six unit transport or a direct classification of the
relative norm-one unit quotient and its `mu_7` phase.  No exact seventh-power
equation for `Q₁`, no receiver, no contradiction, and no unconditional FLT7
claim is made.  See `report-017.md`.

## FLT7TC-005R13 — Relative-norm-one unit reduction and residual μ₇ phase

Status: **Outcome C — NORM-ONE REDUCTION GREEN; CONCRETE/ABSTRACT UNIT-THEORY
TRANSPORT IS THE PRECISE FRONTIER**.

The new module
`PrimeTraceOneDirectCyclotomicRelativeNormPhase` introduces a checked
unit-level quadratic conjugation and norm.  For the actual R12 packet unit
`u`, the preferred phase

```text
delta = u / starUnit u
```

satisfies

```text
quadraticNormUnit delta = 1,
delta - 1 ∈ (7).
```

The latter is a full principal-ideal congruence, obtained from the R12
rational congruence and the unit inverse; it is stronger than equality under
the first ramified residue.

The remaining target is isolated as
`RelativeNormOneScalarUnitAtSeven`.  If this target is supplied, the module
kernel-checks `delta = 1`, `u^2 = t^7`, and the explicit 2/7 Bézout root
construction, yielding conditional equations

```text
Q₁ = gamma^7,
directLinearFactor = ramifiedUniformizer * gamma^7.
```

The target itself is not proved.  The existing
`ringOfIntegersToRing_surjective` map has not been upgraded to an equivalence,
and no checked classification of the concrete relative norm-one units as
roots of unity is available.  Thus no unconditional exact-power equation,
contradiction, receiver, or FLT7 conclusion is claimed.  See `report-018.md`.

## FLT7TC-005R14 — Cyclotomic ring-of-integers equivalence for the CM phase

Status: **Outcome C — RING-OF-INTEGERS EQUIVALENCE GREEN; CM STAR/TORSION
TRANSPORT IS THE PRECISE FRONTIER**.

The PID layer now proves injectivity of the concrete `ringOfIntegersToRing`
map. The proof uses the explicit carrier's first coordinate for characteristic
zero, the fraction-field minimal polynomial of the primitive seventh root, and
`PowerBasis.equivOfMinpoly`. Together with the existing surjection this yields
the new algebra equivalence `ringOfIntegersToRingEquiv` in
`PrimeTraceOneDirectCyclotomicCMUnitPhase`.

The current ring-of-integers type has no Mathlib `Star` instance, so the CM
star transport is not fabricated. Torsion transport, the mod-49 phase kill,
and the unconditional seventh-power closure remain open. No unconditional
direct-factor equation, contradiction, receiver, or FLT7 claim is made. See
`report-019.md`.

## FLT7TC-005R15 — Explicit CM conjugation transport and torsion phase kill

Status: **Outcome A — CM TORSION PHASE KILLED; DIRECT CHOSEN QUOTIENT EXACT
SEVENTH POWER GREEN**.

`PrimeTraceOneDirectCyclotomicCMTorsionPhase` transports Mathlib's explicit
CM conjugation through `ringOfIntegersToRingEquiv`, including the unit-level
coherence, and checks the abstract seventh-cyclotomic torsion order as `14`.
Concrete norm-one units satisfy `delta ^ 28 = 1`; the actual R13 phase has
the checked exponent-14 identity.

The standalone full-`(7)` concrete torsion-kill theorem is proved by a
mod-49 argument in the explicit carrier. Consequently
`RelativeNormOneScalarUnitAtSeven` is unconditional, and the existing R13
2/7 Bézout consequences are instantiated unconditionally:

```text
associated unit = unitRoot^7,
Q₁ = gamma^7,
directLinearFactor = ramifiedUniformizer * gamma^7.
```

The clean downstream audit found no receiver-free theorem that turns this
exact direct-factor equation into a primitive contradiction. FLT7TC-006 and
the public unconditional FLT7 endpoint therefore remain separate targets. See
`report-020.md`.

## FLT7TC-005R16 — Exact root norm and canonical μ₇ first-order phase normalization

Status: **Outcome B — NORMALIZED ROOT PACKET GREEN; EXACT NORM AND MOD-49
SEVENTH-POWER GATE GREEN; SURVIVING RESIDUE/GLOBAL BRANCHES REMAIN**.

The new `PrimeTraceOneDirectCyclotomicRootPhaseNormalization` module packages
the R15 chosen quotient witness with an exact integral root `gamma`. It retains
`gamma ∉ ramifiedPrime` and proves the exact signed norm identity

```text
cyclotomicNormHom gamma = residualRoot.
```

For every non-ramified cyclotomic scalar, the module defines the integer
`scalarLift` and proves existence and uniqueness of the first-order `Fin 7`
μ₇ phase. The normalized root packet preserves both the seventh-power quotient
identity and the residual norm. Its first-order normalization gives the
explicit gain

```text
gammaNorm^7 - scalarLift(gamma)^7 ∈ ramifiedPrime^8.
```

Taking the degree-six rational norm contracts this to `49 ∣ endpointRight -
scalarLift(gamma)^7`, and exposes the exact `ZMod 49` endpoint congruence.
The congruence is a checked gate only: no six-residue classifier, receiver-free
contradiction, or global FLT7 closure is claimed, and no historical receiver is
used. See `report-021.md`.

## FLT7TC-005R17 — Real-cubic exact-power orbit and fixed unit-class frontier

Status: **Outcome B — REAL-CUBIC ORBIT DIFFERENCE GREEN; FIXED UNIT CLASS
DECIDED; NEXT THETA-ADIC COPRIMALITY/DESCENT BRIDGE IDENTIFIED**.

The R16 mod-49 seventh-power congruence is shown, for units in `ZMod 49`, to
be equivalent to the existing sixth-power identity.  Specializing this to
`endpointRight` records that the finite gate is exhausted and is not a
contradiction.

The relative quadratic norm of the R16 normalized cyclotomic root gives a
current-provenance real-cubic element `rho` with
`directChosenQuotientRealSource = rho ^ 7` and exact signed norm equal to
`residualRoot`.  Its nonzero theta residue is proved from the residual-root
seven-unit condition.  The three rotated sources and roots form an exact
order-three orbit.

The first rotated source difference is factored as

```text
orbitUnit01 * (eisensteinAxis^5 * thetaSevenUnit * gapRoot^2)^7
```

where `orbitUnit01` is explicit, source-independent, and a unit.  Its fixed
unit class is computed exactly as `(0, 5)` in `ZMod 7 × ZMod 7`; therefore it
has no seventh root.  This is a global unit-class obstruction, not a
contradiction.

The clean real-cubic files were audited without instantiating a historical
receiver.  No current-provenance theorem yet controls the theta-adic
factorization and coprimality of `rho1 - rho0` together with its homogeneous
seventh quotient, so no descent consumer applies.  No new state or strict
descent measure is claimed.  See `report-022.md`.

## FLT7TC-005R18 — Production direct orbit split

Productionize the direct real-cubic orbit split from Astra-001, stopping at
the exact theta depths and current-provenance stripped-core coprimality.  The
target remains receiver-free and must not assume a successor state.

Status: **completed — Outcome C**.

`PrimeTraceOneDirectRealCubicOrbitSplit` now exposes the seven-adic gap-root
split, exact quotient depth three, exact gap depth `32 + 42*k`, the stable
theta^32 divisibility, direct root coprimality, common-prime localization to
the Eisenstein axis, and coprimality of the stripped cores.  The associated
unit-times-seventh-power extraction and Archimedean smaller-norm bound remain
the next bounded layer.  See `report-023.md`.

## FLT7TC-005R19 — Stripped-core seventh-power extraction

The direct-orbit stripped cores now have a literal theta-cancelled product
identity and generic coprime seventh-power extraction.  The new
`DirectOrbitPowerSplitPacket` retains the current direct provenance, exact
theta depths, coprimality, roots, explicit units, and unit-times-seventh-power
equalities.  The common-prime theorem consumes the neutral homogeneous
quotient kernel from FLT7TC-005R24.

Status: **completed — Outcome C**.  The exact projective unit classes `(2,4)`
and `(5,1)` remain a separate local congruence and generator-invariance
bridge; no Archimedean smaller-norm theorem is claimed here.  See
`report-025.md`.

## FLT7TC-005R20 — Archimedean bridge and smaller-norm frontier

The production height module now contains the exact `H7` sum-of-squares
inequalities needed by the Astra route and exports them through the FLT7
facade.  The required total-positivity bridge from
`QuadraticAlgebra.norm gammaNorm` to all three real embeddings of the cubic
field is not present in the current direct API.

Status: **completed — Outcome C**.  No norm lower bound, strict smaller norm,
successor state, or descent claim is made until that bridge is kernel-checked.
The unresolved projective unit classes are explicitly nonessential for this
height checkpoint.  See `report-026.md`.

## FLT7TC-005R21 — Sign-free three-conjugate gap height and strict smaller norm

The current direct power-split packet now has a chosen real embedding,
cyclic real norm evaluation, sign-free three-conjugate height control, exact
direct orbit norm product, positivity, and a strict smaller root norm.  The
result is packaged as `DirectOrbitSmallerNormPacket` and exported through the
FLT7 facade.

Status: **completed — Outcome A**.  This remains a current-provenance
smaller-norm packet only; no successor state, infinite descent, or
unconditional FLT7 closure is claimed.  See `report-027.md`.

## FLT7TC-005R22 — Smaller-norm successor audit and cyclic twisted state

The smaller-norm packet now exposes the exact complement identity
`natAbs(norm gapRoot) * natAbs(norm quotientRoot) = a^6`.  All three rotated
gap edges are expressed with one common theta factor and retained unit
coefficients; telescoping gives an exact cyclic twisted seventh-power
equation.  These facts are packaged as `DirectRealCubicTwistedSeventhState`,
with root equal to the extracted gap root and a strict measure comparison to
the original summit gap root.

Status: **completed — Outcome B**.  The state is not yet self-similar: exact
theta-depth, quotient coprimality/localization, and a repeated theta-free
seventh-power split are the first missing bridge.  No integer summit
reconstruction or infinite descent is claimed.  See `report-028.md`.

## FLT7TC-005R23 — Twisted coefficient classes and self-similarity obstruction audit

The real-cubic rotation action on the projective unit class is now exported
as an additive map `M(X,Y)=(4X,X+2Y)`, with kernel-checked order-three and
zero-norm identities.  The pair-axis class, exponent reduction, weighted
two-term remainder identity, and a transported twisted successor state are
also productionized.

The exact `(2,4)` class of an arbitrary extracted `gapUnit` is not derivable
from the current power-split packet fields alone: the missing theta-free local
congruence has not been promoted from the Astra finite witness.  Therefore the
coefficient triple, ratio classes, and seventh-power gauge obstruction are
exported only under that explicit local-class hypothesis.  No weighted gap
divisibility or ordinary homogeneous quotient restart is claimed.

Status: **completed — Outcome D**.  The current successor state is not
self-similar under the available extraction mechanism.  The strict smaller
norm from R22 remains available, but no iterable descent is claimed.  See
`report-029.md`.

## FLT7TC-005R24 — Generic homogeneous power quotient kernel

Instruction-024 generalized the existing difference-of-powers quotient without
duplicating `DkMath.Algebra.DiffPow.diffPowSum`.  The new neutral
`DkMath.Lib.NumberTheory.HomogeneousPowerQuotient` alias exposes the generic
factorization, the arbitrary-exponent gap congruence, and common-prime
localization to the exponent scalar, with an `IsCoprime` corollary.  The
generic module imports no FLT code.  Separate tests cover exponents 3, 5, and
7, an integer common-prime instance, and the equality with the existing FLT7
`seventhQuotient`; the module is exported from `DkMath.Lib`.

Instruction-030 extends this kernel with the production real-cubic local-class
bridge in `PrimeTraceOneDirectRealCubicLocalClass`: the canonical quotient core
has three exact theta coordinates, the production quotient-unit class is
`(5,1)`, and the production gap-unit class is `(2,4)`.  The coefficient and
ratio classes are exported unconditionally from the packet identities.

Status: **completed — Outcome A**.  The optional AM-GM inequality was deferred
because it is not part of the quotient/localization kernel.  Weighted successor
divisibility, iterable descent, and unconditional FLT7 closure remain outside
this checkpoint.  See `report-024-generalization.md` and `report-030.md`.

## FLT7TC-005R25 — Weighted-gap nondivisibility and ordinary self-similarity closeout

Instruction-031 computes the scalar theta residue of the transport unit
`directOrbitPairAxisUnitOne` as `4`.  For the transport exponent
`32 + 42*k`, the multiplicative residue-field calculation is carried out
modulo `6`, giving `4^(32+42*k) = 2`; this is kept distinct from the
projective-log exponent reduction modulo `7`.

For every current `DirectOrbitPowerSplitPacket`, the coefficient ratio has
scalar residue `2`.  Consequently the coefficient difference is not divisible
by `eisensteinAxis`, while the rotated root gap is divisible by it and the
root seventh power is not.  The weighted remainder is therefore not
theta-divisible.  The exact weighted difference identity then proves that the
full weighted difference is not divisible by the ordinary root gap.

The production API exposes both
`directOrbit_weighted_difference_not_gap_dvd` and the explicit
`directOrbit_no_ordinary_homogeneous_restart` corollary, plus the optional
unit-gauge obstruction from the R24 projective classes.

Status: **completed — Outcome B**.  The R22/R23 smaller twisted state is not
self-similar under the ordinary homogeneous seventh-power gap extraction
mechanism.  This is a structural obstruction, not an FLT7 contradiction;
weighted/twisted factorization and alternate successor constructions remain
separate research choices.  See `report-031.md`.

## FLT7TC-005R26 — Coprime square refinement beneath the power split

Instruction-032 returns to the exact element product before norms.  For every
current `DirectOrbitPowerSplitPacket`, the unit factors are removed from the
core coprimality statement, and `IsCoprime.pow_iff` proves coprimality of the
two extracted seventh roots.  The R24 projective classes make the unit defect
between the root product and the scalar square a seventh power.  Seventh-power
equality is transported through the existing real embedding, where odd-power
injectivity is valid, and then returned to the integral model.

The existing generic associated-power splitter at exponent two supplies
square roots and explicit unit-times-square equations.  The norm consequences
are `G=R^2`, `Q=S^2`, `R*S=a^3`, together with `0<R` and `R^2<a` from the R21
strict bound.  No norm-coprimality inference, weighted quotient, successor
state, or descent claim is made.

Status: **completed — Outcome A**.  The element-level square refinement is
kernel-checked, while the successor bridge and unconditional FLT7 closure
remain open.  See `report-032.md`.

## FLT7TC-005R27 — Square-refined twisted signature audit

The R27 production layer defines the square-refined twisted unit coefficients
and proves the exact identity

```text
c0 * (r0^7)^2 + c1 * (r1^7)^2 + c2 * (r2^7)^2 = 0.
```

The exponent `32 + 42*k` is even, so the pair-axis factor is a square and
the coefficient transports are `c1 = P^e * rotate(c0)` and
`c2 = P^e * rotate(c1)`.  The projective classes remain `(2,4)`, `(2,2)`,
`(2,5)`, and all three square-root variables are nonzero by real-embedding
injectivity.  A square-unit assumption on `c0` gives a strict real positivity
contradiction, hence `c0` is not a square unit.

The signed norm is fixed by the positive direct-gap norm and unit norm
absolute value: `norm c0 = 1`.  The cyclic real signature is neither totally
positive nor totally negative.  This is a structural mixed-sign obstruction;
it is not an FLT7 contradiction and does not provide the missing successor or
descent theorem.

Status: **completed — Outcome B**. The square-weighted state is green, `c0` is a non-square mixed-sign norm-one unit, and the repeated power-refinement route is frozen. No FLT7 contradiction is claimed. See `report-033.md`.

## FLT7TC-005R28 — Square-root scalar split and Galois prime-support audit

The R28 production layer operates on the current
`DirectOrbitSquareRefinementPacket`. It proves coprimality of the two square
roots by removing the unit factors and applying `IsCoprime.pow_iff`, then
proves the scalar product split

```text
Associated (r * s) (a : O)
r * s = unit * (a : O)
```

The associated-square step uses Mathlib's `Associated.pow_iff` in the
integrally closed real-cubic integer ring. The existing R26 norm theorem is
re-exported as `R * S = a^3`, `0 < R` and `R^2 < a` are retained, and `S > 0`
is added. Both square roots are proved not divisible by the Eisenstein axis.

The rational norm-prime and cyclic Galois support layer is deliberately not
overstated: the current checkpoint does not add a neutral ideal-factorization
bridge, `7 ∤ R/S`, a gcd support theorem, or `q ≡ ±1 (mod 7)`. In particular,
it does not infer element divisibility from rational norm divisibility and it
does not claim `Nat.Coprime R S`.

Status: **completed — Outcome C**. The element-level scalar split and
theta-unit audit are kernel-checked; the prime-ideal/Galois support bridge
remains open. See `report-034.md`.

## FLT7TC-005R29 — Norm-prime to distinct prime ideals above q

The R29 production layer adds the missing ideal-level bridge for the current
R28 square packet.  For a rational prime `q` dividing both current model
norms, Mathlib's absolute-norm support theorem is applied to the two principal
ideals in the actual ring of integers `𝓞 SevenRealCubic.Field`.  The resulting
maximal ideals lie over `Ideal.span {(q : ℤ)}` and divide the corresponding
principal ideals.  R28 coprimality is transported through the ring
equivalence, so equality of the two maximal ideals would force the unit ideal;
therefore they are distinct.  Consequently the primes-over set has cardinal
at least two.

This remains a common-norm-prime existence statement.  It does not infer
`Nat.Coprime` of the two rational norms, does not prove `q ∣ r` or `q ∣ s`,
does not establish complete splitting or residue-degree one, and does not
close FLT7.  See `report-035.md`.

Status: **completed — Outcome B**. Two distinct primes above a supplied common norm prime are kernel-checked; the field-level Galois / complete-splitting bridge is the next frontier. See `report-035.md`.

## FLT7TC-005R30 — Real-cubic Galois bridge and complete splitting

The R30 production layer extends the actual ring-of-integers rotation through
the fraction field, proves the cubic splitting-field and Galois instances,
and instantiates the Mathlib prime-decomposition identity for
`ℤ ⊂ 𝓞 SevenRealCubic.Field`.  The unique prime above `(7)` is exposed with
`primesOver.ncard = 1`; the current R29 norm-prime hypotheses separately
exclude `7` from either square-root norm.  For every supplied common norm
prime, the R29 lower bound together with Galois degree three yields exactly
three primes over the rational prime and ramification/inertia indices equal
to one.

Status: **completed — Outcome B**. The complete-splitting theorem is a
common-norm-prime result.  The audit for a residue criterion
`q ≡ ±1 (mod 7)` and any FLT7 endpoint remains outside this checkpoint. See
`report-036.md`.

## FLT7TC-006 — Primitive FLT7 branch closure

The original away branch no longer needs an independent final contradiction:
it is absorbed into the common ramified second-case surface by FLT7TC-005R4.
The next target is a kernel-checked exclusion of a ramified summit carrying
counterexample provenance:

```text
PrimitiveCounterexampleRamifiedResolution source -> False.
```

Equivalently, a stronger provenance-preserving ramified packet may be shown
impossible.  This is deliberately not a claim that an arbitrary
`PrimitiveRamifiedSummitPacket` is impossible.

Target a theorem at the primitive positive natural level asserting that no
primitive FLT7 counterexample exists.

Keep branch orchestration separate from normalization to make the dependency
surface auditable.

Status: blocked on a counterexample-origin ramified summit exclusion.  The
depth-one subbranch reaches only the historical second-coordinate routing
surface and still needs its explicit shape receiver; the genuinely new
higher-depth branch has `v7(distinguishedEndpoint) ≥ 2` and cannot use the
terminal entry packet.  The historical prescribed-carrier reconstruction
kernel remains an audited conditional boundary, but is no longer needed to
normalize an original away branch into the common summit surface.

## FLT7TC-007 — Public unconditional FLT7 endpoint and closeout

Only after primitive closure is kernel-checked, discharge the standard
normalization layer and expose the final public theorem, conceptually:

```text
x > 0 -> y > 0 -> z > 0 -> x^7 + y^7 ≠ z^7
```

Use the repository's established FLT3/FLT5 naming and facade conventions where
appropriate.

Required closeout:

- focused builds;
- p=7 API regression;
- `#print axioms` audit;
- forbidden-source scan;
- `git diff --check`;
- final report distinguishing the new proof route from the historical FLT7
  research tower.

Status: blocked.

## Global stop rules

Stop and report rather than force a theorem if:

- a generic p=7 coordinate packet is treated as the specialized coordinate
  pair only because their norms agree;
- `residual = delta^7` is treated as contradictory without an additional
  arithmetic invariant;
- `residual_axis_terminal` is silently strengthened beyond its actual
  divisibility content;
- the root coordinates are assumed primitive without a checked descent lemma;
- local mod-7 information is promoted to an integer/global descent witness;
- a specialized FLT7 import already contains the desired terminal
  contradiction and is used circularly;
- the away simultaneous-power split is declared impossible without proof;
- a well-founded descent relation is assumed rather than constructed;
- any new source requires `sorry`, `sorryAx`, `admit`, or a project `axiom`.
