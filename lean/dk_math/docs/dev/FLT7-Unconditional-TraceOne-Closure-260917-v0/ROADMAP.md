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

Status: **completed — Outcome A**.

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
