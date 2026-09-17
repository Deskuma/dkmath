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

## FLT7TC-006 — Primitive FLT7 branch closure

Once both branch contradictions exist, compose them with the checked
`PrimeCounterexampleRoute` / p=7 specialized routing surface.

Target a theorem at the primitive positive natural level asserting that no
primitive FLT7 counterexample exists.

Keep branch orchestration separate from normalization to make the dependency
surface auditable.

Status: blocked on FLT7TC-003/004/005/005R reconstruction frontiers.

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
