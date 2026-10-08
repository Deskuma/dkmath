# Report 043 - finite FLT7 reconstruction boundary

## Result

Outcome B: a bounded additive reconstruction bridge and two precise no-go
results, without an inhabited one-step descent.

The depth-four reconstruction obligation is now equivalent to nonemptiness
of one explicit finite set of positive primitive natural Fermat charts. Both
surviving carrier positions are included. In particular, the prescribed
summand case, previously presented with an unbounded opposite endpoint, has
the proved bounds `z^6 <= c^7` and `z <= c^2`.

A finite certificate assembles the existing away packet and supplies the
conditional strict comparison. No certificate for an actual ramified packet
was constructed. This checkpoint does not establish FLT7, terminal exclusion,
or recursive descent.

## Legendre closeout

The 029-042 laboratory is parked. Its exact prime-only Q floor pulse and
injective target/cofactor representation do not supply an independent
weighted short-interval estimate. The tested whole-shell capacity cannot
close the strict criterion for any `n >= 3`. No Legendre production file was
changed or imported by the new FLT7 modules. The transferred lesson is to
retain source provenance when passing from exact local data to existence.

## Existing surface audited

The live checkout was clean before this implementation. The audit reused
existing APIs rather than introducing another reconstruction packet family.
The source fingerprint inventory records 23 relevant existing files in
[source-audit-043.json](logs/source-audit-043.json). The FLT Seven facade has
191 direct imports; its build validates the complete import closure, whereas
the mathematical source audit concerns the named files below.

| Existing module or layer | Available conclusion | Reconstruction limitation |
| --- | --- | --- |
| SevenRamifiedFusionStrictDescentFailureBoundary | Internal carrier depth 4, outer carrier depth 5, strict inequality; reconstruction iff strict candidate | No new natural counterexample |
| SevenRamifiedFusionCyclotomicAdditiveChartBoundary | Exact coordinates of the loaded carrier, integral norm ledger, phase ambiguity, direct chart exclusion | Carrier coordinates and norms do not give the missing natural additive equation |
| SevenRamifiedFusionElementLevelOrientedPower | Exact `carrier = load * residualRoot^7` with chosen principal generators | No additive natural chart; load need not be a seventh power |
| SevenRamifiedFusionSeventhPowerResidualIdealExtraction | Exact loaded-times-seventh-power ideal identities on full quotient support | Ideal equality is not a Fermat equation |
| SevenRamifiedFusionOrientedCarrierValuationOwnership | Exact selected/conjugate prime ownership and carrier ideals | Valuations do not reconstruct natural endpoints |
| SevenRamifiedFusionGlobalOrientedPrimeFactorization | Supported global factorization, cyclic and conjugate compatibility | Factorization does not construct a new triple |
| SevenRamifiedFusionLoadedCore | Loaded residual power split and quotient-prime addresses | No new chart |
| SevenRamifiedFusionLoadedBranchRecovery | Load absorption conditional on both routed cells being seventh powers | Even the absorbed core conclusion is algebraic, without a natural chart |
| SevenRamifiedSignedRootRouting | Positive coprime multiplicative routing board from signed-depth data | Multiplicative routing is not additive reconstruction |
| SevenRealCubicAxisDrop | Algebraic root gap equals axis cubed times a seventh power | No scalar natural Fermat triple follows from this identity alone |
| CoordinateNormalForm and AwayValuationTransfer | Root/normal-form construction from a real source packet; transfer from exceptional endpoint provenance | Need that source packet with the prescribed carrier |
| PrimeTraceOne reconstruction Kernel/Chart U16 | Exact reduction to AwayCarrierReconstruction and AwayCarrierFermatChart; positive seven-divisible target | These existing equivalences are conditional, not constructors of a chart |
| Prescribed-carrier ramified resolution U16 | From reconstruction: gap-root depth 3 and recovered ramified root-second-coordinate depth 26 | Does not provide the reconstruction premise or a recursive decreasing measure |
| SevenBaseTerminalDescentProvider | Reconstruction seed iff existing closure provider; seed gives strict away depth drop | Seed still requires a new normal form and exceptional-carrier provenance |

`CounterexamplePack x y z` contains positivity of all three naturals,
`Nat.Coprime x y`, and the exact equation `x^7 + y^7 = z^7`. The existing
chart API excludes the `y+z` carrier branch. It also constructs an away route
from either surviving seven-divisible carrier chart: ramified normal forms
are excluded in the indicated orientation, and exceptional-factor uniqueness
forces the selected carrier. Thus, once that primitive natural chart is
supplied, there is no separate missing root or valuation-transfer hypothesis.

## New finite bridge

[PrimeTraceOneReconstructionFiniteChart.lean](../../../DkMath/FLT/Seven/PrimeTraceOneReconstructionFiniteChart.lean)
defines `prescribedCarrierFiniteCharts c` as the filter of
`Icc 1 (c^2) x Icc 1 (c^2)` containing pairs `(u,v)` satisfying either

1. `Nat.Coprime u c` and `u^7 + c^7 = v^7`; or
2. `Nat.Coprime u v` and `u^7 + v^7 = c^7`.

The first certificate gives `(x,y,z) = (u,c,v)`, the second `(u,v,c)`.
There is no sum branch.

For a primitive chart with second summand `c`, positivity gives `x < z`.
The geometric quotient of `z^7 - x^7` contains the term `z^6`, and the
positive gap `z-x` is at least one. Therefore `z^6 <= c^7`. If `z > c^2`,
then `z^6 > c^12 >= c^7`, a contradiction. This proves `z <= c^2` and
bounds both unknown endpoints. In the right-hand-side carrier branch, the
existing endpoint inequalities give `u,v < c <= c^2`.

The production equivalence is

```text
awayCarrierReconstruction_iff_finiteCharts
    (hpos : 0 < c) (hseven : 7 | c) :
  AwayCarrierReconstruction c <->
    (prescribedCarrierFiniteCharts c).Nonempty
```

The notation in this display is ASCII; the source uses Lean's corresponding
divisibility and equivalence symbols.

[SevenRamifiedFusionDepthFourReconstructionAudit.lean](../../../DkMath/FLT/Seven/SevenRamifiedFusionDepthFourReconstructionAudit.lean)
specializes this theorem using already proved target positivity and
seven-divisibility:

```text
InternalDepthFourCounterexampleReconstructionObligation p
  iff
(prescribedCarrierFiniteCharts (internalDepthFourCarrier p)).Nonempty.
```

This finite existence condition is the exact remaining boundary. The bridge
does not assume an independent chart field, phase normalizer, unit equality,
norm-to-chart map, or valuation equation. The conditional theorem
`exists_strict_awayCounterexample_of_depthFourFiniteChart` assembles the
original one-step comparison if that finite condition is proved.

Finiteness does not imply feasible exhaustive computation. Depth four and
positivity imply the target is at least `7^4 = 2401`. Even at that lower
bound, the unfiltered quadratic pair window has `2401^4 = 33232930569601`
entries. This arithmetic observation is a feasibility assessment, not a
new exhaustive search result. No actual ramified packet was enumerated.

## Required eight-item provenance

Neither finite branch is claimed inhabited. The following describes exactly
what a member would supply and how the existing constructor would use it.

| Item | Prescribed summand branch | Right-hand-side branch |
| --- | --- | --- |
| 1. Proposed naturals | `(u,c,v)` | `(u,v,c)` |
| 2. Positivity | `u,v` from the positive finite window; `c` from existing admissibility | Same |
| 3. Primitive/coprime data | Filter supplies `Nat.Coprime u c` | Filter supplies `Nat.Coprime u v` |
| 4. Exact Fermat equation | Filter supplies `u^7+c^7=v^7` | Filter supplies `u^7+v^7=c^7` |
| 5. Exceptional position | `y=c`, source `.right` | `z=c`, source `.left` |
| 6. Target equality | `c := internalDepthFourCarrier p`; existing chart bridge forces route carrier equality | Same |
| 7. Away root | Existing coordinate route construction from CounterexamplePack; ramified branch excluded | Same, in its carrier orientation |
| 8. Transfer equation | Existing away endpoint transfer theorem once normal form and source are obtained | Same |

Unconditionally available target data are the number `c`, its positivity,
seven-divisibility and exact depth four, together with the outer depth-five
comparison. For the requested target packet, the normal form and exceptional
source are not yet available. They become constructible, along with root
positivity and transfer, from a finite member. The genuinely uninhabited
input is the positive primitive additive chart certificate; the table does
not claim existing ramified data already supply its `(u,v)`.

## Two new obstruction theorems and the role of phase

`internalDepthFourReconstructedRoute_root_depth` proves that any matching
away route has root-second-coordinate depth **three**: its transfer law is
`4 = 1 + depth(root.snd)`. Consequently
`internalDepthFourReconstructedRoute_root_ne_innerRoot` proves that this
new root cannot be the current quadratic inner root, whose second coordinate
has depth four. Direct reuse fails independently of the degree-six phase.

`no_fullCoordinate_decoder_on_orientedResidualIdeal` rules out the following
specific contract: a function of `(principal ideal, exact seventh power)`
that returns the full coordinate vector of every generator of the current
residual ideal. The chosen nonzero root and its zeta translate have the same
two inputs and different output vectors. The load and carrier equation can
also be kept fixed by the existing gauge theorem.

This is a proved information-loss obstruction for full-coordinate decoding.
It is not a no-go theorem for every invariant natural-chart extractor, and
it does not establish that the complete routing packet is logically
insufficient to prove reconstruction. For the existential U1.6 target,
canonical phase selection is not a demonstrated necessary missing premise:
the finite-chart bridge needs no such premise. Conversely, choosing a phase
alone would not prove positivity, coprimality, or the natural additive identity.
An extractor using raw residual coordinates must provide appropriate phase
invariance or a specified normalized representative; neither has been
assumed or constructed here.

The earlier direct signed-root Fermat candidate remains excluded. Taking
norms, multiplying all six Galois phases, or applying integer coordinate
projection does not replace the finite additive certificate. No general
impossibility result for reconstruction is asserted.

## Validation performed

Added two production modules, two test/audit modules, and one import to the
existing FLT Seven facade. All five affected Lean headers retain the project
copyright style and the `#print "file: ..."` marker immediately after imports.
No new packet structure, Legendre import, axiom, sorry, admit, native decision,
or unsafe implementation was introduced.

The nine kernel regressions cover empty windows at carriers 0,1,2,3, a
rejected pair at carrier 7, the generic right-chart bounds, the generic finite
receiver, the depth-four specialization, and the forced new root depth three.
The tiny concrete empty windows are calibrations; they do not certify an
actual depth-four carrier. Source and declaration checks are retained in
[check-043.py](checks/check-043.py).

All 11 new public production declarations (one definition, ten theorems)
were checked with `#print axioms`. Their dependencies are contained in
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` occurs in this
audit. Focused and axiom builds emitted no warnings.

All four final builds succeeded with `LEAN_NUM_THREADS` absent from the
subprocess environment, as recorded by [build-043.py](checks/build-043.py)
and the performance JSON files. GNU time telemetry includes waited
descendants and is not a measurement of aggregate concurrent peak RSS.

| Build | Lake target(s) | Jobs | Seconds | Maximum RSS KiB | Swaps |
| --- | --- | ---: | ---: | ---: | ---: |
| Focused | reconstruction audit and calibration | 9076 | 12.708 | 6782268 | 0 |
| Axiom audit | DepthFourReconstructionAxiomAudit | 9076 | 12.398 | 6733348 | 0 |
| FLT facade | DkMath.FLT.Seven | 9279 | 12.595 | 6812424 | 0 |
| Root | DkMath | 10443 | 18.187 | 7093792 | 0 |

The facade replays four pre-existing sorry warnings, and the root replays
five: ZsigmondyCyclotomicResearch:147, TriominoCosmicBranchA:4187,
GcdNextResearch:850, CyclotomicPrincipalization:5389, with
TriominoFLT:1919 additionally present in the root. These existing files were
unchanged. The new declaration audit is clean; the build is not evidence that
the entire repository is sorry-free. Header, source fingerprint, declaration
coverage, forbidden-construct and whitespace checks passed.

## Next implementation proposal

Do not start recursive descent. The one-step route remains uninhabited;
furthermore the existing U16 re-entry theorem maps a hypothetical target
of depth four to a ramified summit with root-second-coordinate depth 26.
The visible `5 -> 4` comparison alone therefore does not supply a consistent
decreasing measure across repeated ramified/away transitions.

The next useful target is an actual scalar additive construction, not another
local valuation or ideal-factorization packet:

1. Specify natural candidate endpoints from the source-indexed routing
   data and record whether the carrier is the summand or the right-hand side.
   If residual generators enter the formula, state their phase dependence
   explicitly. An invariant extractor or a proved chosen-phase construction
   is sufficient; canonical recovery of every generator is impossible.
2. Prove positivity, the relevant coprimality, and one of the two exact
   seventh-power equations. The new finite receiver immediately turns those
   data into the requested route; its bounds can check the candidate's range.
   The existing inner root cannot be the new away root: its successor must
   satisfy the newly proved depth-three requirement.
3. Before attempting a recursive provider, identify a measure on a common
   source-indexed state and prove compatibility with the whole re-entry
   transition, including the depth-26 ramified summit. This step follows
   actual one-step construction, not merely the conditional receiver.

An optional practical next API is a divisor/gap enumeration for the prescribed
summand branch: `d=z-u` divides `c^7`, so a supported-divisor search can replace
the full quadratic grid. Its arithmetic must be proved and it would still be
only a decision/reduction API, not a reconstruction existence theorem. The
remaining mathematical frontier is producing a finite additive member from
the existing ramified source, or deriving a source-specific contradiction.
