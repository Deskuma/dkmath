# FLT7-017 — Seven-adic pivot layer and terminal/step descent boundary

Work on branch:

```text
feature/FLT7-magic-core-260722-v0
```

Use the current branch HEAD after completed FLT7-016.

## Status to preserve

- FLT7-015 remains Outcome C: generic prime-address uniqueness for arbitrary
  `CoprimeTripleRouting` is false. Preserve its diagonal counterexample.
- FLT7-015R proves specialized prime-address uniqueness and exact valuation
  isolation on `AwayCubicRoutingPacket`.
- FLT7-015P proves that every specialized non-seven address is soluble at its
  complete `q^e` depth.
- FLT7-016 strengthens this to exact weight-(3,7) unit-orbit classification for
  all nine non-seven cells.
- Do not revisit non-seven local solubility or orbit completeness.

## Central correction to the descent architecture

The current `AwayDescentClosureProvider` always asks for a new away packet whose
carrier is `|old root.snd|`.

For an away transfer packet,

```text
v7(carrier) = 1 + v7(|root.snd|).
```

Therefore, if the current carrier depth is `1`, then the target carrier
`|root.snd|` has depth `0`. But the carrier of every new away transfer packet has
positive seven-adic depth. Consequently a uniform theorem producing an
`AwayDescentClosureProvider` for every away packet cannot be the final recursive
surface at the terminal depth.

The correct global architecture must separate:

```text
carrier depth = 1   -> terminal arithmetic exclusion,
carrier depth > 1   -> possible recursive reconstruction step.
```

Do not fabricate a next away packet at depth zero.

## Objective

Classify the unique seven-primary pivot at its complete depth

```text
k = v7(pivot) = v7(carrier) = 1 + v7(|root.snd|),
```

as a one-step ramified local layer over `ZMod (7^k)`.

Expose the exact depth drop `k -> k-1`, construct the actual full-depth pivot
solution, and define an honest terminal/step audit boundary. If the strengthened
pivot data is sufficient to construct a new primitive counterexample for
`k > 1`, build it. Otherwise isolate the exact signed reconstruction theorem
still missing.

This checkpoint must not claim FLT7 unless terminal exclusion and recursive
closure are genuinely complete.

## New modules and tests

Create:

```text
DkMath/FLT/Seven/SevenPivotDepthPacket.lean
DkMath/FLT/Seven/SevenPivotPrimePowerSystem.lean
DkMath/FLT/Seven/SevenPivotDescentAudit.lean
DkMathTest/FLT/SevenSevenPivotDepthPacket.lean
DkMathTest/FLT/SevenSevenPivotDescentAudit.lean
```

Update:

```text
DkMath/FLT/Seven.lean
```

Create:

```text
docs/feature/FLT7-magic-core-260722/report-flt7-017.md
```

Suggested imports:

```lean
-- SevenPivotDepthPacket.lean
import DkMath.FLT.Seven.PrimePowerOrbitAudit

-- SevenPivotPrimePowerSystem.lean
import DkMath.FLT.Seven.SevenPivotDepthPacket

-- SevenPivotDescentAudit.lean
import DkMath.FLT.Seven.SevenPivotPrimePowerSystem
```

Use namespace:

```lean
namespace DkMath.FLT.Seven
```

# Part A — Stable unique-pivot selector

The existing `AwayRoutingSevenPivot` and `AwayRoutingPivotDepth` use an
inductive sector and an existential pivot. Expose a stable packet with a row and
the corresponding first-column cell.

Suggested surface:

```lean
structure AwaySevenPivotDepthPacket {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) : Type where
  row : EndpointRoutingRow
  pivot : ℕ
  pivot_eq : pivot = routingCell r.routing row .sevenV
  seven_dvd_pivot : 7 ∣ pivot
  seven_not_dvd_other : ∀ row' column',
    row' ≠ row ∨ column' ≠ .sevenV ->
    ¬ 7 ∣ routingCell r.routing row' column'
  exponent : ℕ
  exponent_eq_pivot : exponent = padicValNat 7 pivot
  exponent_pos : 0 < exponent
  carrier_depth_eq : padicValNat 7 r.cubic.transfer.carrier = exponent
  root_depth_eq : padicValNat 7 r.cubic.rootTriple.vPart = exponent - 1
```

The exact field arrangement may be improved, but preserve:

- the selected row;
- the selected pivot cell;
- exclusivity of the prime `7`;
- the exact equality `k = 1 + v7(vPart)`;
- positivity.

Construct:

```lean
nonempty_awaySevenPivotDepthPacket
```

from `awayRoutingSevenPivot_of_packet` and
`nonempty_awayRoutingPivotDepth`. Do not choose unrelated pivot witnesses; keep
row and depth provenance synchronized.

# Part B — Exact upper and lower moduli

For a pivot packet `p`, define:

```text
k := p.exponent
m := k - 1
upperModulus := 7^k
lowerModulus := 7^m
```

Prove:

```lean
upperModulus_dvd_pivot
next_upper_power_not_dvd_pivot
upperModulus_dvd_carrier
upperModulus_dvd_seven_vPart
lowerModulus_dvd_vPart
upperModulus_not_dvd_vPart
```

The last two statements express that the root second coordinate occupies the
single ramified layer between depths `k-1` and `k`.

Also prove:

```text
upperModulus = 7 * lowerModulus
```

with the required positivity hypotheses handled explicitly.

Transfer `vPart = natAbs root.snd` to signed integer divisibility theorems.

# Part C — Uniform seven-ramified first-coordinate identity

Prove the exact integer polynomial identity:

```text
seventhPowerFst u v - (u^7 + 4*v^7)
  = -14*v^2*(u+v)*(3*u^4 + 2*u^3*v - 7*u^2*v^2 - 2*u*v^3 + v^4).
```

Use a stable named residual polynomial if helpful.

Recommended theorem shape:

```lean
theorem seventhPowerFst_eq_sevenRamifiedCore_add_residual (u v : ℤ) :
  seventhPowerFst u v =
    u^7 + 4*v^7 -
      14*v^2*(u+v)*
        (3*u^4 + 2*u^3*v - 7*u^2*v^2 - 2*u*v^3 + v^4) := by
  ...
```

Then prove the valuation consequence:

```text
if 7^m divides v, then 7^(m+1) divides
  seventhPowerFst u v - (u^7 + 4*v^7).
```

This theorem is uniform, including `m = 0`. Do not split the proof into an
unnecessary mod-seven special case.

# Part D — Unit facts at the exceptional modulus

Let `M = 7^k`.

For the selected endpoint row, prove the noncarrier endpoint coordinates are
units in `ZMod M`, exactly as in the non-seven packet but now using the unique
seven pivot.

For the root side, use the already proved norm/linear theorem to show:

```text
IsUnit ((root.fst + 4*root.snd : ℤ) : ZMod M).
```

A reusable lemma is acceptable:

```text
7 does not divide an integer a -> IsUnit (a : ZMod (7^k)).
```

Do not assume `root.fst` is always a unit when `k = 1`; the stable invariant is
the root linear coordinate `root.fst + 4*root.snd`.

For the lifted sector `1 < k`, prove additionally:

```text
7 divides root.snd,
7 does not divide root.fst,
IsUnit (root.fst : ZMod M).
```

# Part E — Full-depth exceptional local-system surface

Define a dedicated structure. Do not reuse the non-seven `sevenV` structure,
because there `v = 0`, while at the exceptional full depth only `7*v = 0` and
`v` lies in the top ramified layer.

Suggested structure:

```lean
structure AwaySevenPivotPrimePowerSolution
    (k : ℕ) (row : EndpointRoutingRow) : Type where
  u v y z : ZMod (7^k)
  endpoint_nondegenerate :
    AwayEndpointPrimePowerNondegenerate (7^k) row y z
  endpoint_equation :
    AwayEndpointPrimePowerEquation (7^k) row y z
  rootLinear_isUnit : IsUnit (u + 4*v)
  seven_mul_v_eq_zero : 7*v = 0
  v_ne_zero : v ≠ 0
  first_coordinate_equation :
    match row with
    | .y => u^7 + 4*v^7 - z^3 = 0
    | .z | .sum => u^7 + 4*v^7 + y^3 = 0
```

If `v_ne_zero` is awkward for `k = 0`, keep `k > 0` in the packet. The actual
pivot always has positive `k`.

Construct the actual reduction:

```lean
AwaySevenPivotDepthPacket.toPrimePowerSolution
```

Use:

- `upperModulus_dvd_carrier` for the endpoint zero equation;
- `upperModulus_dvd_seven_vPart` for `7*v = 0`;
- `upperModulus_not_dvd_vPart` for `v ≠ 0`;
- the uniform residual theorem and endpoint first-coordinate identities for the
  displayed equation;
- root linear nondivisibility for the unit fact.

# Part F — Base layer and lifted layer split

Define an honest split:

```lean
inductive AwaySevenPivotLayerKind (p : AwaySevenPivotDepthPacket r) : Type
  | base (exponent_eq_one : p.exponent = 1)
  | lifted (one_lt_exponent : 1 < p.exponent)
```

Construct it arithmetically.

## Base layer `k = 1`

Reuse `AwayRootResidueSector` and prove the actual exceptional solution over
`ZMod 7` is exactly one of the three sector forms. Preserve the nonzero root
linear parameter.

Do not claim this base layer is contradictory unless a genuine arithmetic
exclusion is proved.

## Lifted layer `k > 1`

Prove:

```text
v^7 = 0 in ZMod (7^k),
```

because `v` has depth `k-1`.

Hence the first-coordinate equation reduces to:

```text
row Y:       u^7 = z^3,
row Z/Sum:  (-u)^7 = y^3.
```

Use the generic 3/7 unit parametrization to classify the unit coordinates by a
weight-(3,7) orbit. Keep the root second coordinate as a separate ramified
kernel coordinate; do not silently discard it because its seventh power
vanishes.

# Part G — Exact top-layer decomposition of root.snd

For the actual integer root second coordinate, expose its exact unit part:

```text
root.snd = sign * 7^(k-1) * eta,
7 does not divide natAbs eta.
```

Use existing valuation/factor extraction APIs rather than reimplementing prime
factorization. Package the result with a unit cast of `eta` modulo `7^k` or
modulo `7`, whichever gives the cleanest stable theorem.

Suggested packet:

```lean
structure AwaySevenRamifiedKernelPacket ... where
  exponent : ℕ
  unitPart : ℤ
  unitPart_not_seven_dvd : ¬ (7 : ℤ) ∣ unitPart
  rootSnd_eq : root.snd = 7^(exponent-1) * unitPart
```

Handle the sign directly in `unitPart`; do not lose signed provenance through
`natAbs` alone.

# Part H — Corrected terminal/step descent boundary

Do not assert a uniform next packet.

Define a receiver that separates the terminal and recursive obligations, for
example:

```lean
structure AwaySevenTerminalExclusionStatement ... where
  depth_eq_one : ...
  exclusionObligation : Prop
  exclusionObligation_eq :
    exclusionObligation = False -- or the exact refutation proposition
```

and

```lean
structure AwaySevenLiftedReconstructionStatement ... where
  one_lt_depth : ...
  targetCarrier : ℕ
  targetCarrier_eq : targetCarrier = Int.natAbs root.snd
  reconstructionObligation : Prop
  reconstructionObligation_eq :
    reconstructionObligation =
      Nonempty (AwayDescentClosureProvider x y z transfer)
```

A cleaner exact proposition than `False` for the terminal branch is preferred,
such as refuting the source `CounterexamplePack`.

Package:

```lean
inductive AwaySevenPivotDescentAuditResult ...
  | terminalOpen
      (layer : base data)
      (missing : exact terminal exclusion statement)
  | liftedClosed
      (provider : AwayDescentClosureProvider ...)
  | liftedOpen
      (layer : lifted data)
      (kernel : AwaySevenRamifiedKernelPacket ...)
      (missing : exact reconstruction statement)
```

If the new layer data genuinely constructs `AwayFirstCoordinateClosureResolution`
or `AwayDescentClosureProvider`, use the closed constructor. Otherwise retain
the exact missing theorem without manufacturing a provider.

# Part I — Summit route

Define a final checkpoint route from every `CounterexamplePack`:

```text
ramified coordinate branch,
or away branch with:
  - complete non-seven unit-orbit classification from FLT7-016,
  - unique seven-pivot full-depth solution,
  - base/lifted seven-layer audit result.
```

The route should preserve all previously proved data and make the remaining
proof boundary explicit.

# Required tests

Focused tests must include:

1. the generic diagonal counterexample remains valid;
2. exact pivot row selection in all three sectors;
3. `k = 1 + v7(vPart)` and upper/lower modulus divisibility;
4. symbolic verification of the uniform residual identity;
5. actual exceptional reduction over `ZMod (7^k)`;
6. a non-field symbolic lifted example over `ZMod 49` or `ZMod 343`;
7. `v^7 = 0` in the lifted layer;
8. weight-(3,7) classification of the unit coordinates;
9. signed top-layer decomposition of `root.snd`;
10. terminal/step audit route;
11. axiom audit for the public summit.

Avoid `native_decide`.

# Required report

Record:

- Outcome A/B/C;
- exact unique-pivot packet;
- upper/lower seven-power moduli;
- the uniform `u^7 + 4*v^7` residual theorem;
- actual exceptional full-depth solution;
- base/lifted classification;
- root second-coordinate top-layer decomposition;
- whether a genuine closure provider was constructed;
- the corrected terminal/step descent boundary;
- verification and axiom audit;
- recommended next checkpoint.

# Non-goals

Do not:

- reopen non-seven prime-power classification;
- generalize prime-address uniqueness to arbitrary routing grids;
- treat `ZMod (7^k)` as a field;
- replace `7*v = 0` by the false full-depth statement `v = 0`;
- discard the nonzero top ramified layer of `v` merely because `v^7 = 0`;
- fabricate a depth-zero away packet;
- claim that CRT synchronization alone yields exact integer reconstruction;
- claim recursive descent or FLT7 without both terminal exclusion and a valid
  lifted reconstruction step.

# Outcome classification

- Outcome A: the complete seven-pivot ramified layer, base/lifted split, signed
  kernel decomposition, and honest terminal/step audit boundary are complete.
  A closure provider may or may not be obtained; report that separately.
- Outcome B: the full-depth exceptional solution is complete, but one named
  layer/decomposition theorem remains for a follow-up.
- Outcome C: a proposed seven-pivot theorem is false; provide the precise failed
  theorem and a concrete arithmetic or Lean counterexample while preserving all
  prior checkpoints.

Commit with a focused message and push to the current feature branch.