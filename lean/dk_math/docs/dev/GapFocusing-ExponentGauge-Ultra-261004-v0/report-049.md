# Report 049 - centered sextic and canonical endpoint uniqueness

## Result and scope

Outcome B. The GN and ordered alternating residuals are exact evaluations
of the same natural sextic in a center coordinate. The sextic is strictly
increasing for every fixed natural gap. Consequently each fixed allocation
has at most one possible center coordinate across both charts. GN endpoint
uniqueness is recovered, and ordered alternating endpoint uniqueness is
newly proved.

A thin centered candidate retains parity, chart position, positive
primitive endpoints, and canonical alternating orientation. Its two chart
reconstruction equivalences are proved in both directions. A centered
receiver retains every 048 divisor, size, residue, support, threshold and
band guard and is equivalent to the actual source-indexed depth-four
reconstruction obligation.

These results compress the exact scalar equation; they do not establish
endpoint existence, global exclusion, terminal impossibility, or one-step
descent. No additional factor allocation is excluded by the new polynomial
or uniqueness theorems. The independent `r=3, M=1890024` allocation remains
excluded by the already proved 048 sieve. No scalar solution or source
packet was constructed for either retained numerical allocation. No
recursive descent, additional modular filter, or Legendre work was added.

## Implementation and source audit

New production:
[SevenRamifiedFusionCenteredPolynomial.lean](../../../DkMath/FLT/Seven/SevenRamifiedFusionCenteredPolynomial.lean).
New calibration:
[CenteredPolynomialCalibration.lean](../../../DkMathTest/FLT/Seven/CenteredPolynomialCalibration.lean).
The explicit audit of all 29 new public production declarations is in
[CenteredPolynomialAxiomAudit.lean](../../../DkMathTest/FLT/Seven/CenteredPolynomialAxiomAudit.lean).
There are three definitions and 26 theorems. The Seven facade exports the
new module and now has 197 direct imports.

The implementation reuses the natural GN expansion in
`CounterexampleRouting`, the signed alternating cyclotomic identity and
endpoint exchange APIs, the 046 threshold comparison, and the complete
048 source equivalence. No existing receiver definition or theorem body
was changed. Source fingerprints and equality with HEAD were checked for
21 unchanged repository source files, including all reused 044-048
production modules in the retained source inventory. Three local Mathlib
source fingerprints cover monotone-order, natural and integer-cast APIs.

The new Lean files preserve the copyright/import style and the traditional
`#print "file: ..."` following the import block. Small coordinate/parity
lemmas isolate natural arithmetic from the large scalar equations.

## Exact shared polynomial

`centeredSevenSextic D q`, abbreviated here as `P D q`, is

```text
P D q = 7*q^6 + 35*D^2*q^4 + 21*D^4*q^2 + D^6.
```

`centered_seventh_power_difference` proves, for arbitrary integers `x,D`,

```text
64*((x+D)^7-x^7)
  = D*(7*(2*x+D)^6 + 35*D^2*(2*x+D)^4
         + 21*D^4*(2*x+D)^2 + D^6).
```

This is the proposed signed identity, with a stronger integer-gap domain.
`ring` verifies its coefficients. It uses no division by `D` and remains
valid when `D=0`.

`GN_seven_centered_identity` proves, for all natural `D,u`,

```text
64*GN 7 D u = P D (D+2*u).
```

The proof expands the established GN polynomial and checks the identity
in the natural semiring with `ring`. In particular it includes both a zero
gap and the zero-endpoint boundary.

`alternatingCyclotomicSeven_centered_identity` proves

```text
u <= v ->
64*alternatingCyclotomicSeven u v = P (u+v) (v-u).
```

The proof transports to integers, uses the existing signed cyclotomic
expansion, and replaces the cast of `v-u` by the integer difference only
under the order premise. It then verifies the polynomial identity by
`ring`. Natural truncated subtraction is never substituted for an
unrestricted signed difference. Positivity is unnecessary for this
identity; it is retained separately in receiver reconstruction.

`GN_seven_eq_iff_centered` and
`alternatingCyclotomicSeven_eq_iff_centered` turn these identities into
exact scalar equivalences for an arbitrary natural target. The reverse
direction cancels the positive constant 64, not the gap.

## Monotonicity, center position and uniqueness

`centeredSevenSextic_strictMono D` proves `StrictMono (P D)` on naturals
for every `D`, including zero. If `a<b`, then `7*a^6<7*b^6` and the
nonnegative-coefficient fourth- and second-power terms are nondecreasing.
Adding the same constant `D^6` yields the strict inequality. No calculus,
real root estimate, or asymptotic argument is involved.

`centeredSevenSextic_at_gap` proves

```text
P D D = 64*D^6.
```

For `D=7^27*r^49`, both nested scalar branches therefore give exactly

```text
P D q = 64*(7*s^49) = 448*s^49.
```

| Chart | Center coordinate | Position and retained endpoint data |
| --- | --- | --- |
| GN | `q=D+2*u` | `q>D`, `u>0`, `Nat.Coprime u (7*M)` |
| Alternating | `q=v-u`, `D=u+v` | `q<D`, `0<u<=v`, `Nat.Coprime u D` |

`nestedGNResidual_centered` and `nestedAlternatingResidual_centered`
prove the equation and the corresponding strict center position. For
positive `r` and `M=r*s`, `nestedCentered_allocation_threshold` proves

```text
D<q iff 7^161*r^343 < M^49,
q<D iff M^49 < 7^161*r^343,
```

provided the common centered equation holds. It combines strict
monotonicity with `P D D=64*D^6` and the 046 exact exponent comparison.
This reinterprets the existing threshold without inventing a solution `q`.

`centeredSevenSextic_target_unique` proves that equal evaluations at a
fixed gap and target have equal center coordinates. This theorem is
stronger in domain than the requested positive-allocation specialization:
it applies to every natural gap and target.

`GN_seven_endpoint_unique_via_center` maps two GN solutions to their
centers, uses injectivity, and cancels the affine coordinate relation.
The previous `nestedResidual_unit_unique` remains available and is checked
as a retained regression.

`alternatingCyclotomicSeven_ordered_endpoint_unique` proves

```text
u+v=D, u'+v'=D, u<=v, u'<=v',
alternatingCyclotomicSeven u v = target,
alternatingCyclotomicSeven u' v' = target
  -> u=u' and v=v'.
```

Injectivity gives `v-u=v'-u'`; the fixed sums and orientation reconstruct
both endpoints by natural arithmetic. The theorem makes no raw unordered
pair uniqueness claim. Exchange still preserves the residual.

## Canonical candidate and full chart reconstruction

`CenteredNestedAllocationCandidate M r q` uses natural `q`, so `q>=0`
is built into its type. With `D=7^27*r^49`, it carries:

```text
Nat.ModEq 2 q D,
P D q = 64*(7*(M/r)^49),
(
  D<q and exists u>0,
    Nat.Coprime u (7*M), q=D+2*u
  OR
  q<D and exists u,
    0<u<D, u<=D-u, Nat.Coprime u D, D-q=2*u
).
```

Parity is explicit even though the chart relations also imply it. The
coordinate witnesses retain provenance and primitive endpoint conditions;
the predicate is not merely a numerical polynomial equality.
`centeredNestedAllocationCandidate_ne_gap` excludes `q=D`.
`centeredNestedAllocationCandidate_unique` proves that any two complete
candidates at the same `M,r` have equal `q`, including candidates presented
through different chart alternatives. This is uniqueness per fixed
allocation, not uniqueness of the divisor `r` across all allocations.

`nestedRHSAllocation_iff_ordered` selects the smaller alternating endpoint.
If exchange is needed, it transports coprimality with the sum and uses
residual symmetry. Thus orientation does not discard an exact receiver.

The branch equivalences are:

```text
NestedGNAllocationCondition M r
  iff exists q, CenteredNestedAllocationCandidate M r q and D<q;

NestedRHSAllocationCondition M r
  iff exists q, CenteredNestedAllocationCandidate M r q and q<D.
```

Their reverse proofs use the chart relation and the common exact equation
to recover the original scalar equality. For alternating reconstruction,
`D-q=2*u` and `q<D` prove `D-u-u=q`; `u<D` gives `u+(D-u)=D`.
The recovered witness still has positivity, ordering and primitive
coprimality. Neither reverse direction assumes that every numerical sextic
solution is primitive or has the required parity.

`nestedAllocation_iff_centered` combines the two branch equivalences.
`SixthPowerSievedCenteredCondition M` keeps the 048 divisor, coprimality,
coarse size, residue-seven and sixth-power support guards, and then uses
one candidate `q` with the selected chart's strict threshold and the
alternating upper band. Both directions of
`sixthPowerSievedNestedCondition_iff_centered` retain these guards.

Finally `internalDepthFourReconstruction_iff_centered` proves

```text
InternalDepthFourCounterexampleReconstructionObligation p
  iff SixthPowerSievedCenteredCondition (internalDepthFourSeventhCore p).
```

The existing 048 receiver remains intact. The new receiver is an equivalent
canonical presentation with complete chart reconstruction.

## Calibration

Twenty-three new kernel-checked calibration declarations verify the
algebra and the semantic boundaries. Concrete values include:

| Case | Residual and center value |
| --- | --- |
| `D=2,u=v=1` | alternating residual `1`, `q=0`, `P 2 0=64` |
| `D=1,u=0` | GN residual `1`, `q=1`, `P 1 1=64` |
| `D=1,u=1` | GN residual `127`, `q=3`, `P 1 3=8128` |
| `u=1,v=2,D=3` | alternating residual `43`, `q=1`, `P 3 1=2752` |
| `D=0,u=1` | GN residual `7`, `q=2`, `P 0 2=448` |

The swapped pair `(2,1)` has the same alternating residual as `(1,2)`.
Using its truncated difference `1-2=0` in the ordered formula gives the
wrong value; this is explicitly disproved by kernel `decide`. A signed
integer chart example checks `x=-1,D=3`.

Generic regressions check strict monotonicity, shared-target uniqueness,
old and new GN uniqueness, threshold position, ordered pair uniqueness,
parity retention, exclusion of the degenerate center, uniqueness across
charts, and both chart reconstruction equivalences. A midpoint regression
proves any ordered pair with sum two and residual one must be `(1,1)`.

At `M=64002,r=1`, all retained 048 arithmetic filters and the modulus-one
support condition are still proved. No endpoint or center witness is
invented. At `M=1890024,r=3`, the existing 048 exact-branch exclusion
transports to exclusion of every centered candidate. This is retained
pruning, not an additional allocation removed by the polynomial result.
The source-indexed centered equivalence is also checked generically.
The small chart values above are not solutions to an actual nested source
obligation.

## Builds, axioms and audit

All four final measured builds succeeded with `LEAN_NUM_THREADS` removed
from the environment. The focused build reports 9091 jobs, the new axiom
audit 9088, the complete Seven facade 9286, and the root build 10450.
These counts include replayed dependencies. The production module had
already compiled successfully before final measurement; the final focused
build recompiled the extended calibration. These timings are not fresh
compilation benchmarks for the complete dependency tree.

| Build | Elapsed seconds | Maximum RSS, KiB | Exit |
| --- | ---: | ---: | ---: |
| focused | 17.961 | 6766560 | 0 |
| axiom-audit | 15.535 | 6730628 | 0 |
| facade | 16.946 | 6806804 | 0 |
| root | 24.746 | 7088756 | 0 |

GNU time telemetry records zero major page faults and zero swaps for each
final invocation. No final thread-limited retry or memory failure occurred.

All 29 new public production declarations, including all three definitions,
are included in `#print axioms`. Their dependencies are confined to
`propext`, `Classical.choice`, and `Quot.sound`, or no axioms. None depends
on `sorryAx`. Focused and axiom-audit builds have no warnings.

The facade reports the four existing `sorry` warnings in
`ZsigmondyCyclotomicResearch`, `TriominoCosmicBranchA`, `GcdNextResearch`,
and `CyclotomicPrincipalization`; the root additionally reports the existing
`TriominoFLT` warning. These unchanged research modules are outside the
new declaration dependency audit.

[check-049.py](checks/check-049.py) verifies coverage of every new public
declaration, all four checked Lean headers, forbidden constructs, the
21 unchanged source fingerprints and three Mathlib fingerprints, facade
export, successful build records, the axiom whitelist, ASCII report/log
artifacts, and `git diff --check`. Evidence is retained in `logs/*-049.*`.
No new packet structures were added.

## Remaining arithmetic assertion and implementation proposals

The precise unresolved source exclusion assertion is

```text
for every source packet p,
  not SixthPowerSievedCenteredCondition (internalDepthFourSeventhCore p).
```

Unfolded, this requires excluding a natural `q` with
`P (7^27*r^49) q = 448*(M/r)^49` at every source-supported divisor
allocation passing the retained guards, parity and primitive chart
conditions. Excluding all numerical sextic solutions would be a stronger
sufficient theorem; exact reconstruction requires only exclusion of the
fully admissible candidates. Strict monotonicity gives at most one such
coordinate, but does not determine whether the target lies in the integer
image of the polynomial. No theorem that settles that image-membership
question from the current source data was obtained.

Two bounded directions follow from the proved interface; these are
proposals, not implemented results or a design for another checkpoint.

- A small reusable certificate lemma could exclude an integer solution
  from a strict bracket `P D k < target < P D (k+1)`. Monotonicity then
  rules out every natural `q`. To be useful for the actual source, a
  further theorem must produce such a `k` and both strict inequalities
  from packet data. This is not supplied by uniqueness, and no
  enumeration of astronomical endpoint ranges was performed.
- Alternatively, a source-derived Diophantine obstruction could show
  `448*(M/r)^49` never meets the centered polynomial on the admissible
  parity and primitive chart. Any needed global arithmetic hypothesis
  must remain explicit until proved. The current complementary-root
  product and residue support facts do not establish that obstruction.

Thus the new result provides exact compression and canonical uniqueness.
A source-supported image obstruction, an exact admissible witness, or a
proved one-step reconstruction/descent theorem is still needed to resolve
the scalar equation beyond this boundary.
