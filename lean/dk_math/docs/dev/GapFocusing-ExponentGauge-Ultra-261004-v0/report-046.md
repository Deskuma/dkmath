# Report 046 - allocation threshold branch selector

## Result and scope

Outcome B. The two nested receiver branches occupy strictly opposite regions
of the exact allocation threshold `7^161*r^343`. A fixed positive divisor
allocation cannot support both branches. For the actual seven-unit source
core, equality at the threshold is impossible, so a strict arithmetic
comparison selects at most one residual equation per allocation.

The full reconstruction obligation is equivalent to a finite divisor
receiver carrying the explicit threshold guards and a common coarse size
filter. Every reconstruction requires `343<M`. Thus `M<=343` excludes the
reconstruction obligation, conditionally on that source-core bound.

The existing inner-coordinate split also gives a positive complementary
seventh root `N`, an exact source product `M*N=V*C`, coprimality of `M,N`,
and a seven-unit condition for `N`. Reconstruction would force `343<V*C`.
No bound forcing all actual source cores into the excluded range was found.

No unconditional reconstruction, global allocation exclusion, actual
one-step descent, recursive descent, or new FLT7 theorem was obtained.
Legendre remains parked. The fixed-sum/product polynomial identity was
proved; ordered alternating endpoint uniqueness remains open.

## Exact residual and allocation comparisons

All new production declarations are in
[SevenRamifiedFusionAllocationThreshold.lean](../../../DkMath/FLT/Seven/SevenRamifiedFusionAllocationThreshold.lean).
The 044 and 045 production APIs were reused without modification.

For any natural gap `D` and positive `u`,
`GN_seven_gap_pow_six_lt` proves

```text
D^6 < GN 7 D u.
```

It uses the existing explicit expansion to establish `GN 7 D 0=D^6`,
then applies the existing strict monotonicity theorem to `0<u`. The
zero-gap case remains valid. The strict inequality fails at `u=0`, as
the calibration deliberately checks.

For positive natural `x,y`,
`alternatingCyclotomicSeven_lt_sum_pow_six` proves

```text
alt(x,y) < (x+y)^6.
```

Here `alt` is the natural `alternatingCyclotomicSeven`. Both endpoints
are strictly below their sum, so their sixth powers are strictly smaller
than `(x+y)^6`. Multiplication by the positive respective endpoints and
addition give

```text
x^7+y^7 < (x+y)*(x+y)^6.
```

The exact identity `(x+y)*alt(x,y)=x^7+y^7` and cancellation of the positive
sum prove the result. No real roots or analytic estimates are used. If one
endpoint is zero, the residual equals the sixth power of the sum; this
boundary is also checked in calibration.

Let `D=7^27*r^49`, `r>0`, and `M=r*s`.
`nestedAllocation_threshold_comparisons` proves both exact equivalences

```text
D^6 < 7*s^49  iff  7^161*r^343 < M^49,
7*s^49 < D^6  iff  M^49 < 7^161*r^343.
```

The exponent arithmetic is checked in Lean:

```text
D^6 = 7^162*r^294 = 7*(7^161*r^294),
r^49*(7^161*r^294) = 7^161*r^343,
r^49*s^49 = M^49.
```

Cancellation of seven followed by multiplication or cancellation of positive
`r^49` transports either strict comparison. Consequently the exact GN
receiver implies `7^161*r^343<M^49`, and the exact alternating receiver,
with `0<u<D` and `v=D-u>0`, implies `M^49<7^161*r^343`.
These are `nestedGNResidual_allocation_threshold` and
`nestedAlternatingResidual_allocation_threshold`.

## Strict selector, divisor support, and coarse filter

`nestedAllocation_threshold_ne` proves that a seven-unit `M` cannot satisfy
`M^49=7^161*r^343`, for any natural `r`. The right side is divisible by
seven, and primality of seven would then force `7 | M`. The exclusion
does not need a residual equation or an assumption about `r`.
`nestedAllocation_threshold_dichotomy` yields the two strict sides.

The fixed-allocation propositions are thin:

```text
NestedGNAllocationCondition M r :=
  exists u>0,
    Nat.Coprime u (7*M),
    GN 7 (7^27*r^49) u = 7*(M/r)^49.

NestedRHSAllocationCondition M r :=
  exists u,
    0<u<7^27*r^49,
    Nat.Coprime u (7^27*r^49),
    alt(u,7^27*r^49-u) = 7*(M/r)^49.
```

For `M>0` and `r | M`, `nestedAllocation_branch_selector` proves

```text
7^161*r^343 < M^49  ->  not NestedRHSAllocationCondition M r,
M^49 < 7^161*r^343  ->  not NestedGNAllocationCondition M r.
```

`nestedAllocation_branches_disjoint` excludes simultaneous solutions at
the same allocation. Both results hold independently of the source's
seven-unit assumption. That assumption is needed only to guarantee that
every allocation has a strict side. The source specialization
`internalDepthFourAllocation_strict_branch_selector` supplies this strict
disjunction and the corresponding branch exclusion.
`internalDepthFourAllocation_seven_units` also proves that both `r` and
`M/r` are seven-units for every divisor of the actual source core.

The common coarse filter uses Mathlib's proved `add_pow_le` at exponent
seven, giving

```text
(x+y)^7 <= 64*(x^7+y^7).
```

The exact alternating identity and positive-sum cancellation yield
`(x+y)^6<=64*alt(x,y)`. Thus either nested branch supplies

```text
D^6 <= 64*7*s^49.
```

If `s<=7^3*r^6`, the right side is at most
`64*7^148*r^294`, strictly below `D^6=7^162*r^294`, since `r>0` and
`64<7^14`. All of this comparison is over natural integers in Lean.
`nestedResidual_coarse_allocation_bound` and its two residual
specializations prove

```text
7^3*r^6 < s,
7^3*r^7 < r*s,
343 < r*s.
```

No optimization of this simple constant was attempted.

For `M>0`, `nestedPrescribedSummandCondition_iff_allocation` reuses the
044 divisor receiver, while `nestedRightHandSideCondition_iff_allocation`
adds the corresponding alternating divisor support. A divisor gives
positive `r`, positive `s=M/r`, and the exact product `M=r*(M/r)`; the
converse sends any positive allocation into `M.divisors`.

`ThresholdRoutedNestedCondition M` is the finite-supported proposition

```text
exists r in M.divisors,
  Nat.Coprime r (M/r),
  7^3*r^7 < M,
  (
    7^161*r^343 < M^49 and NestedGNAllocationCondition M r
    OR
    M^49 < 7^161*r^343 and NestedRHSAllocationCondition M r
  ).
```

`two_nested_receivers_iff_threshold_routed` proves equivalence with the
OR of the 044 and 045 nested receivers. Its source specialization is
`internalDepthFourReconstruction_iff_threshold_routed`, using the already
proved positivity of `internalDepthFourSeventhCore p`.

The threshold is the explicit formula `7^161*r^343` compared with `M^49`.
It is not defined from a receiver truth value. The converse still requires
the exact endpoint equation and its primitive conditions. Neither
congruences nor numerical approximations construct a solution. No endpoint
enumeration or brute-force search was added.

The global OR remains unresolved. A kernel regression exhibits opposite
threshold sides at coprime divisor allocations `r=1` and `r=2` of the same
seven-unit core `M=64002`. Both pass the coarse filter:

```text
7^161 < 64002^49,
64002^49 < 7^161*2^343,
343*2^7 < 64002,
Nat.Coprime 2 (64002/2).
```

This example checks the selector's scope. It asserts no scalar endpoint
solution or actual source packet at that numerical core. Different divisors
can lie on different sides even when a single divisor cannot support both
branches.

## Source-level exclusion and complementary root relation

`internalDepthFourReconstruction_core_gt_343` proves

```text
InternalDepthFourCounterexampleReconstructionObligation p
  -> 343 < internalDepthFourSeventhCore p.
```

`internalDepthFourReconstruction_false_of_core_le_343` gives the bounded
exclusion for `M<=343`. No theorem placing every source in this range was
assumed or obtained.

For an existing `RamifiedRealCubicNormPacket q`, put

```text
M = natAbs q.innerSndRoot,
V = q.quadratic.canonical.verticalGapRoot,
C = q.quadratic.compensationRoot,
K = natAbs (seventhPowerSndCore q.quadratic.innerRoot.fst
                                    q.quadratic.innerRoot.snd).
```

The already proved source identities are

```text
natAbs innerRoot.snd = 7^4*M^7,
natAbs innerRoot.snd * K = 7^4*(V*C)^7.
```

The existing `exists_inner_secondCoordinate_split` supplies `K=N^7`.
`RamifiedRealCubicNormPacket.exists_inner_complementary_seventh_root`
uses these exact identities to cancel `7^4`, compare seventh powers, and
prove

```text
N>0,
K=N^7,
M*N=V*C,
Nat.Coprime M N,
7 does not divide N.
```

Positivity follows from the existing nonzero inner core; the gcd and unit
facts descend from its existing primitive coordinate facts. This root is
not chosen by matching seven-adic depth. The relation uses the norm packet's
actual signed inner root through its natural absolute value.

Since `N>=1`, the product relation gives `M<=V*C`.
`internalDepthFourReconstruction_outer_root_product_gt_343` combines it
with the reconstruction lower bound and proves `343<V*C`. This is a
restriction on the existing outer roots' product, not an individual lower
bound on either factor and not a global numerical upper bound on `M`.
No existing bound `V*C<=343` was supplied to eliminate all sources.

## Optional alternating identity

`alternatingCyclotomicSeven_fixed_sum_product` proves over integers, with
`D=x+y` and `t=x*y`,

```text
alt(x,y) = D^6 - 7*D^4*t + 14*D^2*t^2 - 7*t^3.
```

The proof casts the existing exact signed cyclotomic identity and checks
the polynomial expansion by `ring`. Signed subtraction is not treated as
truncated natural subtraction. A numerical calibration checks the identity
at `(x,y)=(3,4)`. Canonical order from 045 remains available. No alternating
half-interval monotonicity or ordered/unordered uniqueness theorem was
added; the threshold and divisor routing were the primary results.

## Validation performed

One production module and two calibration/audit modules were added. The
FLT Seven facade gained one import, bringing its direct imports to 194;
its complete closure was built. All four affected Lean files retain the
uniform header and the project `#print "file: ..."` marker immediately
after imports. No existing production theorem body was modified.

The new production surface has 30 public declarations: three definitions
and 27 theorems. All 30 were audited with `#print axioms`. Dependencies are
contained in `propext`, `Classical.choice`, and `Quot.sound`, without
`sorryAx`. No custom axiom, sorry, admit, native decision, unsafe
implementation, or new factor packet structure was introduced.

The 15 kernel regressions check the zero-endpoint GN boundary, its strict
positive comparison and zero-gap behavior, the zero-endpoint alternating
boundary and strict positive comparison, the finite-power bound, exact
exponent transport, opposite supported threshold sides, divisor membership,
equality-boundary exclusion, fixed-allocation disjointness, the right divisor
receiver, the fixed-sum/product identity, the combined source receiver,
and small-core exclusion. The focused build also checks all 13 unchanged
045 calibration declarations. These checks instantiate no FLT7 counterexample.

[source-audit-046.json](evidence/MANIFEST.md#log-58c24e74d78fa6d7) records fingerprints of
16 unchanged repository source files and the Mathlib `add_pow_le` source.
[check-046.py](checks/check-046.py) verifies all production declaration
coverage, the four headers, forbidden constructs, source fingerprints,
standard axiom dependencies, final build records, ASCII artifacts, and
whitespace. `git diff --check` passed.

All four final builds succeeded with `LEAN_NUM_THREADS` unset. Measurements
are retained by [build-046.py](checks/build-046.py); GNU time usage includes
waited descendants, and maximum RSS is not aggregate concurrent peak memory.

| Build | Lake target(s) | Jobs | Seconds | Maximum RSS KiB | Swaps |
| --- | --- | ---: | ---: | ---: | ---: |
| Focused | allocation threshold, new and 045 calibration | 9086 | 13.127 | 6778324 | 0 |
| Axiom audit | AllocationThresholdAxiomAudit | 9085 | 12.604 | 6739584 | 0 |
| FLT facade | DkMath.FLT.Seven | 9283 | 12.818 | 6815308 | 0 |
| Root | DkMath | 10447 | 18.534 | 7096752 | 0 |

Focused and axiom builds emitted no warnings. Facade and root builds
replayed the same four and five existing sorry warnings: ZsigmondyCyclotomicResearch
at 147, TriominoCosmicBranchA at 4187, GcdNextResearch at 850,
CyclotomicPrincipalization at 5389, and additionally TriominoFLT at 1919
in the root. These sources were unchanged. This is not a repository-wide
sorry-free claim.

## Next implementation proposal

The following proposals are not additional Lean results of this checkpoint.

1. Retain a sharper allocation band for the alternating branch. Multiplying
   `D^6<=64*7*s^49` by `r^49` and cancelling seven should give
   `7^161*r^343<=64*M^49`. Combined with the strict upper comparison,
   its supported allocations must satisfy
   `M^49<7^161*r^343<=64*M^49`. This band is stronger than the coarse
   `343*r^7<M` filter. Keep the inequalities integral and division-free;
   do not approximate `7^(161/49)`.
2. Complete ordered alternating endpoint uniqueness using the proved
   fixed-sum/product identity. For `0<u1<u2<=D/2`, the endpoint product
   `u*(D-u)` increases strictly. With `0<=t1<t2<=D^2/4`, the residual
   difference factors as
   `7*(t2-t1)*(D^4-2*D^2*(t1+t2)+t1^2+t1*t2+t2^2)`, which should be
   strictly positive. Prove the order argument over integers or rationals
   and transport it to naturals. Alongside 044 GN uniqueness, this would
   leave at most one endpoint representative in the branch selected for
   each allocation.
3. Audit source-specific prime support through `M*N=V*C` and `Coprime M N`.
   Any stronger restriction on allowed divisors must come from the existing
   outer-root equations, not from the size filter alone. The current source
   supplies a product factorization but no global cap `M<=343`. Seek an
   exact support or coefficient obstruction on the threshold-selected
   allocations, or an exact endpoint certificate, before considering
   actual one-step descent.

The remaining problem is existence or exclusion of the one exact scalar
equation selected per surviving allocation. The per-allocation selector
does not select a favorable branch globally, and recursive descent remains
deferred.
