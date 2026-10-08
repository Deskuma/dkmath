# Report 047 - common seven-adic allocation residue sieve

## Result and scope

Outcome B. Both exact nested receiver branches imply the independent
complementary-factor filter `s=1 mod 7` and the stronger endpoint condition
`w^6=1 mod 343`. The divisor residue filter is equivalent to `r=M mod 7`
for the actual seven-unit source. The alternating branch also implies the
division-free band `M^49<7^161*r^343<=64*M^49`.

A thin filtered-divisor receiver incorporating the residue and band is
proved equivalent, in both directions, to the 046 threshold-routed receiver
and hence to the actual source reconstruction obligation. Its exact scalar
equations, primitive conditions, coarse size filter and two-branch structure
remain intact.

At the numerical calibration core `M=64002`, allocation `r=2` is excluded
by the new residue test and also fails the new alternating band. Allocation
`r=1` still passes the GN-side arithmetic filters. These are not source
packets or scalar solutions.

No endpoint existence, global exclusion, actual one-step descent, recursive
descent, or new FLT7 theorem was obtained. No stronger independent constraint
on the actual outer source roots was derived. Legendre remains parked.
Optional alternating endpoint uniqueness was not implemented.

## Audited reuse and finite arithmetic

The new production API is in
[SevenRamifiedFusionAllocationResidueSieve.lean](../../../DkMath/FLT/Seven/SevenRamifiedFusionAllocationResidueSieve.lean).
All existing 044-046 production theorem bodies and receiver definitions
were retained without changes.

The source audit covered the full-gap GN congruence, the alternating
full-sum congruence and endpoint symmetry, the threshold/divisor receiver,
the complementary-root source product, and the existing cyclic unit-slope
relation. Mathlib's finite-field, natural ModEq and multiplicity APIs were
also inspected. The selected proof uses the existing finite-field facts
and ModEq reduction/cancellation; it needs no general Hensel or lifting-
the-exponent framework. The carry proof is explicit finite integer
polynomial arithmetic.

`sixth_power_mod_seven_of_unit` uses the proved finite-field theorem
`Nat.ModEq.pow_card_sub_one_eq_one`, with coprimality supplied by primality
of seven, to show

```text
7 does not divide w -> w^6 congruent to 1 modulo 7.
```

`fortyNinth_power_mod_seven` uses `ZMod.pow_card_pow` twice to show

```text
s^49 congruent to s modulo 7
```

for every natural `s`, including residue zero. These are exact finite-field
facts, without assumptions on real roots or asymptotic estimates.

`fortyNinth_power_mod_seven_cube_of_one` proves

```text
s congruent to 1 modulo 7
  -> s^49 congruent to 1 modulo 7^3.
```

The ModEq hypothesis gives an integer `k` with `s=1+7*k`. Define

```text
Q = k + 3*7*k^2 + 5*7^2*k^3 + 5*7^3*k^4
      + 3*7^4*k^5 + 7^5*k^6 + 7^5*k^7.
```

The first polynomial identity is `s^7=1+49*Q`. Raising it to the seventh
power and expanding gives

```text
s^49-1 = 343*R,
R = Q + 3*7^2*Q^2 + 5*7^4*Q^3 + 5*7^6*Q^4
      + 3*7^8*Q^5 + 7^10*Q^6 + 7^11*Q^7.
```

Both coefficient identities are checked by `ring`. The proof uses the
negative witness `-R` for ModEq's integer difference `1-s^49`, so it does
not silently truncate a natural subtraction. No generic prime-power
lifting theorem or new arithmetic axiom is assumed.

## Common normalized residue consequences

Let `D=7^27*r^49` and suppose the existing full-gap congruence is

```text
s^49 congruent to w^6 modulo D,
7 does not divide w.
```

`nested_full_gap_residue_sieve` proves

```text
Nat.ModEq 7 s 1,
Nat.ModEq (7^3) (w^6) 1.
```

The first conclusion reduces the full-gap congruence modulo seven,
replaces `s^49` by `s` using Frobenius, and replaces the unit sixth power
by one. The second conclusion reduces the same original congruence modulo
343 and applies the finite carry result to the already derived residue of
`s`. Divisibility `7^3 | D` is checked with witness `7^24*r^49`.

`nestedGNResidual_residue_sieve` supplies the endpoint-unit premise from
`Nat.Coprime u (7*M)` and the GN full-gap theorem. It proves both conclusions
with `w=u`.

`nestedAlternatingResidual_residue_sieve` supplies it from
`Nat.Coprime u D`. Since `u<D`, its other endpoint is `D-u`, and the sum
is exactly `D`. Endpoint symmetry applies the 045 normalized theorem with
`u` as its head endpoint. Thus the alternating theorem also exports
`s=1 mod 7` and `u^6=1 mod 343`.

These consequences require the exact residual equation and primitive
endpoint data. A seven-unit endpoint alone need not satisfy the stronger
cube-modulus condition: the regression checks the counterexample `w=2`.
The residue conclusions are necessary conditions and do not replace either
exact scalar equation.

## Independent allocation filter and exact equivalence

`nestedAllocation_residue_sieve` applies to either fixed-allocation
proposition from 046 and yields

```text
M/r congruent to 1 modulo 7.
```

`nestedAllocation_excluded_of_residue` consequently excludes both exact
branches whenever this explicit arithmetic residue test fails. The theorem
does not require source positivity or a source seven-unit assumption; its
input is the failed complementary-factor congruence.

For `M=r*s` and `7` not dividing `r`,
`nestedAllocation_residue_iff` proves

```text
s congruent to 1 modulo 7 iff r congruent to M modulo 7.
```

One direction multiplies the first congruence by `r`. The converse cancels
`r` using the proved coprimality `Nat.Coprime 7 r`. This is not a division
in a congruence without a unit condition.
`internalDepthFourAllocation_residue_iff` supplies the exact quotient
identity and the seven-unit condition from the actual source's divisor
support. Surviving actual-source allocations therefore have `r=M mod 7`.

The new `ResidueSievedNestedCondition M` is

```text
exists r in M.divisors,
  Nat.Coprime r (M/r),
  7^3*r^7 < M,
  Nat.ModEq 7 (M/r) 1,
  (
    7^161*r^343 < M^49 and NestedGNAllocationCondition M r
    OR
    M^49 < 7^161*r^343 and
    7^161*r^343 <= 64*M^49 and NestedRHSAllocationCondition M r
  ).
```

The filter checks a residue of `M/r`, size and explicit threshold inequalities.
It is not defined from the truth of the endpoint equation. The original
fixed-allocation predicates still carry the exact GN/alternating equality
and all primitive endpoint conditions. The stronger endpoint congruence
is available from the branch lemmas without defining another endpoint
packet or duplicating the existing scalar receiver.

For `M>0`, `thresholdRoutedNestedCondition_iff_residue_sieved` proves
equivalence with the complete 046 receiver. Forward transport adds the
proved necessary residue and band. Reverse transport forgets only these
necessary filters while retaining the exact branch witness.
`internalDepthFourReconstruction_iff_residue_sieved` specializes the
equivalence to `M=internalDepthFourSeventhCore p`.

This is useful pruning before solving an endpoint equation, even though
the receivers are logically equivalent: an allocation with a failed residue
can now be rejected from `M` and `r` alone. Exact scalar solutions are
still required for every arithmetic allocation that survives.

## Alternating band and the numerical regression

`nestedAlternatingResidual_allocation_band` uses the 046 finite-power
estimate and exact equation to obtain `D^6<=64*7*s^49`. Cancelling seven
and multiplying by `r^49` give

```text
7^161*r^343 <= 64*M^49.
```

The already proved strict alternating threshold supplies the other end:

```text
M^49 < 7^161*r^343 <= 64*M^49.
```

`nestedRHSAllocation_band` exposes the band for a positive divisor allocation.
The lower comparison is strict and the upper comparison is weak; no
floating-point approximation or division of the threshold is used.

At `M=64002`, the unchanged 046 regression shows that `r=2`, `s=32001`
is coprime, is divisor-supported, passes `343*r^7<M`, and lies on the
strict alternating threshold side. The new regressions prove

```text
32001 mod 7 = 4,
not (NestedGNAllocationCondition 64002 2
     OR NestedRHSAllocationCondition 64002 2),
not (7^161*2^343 <= 64*64002^49).
```

Thus both new tests reject it. The band is more selective here than the
old coarse filter, which this allocation passes. The residue failure also
excludes the allocation without using the threshold or the band.

For `r=1`, coprimality, the old coarse size filter, `M/r=1 mod 7`, and the
strict GN-side threshold all pass. The new regression preserves these
facts but supplies no endpoint. It does not prove
`ResidueSievedNestedCondition 64002` or an actual FLT7 source at that core.
Another regression uses core one to check that passing the residue alone
does not imply even the old receiver.

## Actual source audit and optional uniqueness

The source still proves `7` does not divide `M`, and the complementary
root relation from 046 remains

```text
M*N = verticalGapRoot*compensationRoot,
N>0, Nat.Coprime M N, 7 does not divide N.
```

The existing cyclic slope also retains the residue of the chosen source
core relative to the inner first coordinate. This audit did not derive
a fixed residue class for every `M`, an extra prime-support exclusion,
or a numerical upper bound from those source facts. The new source-level
result here is the proved translation of the allocation sieve to `r=M mod 7`
and the full filtered-reconstruction equivalence. No further constraint on
`M,N` or the outer roots is claimed.

GN endpoint uniqueness from 044 and canonical alternating order from 045
remain available. The 046 fixed-sum/product identity was retained. No new
half-interval strict monotonicity or alternating ordered/unordered pair
uniqueness theorem was proved; the common residue question and band were
the implemented results.

## Validation performed

One production module and two calibration/audit modules were added. The
FLT Seven facade gained one import and now has 195 direct imports; its
complete closure was built. All four affected Lean files preserve the
uniform header and project `#print "file: ..."` marker immediately after
imports. Existing production theorem bodies were not edited.

The production surface adds 15 public declarations: one definition and
14 theorems. Every declaration was audited with `#print axioms`; all
dependencies are contained in `propext`, `Classical.choice`, and `Quot.sound`,
without `sorryAx`. No custom axiom, sorry, admit, native decision, unsafe
implementation, new factorization framework or packet structure was added.

The 15 new kernel regressions check the unit sixth-power fact, zero-residue
Frobenius, the carry at eight and its boundary at one, failure of the stronger
endpoint residue for an arbitrary unit, failure of the carry without residue
one, preservation of the 046 opposite-threshold example, the complementary
residue at `r=2`, exclusion by the residue, rejection by the band, retention
of `r=1` arithmetic filters, divisor residue equivalence, insufficiency of
the residue alone, the filtered-receiver equivalence, and the actual source
equivalence. The focused build also checks the 15 unchanged 046 regressions.
No test constructs an FLT7 counterexample.

[source-audit-047.json](logs/source-audit-047.json) retains fingerprints of
18 unchanged repository sources and three inspected Mathlib sources.
[check-047.py](checks/check-047.py) checks every new production declaration,
all four headers, forbidden constructs, source fingerprints, final build
records, standard axiom dependencies, ASCII artifacts and whitespace.
`git diff --check` passed.

All four final builds succeeded with `LEAN_NUM_THREADS` unset. Measurements
are retained by [build-047.py](checks/build-047.py). GNU time usage includes
waited descendants; maximum RSS is not aggregate concurrent peak memory.

| Build | Lake target(s) | Jobs | Seconds | Maximum RSS KiB | Swaps |
| --- | --- | ---: | ---: | ---: | ---: |
| Focused | residue sieve, new and 046 calibration | 9087 | 22.011 | 6921068 | 0 |
| Axiom audit | AllocationResidueSieveAxiomAudit | 9086 | 12.468 | 6739956 | 0 |
| FLT facade | DkMath.FLT.Seven | 9284 | 12.854 | 6810360 | 0 |
| Root | DkMath | 10448 | 18.619 | 7097016 | 0 |

Focused and axiom builds emitted no warnings. Facade and root builds
replayed the same four and five existing sorry warnings: ZsigmondyCyclotomicResearch
at 147, TriominoCosmicBranchA at 4187, GcdNextResearch at 850,
CyclotomicPrincipalization at 5389, and additionally TriominoFLT at 1919
in the root. Those source files were unchanged. This is not a repository-wide
sorry-free claim.

## Next natural frontier

The independent filters now leave an exact equation in the branch selected
for each surviving divisor. A useful implementation would classify the
finite endpoint residues satisfying `w^6=1 mod 343` and connect those classes
to the existing full-gap congruence. This should remain a necessary modular
filter, with any finite residue enumeration distinguished from endpoint
existence or a global contradiction.

The fixed-sum/product identity also supplies a narrow route to alternating
half-interval uniqueness. Together with existing GN uniqueness, such a
proof would bound each surviving allocation to at most one canonical
endpoint candidate in the selected branch. It would not construct that
candidate.

Further exclusions must use proved information about the actual source's
coprime divisor support or its exact outer-root equations. The product
`M*N=verticalGapRoot*compensationRoot` has not supplied such a decisive
restriction here. The remaining question is whether any surviving supported
allocation can satisfy the full scalar equality; recursive descent remains
deferred.
