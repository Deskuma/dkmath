# Report 048 - sixth-power allocation residue support

## Result and scope

Outcome B. Both exact nested receiver branches now imply that the
complementary allocation factor `s` is a sixth-power residue modulo `r^49`.
This is an endpoint-independent necessary test. In particular, if `3 | r`,
primitive allocation data force `s=1 mod 3`.

The independent allocation `r=3, s=630008, M=1890024` passes all preceding
GN-side arithmetic guards and fails this new support test. Both exact
scalar branches at this allocation are therefore excluded. The modulus-one
allocation at the old calibration `M=64002` remains unexcluded by the new
sieve. Neither calibration instantiates an actual source packet.

Adding this sieve preserves exact equivalence, in both directions, with
the 047 filtered receiver and the source-indexed depth-four reconstruction
obligation. All exact GN/alternating equalities, primitive endpoint data,
divisor support, coarse size guards, residue-seven condition, strict
thresholds and alternating upper band remain present.

There is no global source exclusion, endpoint existence, or one-step
descent result. No recursion or Legendre development was introduced.
Optional ordered alternating endpoint uniqueness was investigated through
the existing polynomial identity; it was not formalized in this checkpoint.

## Implementation and reused source

New production:
[SevenRamifiedFusionSixthPowerAllocationSieve.lean](../../../DkMath/FLT/Seven/SevenRamifiedFusionSixthPowerAllocationSieve.lean).
New calibration:
[SixthPowerAllocationSieveCalibration.lean](../../../DkMathTest/FLT/Seven/SixthPowerAllocationSieveCalibration.lean).
All 14 new public production declarations, including the two definitions,
are checked in
[SixthPowerAllocationSieveAxiomAudit.lean](../../../DkMathTest/FLT/Seven/SixthPowerAllocationSieveAxiomAudit.lean).
The Seven facade exports the production module; its direct import count
is now 196.

The proof reuses the GN full-gap congruence from 044, the alternating
full-sum congruence and endpoint symmetry from 045, the fixed allocation
predicates and complementary-root identity from 046, and the complete
residue/band receiver from 047. Existing production definitions and proofs
in those modules were retained. SHA256 and HEAD equality checks cover 19
unchanged repository source files. Four local Mathlib source fingerprints
cover ZMod, finite-field, natural ModEq and natural GCD APIs.

New Lean files follow the project copyright/import header and include
`#print "file: ..."` immediately after the import block.

## Exact modular theorem

`exists_sixth_power_residue_of_fortyNinth_power` proves, for natural numbers:

```lean
Nat.Coprime r s ->
Nat.ModEq (r ^ 49) (s ^ 49) (w ^ 6) ->
exists t : Nat, Nat.ModEq (r ^ 49) (t ^ 6) s
```

For `r != 0`, work in the ring `ZMod (r^49)`. Coprimality gives
`Nat.Coprime s (r^49)`. Mathlib's `ZMod.coe_mul_inv_eq_one` supplies the
inverse `i=s^(-1)` and proves `s*i=1`; the modulus is not assumed prime.
Choose the ring element `a=w*i^8`. Then

```text
a^6 = w^6*i^48
    = s^49*i^48
    = s*(s*i)^48
    = s.
```

The exponent identity and ring rearrangement are checked by `ring`.
Take the natural representative `t=a.val`; `ZMod.natCast_zmod_val` and
`ZMod.natCast_eq_natCast_iff` transport the equality to `Nat.ModEq`.
No field cancellation or unproved lifting step is used.

For `r=0`, coprimality forces `s=1`, and `t=1` proves the conclusion even
for modulus zero. For `r=1`, modulus one imposes no restriction on `s`.
`sixthPowerAllocationSieve_mod_one` explicitly proves this for every
natural complement, with witness zero. Witness positivity is not required
by a modular support condition.

`SixthPowerAllocationSieve r s` is precisely the existential conclusion
above. `nested_full_gap_sixth_power_sieve` first reduces the existing
congruence modulo `D=7^27*r^49` to modulus `r^49`. For GN the endpoint is
`u`. For the alternating branch, commutativity swaps the endpoints and
`u<D` proves `(D-u)+u=D`, so the established full-sum theorem supplies
`u^6` as the corresponding sixth power.

`nestedAllocation_sixth_power_sieve` handles either exact branch at a
fixed allocation, provided `Nat.Coprime r (M/r)`. Its contrapositive,
`nestedAllocation_excluded_of_sixth_power`, excludes both branches when
the allocation-only support test fails.

## Prime reduction and the factor three

`sixthPowerAllocationSieve_reduce` proves

```text
q | r -> SixthPowerAllocationSieve r s
  -> exists t, t^6 congruent to s modulo q.
```

This works for every divisor `q`, and hence for all prime divisors, using
`q | r^49`. Primality is unnecessary for this reduction.

`sixthPowerAllocationSieve_mod_three` adds coprimality and `3 | r` to
conclude `Nat.ModEq 3 s 1`. Coprimality first gives `3` not dividing `s`.
If the reduced witness `t` were divisible by three, its sixth power and
then `s` would be divisible by three, a contradiction. Fermat's little
theorem gives `t^2=1 mod 3`; taking its cube gives `t^6=1 mod 3`.
`nestedAllocation_mod_three` exports this consequence for either branch.
This proof uses a nonzero unit witness, rather than assuming that every
sixth power modulo three is one.

## Exact receiver integration

The new `SixthPowerSievedNestedCondition M` is:

```text
exists r in M.divisors,
  Nat.Coprime r (M/r),
  7^3*r^7 < M,
  Nat.ModEq 7 (M/r) 1,
  SixthPowerAllocationSieve r (M/r),
  (
    7^161*r^343 < M^49 and NestedGNAllocationCondition M r
    OR
    M^49 < 7^161*r^343 and
    7^161*r^343 <= 64*M^49 and NestedRHSAllocationCondition M r
  ).
```

`residueSievedNestedCondition_iff_sixth_power_sieved` proves equivalence
with `ResidueSievedNestedCondition M` for every natural `M`. The forward
direction derives support from the chosen exact branch and coprimality.
The reverse direction forgets only the new necessary support condition.
It retains the original allocation and the exact endpoint witness.

`internalDepthFourReconstruction_iff_sixth_power_sieved` composes this
with the already established source-indexed 047 equivalence. Thus the new
preliminary test is stronger, while the complete exact receiver remains
equivalent to reconstruction. Support by itself is never asserted to be
sufficient for either scalar equation.

## Independent regressions

Sixteen new kernel-checked declarations cover the following cases:

- The general inverse theorem, modulus zero, and modulus one for every
  complement.
- Necessity of coprimality: `r=s=3, w=0` satisfies the powered congruence
  modulo `3^49`, but has no sixth-power witness for `s` modulo `3^49`.
  Reduction modulo nine and the nine possible residues prove failure.
- For `r=3, s=630008, M=1890024`, the exact product, divisor membership,
  quotient, coprimality, both seven-unit conditions, `s=1 mod 7`,
  `343*r^7<M`, and `7^161*r^343<M^49` all hold. These numerical facts use
  kernel `decide`, including the large finite powers.
- `630008 % 3 = 2`; support would force residue one. The new support test
  fails, and neither exact branch can exist at this allocation.
- At `M=64002`, the old `r=2` exclusion remains available. The `r=1`
  allocation retains its coprimality, coarse bound, residue-seven and GN
  threshold guards and satisfies the modulus-one support condition. No
  endpoint solution is constructed for it.
- General divisor reduction, the both-branch mod-three consequence, both
  directions of filtered equivalence and the actual-source specialization.
- The arithmetic identity `3*2=3*2` with coprime factors permits three in
  the first factor and its corresponding outer root. This does not
  instantiate a source packet.
- An inhabited sieve at `r=s=1` does not supply the exact receiver at `M=1`;
  the already proved coarse-bound obstruction still excludes that receiver.

These calibrations supply independent pruning evidence and boundary
checks. They are not FLT7 counterexamples or source witnesses.

## Actual source prime-support effect

Let `M=internalDepthFourSeventhCore p` and let the existing packet provide
`N>0` with

```text
M*N = verticalGapRoot*compensationRoot,
Nat.Coprime M N,
7 does not divide N.
```

For any prime `q | r` and supported divisor `r | M`,
`allocation_prime_support_of_coprime_product` proves

```text
q does not divide N,
q divides verticalGapRoot OR q divides compensationRoot.
```

`internalDepthFourAllocation_prime_support` specializes this to the actual
packet and returns the same complementary root `N`, product identity,
coprimality and seven-unit data together with these support consequences.
The existing seven-unit source theorem also excludes `q=7` from `r`.

The product and coprimality locate prime support and separate it from
`N`; they do not by themselves forbid `q=3`, bound `M`, or determine the
sixth-power class of `s=M/r`. The standalone coprime product calibration
shows why excluding three merely from these two identities would be
invalid. No additional theorem forcing an incompatible class for every
actual supported allocation was obtained. Consequently these source facts
do not turn the new necessary condition into terminal exclusion or descent.

## Builds, axioms and audit

All four measured builds completed successfully with `LEAN_NUM_THREADS`
removed from the environment. Commands and GNU time telemetry are retained
in `logs/*-048.*`; no thread-limited retry was needed.

| Build | Elapsed seconds | Maximum RSS, KiB | Exit |
| --- | ---: | ---: | ---: |
| focused | 7.050 | 979284 | 0 |
| axiom-audit | 12.437 | 6742648 | 0 |
| facade | 12.916 | 6810904 | 0 |
| root | 18.567 | 7099504 | 0 |

The focused build checks the new production module and calibration and
retains the 047 calibration; it reports 9089 jobs. The axiom audit reports
9087 jobs, the complete Seven facade 9285, and the root `DkMath` build
10449. These counts include replayed dependencies. The final focused
measurement reused the already compiled successful implementation and
calibration; its elapsed time is not a fresh compilation benchmark.

Every new public production declaration is included in the explicit
`#print axioms` audit. Only `propext`, `Classical.choice`, and `Quot.sound`
occur; none depends on `sorryAx`. The focused and axiom-audit logs contain
no warnings. The facade reports four existing declaration-with-`sorry`
warnings in `ZsigmondyCyclotomicResearch`, `TriominoCosmicBranchA`,
`GcdNextResearch`, and `CyclotomicPrincipalization`; the root additionally
reports the existing `TriominoFLT` warning. Those unchanged research
modules are outside the new declaration dependency audit.

[check-048.py](checks/check-048.py) checks declaration coverage, all four
Lean headers, forbidden constructs, unchanged source fingerprints, the
four successful builds, the axiom whitelist, ASCII report/log artifacts,
and `git diff --check`. Its retained output is `logs/check-048.txt`.
No new packet structures or Legendre imports were added.

## Next implementation proposals and mathematical frontier

The following are reasoned proposals, not additional implemented results.

1. Formalize ordered alternating endpoint uniqueness using the existing
   fixed-sum/product polynomial. Put `t=x*(D-x)` and
   `F(t)=D^6-7*D^4*t+14*D^2*t^2-7*t^3`. For
   `0<x1<x2<=D/2`, the product difference is
   `(x2-x1)*(D-x1-x2)>0`, so `0<t1<t2<=D^2/4`. The finite polynomial
   difference factors as

   ```text
   F(t1)-F(t2) = 7*(t2-t1)*
     [D^4-2*D^2*(t1+t2)+t1^2+t1*t2+t2^2].
   ```

   The first two terms in brackets have nonnegative sum, and `t2^2>0`.
   This suggests a strict decrease on the ordered half interval and then
   at most one ordered endpoint for a fixed allocation and target.
   Implement the product-order lemma and integer polynomial inequality
   before transporting them back to the natural alternating receiver.
   Kernel-check the difference factorization and midpoint cases. This
   needs no calculus and supplies uniqueness, not existence or exclusion.

2. Use the proved source support localization to seek a source theorem
   about the sixth-power class of `M/r` at a prime actually dividing `r`.
   A useful exclusion bridge must provide a supported prime with an
   incompatible class; prime membership in an outer root alone is
   insufficient. Keep that premise explicit until proved from packet
   data. Do not add a series of unrelated modular filters or assume that
   every allocation has a factor three. In particular, `r=1` has no prime
   support and the new sieve intentionally gives no obstruction there.

The remaining central obstacle is the exact scalar equality at surviving
allocations. Local support and endpoint uniqueness would organize that
problem but would not prove it impossible without additional source
arithmetic or a proved descent step.
