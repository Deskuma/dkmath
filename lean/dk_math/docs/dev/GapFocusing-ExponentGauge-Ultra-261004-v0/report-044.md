# Report 044 - nested seven-adic reconstruction normal form

## Result and scope

Outcome B. The prescribed-summand branch is now equivalent to a nested
factor-allocation condition with one exact GN equation. The second extraction
proves `a=7^3*r^7`, `b=s^7`, and `M=r*s`, with positive coprime factors.
For the actual depth-four source, both factors are seven-units, the gap has
exact seven-adic depth 27, and its residual is seven times a forty-ninth power.

The normalized residual satisfies the requested congruence modulo
`7^26*r^49`, and a stronger congruence modulo the entire gap `7^27*r^49`.
There is also an exact division-free comparison of the exceptional factor
with the reconstructed away root through seven-unit multipliers.

No chart or new away packet was constructed unconditionally. No contradiction,
actual one-step descent, recursive descent, or FLT7 theorem was obtained.
Legendre remains parked; no Legendre production module was changed or imported.

## Source identity and audited reuse

The new source core is

```text
M = internalDepthFourSeventhCore p
  = natAbs (p's existing signed norm packet.innerSndRoot).
```

The existing `RamifiedRealCubicNormPacket.innerSnd_eq` is an integer identity
`quadratic.innerRoot.snd = 7^4 * innerSndRoot^7`. Applying natural absolute
value proves

```text
internalDepthFourCarrier p = 7^4 * M^7.
```

This uses the previously constructed root, not a new factorization inferred
from depth alone. The existing `innerSndRoot_not_seven_dvd` proves `7` does
not divide `M`; its positivity follows. These facts are exported as
`internalDepthFourCarrier_eq_seven_pow_four_mul_core_pow`,
`internalDepthFourSeventhCore_not_seven_dvd`, and
`internalDepthFourSeventhCore_pos`.

The source audit reused SevenAdicPowerSplit, generic PrimeAdicPowerSplit,
`seventh_power_factor_split`, the underlying `power_factor_split`, the
quadratic-inner-root/norm packet, the existing prescribed-carrier ramified
resolution, the 043 chart receiver, and the GN/away coordinate ledgers.
[source-audit-044.json](evidence/MANIFEST.md#log-14c0924b8fdf4f80) retains fingerprints of
15 relevant existing source files. No new factorization framework or packet
structure was introduced.

## Hypothetical ramified chart and nested extraction

Let `c=7^4*M^7` and assume `CounterexamplePack u c v`. In particular all three
naturals are positive, `Nat.Coprime u c`, and `u^7+c^7=v^7`.

`nonempty_ramified_of_seven_dvd_second` exchanges the two summands and
constructs the existing ramified normal form for `(c,u,v)`. Its existing
residual power split supplies positive coprime `a,b` satisfying

```text
v-u = 7^6*a^7,
GN 7 (v-u) u = 7*b^7,
c = 7*a*b,
7 does not divide b.
```

The new `CounterexamplePack.prescribedSummand_nested_split` retains this
exact `SevenAdicPowerSplit` witness as provenance. The extraction theorem is
`SevenAdicPowerSplit.exists_nested_seventh_roots` in
[SevenAdicNestedPowerSplit.lean](../../../DkMath/FLT/Seven/SevenAdicNestedPowerSplit.lean).

The proof uses only exact arithmetic and the existing coprime-power theorem:

1. Cancel one seven in `7^4*M^7=7*a*b` to obtain `a*b=7^3*M^7`.
2. Thus `(7^4*a)*b=(7*M)^7`. These two factors are coprime because
   `Nat.Coprime a b` and `7` does not divide `b`.
3. `seventh_power_factor_split` produces `7^4*a=R^7` and `b=s^7`.
4. Primality of seven forces `7 | R`. Write `R=7*r` and cancel `7^4`:
   `a=7^3*r^7`.
5. Substitute into the distinguished-carrier identity and use injectivity
   of the natural seventh-power map to obtain `M=r*s`.

The original positive factors prove `r,s>0`; coprimality descends through
divisibility. For the current source, `7` cannot divide either `r` or `s`
because it cannot divide `M=r*s`. The argument does not rely on an informal
unique-factorization allocation or a valuation-only substitute.

## Exact gap, residual and congruences

`SevenAdicPowerSplit.nested_gap_residual` proves

```text
v-u = 7^27*r^49,
GN 7 (v-u) u = 7*s^49.
```

The first exponent is `6+3*7=27`; the nested root exponent is `7*7=49`.
Since `r` is a seven-unit, `nestedFactor_exact_depths` proves

```text
padicValNat 7 a = 3,
padicValNat 7 (v-u) = 27.
```

The source-indexed theorem `internalDepthFourSummand_nested_normal_form`
packages positive coprime `r,s`, the exact core product, both seven-unit
conditions, the gap/residual identities, gap depth 27, and both congruences.

The existing explicit expansion is

```text
GN 7 d u = d*P(d,u) + 7*u^6,
P(d,u) = d^5 + 7*d^4*u + 21*d^3*u^2
       + 35*d^2*u^3 + 35*d*u^4 + 21*u^5.
```

`GN_seven_div_seven_eq_head_add`, for `7 | d`, proves the division-safe equality

```text
GN 7 d u / 7 = u^6 + (d/7)*P(d,u).
```

Exact divisibility of the GN expression by seven is proved before dividing.
This gives `GN/7` congruent to `u^6` modulo `d/7`. Substitution and exact
division of `7*s^49` give

```text
GN 7 (7^27*r^49) u / 7 = s^49,
s^49 congruent to u^6 modulo 7^26*r^49.
```

There is a further exact gain: when seven divides `d`, it also divides every
term of `P(d,u)`, including `d^5`. Consequently `(d/7)*P=d*(P/7)`, and
`GN_seven_div_seven_modEq_gap` proves the stronger full-gap congruence.
`nestedResidual_full_gap_congruence` specializes it to

```text
s^49 congruent to u^6 modulo 7^27*r^49.
```

Both modulus statements use `Nat.ModEq`; no replacement by an approximate
or bounded-depth congruence is made. These congruences are necessary
consequences, not sufficient substitutes for the exact GN equation.

## Equivalent arithmetic receiver and finite factor support

[SevenRamifiedFusionNestedReconstruction.lean](../../../DkMath/FLT/Seven/SevenRamifiedFusionNestedReconstruction.lean)
defines `NestedPrescribedSummandCondition M` by

```text
exists r,s,u > 0,
  M=r*s,
  Nat.Coprime r s,
  Nat.Coprime u (7*M),
  GN 7 (7^27*r^49) u = 7*s^49.
```

`prescribedSummandChart_iff_nested` proves equivalence with
`exists u,v, CounterexamplePack u (7^4*M^7) v`. This is not only a necessary
condition. In the reverse direction, set `d=7^27*r^49`, `v=u+d`. Then

```text
d*GN 7 d u = 7^28*r^49*s^49 = (7^4*M^7)^7.
```

The existing cosmic identity gives `u^7+c^7=v^7`. Positivity is supplied by
the receiver, and coprimality with `7*M` gives coprimality with `7^4*M^7`.
Thus all five CounterexamplePack fields are constructed conditionally on
the displayed arithmetic receiver. No GN congruence is used in place of
the required exact equality.

For positive `M`, `nestedPrescribedSummandCondition_iff_divisor` replaces
`(r,s)` by `r` in `M.divisors`, with `s=M/r` and
`Nat.Coprime r (M/r)`. This is a finite supported factor allocation rather
than arbitrary endpoint pairs below `c^2`.

Furthermore, `GN_seven_unit_strictMono` proves strict monotonicity of
`GN 7 d u` in `u`, for every fixed natural `d`. Its head `7*u^6` strictly
increases, while the remaining terms are nondecreasing.
`nestedResidual_unit_unique` therefore proves that each fixed factor
allocation `(r,s)` admits at most one endpoint `u` solving the residual
equation. This materially reduces the mathematical search space to
supported factor allocations with a unique-or-absent scalar solution.

No large pair enumeration or brute-force decision procedure was implemented.
Uniqueness does not construct the endpoint or prove that any allocation works.

## Relation to the reconstructed away root

Let an actual `AwayValuationTransferPacket u c v` be supplied, together with
the corresponding `SevenAdicPowerSplit c u v`. Write

```text
S = natAbs awayRoot.snd,
T = natAbs (seventhPowerSndCore awayRoot.fst awayRoot.snd).
```

The existing endpoint ledger is `c*v*(c+v)=7*S*T`. Substituting `c=7*a*b`
and cancelling seven proves the new exact identity

```text
a * (b*v*(c+v)) = S*T.
```

`AwayValuationTransferPacket.prescribedSummand_root_unit_comparison` also
proves that both `b*v*(c+v)` and `T` are not divisible by seven.
The first uses the residual-unit property of `b`, primitive endpoint
coprimality, and `7 | c`; the second is the existing away core-unit theorem.

This is a division-free equality through seven-unit multipliers. It is
stronger than a mere equality of depths. Here seven-unit means an integer
not divisible by seven; it does not mean an integer unit `+1` or `-1`.
Neither `a=S` nor equality up to an integer unit was proved. With the current
carrier, both have depth three, consistently with instruction 043.
No such route has been constructed unconditionally, and the old quadratic
inner root still cannot be reused as this new away root.

## Right-hand-side branch is retained

The reconstruction obligation is now explicitly equivalent to

```text
NestedPrescribedSummandCondition (internalDepthFourSeventhCore p)
  OR
exists u,v, CounterexamplePack u v (internalDepthFourCarrier p).
```

This is `internalDepthFourReconstruction_iff_nested_or_left`. The existing
endpoint-sum carrier branch is excluded by its previous theorem. The second
branch above remains unresolved and was not silently discarded.

For that branch, seven divides the right-hand side `c`. The original natural
chart is away: the other endpoint is a seven-unit and the gap `c-v` is not
divisible by seven. The existing chart-to-route bridge constructs its away
normal form and prescribed left carrier conditionally on the primitive
Fermat packet.

For ramified re-entry, `seven_dvd_sum_of_seven_dvd_third` proves `7 | u+v`.
`PrescribedCarrierAlternatingPowerSplit` already supplies positive coprime
`A,B` with

```text
u+v = 7^6*A^7,
alternatingCyclotomicSeven u v = 7*B^7,
c = 7*A*B.
```

The existing prescribed-carrier ramified summit uses the signed chart
`(u,-v,c)`. Its construction also proves the stripped alternating residual
is a seven-unit. This checkpoint did not promote a second nested normal-form
receiver for that alternating branch or exclude it. The existence obligation
continues to be a disjunction.

## Validation performed

Two production modules and two test/audit modules were added. One import was
added to the FLT Seven facade. The facade now has 192 direct imports; its full
import closure was built. All five affected Lean files retain the project
header and the `#print "file: ..."` marker immediately after imports.

The new production surface has 21 public declarations: two definitions and
19 theorems. All were audited with `#print axioms`; dependencies are contained
in `propext`, `Classical.choice`, and `Quot.sound`, without `sorryAx`.
No custom axiom, sorry, admit, native decision, unsafe implementation, or new
parallel packet structure was introduced.

The ten kernel regressions check the normalized value at gap seven, a
nontrivial full-gap congruence, zero-gap normalization, whole-prime-power
coprime divisor allocation at core 12, endpoint uniqueness, the large modulus,
exact depths 3 and 27, the summand equivalence, the divisor receiver, and
preservation of the full reconstruction disjunction. They do not instantiate
an actual FLT7 counterexample.

All four final builds succeeded with `LEAN_NUM_THREADS` unset. Measurements
are retained by [build-044.py](checks/build-044.py); GNU time resource usage
includes waited descendants and does not represent aggregate concurrent peak
memory.

| Build | Lake target(s) | Jobs | Seconds | Maximum RSS KiB | Swaps |
| --- | --- | ---: | ---: | ---: | ---: |
| Focused | nested reconstruction and calibration | 9083 | 13.603 | 6776244 | 0 |
| Axiom audit | NestedReconstructionAxiomAudit | 9083 | 13.973 | 6737908 | 0 |
| FLT facade | DkMath.FLT.Seven | 9281 | 12.994 | 6811984 | 0 |
| Root | DkMath | 10445 | 18.464 | 7094848 | 0 |

Focused and axiom builds emitted no warnings. The facade replayed four
existing sorry warnings, and the root replayed five: ZsigmondyCyclotomicResearch
at 147, TriominoCosmicBranchA at 4187, GcdNextResearch at 850,
CyclotomicPrincipalization at 5389, plus TriominoFLT at 1919 in the root.
These files were unchanged. This is not a repository-wide sorry-free claim.
[check-044.py](checks/check-044.py) verifies source fingerprints, all declaration
coverage, headers, forbidden constructs, build records, and whitespace.

## Next implementation proposal

The next natural frontier is the exact scalar equation over source-supported
factor allocations, not more generic chart bookkeeping.

1. Give the right-hand-side branch the parallel nested alternating receiver.
   Extract a narrow arithmetic helper from the proved second allocation,
   taking positive coprime `A,B`, `7` not dividing `B`, and
   `7*A*B=7^4*M^7`. Reuse the already proved alternating split to derive
   `u+v=7^27*r^49` and the alternating residual `7*s^49`. This would expose
   both branches in equally source-indexed form while retaining their signs.
2. For the GN branch, combine strict monotonicity and the full-gap congruence
   with exact coefficient inequalities. A candidate is still required to
   satisfy equality, not just a congruence. Necessary bounds from the positive
   head and terminal terms can prune factor allocations before any search.
   A binary-search receiver on the previously proved bounded endpoint range
   could be a small computational API; it would be a decision API, without
   a theorem asserting that a solution exists.
3. Investigate the seven-unit comparison `a*L=S*T` using the explicit
   away coordinate formulas. Any stronger equality or controlled multiplier
   must follow from those formulas; matching seven-adic depth cannot supply it.
   The current equation offers concrete provenance for this audit.

Do not start recursive descent. One-step reconstruction is still uninhabited,
and the common state/measure compatibility required after the ramified/away
transition remains a separate obligation. The next mathematical result must
either construct an exact scalar solution from the actual source or prove
that its source-supported allocations are impossible.
