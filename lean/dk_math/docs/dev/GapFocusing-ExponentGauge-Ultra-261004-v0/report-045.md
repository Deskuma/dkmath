# Report 045 - symmetric forty-ninth-power reconstruction receivers

## Result and scope

Outcome B. Both reconstruction branches now have exact scalar receivers
over the same source core `M`, the same coprime allocation `M=r*s`, and the
same large scale `D=7^27*r^49`. The alternating branch is equivalent to its
one-variable receiver, including the exact positive primitive Fermat equation
in the reverse direction. Its normalized residual has a congruence modulo
the entire sum `D`, rather than only `D/7`.

For the actual source, the factors are seven-units and the sum has exact
seven-adic depth 27. An analogous division-free away-root comparison is also
proved. Endpoint exchange permits a canonical order `u<=v`; uniqueness on
that half interval was not proved in this checkpoint.

Neither receiver is asserted to be inhabited. No contradiction, unconditional
counterexample reconstruction, one-step descent, terminal exclusion, recursive
descent, or new FLT7 theorem was obtained. Legendre remains parked.

## Common arithmetic allocation and preserved APIs

[SevenAdicNestedPowerSplit.lean](../../../DkMath/FLT/Seven/SevenAdicNestedPowerSplit.lean)
now exposes `exists_nested_seventh_allocation`. Its inputs are positive
natural `a,b`, `Nat.Coprime a b`, `7` not dividing `b`, and the exact identity

```text
7^4*M^7 = 7*a*b.
```

It proves positive coprime `r,s` with

```text
a = 7^3*r^7,
b = s^7,
M = r*s.
```

This is the arithmetic proof from 044 extracted without changing its
mathematical argument. It applies the existing coprime seventh-power
extraction to `(7^4*a)*b=(7*M)^7`, writes the exceptional root as `7*r`,
cancels powers of seven, and uses injectivity of natural seventh powers.

`SevenAdicPowerSplit.exists_nested_seventh_roots` retains its existing
signature and becomes a thin application of this helper. The new
`PrescribedCarrierAlternatingPowerSplit.exists_nested_seventh_roots` uses
the very same helper. No second Row-Z factorization or new packet structure
was introduced.

The new projection `PrescribedCarrierAlternatingPowerSplit.seven_not_dvd_b`
exposes the missing residual-unit fact. It uses the primitive endpoint,
`7 | u+v`, and the existing signed cyclotomic theorem excluding divisibility
by 49. If `7 | b`, the split identity `alt(u,v)=7*b^7` would violate that
theorem. The existing split constructor and its fields were not changed.

[source-audit-045.json](evidence/MANIFEST.md#log-d6d4c24e4d3431c6) records 13 relevant existing
sources and verifies their contents against HEAD, including the alternating
split, primitive cyclotomic depth, 044 receiver, source norm packet, exact
reconstruction obligation, and away coordinate ledger.

## Alternating identities and the exact scalar equivalence

For `source : CounterexamplePack u v (7^4*M^7)`, the existing split supplies

```text
u+v = 7^6*A^7,
alt(u,v) = 7*B^7,
7^4*M^7 = 7*A*B.
```

Here `alt` denotes the natural `alternatingCyclotomicSeven`. Substitution
of the common nested allocation gives the exact natural equalities

```text
u+v = 7^27*r^49,
alt(u,v) = 7*s^49.
```

These are `PrescribedCarrierAlternatingPowerSplit.nested_sum_residual`.
The exponents arise from `6+3*7=27` and `7*7=49`.

[SevenRamifiedFusionSymmetricReconstruction.lean](../../../DkMath/FLT/Seven/SevenRamifiedFusionSymmetricReconstruction.lean)
defines the thin proposition `NestedRightHandSideCondition M`:

```text
exists r,s,u,
  r>0, s>0, 0<u<D,
  M=r*s,
  Nat.Coprime r s,
  Nat.Coprime u D,
  alt(u,D-u)=7*s^49,
where D=7^27*r^49.
```

`rightHandSideChart_iff_nested` proves

```text
(exists u,v, CounterexamplePack u v (7^4*M^7))
  iff NestedRightHandSideCondition M.
```

Forward extraction retains positivity, coprimality, and the actual nested
identities. The equality `u+v=D` gives `v=D-u`. Coprimality with `D` follows
from primitive endpoint coprimality through the gcd addition theorem.

Conversely, set `v=D-u`. The strict interval proves `v>0` and `u+v=D`.
`Nat.coprime_sub_self_right` transports `Nat.Coprime u D` to
`Nat.Coprime u (D-u)`. The existing alternating identity then gives

```text
u^7+v^7 = D*alt(u,v)
        = (7^27*r^49)*(7*s^49)
        = (7^4*(r*s)^7)^7
        = (7^4*M^7)^7.
```

Together with positivity of `7^4*M^7`, this constructs all fields of the
CounterexamplePack conditionally on the receiver. A congruence is not used
as a substitute for its exact Fermat equality. The equivalence holds for
every natural `M`; at `M=0`, both sides are empty by positivity.

## Normalization with the full sum modulus

The existing integer expansion is

```text
alt(x,y) = D*P(D,y) + 7*y^6,
P(D,y) = D^5 - 7*D^4*y + 21*D^3*y^2
       - 35*D^2*y^3 + 35*D*y^4 - 21*y^5,
D=x+y.
```

The casts into integers are essential: this expression has signed
coefficients. If `D=7*k`, define the integer polynomial

```text
Q = k*D^4 - D^4*y + 3*D^3*y^2
  - 5*D^2*y^3 + 5*D*y^4 - 3*y^5.
```

The Lean proof checks by polynomial arithmetic that

```text
alt(x,y) = 7*(y^6+D*Q).
```

It first proves exact divisibility of the natural residual by seven, then
casts the exact natural division identity to integers and cancels seven.
Thus the difference between `alt/7` and `y^6` is an integer multiple of `D`,
even when `Q` is negative. No truncated natural subtraction of the signed
polynomial is used.

`alternatingCyclotomicSeven_div_seven_modEq_sum` proves, for any natural
endpoints with `7 | x+y`,

```text
Nat.ModEq (x+y) (alt(x,y)/7) (y^6).
```

No positivity or primitive hypothesis is required by this congruence;
the zero-sum boundary also remains valid. `nestedAlternatingResidual_full_sum_congruence`
specializes the exact identities to

```text
alt(u,v)/7 = s^49,
s^49 congruent to v^6 modulo 7^27*r^49.
```

Endpoint exchange gives the corresponding congruence with `u` as well.
These are necessary consequences of the receiver, not existence criteria.

## Source specialization and the matched disjunction

The core remains the source chosen in 044:

```text
M = internalDepthFourSeventhCore p
  = natAbs (the existing norm packet.innerSndRoot),
internalDepthFourCarrier p = 7^4*M^7,
7 does not divide M.
```

`internalDepthFourRightHandSide_nested_normal_form` specializes a hypothetical
right-hand-side chart to positive coprime `r,s`, `M=r*s`, both seven-unit
conditions, the exact sum/residual identities, exact sum depth 27, and the
normalized congruence modulo the full sum. The seven-unit facts descend from
the actual source `M=r*s`, rather than from a generic depth assertion.

The main theorem is
`internalDepthFourReconstruction_iff_two_nested_receivers`:

```text
InternalDepthFourCounterexampleReconstructionObligation p
  iff
NestedPrescribedSummandCondition (internalDepthFourSeventhCore p)
  OR
NestedRightHandSideCondition (internalDepthFourSeventhCore p).
```

Both branches therefore share `M=r*s` and `D=7^27*r^49`, and require the
same residual target `7*s^49`. Their equations and endpoint domains differ:

| Branch | Exact equation | Endpoint geometry |
| --- | --- | --- |
| Prescribed summand | `GN 7 D u = 7*s^49` | `u>0`, primitive with `7*M`, endpoint `u+D` |
| Right-hand side | `alt(u,D-u) = 7*s^49` | `0<u<D`, primitive with `D`, endpoint `D-u` |

The previous impossible endpoint-sum carrier chart stays excluded by its
existing theorem. Neither of the two remaining scalar receivers is removed
or constructed by this disjunction.

## Symmetry and away-root comparison

`alternatingCyclotomicSeven_comm` proves exact endpoint symmetry.
`nestedRightHandSideCondition_iff_ordered` proves that a receiver can always
be represented with `u<=D-u`. If its original endpoint is larger, the proof
exchanges `u` and `D-u`, transporting the primitive gcd condition by the
subtraction lemma. This is equivalently the half interval `u<=D/2`.

No strict monotonicity, ordered endpoint uniqueness, or unordered pair
uniqueness theorem for the alternating receiver was proved. The 044 GN
endpoint uniqueness remains available and its calibration was rebuilt.

For a supplied `AwayValuationTransferPacket u v c` and its alternating
split, write `S=natAbs awayRoot.snd` and
`T=natAbs (seventhPowerSndCore awayRoot.fst awayRoot.snd)`. The existing
ledger is `v*c*(v+c)=7*S*T`. Substitution of `c=7*A*B` and cancellation
of seven prove

```text
A * (B*v*(v+c)) = S*T,
7 does not divide B*v*(v+c),
7 does not divide T.
```

This is `AwayValuationTransferPacket.rightHandSide_root_unit_comparison`.
The unit multiplier follows from `B` being a seven-unit, primitive endpoint
arithmetic, and `7 | c`. The core-unit fact is already part of the away
normal form. Here seven-unit means not divisible by seven, not an integer
unit `+1` or `-1`. This comparison does not prove `A=S`, associate equality,
or that the old quadratic inner root can serve as the new away root.

## Validation performed

One production module and two calibration/audit modules were added. The
shared 044 production module was refactored, and the FLT Seven facade gained
one import; it now has 193 direct imports and its full closure was built.
All five affected Lean files retain the uniform header and the project
`#print "file: ..."` marker immediately after imports.

There are 13 new production declarations: one definition and 12 theorems.
The audit prints axioms for all of these and all seven existing public
theorems in the shared module, including its refactored wrapper. All 20
dependencies are contained in `propext`, `Classical.choice`, and `Quot.sound`;
there is no `sorryAx` in the audit. No custom axiom, sorry, admit, native
decision, unsafe implementation, or new factor packet was introduced.

The 13 new kernel regressions check a signed numerical residual and its
exact division, nontrivial full-sum moduli 7 and 14, the zero-sum boundary,
endpoint exchange, packet-independent allocation, primitive gcd transport,
absence at core zero, exact chart equivalence, the nested congruence, and
preservation of both reconstruction branches. The focused build also
rebuilt the existing ten 044 calibration declarations after the shared
helper refactor. No regression instantiates an actual FLT7 counterexample.

All four final builds succeeded with `LEAN_NUM_THREADS` unset. The retained
[build-045.py](checks/build-045.py) records GNU time resource usage including
waited descendants; maximum RSS is not aggregate concurrent peak memory.

| Build | Lake target(s) | Jobs | Seconds | Maximum RSS KiB | Swaps |
| --- | --- | ---: | ---: | ---: | ---: |
| Focused | symmetric reconstruction, new and 044 calibration | 9085 | 13.255 | 6777960 | 0 |
| Axiom audit | SymmetricReconstructionAxiomAudit | 9084 | 12.493 | 6738604 | 0 |
| FLT facade | DkMath.FLT.Seven | 9282 | 12.791 | 6811976 | 0 |
| Root | DkMath | 10446 | 18.365 | 7097512 | 0 |

Focused and axiom builds emitted no warnings. Facade and root builds replayed
the same four and five existing sorry warnings, respectively:
ZsigmondyCyclotomicResearch at 147, TriominoCosmicBranchA at 4187,
GcdNextResearch at 850, CyclotomicPrincipalization at 5389, and additionally
TriominoFLT at 1919 for the root. These files were unchanged; this is not
a repository-wide sorry-free claim.

[check-045.py](checks/check-045.py) verifies declaration coverage, source
fingerprints, all five headers, forbidden constructs, build records,
standard axiom dependencies, ASCII report/log artifacts, and whitespace.

## Next implementation proposal

The next frontier is an exact scalar obstruction over source-supported
factor allocations. The following are proposals, not additional Lean
theorems implemented or checked in this checkpoint.

1. Prove a common size filter for both receivers. The GN expansion gives
   `D^6 <= GN 7 D u`. For the alternating branch, use the existing Mathlib
   `add_pow_le` in `Mathlib/Algebra/Order/Ring/Basic.lean` at exponent seven:
   `(u+v)^7 <= 64*(u^7+v^7)`. Since `D=u+v>0` and the exact alternating
   identity holds, cancellation gives `D^6 <= 64*alt(u,v)`. Both receivers
   should therefore imply `D^6 <= 64*7*s^49`. Comparing this with
   `D^6=7^162*r^294` excludes `s<=7^3*r^6`, since `64<7^14` and `r>0`.
   The resulting proposed common necessary conditions are
   `s>7^3*r^6` and `M>7^3*r^7`. This would rigorously prune allocations
   and give a bounded exclusion for `M<=343`; it would not exclude all
   source cores without further source-specific information.
2. Prove uniqueness of the canonical alternating endpoint with a small
   polynomial argument. At fixed sum, set `t=u*v`. The candidate signed
   identity is `alt=D^6-7*D^4*t+14*D^2*t^2-7*t^3`. On `u<=v`, the product
   increases strictly with `u`, with `0<=t<=D^2/4`. For `t1<t2`, the
   difference of residuals factors as
   `7*(t2-t1)*(D^4-2*D^2*(t1+t2)+t1^2+t1*t2+t2^2)`, whose bracket is
   positive in this interval. Formalize the identity and order proof over
   integers or rationals, then transport back to naturals. This targets
   one unordered pair per allocation without a general calculus framework.
3. Give both receivers a common finite supported API with `r` in
   `M.divisors`, `s=M/r`, and `Nat.Coprime r (M/r)`. The GN branch already
   has this divisor receiver. Combine a corresponding alternating divisor
   receiver with the proposed size filter and canonical order. If the
   uniqueness proof succeeds, each allocation has at most one candidate in
   each branch. A binary search or exact decision certificate must still
   verify the full residual equality and primitive conditions; congruence
   filtering alone cannot construct a reconstruction witness.

The source must ultimately either supply an exact scalar solution or impose
an obstruction eliminating every allowed allocation in both branches.
The matched disjunction and the away-root comparisons do not supply that
missing theorem, and recursive descent should remain deferred.
