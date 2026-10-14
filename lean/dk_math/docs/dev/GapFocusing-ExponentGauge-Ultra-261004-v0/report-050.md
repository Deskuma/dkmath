# Report 050 - adjacent sixth-power gnomon gap

## Result and scope

Outcome B. A general symbolic adjacent-sixth-power bracket is proved in
natural arithmetic. For positive `D` and `9*D^2<=Q`, it puts the pure sixth
power `7*Q^6` strictly between `P D (Q-1)` and `P D Q`. Strict monotonicity
therefore excludes every natural center coordinate at that target.

At the nested scale, the infinite conditional family

```text
r>0, 9*r^2<=t, s=t^6
  -> for every natural q, P (7^27*r^49) q !=448*s^49
```

is kernel-checked. It excludes centered candidates and both exact scalar
branches at every allocation `M=r*t^6` satisfying these hypotheses.
The source-free allocation `r=1,t=9,s=M=531441` passes the preceding
allocation-only filters but is now excluded. This is new pruning beyond
048-049, not merely a finite numerical certificate.

The perfect-sixth-power and size assumptions are additional arithmetic
premises. They have not been derived from actual source packets. A source
conditional theorem exhibits the precise family premise that would make
the entire reconstruction receiver empty. Its conclusion is obstruction
of reconstruction, not nonexistence of the original source packet.
No original FLT7 counterexample was ruled out and no valid new counterexample
or one-step descent was constructed. No recursion or Legendre work was added.

## Implementation and preserved interfaces

New production:
[SevenRamifiedFusionCenteredGnomonGap.lean](../../../DkMath/FLT/Seven/SevenRamifiedFusionCenteredGnomonGap.lean).
New calibration:
[CenteredGnomonGapCalibration.lean](../../../DkMathTest/FLT/Seven/CenteredGnomonGapCalibration.lean).
All 15 new public production theorems are explicitly audited in
[CenteredGnomonGapAxiomAudit.lean](../../../DkMathTest/FLT/Seven/CenteredGnomonGapAxiomAudit.lean).
No new receiver definitions, packet structures, or modular filters were
introduced. The 049 centered candidate, selected-branch receiver and source
equivalence remain unchanged. The Seven facade exports the module and
now has 198 direct imports.

The implementation reuses the 049 common polynomial and strict
monotonicity, its complete chart reconstruction, and the actual source
core/divisor APIs. Source audit fingerprints and equality with HEAD cover
26 unchanged repository source files, including the retained 044-049
inventory and four U1.6 interfaces inspected for the logical boundary.
Three local Mathlib fingerprints cover natural, monotone-order and
ordered-ring APIs. New Lean files preserve the project header and the
traditional `#print "file: ..."` after imports.

## Adjacent sixth-power inequality

`adjacent_sixth_power_add_le` proves

```text
Q>0 -> (Q-1)^6 + Q^5 <=Q^6.
```

Write `Q=k+1`. The proof checks the nonnegative-coefficient identity

```text
(k+1)^6 = k^6 + (k+1)^5
          + k*(5*k^4+10*k^3+10*k^2+5*k+1).
```

The last term is nonnegative in naturals. This obtains the inequality
without interpreting a signed difference as truncated subtraction.
`adjacent_sixth_power_sub_ge` then proves the requested form

```text
Q^5 <=Q^6-(Q-1)^6.
```

The regression at `Q=1` includes the equality boundary, and `Q=2` supplies
an independent numerical check.

## Uniform extra-term bound and strict bracket

Recall

```text
P D q = 7*q^6+35*D^2*q^4+21*D^4*q^2+D^6.
```

`centeredSevenSextic_extra_le_fiftySeven` proves, under `D<=Q`,

```text
35*D^2*(Q-1)^4+21*D^4*(Q-1)^2+D^6 <=57*D^2*Q^4.
```

Natural power monotonicity gives `(Q-1)^4<=Q^4` and `(Q-1)^2<=Q^2`.
The second and third bounds use `D^2<=Q^2`:

```text
D^4*(Q-1)^2 <= D^2*Q^4,
D^6 <= D^2*Q^4.
```

Their coefficients sum to `35+21+1=57`. Ring rearrangements and exact
natural multiplication bounds check each comparison.

For `D>0` and `9*D^2<=Q`, positivity gives `Q>0` and
`D<=D^2<=Q`. Moreover,

```text
57*D^2*Q^4 <63*D^2*Q^4 <=7*Q^5.
```

The first inequality is strict because `D^2*Q^4>0`; the second is the
scale hypothesis multiplied by a nonnegative quantity. Combining it with
the adjacent-power inequality proves

```text
P D (Q-1)
  <7*(Q-1)^6+7*Q^5
  <=7*Q^6.
```

The upper inequality `7*Q^6<P D Q` follows from the positive constant
term `D^6` and the other nonnegative terms. Thus
`centeredSevenSextic_adjacent_sixth_bracket` proves the full strict bracket
symbolically, for every natural `D,Q` under the stated hypotheses.

`centeredSevenSextic_no_image_of_adjacent_bracket` is the thin certificate
lemma proposed in 049. For any natural `k,target`,

```text
P D k <target<P D (k+1)
  -> not exists q : Nat, P D q=target.
```

If `q<=k`, monotonicity puts its evaluation below the target. Otherwise
`k+1<=q`, putting its evaluation above the target. No center-coordinate
enumeration or approximate real sixth root is involved.

## Perfect-sixth-power target and source-scale exclusion

`centeredSevenSextic_perfectSixth_target` checks the exact exponent identity

```text
448*(t^6)^49 =7*(2*t^49)^6.
```

For `D>0,t>0,9*D^2<=2*t^49`, the perfect-sixth-power bracket and no-image
theorems apply with `Q=2*t^49`. Natural positivity proves `Q>=1`, so
`(Q-1)+1=Q` is justified before using the adjacent integer certificate.
The positivity hypotheses remain explicit in these interfaces.

The zero gap is a real boundary failure: for every natural `t`,
`q=2*t^49` satisfies `P 0 q=448*(t^6)^49`. A zero root cannot satisfy
the scale condition when `D>0`. A separate regression at `D=2,Q=1`
shows that dropping the size condition can break the lower bracket.

`nestedCentered_perfectSixth_scale_constant` proves by kernel `decide`

```text
9*7^54 <=2*9^49.
```

`nestedCentered_perfectSixth_scale` then derives, from `9*r^2<=t`,

```text
9*(7^27*r^49)^2
  =(9*7^54)*r^98
  <=(2*9^49)*r^98
  =2*(9*r^2)^49
  <=2*t^49.
```

This is the exact sufficient condition for the nested scale. For `r>0`
it also forces `t>0`. `nestedCentered_perfectSixth_ne` therefore proves

```text
r>0, 9*r^2<=t, s=t^6
  -> for all q, P (7^27*r^49) q !=448*s^49.
```

This is an unbounded symbolic family: for each positive fixed `r`, all
`t>=9*r^2` are covered. The calibration additionally specializes it to
every `t>=9` at `r=1`. Those infinitely many distinct sixth-power cores
are covered by one proof, not by a list of numerical cases.

## Effect on centered candidates and exact branches

For `M=r*t^6` and `r>0`, exact natural quotient cancellation gives
`M/r=t^6`. `nestedCenteredAllocation_excluded_of_perfectSixth` then excludes

```text
exists q, CenteredNestedAllocationCandidate M r q.
```

A candidate's polynomial equality has target `64*(7*(M/r)^49)`, exactly
`448*(M/r)^49`, so it contradicts the raw no-image theorem. The raw theorem
excludes all natural centers, including ones without the candidate's
parity or primitive data. All those data remain present in the unchanged
candidate definition and the existing chart reconstruction equivalence.

`nestedAllocation_excluded_of_perfectSixth` uses that equivalence to exclude
both `NestedGNAllocationCondition M r` and `NestedRHSAllocationCondition M r`.
It does not weaken or alter either scalar equality.

`internalDepthFourAllocation_excluded_of_perfectSixth` specializes to a
supported divisor of an actual source core, while explicitly requiring

```text
M/r=t^6,
9*r^2<=t.
```

Divisor support and source positivity provide `r>0`. The perfect-power and
size hypotheses are still supplied separately.

The second source theorem,
`internalDepthFourReconstruction_excluded_of_perfectSixth_family`, requires
this exact additional premise:

```text
for every r in M.divisors,
  Nat.Coprime r (M/r),
  7^3*r^7<M,
  Nat.ModEq 7 (M/r) 1,
  SixthPowerAllocationSieve r (M/r)
    -> exists t, M/r=t^6 and 9*r^2<=t.
```

Under that premise it proves the reconstruction obligation false. The
proof extracts any proposed centered receiver's allocation and applies
the family exclusion. No theorem in this checkpoint supplies the premise
from the packet, and the conclusion contains no assertion that the packet
itself cannot exist.

## New pruning and retained calibration

Twenty-two new kernel regressions check the symbolic arithmetic, concrete
pruning and semantic boundaries.

For `r=1,t=9,s=M=531441`, kernel proofs verify:

- `M=1*9^6`, divisor membership and coprimality;
- seven-unit status of both factors and `s=1 mod 7`;
- sixth-power support modulo `r^49=1`;
- `343*r^7<M` and `7^161*r^343<M^49`;
- the exact strict inequalities

  ```text
  P (7^27) (2*9^49-1) <448*(9^6)^49
                        <P (7^27) (2*9^49);
  ```

- exclusion of every center, every centered candidate, and both exact
  fixed-allocation branches.

The huge numerical inequalities are independently checked by `decide`.
The no-image and branch exclusions use the symbolic family. This allocation
passed the older allocation-only filters; the new theorem removes it.
It is not an actual source packet or a solution to either scalar equation.

The old `M=64002,r=1` filters and modulus-one support are retained, without
asserting an endpoint. A new regression proves `64002` is not a perfect
sixth power, using the strict bounds `6^6<64002<7^6` and natural power
monotonicity. Thus even an inhabited sixth-power-residue sieve does not
supply the perfect-power premise.

The independent `M=729=3^6,r=1` example passes the old numeric GN filters
but has `t=3<9`, showing that those arithmetic filters plus a perfect sixth
power do not imply the new size premise. Its modulus-one support is also
available from the universal modulus-one API. No scalar solution or new
exclusion for this allocation is asserted.

At `M=1890024,r=3`, the existing 048-049 exclusion of all centered
candidates remains intact. The 049 actual-source centered equivalence is
retained as a generic regression. A standalone coprime product
`64002*5=64002*5` permits a nonperfect core; it checks insufficiency of
that product identity alone, not a counterexample to a full source packet
statement.

## Source audit and logical descent boundary

The source audit inspected the chosen seventh root of the internal
coordinate, its positive seven-unit core, the complementary-root identity

```text
M*N=verticalGapRoot*compensationRoot,
Nat.Coprime M N,
N>0, 7 does not divide N,
```

and the existing prime-support localization. These statements supply no
proved perfect-sixth-power identity for `M/r` and no proved inequality
`9*r^2<=t` for such a root. The real-cubic source-difference theorem has
`normalizedAxis^6*normalizedWitness(innerSndRoot)^7`; it is a ring identity
about a source difference, not the natural integer identity `s=t^6`.
No proved transport converts its sixth-power axis into that integer premise.

The inspected U1.6 kernel/chart APIs give equivalences with an existence
obligation. The ramified-resolution and primitive-resolution constructors
explicitly require a hypothesis inhabiting that obligation. Its definition
is an existential new away counterexample route with a prescribed carrier;
it is not an automatic consequence of the supplied source packet.
The strict-depth comparison and reconstructed counterexample remain
conditional on actually supplying this route.

Therefore even a universal proof that the centered receiver is empty would
obstruct this proposed reconstruction route. It would not, by itself,
prove the original source or original FLT7 counterexample nonexistent.
For terminal exclusion one still needs a proved implication from the
hypothetical original counterexample to the contradicted scalar condition,
or a proved mandatory reconstruction theorem. For genuine descent one
needs an actual reconstructed counterexample and the strict transition.
The negative family result supplies none of those existence implications.

## Validation

All four final measured builds succeeded with `LEAN_NUM_THREADS` absent
from the environment. Commands, exit codes, logs and GNU time telemetry
are retained in `logs/*-050.*`.

| Build | Elapsed seconds | Maximum RSS, KiB | Exit |
| --- | ---: | ---: | ---: |
| focused | 7.127 | 979268 | 0 |
| axiom-audit | 12.549 | 6742012 | 0 |
| facade | 12.715 | 6815436 | 0 |
| root | 18.763 | 7100692 | 0 |

The focused build reports 9093 jobs, the axiom audit 9089, the complete
Seven facade 9287, and the root build 10451. Job counts include replayed
dependencies. The final focused measurement reused the implementation and
calibration already compiled successfully; it is not a fresh compilation
benchmark. Every final invocation records zero major page faults and swaps.
No thread-limited retry or memory failure occurred.

All 15 new public production theorems have explicit `#print axioms` checks.
Only `propext`, `Classical.choice`, and `Quot.sound` occur; none depends on
`sorryAx`. The focused and axiom-audit logs contain no warnings. The facade
retains four existing `sorry` warnings in `ZsigmondyCyclotomicResearch`,
`TriominoCosmicBranchA`, `GcdNextResearch`, and `CyclotomicPrincipalization`.
The root additionally retains the existing `TriominoFLT` warning. Those
unchanged research modules are outside the new theorem dependency audit.

[check-050.py](checks/check-050.py) checks all theorem coverage, 22 calibration
declarations, four Lean headers, forbidden constructs, 26 unchanged source
fingerprints and three Mathlib fingerprints, the facade export, four
successful build records, standard axiom dependencies, ASCII artifacts,
and `git diff --check`. Its retained result is `logs/check-050.txt`.

## Next genuine arithmetic frontier and implementation proposals

These are bounded proposals, not a design for another numbered checkpoint.

The first arithmetic question is whether actual source factorization can
supply the perfect-power and size premises on a useful allocation class.
A theorem that all prime valuations of the complementary factor are
multiples of six would support an integer sixth-root construction, but the
current seventh-root and residue APIs do not prove that divisibility.
The root bound `9*r^2<=t` needs a separate source-derived estimate. Merely
restating both as hypotheses proves only the conditional obstruction
already implemented here.

A broader integer-image obstruction would require a source-derived strict
adjacent bracket for `448*(M/r)^49` when the complement is not a perfect
sixth power. The generic certificate lemma is now available, so an
implementation should prove the arithmetic inequalities that supply the
certificate from source data. Approximate roots, unrelated congruence
filters, or an astronomical search would not replace that theorem.

Before interpreting any such exclusion as FLT7 progress, establish the
logical bridge that makes its scalar equality mandatory for the original
counterexample, or construct the actual one-step descent route. A proved
receiver-empty theorem without that bridge remains an obstruction to the
chosen reconstruction method. The unresolved frontier thus has both an
integer-image arithmetic premise and an independent source-to-contradiction
or source-to-new-counterexample premise.
