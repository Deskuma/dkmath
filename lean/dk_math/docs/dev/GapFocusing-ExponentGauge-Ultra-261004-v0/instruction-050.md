# Instruction 050 - Adjacent sixth-power gnomon gap for centered FLT7

## Mission

Continue from Instruction 049.

Instruction 049 proves exact polynomial reconstruction through

  P D q = 448*s^49,
  P D q = 7*q^6 + 35*D^2*q^4 + 21*D^4*q^2 + D^6,
  D = 7^27*r^49,  M = r*s,

with positive coprime source-supported factors. Its centered candidate
keeps primitive endpoints, parity, and the GN/alternating chart position.
It also proves P D strictly increasing and the entire centered receiver
equivalent to the depth-four reconstruction obligation.

No source-supported endpoint exists by any current theorem; the new
uniqueness result is not existence or global exclusion.

The next goal is a genuine *integer-image exclusion family* for this
polynomial, not another exact receiver or unrelated congruence sieve.

## Main proposed gnomon-gap theorem

If the complementary factor happens to be a perfect sixth power,

  s = t^6,  0<t,

then the target aligns with a pure sixth power:

  448*s^49 = 7*(2*t^49)^6.

Put Q=2*t^49. For D>0, the central polynomial has P D Q >
7*Q^6. On the other hand, when

  9*D^2 <= Q,

the adjacent-sixth-power GN difference should dominate the extra terms,
giving the strict bracket

  P D (Q-1) < 7*Q^6 < P D Q.

Prove this general theorem in natural arithmetic. In particular derive

  D>0, t>0, 9*D^2<=2*t^49
    -> not exists q : Nat, P D q = 448*(t^6)^49.

Use Instruction 049's proved strict monotonicity to exclude every q
from the strict bracket. Do not use approximate real sixth roots.

### Suggested arithmetic route

For Q>=1, prove the elementary adjacent-power estimate

  Q^6 - (Q-1)^6 >= Q^5.

The higher terms in P D (Q-1) are

  35*D^2*(Q-1)^4 + 21*D^4*(Q-1)^2 + D^6.

Under Q>=9*D^2 and D>=1, each is bounded by its corresponding
D^2*Q^4 multiple, with total <=57*D^2*Q^4.

Meanwhile

  7*Q^5 >=63*D^2*Q^4 >57*D^2*Q^4.

This should yield the lower strict bracket.
The upper bracket follows from the positive D^6 term.
The hypotheses D>0 and t>0 are essential: D=0 has an exact
pure-sixth-power equality at q=2*t^49.

Handle Nat subtraction carefully, or substitute Q=k+1 and prove a
polynomial identity with nonnegative coefficients. Prove the inequalities
before the integer-image corollary.

## Source-scale specialization

For the actual nested scale D=7^27*r^49, r>0, test the simple
sufficient condition

  s=t^6,  9*r^2 <= t.

It implies 9*D^2 <= 2*t^49 because

  D^2=7^54*r^98,
  (9*r^2)^49=9^49*r^98,
  9*7^54 <=2*9^49.

Verify the last constant inequality in Lean (it is an integer fact).

The desired source-scale exclusion is

  r>0, t>=9*r^2, s=t^6
    -> for all q, P (7^27*r^49) q !=448*s^49.

Connect it to the existing
CenteredNestedAllocationCandidate M r, with M=r*s, and then to
both exact fixed-allocation predicates. Retain all existing chart
provenance and do not change the 049 receiver.

The condition that s be a sixth power is an additional assumption:
the actual source has NOT been shown to impose it. Do not infer it
from s being a sixth-power residue modulo r^49.

## Concrete new-pruning calibration

Use the source-free arithmetic allocation

  r=1, t=9, s=9^6=531441, M=531441.

It satisfies:

- r divides M and Nat.Coprime r s;
- seven-unit status, s=1 mod 7 and sixth-power support modulo r^49=1;
- the 046 coarse size guard 343*r^7<M;
- the strict GN-side allocation threshold 7^161*r^343<M^49.

Thus it passes the old allocation-only filters.

The proposed gnomon bracket should nevertheless exclude *all*
center coordinates and therefore both scalar endpoint equations at
this fixed allocation. Test and kernel-check the exact inequalities

  P (7^27) (2*9^49-1) < 448*(9^6)^49
  < P (7^27) (2*9^49).

This is a calibration, not an actual source packet or FLT7 solution.
Retain the 049 cases M=64002,r=1 and M=1890024,r=3 without
misrepresenting their status.

## Optional general integer-gap certificate

If it is useful, factor out a thin theorem

  P D k < target < P D (k+1)
    -> not exists q, P D q = target.

This follows from strict monotonicity and is only infrastructure;
it is not by itself Outcome B. The substantial result is the symbolic
family of brackets at Q=2*t^49, not a manual bracket for each arbitrary
huge numerical target.

Do not construct binary searches or large enumerations unless a source
theorem makes them decisive.

## The logical descent boundary

Be precise about what a negative result means.

  InternalDepthFourCounterexampleReconstructionObligation p

is currently an additional existence obligation, *not a theorem*
obtained automatically from a source packet p.

Proving that some or even every centered receiver is empty would
obstruct this proposed reconstruction/descent route; it does NOT,
by itself, prove that the original source p cannot exist.

Genuine FLT7 terminal exclusion requires a separate proved implication
from a hypothetical original counterexample to the arithmetic
contradiction, or a proved one-step descent to an actual new
counterexample. Do not label receiver nonexistence alone as FLT7.

Audit whether existing outer-root/source constraints force the perfect
sixth-power condition or an analogous universal power-gap obstruction.
Report an exact missing premise if not.

Do not start recursive descent. Legendre stays parked.

## Outcome classification

Outcome A: source-specific arithmetic bridges actually rule out the
original counterexample or construct a valid one-step strict descent.

Outcome B: the general adjacent-sixth-power bracket and a nontrivial
infinite family of source-scale scalar exclusions are kernel-checked,
the previously surviving r=1,t=9 allocation is excluded, and the
remaining global bridge is stated honestly.

Outcome C: only the generic monotonic bracket lemma or finite
numerical certificates are obtained, or the proposed symbolic
power-gap inequality fails.

All outcomes are acceptable. Do not predesign Instruction 051.

## Validation and report

Run focused, new-declaration axiom audit, FLT Seven facade and root
builds. Preserve existing sorry warnings as existing scope only.

Write

  lean/dk_math/docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/report-050.md

Record the adjacent-power inequality, exact bracket and its
hypotheses, source-scale sixth-power exclusion, r=1,t=9 regression,
effect on existing centered candidates, whether the source forces
any sixth-power or size premise, logical meaning for reconstruction
versus actual FLT7, build/axiom status, Outcome A/B/C, and the
next genuine Diophantine frontier.
