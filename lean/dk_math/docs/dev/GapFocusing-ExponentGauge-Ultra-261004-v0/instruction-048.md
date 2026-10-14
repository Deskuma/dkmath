# Instruction 048 - Sixth-power residue support sieve

## Mission

Continue from Instruction 047. The FLT7 depth-four reconstruction obligation is equivalent to the OR of two exact nested scalar receivers over positive coprime factors M=r*s:

- GN 7 D u = 7*s^49;
- alternatingCyclotomicSeven u (D-u) = 7*s^49;

where D=7^27*r^49. Instruction 046 selects a branch by an exact threshold; Instruction 047 filters s=1 mod 7 and adds the alternating band. Existence, exclusion, and descent remain open.

Do not restart recursion, change the exact scalar equations, or reopen Legendre.

## Primary mathematical question

Both exact receivers imply

  s^49 = w^6 (mod D)

for an appropriate endpoint w. Since r^49 divides D, the same congruence holds modulo r^49.

Use coprimality of r,s and the identity 49=1+6*8:

  s^49 = s*(s^8)^6.

As s has a modular inverse i, formally test

  (w*i^8)^6 = s (mod r^49).

Main target:

  Nat.Coprime r s ->
  Nat.ModEq (r^49) (s^49) (w^6) ->
  exists t, Nat.ModEq (r^49) (t^6) s.

Use Mathlib ZMod/unit/inverse or Nat.ModEq support; do not create a broad residue theory. Handle r=1 safely.

This turns the full-gap condition into an allocation-only sixth-power-residue requirement on s modulo r^49. Reduce further modulo any prime q dividing r. In particular, prove if possible

  3 divides r -> s = 1 (mod 3)

under the nested receiver hypotheses.

The condition is necessary, never sufficient for the scalar equation.

## Independent numerical regression

Check r=3, s=630008, M=1890024.

These satisfy M=r*s, coprimality, seven-unit status, s=1 mod 7, the coarse bound 343*r^7<M, and the strict GN threshold 7^161*r^343<M^49.

But s=2 mod 3, impossible for a sixth power modulo 3.

Thus this allocation passes the old arithmetic filters but should be rejected by the new one. It is NOT an actual FLT7 source or endpoint solution.

Retain M=64002 from Instruction 047: r=2 fails existing filters; r=1 must not be erroneously excluded by the modulus-one case.

## Receiver integration

If proved, add a thin sixth-power sieve to the existing
ResidueSievedNestedCondition and prove equivalence in both directions,
keeping the true GN/alternating endpoint equality and primitive data.

Specialize to the source-indexed internal depth-four reconstruction
obligation. Preserve all threshold, divisor and size guards.

Audit whether the source identity M*N=verticalGapRoot*compensationRoot
and Nat.Coprime M N restrict the eligible prime support of r.
Do not infer any bound or restriction not provided by a theorem.

## Optional endpoint uniqueness

GN scalar endpoint uniqueness is already proved. On the ordered alternating
half interval 0<u<=D-u, use the fixed-sum/product polynomial from 046 to
investigate strict monotonicity and uniqueness of the ordered endpoint.
This is secondary to the sixth-power sieve. Do not introduce calculus
unless necessary.

## Stopping rule and outcomes

Outcome A: prove terminal exclusion or genuine one-step descent from new
source-supported arithmetic.

Outcome B: prove a genuinely stronger sixth-power allocation sieve, exhibit
independent pruning, and retain exact equivalence with reconstruction.

Outcome C: prove the obstruction false or unusable, or establish that no
nontrivial pruning follows.

If the prime-support route stalls, do not accumulate ad hoc new modular
filters. The main remaining obstacle is exact scalar equality.

Use focused, axiom audit, Seven facade and root builds as in 047.

Write report-048.md in the same docs directory, with exact modular theorem,
r=3 and M=64002 regressions, source effect, receiver equivalence,
optional uniqueness status, axioms/builds, Outcome, and next frontier.
