# Instruction 045 - Symmetric forty-ninth-power reconstruction receivers

## Mission

Continue from Instruction 044.

Instruction 044 reduced the prescribed-summand reconstruction branch to the exact nested scalar receiver

  M = r*s,
  d = 7^27*r^49,
  GN 7 d u = 7*s^49,

with positivity, coprimality, seven-unit data, full-gap congruence, and uniqueness of u for each fixed factor allocation.

The full reconstruction obligation is still a disjunction because the right-hand-side Fermat chart

  u^7 + v^7 = c^7

remains open.

The next task is to put that branch into the same source-indexed forty-ninth-power currency.

Do not start recursive descent.

## Existing right-hand-side arithmetic

Let

  c = 7^4*M^7

and assume

  source : CounterexamplePack u v c.

The existing prescribed-carrier alternating split already gives positive coprime A,B with

  u+v = 7^6*A^7,
  alternatingCyclotomicSeven u v = 7*B^7,
  c = 7*A*B.

The construction also has enough arithmetic to prove that B is a seven-unit.

Reuse this existing split. Do not create a second Row-Z factorization framework.

## First target: shared nested factor allocation

Extract the common arithmetic from Instruction 044 if useful.

From

  c = 7*A*B = 7^4*M^7,
  Nat.Coprime A B,
  7 does not divide B,

prove the same second-stage allocation

  A = 7^3*r^7,
  B = s^7,
  M = r*s,

with r,s positive, coprime, and seven-units for the current source core.

Prefer a small common helper reusable by both:

- SevenAdicPowerSplit;
- PrescribedCarrierAlternatingPowerSplit.

Do not duplicate a long perfect-power proof solely because the outer packet type differs.

## Exact alternating consequences

Substitute the nested split into the existing alternating identities and prove

  u+v = 7^27*r^49,

and

  alternatingCyclotomicSeven u v = 7*s^49.

Preserve exact natural-number equalities.

The first equation is the right-branch analogue of the GN gap equation.

## Scalar one-variable receiver

Let

  D(r) = 7^27*r^49.

Since u+v=D, the right branch should be expressible using one scalar endpoint, for example v=D-u.

Define a thin arithmetic proposition only if useful, conceptually:

  NestedRightHandSideCondition M :=
    exists r s u,
      0<r and 0<s and 0<u and u<D(r) and
      M=r*s and
      Nat.Coprime r s and
      appropriate endpoint coprimality and
      alternatingCyclotomicSeven u (D(r)-u) = 7*s^49.

Choose the cleanest coprimality condition.

For example, Nat.Coprime u D may be easier to transport to
Nat.Coprime u (D-u), but prove the bridge rather than assuming it.

## Main equivalence target

Prove, if the existing APIs permit it,

  NestedRightHandSideCondition M
    iff
  exists u v, CounterexamplePack u v (7^4*M^7).

The reverse construction should use

  D * alternatingCyclotomicSeven u (D-u)
    = u^7 + (D-u)^7

and the nested identities

  D = 7^27*r^49,
  M = r*s

to recover

  u^7 + v^7 = (7^4*M^7)^7.

Do not replace the exact Fermat equation by a congruence.

A one-way exact reduction is still useful if the converse has a genuine API obstruction; report that precisely.

## Alternating normalized congruence

Audit the existing expansion

  alternatingCyclotomicSeven x y
    = (x+y)*P(x+y,y) + 7*y^6

in integer/natural form.

When 7 divides D=x+y, investigate the normalized congruence

  alternatingCyclotomicSeven x y / 7
    congruent to
  y^6
    modulo D,

or the strongest correct modulus naturally obtainable.

For the nested branch this would yield

  s^49 ≡ v^6  (mod 7^27*r^49)

or the corresponding congruence with u, depending on orientation.

Do not force a full-D modulus if the signed polynomial coefficients make only D/7 immediate.

Preserve whichever theorem is actually proved.

## Symmetry and endpoint uniqueness

Unlike the GN receiver, the alternating residual is symmetric in u and v.

Therefore literal uniqueness of u cannot hold without choosing an orientation.

If useful, impose a canonical order such as

  u <= v

or equivalently u <= D/2,

and investigate whether the normalized alternating residual is strictly monotone on that half interval.

A theorem saying each fixed factor allocation admits at most one unordered pair {u,v}, or at most one ordered representative u<=v, would be valuable.

This is optional. Do not spend the checkpoint building a large monotonicity framework if the nested receiver equivalence is already the main result.

## Reconstruction obligation in two matched currencies

The preferred end product is a theorem of the form

  InternalDepthFourCounterexampleReconstructionObligation p
    iff
  NestedPrescribedSummandCondition M
    or
  NestedRightHandSideCondition M,

where

  M = internalDepthFourSeventhCore p.

Both branches should then expose the same source factor allocation

  M=r*s

and the same large scale

  D=7^27*r^49,

with only the residual polynomial / sign geometry differing:

  GN 7 D u = 7*s^49

versus

  alternatingCyclotomicSeven u (D-u) = 7*s^49.

This matched disjunction is the main objective.

## Why this matters

Instruction 044 made one branch extremely thin, but it could not close reconstruction because the other branch remained generic.

Once both branches are in the same source-indexed 49th-power form, the next research question can be a common scalar obstruction rather than more chart bookkeeping.

Do not claim one-step descent merely from this symmetrization.

## Relation to away-root depth

Instruction 044 obtained a division-free comparison between the prescribed-summand nested factor and the reconstructed away root.

Audit whether the right-hand-side branch supplies an analogous comparison.

This is secondary to the matched scalar receiver.

Matching seven-adic depth is not enough to assert coordinate equality.

## Outcome classification

Outcome A:

The symmetric nested receiver yields a contradiction for the right-hand-side branch or, together with the GN branch, constructs/excludes the full reconstruction obligation and produces genuine one-step descent or terminal exclusion.

Outcome B:

The right-hand-side branch is reduced to a source-indexed nested forty-ninth-power scalar receiver and the full reconstruction obligation is expressed as the OR of two matched thin receivers, but existence remains unresolved.

Outcome C:

The alternating branch cannot be sharpened beyond the existing power split, or the expected second-stage allocation / scalar equivalence fails.

All outcomes are acceptable.

## Validation

Use:

- focused build;
- FLT Seven facade build;
- root build when appropriate;
- axiom audit for all new public declarations.

Keep Legendre parked.

## Report

Write:

  lean/dk_math/docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/report-045.md

State:

- the common nested factor-allocation helper, if introduced;
- whether A=7^3*r^7, B=s^7, M=r*s is proved for the alternating split;
- the exact sum and alternating residual identities;
- the scalar one-variable right-hand-side receiver;
- whether chart existence is equivalent to that receiver;
- any normalized alternating congruence;
- any ordered/unordered endpoint uniqueness theorem;
- the final two-branch reconstruction equivalence;
- whether an away-root comparison is obtained;
- whether one-step descent or exclusion is obtained;
- build/axiom status;
- Outcome A/B/C;
- the next natural frontier.
