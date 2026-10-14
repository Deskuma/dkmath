# Instruction 044 - Nested seven-adic reconstruction normal form

## Mission

Continue from Instruction 043.

Instruction 043 reduced the one-step FLT7 reconstruction obligation to a finite positive primitive Fermat-chart condition for the prescribed carrier

  c = internalDepthFourCarrier p.

It also proved:

- c has exact seven-adic depth four;
- any reconstructed away root has second-coordinate depth three;
- the current inner root cannot be reused as that away root;
- ideal plus exact seventh power does not determine the full residual coordinates.

Do not start recursive descent.

The next task is to exploit the arithmetic already present in DkMath to sharpen the prescribed-summand branch of the finite chart into a nested power normal form.

## Existing source shape

The current quadratic-inner-root machinery already proves that the prescribed carrier is not merely depth four.

After taking absolute value, it has the form

  c = 7^4 * M^7

for some positive natural seventh-root core M.

Reuse the existing inner second-coordinate split rather than reproving this from valuation alone.

## Prescribed-summand branch

Assume a finite chart of the form

  u^7 + c^7 = v^7

with positive primitive data.

Exchange the two summands when convenient and apply the existing p=7 ramified factorization to the counterexample

  c^7 + u^7 = v^7.

The existing SevenAdicPowerSplit should supply positive coprime a,b with

  v-u = 7^6 * a^7,
  GN 7 (v-u) u = 7 * b^7,
  c = 7 * a * b,

and 7 does not divide b.

The main question is what the additional source identity

  c = 7^4 * M^7

forces on a,b.

## Primary target

Seek a clean theorem reducing the hypothetical prescribed-summand chart to a second nested split

  a = 7^3 * r^7,
  b = s^7,
  M = r * s,

with the expected positivity and coprimality conditions.

Equivalent formulations are acceptable if signs or natural absolute values make a slightly different statement cleaner.

The proof should use exact prime-exponent allocation / coprime perfect-power extraction, not unique factorization by informal arithmetic.

Audit and reuse:

- SevenAdicPowerSplit;
- PrimeAdicPowerSplit;
- seventh_power_factor_split;
- existing coprime product-to-power extraction lemmas;
- the inner second-coordinate split from the ramified quadratic packet.

Do not build a new generic factorization framework unless the existing one is insufficient.

## Consequences to expose

If the nested split is proved, derive the strongest exact consequences that follow naturally.

In particular test the expected identities

  v-u = 7^27 * r^49,

and

  GN 7 (v-u) u = 7 * s^49.

The first identity should explain the exact gap depth 27, not merely the older shape

  depth = 6 + 7*m.

The second turns the residual into a forty-ninth-power equation after removing the unique factor seven.

If useful, expose

  GN 7 (7^27 * r^49) u / 7 = s^49

in a division-safe form.

## Congruence / GN remainder audit

The GN expansion gives a possible further reduction.

Because

  GN 7 d u = 7*u^6 + d*(higher polynomial terms),

when 7 divides d one expects

  GN 7 d u / 7
    congruent to
  u^6
    modulo d/7.

For

  d = 7^27 * r^49,

this would give the very strong necessary congruence

  s^49 ≡ u^6  (mod 7^26 * r^49).

Investigate whether a clean existing GN congruence theorem already gives this, or whether a small specialized lemma is worthwhile.

Do not force this congruence if the available APIs make it disproportionately expensive.

A proved normalized congruence would be substantial Outcome B progress even without contradiction.

## Relation to the new away root

Instruction 043 proved that any reconstructed AwayValuationTransferPacket at carrier c has root-second-coordinate depth three.

The hypothetical nested factor a also has expected depth three.

Audit whether current reconstruction/coordinate formulas relate that away root second coordinate to a.

Possible outcomes include:

- equality;
- equality up to a seven-unit;
- only equality of seven-adic depth;
- or no proved connection.

Do not infer equality from matching depth alone.

If only the depth matches, record that boundary explicitly.

## Right-hand-side branch

The finite receiver also permits

  u^7 + v^7 = c^7.

Do not silently discard this branch.

Audit its existing CounterexampleRoute classification and state what normal form is already available when 7 divides c.

A full treatment is not required if the prescribed-summand branch produces the stronger new theorem, but report clearly that the reconstruction obligation remains a disjunction unless one branch is excluded.

Do not claim one-step descent from a theorem concerning only one finite-chart branch.

## Quantitative / finite reduction

Instruction 043 bounded the prescribed-summand search by c^2.

If the nested split is obtained, explain how it reduces the search space structurally.

For example, candidate data should now come from coprime factor allocation of the seventh-root core M, rather than arbitrary pairs below c^2.

A finite divisor/factor receiver is acceptable if it follows naturally.

Do not implement a brute-force enumeration whose size is still astronomical merely to obtain decidability.

## Main success test

The important question is not computational speed.

It is whether the reconstruction condition becomes a source-indexed arithmetic equation substantially thinner than the generic finite Fermat chart.

A useful endpoint is something like:

  prescribed-summand reconstruction
    -> exists r,s,u satisfying
         M = r*s,
         coprime conditions,
         gap = 7^27*r^49,
         normalized GN residual = s^49.

An equivalence is better if available, but a strong necessary-condition theorem is already useful.

## Outcome classification

Outcome A:

The nested normal form yields an actual contradiction or constructs the required finite chart / AwayValuationTransferPacket, giving genuine one-step descent.

Outcome B:

The prescribed-summand finite chart is reduced to a substantially thinner nested seventh-/forty-ninth-power receiver, with exact gap/residual identities and useful provenance, but chart existence remains unresolved.

Outcome C:

The existing power-split machinery does not sharpen the finite-chart condition beyond a repackaging, or the expected nested extraction fails.

All outcomes are acceptable.

## Validation

Use:

- focused build;
- FLT Seven facade build;
- root build when appropriate;
- axiom audit for all new public production declarations.

Keep Legendre parked.

## Report

Write:

  lean/dk_math/docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/report-044.md

State:

- the source identity used for c = 7^4*M^7;
- the exact hypothetical SevenAdicPowerSplit on the prescribed-summand chart;
- whether a=7^3*r^7, b=s^7, M=r*s is proved;
- the resulting gap and residual identities;
- any normalized GN congruence;
- whether the factor a is connected to the new away root;
- status of the right-hand-side chart branch;
- whether the finite reconstruction search is materially reduced;
- whether one-step descent is obtained;
- build/axiom status;
- Outcome A/B/C;
- the next natural frontier.
