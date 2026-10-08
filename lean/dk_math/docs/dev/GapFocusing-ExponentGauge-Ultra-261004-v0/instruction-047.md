# Instruction 047 - Common seven-adic residue sieve for nested allocations

## Mission

Continue from Instruction 046.

The full depth-four reconstruction obligation is now equivalent to a finite
divisor-supported receiver over the source core M.  Every candidate uses

  M = r*s,  D = 7^27*r^49,

with coprime positive seven-unit factors r,s.  The exact threshold comparison
selects at most one of the GN or alternating scalar equations at each r.

No scalar endpoint existence, global exclusion or genuine one-step descent
has been proved.  Do not start recursive descent.

The next question is whether the full-gap congruences of Instructions 044-045
give an independent residue filter that removes divisor allocations *before*
solving the selected scalar equation.

## Main question: a common seven-adic residue condition

Both branches prove a normalized congruence of the form

  s^49 congruent to w^6 modulo D,

where w is the positive GN endpoint u, or an alternating endpoint u or v.

In either branch, primitive endpoint conditions imply

  7 does not divide w.

Because 7^27 divides D, investigate the following deductions:

  s congruent to 1 modulo 7,

and the stronger endpoint condition

  w^6 congruent to 1 modulo 7^3.

The proposed proof mechanism is entirely finite:

1. Reduce the existing full-gap congruence modulo 7.
2. Use the proved finite-field unit fact w^6=1 mod 7.
3. Show s^49=s mod 7 and hence s=1 mod 7.
4. For s=1+7*k, prove by integer binomial arithmetic that
   s^49=1 mod 7^3.
5. Reduce the original congruence modulo 7^3.

Treat these as research targets, not assumptions.  Audit available
ZMod/prime-power/carry congruence lemmas before adding new machinery.

The resulting constraints must remain necessary conditions; they do not
replace the exact GN or alternating equality.

## Source-supported divisor filter

The first residue constraint is independent of the scalar endpoint:

  s = M/r congruent to 1 mod 7.

Under M=r*s it is equivalent to

  r congruent to M mod 7.

Prove a thin filtered-divisor receiver if useful.  It should retain only
positive divisors r of M with

- Nat.Coprime r (M/r);
- the already proved coarse size filter;
- the 046 strict branch threshold;
- the new residue constraint on M/r;
- and the corresponding exact scalar endpoint equation.

Preserve equivalence with the existing 046 reconstruction condition,
rather than weakening one direction.

Do not define the filter by inspecting the truth of the endpoint equation.

## Concrete regression

Instruction 046 used the seven-unit core M=64002 to demonstrate that
different divisor allocations can fall on opposite sides of the threshold.

Its r=2 allocation has

  s = M/r = 32001,  s mod 7 = 4.

So this allocation should be excluded by the new residue sieve, despite
passing the old size and threshold tests.

This is a calibration of the filter, not evidence for an actual FLT7 source
or solution.  Preserve the r=1 allocation as an example that a residue
filter does not automatically eliminate all candidates.

## Sharper alternating size band

Report 046 identified a useful independent necessary band.

For the right-hand-side branch the existing finite-power estimate gives

  D^6 <= 64*7*s^49,

while the strict branch comparison gives

  7*s^49 < D^6.

With M=r*s, derive the exact integer band

  M^49 < 7^161*r^343 <= 64*M^49.

Compare it to the existing coarse filter 343*r^7<M.

Retain integral, division-free inequalities and the correct weak/strict
orientations.  Do not use floating point powers as proof premises.

If both the residue sieve and this band are obtained, incorporate them into
the existing threshold-routed receiver with minimal new public surface.

## Relation to the actual source

The source already proves

  7 does not divide M,
  M*N = verticalGapRoot*compensationRoot,
  Nat.Coprime M N,
  7 does not divide N.

Audit whether the residue restriction r=M mod 7 interacts with these
existing equations or prime-support facts.

Only record an additional source constraint when it is a proved theorem.
Do not infer a numerical upper bound for M from the source product.

A bounded exclusion for some M or a class of divisors is useful even if it
does not extend to every actual source.

## Optional endpoint uniqueness

Instruction 044 proves GN endpoint uniqueness for each (r,s).
Instruction 045 gives the canonical alternating order u<=D-u.
Instruction 046 proves the fixed-sum/product polynomial identity.

If the main residue and band work is complete, investigate whether the
alternating residual is strictly monotone on the ordered half interval,
giving at most one unordered endpoint pair per allocation.

A simple fixed-sum power argument is acceptable; no general calculus
framework is needed.

This is optional and must not displace the common residue question.

## Stopping boundary

The goal is a genuinely independent filter of factor allocations or
endpoint residues, not a new naming of the old full-gap congruence.

If the proposed 7-adic consequences add no useful constraints beyond an
equivalent rewriting, or if the source does not constrain the remaining
allocations, state that boundary plainly.

Keep the exact scalar equations and the full two-branch disjunction.
Do not claim existence, exclusion, or descent from finite diagnostics.

Do not predesign Instruction 048.

## Outcome classification

Outcome A:
the new constraints, together with proved source data, eliminate every
remaining allocation or otherwise solve the reconstruction obligation,
producing genuine one-step descent or a terminal exclusion.

Outcome B:
a nontrivial common residue/divisor filter and/or sharper alternating
allocation band is formalized and improves the supported finite receiver,
but some allocations and exact scalar equations remain open.

Outcome C:
the proposed filters fail or yield only an exact reformulation without an
independent pruning or new structural consequence.

All outcomes are acceptable.

## Validation and report

Use focused build, FLT Seven facade build, root build when appropriate,
and axiom audit for every new public production declaration.

Write

  lean/dk_math/docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/report-047.md

Record the 7-adic deductions actually proved, impact on M=64002,
the filtered-divisor equivalence, alternating size band, any source-specific
consequence, status of optional alternating uniqueness, build/axiom status,
Outcome A/B/C, and the next natural frontier.
