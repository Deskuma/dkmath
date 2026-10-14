# Instruction 040 - Repeated-large prime-power phase compression

## Mission

Continue from Instruction 039.

Instruction 039 formally refuted one canonical pooled-threshold principle for
the unresolved central-binomial compensation problem.

The total central residual-product conjecture remains open, but local matching,
one-coordinate domination and threshold-separated pooling have now all shown
structural limitations.

Do not continue by adding ad hoc block heuristics.

Redirect this checkpoint to the repeated-large prime-power correction, as
suggested by report-039.

## Exact starting point

The exact old ledger remains

  oldBudget
    = Q
    + small carry
    + repeated large carry
    + higher correction.

Instruction 037 gives the strongest proved small-carry phase bound.
Instruction 039 does not improve that bound.

The repeated-large term is

  gnomonRepeatedCarryMass n,

the nonprime part of the large carry labels.

The current independent upper envelope uses the full nonprime prime-power band

  2*n < d <= n^2,

discarding the actual carry phase.

This is often very loose.

At n=69 the retained diagnostics give approximately

  repeated exact      = 9.11757
  repeated band bound = 68.41373.

Even under the hypothetical unresolved central small-carry bound, the reduced
criterion misses by only about 3.81 at n=69.

This is motivation only, not a proof premise.

## Main research question

Can the modular carry phase and exponent structure of repeated large prime
powers yield a strictly sharper independent upper bound

  repeated large carry <= R_phase(n)

than the full nonprime band budget?

The bound must remain independent of Q and of shell-prime existence.

Do not reopen singleton prime fibers.

## Existing structure to audit first

Reuse and audit before adding new definitions:

- gnomonLowDivisorCarryBit and the large-gap form,
- gnomonNextShellMultiple and its uniqueness theorem,
- gnomonLarge_prime_power_divisors_same_base,
- GnomonCarryFiber:
    exact consecutive exponent fibers,
    exponent cutoffs,
    same-target same-base geometry,
- the repeated/singleton split in GnomonCofactorWindow,
- any finite lcm / valuation / prime-power maximum APIs in Mathlib or DkMath,
- divisor-incidence and factorial/log-product identities if they provide a
  cleaner aggregate representation.

Prefer a thin structural compression theorem over a new hierarchy.

## Repeated-large phase

For 2*n < d, the existing carry condition is equivalent to the unique next
multiple after n^2 lying in the shell:

  nextMultipleGap(n^2,d) <= 2*n.

For d=p^a with a>=2, investigate whether this phase condition admits a useful
aggregate description.

Possible directions include:

- an explicit zero-phase exclusion inside the nonprime band,
- a cofactor / quotient description using
    k = n^2 / d + 1,
- a per-base exponent-gap estimate,
- an lcm / maximum-valuation interpretation of active prime powers,
- a finite product inequality that bounds the active repeated powers without
  enumerating the exact carry inventory.

Do not force any one of these if another cleaner route emerges.

## Important distinction

An exact restatement of repeated carry events is not a new upper bound.

For example, defining a budget as the sum over exactly those prime powers whose
next multiple lies in the shell merely renames the target.

A useful result must discard information while still proving a quantitatively
smaller envelope than the full nonprime band.

## Same-base multiplicity

Retain the known fact that several exponents of one prime base can hit the same
shell target.

The n=2896 base-2 fiber with ten consecutive exponents remains an important
regression.

Do not use one-log-per-target or a uniformly bounded fiber length; those routes
were already refuted in Instruction 029.

Any aggregate bound must preserve exponent multiplicity correctly.

## Required calibration

Retain at least:

- n=69, because the repeated-band slack is decisive there,
- n=2896, because long same-base exponent fibers occur,
- n=32 and 297 from earlier carry diagnostics,
- n=1031 and 5000 as large anchors.

If useful, also keep a small anchor where repeated carry is empty.

Explain structurally which band prime powers are excluded by the new bound,
rather than only reporting the final numerical mass.

## Combined correction budget

If a sharper repeated bound R_phase is proved, combine it with:

- the strongest proved small-carry bound from Instruction 037,
- the existing reciprocal higher-correction bound.

Define or expose one stronger independent correction envelope only if useful:

  B_repeatPhase(n).

Prove

  C_ns(n) <= B_repeatPhase(n)

and compare it with B_phase_037.

Do not assume the unresolved central-binomial compensation theorem.

## Budget test

Connect any stronger correction envelope to the existing exact Q term:

  Q + B_repeatPhase(n) < log(cell)
    -> exists prime in SquareCell n.

This is a sufficient criterion, not an equivalence.

Check whether the new repeated-phase saving repairs retained envelope failures,
especially n=69 and n=297, without using the unresolved central conjecture.

A finite recovery is useful evidence but remains Outcome B unless the existing
project-level Outcome A criterion is met.

## Optional lcm interpretation

If the repeated carry naturally equals or is bounded by a prime-power part of
the lcm of the shell integers, this may be formalized.

Such an lcm representation is useful only if it leads to an independent
quantitative bound.

Do not introduce a large lcm framework merely to restate the exact repeated
inventory.

## Circularity guard

The following do not count as progress:

- using the exact repeated carry carrier as the new budget,
- using Q or shell-prime birth mass,
- assuming oldBudget < log(cell),
- ignoring exponent multiplicity,
- replacing the full nonprime band by another equivalent exact sum,
- returning to the closed singleton factor-depth campaign.

## Stopping rule

Investigate one coherent repeated-large phase/exponent compression.

If no meaningful independent saving can be proved, identify the precise
obstruction and stop rather than adding increasingly local exclusions.

Keep the unresolved central-binomial total-product conjecture parked unless a
new structural theorem directly connects to it.

Do not predesign Instruction 041.

## Validation

Use the standard branch validation:

- focused build,
- Legendre facade build,
- root build when appropriate,
- axiom audit for new production declarations,
- bounded diagnostics where useful.

## Outcome classification

Outcome A:

A repeated-large phase bound, together with existing production results, yields
a universal strict budget theorem or a genuinely new unconditional
prime-existence range.

Outcome B:

A genuine independent repeated-large phase/exponent bound and stronger
correction envelope are formalized, but universal closure is not obtained.

Outcome C:

No meaningful independent compression beyond the full nonprime band is found,
or the proposed route collapses to exact repeated-carry classification.

All outcomes are acceptable.

## Report

Write:

  lean/dk_math/docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/report-040.md

State:

- the repeated-large phase/exponent structure actually used,
- the strongest independent bound proved,
- how same-base multiplicity is preserved,
- effect at n=69 and n=2896,
- comparison with the 037 repeated-band budget,
- the resulting combined correction envelope,
- diagnostics at retained anchors,
- whether n=69 / n=297 correction failures are repaired,
- axiom/build status,
- Outcome A/B/C,
- the next natural frontier suggested by the result.
