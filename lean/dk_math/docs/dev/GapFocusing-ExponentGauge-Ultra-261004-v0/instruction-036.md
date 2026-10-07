# Instruction 036 - Non-singleton correction compression

## Mission

Continue from Instruction 035.

Instruction 035 closed the finite factor-depth campaign.

With the adaptive square-root basis, the existing semiprime and three-prime
images exhaust all surviving composites. The corrected singleton envelope is
therefore exact:

  adaptive corrected singleton budget = Q.

The remaining prime-existence criterion is the exact old ledger itself.

Do not reopen the singleton approximation campaign.

The next question is whether the non-singleton part of the exact old budget can
be compressed independently enough to isolate the true remaining hard term.

## Exact starting point

For n >= 3, the existing production theorems give

  oldBudget
    = higher correction
    + small carry
    + repeated large carry
    + Q.

Here Q is now exact, not an envelope.

Define or name the non-singleton correction only if useful:

  C_ns(n)
    = higher correction
    + small carry
    + repeated large carry.

Then

  oldBudget = Q + C_ns.

The strict inequality

  oldBudget < log(cell)

is already equivalent to prime existence in the square shell.

Therefore merely repackaging this equality is not progress.

## Main research question

Can C_ns be bounded by an independent explicit function B(n) that is
substantially simpler and smaller than the full old budget, without using Q,
the shell prime inventory, or the desired prime-existence conclusion?

The purpose is not necessarily to prove Legendre immediately.

A useful result would formally isolate Q as the only remaining large /
short-window term.

## Audit before implementation

Reuse existing results before adding definitions.

In particular inspect:

- small carry events d <= 2*n and their von Mangoldt weights,
- repeated large carry events, which are nonprime prime powers,
- the exact higher-shell prime-power correction,
- the existing odd-depth / reciprocal / log-log bounds from Instructions 026-027,
- any Mathlib or DkMath finite theta/psi estimates that bound prime-power mass
  without short-interval prime-distribution input.

Do not duplicate already-proved correction bounds.

## Small carry

Determine the strongest natural independent upper bound already available or
easily derivable for

  gnomonPascalSmallCarryMass n.

Its event carrier consists only of prime-power labels at most 2*n.

A global prime-power bound such as a finite psi-type quantity may be natural,
but do not force this representation if a sharper structural bound exists.

The important point is that the bound must not inspect which shell primes exist.

## Repeated large carry

Audit the nonprime part of the large carry:

  gnomonRepeatedCarryMass n.

Use the same-base / exponent results from 029 when useful, but do not restart
the singleton fiber campaign.

Ask whether repeated prime-power labels admit a genuinely small global bound
from their exponent >= 2 structure, valuation cutoffs, or a finite
prime-power correction estimate.

## Higher correction

Reuse the strongest existing bound for

  gnomonPascalShellHigherPrimePowerMass n.

Do not spend this checkpoint reproving the 027 reciprocal/log-log gauge unless
a new interaction with small/repeated carry gives a stronger combined result.

## Combined question

Seek one clean theorem of the form

  C_ns(n) <= B(n),

where B is independent of Q and of actual shell prime existence.

The exact shape of B is open.

A bound of linear, near-linear, logarithmic-correction, or other explicit
finite scale is acceptable if it is genuinely informative.

If separate component bounds combine naturally, expose only the minimal public
surface needed for the combined result.

## Quantitative test

Compare B(n) with the exact ledger margin at retained anchors.

The intended reduced criterion is conceptually

  Q + B(n) < log(cell).

Do not confuse this sufficient criterion with the exact old-budget criterion.

The main diagnostic question is:

  after independently bounding C_ns,
  is Q clearly the dominant unresolved term?

Retain representative anchors from the current branch, including large ones
such as 297, 1031 and 5000.

Diagnostics are not proof premises.

## Circularity check

The following do not count as progress:

- defining B := C_ns,
- replacing a component by an equivalent exact sum,
- using the shell prime-birth mass to prove the upper bound,
- assuming oldBudget < log(cell),
- hiding Q or the desired theta increment inside B.

If every strong-looking estimate reduces to the same short-interval
prime-distribution problem, state that explicitly.

## Budget interpretation

If C_ns <= B is proved, connect it to the existing prime-existence consumer:

  Q + B < log(cell)
    -> prime exists in SquareCell.

This is a sufficient provider, not an equivalence unless separately proved.

If the new bound plus an existing independent estimate for Q unexpectedly
closes the strict inequality, that is a stronger outcome.

Otherwise the value of the checkpoint is to isolate the remaining frontier
cleanly.

## Implementation policy

Work autonomously.

Choose theorem names, module placement, helper lemmas, diagnostics and proof
strategy.

Keep the production surface small.

Prefer:

  exact non-singleton split
  -> strongest independent component bounds
  -> one combined C_ns bound
  -> one conditional consumer
  -> frontier audit

Do not redesign the closed 029-035 singleton branch.

Do not predesign Instruction 037.

## Validation

Use the standard branch validation:

- focused build,
- Legendre facade build,
- root build when appropriate,
- axiom audit for new production declarations,
- bounded diagnostics where useful.

## Outcome classification

Outcome A:

A new independent non-singleton bound, together with existing production
results, yields a universal strict budget theorem or genuinely new
unconditional prime-existence range.

Outcome B:

A genuine independent compression C_ns <= B is formalized and isolates Q as
the remaining dominant frontier, but universal closure is not obtained.

Outcome C:

No meaningful independent compression beyond existing results is available,
or the proposed bounds merely restate the exact ledger / short-interval
prime problem.

All outcomes are acceptable.

## Report

Write:

  lean/dk_math/docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/report-036.md

State:

- the exact non-singleton correction used,
- the strongest bound for small carry,
- the strongest bound for repeated large carry,
- the higher-correction bound reused,
- the combined independent B(n),
- whether B is genuinely new or only assembled from existing estimates,
- the reduced Q+B criterion,
- diagnostics at retained anchors,
- whether Q is now isolated as the principal remaining frontier,
- axiom/build status,
- Outcome A/B/C,
- the next natural frontier suggested by the result.
