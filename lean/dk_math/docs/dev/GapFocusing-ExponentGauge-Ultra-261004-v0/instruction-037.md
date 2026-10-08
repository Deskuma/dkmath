# Instruction 037 - Phase-aware small-carry compression

## Mission

Continue from Instruction 036.

Instruction 036 proved the exact split

  oldBudget = Q + C_ns

and an independent non-singleton bound

  C_ns <= B,

with

  B =
    theta(2*n)
    + (psi(n^2) - theta(n^2))
    + reciprocalBudget(n).

This is a genuine compression, but it drops the modular carry phase.
At retained anchors the resulting slack can still decide the reduced criterion.

Do not reopen the closed singleton factor-depth campaign.

## Main research question

Can the exact modular phase of the small carry be used to replace the coarse
theta(2*n) term by a substantially sharper width-only quantity?

The primary candidate is

  gnomonPascalSmallCarryMass n
    <= log (Nat.choose (2*n) n).

Treat this as a conjectured research target, not as an assumption.

Independent diagnostics found no counterexample for n=3..10000, with the
largest sampled ratio small/log central-binomial near n=27 at about 0.895.
This is evidence only.

## Why this candidate matters

The small carry records prime-power carry bits at labels d <= 2*n.

The exact carry predicate is already available:

  gnomonLowDivisorCarryBit n d = 1
    iff
  d <= n^2 % d + (2*n) % d.

Equivalently it is the one-step floor carry associated with the square-shell
addition n^2 + 2*n.

The central binomial coefficient is also a pure width object and has its own
prime-power carry/factorization interpretation.

Investigate whether these two carry systems admit:

- a direct weighted comparison,
- an injection or domination of carry coordinates,
- a factorial/binomial product inequality,
- or another finite argument proving the same logarithmic bound.

Do not assume pointwise inclusion of prime-power carry events; it need not hold.

## Audit first

Before adding definitions, inspect and reuse:

- gnomonLowDivisorCarryBit and its remainder/floor forms,
- gnomonLowDivisorCarryBit_prime_pow_iff,
- factorization_choose / Kummer-style receivers in Mathlib and DkMath,
- existing central-binomial or binomial-factorization lemmas,
- Pascal prebirth / prime-power carry interfaces where relevant.

Prefer a thin theorem over a new carry framework.

## If the central-binomial bound is false

Preserve a smallest or structurally clear counterexample.

Then seek the strongest nearby phase-aware statement justified by the same
carry geometry.

Examples of acceptable alternatives include:

- a different width-only binomial or factorial bound,
- theta(2*n) minus an explicit positive phase exclusion,
- a weighted carry count with a proved endpoint correction.

Do not force the candidate formula if the arithmetic says otherwise.

## Repeated large carry refinement

Instruction 036 bounded repeated large carry by the full nonprime prime-power
prefix through n^2.

Because repeated large labels satisfy 2*n < d <= n^2, also test the sharper
band-only nonprime prefix:

  nonprime prime-power mass on (2*n, n^2].

Use an exact finite carrier or a psi-theta difference if subtraction is
convenient and justified.

Do not re-enter same-base singleton fibers.

## Candidate combined budget

If the central-binomial bound and the band-only repeated bound are proved,
a natural stronger correction envelope is conceptually

  B_phase(n)
    =
      log (choose (2*n) n)
      + nonprimePrimePowerMass(2*n, n^2]
      + reciprocalBudget(n).

The exact Lean definition may differ.

The required theorem is

  C_ns(n) <= B_phase(n),

independent of Q and of shell-prime existence.

Compare it formally with the Instruction 036 budget when possible.

## Quantitative checks

Retain the existing anchors, especially

  32, 69, 210, 297, 1031, 5000.

At n=5000, the 036 diagnostic had:

  exact small carry   ~ 4287.17
  theta(2*n)          ~ 9895.99
  log choose(2*n,n)   ~ 6926.64

so the candidate replacement saves about 2969 in that term, while the 036
reduced criterion missed by only about 419.

This is diagnostic motivation, not a proof premise.

Also preserve difficult small anchors such as n=27, where the sampled
small/central-binomial ratio is relatively large.

## Consumer

If a stronger independent correction bound is obtained, connect it to

  Q + B_phase(n) < log(cell)
    -> exists prime in SquareCell n.

This remains a sufficient criterion, not an equivalence.

The purpose of this checkpoint is to reduce correction slack enough that Q
becomes a cleaner principal frontier.

## Circularity guard

The following are not progress:

- defining the new budget from the exact small-carry carrier itself,
- using Q or shell prime-birth mass to prove the small-carry bound,
- assuming the old strict criterion,
- hiding the target shell prime inventory inside a new notation.

A width-only binomial/factorial quantity is acceptable because it is
independent of the target shell prime inventory.

## Stopping rule

Do not branch into a general theory of arbitrary Pascal carry comparisons.

Either prove/refute the phase-aware width bound, obtain one useful replacement,
and connect it to the correction budget, or report the precise obstruction.

Do not predesign Instruction 038.

## Validation

Use the standard branch validation:

- focused build,
- Legendre facade build,
- root build when appropriate,
- axiom audit for new production declarations,
- bounded diagnostics where useful.

## Outcome classification

Outcome A:

A phase-aware correction bound, together with existing production results,
yields a universal strict budget theorem or a genuinely new unconditional
prime-existence range.

Outcome B:

A genuine phase-aware small-carry bound and stronger independent correction
budget are formalized, but universal closure is not obtained.

Outcome C:

The central-binomial / width-only phase route is false or yields no meaningful
improvement over Instruction 036.

All outcomes are acceptable.

## Report

Write:

  lean/dk_math/docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/report-037.md

State:

- whether smallCarry <= log choose(2*n,n) is true,
- the exact proof mechanism or counterexample,
- the strongest phase-aware small-carry bound proved,
- the repeated-large band refinement, if any,
- the resulting combined correction budget,
- comparison with the Instruction 036 budget,
- diagnostics at retained anchors,
- whether the n=5000 correction slack is removed,
- whether Q is more cleanly isolated as the remaining frontier,
- axiom/build status,
- Outcome A/B/C,
- the next natural frontier suggested by the result.
