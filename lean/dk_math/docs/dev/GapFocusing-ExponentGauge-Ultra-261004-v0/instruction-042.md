# Instruction 042 - Q floor-pulse and quotient-block control

## Mission

Continue from Instruction 041.

Instruction 041 closes the local correction-refinement campaign.

The strongest proved correction envelope remains Instruction 040:

  B040(n) = gnomonRepeatPhaseCorrectionBudget n,

with the conditional consumer

  Q(n) + B040(n) < log(cell(n))
    -> exists p, Prime(p) and SquareCell n p.

Instruction 041 supplies a simpler endpoint-only repeated bound but is
deliberately weaker than 040. Do not replace 040 by the looser envelope when
testing the remaining frontier.

The next task is independent control of

  Q(n) = gnomonCofactorWindowMass n.

Do not reopen singleton factor-depth classification or local correction
heuristics.

## Exact Q currencies

Audit and, where useful, expose thin equivalences between the following three
views of Q.

### 1. Cofactor-window view

The existing exact definition is

  Q(n)
    = sum over k in [2,n-1]
        sum over prime p in the kth cofactor window
          log p.

The windows are indexed by the canonical cofactor

  k = n^2 / p + 1.

### 2. Large-prime floor-pulse view

For p>2*n, the carry is binary:

  floor((n^2+2*n)/p) - floor(n^2/p) in {0,1}.

The intended exact prime-only pulse is conceptually

  Q(n)
    =
  sum over primes p with 2*n < p <= n^2
    log p *
    (floor((n^2+2*n)/p) - floor(n^2/p)).

Prove this bridge if it is not already available in a suitable form.

A von-Mangoldt version with an explicit prime/depth-one filter is acceptable.

Do not silently include repeated prime powers; those belong to the correction
side already handled in 040.

### 3. Shell-target / cofactor view

Every Q-prime has the unique shell target

  y = k*p,
  n^2 < y <= n^2+2*n,

with 2<=k<n.

If useful, package the exact target/cofactor incidence and its injectivity.

A product identity of the form

  product p * product k = product y

over the actual Q carrier may be useful infrastructure.

It is not itself an independent upper bound.

## Available margin

Name an available margin only if it improves clarity:

  M040(n) = log(cell(n)) - B040(n).

The exact sufficient condition is

  Q(n) < M040(n).

Merely defining M040 or rewriting the existing consumer is infrastructure,
not Outcome B.

The new mathematics must provide an independent upper bound for Q or an
independent lower bound for M040 strong enough to compare the two.

## Main research question

Can the full family of cofactor windows be controlled in aggregate, without
estimating each window separately and without reconstructing the exact prime
inventory?

Seek a theorem

  Q(n) <= U_Q(n)

where U_Q is defined from endpoint, quotient-block, divisor-hyperbola,
factorial/product, or other independent finite geometry.

The target comparison is

  U_Q(n) + B040(n) < log(cell(n)).

Do not assume this strict inequality in the definition of U_Q.

## Quotient-block / divisor-hyperbola direction

The individual windows are centered near

  p ~ n^2/k

and have width approximately

  2*n/k.

Rather than summing independent per-window overcovers as in Instructions
030-031, investigate grouping quotient indices k into coherent blocks.

Possible useful structures include:

- dyadic or harmonic blocks of quotient values;
- a global divisor-hyperbola identity for the floor-pulse sum;
- product or factorial ratios accumulated over many windows at once;
- target/cofactor product inequalities using injectivity of shell targets;
- a finite theta/psi block estimate if its orientation is valid and it does not
  merely subtract unrelated global upper bounds;
- a global spacing/capacity theorem that couples different windows.

Let the arithmetic determine the useful grouping.

Do not recreate the 030 geometric budget or 031 sieve under a new name.

## Important failure history

Preserve the lessons from 030-035.

- Per-window binomial/geometric envelopes are far too loose at large anchors.
- A finite wheel produces surviving composite error.
- Lower certified composite mass may be subtracted; an upper error bound may
  not be subtracted in the wrong orientation.
- Adaptive square-root roughness eventually reconstructs Q exactly, which is
  classification rather than an independent estimate.

The new U_Q must avoid those failure modes.

## Von Mangoldt / CFBRC audit

The repository contains RH/CFBRC finite von-Mangoldt pulse and finite-block
compensation machinery.

A preliminary audit shows that

  pascalCenteredXiPrimeSideFiniteModeKernel

is a Mellin/phase integral kernel, not the Legendre 0/1 shell carry bit.

Therefore do not identify the CFZP pulse with Q without an explicit theorem.

It is acceptable to reuse generic finite von-Mangoldt support, block-sum or
telescoping infrastructure if it gives a thin exact bridge.

Do not import RH, a cofinal sign provider, or an unproved CFBRC compensation
contract to force the result.

If the CFBRC machinery is structurally unrelated after audit, say so and keep
the implementation in the Legendre package.

## Shell-target product direction

If the target/cofactor representation is used, remember that

  log p = log y - log k.

A useful theorem must control the selected target product and/or cofactor
product independently.

The following do not count as progress:

- replacing Q by the exact product of its selected targets;
- using the exact Q carrier to choose a favorable subset;
- bounding selected targets by the entire shell product if the resulting bound
  is quantitatively useless;
- assuming a lower bound for the cofactor product that is equivalent to the
  desired Q inequality.

A genuinely new multiplicative inequality is acceptable.

## Required diagnostics

Retain at least:

- n=32,
- n=69,
- n=210,
- n=297,
- n=1031,
- n=2896,
- n=5000.

Use the stronger 040 correction budget for the available margin.

Record separately:

  exact Q,
  proposed U_Q,
  B040,
  log(cell),
  U_Q + B040 margin.

If useful, scan a bounded interval to locate the worst ratio or first failure of
the proposed independent Q estimate.

Diagnostics are not proof premises.

## Quantitative acceptance

A useful Outcome B estimate should do more than bound Q formally.

It should either:

- materially reduce the 030/031 Q overcover;
- recover a nontrivial retained range with the 040 correction budget;
- expose a new scale or cancellation mechanism across quotient windows;
- or reduce Q control to one substantially simpler independent arithmetic
  inequality.

A bound that is orders of magnitude above the available margin at all large
anchors is Outcome C unless it reveals a genuinely new structural theorem.

## Circularity guard

The following do not count as independent Q control:

- using gnomonCofactorWindowMass itself inside U_Q;
- filtering candidates by primality and then summing the survivors;
- adaptive factor-depth classification that reconstructs the composite error;
- using shell prime birth or the conclusion that a prime exists;
- assuming oldBudget < log(cell);
- subtracting a quantity known only to be an upper bound on an error;
- importing PNT, RH, or an unproved short-interval estimate as a premise.

A proved unconditional Mathlib theorem may be used, but its actual quantitative
strength must be audited against the retained margins.

## Stopping rule

Investigate one coherent aggregate Q mechanism.

Do not begin another long hierarchy of progressively refined finite sieves.

If the best independent aggregate estimate remains far above M040, identify
the precise missing inequality and classify the route honestly.

At that point the Legendre laboratory should be summarized as having reduced
the problem to a genuine weighted short-interval / quotient-window theorem,
rather than continuing local bookkeeping.

Do not predesign Instruction 043.

## Validation

Use the standard branch validation:

- focused build,
- Legendre facade build,
- root build when appropriate,
- axiom audit for new production declarations,
- bounded diagnostics where useful.

## Outcome classification

Outcome A:

An independent Q estimate together with the proved 040 correction envelope
yields a universal strict budget theorem or a genuinely new unconditional
prime-existence range.

Outcome B:

A genuine independent aggregate Q bound or quotient-block theorem is formalized
and materially advances the available-margin comparison, but universal closure
is not obtained.

Outcome C:

Only exact reindexing is obtained, or every investigated independent Q
envelope remains quantitatively too weak / reduces to the unresolved weighted
short-interval problem.

All outcomes are acceptable.

## Report

Write:

  lean/dk_math/docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/report-042.md

State:

- the exact Q currency or bridge actually used;
- whether the floor-pulse identity is formalized;
- any target/cofactor product identity;
- the aggregate quotient-block mechanism investigated;
- the strongest independent U_Q obtained;
- comparison with the 030/031 envelopes;
- interaction with B040 and retained margins;
- whether CFBRC finite-pulse infrastructure was useful or inapplicable;
- diagnostics at retained anchors;
- axiom/build status;
- Outcome A/B/C;
- the next natural frontier suggested by the result.
