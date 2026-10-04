# Gap Focusing / Exponent Gauge Ultra

Branch: **research/GapFocusing-ExponentGauge-Ultra-261004-v0**

Base: current `develop`, after merged PR #112.

## Research question

Study the passage

```text
(a - b)          -> x
a^d - b^d        -> (x+u)^d - u^d = x * GN_d(x,u)
```

through the change of variables

```text
a = x + u
b = u.
```

The aim is not to celebrate a convenient substitution.  The aim is to decide
whether this operation exposes a genuine structural decomposition:

```text
general power difference
-> focused Gap
-> cyclotomic phase decomposition
-> prime/composite degree structure
-> residual exponent/unit gauge.
```

The previous FLT3/5/7 Ultra audit established a real common obstruction after
power extraction: for fixed source/order/ramifier normalization, the residual
unit class modulo p-th powers is root-choice independent but normalization
dependent.

This branch asks whether that phenomenon can be understood as a downstream
effect of a more primitive "Gap focusing" structure.

## Starting identities

The basic focused identity is

```text
(x+u)^d - u^d = x * GN_d(x,u).
```

For arbitrary anchors u,v,

```text
(x+u)^d - v^d
  = x * GN_d(x,u) + (u^d - v^d).
```

Thus the residual `u^d-v^d` measures failure of the chosen anchor to focus
the difference onto the single Gap coordinate x.

The cyclotomic form is expected to expose the same distinction:

```text
(x+u)^d - u^d
  = product_{zeta^d=1} (x + (1-zeta)u).
```

The trivial phase zeta=1 produces the exact factor x; the other phases retain
the background/scale u.

## Core hypotheses to test

1. **Gap focusing is structural.**
   The transformation from `(a,b)` to `(x,u)` separates a pure Gap direction
   from phase/background information rather than merely renaming variables.

2. **Composite degree has internal routes.**
   Existing product-degree GN identities for `d=ab` may encode lower-degree
   factor routes corresponding to nontrivial divisors of d.

3. **Prime degree is rigid.**
   For prime p, there is no nontrivial degree-factor route analogous to
   `d=ab` with a,b>1.  Determine whether this can be expressed as an honest
   theorem schema rather than a slogan.

4. **Unit gauge is downstream, not assumed.**
   Test whether the normalization-fixed class
   `[u] in R^×/(R^×)^p` from the FLT3/5/7 audit is naturally related to the
   residual nontrivial phase freedom after Gap focusing.

5. **2p is a composite-degree calibration.**
   Analyze `2p=p*2` algebraically.  Record what would be required to connect
   it to the separately observed planar/magic-square 2p phenomenon.  Do not
   assume the geometric interpretation.

## Boundaries

This is a structural research audit, not a new FLT proof campaign.

Do not:

- encode landing/descent conclusions as fields of a generic structure;
- infer element equality from norm equality;
- claim a universal periodic/moire law without a checked invariant;
- claim a magic-square theorem from the algebraic `2p` factorization alone;
- refactor production code for cosmetic uniformity.

Prefer existing `DkMath.Lib.*`, GN, cyclotomic, DRC, and the merged FLT3/5/7
audit results.  Small neutral Lean probes are welcome when they distinguish a
real theorem from an attractive interpretation.

## Possible outcomes

- **Outcome A:** Gap focusing, degree rigidity, and residual unit gauge form one
  checked structural chain.
- **Outcome B:** Gap focusing and prime/composite degree rigidity are genuine,
  but the FLT unit gauge is a later arithmetic layer requiring extra source and
  normalization data.
- **Outcome C:** the focusing operation is mainly a coordinate presentation;
  the essential arithmetic structure begins elsewhere.

All three outcomes are useful.

## Instruction 004 checkpoint

[Report 004](report-004.md) — Outcome B. The lower degree-two cyclotomic/order bridge, complete shell residue class and finite frequency are checked. Fixed-seat divisibility supplies a weighted lower-sector persistence cap and a conditional fresh-incidence bound; a twenty-transition regression forces at least 76 fresh incidences under the existing simultaneous full-cover hypothesis. No strict reduction of an existing residual capacity is proved.

[Source inventory](source-inventory-004.md) · [Findings](findings-004.md) · [Validation](validation-004.md).

## Instruction 005 checkpoint

[Report 005](report-005.md) — Outcome A in the finite support-excess case. Candidate parity doubles the fixed-seat prime-address period to 2q and strictly lowers the main-block temporal cap from 169 to 97. Exact fresh/first-slot cost accounting forces at least 38 units of existing support excess, under the existing simultaneous full-cover hypothesis, and adds +38 to the existing summed candidate/incidence necessary balance. Residual/collision recipient localization and a global full-cover contradiction remain unproved.

[Source inventory](source-inventory-005.md) · [Findings](findings-005.md) · [Validation](validation-005.md).

## Instruction 006 checkpoint

[Report 006](report-006.md) — Outcome C for the new cancellation question. The checked38 is localized exactly into existing outside support and collision support, but supplies no new obstruction after incidence elimination. The actual main block is refuted and a prime in a square cell with n in21..40 is extracted; the same refutation follows from the mature ledger without38. Exact support-only slack is490, and the strongest second-cancellation support-charge slack is72. Generic block localization and independent-upper-capacity contradiction consumers are exported by the facade.

[Source inventory](source-inventory-006.md) · [Findings](findings-006.md) · [Validation](validation-006.md).

## Instruction 007 checkpoint

[Report 007](report-007.md) — Outcome A for explicit block width shrinking. A full-cover-independent wave cap combines2q packing, exact odd quotient endpoints and the best single odd-anchor-prime exclusion. The N=20,T=20 cap425 supplies an unconditional uncovered lower bound65 without exact I=418. All prescribed widths down to1 succeed at N=20; shell21 has at least5 uncovered candidates and a square-cell prime. No uniform-in-N result is proved. Two-divisor exclusion and local independent excess certificates are proposed as the next development.

[Source inventory](source-inventory-007.md) · [Findings](findings-007.md) · [Validation](validation-007.md).

## Instruction 008 checkpoint

[Report 008](report-008.md) — Outcome A for the hybrid provider. A Nat-safe two-prime inclusion-exclusion cap proves I<=B2<=B and lowers the main cap425 to418. Finite support witnesses at shell29 seats14,56 prove excess>=4, uncovered>=1 and a prime in(841,900), without evaluating whole-shell incidence/excess. With a two-seat/three-prime certificate budget, shells2..100 partition into59 zero-excess successes,10 certificate successes and30 unresolved. The new cap gains77,85,95 under that same budget. A general theorem fixes the limit B2=B on anchors2^a*p^k; no uniform prime-existence provider is proved. Next proposals target certificates whose charge scales with the remaining deficit.

[Source inventory](source-inventory-008.md) · [Findings](findings-008.md) · [Validation](validation-008.md).

## Instruction 009 checkpoint

[Report 009](report-009.md) — Outcome A for adaptive certificate providers. Three-seat active-support witnesses prove excess≥6 and uncovered≥2 at41 and91, yielding square-cell primes without whole-shell incidence/excess evaluation. A three-seat/three-witness budget resolves five of the previous30 unresolved shells, leaving25 whose demand exceeds6. The new CRT module proves support transport, parity-adjusted short-window existence, prime-anchor candidate coprimality and distinct same-modulus lift families with charge floor((n−1)/product(Q))·(Q.card−1). It supplies a quantitative infinite-class excess provider; uniform demand sufficiency remains unproved. Next proposals target actual required charge, merging colliding seat witnesses and mixed-anchor CRT.

[Source inventory](source-inventory-009.md) · [Findings](findings-009.md) · [Validation](validation-009.md).

## Instruction 010 checkpoint

[Report 010](report-010.md) — Outcome B for fixed-pool demand scaling. Witness unions at actual image seats provide a reusable excess lower bound without injectivity; a structural counterexample rejects naive family-index summation. Mixed anchors2^a*p^k have a parity/coprimality CRT selector and a counted floor(n/(p*product(Q))) family. Two overlapping prime-anchor pair families prove12(n−1)≤105E+198. A controlled basis7 solves24 of the25 previous survivors, and adding23,29,31 at97 solves the last; the same expansion proves primes at107 and127. Both fixed bases fail the checked demand at211/503. Uniform charge sufficiency remains unproved. Next proposals target growing bases, incremental witness-union charge and all-unit mixed selectors.

[Source inventory](source-inventory-010.md) · [Findings](findings-010.md) · [Validation](validation-010.md).
