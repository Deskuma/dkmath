# Instruction 028 - Gnomon divisor incidence and binary carry mass

## Mission

Continue from Instruction 027.

Instruction 027 compressed the higher prime-power shell correction to an explicit log-log-style budget.

The remaining universal frontier is a lower bound for:

  psi(n^2+2*n) - psi(n^2).

Report 027 proposed an exact bridge from the gnomon Pascal product to shell von Mangoldt mass by making lower divisors explicit.

This checkpoint must implement that bridge and then refine it one step further.

The main goal is not merely:

  log(cell) + log((2*n)!)
  =
  shellVonMangoldtMass + lowerDivisorMass.

The stronger target is to subtract the uniform factorial contribution from lower-divisor multiplicities and expose the residual as a binary floor-carry mass.

Let:

  base = n^2
  width = 2*n
  top = base + width.

For positive d define the shell multiple count:

  M_n(d) = top / d - base / d.

This is the exact number of multiples of d in the strict integer shell:

  base < m <= top.

For lower divisors d<=base, compare this with the uniform width count:

  width / d.

The addition formula for natural division gives:

  M_n(d)
  =
  width / d + carry_n(d)

where carry_n(d) is either 0 or 1 and is determined by the remainder phase:

  d <= base % d + width % d.

Define the lower carry mass:

  K(n)
  =
  sum over d in Icc 1 base of
    carry_n(d) * Lambda(d).

The principal exact target is:

  log(GnomonPascalCell n)
  =
  gnomonPascalShellVonMangoldtMass n
  +
  K(n).

This should then agree exactly with the already proved Pascal ledger:

  gnomonPascalOldLogBudget n
  =
  gnomonPascalShellHigherPrimePowerMass n
  +
  K(n).

Thus this checkpoint must determine whether the divisor-incidence route creates a genuinely new lower-bound object or merely gives a more geometric coordinate for the old carry frontier.

The expected new value, even if it is an equivalent coordinate, is that K(n) is supported on binary phase-crossing prime-power labels rather than full prime valuations.

Do not claim a Legendre proof from the identity alone.

All new instruction, findings, logs, and report artifacts must remain parser-safe plain text. Avoid backslash notation and LaTeX control sequences.

## Branch and workspace

Repository: Deskuma/dkmath

Branch: research/GapFocusing-ExponentGauge-Ultra-261004-v0

Workspace:

lean/dk_math/docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/

Read report-027.md before editing.

## Phase 0 - source audit

Audit at minimum:

DkMath.NumberTheory.Legendre.GnomonPascalCell
DkMath.NumberTheory.Legendre.SquareShellVonMangoldt
DkMath.NumberTheory.Legendre.SquareShellPrimePowerGauge
DkMath.NumberTheory.BinomialPrimePower

Audit Mathlib:

Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
Mathlib.Data.Nat.Choose.Factorization
Mathlib.Data.Nat.Factorization.Basic
Mathlib.Data.Nat.Factorial.BigOperators
Mathlib.Algebra.BigOperators.Intervals

Expected declarations:

- ArithmeticFunction.vonMangoldt_sum
- ArithmeticFunction.vonMangoldt_apply
- ArithmeticFunction.vonMangoldt_nonneg
- Nat.factorization_factorial
- Nat.factorization_choose
- Nat.add_div
- Nat.div_add_mod
- Nat.prod_factorization
- Real.log_prod
- Real.log_mul
- Real.log_nat_eq_sum_factorization

Reuse existing DkMath declarations:

- gnomonPascalCell_mul_factorial
- gnomonPascalCell_factorization_carries
- gnomonPascalCell_log_eq_old_add_birth
- gnomonPascalOldLogBudget
- gnomonPascalShellVonMangoldtMass
- gnomonPascalShellHigherPrimePowerMass
- gnomonPascalShellVonMangoldtMass_eq_birth_add_higher

Record source-inventory-028.md before substantial production work.

## Phase 1 - shell multiple count

Define:

  gnomonShellMultipleCount n d

for positive d as:

  (n^2+2*n)/d - n^2/d.

A total Nat definition may use the same formula for d=0, but all arithmetic theorems must state d>0 explicitly.

Prove the counting theorem:

For d>0,

  gnomonShellMultipleCount n d

equals the card of integers m in:

  Icc (n^2+1) (n^2+2*n)

such that d divides m.

Prefer an exact Finset filter theorem.

This is a reusable arithmetic lemma and should not mention von Mangoldt.

## Phase 2 - full divisor-incidence transpose

For n>=1 prove an exact finite identity:

  sum over shell integers m of
    sum over d in m.divisors of Lambda(d)

  =
  sum over d in Icc 1 top of
    gnomonShellMultipleCount n d * Lambda(d).

Use finite incidence transposition.

Do not use analytic Chebyshev estimates.

All carriers are finite.

## Phase 3 - shell log product as divisor mass

Use:

  ArithmeticFunction.vonMangoldt_sum

pointwise on every positive shell integer.

Prove:

  sum over shell m of log(m)
  =
  sum over d in Icc 1 top of
    gnomonShellMultipleCount n d * Lambda(d).

Then prove the multiplicative form:

  log(product of shell integers)
  =
  the same divisor mass.

Reuse positivity of all shell integers.

## Phase 4 - Pascal product log identity

Use:

  gnomonPascalCell_mul_factorial.

For n>=1 prove:

  log(GnomonPascalCell n)
  +
  log((2*n)!)
  =
  sum over shell m of log(m).

Then combine with Phase 3.

This is the product-to-von-Mangoldt bridge.

No lower bound is asserted yet.

## Phase 5 - lower divisor shell mass

Define:

  gnomonPascalLowerDivisorMass n
  =
  sum over d in Icc 1 (n^2) of
    gnomonShellMultipleCount n d * Lambda(d).

Prove nonnegativity.

Prove for n>=3:

  full divisor mass
  =
  gnomonPascalLowerDivisorMass n
  +
  gnomonPascalShellVonMangoldtMass n.

The high-divisor proof must be exact.

For n>=3 and:

  n^2 < d <= top

show:

- top < 2*d
- the shell multiple count of d is exactly 1
- therefore the high-divisor term is exactly Lambda(d)

and the carrier Icc(n^2+1,top) is exactly the strict shell integer carrier.

## Phase 6 - main report-027 identity

Combine Phases 4 and 5.

Required theorem for n>=3:

  log(GnomonPascalCell n)
  +
  log((2*n)!)
  =
  gnomonPascalShellVonMangoldtMass n
  +
  gnomonPascalLowerDivisorMass n.

Suggested name:

  gnomonPascalCell_log_add_factorial_eq_shellVM_add_lowerDivisorMass

This is a primary acceptance theorem.

## Phase 7 - generic factorial von Mangoldt floor identity

Prove or reuse a neutral theorem:

For N:

  log(N!)
  =
  sum over d in Icc 1 N of
    (N/d) * Lambda(d).

A version summing to any larger cutoff B>=N with zero quotient outside N is also useful.

Preferred proof:

- expand log(k) by vonMangoldt_sum
- transpose divisor incidence
- count multiples of d in Icc 1 N

or reuse an existing Mathlib theorem if found.

Do not prove the same result twice through factorization and divisor incidence unless one form is materially needed.

## Phase 8 - binary carry bit

Define:

  gnomonLowDivisorCarryBit n d

for positive d by the exact remainder predicate:

  if d <= n^2 % d + (2*n) % d then 1 else 0.

For d=0 choose a harmless total value, preferably zero.

Prove for d>0:

  gnomonShellMultipleCount n d
  =
  (2*n)/d + gnomonLowDivisorCarryBit n d.

This should be a thin consequence of Nat.add_div.

Then prove:

- carryBit is 0 or 1
- carryBit <= 1
- carryBit = 1 iff d <= n^2 % d + (2*n) % d
- carryBit = 0 iff the strict reverse inequality holds

Do not turn Bool and Nat representations into parallel APIs unless necessary.

## Phase 9 - phase-distance characterization

For d>0 define or expose the distance to the next multiple after n^2.

A safe total form may be:

  nextMultipleGap(base,d)

with the convention that if base%d=0 the gap is d, otherwise d-base%d.

Prove that carryBit=1 is equivalent to:

  nextMultipleGap(n^2,d) <= (2*n) % d.

If d>2*n, then width%d=2*n, so derive:

  carryBit=1
  iff
  nextMultipleGap(n^2,d) <= 2*n.

Interpretation:

the next d-grid point after the square boundary lands inside the open shell.

This is the phase/address form of the carry.

## Phase 10 - lower carry mass

Define:

  gnomonPascalLowDivisorCarryMass n
  =
  sum over d in Icc 1 (n^2) of
    carryBit(n,d) * Lambda(d).

Prove nonnegativity.

Using Phase 8, split lower divisor mass exactly:

  lowerDivisorMass
  =
  factorialLogContribution
  +
  lowCarryMass.

For n>=3, preferred theorem:

  gnomonPascalLowerDivisorMass n
  =
  log((2*n)!)
  +
  gnomonPascalLowDivisorCarryMass n.

This uses the fact that 2*n <= n^2.

## Phase 11 - central cancellation identity

Cancel the factorial term between Phase 6 and Phase 10.

Required theorem for n>=3:

  log(GnomonPascalCell n)
  =
  gnomonPascalShellVonMangoldtMass n
  +
  gnomonPascalLowDivisorCarryMass n.

This is the central theorem of Instruction 028.

It expresses the Pascal-cell log as:

- true shell von Mangoldt mass
- plus lower prime-power phase-crossing carry mass

with no hidden factorial term.

## Phase 12 - exact comparison with the old Pascal ledger

Use the existing exact identities:

  log(cell) = oldBudget + birthMass

and:

  shellVM = birthMass + higherCorrection.

Combine them with Phase 11.

Prove the subtraction-free identity:

  gnomonPascalOldLogBudget n
  =
  gnomonPascalShellHigherPrimePowerMass n
  +
  gnomonPascalLowDivisorCarryMass n.

This is mandatory.

It determines exactly how much novelty the new coordinate has.

Equivalent rearrangements using subtraction may be added only as corollaries.

## Phase 13 - prime-power support of low carry mass

Because Lambda(d) is nonzero only at prime powers, prove an exact filtered form:

  lowCarryMass
  =
  sum over d in Icc 1 n^2 with
    IsPrimePow d and carryBit=1
  of Lambda(d).

If possible, define:

  gnomonPascalLowCarryEvents n

as that carrier.

Prove exact membership.

Then:

  lowCarryMass
  =
  sum d in lowCarryEvents of Lambda(d).

This makes the frontier a finite event carrier rather than a weighted full interval.

## Phase 14 - relation to existing choose carries

For a prime p, compare:

  gnomonPascalCell_factorization_carries

with lowCarryEvents at labels p^i.

The desired exact statement is:

For every prime p, the old part of the p-adic factorization height of the gnomon cell equals the number of powers p^i<=n^2 whose low carry bit is one.

The fresh/higher shell powers should account for the remaining factorization contribution above n^2.

Do not force a complicated theorem if a clean sum-level identity already proves the same fact.

At minimum prove pointwise compatibility:

For d=p^i with i>0 and d<=n^2,

  carryBit(n,d)=1

iff

  d <= (2*n)%d + n^2%d,

which is the exact predicate used by Nat.factorization_choose.

## Phase 15 - low and high divisor bands

Split low carry events into:

- small labels d<=2*n
- large labels 2*n<d<=n^2.

For the large band prove:

  width%d = 2*n

and hence carry occurs iff the next multiple of d after n^2 lies inside the shell.

For the small band keep the exact modular remainder form.

Define band masses only if they have a consumer.

The goal is to identify which band dominates and which one may admit the next bound.

## Phase 16 - large-band shell-multiple map

For a large carry event d>2*n, define its unique shell multiple:

  m = d * (n^2/d + 1).

Prove:

- SquareCell n m
- d divides m
- m is the unique shell multiple of d

under carryBit=1.

Study the map:

  d -> m.

Do not assume injectivity.

Record exact collision semantics:

different prime-power labels d may map to the same shell integer m precisely when that shell integer has multiple such divisors.

This should connect to the existing support/factorization perspective without restarting deletion packing.

## Phase 17 - divisor-depth interpretation

For a low carry event d that is a prime power:

  d=p^a.

Record:

  Lambda(d)=log p.

If d>2*n, the unique shell multiple m=d*k has k<n or an exact comparable quotient bound if true.

Investigate simple quotient constraints but do not overclaim.

The purpose is to expose whether large carry events correspond to high prime-power divisors of shell integers with small cofactors.

## Phase 18 - exact conditional lower-bound provider

From Phase 11 prove a generic consumer:

If:

  lowCarryMass <= B

and:

  B + desiredMargin < log(GnomonPascalCell n)

then:

  desiredMargin < shellVonMangoldtMass n.

Specialize desiredMargin to the Instruction 027 log-log higher correction budget.

Thus for n>=3, if:

  lowCarryMass
  +
  shellHigherPrimePowerLogLogBudget n
  <
  log(GnomonPascalCell n)

then the shell contains a prime.

Then use Phase 12 to determine whether this condition is new or exactly equivalent to the old-budget strict criterion.

The report must state the answer explicitly.

## Phase 19 - multiplicative growth lower bound

Audit and expose a clean lower bound for the gnomon cell or shell product.

Use existing Mathlib or DkMath results when available.

Candidate:

  Nat.pow_le_choose

at:

  N = n^2+2*n
  k = 2*n.

Together with the exact factorial product identity, derive a lower bound on:

  log(GnomonPascalCell n)

or on:

  log(cell) + log((2*n)!).

Do not confuse a product lower bound with a shell von Mangoldt lower bound.

The low carry mass must remain explicitly subtracted.

## Phase 20 - carry diagnostics

Extend exact integer diagnostics through at least n=5000.

For each n record:

- number of low carry events
- low carry event labels
- prime-power base and depth
- small-band count
- large-band count
- low carry mass
- old Pascal budget
- higher correction
- verify oldBudget = higher + lowCarry
- shell von Mangoldt mass
- log cell
- verify logCell = shellVM + lowCarry
- maximum number of carry labels mapping to one shell integer
- distribution of unique shell multiples in the large band

Real logs may remain floating diagnostics.

All carrier equalities and integer counts should be independently reconstructed.

Mandatory anchors:

  3
  5
  11
  19
  29
  297
  1031.

## Phase 21 - kernel calibrations

Kernel-check finite carrier structure for representative small anchors.

At minimum certify:

- one anchor with no higher correction
- n=5
- n=11
- one anchor with a nontrivial small-band carry
- one anchor with a nontrivial large-band carry
- n=297
- n=1031

For each selected label d certify:

- prime-power status
- carry bit
- remainder predicate
- shell multiple count
- large-band unique shell multiple when applicable

Do not kernel-evaluate large transcendental inequalities.

## Phase 22 - route judgment

This phase is mandatory and skeptical.

Determine which statement is true.

A. The binary carry coordinate exposes a new structurally smaller frontier with a plausible independent bound.

B. The exact identities close, but lowCarryMass is only the old Pascal budget minus the already-small higher correction. It is a better coordinate but no new inequality yet.

C. Large-band unique shell multiples or another phase theorem produces a genuinely new upper bound on lowCarryMass.

D. One exact divisor-incidence or factorial cancellation bridge remains.

Do not label an exact change of variables as a new provider.

## Phase 23 - next theorem selection

If the result is mainly Outcome B, do not immediately add another equivalent ledger.

Use diagnostics and large/small band structure to choose one precise next theorem.

Preferred candidates include:

- a bound on large-band carry mass via shell divisor multiplicity
- a bound on small-band carry mass via periodic phase density
- a quotient/cofactor bound for large carry events
- a direct comparison between low carry mass and a provable fraction of log cell

Choose exactly one based on proved data.

Do not return to FLT7 or deletion packing inside this checkpoint.

## Possible outcomes

Outcome A - DIVISOR INCIDENCE EXPOSES A NEW BINARY CARRY FRONTIER

The exact Pascal-product and von Mangoldt bridge closes, and the residual old contribution becomes a binary phase-crossing event mass with a materially sharper structural constraint.

Outcome B - BINARY CARRY MASS IS AN EXACT RECOORDINATION OF THE OLD FRONTIER

All exact identities close, including oldBudget = higherCorrection + lowCarryMass, but no new universal upper bound on lowCarryMass is obtained.

Outcome C - SHELL-MULTIPLE GEOMETRY YIELDS A NEW LOW-CARRY BOUND

The large/small band analysis produces a genuinely stronger upper bound on lowCarryMass.

Outcome P - ONE DIVISOR-INCIDENCE CANCELLATION BRIDGE REMAINS

The finite incidence setup is correct but one exact product, factorial, or carry cancellation theorem blocks the central identity.

## Non-goals

Do not claim:

- Legendre conjecture
- a universal lower bound on shell von Mangoldt mass
- that lowerDivisorMass itself is small
- that lowCarryMass is new information before comparing with the old ledger
- injectivity of the large carry event to shell multiple map without proof
- PNT or RH
- a short-interval Chebyshev theorem
- that multiplicative Pascal growth alone forces a shell prime

Do not resume terminal cofactor, deletion packing, or FLT7.

## Suggested implementation surface

Possible production module:

DkMath/NumberTheory/Legendre/GnomonDivisorCarry.lean

Neutral multiple-count or factorial-von-Mangoldt lemmas may live in a lower NumberTheory module if they are genuinely reusable.

Keep the Legendre facade dependency one-way.

Update the facade after focused builds pass.

## Validation

Use:

  LEAN_NUM_THREADS=2

for final focused, facade, root, and axiom-audit validation unless a measured reason suggests otherwise.

Record /usr/bin/time -v telemetry again when available.

For all new public declarations:

- focused build
- Legendre facade build
- DkMath root build
- print axioms
- forbidden-token scan
- git diff --check

No new sorryAx dependencies.

## Durable checkpoint protocol

Update findings after:

- source audit
- shell multiple count
- incidence transpose
- log shell-product identity
- lower-divisor split
- main cell/factorial identity
- factorial floor identity
- binary carry bit
- phase-distance characterization
- low carry mass
- central log cell identity
- old ledger comparison
- prime-power event carrier
- choose-carry compatibility
- small/large band split
- large-band shell-multiple map
- diagnostics
- route judgment

Preserve failed conjectures and smallest counterexamples.

## Final report

Answer explicitly:

1. What exact shell multiple-count function was defined?
2. Is it proved to count shell multiples of d?
3. Was the von Mangoldt divisor incidence sum transposed exactly?
4. Is log(shell product) exactly the full divisor mass?
5. Is log(cell)+log((2*n)!) exactly shellVM+lowerDivisorMass?
6. Was log((2*n)!) expressed as a divisor-floor von Mangoldt sum?
7. What exact binary carry bit was defined?
8. Is shellMultipleCount = width/d + carryBit proved?
9. Is the carry bit exactly the remainder-phase crossing condition?
10. What next-multiple-gap characterization was proved?
11. Is lowerDivisorMass exactly factorialLog + lowCarryMass?
12. Is log(cell) exactly shellVM + lowCarryMass?
13. Is old Pascal budget exactly higherCorrection + lowCarryMass?
14. Is lowCarryMass exactly supported on prime-power carry events?
15. How does this match gnomonPascalCell_factorization_carries?
16. What small-band and large-band decomposition was obtained?
17. Does every large carry label have a unique shell multiple?
18. Is the large carry label to shell multiple map injective? If not, give the smallest collision.
19. Does the new conditional prime criterion reduce exactly to the old strict budget criterion?
20. What do diagnostics show for 297 and 1031?
21. Did the divisor-incidence coordinate produce a genuinely new bound?
22. What single theorem should Instruction 029 attempt?

End with exactly one judgment:

Outcome A - DIVISOR INCIDENCE EXPOSES A NEW BINARY CARRY FRONTIER
Outcome B - BINARY CARRY MASS IS AN EXACT RECOORDINATION OF THE OLD FRONTIER
Outcome C - SHELL-MULTIPLE GEOMETRY YIELDS A NEW LOW-CARRY BOUND
Outcome P - ONE DIVISOR-INCIDENCE CANCELLATION BRIDGE REMAINS
