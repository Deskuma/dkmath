# Instruction 026 - Square-shell von Mangoldt split and prime-power gauge gap

## Mission

Continue from Instruction 025.

Instruction 025 closed the exact Pascal prebirth boundary:

- preceding-row alternating residues are equivalent to next-row common divisibility
- common prime divisibility classifies positive prime-power rows
- prime rows are exactly the self-modulus prebirth boundary
- prime birth is separated from higher prime-power resynchronization
- the gnomon Pascal cell detects fresh shell prime factors exactly
- shell prime existence is exactly positive shell prime-birth log mass
- the cell logarithm splits exactly into an old coordinate budget plus shell birth mass

The remaining Legendre frontier is a strict old-budget inequality.

Instruction 026 must change coordinates before attempting that inequality.

The key square-shell observation is:

A prime-power event q = p^a inside the strict shell

  n^2 < q < (n+1)^2

cannot have even exponent a, because every even power is a square.

Therefore every nonprime prime-power event in the shell has odd exponent at least 3.

Its von Mangoldt weight is:

  log p = (1/a) * log q

so the relative prime-power gauge is at most one third.

This creates a square-shell-specific gap:

- genuine prime birth has exponent 1 and gauge 1
- exponent 2 is absent
- old prime-power resynchronization has exponent at least 3 and gauge at most 1/3

The checkpoint must formalize this exact split, compress the higher-prime-power correction as sharply as possible, and judge whether it yields a genuinely smaller Legendre frontier.

A second major target is to prove that for each fixed exponent a >= 3, at most one a-th power can lie in one strict square shell. If successful, the number of higher-power shell events is logarithmic in the shell height, and their total von Mangoldt mass admits a polylogarithmic-style finite bound rather than an O(n) old-prime bound.

Do not assume this stronger sparsity theorem until Lean proves it.

All new instruction, findings, logs, and report artifacts must remain parser-safe plain text. Avoid backslash notation and LaTeX control sequences.

## Branch and workspace

Repository: Deskuma/dkmath

Branch: research/GapFocusing-ExponentGauge-Ultra-261004-v0

Workspace:

lean/dk_math/docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/

Read report-025.md before editing.

## Phase 0 - broad audit

Audit at minimum:

DkMath.NumberTheory.Legendre.GnomonPascalCell
DkMath.NumberTheory.PascalPrebirthBirth
DkMath.NumberTheory.PascalPrebirthBoundary
DkMath.NumberTheory.BinomialPrimePower
DkMath.NumberTheory.PrimitiveSet.VonMangoldtShadow
DkMath.RH.CFBRC.PascalPrimePowerCanonicalFold
DkMath.RH.CFBRC.PascalVonMangoldtLSeriesBridge

Audit Mathlib:

Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
Mathlib.NumberTheory.Chebyshev
Mathlib.Algebra.IsPrimePow
Mathlib.Data.Nat.Factorization.PrimePow
Mathlib.Data.Nat.Prime.Pow

Expected reusable declarations include:

- ArithmeticFunction.vonMangoldt_apply
- ArithmeticFunction.vonMangoldt_apply_pow
- ArithmeticFunction.vonMangoldt_apply_prime
- ArithmeticFunction.vonMangoldt_eq_zero_iff
- isPrimePow_nat_iff
- isPrimePow_nat_iff_bounded_log_minFac
- IsPrimePow.minFac_pow_factorization_eq
- Nat.Prime.pow_minFac
- Chebyshev.psi_eq_sum_Icc
- Chebyshev.theta_eq_sum_Icc
- Chebyshev.theta_eq_sum_primesLE_log
- Chebyshev.sum_PrimePow_eq_sum_sum
- Chebyshev.psi_eq_sum_theta
- Chebyshev.psi_sub_theta_le_mul_sqrt
- Chebyshev.theta_le_log4_mul_x

Do not import high-level RH modules into foundational Legendre code merely to reuse canonical shadow names.

Prefer Mathlib ArithmeticFunction.vonMangoldt and IsPrimePow directly in the Legendre layer.

Record source-inventory-026.md before substantial production edits.

## Phase 1 - shell von Mangoldt mass

Define the exact shell prime-power mass:

  gnomonPascalShellVonMangoldtMass n
  =
  sum over r in squareOffsets n of
    ArithmeticFunction.vonMangoldt (n^2+r).

Prove nonnegativity.

Prove the exact Chebyshev difference formula:

  shellVonMangoldtMass n
  =
  Chebyshev.psi (n^2+2*n)
  -
  Chebyshev.psi (n^2).

Use exact finite-sum splitting, not an asymptotic argument.

Handle n=0 explicitly.

This theorem identifies the shell observable with a standard arithmetic function.

## Phase 2 - pointwise prime versus higher-prime-power split

Define a pointwise higher-prime-power weight:

  higherPrimePowerWeight q

which is von Mangoldt q exactly when:

  IsPrimePow q
  and not q.Prime

and zero otherwise.

Then prove for every q:

  vonMangoldt q
  =
  pascalPrimeBirthLogMass q
  +
  higherPrimePowerWeight q.

The proof must distinguish:

- prime
- nonprime prime power
- non-prime-power

and reuse the exact Mathlib von Mangoldt formulas.

Do not identify all prime powers with prime birth.

## Phase 3 - shell higher-prime-power correction

Define:

  gnomonPascalShellHigherPrimePowerMass n

as the sum of higherPrimePowerWeight over squareOffsets.

Sum the pointwise split to prove:

  shellVonMangoldtMass n
  =
  gnomonPascalShellBirthLogMass n
  +
  shellHigherPrimePowerMass n.

This is the square-shell theta versus psi split.

Also prove:

  shellHigherPrimePowerMass n >= 0.

If convenient, expose the exact carrier of shell values q that are:

  SquareCell n q
  and IsPrimePow q
  and not q.Prime.

Call this the higher-prime-power event carrier.

## Phase 4 - no perfect square in a strict square shell

Prove the elementary theorem:

For all n and m:

  not SquareCell n (m^2).

This should be fully generic and independent of primality.

Preferred proof:

  n^2 < m^2 implies n < m
  m^2 < (n+1)^2 implies m < n+1
  contradiction in Nat.

Reuse strict monotonicity of squaring or prove the needed Nat inequality cleanly.

This is a basic square-shell theorem and may belong in Basic.lean if dependency direction is appropriate.

## Phase 5 - no even prime-power exponent

For prime p and positive even exponent a, prove:

  not SquareCell n (p^a).

Use:

  a = 2*b
  p^a = (p^b)^2

and Phase 4.

Do not special-case exponent 2 only.

Then derive:

If:

  q is a nonprime prime power
  and SquareCell n q

then any prime-power witness q=p^a has:

  3 <= a
  and Odd a.

The witness theorem may use isPrimePow_nat_iff.

## Phase 6 - canonical minFac depth packet

For a shell higher-prime-power event q, avoid arbitrary witness dependence when possible.

Use:

  p = q.minFac
  a = q.factorization q.minFac.

Prove:

- p.Prime
- 3 <= a
- Odd a
- q = p^a
- p <= n for n>=3
- p^3 < (n+1)^2.

The equality should reuse:

  IsPrimePow.minFac_pow_factorization_eq.

This packet is the canonical arithmetic description of a shell resynchronization.

## Phase 7 - relative gauge gap

For a shell higher-prime-power event q with canonical p and exponent a, prove the exact log relation:

  ArithmeticFunction.vonMangoldt q
  =
  Real.log p

and:

  Real.log q
  =
  a * Real.log p.

Then prove either or both of:

  3 * vonMangoldt q <= Real.log q

and:

  pascalPrimePowerLogGauge p a <= 1/3.

The multiplicative inequality is preferred as the low-dependency theorem.

For genuine prime q prove the contrasting equality:

  vonMangoldt q = Real.log q.

Document the exact square-shell gauge gap:

  prime event weight ratio = 1
  higher event weight ratio <= 1/3.

Do not claim any continuous interpolation between them.

## Phase 8 - same base prime cannot occur twice in one shell

For n>=3, prove:

If:

  q1 and q2 are prime powers
  SquareCell n q1
  SquareCell n q2
  q1.minFac = q2.minFac

then:

  q1 = q2.

A witness-based equivalent theorem is acceptable:

If p is prime and p^a and p^b both lie in the same shell, then a=b.

Preferred proof:

Two distinct powers of the same p differ by a factor at least p>=2, while the ratio between shell endpoints is less than 2 for n>=3.

Avoid Real division if a Nat inequality proof is cleaner.

This theorem makes the minFac map injective on the higher-event carrier.

## Phase 9 - old-base injection and theta bound

Use Phase 8 and the canonical packet.

Map each shell higher-prime-power event q to q.minFac.

Prove:

- the map is injective
- its image consists of primes at most n

for n>=3.

Then reindex the higher mass:

  shellHigherPrimePowerMass n
  =
  sum over base primes in the image of Real.log p.

Derive the exact uniform bound:

  shellHigherPrimePowerMass n
  <= Chebyshev.theta n.

Use:

  Chebyshev.theta_eq_sum_primesLE_log.

This is a required theorem.

It shrinks the correction universe from all old prime coordinates up to n^2 to old base primes at most n.

## Phase 10 - fixed-exponent shell uniqueness

This is a major experimental theorem target.

For n>=3 and exponent a>=3, investigate and prove:

If:

  x<y
  SquareCell n (x^a)
  SquareCell n (y^a)

then contradiction.

Equivalently:

For fixed a>=3, a strict square shell contains at most one natural a-th power.

A possible Nat proof route is:

- shell membership gives x<=n and y<=n
- x^a>n^2 and y^a>n^2
- derive x^(a-1)>n and y^(a-1)>n
- factor y^a-x^a
- its factor sum contains at least x^(a-1)+y^(a-1)
- therefore y^a-x^a>2*n
- but two shell points differ by at most 2*n

This route is only a proposal. Lean must verify every boundary.

If false, find the smallest counterexample and stop using it.

## Phase 11 - exponent-indexed higher-event carrier

If Phase 10 succeeds, define for each exponent a:

  shellPrimePowerBasesAtExponent n a

as prime bases p such that:

  SquareCell n (p^a).

Prove for n>=3 and a>=3:

  card <= 1.

Prove the carrier is empty for even a.

Thus only odd exponents a>=3 can contribute, and each contributes at most one prime base.

## Phase 12 - finite exponent cutoff

For any shell prime-power event q=p^a, prove a finite exponent bound using p>=2:

  2^a <= q < (n+1)^2.

Derive a bound in terms of Nat.log base 2, for example:

  a <= Nat.log 2 ((n+1)^2)

or the exact available Mathlib inequality.

Do not invent a new logarithm theory if Mathlib has a suitable theorem.

If Nat.log boundary friction is high, define a simple finite exponent carrier:

  Finset.Icc 3 (Nat.log 2 ((n+1)^2) + 1)

and prove all contributing exponents lie inside it.

## Phase 13 - higher-event count bound

If Phases 10 through 12 close, prove:

  higherEventCarrier.card
  <=
  number of odd exponents a in the finite exponent carrier.

A simpler accepted bound is:

  higherEventCarrier.card
  <=
  Nat.log 2 ((n+1)^2) + 1.

Do not spend excessive code optimizing the plus-one constant.

This is the main combinatorial sparsity theorem.

## Phase 14 - logarithmic mass bound

For every higher shell event, the base prime satisfies p<=n, hence:

  log p <= log n

for n>=3.

Combine with the event-count theorem to derive a fully explicit finite bound such as:

  shellHigherPrimePowerMass n
  <=
  (Nat.log 2 ((n+1)^2) + 1) * Real.log n.

Use the exact casted form that Lean prefers.

If the fixed-exponent uniqueness theorem fails, retain only the theta(n) bound from Phase 9 and classify the stronger route honestly.

## Phase 15 - optional sharper cube-base carrier

Define, only if useful:

  shellHigherBaseCandidates n
  =
  primes p with p<=n and p^3 < (n+1)^2.

Prove the minFac image of higher events is contained in this carrier.

Then derive:

  shellHigherPrimePowerMass n
  <=
  sum over p in shellHigherBaseCandidates n of log p.

This is strictly at least as sharp as the theta(n) bound.

Do not introduce real cube roots unless they materially simplify a later theorem.

## Phase 16 - psi minus theta shell identity

Using Chebyshev functions, prove that the higher-prime-power correction is exactly the increment of psi minus theta across the shell:

  shellHigherPrimePowerMass n
  =
  (psi(top)-theta(top))
  -
  (psi(n^2)-theta(n^2))

with:

  top = n^2+2*n.

Use an additive Nat-safe or Real equality arrangement if direct subtraction rewriting is awkward.

This identifies the new carrier with the classical higher-prime-power correction.

## Phase 17 - Chebyshev bound audit

Audit these Mathlib theorems:

- theta_le_log4_mul_x
- psi_sub_theta_le_mul_sqrt
- psi_le_const_mul_self
- psi_eq_sum_theta

Determine whether any existing unconditional bound gives a useful shell-local estimate stronger than the exact finite bounds from Phases 9 and 14.

Important firewall:

A global bound on psi(x)-theta(x) does not automatically give a sharp increment bound on one short shell.

Do not subtract unrelated upper bounds as if they were monotone-error estimates.

Only add production theorems that are logically valid.

## Phase 18 - fresh-prime criterion from the correction bound

From:

  shellVonMangoldtMass
  =
  birthMass + higherMass

and nonnegativity, prove generic sufficient criteria.

Examples:

If:

  theta(n) < shellVonMangoldtMass n

then:

  shell birth mass > 0

and hence the shell contains a prime.

If the logarithmic event-count bound B(n) is proved, also derive:

If:

  B(n) < shellVonMangoldtMass n

then:

  shell contains a prime.

Route the conclusion through:

  gnomonPascalShellBirthLogMass_pos_iff.

These are conditional providers, not proofs that the inequalities hold.

## Phase 19 - compare with the old Pascal cell budget

The old Instruction 025 frontier was:

  gnomonPascalOldLogBudget n
  <
  log(GnomonPascalCell n).

Compare it with the new shell criterion:

  higherCorrectionBound n
  <
  shellVonMangoldtMass n.

Explain exactly how the coordinates differ.

The new correction concerns only prime-power labels that themselves lie in the square shell.

The old cell budget counts all lower prime-power carry events contributing to the binomial coefficient.

Do not claim one inequality implies the other unless proved.

The goal is to isolate whether the new theta versus psi split genuinely narrows the unresolved object.

## Phase 20 - gnomon top row is not a prime power

Implement the preliminary audit from report 025 if it remains cheap.

Prove for n>=3:

  not IsPrimePow (n*(n+2)).

Recall:

  n^2+2*n = n*(n+2).

Then conclude using Instruction 025:

  pascalInnerCommonDivisor (n^2+2*n) = 1.

This theorem explains that the entire gnomon row is not a global prime-power synchronization boundary.

It does not imply fresh prime existence in the chosen cell.

Preserve that firewall in comments and report.

## Phase 21 - prime-power event diagnostics

Run exact diagnostics over a broad bounded range, for example n from 1 through at least 5000 if inexpensive.

For each n record:

- number of shell primes
- number of higher prime-power shell events
- exponents of higher events
- bases of higher events
- shell von Mangoldt mass
- shell birth mass
- higher correction mass
- theta(n)
- cube-base candidate mass
- event-count logarithmic bound if available

Report:

- maximum number of higher events in one shell
- maximum exponent observed
- whether two events ever share one exponent
- whether two events ever share one base
- smallest shell with a higher event
- smallest shell with more than one higher event
- sharpness ratios for theta and logarithmic bounds

Do not infer universal uniqueness from finite scans.

## Phase 22 - kernel calibrations

Kernel-check named examples covering:

- one shell containing only a prime event
- one shell containing a cube event
- one shell containing a higher odd exponent event if found
- one shell with no higher event
- one shell with more than one higher event if diagnostics find one

Also preserve anchors:

  5
  11
  19
  29
  297
  1031.

For the large anchors, compact event summaries are sufficient.

## Phase 23 - relation to prime-power prebirth gauge

For each shell higher event q=p^a, connect to Instruction 025:

- row q-1 has exact prebirth alternation modulo p
- row q is a p-resynchronization
- pascalPrimePowerLogGauge p a = 1/a
- a>=3 in a strict square shell

Package a thin theorem if this produces a clean conceptual API:

  shellHigherPrimePowerResynchronizationPacket.

For prime q in the shell, contrast with:

  prime_prebirth_birth_packet.

This makes the gauge gap explicit in one theorem layer.

## Phase 24 - reassess the product-certificate proposal

Report 025 proposed an exact old carry product and fresh product factorization.

After the shell von Mangoldt split is formalized, reassess whether that product interface adds any new inequality.

Implement it only if it gives a theorem not already encoded by:

  log cell = old carry budget + birth mass

or by the new shell psi-theta split.

Avoid creating a second equivalent frontier without a consumer.

## Phase 25 - universal-provider judgment

This phase is mandatory.

Classify what the square-shell gauge gap actually buys.

Possible strong results:

A. higher correction gets a genuinely small explicit bound, such as logarithmic event count times log n, and this yields new finite or symbolic prime criteria.

B. theta(n) bound is exact and useful but the fixed-exponent uniqueness route does not close.

C. all exact decompositions are valid but the remaining lower bound on shell von Mangoldt mass is still as hard as the original short-interval prime problem.

D. one precise fixed-exponent power-gap theorem remains.

Do not call the checkpoint successful merely because psi and theta are named.

## Possible outcomes

Outcome A - SQUARE-SHELL GAUGE GAP YIELDS A NEW SMALL HIGHER-POWER BUDGET

The exponent gap and fixed-exponent sparsity produce a substantially smaller explicit higher-prime-power correction bound, ideally logarithmic-event or polylogarithmic in n, and a new conditional or finite Legendre criterion.

Outcome B - VON MANGOLDT SPLIT IS EXACT AND HIGHER EVENTS ARE SPARSE

The exact psi-theta shell split, no-even-exponent theorem, and theta(n) or comparable correction bound close, but the shell lower-mass provider remains unresolved.

Outcome C - PRIME-POWER GAUGE GAP DOES NOT IMPROVE THE LEGENDRE FRONTIER

The structural split is correct, but the available correction bounds do not materially reduce the old-budget problem.

Outcome P - ONE FIXED-EXPONENT POWER-GAP BRIDGE REMAINS

The exact shell split and exponent classification close, but the theorem that one square shell contains at most one a-th power for fixed a>=3 remains the precise blocker to the stronger correction bound.

## Non-goals

Do not claim:

- Legendre conjecture
- PNT or RH
- a short-interval lower bound for psi without proof
- that a global Chebyshev error bound may be subtracted to get a local error bound
- that every square shell contains a prime power
- that higher-prime-power events are absent
- that exponent 2 is the only even exponent to exclude
- that fixed-exponent uniqueness is true before Lean proves it
- that StructuralArithmetic.PowerGauge is the same as the 1/a log gauge
- that the gnomon row not being a prime power implies the selected cell has a fresh prime

Do not resume deletion packing or the 024 cofactor campaign in this checkpoint.

## Suggested implementation surface

Possible modules:

DkMath/NumberTheory/Legendre/SquareShellPrimePower.lean
DkMath/NumberTheory/Legendre/SquareShellVonMangoldt.lean
DkMath/NumberTheory/Legendre/SquareShellPrimePowerGauge.lean

Keep neutral prime-power facts outside Legendre if they are genuinely reusable.

Avoid importing DkMath.RH.CFBRC into Legendre production modules.

Use Mathlib ArithmeticFunction.vonMangoldt and Chebyshev directly.

Update the Legendre facade after focused builds are green.

## Validation

For all new production declarations:

- focused builds
- lake build DkMath.NumberTheory.Legendre
- lake build DkMath
- forbidden-token scan
- print axioms for every new public declaration
- git diff --check

No new sorryAx dependencies.

Existing unrelated root warnings may remain.

## Durable checkpoint protocol

Update findings after:

- source audit
- shell von Mangoldt mass
- prime versus higher split
- no-square theorem
- no-even-exponent theorem
- canonical minFac depth packet
- gauge gap
- same-base uniqueness
- theta bound
- fixed-exponent uniqueness
- exponent cutoff
- higher-event count bound
- higher-mass bound
- Chebyshev audit
- gnomon-row prime-power exclusion
- diagnostics
- final A/B/C/P judgment

Preserve false conjectures and smallest counterexamples.

## Final report

Answer explicitly:

1. What exact shell von Mangoldt mass was defined?
2. Is it exactly psi(n^2+2*n)-psi(n^2)?
3. Is von Mangoldt pointwise split into prime birth plus nonprime prime-power correction?
4. Is shell mass exactly birth mass plus higher-prime-power mass?
5. Is every perfect square excluded from a strict square shell?
6. Are all even prime-power exponents excluded?
7. Does every nonprime shell prime power have odd exponent at least 3?
8. What canonical minFac and exponent packet was proved?
9. Is the relative log gauge of every higher event at most one third?
10. Can the same base prime produce two shell events in one shell?
11. Is higher-prime-power mass bounded by Chebyshev.theta n?
12. For fixed exponent a>=3, can one shell contain more than one a-th power?
13. What exact event-count bound follows?
14. What explicit higher-mass bound follows from event count?
15. Is the higher correction exactly the shell increment of psi-theta?
16. Do Mathlib Chebyshev bounds improve the shell-local correction estimate?
17. What sufficient prime-existence criterion follows from the correction bound?
18. Is n*(n+2) proved not to be a prime power for n>=3?
19. What do diagnostics show about higher-event multiplicity and exponents?
20. Does the 1/a gauge gap materially narrow the Legendre frontier?
21. What single theorem should be attempted next?

End with exactly one judgment:

Outcome A - SQUARE-SHELL GAUGE GAP YIELDS A NEW SMALL HIGHER-POWER BUDGET
Outcome B - VON MANGOLDT SPLIT IS EXACT AND HIGHER EVENTS ARE SPARSE
Outcome C - PRIME-POWER GAUGE GAP DOES NOT IMPROVE THE LEGENDRE FRONTIER
Outcome P - ONE FIXED-EXPONENT POWER-GAP BRIDGE REMAINS
