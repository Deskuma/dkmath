# Instruction 027 - Odd-depth reciprocal budget and logarithmic correction compression

## Mission

Continue from Instruction 026.

Instruction 026 established:

- exact shell von Mangoldt mass
- exact split:
    shell mass = prime birth mass + higher prime-power correction
- every nonprime shell prime power has odd exponent at least 3
- fixed exponent a>=3 contributes at most one power to one strict square shell
- canonical depth is injective on higher events
- higher-event count is logarithmic in the shell height
- higher correction is bounded by theta(n), by a cube-cutoff prime sum, and by:
    (Nat.log 2 ((n+1)^2)+1) * log n
- universal shell-mass lower bound remains unresolved

The next task is to use the exact 1/a prime-power gauge rather than charging every occupied depth the uniform cost log n.

For a higher event:

  q = p^a

the existing packet gives:

  Lambda(q) = log p
  log q = a * log p

therefore:

  Lambda(q) = log q / a.

Because q<=n^2+2*n in the strict shell:

  Lambda(q) <= log(n^2+2*n) / a.

Instruction 026 also proved that canonical depths are injective, all occupied depths are odd, and each is at least 3.

Therefore the primary exact target is:

  higherCorrection(n)
  <=
  log(n^2+2*n)
  *
  sum over odd a in Icc 3 L(n) of 1/a

where:

  L(n) = Nat.log 2 ((n+1)^2).

Then use Mathlib harmonic bounds to prove a clean explicit compression:

  sum over odd a in Icc 3 L of 1/a
  <= log L

for the relevant nontrivial range.

This yields an explicit correction budget of the form:

  log(n^2+2*n) * log(L(n)).

This is the intended finite realization of the heuristic:

  O(log n * log log n)

but do not state an asymptotic theorem unless it is separately proved.

The universal lower bound for the shell von Mangoldt mass remains a separate problem.

## Branch and workspace

Repository: Deskuma/dkmath

Branch: research/GapFocusing-ExponentGauge-Ultra-261004-v0

Workspace:

lean/dk_math/docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/

Read report-026.md before editing.

## Phase 0 - source audit

Audit at minimum:

DkMath.NumberTheory.Legendre.SquareShellPrimePower
DkMath.NumberTheory.Legendre.SquareShellVonMangoldt
DkMath.NumberTheory.Legendre.SquareShellPrimePowerGauge
DkMath.NumberTheory.Legendre.GnomonPascalCell

Reuse these declarations:

- shellHigherPrimePowerEvents
- mem_shellHigherPrimePowerEvents
- shell_higher_primePower_canonical
- shellHigherPrimePower_depth_injective
- shellHigherPrimePowerEvents_card_le
- squareCell_prime_power_exponent_le_log
- gnomonPascalShellHigherPrimePowerMass_eq_events
- shellHigherPrimePower_log_packet
- shellHigherPrimePower_weight_gap
- gnomonPascalShellHigherPrimePowerMass_le_logBudget
- exists_prime_squareCell_of_higher_bound

Audit Mathlib:

Mathlib.NumberTheory.Harmonic.Bounds
Mathlib.NumberTheory.Harmonic.Defs
Mathlib.Analysis.SpecialFunctions.Log.Basic

Expected useful declarations:

- harmonic_eq_sum_Icc
- harmonic_le_one_add_log
- log_add_one_le_harmonic
- Real.log_le_log
- Real.log_mul
- Real.log_pow

Confirm exact namespaces and coercions in the installed version.

Do not import RH or L-series modules for this checkpoint.

Record source-inventory-027.md before substantial production edits.

## Phase 1 - canonical depth carrier

Define the occupied higher-prime-power depth carrier:

  shellHigherPrimePowerDepths n
  =
  image
    (fun q => q.factorization q.minFac)
    (shellHigherPrimePowerEvents n).

Prove exact membership:

  a in shellHigherPrimePowerDepths n

iff

  there exists q in shellHigherPrimePowerEvents n
  with a = q.factorization q.minFac.

Prove:

- every occupied depth is at least 3
- every occupied depth is odd
- every occupied depth is at most L(n)
- depth image cardinality equals event cardinality

The final equality should use the existing depth injectivity.

## Phase 2 - full odd-depth carrier

Define:

  shellOddDepths n
  =
  filter Odd (Finset.Icc 3 (Nat.log 2 ((n+1)^2))).

Prove:

  shellHigherPrimePowerDepths n subset shellOddDepths n.

Do not encode primality in this carrier.

It is only the admissible exponent universe.

## Phase 3 - exact weight equals log q divided by depth

For a higher event q define:

  a = q.factorization q.minFac.

Using shellHigherPrimePower_log_packet and a>0, prove:

  ArithmeticFunction.vonMangoldt q
  =
  Real.log (q : Real) / (a : Real).

This should be a thin theorem.

Suggested name:

  shellHigherPrimePower_weight_eq_log_div_depth

Do not use approximate inequalities here.

## Phase 4 - pointwise top-log reciprocal bound

Let:

  top(n) = n^2+2*n.

For n>=3 and q in shellHigherPrimePowerEvents n prove:

  ArithmeticFunction.vonMangoldt q
  <=
  Real.log (top(n) : Real)
  /
  (q.factorization q.minFac : Real).

Required facts:

- q<=top(n)
- q>0
- top(n)>0
- depth>=3
- Real.log monotonicity

Keep all positivity assumptions explicit.

Do not replace top by (n+1)^2 in the primary theorem.

## Phase 5 - event sum to occupied-depth sum

Start from:

  higherCorrection
  =
  sum q in events of Lambda(q).

Apply the pointwise bound.

Then use injectivity of the canonical depth map to prove:

  higherCorrection
  <=
  sum a in shellHigherPrimePowerDepths n of
    Real.log(top(n)) / (a : Real).

The event-to-depth reindex must be kernel-proved.

Do not introduce a choice of inverse event for each depth.

Prefer Finset.sum_image using the existing injectivity.

## Phase 6 - occupied depths to all odd depths

Using:

  shellHigherPrimePowerDepths n subset shellOddDepths n

and nonnegativity of:

  log(top)/a

prove:

  higherCorrection
  <=
  sum a in shellOddDepths n of
    Real.log(top(n)) / (a : Real).

Then factor the constant:

  =
  Real.log(top(n))
  *
  sum a in shellOddDepths n of 1/(a : Real).

This is the primary finite reciprocal-budget theorem.

## Phase 7 - named reciprocal budget

Define:

  shellOddDepthReciprocalSum n

as:

  sum a in shellOddDepths n of 1/(a : Real).

Define:

  shellHigherPrimePowerReciprocalBudget n

as:

  Real.log(n^2+2*n)
  *
  shellOddDepthReciprocalSum n.

Prove for n>=3:

  higherCorrection <= reciprocalBudget.

This theorem must be independent of any harmonic approximation.

## Phase 8 - generic odd reciprocal sum bound

Prove a neutral finite theorem for L>=3:

  sum over odd a in Icc 3 L of 1/(a:Real)
  <=
  sum a in Icc 2 L of 1/(a:Real).

This is only subset monotonicity with nonnegative summands.

Then connect the full reciprocal interval to harmonic numbers.

Target:

  sum a in Icc 2 L of 1/(a:Real)
  =
  (harmonic L : Real) - 1.

Audit coercions carefully because Mathlib harmonic is rational-valued before coercion.

Do not reimplement harmonic numbers.

## Phase 9 - harmonic compression

Use:

  harmonic_le_one_add_log L

to prove for L>=3:

  sum over odd a in Icc 3 L of 1/(a:Real)
  <=
  Real.log (L : Real).

This is a required theorem.

Suggested neutral name:

  odd_reciprocal_sum_le_log

or a repository-consistent equivalent.

Do not claim the sharper asymptotic one-half coefficient unless separately proved.

## Phase 10 - explicit log-log-style budget

Define:

  shellHigherPrimePowerLogLogBudget n
  =
  Real.log(n^2+2*n)
  *
  Real.log(Nat.log 2 ((n+1)^2) : Real).

For n>=3 prove that the binary logarithmic cutoff is at least 3.

Then prove:

  shellHigherPrimePowerReciprocalBudget n
  <=
  shellHigherPrimePowerLogLogBudget n.

Hence:

  higherCorrection
  <=
  shellHigherPrimePowerLogLogBudget n.

This is the main acceptance theorem.

The name log-log refers to the nested logarithmic scale only.

Do not claim a formal Big-O theorem from this name.

## Phase 11 - optional shell-top simplification

If clean, derive:

  Real.log(n^2+2*n)
  <
  2 * Real.log(n+1)

for n>=1.

Then obtain a more geometric budget:

  higherCorrection
  <=
  2 * log(n+1) * log(L(n)).

This theorem is optional.

Do not let real-log boundary friction block the primary reciprocal result.

## Phase 12 - compare against previous logarithmic-count budget

The Instruction 026 budget was:

  (L(n)+1) * log n.

The new budget is:

  log(top(n)) * log(L(n)).

Investigate whether the new budget is provably no larger than the old budget for all n>=3.

If a clean universal comparison closes, prove it.

If not, provide:

- finite diagnostics
- the smallest counterexample if one exists
- no false monotonic claim

The main mathematical gain is the 1/a weighting, even if tiny anchors cross.

## Phase 13 - optional sharper odd-only harmonic identity

Only if cheap, derive an exact identity or sharper bound for odd reciprocal depths.

Possible identity:

  sum over odd a in Icc 3 L of 1/a
  =
  harmonic L
  -
  1
  -
  one-half times harmonic (L/2)

with correct floor semantics.

This is optional.

Do not delay the main checkpoint for parity reindexing.

If implemented, derive a correspondingly sharper budget and compare it numerically.

## Phase 14 - conditional prime provider

Reuse:

  exists_prime_squareCell_of_higher_bound.

Prove:

If n>=3 and:

  shellHigherPrimePowerReciprocalBudget n
  <
  gnomonPascalShellVonMangoldtMass n

then the shell contains a prime.

Also prove the log-log-budget specialization.

These are conditional providers.

Do not claim the strict shell-mass comparison universally.

## Phase 15 - exact psi form

Use:

  gnomonPascalShellVonMangoldtMass_eq_psi_sub

to expose the provider equivalently as:

  reciprocalBudget
  <
  psi(n^2+2*n)-psi(n^2)

implies shell prime existence.

Likewise for the log-log budget.

This should be a thin theorem.

## Phase 16 - diagnostics

Extend the exact diagnostics to at least n=1 through 5000.

For each n record:

- L(n)
- occupied higher depths
- odd admissible depths
- higher correction
- old log-count budget
- reciprocal budget
- log-log budget
- theta budget
- cube-candidate budget
- ratios correction/budget where defined
- whether each conditional strict comparison passes numerically

Mandatory anchors:

  3
  5
  7
  9
  11
  19
  29
  297
  1031.

Report:

- worst correction/reciprocal-budget ratio
- worst correction/log-log-budget ratio
- smallest n where each new budget beats the old log-count budget
- all small exceptions
- whether a shell with two higher events substantially improves under 1/a weighting

Floating log diagnostics are not theorem premises.

## Phase 17 - kernel calibrations

Kernel-check representative higher-event depth patterns.

At minimum:

- n=2 with 2^3
- n=5 with depths 3 and 5
- n=11 with depths 3 and 7
- one shell with a single high odd depth
- n=297
- n=1031

For each relevant event certify:

- canonical depth
- odd-depth membership
- exact weight equals log q divided by depth, as a symbolic theorem instantiation
- carrier membership

Do not kernel-evaluate unnecessary giant real logarithmic inequalities.

The finite structural carrier is the certified content.

## Phase 18 - memory and build telemetry

The user environment has 32 GiB main memory and 64 GiB swap.

Final validation should keep:

  LEAN_NUM_THREADS=2

unless there is a concrete reason to change it.

For focused, facade, root, and axiom-audit builds, record process telemetry with a tool such as:

  /usr/bin/time -v

when available.

Record at least:

- elapsed time
- maximum resident set size
- major page faults
- minor page faults
- swap count if the platform reports it

If a process is killed, explicitly determine whether it was:

- OOM
- timeout
- manual termination
- another failure

Do not infer OOM merely from using two Lean threads.

Put the summary in validation-027.md.

## Phase 19 - next frontier audit

Once the correction is compressed, do not immediately add another correction refinement.

The report must reassess the remaining inequality:

  shellHigherPrimePowerLogLogBudget n
  <
  shellVonMangoldtMass n.

The right side is:

  psi(n^2+2*n)-psi(n^2).

Audit which already-formalized DkMath and Mathlib structures could possibly give a lower bound for this short interval.

At minimum revisit:

- GnomonPascalCell factorial identity
- WallisCellGrowth
- central or general binomial growth
- ArithmeticFunction identity summing von Mangoldt over divisors
- Chebyshev lower bounds
- Bertrand proof infrastructure

Do not implement a large new lower-bound proof inside 027.

Identify the smallest exact bridge that could convert a multiplicative Pascal-cell growth lower bound into a shell von Mangoldt lower bound while explicitly subtracting lower-divisor contributions.

This should become the proposed Instruction 028 target.

## Phase 20 - route judgment

The report must distinguish:

A. Correction compression succeeds and materially sharpens the unresolved frontier.

B. Reciprocal weighting is exact but harmonic compression gives no meaningful gain over the 026 budget.

C. The occupied-depth reindex exposes a stronger unexpected identity.

D. One precise reciprocal or harmonic coercion bridge remains.

The universal lower shell-mass theorem is not required for Outcome A.

## Possible outcomes

Outcome A - ODD-DEPTH RECIPROCAL GAUGE COMPRESSES THE HIGHER CORRECTION

The exact 1/a reindex and harmonic bound close, yielding a substantially smaller explicit higher-prime-power budget and new conditional prime providers.

Outcome B - RECIPROCAL REINDEX IS EXACT BUT DOES NOT IMPROVE THE FINITE FRONTIER

The finite identities close but the resulting bound gives no meaningful improvement over Instruction 026.

Outcome C - DEPTH REINDEX REVEALS A STRONGER STRUCTURE

A stronger exact relation than the planned reciprocal upper bound emerges and materially changes the next target.

Outcome P - ONE HARMONIC COMPRESSION BRIDGE REMAINS

The event-to-depth reciprocal budget closes, but one exact harmonic or coercion theorem blocks the log-log-style bound.

## Non-goals

Do not claim:

- Legendre conjecture
- a universal positive lower bound on the shell von Mangoldt mass
- PNT or RH
- an asymptotic O(log n log log n) theorem unless explicitly formalized
- that the new budget is universally smaller than every old budget without proof
- that odd reciprocal sums have a one-half log coefficient unless proved
- that finite floating diagnostics certify real-log inequalities
- that two Lean threads indicate an OOM condition

Do not return to deletion packing, terminal cofactor, or FLT7 in this checkpoint.

## Suggested implementation surface

Prefer extending:

DkMath/NumberTheory/Legendre/SquareShellPrimePowerGauge.lean

If the harmonic lemma is neutral and reusable, a small neutral module is acceptable.

Avoid unnecessary new modules.

Keep finite diagnostics and calibration under DkMathTest.

Update the Legendre facade only after focused builds are green.

## Validation

For all new public production declarations:

- focused build
- lake build DkMath.NumberTheory.Legendre
- lake build DkMath
- forbidden-token audit
- print axioms
- git diff --check

No new sorryAx dependencies.

Existing unrelated warnings may remain.

## Durable checkpoint protocol

Update findings after:

- source audit
- occupied depth carrier
- odd-depth carrier
- exact log/depth weight
- pointwise top-log bound
- event-to-depth reindex
- reciprocal budget
- harmonic compression
- log-log budget
- conditional providers
- diagnostics
- build memory telemetry
- next-frontier audit
- final A/B/C/P judgment

Preserve failed comparisons and smallest counterexamples.

## Final report

Answer explicitly:

1. What is the exact occupied-depth carrier?
2. Is it exactly the depth image of higher shell events?
3. Is it contained in the odd Icc 3 L carrier?
4. Is higher-event weight exactly log(q)/depth?
5. What pointwise top-log/depth bound was proved?
6. Was the event sum reindexed injectively by canonical depth?
7. What exact reciprocal budget was proved?
8. Was odd reciprocal sum bounded by log L using Mathlib harmonic bounds?
9. What explicit log-log-style higher correction budget follows?
10. Is the new budget provably below the Instruction 026 log-count budget for all n>=3?
11. Was a sharper odd-only harmonic identity implemented?
12. What conditional Legendre provider follows?
13. What is its exact psi-difference form?
14. What do diagnostics show at n=5 and n=11 where two higher events coexist?
15. What are the worst observed correction/budget ratios through the scan?
16. What build peak RSS and paging behavior were recorded?
17. Was there any actual OOM evidence?
18. After this compression, what exact shell-mass lower-bound statement remains?
19. Which existing Pascal or von Mangoldt theorem is the best candidate to attack that lower bound?
20. What single theorem should Instruction 028 attempt?

End with exactly one judgment:

Outcome A - ODD-DEPTH RECIPROCAL GAUGE COMPRESSES THE HIGHER CORRECTION
Outcome B - RECIPROCAL REINDEX IS EXACT BUT DOES NOT IMPROVE THE FINITE FRONTIER
Outcome C - DEPTH REINDEX REVEALS A STRONGER STRUCTURE
Outcome P - ONE HARMONIC COMPRESSION BRIDGE REMAINS
