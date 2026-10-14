# Instruction 025: Pascal prebirth boundary, prime-power synchronization, and shrinking gnomon gauge

## Mission

Reframe the Legendre program around an exact Pascal boundary before spending another checkpoint on local deletion packing.

The central observation to formalize is:

- one row before a common prime-support row, Pascal coefficients can form an exact alternating plus-one minus-one phase modulo the common prime;
- Pascal addition turns adjacent opposite residues into zero;
- the next row therefore has that prime in every inner coefficient;
- Mathlib already classifies when this can happen: exactly at prime-power rows;
- for modulus equal to the row number itself, the boundary should classify prime rows.

This checkpoint must distinguish three notions:

- genuine prime-coordinate birth at row p;
- prime-power resynchronization at row p^a for a greater than one;
- generic common-factor structure of a Pascal row.

Do not call every p^a event a new prime birth. The prime p is globally new only at row p. Higher powers are common-support resynchronizations.

The second purpose is to connect this exact Pascal boundary to the Legendre shrinking-gauge view and decide whether it gives a genuinely new provider or only a clean structural coordinate.

## Branch and workspace

Repository: Deskuma/dkmath

Branch: research/GapFocusing-ExponentGauge-Ultra-261004-v0

Workspace:

lean/dk_math/docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/

Read report-024.md and the current Legendre facade before editing.

## Mandatory source audit

Audit and reuse these DkMath modules before adding declarations:

- DkMath.NumberTheory.BinomialPrime
- DkMath.NumberTheory.BinomialPrimePower
- DkMath.NumberTheory.PascalPrimeDial
- DkMath.NumberTheory.PascalPrimeCoordinateDecoder
- DkMath.Pascal.WallisGrowthBridge
- DkMath.Pascal.WallisCellGrowth
- DkMath.NumberTheory.ZsigmondyCyclotomic
- DkMath.NumberTheory.Legendre.Basic
- DkMath.NumberTheory.Legendre.Frontier
- current Legendre modules from instructions 016 through 024

Audit these existing declarations in particular:

- AllInnerChooseDivisible
- InnerRowSupportPrime
- RowBirthPrime
- PrimePowerRowSupport
- PrimePrebirthAlternation
- prime_prebirthAlternation_step
- prime_prebirthAlternation
- prime_power_allInnerChooseDivisible
- prime_power_rowBirthPrime
- padicValNat_choose_prime_pow
- padicValNat_choose_prime_pow_add_index
- pascalPrimeDialHeight_prime_pow_add_index
- pascalPrimeDialHeight_prime_pow
- prime_power_unitFilteredPrimeDialHeight
- prime_not_dvd_pascalCoeffMass_of_row_lt
- pascalPrimeCoordinateBirthSupport
- pascalPrimeBirthLogMass
- pascalPrimeBirthLogMass_eq
- pascalPrimeCoordinateSupportUpTo_succ

Audit Mathlib before reproving any Lucas or common-gcd theorem:

- Mathlib.Data.Nat.Choose.Lucas
- Mathlib.Data.Nat.Choose.Factorization

The following Mathlib declarations are expected to be central. Confirm exact namespaces and signatures in the installed version:

- Choose.lucas_theorem_nat
- Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat
- Choose.gcd_choose_eq_minFac_of_isPrimePow
- Choose.gcd_choose_eq_one_of_not_isPrimePow
- Nat.factorization_choose
- Nat.factorization_choose_le_log
- Nat.factorization_choose_le_one
- Nat.factorization_choose_eq_zero_of_lt

DkMath.NumberTheory.ZsigmondyCyclotomic already imports the Lucas file, but current Pascal modules do not expose the prime-power boundary classification through it. Reuse Mathlib directly at the proper low dependency level. Do not route a foundational Pascal theorem through ZsigmondyCyclotomic merely to inherit an import.

Also audit DkMath.NumberTheory.StructuralArithmetic.PowerGauge.

Important semantic firewall:

- existing PowerGauge means exponent reduction modulo a period;
- it is not a logarithmic relative scale and not a Pascal common-divisor gauge;
- do not identify or rename it as the gauge introduced here.

If a new gauge is needed, use a distinct name.

## Preflight report-024 calibration check

Before using 024 diagnostics, verify two apparent report transcription mismatches against kernel definitions.

Expected arithmetic:

- 297 squared plus 350 equals 88559 equals 19 times 59 times 79
- 1031 squared plus 90 equals 1063051 equals 11 times 241 times 401

The report table currently appears to show 41 instead of 19 in the first support and 37 instead of 11 in the second support.

Determine whether this is documentation-only or whether any test calibration contains the wrong carrier. Correct documentation or tests only if the mismatch is real. Do not alter a proved theorem merely to match the report.

Record the result in findings-025.md.

## Part A. Generic prebirth alternation carrier

Introduce a generic row and modulus version of the existing prime-specific prebirth predicate.

Preferred semantic shape:

PascalPrebirthAlternationMod d m

means that for every k at most d, the coefficient choose d k viewed modulo m equals the alternating unit residue, one for even k and minus one for odd k.

ZMod is acceptable and matches PrimePrebirthAlternation. Nat.ModEq is also acceptable if it gives a cleaner reusable theorem. Prefer one canonical representation and thin adapters rather than two parallel theories.

Prove that the existing PrimePrebirthAlternation p is exactly the specialization at row p minus one and modulus p, or provide an equivalence theorem if definitional equality is not practical.

Do not duplicate the existing prime_prebirthAlternation proof once the generic theorem is available.

## Part B. Pascal cancellation defect

Define the local additive cancellation observable for adjacent cells of row d.

A suitable mathematical value is the residue modulo m of

choose d k plus choose d (k plus 1).

For in-range k, prove by Pascal recurrence that this is exactly the residue of

choose (d plus 1) (k plus 1).

Expose both the equality and the zero criterion.

The intended meaning is:

- nonzero defect means the adjacent pair does not cancel modulo m;
- zero defect means the next-row coefficient carries modulus m.

For prime p and an actual nonzero coefficient, connect zero defect to positive Pascal prime-dial height at the next-row cell.

Do not claim a real-valued distance or monotonic decay here.

## Part C. Exact alternation versus next-row common support

This is the first major acceptance target.

Prove an exact theorem, under only the minimal modulus hypotheses needed, of the form:

PascalPrebirthAlternationMod d m
if and only if
AllInnerChooseDivisible (d plus 1) m.

The forward direction is adjacent cancellation.

The reverse direction should start from choose d 0 equals 1 and use Pascal recurrence inductively: if every adjacent sum vanishes modulo m, consecutive residues are negatives, hence the whole row alternates.

This theorem should be generic in the modulus. Primality is not conceptually required for the Pascal recurrence itself.

Then derive:

- existing prime_prebirthAlternation from prime_allInnerChooseDivisible_self;
- prime-power prebirth alternation at row p^a minus one from prime_power_allInnerChooseDivisible;
- a paired theorem showing the prebirth row and next-row common-support row in one packet.

Handle p equals 2 explicitly rather than silently assuming oddness. The alternating residues collapse to the same residue modulo 2, but the theorem should remain correct.

## Part D. Prime-power synchronization classifier

This is the second major acceptance target.

Use Mathlib Lucas results rather than proving a new prime-power classification from scratch.

For prime p and row N greater than one, prove the clean equivalence:

AllInnerChooseDivisible N p
if and only if
there exists positive a with N equals p^a.

Equivalent formulations through multiplicity are acceptable internally, but caller-facing API should expose the positive prime-power witness if practical.

The reverse direction should reuse prime_power_allInnerChooseDivisible.

The forward direction should reuse Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat or an even shorter existing theorem.

Then combine Part C and Part D:

For prime p and d plus one greater than one,

PascalPrebirthAlternationMod d p
if and only if
d plus one is a positive power of p.

This is the exact theorem that turns the plus-one minus-one boundary into a predictor of the next prime-power row.

Use the phrase prime-power synchronization, not new prime birth, for exponent greater than one.

## Part E. Close the old prime-row converse

The existing BinomialPrime roadmap left the reverse implication open.

Use the new generic boundary and Mathlib common-gcd or Lucas classification to close, if clean:

For d greater than one,

d is prime
if and only if
AllInnerChooseDivisible d d.

Then derive the prebirth characterization:

For d greater than one,

d is prime
if and only if
row d minus one alternates plus one minus one modulo d.

This is a major desired theorem.

A clean proof route is:

- all inner coefficients divisible by d means d divides their common gcd;
- Mathlib classifies the gcd as the base prime for prime-power rows and 1 otherwise;
- d greater than one rules out the non-prime-power case;
- if d is p^a and d divides p, force a equals one.

If Mathlib offers a shorter exact route, use it.

Do not introduce FactorRigid or a custom primality predicate for this checkpoint.

## Part F. Common-divisor gauge

Define or expose the common inner-row gcd:

pascalInnerCommonDivisor N

as the gcd of choose N k over inner k.

Prefer a thin wrapper around the exact Finset used by Mathlib if a DkMath-facing name materially improves readability. Do not duplicate gcd machinery.

Prove the classification by reusing Mathlib:

- if N is a prime power, the common divisor equals minFac N;
- if N greater than one is not a prime power, the common divisor equals 1;
- if N is prime, the common divisor equals N;
- conversely, for N greater than one, common divisor equals N implies N prime.

Interpret this as the maximal common cancellation modulus visible one row earlier through Part C.

This scalar is the preferred exact finite gauge for this checkpoint.

Do not call it StructuralArithmetic.PowerGauge.

Possible names include PascalCommonModulusGauge or PascalPrebirthCommonDivisor.

## Part G. Logarithmic relative gauge audit

The user-level heuristic is that a relative unit scale shrinks.

For a prime-power row N equals p^a, the exact common modulus is p. Therefore informally:

log p divided by log N equals 1 divided by a.

Audit whether a lightweight exact real theorem is worthwhile using existing Real.log facts.

Only implement it if the dependency cost stays local and the boundary cases are clean.

The exact arithmetic theorem N equals p^a and common modulus equals p is more important than the Real.log corollary.

If implemented, use a distinct name such as pascalPrimePowerLogGauge.

Do not identify this with StructuralArithmetic.PowerGauge.

## Part H. Test the claimed monotone shrinking behavior skeptically

The endpoint theorem is exact. A monotone approach to that endpoint is not yet established.

Create finite diagnostics for simple candidate defect observables before formalizing any monotonicity theorem.

At minimum test:

- number of nonzero adjacent cancellation defects modulo p;
- number of cells mismatching the alternating plus-one minus-one phase;
- a simple centered residue magnitude sum if cheap;
- normalized versions only if they have a clear exact definition.

Test prime targets and prime-power targets over a useful bounded range.

If a proposed defect is not monotone as rows approach p or p^a, record the smallest counterexample and do not formalize the false claim.

A likely phenomenon is abrupt synchronization rather than smooth monotone decay. Let the data and Lean decide.

The report must clearly separate:

- exact zero-defect boundary;
- any empirical trend;
- any proved monotonic statement.

No heuristic monotonicity may be promoted to a theorem without proof.

## Part I. Prime birth versus prime-power resynchronization

Bridge to PascalPrimeCoordinateDecoder.

For a prime p:

- the coordinate p is absent from every earlier row;
- it is genuinely born at row p;
- pascalPrimeBirthLogMass p equals log p.

For row p^a with a greater than one:

- p is not a globally new coordinate;
- the event is a whole-inner-row resynchronization of an already existing prime direction.

Add thin terminology or theorem packets only if useful. Do not change the semantics of pascalPrimeCoordinateBirthSupport.

If a new finite event carrier is introduced for resynchronization, prove that prime birth is exactly the exponent-one subcase.

## Part J. Gnomon Pascal cell bridge

After the prebirth boundary is stable, connect it to the Legendre shrinking-gauge program.

Define or reuse the Pascal cell

GnomonPascalCell n equals choose (n squared plus 2 times n) (2 times n).

Record the exact factorial interpretation:

the numerator interval is the open square shell from n squared plus 1 through n squared plus 2 times n, divided by the local factorial denominator.

For the clean range n at least 3, investigate and prove the fresh-prime equivalence:

there exists prime p with n squared less than p and p less than (n plus 1) squared
if and only if
there exists prime p dividing GnomonPascalCell n with n squared less than p.

Use exact inequalities. Do not use asymptotics for this equivalence.

Also record the shrinking Pascal-cell ratio:

2 times n divided by n squared plus 2 times n

which reduces to the conceptual gauge 2 divided by n plus 2 over rationals or reals.

Do not claim that this shrinking ratio alone proves fresh-prime existence.

## Part K. Shell birth log mass

Using pascalPrimeBirthLogMass, define a finite open-shell birth mass if it does not already exist:

sum over r from 1 through 2 times n of pascalPrimeBirthLogMass (n squared plus r).

Prove the exact positivity criterion:

shell birth log mass is positive
if and only if
the open square shell contains a prime.

This should be a thin finite-sum bridge using:

- pascalPrimeBirthLogMass_eq;
- positivity of Real.log at primes;
- the exact square-offset carrier.

This theorem is an exact restatement of Legendre, not a proof of Legendre. Mark it accordingly.

The purpose is to create a common target for the Pascal growth side and the Legendre shell side.

## Part L. Growth-to-birth gap

Audit, but do not overclaim, the missing bridge:

Pascal coefficient growth
minus old prime-power valuation budget
leaves positive fresh prime-birth mass.

Reuse:

- WallisGrowthBridge for central growth;
- WallisCellGrowth for arbitrary Pascal cells;
- Nat.factorization_choose and carry-count formulas;
- Pascal prime-power canonical support if useful;
- pascalPrimeBirthLogMass for prime-only birth.

Classify what is already exact and what remains genuinely new.

The report must answer whether the gnomon Pascal cell admits a useful exact prime-power carry ledger whose fresh part is the shell birth mass, or whether additional cancellation terms prevent that direct identification.

Do not start a large analytic proof in this checkpoint.

## Part M. Report-024 gcd cofactor proposal

Do not make the terminal cofactor theorem the main task of instruction 025.

After Parts A through L, reassess it.

If the new Pascal boundary gives no stronger Legendre provider, the cofactor theorem may be implemented later as a local arithmetic refinement.

If it is extremely short and uses already imported APIs, an optional proof is acceptable, but it must be reported as a side result and compared against the new Pascal route.

No additional deletion-packing campaign should start inside this checkpoint.

## Required diagnostics

Include small exact examples for:

- p equals 2, 3, 5, 7;
- prime-power rows 4, 8, 9, 25, 27;
- non-prime-power rows 6, 10, 12, 15;
- prime row prebirth examples 4 to 5 and 6 to 7;
- prime-power prebirth examples 7 to 8, 8 to 9, 24 to 25, 26 to 27.

For each relevant row record:

- row number;
- common inner gcd;
- whether it is prime;
- whether it is a prime power;
- base prime if prime power;
- whether the previous row has exact alternating residues modulo that base prime;
- whether all next-row inner coefficients carry that prime;
- selected prime-dial heights.

Also include Legendre anchors already used by this project where computationally cheap:

- n equals 5, 11, 19, 29, 297, 1031.

For these anchors report only compact data needed for the new Pascal-cell and shell-log interfaces. Do not print huge binomial coefficients if factor support or valuation summaries suffice.

## Production placement

Prefer a neutral NumberTheory Pascal module for the generic boundary, for example:

DkMath/NumberTheory/PascalPrebirthBoundary.lean

or extend BinomialPrimePower only if the file remains coherent.

Legendre-specific wrappers belong under:

DkMath/NumberTheory/Legendre/

Do not make neutral Pascal theorems depend on Legendre.

Update facades only after focused builds pass.

## Validation

Run:

- focused build for every changed production module;
- lake build DkMath.NumberTheory.Legendre;
- lake build DkMath;
- forbidden-token audit;
- print axioms for all new public declarations;
- git diff check.

No new sorryAx dependencies.

## Required report questions

report-025.md must answer all of the following.

1. Was generic prebirth alternation defined without duplicating the prime-specific theory?
2. Is prebirth alternation exactly equivalent to next-row common divisibility?
3. Does the equivalence include modulus 2 cleanly?
4. Was prime-power prebirth alternation proved for every positive exponent?
5. Does exact prebirth alternation modulo prime p classify the next row as a p-power?
6. Was the old prime_iff_allInnerChooseDivisible_self converse finally closed?
7. Is prime N exactly characterized by plus-one minus-one alternation in row N minus one modulo N?
8. Is the common inner-row gcd exactly the maximal prebirth cancellation modulus?
9. Does Mathlib's gcd classification remove the need for a custom prime-power detector?
10. Which candidate defect observables are monotone, and which fail? Give the smallest counterexamples for failures.
11. Is prime birth clearly separated from prime-power resynchronization?
12. Does the gnomon Pascal cell fresh-prime factor criterion close exactly?
13. Is shell prime existence exactly equivalent to positive shell Pascal birth log mass?
14. What exact bridge is still missing from Pascal growth to positive shell birth mass?
15. Does the report-024 cofactor proposal become more or less relevant after this checkpoint?
16. Were the two apparent report-024 support transcription mismatches confirmed and corrected if necessary?

## Final judgment

Use exactly one of:

Outcome A - PASCAL PREBIRTH GAUGE YIELDS A NEW LEGENDRE OBSTRUCTION

Outcome B - PRIME-POWER PREBIRTH BOUNDARY IS EXACT BUT LEGENDRE GROWTH BRIDGE REMAINS

Outcome C - SIMPLE SHRINKING-GAUGE HEURISTIC FAILS BEYOND THE EXACT BOUNDARY

Outcome P - ONE PRECISE PASCAL TO SHELL GROWTH BRIDGE REMAINS

The preferred success is not module count. It is whether the exact plus-one minus-one prebirth boundary, prime-power synchronization theorem, and gnomon Pascal cell can be placed in one mathematically honest chain without turning a structural restatement into a Legendre proof.
