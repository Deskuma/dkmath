# FLT7TC-005R36 — Ideal-norm exponent transport for the exact 1-to-2 allocation

Branch: research/FLT7-Unconditional-TraceOne-Closure-260917-v0

Authoritative inputs:

- report-040.md
- report-041.md
- PrimeTraceOneDirectRealCubicPrimeAllocation.lean
- PrimeTraceOneDirectRealCubicCanonicalCommonFactor.lean
- PrimeTraceOneDirectRealCubicSquareIdealSupport.lean
- PrimeTraceOneDirectRealCubicSquareGaloisSupport.lean
- PrimeTraceOneDirectRealCubicCubeDefect.lean
- historical proof-pattern reference only: SevenRamifiedFusionPrimeLoadGlobalFactorization.lean

R34 kernel-checks exact common-prime cardinal allocation: gap side has exactly one prime ideal above q; quotient side has exactly two.
R35 kernel-checks exact ideal multiplicities. Writing m := a.factorization q, every prime P above a common q has exactly one alternative:

- gap allocation: multiplicity P gapIdeal = m and multiplicity P quotientIdeal = 0;
- quotient allocation: multiplicity P gapIdeal = 0 and multiplicity P quotientIdeal = m.

The remaining frontier is global transport from ideal multiplicities to Nat.factorization coefficients of the two absolute norms.

## Goal

For every common norm prime q prove:

    R.factorization q = a.factorization q
    S.factorization q = 2 * a.factorization q

where

    R := Int.natAbs (norm t.gapSquareRoot)
    S := Int.natAbs (norm t.quotientSquareRoot)
    a := t.powerSplit.gapSplit.a.

Stop after this transport and immediate consistency audit. Do not construct the global canonical C,U,V packet in R36.

## Part A — exact norm of a prime above common q

For every prime ideal P above q, prove

    Ideal.absNorm P = q.

Use the checked inertia degree one from R30 and Ideal.natAbs_pow_inertiaDeg or the equivalent residue-field cardinal theorem.
Do not infer this merely from primesOver.ncard = 3.

## Part B — q-primary residual strategy

Mathlib's current absNorm API is multiplicative, but no one-line theorem was found that directly rewrites

    (absNorm I).factorization q

as the sum of prime-ideal multiplicities above q.

Therefore prefer the following exact residual strategy.

For a side ideal I, collect every prime ideal above q occurring on that side at its exact R35 multiplicity. Form

    Qpart := product P^(multiplicity P I).

Prove Qpart divides I and choose J with

    I = Qpart * J.

Then prove

    not (q divides Ideal.absNorm J).

The required contradiction route is:

1. Assume q divides absNorm J.
2. Use Ideal.exists_isMaximal_dvd_of_dvd_absNorm' to obtain a maximal ideal Q above q with Q divides J.
3. Since I = Qpart * J, Q contributes an additional positive multiplicity to I.
4. If Q was already selected, this exceeds its exact R35 multiplicity.
5. If Q was not selected, R35 says its multiplicity on this side is zero.
6. Contradiction.

A specialized gap/quotient implementation is acceptable if a generic helper becomes disproportionately elaborate.

## Part C — gap-side transport

Use the R34 singleton gap-prime theorem. Choose the unique Pgap above q with gapSquareIdeal t <= Pgap.
R35 gives multiplicity Pgap gapSquareIdeal = m.

Construct

    gapSquareIdeal t = Pgap^m * Jgap

with

    not (q divides Ideal.absNorm Jgap).

Part A and multiplicativity give

    Ideal.absNorm (gapSquareIdeal t) = q^m * Ideal.absNorm Jgap.

Convert q-freeness of Jgap into

    (Ideal.absNorm (gapSquareIdeal t)).factorization q = m.

Use Nat.factorization_mul only after proving the required nonzero hypotheses.

Finally rewrite through directOrbitSquareRefinement_absNorm_span_model to expose

    R.factorization q = m.

## Part D — quotient-side transport

Use the R34 quotient-side ncard = 2 theorem. Either choose the two distinct quotient primes explicitly, or use the finite filtered primes-over set.

Each quotient prime has exact multiplicity m by R35 and absNorm q by Part A.

Construct the q-primary factor

    P1^m * P2^m

or its finite-product equivalent, and a residual Jquot with

    quotientSquareIdeal t = (P1^m * P2^m) * Jquot
    not (q divides Ideal.absNorm Jquot).

Then prove

    Ideal.absNorm (quotientSquareIdeal t) = q^(2*m) * Ideal.absNorm Jquot

and hence

    S.factorization q = 2*m.

Do not infer the factor 2 merely from ncard = 2. It must come from two prime ideals each with exact multiplicity m and norm q.

## Part E — optional local q-primary factorization API

If natural, expose audit theorems carrying the exact residual decompositions for both sides. They are useful but not mandatory. The mandatory endpoint is the two Nat.factorization equalities.

## Part F — cube-ledger regression only

Kernel-check consistency with the already existing ledger

    R.factorization q + S.factorization q = 3 * a.factorization q.

The ledger is regression/calibration only. It must not be used as the source of either exact side exponent.

## Part G — cheap gcd consequence

After the exact exponent equalities are green, it is acceptable to expose

    (Nat.gcd R S).factorization q = a.factorization q

for common q, using the actual gcd factorization/min theorem.

Do not construct C,U,V globally in this checkpoint.

## Hard stops

- No R.factorization q = m from one gap prime plus R*S=a^3.
- No S.factorization q = 2*m from cardinality alone.
- No residual q-freeness without a checked argument using exists_isMaximal_dvd_of_dvd_absNorm' or an equivalent theorem.
- No historical routing/address packet as mathematical input; historical files are proof-pattern references only.
- No canonical C,U,V packet.
- No successor/descent or FLT7 contradiction claim.
- No sorry, sorryAx, admit, unsafe, or project axiom.

## Preferred production file

Continue in:

    DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicCanonicalCommonFactor.lean

Update the existing API/axiom tests and scratch file.
Create report-042.md and update ROADMAP.md.

## Report questions

1. Was Ideal.absNorm P = q proved for every prime P above a common q?
2. Was an exact q-primary factor extracted from the gap ideal?
3. Was its residual norm proved q-free?
4. Was R.factorization q = a.factorization q kernel-checked?
5. Was an exact two-prime q-primary factor extracted from the quotient ideal?
6. Was its residual norm proved q-free?
7. Was S.factorization q = 2*a.factorization q kernel-checked?
8. Were the public natural norm equalities obtained through the existing principal-ideal absNorm bridge?
9. Was the cube ledger used only as consistency/regression?
10. Did any immediate contradiction arise once exact rational exponents were known?

## Outcomes

- Outcome A — exact norm exponent transport green and current data immediately closes a contradiction.
- Outcome B — exact common-prime norm exponents green; no contradiction yet.
- Outcome C — gap-side transport green; two-prime quotient residual is the precise frontier.
- Outcome D — q-primary ideal extraction green; proving residual norm q-free is the precise frontier.
- Outcome E — current ideal/norm API cannot connect exact ideal multiplicities to natural norm factorization without a new neutral lemma.

## Validation

At minimum:

    lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicCanonicalCommonFactor
    lake build DkMath.FLT.Seven
    lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicCanonicalCommonFactorApi
    lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicCanonicalCommonFactorAxiom
    lake env lean DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicCanonicalCommonFactorScratch.lean
    git diff --check

Print axioms for:

- prime-above-q absNorm equality;
- gap residual q-freeness;
- quotient residual q-freeness;
- common-prime gap natural factorization equality;
- common-prime quotient natural factorization equality.

Run forbidden-source/import scans on every decisive file.
