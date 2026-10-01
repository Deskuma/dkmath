# FLT7TC-005R56 — Fixed n=6 finite certificate bridge

Branch: research/FLT7-Unconditional-TraceOne-Closure-260917-v0

Authoritative project inputs:

- report-061.md
- ThomasThueSixAudit.lean
- SevenRealCubicHighDepthFive.lean
- scratch-061-mathlib-audit.lean

External primary-source targets:

- E. Thomas, Complete solutions to a family of cubic Diophantine equations,
  J. Number Theory 34 (1990), 235–250.
- M. Mignotte, Verification of a conjecture of E. Thomas,
  J. Number Theory 44 (1993), 172–177.
- M. Mignotte, A. Petho, F. Lemmermeyer, On the family of Thue equations
  x^3-(n-1)x^2 y-(n+2)xy^2-y^3=k, Acta Arith. 76 (1996), 245–269.

Source discipline:

- The 1996 paper explicitly treats the |F_n|=1 classification as already
  solved by Thomas/Mignotte. Its detailed Siegel–Baker/Baker–Davenport
  machinery is not, by itself, the fixed n=6 proof.
- Thomas 1990 states that for 0 <= n <= 1000 nontrivial solutions occur only
  for n = 0,1,3. Therefore n=6 is already covered by Thomas's finite/small-n
  argument.
- Do not use any published theorem as an axiom. Extract a finite certificate.

Current FLT7 requirement:
after cyclic normalization a nontrivial C=1 branch gives

    F5(R,S)=1
    7^8 | S
    7 ∤ R
    IsCoprime R S.

Hence |S| >= 7^8 = 5764801.

R56 has two goals:

1. finish the exact Lean approximation-to-convergent bridge;
2. identify and formalize the smallest fixed-n=6 finite certificate giving
   |S| < 7^8, or full triviality.

## Part A — exact three roots as ordered data

Upgrade the R55 existential roots to a reusable packet with

    lambda1 in [-6/5,-11/10]
    lambda2 in [-1/5,-1/10]
    lambda3 in [6,13/2]
    f5Real lambda_i = 0
    lambda1 < lambda2 < lambda3.

Retain the proved separation bounds:
    lambda2-lambda1 >= 9/10
    lambda3-lambda2 >= 61/10
    lambda3-lambda1 >= 71/10.

Do not require closed-form radicals.

## Part B — factorization at the three roots

For integers R,S with S != 0, prove over R:

    F5(R,S) / S^3
      = (R/S-lambda1)*(R/S-lambda2)*(R/S-lambda3).

It is acceptable to prove the monic-cubic factorization from:

- the three roots;
- pairwise distinctness;
- equality of two monic cubics of degree three.

Avoid introducing a general polynomial root-factorization framework unless
Mathlib already makes it short.

For F5(R,S)=1 conclude

    abs(Product_i (R/S-lambda_i)) = 1 / abs(S)^3.

## Part C — nearest-root approximation with explicit rational constant

For |S| >= 6, prove there exists i in {1,2,3} such that

    |R/S - lambda_i| < 1 / (2*S^2).

A simple fixed constant proof is preferred.

Suggested route:

1. From the product identity, one factor has absolute value <= 1/|S|.
2. For |S| >= 6 this nearest distance is <= 1/6.
3. The two other root distances are bounded below using the minimum root
   separation 9/10, hence at least 11/15 (or any easy rational lower bound).
4. Return to the exact product identity to improve the nearest distance to
   C/|S|^3 with a rational C < 3.
5. Check C/|S|^3 < 1/(2*S^2) for |S| >= 6.

Use rational constants friendly to linarith/norm_num; sharpness is irrelevant.

## Part D — Legendre bridge in the project Mathlib revision

Using Real.exists_rat_eq_convergent or its primed variant, prove:

    F5(R,S)=1
    IsCoprime R S
    |S| >= 6
    ----------------
    R/S is a continued-fraction convergent of one of lambda1,lambda2,lambda3.

Make denominator normalization/sign explicit.

Do not hide a reduced-fraction assumption: use IsCoprime R S to show the
rational denominator is |S| after normalization.

This theorem is a mandatory R56 Lean deliverable.

## Part E — inspect Thomas 1990 small-n proof directly

Obtain the actual article text if legally/publicly accessible in the working
environment. Do not infer its method from the abstract.

For the proof of the range 0 <= n <= 1000, record exactly:

- theorem/lemma numbers;
- root chosen;
- rational approximation theorem used;
- any bound on |y| or convergent index;
- any table/list of continued-fraction candidates;
- whether the computation is exhaustive by a mathematically proved bound;
- what input data specialize at n=6.

The report must distinguish:
    "stated in the paper"
from
    "reconstructed/inferred by us".

If the full text cannot be obtained, say so and do not invent constants.

## Part F — n=6 certificate extraction

Preferred result: an explicit theorem/data pair

    nontrivial F5(R,S)=1 -> |S| <= B

with a concrete integer B < 7^8.

The proof may be:

- a direct specialization of Thomas's small-n bound;
- a finite convergent-index bound;
- a fixed unit-exponent bound;
- another exact finite certificate present in the paper.

Every numerical constant used must be traced to a proved inequality or a
finite object that Lean can verify.

The current FLT7 branch only needs B < 5764801.

A dramatically smaller B is welcome but not required.

## Part G — finite convergent certificate

If Thomas provides a convergent/index bound N rather than a denominator bound:

1. materialize the first N convergents of the relevant root(s) as explicit
   rational data;
2. prove their recurrence in Lean;
3. prove every convergent up to index N appears in the data;
4. evaluate F5 on each reduced numerator/denominator;
5. retain only the trivial shell.

Generating the list with PARI/Sage/Python is allowed.
Completeness must be checked in Lean.

If N is large, prefer a recurrence theorem plus interval/index arithmetic over
a giant hand-written list.

## Part H — current-only shortcut

If the full Thomas certificate is awkward, seek only:

    F5(R,S)=1
    IsCoprime R S
    7^8 | S
    7 ∤ R
    ----------------
    False.

Allowed tools:

- Part D convergent bridge;
- exact continued-fraction prefix/recurrence;
- denominator growth;
- Thomas small-n explicit constants.

Do not require classification of solutions with small S if the high-depth
contradiction closes earlier.

## Part I — Mignotte 1993 fallback

If Thomas 1990 does not expose a usable finite certificate, inspect Mignotte
1993 directly.

Extract the fixed n=6 specialization of the proof of n>3 triviality:

- fundamental units used;
- linear form in logarithms;
- explicit lower bound;
- initial exponent bound;
- reduction step;
- final finite search.

Again, do not formalize a general transcendence theorem unless unavoidable.

If the only missing ingredient is one explicit fixed-number inequality from a
linear-forms theorem, isolate it exactly as the sole external mathematics
boundary.

## Part J — 1996 paper role

Use the 1996 Mignotte–Petho–Lemmermeyer paper only for:

- root estimates that can be specialized and proved directly;
- general method calibration;
- Baker–Davenport lemma shape;
- explicit finite numerical procedures when their hypotheses apply to n=6.

Do not cite its Theorem 1 as an n=6 bound: that theorem assumes n >= 1650.

Do not cite its Theorem 3 as the proof of F6=1 triviality: the paper itself
uses the already-solved |F_n|=1 result as input.

## Part K — production endpoint if certificate closes

If a certified B < 7^8 is proved, combine with the current deep-S branch:

    7^8 | S
    S != 0
      -> 7^8 <= |S|
      -> contradiction with |S| <= B.

Then prove

    EisensteinCurrentHighDepthFivePacket.source.q = 1

via the existing q=1 iff product-zero theorem, and trace through the already
checked trivial shell/projective-log/calibration chain to eliminate C=1.

Preferred public endpoint remains:

    directOrbit_no_trivial_common_factor_sharpened_packet
      (P : DirectOrbitTrivialCommonFactorSharpenedPacket h) : False.

Only add it if all steps are kernel-checked.

## Part L — exact boundary if still open

If R56 cannot obtain the finite bound, report the missing theorem in one line,
for example:

    FixedThomasSixBound:
      F5(R,S)=1 -> |S| < 5764801

or a stronger exact index-bound version.

Also state:

- everything before this theorem that is kernel-checked;
- everything after it that would be finite/kernel-checkable;
- why the missing theorem requires new transcendence/reduction machinery.

## Hard stops

- No paper theorem as axiom.
- No invented Thomas/Mignotte constants.
- No use of the 1996 n>=1650 theorem at n=6.
- No CAS claim of completeness without a Lean-checked bound.
- No floating-point root proof.
- No generic Baker theory unless fixed n=6 cannot be isolated.
- No C>1 work in this checkpoint.
- No final FLT7 theorem until the remaining branch is closed.
- No sorry, sorryAx, admit, unsafe, native_decide, or project axiom.

## Deliverables

Primary:

- report-062.md
- ROADMAP.md
- scratch/production Lean for Parts A-D.
- a concrete Thomas/Mignotte n=6 certificate ledger.

Promote a production closure module only if the finite bound is genuinely
kernel-checked.

## Outcomes

- Outcome A — a Thomas/Mignotte fixed-n=6 finite certificate gives B < 7^8
  (or full triviality) and C=1 is eliminated.
- Outcome B — approximation-to-convergent bridge is green and a complete
  finite n=6 certificate is identified, but one explicit bound lemma remains
  to formalize.
- Outcome C — Parts A-D are green; original small-n proof data are not
  accessible or not extractable into a finite certificate yet.
- Outcome D — fixed n=6 closure provably requires substantial new
  linear-forms-in-logarithms formalization; record the exact theorem boundary.
