# FLT7TC-005R55 — Fixed n=6 Thomas–Mignotte certificate extraction

Branch: research/FLT7-Unconditional-TraceOne-Closure-260917-v0

Authoritative current inputs:
- report-060.md
- SevenRealCubicHighDepthFive.lean
- SevenRealCubicEisensteinCoprimality.lean
- SevenRealCubicEisensteinCubeCertificate.lean

Current kernel endpoint on the C = 1 branch:

    F5(R,S) = R^3 - 5*R^2*S - 8*R*S^2 - S^3 = 1
    7^8 | R*S*(R+S)
    Q5(R,S) = R^2 + R*S + S^2 = q > 0
    q = 1 <-> R*S*(R+S) = 0

and the T=0 shell is already exactly

    (1,0), (0,-1), (-1,1).

Thus one theorem remains:

    F5(R,S) = 1 -> R*S*(R+S) = 0

or, for current provenance only, the weaker

    F5(R,S) = 1
    7^8 | R*S*(R+S)
    -----------------
    R*S*(R+S) = 0.

External mathematical calibration only:
- This is the Thomas family
    X^3 - (n-1)X^2Y - (n+2)XY^2 - Y^3 = 1
  at n = 6.
- Thomas (1990) verified the small-parameter range including n=6.
- Mignotte (1993) proved that for n>3 only the trivial solutions occur.
- Hoshi's simplest-cubic survey/correspondence records the same lambda=1
  classification.

These published theorems are NOT Lean assumptions. R55 must extract a
kernel-checkable fixed-n=6 certificate.

Do not formalize the full parametric Thomas–Mignotte theorem.

## Part A — target theorem and exact identification

Create a scratch target first:

    theorem F5_eq_one_trivial
        {R S : Z} (h : F5 R S = 1) :
        R*S*(R+S) = 0

and prove the literal identification with Thomas parameter n=6:

    F_Thomas 6 R S = F5 R S.

If a general Thomas form is not useful elsewhere, keep it local.

Also record the equivalent explicit three-solution theorem using the already
checked trivial shell.

## Part B — exact project Mathlib capability audit

Audit the exact Mathlib revision used by this branch, not current master only.

Check for:
- Mathlib.NumberTheory.DiophantineApproximation.Basic
- Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions
- Real.exists_rat_eq_convergent
- Real.exists_convs_eq_rat
- regular continued-fraction computation APIs
- exact/finitary convergent computation.

Record theorem names and whether they compile under the project toolchain.

Do not claim that the presence of Legendre's theorem is a complete Thue solver.

## Part C — fixed polynomial and rational root isolation

Define

    f5Poly(X) = X^3 - 5*X^2 - 8*X - 1.

Prove it has three real roots in explicit rational intervals, for example
intervals separating the approximate roots

    -1.1588...
    -0.1370...
     6.2958...

Choose rational endpoints that make all sign checks norm_num/ring-friendly.

Prove pairwise root-separation lower bounds sufficient for the approximation
argument.

Do not introduce decimal constants into production.

## Part D — direct approximation lemma for an F5 solution

For S != 0 and F5(R,S)=1, prove

    product_i (R/S - lambda_i) = 1/S^3

in the real field.

Choose a nearest root lambda and prove an explicit estimate of the form

    |lambda - R/S| < C / |S|^3

with a rational C small enough that for |S| >= a concrete small threshold,

    |lambda - R/S| < 1/(2*S^2).

Then use Mathlib's Legendre theorem to conclude that R/S is a convergent of
the continued fraction of lambda.

This part should be fixed-n=6 and use explicit rational root-separation bounds.

## Part E — high-depth shortcut

The current branch does NOT need full F5 classification if a denominator
bound below 7^8 can be certified.

After cyclic normalization, one of R, S, R+S is divisible by 7^8. Use sigma5
to normalize to

    7^8 | S
    7 ∤ R.

Hence nontrivial current solutions satisfy

    |S| >= 7^8.

Therefore any rigorously proved fixed-n=6 upper bound

    |S| < 7^8

for nontrivial F5=1 solutions immediately closes the current C=1 branch.

This is the preferred certificate shape if it is substantially cheaper than
the full Thomas–Mignotte classification.

## Part F — extract the published fixed-n=6 finite certificate

Read the actual Thomas/Mignotte proof mechanism, not only the theorem
statement.

Identify exactly what proves the n=6 case:
- a fundamental-unit representation;
- a continued-fraction finite search;
- a Baker/linear-form upper bound followed by reduction;
- or an explicit finite list produced by a certified recurrence.

Produce a ledger:

    theorem/lemma used
    exact numerical constant for n=6
    finite object to verify
    Mathlib/DkMath support
    missing formal lemma

The goal is to replace "the paper says n=6 is solved" by a finite list of
claims that Lean can check.

## Part G — certificate architecture

Prefer one of these architectures.

### G1. Continued-fraction certificate

If the published proof yields an explicit denominator/index bound:
1. prove every nontrivial solution ratio is a convergent;
2. compute all convergents up to the certified bound;
3. check exactly which convergents solve F5=1;
4. conclude only the three trivial solutions.

A generated list of convergents is acceptable if Lean verifies:
- the recurrence;
- completeness up to the proved bound;
- evaluation of F5.

Do not trust an external list without a Lean completeness proof.

### G2. High-depth denominator certificate

If only the current branch is targeted:
1. prove every current normalized solution has |S| >= 7^8;
2. derive a rigorous fixed-n=6 theorem |S| < 7^8 for any nontrivial solution;
3. contradict.

This is preferred over full classification if available.

### G3. Fundamental-unit certificate

If Thomas' 1979 unit theorem specializes cleanly to the fixed cubic order:
1. prove the required two explicit units form a fundamental system for the
   relevant order;
2. express R-lambda*S as a unit monomial;
3. derive the coefficient-zero equation;
4. reduce it to a finite exponent range with a proved bound;
5. verify that range.

Do not assume a fundamental-unit basis merely from numerical regulator data.

## Part H — allowed external computation

PARI/GP, Sage, Python, or another CAS may be used to GENERATE:
- root intervals;
- continued-fraction terms;
- candidate convergents;
- unit exponents;
- reduction matrices;
- numerical constants.

But production may consume them only as explicit data whose required
properties and completeness are proved in Lean.

A CAS statement "all solutions are ..." is not a certificate.

## Part I — production promotion if complete

Only if a complete fixed-n=6 proof is kernel-checked, create a neutral module,
preferred name:

    DkMath/NumberTheory/ThomasThueSix.lean

or a narrowly FLT7-owned module if the proof is too specialized.

Expose:

    theorem thomasSix_eq_one_trivial
        {R S : Z}
        (h : R^3 - 5*R^2*S - 8*R*S^2 - S^3 = 1) :
        R*S*(R+S) = 0

Then in FLT7 prove immediately:

    EisensteinCurrentHighDepthFivePacket.source.q = 1

and consume the existing q=1/T=0/trivial-shell chain.

Trace back through R53/R50 to prove the C=1 sharpened packet impossible.

Do not duplicate the already checked shell classification.

## Part J — C=1 exclusion endpoint

If Part I succeeds, add the provenance-preserving endpoint:

    theorem directOrbit_no_trivial_common_factor_sharpened_packet
        (P : DirectOrbitTrivialCommonFactorSharpenedPacket h) :
        False

and consequently

    h.c != 1

for the canonical current packet.

Then collapse the R49 dichotomy to the C>1 branch:

    1 < h.c
    29 <= h.c
    forall prime q | h.c, q % 7 = 1
    29*h.u^5 < h.v.

This is a genuine branch elimination.

## Part K — if the proof is still too large

If the fixed n=6 published proof fundamentally requires a large
Baker/linear-form formalization not present in Mathlib, do NOT begin a generic
transcendence library in this checkpoint.

Instead report the smallest verifiable certificate boundary, for example:

    all nontrivial solutions have |S| <= B

where:
- B is explicit;
- the proof of this bound is the only missing imported mathematics;
- everything after B is finite and Lean-checkable.

Likewise, if the continued-fraction route lacks only one effective bound,
state that exact bound theorem.

## Hard stops

- No external paper theorem as axiom.
- No bounded search without a proved bound.
- No floating-point root proof.
- No unverified CAS completeness.
- No generic Thomas–Mignotte formalization unless the n=6 specialization
  genuinely forces it.
- No p-adic congruence promoted to integer equality.
- No FLT3 terminal theorem reuse.
- No C>1 work in R55.
- No FLT7 final theorem until the remaining branch is closed.
- No sorry, sorryAx, admit, unsafe, native_decide, or project axiom.

## Deliverables

Primary:
- report-061.md
- ROADMAP.md
- scratch Lean for root isolation / Legendre / certificate verification.

Promote production only if the fixed-n=6 completeness argument is genuinely
kernel-checked.

## Outcomes

- Outcome A — fixed n=6 certificate is kernel-checked; F5 has only trivial
  solutions and C=1 is eliminated.
- Outcome B — a current-only bound below 7^8 is kernel-checked; C=1 is
  eliminated without full F5 classification.
- Outcome C — Legendre/root/certificate infrastructure is green and only one
  explicit effective bound remains.
- Outcome D — the fixed theorem requires substantial Baker/linear-form
  machinery absent from the project; record the exact missing theorem and stop.
