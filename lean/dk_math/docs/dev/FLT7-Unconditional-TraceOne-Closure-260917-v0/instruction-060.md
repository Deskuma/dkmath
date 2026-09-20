# FLT7TC-005R54 — High-depth F5 packet and cyclic normalization

Branch: research/FLT7-Unconditional-TraceOne-Closure-260917-v0

Authoritative inputs:
- report-059.md
- SevenRealCubicEisensteinCoprimality.lean
- SevenRealCubicEisensteinCubeCertificate.lean
- SevenRealCubicSimplestCubicCertificate.lean
- SevenRealCubicSourcePlaneNormSeven.lean

R53 kernel-checks:
- current Eisenstein conjugate relative primality;
- cube extraction;
- unique tauSq sector;
- the exact surviving equation

    F5(R,S) := R^3 - 5*R^2*S - 8*R*S^2 - S^3 = 1.

The report records the remaining current high-depth condition

    7^8 | R*S*(R+S),

but this transport is not yet exposed as a public production theorem.

R54 must first make that high-depth F5 packet explicit and provenance-preserving.
Then audit the strongest elementary consequences before invoking any new
effective Thue/field-isomorphism theory.

## Part A — exact tauSq coordinate transport

Let a current R53 packet have

    delta = tauSq * gamma^3
    gamma = eisensteinCoord R S

and let

    X := R^3 - 3*R*S^2 - S^3
    Y := 3*R*S*(R+S).

Using the exact current stripping coordinates, introduce T with

    r = -1 + 8*T
    s =  1 - 5*T
    7^8 | T.

Prove from delta = tauSq * gamma^3:

    X = 1 - 5*T
    Y = -3*T.

Then prove exactly

    T = -R*S*(R+S),

hence

    7^8 | R*S*(R+S).

Also prove

    q^3 = 49*T^2 - 13*T + 1

for q = norm gamma.

This transport is mandatory.

## Part B — public high-depth F5 packet

Create a thin structure, conceptually:

    structure EisensteinCurrentHighDepthFivePacket where
      R S q T : Z
      five_eq :
        R^3 - 5*R^2*S - 8*R*S^2 - S^3 = 1
      q_norm :
        R^2 + R*S + S^2 = q
      q_pos : 0 < q
      T_eq : T = -R*S*(R+S)
      T_depth : 7^8 | T
      q_cube :
        q^3 = 49*T^2 - 13*T + 1

Construct it directly from the current C=1 sharpened provenance, not from
arbitrary assumptions only.

Retain source/r/p/h/P provenance through the wrapper theorem.

## Part C — primitive triple of linear factors

From F5(R,S)=1 prove:

    IsCoprime R S
    IsCoprime R (R+S)
    IsCoprime S (R+S)

over integers.

Hence among

    R, S, R+S

at most one is divisible by 7.

Together with 7^8 | R*S*(R+S), prove that exactly one factor carries the
entire 7-adic depth at least 8.

Package the three alternatives explicitly:

    7^8 | R
or
    7^8 | S
or
    7^8 | R+S,

with pairwise exclusion modulo 7.

## Part D — order-three symmetry of F5

Define the integral transformation

    sigma5(R,S) = (-R-S, R).

Prove:

    sigma5^3 = identity

and exact invariance of:

    F5(R,S)
    Q5(R,S) := R^2 + R*S + S^2
    T5(R,S) := R*S*(R+S).

Thus every current high-depth packet may be rotated so that the deep factor is
in one chosen coordinate, preferably S.

Do not lose the sign/orientation of T.

## Part E — standard deep-S branch

After cyclic normalization, obtain

    F5(R,S)=1
    7^8 | S
    7 does not divide R.

Prove the exact identity

    F5(R,S)
      = (R + 3*S)^3
        - 7*S*(2*R^2 + 5*R*S + 4*S^2).

Therefore

    (R + 3*S)^3 - 1
      = 7*S*(2*R^2 + 5*R*S + 4*S^2).

Factor the left side:

    (R+3S-1) * ((R+3S)^2 + (R+3S) + 1).

Audit the exact gcd of these two factors; it divides 3.

Record which of the three cube-root branches modulo 7 occurs.
Do not claim global uniqueness from Hensel lifting.

## Part F — q=1 iff T=0

From

    q > 0
    q^3 = 49*T^2 - 13*T + 1

prove:

    T = 0 -> q = 1.

Also prove the converse:

    q = 1 -> T = 0.

For the converse, reduce to

    T*(49*T - 13) = 0

and exclude 49*T=13 over integers.

Hence

    q = 1 iff R*S*(R+S)=0.

## Part G — finite trivial shell from T=0

Prove neutrally:

    F5(R,S)=1
    R*S*(R+S)=0
    --------------------------------
    (R,S) = (1,0) or (0,-1) or (-1,1).

For each case prove

    Q5(R,S)=1.

This is a finite exact classification and is admissible.

If current q=1 is later proved, R53/R50 can consume this immediately.

## Part H — simplest-cubic parameter shadow

Define

    n5(R,S) := 5 + 49*R*S*(R+S).

Kernel-check the purely arithmetic identities:

    n5 = 5 - 49*T

under T = -R*S*(R+S),

and current high depth implies

    7^10 | n5 - 5.

Also prove n5 = 5 iff T=0.

This is only an arithmetic shadow.

External research calibration:
for Shanks simplest cubic forms, a nontrivial F_m=1 solution naturally
produces a parameter n = m + (m^2+3m+9)xy(x+y), and the associated simplest
cubic field is isomorphic to the original one. For m=5 this is exactly
n = 5 + 49*R*S*(R+S).

Do NOT use that external field-isomorphism theorem as a Lean axiom.

## Part I — explicit Tschirnhausen audit

Investigate whether, for m=5 only, the field-isomorphism direction can be
proved directly by an explicit algebraic element in the already formalized
SevenRealCubic field.

Target only an explicit statement of the form:

    F5(R,S)=1
      -> exists beta in SevenRealCubicInt/Field
           satisfying
           beta^3 - n*beta^2 - (n+3)*beta - 1 = 0

with

    n = 5 + 49*R*S*(R+S).

A direct polynomial identity is acceptable.

This does NOT close the branch by itself.

Do not attempt the global classification of all n with L_n = L_5 in R54.

## Part J — completeness route audit

Compare these exact next routes after the high-depth packet is green:

1. Direct high-depth F5 theorem:
       F5=1 and 7^8 | R*S*(R+S) -> product = 0.
2. Explicit simplest-cubic field-isomorphism plus a new special
   n ≡ 5 mod 7^10 rigidity theorem.
3. Fundamental-unit / logarithmic-lattice route.
4. Effective Thue/continued-fraction certificate.

For each, state the minimum missing theorem and estimated implementation size.

Do not manufacture a winner if all require major new theory.

## Part K — optional C=1 closure

Only if Part J unexpectedly yields a kernel-checked theorem

    R*S*(R+S)=0

consume Part F/G to get q=1 and the trivial F5 solution.

Then trace backwards through R53/R50 and contradict

    correction_ne_one.

Only then expose C=1 exclusion.

## Hard stops

- No external Hoshi/Okazaki classification as an axiom.
- No finite unbounded search as proof.
- No p-adic congruence promoted to integer equality.
- No FLT3 terminal contradiction/descent reuse.
- No C>1 character work in this checkpoint.
- No FLT7 conclusion unless all required branches close.
- No sorry, sorryAx, admit, unsafe, native_decide, or project axiom.

## Deliverables

Primary:
- a neutral/current high-depth F5 production module if Parts A-G are clean;
- report-060.md;
- ROADMAP.md.

If Part I is only reconnaissance, keep it in scratch/report rather than
polluting the production API.

## Outcomes

- Outcome A — high-depth F5 packet is green and the product is proved zero,
  eliminating C=1.
- Outcome B — high-depth packet, cyclic normalization, q=1 iff T=0, and
  trivial T=0 shell are green; product=0 remains the exact theorem.
- Outcome C — exact high-depth transport is green but cyclic normalization or
  packet orchestration remains the frontier.
- Outcome D — the expected 7^8 transport fails; document the corrected
  current arithmetic.
