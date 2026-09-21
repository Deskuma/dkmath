# FLT7TC-005R38 — Common-prime Kummer residue obstruction and canonical branch split

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

Authoritative inputs:

- `report-043.md`
- `PrimeTraceOneDirectRealCubicCanonicalCommonFactor.lean`
- `PrimeTraceOneDirectRealCubicPrimeAllocation.lean`
- `PrimeTraceOneDirectRealCubicSquareTwistObstruction.lean`
- `PrimeTraceOneDirectRealCubicLocalClass.lean`
- `PrimeTraceOneDirectRealCubicTwistClass.lean`
- `PrimeTraceOneDirectRealCubicResidueSupport.lean`
- `SevenRealCubicUnitClass.lean`

R37 supplies a canonical packet with

```text
C = gcd R S
R = C * U^3
S = C^2 * V^3
a = C * U * V
pairwise Coprime C U, C V, U V
C * U^5 < V,
```

and every prime divisor of `C` is congruent to `±1 mod 7`.

R34–R36 additionally give, for every prime `q | C`, exact complete splitting,
one gap prime versus two quotient primes, exact prime-ideal multiplicities,
and the rational norm exponent pair `(m,2m)` where `m = a.factorization q`.

R27 gives the exact square-twisted identity

```text
c0 * (r0^7)^2 + c1 * (r1^7)^2 + c2 * (r2^7)^2 = 0
```

with `r1 = rotate r0`, `r2 = rotate^2 r0`, and coefficient projective classes

```text
log c0 = (2,4)
log c1 = (2,2)
log c2 = (2,5).
```

This checkpoint is the first direct contradiction audit after the canonical
`C,U,V` split.  Do not add another global normalization layer unless it is
forced by the local calculation.

## Goal

Split the canonical state into the two honest cases

```text
C = 1
or
C > 1 and there exists a prime q | C.
```

For the nontrivial-common-factor branch, reduce R27 at the unique gap prime
above `q` and obtain an explicit seventh-power residue condition for one fixed
global unit class.

The intended fixed representative is

```text
epsilon := alphaUnit * alphaAddOneUnit
```

whose projective class is `(0,3)`.

The desired local endpoint is conceptually:

```text
q | C
  -> choose the unique gap prime P above q
  -> beta := alpha mod P
  -> exists z != 0 in P.ResidueField,
       z^7 = beta * (1 + beta).
```

Together with the existing cubic relation for `beta`, this is the Kummer
residue obstruction attached to the common-prime branch.

No contradiction is to be claimed unless the checked residue condition is
actually incompatible with the existing data.

## Part A — canonical `C = 1` / `C > 1` split

For `h : DirectOrbitCanonicalCommonFactorPacket p`, expose a small branch
theorem:

```text
h.c = 1
or
exists q, q.Prime and q | h.c.
```

In the `C = 1` branch record only the immediate arithmetic state:

```text
R = U^3
S = V^3
a = U * V
Nat.Coprime U V
U^5 < V.
```

Do not attempt ideal scalarization of the square roots in this checkpoint.
If the common-prime branch survives, scalarization of the `C = 1` branch is a
candidate for the next checkpoint.

## Part B — instantiate a canonical common prime

Assume `q.Prime` and `q | h.c`.

Using `h.c_eq_gcd`, derive

```text
q | R
q | S
q | a.
```

Reuse existing theorems to obtain:

```text
q != 7
q % 7 = 1 or q % 7 = 6
primesOver(q).ncard = 3
ramification index = 1
inertia degree = 1.
```

Do not rebuild the R30/R31 finite-field argument.

## Part C — choose the unique gap prime and fix the vanishing orientation

Choose a prime ideal `P` above `(q)` with

```text
model r0 in P
```

where `r0 := h.squareRefinement.gapSquareRoot`.

Prefer reusing the R36 gap q-primary residual theorem to obtain such a `P`.

Prove the exact orientation facts:

```text
evalP r0 = 0
evalP r1 != 0
evalP r2 != 0,
```

where

```text
r1 := rotateEquiv r0
r2 := rotateEquiv r1
evalP : SevenRealCubicInt ->+* P.ResidueField.
```

The nonvanishing proof must use the checked cyclic Galois action and the R34
singleton gap-prime allocation.  Do not assume that distinct conjugate
elements automatically have distinct reductions.

A recommended proof shape is:

1. `r0 in P` identifies `P` as the unique gap prime;
2. if `r1 in P`, use the inverse/comap action transport to make another
   Galois conjugate prime a gap prime;
3. singleton allocation forces that conjugate prime to equal `P`;
4. this collapses the three-element Galois orbit, contradicting
   `primesOver(q).ncard = 3`;
5. similarly for `r2`.

Equivalent kernel-checked arguments are acceptable.

## Part D — reduce the R27 equation modulo the gap prime

Map `directOrbit_squareTwist_twisted_eq` into `P.ResidueField`.

Since `r0` vanishes and `r1,r2` do not, divide by the nonzero unit and root
factors to prove a literal 14th-power relation.

Define, or use locally, the global unit

```text
twistRatio21(t) :=
  (-1) * directOrbitSquareTwistCoeff2 t *
    (directOrbitSquareTwistCoeff1 t)^(-1).
```

Then prove in the residue field:

```text
exists y != 0,
  y^14 = evalP (twistRatio21(t)).
```

With the orientation above, the natural witness is the quotient `r1 / r2`.

Do not replace this by an abstract cardinality statement.  Keep the explicit
ratio because it is needed for the unit-class bridge.

## Part E — identify the fixed global unit class

Define the fixed unit

```text
commonKummerUnit := alphaUnit * alphaAddOneUnit.
```

Kernel-check

```text
projectiveLog commonKummerUnit = (0,3).
```

using the existing generator values

```text
projectiveLog alphaUnit       = (5,5)
projectiveLog alphaAddOneUnit = (2,5).
```

Also prove

```text
projectiveLog twistRatio21(t) = (0,3).
```

using the R27 coefficient classes and `projectiveLog_neg_one`.

Hence

```text
projectiveLog
  (twistRatio21(t) * commonKummerUnit^(-1)) = 0.
```

Apply

```text
unit_isSeventhPower_iff_projectiveLog_eq_zero
```

to obtain an exact global unit `w` with

```text
twistRatio21(t) = commonKummerUnit * w^7.
```

Do not treat equality of projective classes as literal unit equality without
this checked seventh-power correction.

## Part F — fixed Kummer residue condition

Combine Part D and Part E in `P.ResidueField`.

Because

```text
y^14 = (y^2)^7
```

and the image of the global unit `w` is nonzero, divide the two seventh powers
to prove

```text
exists z != 0,
  z^7 = evalP commonKummerUnit.
```

Let

```text
beta := evalP alpha.
```

Using the literal values of `alphaUnit` and `alphaAddOneUnit`, rewrite the
endpoint as

```text
exists z != 0,
  z^7 = beta * (1 + beta).
```

Also retain the checked cubic relation

```text
beta^3 = 2*beta^2 + beta - 1
```

and, if cheap, the existing `beta^3 != 1` fact from the residue criterion.

Package these facts in a small local packet or theorem.  Avoid a large new
global structure unless it materially improves the API.

## Part G — optional transport to `ZMod q`

If practical, use the same degree-one finite-field equivalence pattern as
`common_norm_prime_mod_seven` to transport the local packet to `ZMod q`.

A useful public or scratch statement is:

```text
exists beta z : ZMod q,
  beta^3 = 2*beta^2 + beta - 1
  and z != 0
  and z^7 = beta * (1 + beta).
```

Keep the `q % 7 = 1` and `q % 7 = 6` cases distinct:

- if `q % 7 = 6`, the seventh-power map on `F_q^*` is bijective, so the
  fixed seventh-power condition by itself is not an obstruction;
- if `q % 7 = 1`, the condition is genuinely a seventh-power residue
  restriction.

Do not claim either branch impossible without proof.

## Part H — finite calibration, scratch/report only

Calibrate the `q % 7 = 1` residue condition so that the next checkpoint does
not chase a false universal contradiction.

Recommended examples in `ZMod` scratch:

```text
q = 29:
  beta = 4 is a cubic root, but beta*(1+beta) = 20 is not a seventh power.

q = 379:
  beta = 206 is a cubic root,
  beta*(1+beta) = 194,
  29^7 = 194 mod 379.
```

The `q=379` example demonstrates that the fixed Kummer condition is
arithmetically consistent for at least one `q ≡ 1 mod 7`.

This calibration is not production mathematics and should remain in scratch
or the report.

## Part I — existing-theorem clash audit

After the local Kummer packet is green, audit the current checked surface.

Questions:

1. Does any existing theorem imply that `commonKummerUnit` cannot be a
   seventh power in the selected residue field?
2. Does the exact coefficient transport give an additional independent
   square-class condition beyond the seventh-power condition?
3. Can the signed norm `norm c0 = 1` or the mixed real signature constrain
   this finite-field residue?
4. Does the canonical pairwise coprimality of `C,U,V` add another local
   condition at `q` beyond the already used common-prime hypotheses?
5. Does current provenance force `C = 1`?

Important separation:

`projectiveLog` is a ramified/theta-adic mod-7 unit-class invariant.  It does
not, by itself, decide seventh-power residuosity modulo an arbitrary common
prime `q`.  The bridge in Part E is valid only because it produces a literal
global seventh-power correction before reduction.

If the `q=379` calibration survives, do not claim that the seventh-power
condition alone excludes the `q % 7 = 1` branch.

## Part J — stop

Stop after the common-prime Kummer residue condition and clash audit.

If no contradiction is found, the next research choices should be recorded
explicitly:

```text
C > 1 branch:
  study the power-residue symbol of alpha*(1+alpha), possibly together with
  the independent square condition carried by the full 14th-power ratio;

C = 1 branch:
  audit ideal scalarization of the two square roots against the canonical
  U,V split.
```

Do not begin either large follow-up inside R38.

## Hard stops

- No assumption that `C > 1`.
- No assumption that a common prime exists in the `C = 1` branch.
- No identification of projectiveLog with a residue symbol modulo `q`.
- No claim that projective class `(0,3)` is itself a contradiction.
- No claim that `q ≡ 1 mod 7` is impossible from the Kummer condition alone.
- No claim that `q ≡ 6 mod 7` is impossible from seventh-power residuosity;
  the seventh-power map is bijective there.
- No inference that two rotated roots are nonzero modulo `P` without a checked
  Galois/singleton argument.
- No successor/descent construction.
- No FLT7 contradiction claim without an actual checked clash.
- No `sorry`, `sorryAx`, `admit`, `unsafe`, or project `axiom`.

## Preferred production file

Prefer a new focused file:

```text
DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicCommonPrimeKummer.lean
```

importing the canonical common-factor layer and the square-twist/unit-class
surface.

Export only stable theorems through `DkMath.FLT.Seven`.

Add focused API/axiom tests and an R38 scratch file.

Create `report-044.md` and update `ROADMAP.md`.

## Report questions

1. Was the `C=1` / nontrivial-common-prime branch split exposed?
2. For `q | C`, was a unique oriented gap prime `P` chosen?
3. Were `r1` and `r2` proved nonzero in `P.ResidueField`?
4. Was the exact 14th-power coefficient-ratio relation kernel-checked?
5. Was the fixed unit `alphaUnit * alphaAddOneUnit` proved to have class `(0,3)`?
6. Was the square-twist ratio proved to have the same class?
7. Was their quotient proved to be an exact global seventh power?
8. Was `beta*(1+beta)` proved to be a seventh power in the selected residue field?
9. Was the condition transported to `ZMod q` if practical?
10. Did the `q=379` calibration confirm that the `q ≡ 1 mod 7` condition is not universally contradictory?
11. Did any additional existing checked invariant close either branch?

## Outcomes

- Outcome A — the local Kummer reduction plus existing checked invariants gives an actual contradiction.
- Outcome B — fixed Kummer residue condition is green; it is arithmetically compatible and no contradiction is obtained.
- Outcome C — the 14th-power local ratio is green, but the exact global seventh-power correction to the fixed `(0,3)` unit is the precise frontier.
- Outcome D — common-prime orientation is green, but proving both rotated roots nonzero in the chosen residue field is the precise frontier.
- Outcome E — the residue-field reduction is blocked by an unavailable quotient/action API.

## Validation

At minimum:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicCommonPrimeKummer
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicCommonPrimeKummerApi
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicCommonPrimeKummerAxiom
lake env lean DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicCommonPrimeKummerScratch.lean
git diff --check
```

Print axioms for:

- the unique-gap-prime rotated-root nonvanishing theorem;
- the local 14th-power ratio theorem;
- the fixed Kummer unit projective class;
- the exact global seventh-power correction;
- the residue-field `beta*(1+beta)` seventh-power theorem.

Run forbidden-source/import scans on every decisive file.
