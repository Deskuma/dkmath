# FLT7TC-005R11 — Chosen-factor/tail nonramified coprimality and direct ideal extraction

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

Starting point: FLT7TC-005R10 / `report-015.md`.

This checkpoint must stay entirely on the **current**
`PrimitiveCounterexampleRamifiedProvenance` / direct cyclotomic factor route.
Do not enter `RamifiedSignedRootRoutingPacket` as a bypass, do not use a
receiver assumption, and do not use any theorem whose axiom audit contains
`sorryAx`.

The purpose is to replace the unnecessarily heavy “six stripped ideals are
pairwise coprime” route by a **chosen-factor vs. stripped-tail** two-factor
argument.

## 1. Fixed current data

For

```lean
r : PrimitiveCounterexampleRamifiedProvenance source
```

write conceptually

```text
L = r.summit.endpointLeft
R = r.summit.endpointRight
B = r.summit.residualRoot
pi = SevenCyclotomicDegreeSixInt.ramifiedUniformizer = 1 - zeta
eta = directLinearFactor r = L - zeta * R
q1 = directRamifiedQuotient r
```

Already checked:

```text
eta = pi * q1
q1 ∉ ramifiedPrime
eta ∈ ramifiedPrime
eta ∉ ramifiedPrime^2
sixPhaseProduct eta = 7 * B^7
N(eta) = 7 * B^7
7 ∤ R
IsCoprime L R
```

Also reuse the clean generic Kummer lemmas in
`DkMath.FLT.Kummer.CyclotomicPrincipalization`, especially:

```text
commonPrimeContainsSubOneY
commonPrimeDvdsSubOneOrY
spanSingletons_isCoprime_of_noCommonPrime
idealIsCoprime_prod_of_forall
dedekindIdealEqPowOfMulEqPowOfIsCoprime
linearFactorSpanEqPowOfTailMulEqSpanPowAndIsCoprime
```

and the concrete p=7 facts:

```text
SevenCyclotomicDegreeSixInt.zeta_isPrimitiveRoot
SevenCyclotomicDegreeSixInt.ramifiedPrime_isMaximal
SevenCyclotomicDegreeSixInt.ramifiedPrime_eq_span_uniformizer
SevenCyclotomicDegreeSixInt.ofReal_seven_eq_uniformizer_pow_six_mul_unit
SevenCyclotomicDegreeSixInt.ramifiedSevenUnit_isUnit
```

## 2. General nontrivial phase and a common uniformizer quotient

For `1 ≤ j < 7`, define the direct phase

```text
F_j = ofReal L - zeta^j * ofReal R.
```

Prefer a thin definition such as

```lean
def directCyclotomicPhaseFactor (r) (j : ℕ) : Ring := ...
```

and define

```text
S_j = 1 + zeta + ... + zeta^(j-1).
```

Use the exact identity

```text
1 - zeta^j = (1 - zeta) * S_j
```

and the existing direct gap factorization to construct an explicit quotient
`Q_j` with

```text
F_j = pi * Q_j.
```

The quotient should specialize/calibrate to the existing chosen quotient at
`j = 1`:

```text
Q_1 = directRamifiedQuotient r
```

up to definitional equality or a proved equality.

Prove the ramified residue formula

```text
ramifiedEval Q_j = j * R   in ZMod 7
```

(or the equivalent casted statement). Hence for `1 ≤ j < 7`:

```text
Q_j ∉ ramifiedPrime
F_j ∈ ramifiedPrime
F_j ∉ ramifiedPrime^2.
```

This is the preferred way to transport exact ramified multiplicity to all six
nontrivial phases. Do not infer it from the integer norm.

## 3. Chosen-vs-other common-prime classification

Prove the source-local theorem that for every `2 ≤ j < 7`, a prime ideal that
contains both the chosen phase and the `j`-th phase must be the ramified prime.
Conceptually:

```lean
theorem prime_eq_ramified_of_mem_chosen_and_other_phase
    (r : PrimitiveCounterexampleRamifiedProvenance source)
    {P : Ideal Ring} (hP : P.IsPrime)
    {j : ℕ} (hj2 : 2 ≤ j) (hj7 : j < 7)
    (h1 : F_1 ∈ P) (hj : F_j ∈ P) :
    P = ramifiedPrime
```

Use the existing generic theorem

```text
commonPrimeDvdsSubOneOrY
```

with the concrete primitive seventh root.

The two branches must be closed honestly:

1. `(zeta - 1) ∈ P`:
   use `ramifiedPrime_eq_span_uniformizer`, maximality, and the fact that
   `P` is proper to conclude `P = ramifiedPrime`.

2. `ofReal R ∈ P`:
   combine this with `F_1 ∈ P` to obtain `ofReal L ∈ P`, then use the stored
   endpoint coprimality to force `1 ∈ P`, contradicting primality/properness.
   Add only the smallest cast/Bezout helper needed for this step.

Do not assume a ring-of-integers identification.

## 4. Quotient coprimality: chosen quotient vs. every other quotient

For `2 ≤ j < 7`, prove

```text
IsCoprime (Ideal.span {Q_1}) (Ideal.span {Q_j}).
```

A recommended proof is via `spanSingletons_isCoprime_of_noCommonPrime`:
if a prime `P` contains `Q_1` and `Q_j`, then it also contains
`F_1 = pi*Q_1` and `F_j = pi*Q_j`. Section 3 gives `P = ramifiedPrime`, but
`Q_1 ∉ ramifiedPrime`, contradiction.

This is the key simplification: **do not prove all `Q_i,Q_j` pairwise
coprime.** Only `Q_1` against `Q_j`, `j=2,...,6`, is required.

## 5. Tail quotient and chosen-vs-tail coprimality

Define

```text
T = product of Q_j for j = 2,...,6.
```

Any minimal finite indexing is acceptable (`Finset.Icc 2 6`, an explicit
five-element finset, etc.).

Use the preceding pairwise chosen-vs-other statements and
`idealIsCoprime_prod_of_forall` to prove

```text
IsCoprime (Ideal.span {Q_1}) (Ideal.span {T}).
```

Also prove the five-phase factorization

```text
product_{j=2..6} F_j = pi^5 * T.
```

and the full six-phase factorization

```text
product_{j=1..6} F_j = pi^6 * (Q_1 * T).
```

Connect this explicit nontrivial-root product to the already checked
`sixPhaseProduct (directLinearFactor r)`.

You may prove the correspondence using the existing Galois formulas

```text
rotateEquiv_zeta
rotateEquiv_three
star_zeta
zetaInv_eq_pow_six
```

or by a direct primitive-root product identity. Choose the smaller checked
route; do not duplicate a large cyclotomic development.

## 6. Cancel the total ramified load

Combine

```text
sixPhaseProduct eta = 7 * B^7
ofReal 7 = pi^6 * ramifiedSevenUnit
```

with the full quotient factorization and `pi ≠ 0` to prove an element-level
identity of the form

```text
Q_1 * T = ramifiedSevenUnit * ofReal(B)^7.
```

Exact coercion/order variations are fine.

At the ideal level, remove the unit and prove

```text
Ideal.span {Q_1} * Ideal.span {T}
  = Ideal.span {ofReal B} ^ 7.
```

Do **not** claim that `ramifiedSevenUnit` is a seventh power. Only its being a
unit is needed here.

## 7. Direct seventh-power ideal extraction

Use the two-factor Dedekind theorem

```text
dedekindIdealEqPowOfMulEqPowOfIsCoprime
```

(or the thin `linearFactor...` wrapper if cleaner) with the chosen-vs-tail
coprimality to obtain

```text
∃ I : Ideal Ring,
  Ideal.span {Q_1} = I ^ 7.
```

Then combine with

```text
eta = pi * Q_1
ramifiedPrime = Ideal.span {pi}
```

to prove the direct target:

```lean
theorem directLinearFactorIdeal_eq_ramifiedPrime_mul_pow
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    ∃ I : Ideal Ring,
      Ideal.span {directLinearFactor r} =
        ramifiedPrime * I ^ 7
```

This theorem is the primary success criterion of FLT7TC-005R11.

## 8. Optional PID extraction only after Section 7

Only if Section 7 is green, use the already checked PID for the concrete
carrier to expose the honest element-level consequence, conceptually

```text
eta = u * pi * beta^7
```

for an explicit/existential unit `u`.

Do not attempt to kill or normalize `u` in this checkpoint. The `mu_7` phase
is a later frontier.

## 9. Calibration / non-circularity audits

Add API tests proving at least:

- `Q_1` agrees with `directRamifiedQuotient`;
- the chosen-vs-other common-prime theorem for one concrete phase, e.g. `j=2`;
- chosen quotient vs. tail coprimality;
- the quotient product ideal identity;
- the final direct ideal packet if obtained.

Axiom audit every decisive theorem. The new path must not depend on:

```text
RamifiedSignedRootRoutingPacket
CubicGapSeventhShapeReceiver
triominoCosmicNoPowOnGN_default
cyclotomicNormDescentNonFirstCaseGNPowerReceiver_of_classGroupPTorsionFree
```

if those introduce circularity or `sorryAx`.

## 10. Hard stops

Do not:

- infer ideal exponent ownership from `N(eta) = 7 * B^7` alone;
- infer `Q_j ∉ ramifiedPrime` merely from the norm;
- infer `Q_1` and `T` are coprime without the common-prime proof;
- treat a unit multiple of a seventh power as a seventh power;
- assume `ramifiedSevenUnit` is a seventh power;
- identify the concrete carrier with a full ring of integers unless a checked
  theorem already supplies that identification;
- use `sorry`, `admit`, `unsafe`, a project `axiom`, or a theorem carrying
  `sorryAx`;
- claim FLT7, receiver existence, or a contradiction merely from the ideal
  packet.

## 11. Preferred new modules

Prefer a narrow module such as

```text
DkMath/FLT/Seven/PrimeTraceOneDirectCyclotomicChosenTail.lean
```

with matching API/axiom audits. Update `report-016.md` and this campaign's
`ROADMAP.md`. Do not expand the public facade unless a stable non-speculative
API is actually obtained.

## 12. Required validation

At minimum run:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicChosenTail
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectCyclotomicChosenTailApi
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectCyclotomicChosenTailAxiom
```

plus `git diff --check` and a forbidden-source scan over newly added Lean
sources.

## 13. Report outcome

Report exactly one of:

```text
Outcome A — CHOSEN/TAIL COPRIMALITY AND DIRECT RAMIFIED-IDEAL SEVENTH-POWER EXTRACTION GREEN
```

The theorem

```text
span{eta} = ramifiedPrime * I^7
```

is kernel-checked from current counterexample provenance. Any remaining gap is
strictly after ideal extraction (PID associated unit / mu_7 phase).

```text
Outcome B — COMMON-PRIME AND CHOSEN/TAIL COPRIMALITY GREEN; QUOTIENT PRODUCT/POWER EXTRACTION REMAINS
```

The nonramified support problem is solved, but the exact `Q_1*T` or ideal
product equality has a concrete remaining bridge.

```text
Outcome C — COMMON-PRIME CLASSIFICATION GREEN; TAIL QUOTIENT PACKAGING REMAINS THE PRECISE FRONTIER
```

The key arithmetic classification is proved, but the five-phase quotient/tail
transport is not yet completed.

```text
Outcome D — CHOSEN/OTHER COMMON-PRIME CLASSIFICATION ITSELF REQUIRES A NEW BRIDGE
```

Record the exact missing theorem/type obstruction. Do not substitute a norm or
valuation argument.
