# FLT7TC-005R49 — Post-Astra sharpened branch packet

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

Authoritative inputs:

- `report-051.md` — finite-Hensel `7^9) correction.
- `report-053.md` — source-sensitive calibration exclusion.
- `report-054.md` — common-prime residue-one strengthening.
- `PrimeTraceOneDirectRealCubicTrivialCommonFactor.lean`
- `PrimeTraceOneDirectRealCubicTrivialCommonFactorDeepJet.lean`
- `PrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJet.lean`
- `PrimeTraceOneDirectRealCubicCalibrationExclusion.lean`
- `PrimeTraceOneDirectRealCubicCommonPrimeResidueOne.lean`
- `SevenRealCubicUnitClass.lean`

R49 is a consolidation checkpoint.

Do not invent a new contradiction.  Package the two Astra breakthroughs and
the R45 high-power correction into one current-provenance branch surface that
future research can consume directly.

## Part A — new production module

Create:

```text
DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicSharpenedBranch.lean
```

Preferred imports:

```lean
import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicCalibrationExclusion
import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicCommonPrimeResidueOne
import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJet
```

Keep this module thin: it should mostly orchestrate existing public theorems.

Namespace:

```text
DkMath.FLT.Seven.SevenRealCubic
```

## Part B — C=1 high-power correction with nontrivial correction

From:

```text
h : DirectOrbitCanonicalCommonFactorPacket p
hc : h.c = 1
```

construct the existing scalar units:

```text
eta
xi
```

using:

```text
directOrbitTrivialCommonFactor_gap_scalar_unit_of_c_eq_one
directOrbitTrivialCommonFactor_quotient_scalar_unit_of_c_eq_one.
```

Then construct the R41 seventh-root unit `v` using the existing global
deep-jet correction and linear-coordinate closure.

Feed these data into

```text
directOrbitPairedDeepJet_current_depth9_wrapper
```

to obtain a unit `t` with

```text
W = rho * t^(7^9).
```

Use the R47 public theorem

```text
directOrbitDeepJetWUnit_ne_calibration
```

to prove

```text
t^(7^9) != 1.
```

This is mandatory.

Preferred public theorem shape:

```lean
theorem directOrbitTrivialCommonFactor_exists_nontrivial_7pow9_correction
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p)
    (hc : h.c = 1) :
    ∃ eta xi v t : SevenRealCubicIntˣ,
      h.squareRefinement.gapSquareRoot =
        (eta : SevenRealCubicInt) * (h.u : SevenRealCubicInt) ∧
      h.squareRefinement.quotientSquareRoot =
        (xi : SevenRealCubicInt) * (h.v : SevenRealCubicInt) ∧
      directOrbitDeepJetWUnit h.squareRefinement eta =
        directOrbitDeepJetRho * v^7 ∧
      thetaLinearModSeven (v : SevenRealCubicInt) = 0 ∧
      v = t^(7^8) ∧
      directOrbitDeepJetWUnit h.squareRefinement eta =
        directOrbitDeepJetRho * t^(7^9) ∧
      t^(7^9) != 1
```

Equivalent association/order is acceptable.

Retain the original `source/r/p/h` provenance.

## Part C — norm-one correction audit

Attempt the cheap strengthening:

```text
norm (t : SevenRealCubicInt) = 1.
```

Use only existing facts:

```text
norm W = 1
norm rho = 1
W = rho * t^(7^9).
```

Since `7^9` is odd, the norm of `t` cannot be `-1`.

Do not prove a generic new unit-norm theory if this is not a short consequence
of the existing unit norm API.

If green, add the norm-one conclusion to the C=1 wrapper.

If the proof becomes disproportionately large, leave it as an explicit R49
audit result and do not block the mandatory theorem.

## Part D — non-torsion correction audit

If Part C is green, inspect the already-used theorem

```text
NumberField.Units.torsion_eq_one_or_neg_one_of_odd_finrank
```

through

```text
modelUnitsEquivRingOfIntegers.
```

Attempt to prove that the model unit `t` is not torsion in the full ring of
integers.

Conceptually:

1. transport `t` to `(𝓞 Field)ˣ`;
2. assume its image lies in `NumberField.Units.torsion Field`;
3. odd degree gives image `= 1` or `= -1`;
4. norm-one excludes `-1`;
5. image `=1` gives `t=1`;
6. hence `t^(7^9)=1`, contradicting Part B.

A theorem expressing “not in the torsion subgroup” is preferred over inventing
a new notion of infinite order.

This strengthening is optional but highly desirable.

Do not assert a concrete fundamental-unit decomposition.

## Part E — C>1 sharpened support packet

Prove a thin wrapper:

```lean
theorem directOrbitCommonFactor_large_residue_one_support
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p)
    (hc : 1 < h.c) :
    29 <= h.c ∧
      ∀ q, q.Prime -> q ∣ h.c -> q % 7 = 1
```

Use only:

```text
directOrbitCommonFactor_c_ge_29
directOrbitCommonPrime_q_mod_seven_one.
```

No new prime arithmetic is needed.

## Part F — sharpened dichotomy theorem

Package the current canonical packet into one public theorem.

Preferred conceptual shape:

```lean
theorem directOrbit_sharpened_common_factor_dichotomy
    (h : DirectOrbitCanonicalCommonFactorPacket p) :
    (h.c = 1 ∧ <C=1 high-power nontrivial-correction data>) ∨
    (1 < h.c ∧ 29 <= h.c ∧
      ∀ q, q.Prime -> q ∣ h.c -> q % 7 = 1)
```

Because the C=1 branch contains existential unit data, a dedicated structure
is preferred if the tuple becomes unreadable.

Recommended structures:

```lean
structure DirectOrbitTrivialCommonFactorSharpenedPacket ... where
  eta : SevenRealCubicIntˣ
  xi : SevenRealCubicIntˣ
  v : SevenRealCubicIntˣ
  t : SevenRealCubicIntˣ
  ...
  correction_eq :
    W = rho * t^(7^9)
  correction_ne_one :
    t^(7^9) != 1
  -- optional:
  correction_norm_eq_one : norm (t : SevenRealCubicInt) = 1
  -- optional non-torsion field if Part D is green

structure DirectOrbitNontrivialCommonFactorSharpenedPacket ... where
  c_ge_29 : 29 <= h.c
  prime_support :
    ∀ q, q.Prime -> q ∣ h.c -> q % 7 = 1
```

Then expose:

```text
Nonempty trivial-sharpened-packet
  or
Nonempty nontrivial-sharpened-packet.
```

Keep naming compact and consistent with repository conventions.

## Part G — optional height corollary

On the `1 < h.c` branch, combine:

```text
29 <= h.c
h.height : h.c * h.u^5 < h.v
```

to obtain:

```text
29 * h.u^5 < h.v.
```

Promote only if this is a short arithmetic corollary.

## Part H — do not reopen character/degree-six work yet

Astra also produced the cyclic product:

```text
R * sigma(R) * sigma^2(R) = -1.
```

Do not use it in R49.

The 14th-power condition lives at oriented Galois-shifted primes, so a
quadratic-character product requires an exact residue-field transport theorem.
Do not infer `q % 28 = 1` from the current data without that transport.

This warning should be recorded in the report.

## Part I — integration

Add the new module to the FLT7 facade.

Add:

- focused API audit;
- focused axiom audit;
- R49 scratch/client.

Update:

- `report-055.md`;
- `ROADMAP.md`.

## Hard stops

- No claim that either branch is impossible.
- No claim that `t` is generated by alpha / 1+alpha.
- No explicit fundamental-unit basis.
- No Thue completeness theorem.
- No `q % 28 = 1` theorem without a separately checked Galois residue
  transport.
- No reciprocity law.
- No new Hensel depth.
- No successor/descent construction.
- No FLT7 conclusion.
- No `sorry`, `sorryAx`, `admit`, `unsafe`, or project `axiom`.

## Validation

Run sequentially:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSharpenedBranch
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicSharpenedBranchApi
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicSharpenedBranchAxiom
lake env lean DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicSharpenedBranchR49Scratch.lean
git diff --check
```

Print axioms for:

- the C=1 nontrivial `7^9)-correction theorem;
- the C>1 sharpened support theorem;
- the final dichotomy theorem;
- optional non-torsion theorem if promoted.

Expected project-level axioms:

```text
[propext, Classical.choice, Quot.sound]
```

## Report questions

1. Was the C=1 branch constructed entirely from existing public R39–R47 APIs?
2. Was `t^(7^9) != 1` derived directly from R47 calibration exclusion?
3. Was `norm t = 1` obtained cheaply?
4. Was the transported unit proved non-torsion without an explicit
   fundamental-unit basis?
5. Does the C>1 wrapper give both `29 <= C` and prime support `1 mod 7`?
6. Is the final dichotomy provenance-preserving?
7. Was the optional `29*u^5 < v` height bound cheap enough to include?
8. Were character/mod-28 claims intentionally deferred?
9. Are facade/API/axiom/client checks green?

## Outcomes

- Outcome A — sharpened dichotomy is green, C=1 correction is nontrivial
  norm-one and non-torsion, and C>1 gets the strengthened height bound.
- Outcome B — mandatory sharpened dichotomy is green; one or more optional
  norm/torsion/height refinements are deferred.
- Outcome C — C=1 high-power nontrivial correction is green but the final
  dichotomy packaging is the remaining frontier.
- Outcome D — an unexpected dependency mismatch prevents composition of the
  already checked R45/R47 endpoints; document the exact mismatch and stop.
