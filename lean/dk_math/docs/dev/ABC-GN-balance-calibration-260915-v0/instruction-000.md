# Instruction-000 — Extract the ABC/GN balance and calibration coordinates

## Working branch

Work only on:

```text
repository: Deskuma/dkmath
branch: research/ABC-GN-balance-calibration-260915-v0
base develop commit: 5bba76f07a966e23eba7d0fbf7c70f1133d7e90e
```

Read first:

```text
README.md
AGENT.md
SUMMARY.md
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/README.md
```

This checkpoint is deliberately thin.

**Do not try to improve any exponent, shell count, square-full estimate, or ABC constant.**

The task is to extract exact coordinate definitions and theorem aliases from the existing production ABC/GN accounting.

---

## 0. Repository-first audit

Before editing production code, locate and record the exact declarations and source files for at least:

```lean
Triple.abcGap_eq_valuationExcess_sub_log_rad_ab
Triple.abcGap_eq_abcEpsilon_mul_radLog
Triple.abcEpsilon_eq_valuationExcess_sub_log_rad_ab_div_log_rad_abc
Triple.quality_eq_one_add_abcEpsilon

GNNonExceptionalSupportProduct
GNNonExceptionalValuationExcess
GNNonExceptionalChannelMassBudgetAffine

Triple.log_GN_eq_log_exceptional_add_log_nonExceptional_add_excess
Triple.log_rad_gnPowerLift_eq_log_rad_add_log_nonExceptionalSupport_of_prime
Triple.oddPrimeJointPressure_iff_nonExceptionalChannelMass
Triple.log_c_mul_pred_le_of_oddPrime_jointPressure

GNEpsilon
GNEpsilon_le_iff_margin
Triple.abcEpsilon_le_GNEpsilon_add_correction

GNABCConstant
ABCGNOddPrimeJointContract
abc_positive_of_GNOddPrimeJointContract
abc_of_GNOddPrimeJointContract
```

Also inspect the actual import direction among:

```text
ABCEpsilonIdentity
GNJointPressureOddPrime
ABCEpsilonSlopeBridge
```

Do not introduce an import cycle.

Create and maintain:

```text
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/report-000.md
```

The report must list exact theorem names, files, imports, and any mismatch between this instruction and current production names.

---

## 1. New module

Preferred file:

```text
DkMath/ABC/GNBalanceCalibration.lean
```

Choose the thinnest production import that exposes the required GN joint-pressure quantities. If importing `ABCEpsilonSlopeBridge` would create an undesirable dependency direction, keep checkpoint 000 below that layer and defer the epsilon consumer theorem to checkpoint 001.

Namespace:

```lean
namespace DkMath.ABC
```

Use `noncomputable` only where existing real logarithmic quantities require it.

---

## 2. Required coordinate definitions

Implement explicit names for the two GN channel components and their sum/difference coordinates.

The intended mathematical meanings are:

```text
support mass S(T,p)
  := log(GNNonExceptionalSupportProduct p T.a T.b)

depth mass E(T,p)
  := GNNonExceptionalValuationExcess p T.a T.b

channel mass M(T,p)
  := S(T,p) + E(T,p)

channel balance Q(T,p)
  := S(T,p) - E(T,p)
```

Suggested names; adjust only if repository naming conventions strongly favor another spelling:

```lean
GNChannelSupportMass
GNChannelDepthMass
GNChannelMass
GNChannelBalance
```

These are coordinate aliases, not new arithmetic claims.

Do not redefine the underlying support product or valuation excess.

---

## 3. Exact reconstruction identities

Prove the coordinate reconstruction identities over `ℝ`:

```text
S = (M + Q) / 2
E = (M - Q) / 2
```

Suggested theorem shapes:

```lean
theorem GNChannelSupportMass_eq_half_mass_add_balance ...
theorem GNChannelDepthMass_eq_half_mass_sub_balance ...
```

These should be algebraic proofs (`ring`, `linarith`, or similarly transparent tactics).

Also provide direct simp/rewrite theorems if the definitions do not unfold cleanly enough for consumers.

Do **not** prove or state:

```text
Q = 0
Q >= 0
Q <= 0
```

for arbitrary triples. The zero contour is a coordinate landmark, not an established global theorem.

---

## 4. Calibration residual

Define the signed pointwise residual at slope `ρ`:

```text
Cal(T,p,ρ) := M(T,p) - ρ * T.radLog
```

Suggested name:

```lean
GNCalibrationResidual
```

This is pointwise. It is **not** the uniform contract constant `C`.

Prove the exact budget equivalence:

```text
GNNonExceptionalChannelMassBudgetAffine T p ρ C
iff
GNCalibrationResidual T p ρ <= C
```

Suggested theorem:

```lean
GNNonExceptionalChannelMassBudgetAffine_iff_calibrationResidual_le
```

The proof should be definitional/algebraic. No prime hypothesis should be introduced unless required by an existing definition (it should not be needed for this equivalence).

---

## 5. Existing joint pressure transported to residual form

Using the existing theorem

```lean
Triple.oddPrimeJointPressure_iff_nonExceptionalChannelMass
```

prove a consumer theorem of the form:

```lean
theorem Triple.oddPrimeJointPressure_iff_calibrationResidual_le
    (T : Triple) {p : ℕ} {ρ C : ℝ}
    (hp : Nat.Prime p)
    (ha : 0 < T.a) (hb : 0 < T.b) :
    GNOddPrimeJointPressureBudgetAffine T p ρ C ↔
      GNCalibrationResidual T p ρ ≤ C := by
  ...
```

Prefer composition of existing equivalences over re-proving the long GN accounting chain.

This theorem is the load-bearing result of checkpoint 000.

---

## 6. Optional epsilon bridge — only if dependency direction is clean

If and only if the import graph remains clean, expose the existing epsilon correction in calibration language.

The production theorem already proves, under odd-prime joint pressure,

```text
abcEpsilon(T)
  <= GNEpsilon(p,ρ)
     + (C + log(rad p)) / ((p-1) * radLog(T)).
```

Checkpoint 000 may add a theorem whose assumption is directly

```text
GNCalibrationResidual T p ρ <= C
```

and whose conclusion is the same existing bound, by transporting the residual bound back through the equivalence and calling

```lean
Triple.abcEpsilon_le_GNEpsilon_add_correction
```

Do not duplicate its arithmetic proof.

If this would force an import cycle, defer the theorem and record the exact reason in `report-000.md`.

---

## 7. Public surface and imports

Do not automatically add the module to a top-level aggregator before the focused build passes.

After the module is stable:

1. identify the nearest appropriate aggregator (`DkMath.ABC` or another existing ABC facade),
2. add one import only if consistent with current architecture,
3. ensure no unrelated module acquires a reverse dependency.

Do not refactor old files in this checkpoint unless required to break an actual import cycle.

---

## 8. Validation

Run at least:

```text
lake env lean DkMath/ABC/GNBalanceCalibration.lean
```

or the repository-equivalent focused build command, plus the relevant ABC facade build if the import is exported.

Run forbidden-pattern checks according to repository policy. In particular report whether the new module contains any of:

```text
sorry
admit
axiom
unsafe
```

Do not modify or remove legacy ABC axioms elsewhere as part of this checkpoint.

Record `#print axioms` for the load-bearing theorem if that is standard in the current ABC audit workflow.

---

## 9. Outcome classification

Use one of:

```text
Outcome A — EXACT BALANCE/CALIBRATION API COMPLETE
Outcome B — PARTIAL EXTRACTION / DEPENDENCY BOUNDARY FOUND
Outcome C — EXISTING API ALREADY SUFFICIENT / NO NEW PRODUCTION MODULE JUSTIFIED
```

Outcome A requires at minimum:

```text
GNChannelMass
GNChannelBalance
GNCalibrationResidual
support/depth reconstruction identities
channel-budget iff residual <= C
odd-prime joint-pressure iff residual <= C
focused build success
```

---

## 10. Hard boundary for checkpoint 000

Do not attempt any of the following yet:

```text
uniform bound on GNCalibrationResidual
supremum over all ABC triples
new construction of ABCGNOddPrimeJointContract
new Kε estimate
new shell-count exponent
new square-full count theorem
claim that GNChannelBalance = 0 is optimal
claim monotonicity of the balance coordinate
Hensel/shell transport theorem for the balance coordinate
```

Those are later research questions.

The purpose of checkpoint 000 is to make the existing hidden scale geometry explicit without changing the mathematical strength of the library.
