# Instruction-001 — Extract the pointwise calibration function and outer ABC balance

## Working branch

Work only on:

```text
repository: Deskuma/dkmath
branch: research/ABC-GN-balance-calibration-260915-v0
checkpoint base: 39022f480db874c91432f4c114bb7e1c3661fa5b
```

Checkpoint 000 is accepted as Outcome A.

Read first:

```text
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/README.md
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/report-000.md
DkMath/ABC/GNBalanceCalibration.lean
DkMath/ABC/ABCEpsilonIdentity.lean
DkMath/ABC/ABCEpsilonSlopeBridge.lean
```

This checkpoint is still structure-first.

**Do not improve an exponent, prove a uniform calibration bound, or construct a new ABC contract.**

The purpose is to remove the arbitrary allowance `C` from the pointwise view and expose the actual calibration correction required by one triple, while also placing the outer ABC balance into the same mass/balance coordinate language.

---

## 0. Repository-first audit

Before coding, confirm the exact current declarations:

```lean
GNChannelSupportMass
GNChannelDepthMass
GNChannelMass
GNChannelBalance
GNCalibrationResidual
GNNonExceptionalChannelMassBudgetAffine_iff_calibrationResidual_le
Triple.oddPrimeJointPressure_iff_calibrationResidual_le
Triple.abcEpsilon_le_GNEpsilon_add_correction_of_calibrationResidual_le

Triple.abcGap_eq_valuationExcess_sub_log_rad_ab
Triple.abcGap_eq_abcEpsilon_mul_radLog
Triple.abcEpsilon_eq_valuationExcess_sub_log_rad_ab_div_log_rad_abc
Triple.quality_eq_one_add_abcEpsilon
GNEpsilon
Triple.abcEpsilon_le_GNEpsilon_add_correction
```

Record any declaration mismatch in:

```text
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/report-001.md
```

---

## 1. Pointwise calibration correction

Checkpoint 000 exposed

```text
Cal(T,p,ρ) := GNChannelMass(T,p) - ρ * radLog(T).
```

The current epsilon bridge still consumes an arbitrary upper allowance `C`:

```text
Cal(T,p,ρ) <= C
```

and then returns the correction

```text
(C + log(rad p)) / ((p - 1) * radLog(T)).
```

For a single triple, the least algebraically available choice in the existing theorem is the pointwise residual itself.

Define an explicit pointwise correction coordinate, preferably in a new bridge module or in the thinnest existing balance module consistent with the import graph:

```lean
noncomputable def GNPointwiseCalibrationCorrection
    (T : Triple) (p : ℕ) (ρ : ℝ) : ℝ :=
  (GNCalibrationResidual T p ρ + Real.log (rad p : ℝ)) /
    (((p - 1 : ℕ) : ℝ) * T.radLog)
```

The name may be adjusted only for strong repository naming reasons.

This definition is not claimed minimal among all possible proofs. It is the pointwise correction obtained by substituting the actual residual into the already-proved production bridge.

---

## 2. Direct pointwise epsilon consumer

Prove a theorem of the form:

```lean
theorem Triple.abcEpsilon_le_GNEpsilon_add_pointwiseCalibrationCorrection
    (T : Triple) {p : ℕ} {ρ : ℝ}
    (hp : Nat.Prime p)
    (hpOdd : Odd p)
    (ha : 0 < T.a)
    (hb : 0 < T.b) :
    T.abcEpsilon ≤
      GNEpsilon p ρ + GNPointwiseCalibrationCorrection T p ρ := by
  ...
```

Prefer proving this by reusing

```lean
Triple.abcEpsilon_le_GNEpsilon_add_correction_of_calibrationResidual_le
```

with

```text
C := GNCalibrationResidual T p ρ
```

and `le_rfl`, then simplifying the correction definition.

Do not duplicate the long epsilon proof.

This theorem is the primary consumer showing that `GNCalibrationResidual` is not a decorative rename: it directly determines a pointwise calibration correction.

---

## 3. Uniform allowance as an envelope of pointwise correction

If clean with the existing positivity facts, prove the monotone envelope theorem:

```text
GNCalibrationResidual T p ρ <= C
```

implies

```text
GNPointwiseCalibrationCorrection T p ρ
  <=
(C + log(rad p)) / ((p - 1) * radLog(T)).
```

Expected assumptions may include:

```lean
hp : Nat.Prime p
ha : 0 < T.a
hb : 0 < T.b
```

Use them only to prove positivity of the denominator.

This theorem should make the semantics precise:

```text
pointwise correction
    <=
uniform correction determined by C.
```

Do not introduce a supremum over all triples.

---

## 4. Outer ABC balance coordinates

Production already has the exact outer imbalance

```text
abcGap(T)
  = valuationExcess(T.c)
    - log(rad(T.a*T.b)).
```

Expose the two outer components as coordinate aliases:

```text
input support mass  A(T) := log(rad(T.a*T.b))
output depth mass   D(T) := valuationExcess(T.c)
outer mass          M₀(T) := A(T) + D(T)
outer balance       Q₀(T) := D(T) - A(T)
```

Suggested names:

```lean
ABCInputSupportMass
ABCOutputDepthMass
ABCOuterMass
ABCOuterBalance
```

The sign convention for `ABCOuterBalance` should follow the existing `abcGap`, so positive balance means output valuation depth exceeds input support.

Prove the exact reconstruction identities:

```text
D = (M₀ + Q₀) / 2
A = (M₀ - Q₀) / 2
```

and the exact bridge:

```lean
theorem Triple.ABCOuterBalance_eq_abcGap ...
```

under the same positivity assumptions required by the existing production theorem.

Also expose, by reusing production theorems rather than reproving logarithmic arithmetic:

```text
ABCOuterBalance = abcEpsilon * radLog
```

under positive inputs.

A zero-contour equivalence such as

```text
ABCOuterBalance = 0 ↔ abcGap = 0
```

is acceptable because it is purely definitional/exact. Do not claim that this contour is dynamically preferred or sufficient for ABC.

---

## 5. Keep inner and outer balances conceptually distinct

Checkpoint 000 uses

```text
GNChannelBalance = support - depth.
```

This checkpoint proposes

```text
ABCOuterBalance = depth - support
```

because the latter is required to agree with the pre-existing signed `abcGap` convention.

Do not silently identify these coordinates or state a transport relation between them.

Record this sign-orientation difference explicitly in `report-001.md`.

A later checkpoint may decide whether a common generic `PowerSwap` orientation is useful.

---

## 6. Preferred module structure

Prefer keeping checkpoint-000 GN coordinates stable.

A clean option is:

```text
DkMath/ABC/ABCBalanceCalibrationBridge.lean
```

with an import of:

```lean
DkMath.ABC.GNBalanceCalibration
```

and with the outer ABC balance definitions plus pointwise calibration correction/consumer in the bridge layer.

If a thinner or more repository-consistent placement exists, use it and document the reason.

Do not refactor old production files merely to relocate definitions.

After the focused build passes, export the new module through `DkMath.ABC` once.

---

## 7. Validation

Run at least:

```text
lake env lean DkMath/ABC/ABCBalanceCalibrationBridge.lean
lake build DkMath.ABC.ABCBalanceCalibrationBridge
lake build DkMath.ABC
```

or repository-equivalent commands if a different module path is selected.

Also run:

```text
git diff --check
```

and the standard forbidden-pattern scan for:

```text
sorry
admit
axiom
unsafe
```

Audit `#print axioms` for the primary pointwise epsilon consumer theorem.

Write all results to:

```text
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/report-001.md
```

---

## 8. Outcome classification

Use one of:

```text
Outcome A — POINTWISE CALIBRATION / OUTER BALANCE API COMPLETE
Outcome B — PARTIAL EXTRACTION / SIGN OR DEPENDENCY BOUNDARY FOUND
Outcome C — EXISTING API ALREADY SUFFICIENT / NO NEW PRODUCTION SURFACE JUSTIFIED
```

Outcome A requires at minimum:

```text
GNPointwiseCalibrationCorrection
pointwise epsilon consumer from the actual residual
outer ABC support/depth mass coordinates
outer mass/balance reconstruction identities
ABCOuterBalance = abcGap
focused build success
```

The uniform-envelope theorem is desirable but not mandatory if it creates avoidable proof noise.

---

## 9. Hard boundary for checkpoint 001

Do not attempt:

```text
supremum of GNCalibrationResidual over all triples
uniform residual bound
new ABCGNOddPrimeJointContract construction
better rho / epsilon
new K-epsilon estimate
shell-count or squarefull estimates
Hensel transport of GNChannelBalance
relation between GNChannelBalance and ABCOuterBalance
claim that either zero contour is optimal
```

The purpose is to expose the **actual pointwise calibration function** before studying where its residual comes from.

Checkpoint 002 will audit the proof chain to locate every source of inequality/slack inside that calibration function.
