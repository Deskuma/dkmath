# Instruction-002 — Decompose the calibration correction into exact return and gauge slack

## Working branch

Work only on:

```text
repository: Deskuma/dkmath
branch: research/ABC-GN-balance-calibration-260915-v0
checkpoint base: 748adca6ee93715ecf5d30c90ed2352f7e0d23c2
```

Checkpoints 000 and 001 are accepted as Outcome A.

Read first:

```text
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/README.md
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/report-000.md
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/report-001.md
DkMath/ABC/GNBalanceCalibration.lean
DkMath/ABC/ABCBalanceCalibrationBridge.lean
DkMath/ABC/GNJointPressureOddPrime.lean
DkMath/ABC/GNSupportReturn.lean
DkMath/ABC/GNQualityExcessBridge.lean
DkMath/ABC/GNPowerLift.lean
```

This checkpoint is still structure-first.

**Do not improve an exponent, prove a uniform residual bound, construct a new ABC contract, or estimate a supremum.**

The purpose is to open the pointwise calibration correction and identify exactly which parts are structural identities and which parts are nonnegative proof-envelope slack.

---

## 0. Repository-first proof-chain audit

Before coding, inspect the exact proof of

```lean
Triple.log_c_mul_pred_le_of_oddPrime_jointPressure
```

and record every equality and inequality used in it.

The current proof introduces conceptually:

```text
R := log(rad(a*b*c))
L := log(rad(gnPowerLift product))
S := log(GNNonExceptionalSupportProduct p a b)
E := GNNonExceptionalValuationExcess p a b
Qrad := log(rad(GN p a b))
G := log(GN p a b)
H := log c
P := log(rad p)
X := log(GNExceptionalSupportProduct p a b)
```

The audit should verify the following current facts and distinguish equality from inequality:

```text
G = Qrad + E                           exact at odd prime
G = X + S + E                          exact at odd prime
L = R + S                              exact for prime exponent
(p-1) * H <= G                         return inequality
X <= P                                 exceptional gauge inequality
```

The old height proof also uses an inequality of shape

```text
R + S <= L
```

through an older generic theorem. For prime exponents, production already has the stronger exact theorem

```lean
Triple.log_rad_gnPowerLift_eq_log_rad_add_log_nonExceptionalSupport_of_prime
```

so **do not introduce a new transport slack for this step**. Record that the apparent lift-radical slack is zero on the prime-exponent route.

Write the audit and all theorem-name/source information to:

```text
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/report-002.md
```

---

## 1. Return slack

The current deterministic return theorem is

```text
(p-1) * log c <= log GN.
```

Expose the signed pointwise difference as a coordinate alias.

Preferred definition:

```lean
noncomputable def GNReturnSlack
    (T : Triple) (p : ℕ) : ℝ :=
  Real.log ((GN p T.a T.b : ℕ) : ℝ) -
    ((p - 1 : ℕ) : ℝ) * Real.log (T.c : ℝ)
```

Prove nonnegativity under the existing hypotheses needed by

```lean
Triple.log_c_mul_pred_le_log_GN
```

For the prime-exponent consumer it is acceptable to state:

```lean
0 <= GNReturnSlack T p
```

under

```text
hp : Nat.Prime p
ha : 0 < T.a
hb : 0 < T.b
```

by reusing the existing return theorem. Do not re-prove `pow_pred_c_le_GN`.

Interpretation for the report only:

```text
GNReturnSlack = how much larger log GN is than the mandatory (p-1) log c return floor.
```

Do not claim it is uniformly bounded, monotone, or normally small.

---

## 2. Exceptional gauge slack

At prime exponent `p`, the exceptional GN support product is absorbed into `rad p`, but production does not generally identify it with `rad p`.

Expose the difference:

```lean
noncomputable def GNExceptionalGaugeSlack
    (T : Triple) (p : ℕ) : ℝ :=
  Real.log (rad p : ℝ) -
    Real.log (GNExceptionalSupportProduct p T.a T.b : ℝ)
```

Prove

```text
0 <= GNExceptionalGaugeSlack T p
```

from the existing theorem

```lean
log_GNExceptionalSupportProduct_le_log_rad
```

using only the hypotheses genuinely required.

Interpretation:

```text
GNExceptionalGaugeSlack
  = finite exponent-gauge allowance introduced when exact exceptional support X
    is replaced by the coarser fixed quantity log(rad p).
```

Do not claim it is always positive. It may vanish.

---

## 3. Exact pointwise correction before the safe envelope

Checkpoint 001 defined

```text
GNPointwiseCalibrationCorrection
  = (Cal + P) / (d*R)
```

where conceptually

```text
Cal := GNCalibrationResidual T p rho
d   := p - 1
R   := T.radLog
P   := log(rad p).
```

This is a **safe pointwise envelope** inherited from the existing epsilon theorem. It is not yet the exact correction forced by the exact odd-prime accounting.

Define an exact correction coordinate using the actual exceptional support and the return slack.

Preferred shape:

```lean
noncomputable def GNExactCalibrationCorrection
    (T : Triple) (p : ℕ) (rho : ℝ) : ℝ :=
  (GNCalibrationResidual T p rho +
      Real.log (GNExceptionalSupportProduct p T.a T.b : ℝ) -
      GNReturnSlack T p) /
    (((p - 1 : ℕ) : ℝ) * T.radLog)
```

The name may be adjusted if repository naming strongly favors another spelling, but the distinction between the **exact correction** and the existing **safe pointwise envelope** must remain explicit.

Do not call this globally minimal or optimal. It is exact relative to the already-formalized odd-prime identities and chosen slope `rho`.

---

## 4. Load-bearing exact epsilon identity

Using existing production identities only, prove an equality of the form:

```lean
theorem Triple.abcEpsilon_eq_GNEpsilon_add_exactCalibrationCorrection
    (T : Triple) {p : ℕ} {rho : ℝ}
    (hp : Nat.Prime p)
    (hpOdd : Odd p)
    (ha : 0 < T.a)
    (hb : 0 < T.b) :
    T.abcEpsilon =
      GNEpsilon p rho + GNExactCalibrationCorrection T p rho := by
  ...
```

Conceptual algebra to verify, not blindly copy:

```text
G = X + S + E
M = S + E
Cal = M - rho*R
ReturnSlack = G - d*H

therefore

d*H = X + rho*R + Cal - ReturnSlack.
```

Together with the exact outer identity

```text
abcEpsilon = log(c)/R - 1
```

for positive triples, this should yield the equality.

Prefer deriving the needed `abcEpsilon = log(c)/radLog - 1` identity from existing production definitions/theorems in a small transparent lemma if no exact named theorem already exists. Do not duplicate large ABC or GN proofs.

If the equality cannot be proved without an additional arithmetic hypothesis not already present, stop and report Outcome B rather than weakening it silently.

This theorem is the load-bearing target of checkpoint 002.

---

## 5. Exact decomposition of the checkpoint-001 envelope

Prove that the existing safe pointwise correction is exactly the new exact correction plus the two normalized nonnegative slacks.

Target shape:

```text
GNPointwiseCalibrationCorrection T p rho
  = GNExactCalibrationCorrection T p rho
    + (GNReturnSlack T p + GNExceptionalGaugeSlack T p)
        / (((p-1 : Nat) : Real) * T.radLog)
```

under whatever positivity hypotheses are needed only for denominator-sensitive rearrangement; algebraically the equality may need no positivity assumptions after unfolding.

This identity should explain precisely why checkpoint 001 had an inequality consumer:

```text
exact correction
  + return slack
  + exceptional gauge slack
  = safe pointwise correction.
```

Then, if clean, derive the monotone corollary

```text
GNExactCalibrationCorrection T p rho
  <= GNPointwiseCalibrationCorrection T p rho
```

for odd prime `p` and positive triple inputs, using nonnegativity of the two slacks and positivity of the denominator.

Do not make this corollary the main theorem; the exact decomposition is more important.

---

## 6. What is *not* a calibration source here

Checkpoint 002 must explicitly record the following in `report-002.md`:

1. `GNCalibrationResidual` itself is not proof slack; it is the signed pointwise mismatch between channel mass and the chosen slope line `rho*R`.
2. `GNChannelBalance = S-E` is not yet consumed by the current epsilon proof and is not part of this correction decomposition.
3. The prime-exponent lifted-radical transport has an exact identity `L = R + S`; do not count that step as a positive slack source.
4. `GNABCConstant` and any later `max 1`, absolute value, exponential packaging belong to a later outer safe-envelope layer and should not be mixed into this checkpoint.
5. No uniformization allowance `C` is needed for the exact pointwise identity. `C` appears only when replacing the actual pointwise residual by a common upper allowance over a family.

This classification is part of the mathematical result.

---

## 7. Preferred module structure

Prefer a new bridge/audit module rather than modifying the accepted checkpoint files heavily.

Suggested file:

```text
DkMath/ABC/ABCCalibrationSourceDecomposition.lean
```

Import only the thinnest layer needed, likely:

```lean
DkMath.ABC.ABCBalanceCalibrationBridge
```

plus another production module only if declarations are not transitively available.

Do not refactor `GNJointPressureOddPrime.lean`, `GNSupportReturn.lean`, or `GNQualityExcessBridge.lean` merely to rewrite their historical proofs.

After the focused build succeeds, export the new module through `DkMath.ABC` once.

---

## 8. Validation

Run at least:

```text
lake env lean DkMath/ABC/ABCCalibrationSourceDecomposition.lean
lake build DkMath.ABC.ABCCalibrationSourceDecomposition
lake build DkMath.ABC
git diff --check
```

Also run the standard forbidden-pattern scan for:

```text
sorry
admit
axiom
unsafe
```

Audit `#print axioms` for the load-bearing exact epsilon identity.

Write all results, exact theorem names, any dependency mismatch, and the equality/inequality source table to:

```text
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/report-002.md
```

---

## 9. Outcome classification

Use one of:

```text
Outcome A — EXACT CALIBRATION-SOURCE DECOMPOSITION COMPLETE
Outcome B — PARTIAL DECOMPOSITION / AN ADDITIONAL NON-EXACT STEP REMAINS
Outcome C — PROPOSED SLACK SPLIT IS NOT SUPPORTED BY CURRENT PRODUCTION IDENTITIES
```

Outcome A requires at minimum:

```text
GNReturnSlack
GNExceptionalGaugeSlack
nonnegativity of both under the appropriate hypotheses
GNExactCalibrationCorrection
abcEpsilon = GNEpsilon + exact correction
pointwise correction = exact correction + normalized(return slack + gauge slack)
focused build success
```

---

## 10. Hard boundary for checkpoint 002

Do not attempt:

```text
uniform bound on GNReturnSlack
uniform bound on GNExceptionalGaugeSlack
uniform bound on GNCalibrationResidual
supremum over triples
new ABCGNOddPrimeJointContract
better rho / epsilon
new K-epsilon estimate
shell-count or squarefull estimates
Hensel transport of GNChannelBalance
relation between GNChannelBalance and ABCOuterBalance
claim that any balance contour is optimal
```

The goal is narrower and more fundamental:

> identify exactly where the current pointwise calibration envelope is larger than the exact correction forced by the existing arithmetic identities.
