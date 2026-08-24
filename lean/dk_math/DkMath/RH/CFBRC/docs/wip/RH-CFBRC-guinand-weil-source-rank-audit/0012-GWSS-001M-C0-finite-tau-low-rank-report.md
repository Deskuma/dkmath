Global objective:
zero configuration -> independent source -> off-critical detector -> arithmetic control -> centered-coordinate uniqueness -> RiemannHypothesis
Current GWSS stage: GWSS-001M-C0
Load-bearing boundary: finite nonzero-τ evaluation separation is proved for the bare kernel and transferred exactly through the fixed spectral factors; no limit exchange, positivity, sign control, or RH conclusion is used.
Next unresolved Gap: GENERAL-FINITE-ORBIT-MELLIN-RANK-GAP

## C0-A 2-orbit bare-kernel result

`bareTwoOrbitEvaluationDeterminant` evaluates the kernel at exactly `t` and
`2t`.  Its quotient by `(t : ℂ)^2` tends to `3 * D₂`, where
`D₂ = q₁ * (q₂^2 / 12) - q₂ * (q₁^2 / 12)`.  Nonzero distinct squared
coordinates therefore give eventual nonvanishing of the unnormalized
determinant on the punctured neighborhood of `0`.

## C0-B 3-orbit bare-kernel result

`bareThreeOrbitEvaluationDeterminant` uses exactly `t`, `2t`, and `3t`.
Its quotient by `(t : ℂ)^6` tends to `120 * D₃`, with the explicit
`q, q^2/12, q^3/360` determinant expression.  The existing three-orbit jet
nonvanishing theorem gives eventual nonvanishing of the unnormalized finite
determinant for pairwise distinct nonzero squared coordinates.

## C0-C spectral-factor scaling result

The module defines the actual two- and three-orbit Mellin determinants and
proves exact identities multiplying the bare determinants by
`Sε(z₁) * Sε(z₂)` and `Sε(z₁) * Sε(z₂) * Sε(z₃)`, respectively.  The factor
is retained as an exact fixed-`ε` column scaling; it is not replaced by `1`.

## C0-D actual-window result

Using `eventually_pascalCenteredXiMellinSpectralWeight_ne_zero_on_actual_window`
and `pascalCenteredXiZeroDiskFinset_sq_ne_zero`, the module proves nested
eventual nonvanishing statements: first positive `ε` in
`nhdsWithin 0 (Ioi 0)`, then punctured finite `t` in
`nhdsWithin 0 ({0}ᶜ)`, for actual Xi-window points with distinct squared
coordinates.

## primary classification

`FINITE-TAU-LOW-RANK-SEPARATION-FOUND`

This classification is limited to ranks 2 and 3 and to the stated finite
parameter choices.  It does not establish full rank for an arbitrary finite
window.

## GWSS-002 authorization status

Not authorized.  The next gap is the general finite-orbit rank problem;
GWSS-001M-C1/C2 and GWSS-002/GWSS-003 remain outside this bounded assignment.

## Verification

- `lake build DkMath.RH.CFBRC.PascalCenteredXiMellinFiniteTauLowRankAudit`
  succeeds under `leanprover/lean4:v4.32.2`.
- `git diff --check` is required as the final working-tree check.
- No `sorry`, `admit`, or newly introduced axiom is used.
- The load-bearing normalized-limit, eventual-nonzero, exact scaling, and
  actual-window theorems are ordinary Lean theorems; the module imports only
  the previously established Mellin jet and actual-window APIs.
