# FLT7TC-005R40 — Weighted cyclic trace and the first mod-49 seventh-power jet

## Scope

This report records the R40 implementation and verification. The checkpoint
starts from the R39 `C = 1` scalarization and targets only weighted cyclic
trace normalization, the neutral mod-49 seventh-power theta jet, the first
linear-coordinate restriction, and the resulting binary cubic frontier. It
does not claim a successor, descent, or FLT7 closure.

## Initial investigation

- `PrimeTraceOneDirectRealCubicSuccessorAudit.lean` supplies the cyclic axis
  transport and the exact weights `32 + 42*k`.
- `PrimeTraceOneDirectRealCubicSquareTwistObstruction.lean` supplies the
  square-twisted coefficients, their projective classes, and the signed norm
  of coefficient zero.
- `SevenRealCubicThetaCoordinates.lean` supplies the integral theta basis and
  coordinate decomposition.
- `SevenRealCubicThetaSeventhPower.lean` supplies the exact linear and square
  seventh-power quotient formulas and their mod-seven factors.
- `SevenRealCubicAxisDrop.lean` supplies `7 = theta^3 * thetaSevenUnit`.

The implementation and validation log will be appended below as each R40
part is kernel-checked.

## Implementation

The focused production module now contains:

- `directOrbitCyclicTrace` as a neutral model-ring cyclic trace;
- the R40 root/X/W unit definitions and the exact exponent identity
  `32 + 42*k = 3*(10 + 14*k) + 2`;
- an explicit equality of `X` with the R39 square-twist coefficient zero
  multiplied by `eta^14`;
- the weighted three-term equation, its literal cyclic-trace form, and the
  ramified-axis normalization target;
- the exact arbitrary-coordinate trace formula
  `7 * (3*A - 10*B + 35*C)` and the corresponding integral trace-plane
  theorem;
- the calibrated unit `rho = -alphaUnit^3`, including its theta coordinates,
  norm, projective class `(1,1)`, and trace-zero check.

The new neutral module
`SevenRealCubicThetaSeventhPowerMod49.lean` now exports the two
packet-independent
mod-49 consequences obtained from the existing exact quotient formulas:

```text
49 | thetaLinearInt (x^7) - 7*B*A^6
49 | thetaSquareInt (x^7) - 7*(C*A^6 + 3*B^2*A^5).
```

The scratch file records both local derivations and checks the public neutral
statements. The direct constant-coordinate mod-49 expansion was tested as a
scratch direction but removed because its unrestricted coordinate expansion
did not finish within the available single-process check; no unproved claim
was retained.

The public facade import and focused API/axiom audit files were added for the
new production surface.

## Boundary

The current implementation stops before the requested Parts D, F global
seventh-power correction, G constant-coordinate jet, H transport to
`thetaLinearModSeven v = 0`, and I Thue normal form. In particular, the
existing checked data do not yet supply a completed current-provenance proof
of `norm W = 1` and `projectiveLog W = (1,1)` for the newly normalized `W`.
The explicit `rho` calibration confirms that trace zero, norm one, and class
`(1,1)` are mutually consistent; no contradiction is claimed.

## Validation log

- The exact coordinate formula was reproduced in the R40 scratch file before
  being placed in production.
- The linear and square mod-49 proofs were derived from the existing exact
  seventh-power quotient formulas and mod-seven factor theorems; the same
  proofs were added to the neutral module.
- The focused production module builds successfully:
  `DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicTrivialCommonFactorDeepJet`.
- The public facade builds successfully:
  `DkMath.FLT.Seven`.
- The focused API surface builds successfully:
  `DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorDeepJetApi`.
- The focused axiom audit builds successfully. Its output records only the
  existing foundational axioms (`propext`, `Classical.choice`, and
  `Quot.sound`) in the inspected theorem dependencies.
- The reusable scratch verification builds successfully:
  `DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorDeepJetR40Scratch`.
- The source scan over the R40 production, neutral, API, and scratch files
  found no `sorry`, `axiom`, or `unsafe` occurrences; the audit file contains
  only the intentional `#print axioms` commands. `git diff --check` and the
  new-report check also completed without diagnostics, and the original
  `SevenRealCubicThetaSeventhPower.lean` has no diff.

Outcome: **Outcome E/C boundary** — the weighted cyclic-trace and exact
trace-plane layer is implemented, while the current-provenance norm/class
normalization and constant-coordinate mod-49 transport remain the precise
frontier.
