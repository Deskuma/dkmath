# Instruction 036 source inventory

Added production: DkMath/NumberTheory/Legendre/GnomonNonSingletonCorrection.lean. Two definitions, six public theorems and two private finite-sum helpers.
Modified facade: DkMath/NumberTheory/Legendre.lean. One added import.
Added calibration: DkMathTest/NumberTheory/GnomonNonSingletonCorrectionCalibration.lean. Four regression theorems.
Added axiom audit: DkMathTest/NumberTheory/GnomonNonSingletonCorrectionAxiomAudit.lean. All eight public production declarations.

Existing 026-035 source modules remain unchanged. Audited SquareShellPrimePowerGauge (odd-depth, reciprocal and log-log bounds), GnomonDivisorCarry (modular carry events and same-base geometry), GnomonCarryFiber (exponent cutoffs), GnomonCofactorWindow (repeated/singleton split), and GnomonCofactorAdaptiveRoughness (exact closure). Mathlib NumberTheory.Chebyshev and ArithmeticFunction.VonMangoldt were inspected and reused. No shell prime inventory is part of the new bound.

The focused, facade and root build scopes are broader than these changed sources. Build telemetry and complete logs are retained separately.
