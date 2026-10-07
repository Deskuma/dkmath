# Instruction 037 source inventory

Added DkMath/NumberTheory/Legendre/GnomonSmallCarryPhase.lean: ten public declarations (four definitions and six theorems), two private finite prefix helpers.
Modified DkMath/NumberTheory/Legendre.lean: one added import.
Added DkMathTest/NumberTheory/GnomonSmallCarryPhaseCalibration.lean: five regression theorems, including a finite central-binomial proof at 27.
Added DkMathTest/NumberTheory/GnomonSmallCarryPhaseAxiomAudit.lean: all ten public production declarations.

Audited unchanged sources: GnomonDivisorCarry remainder/floor carry APIs, GnomonNonSingletonCorrection prefix compression, SquareShellPrimePowerGauge reciprocal bound, BinomialPrimePower prime-power/Kummer receivers, PascalPrebirthBoundary, and Mathlib Data.Nat.Choose.Factorization. The coefficient factorization API counts central carry coordinates but does not provide the required weighted domination. No existing 029-036 source module or singleton carrier was changed.

The private nonprime-prefix identity mirrors the finite identity hidden in the 036 private helper; no new correction estimate is claimed for that identity. The new mathematical steps are the restricted zero-phase exclusion, independent band localization, and subtraction from the previous correction envelope.
