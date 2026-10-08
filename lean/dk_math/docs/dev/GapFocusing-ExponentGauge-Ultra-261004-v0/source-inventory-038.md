# Instruction 038 source inventory

Added production: DkMath/NumberTheory/Legendre/GnomonCentralCarryCompensation.lean. Ten public declarations: four definitions and six theorems. One private log-product helper.
Modified facade: DkMath/NumberTheory/Legendre.lean. One import added.
Added calibration: DkMathTest/NumberTheory/GnomonCentralCarryCompensationCalibration.lean. Nine regression theorems, including a formal obstruction to a dominating injection at 27.
Added axiom audit: DkMathTest/NumberTheory/GnomonCentralCarryCompensationAxiomAudit.lean. All ten public production declarations.

Audited unchanged sources: DivisorIncidence factorial/floor identities, GnomonDivisorCarry binary carry and exact small events, BinomialPrimePower Kummer valuation receivers, Mathlib Data.Nat.Choose.Factorization and Choose.Basic, and the retained 036/037 correction and calibration APIs. The production imports the 037 facade module and reuses its transitive arithmetic dependencies. No arbitrary-binomial carry framework or new exclusion radius is added.

The central logarithm bridge, exact common cancellation and positive product equivalence are formalized. They are reported as exact infrastructure, not a proof of universal compensation or a new independent correction estimate. Existing 029-037 modules and correction budgets remain unchanged.
