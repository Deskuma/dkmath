# Instruction 039 source inventory

Added production: DkMath/NumberTheory/Legendre/GnomonPooledThresholdAudit.lean. Two definitions and four theorems, all public.
Modified facade: DkMath/NumberTheory/Legendre.lean. One import added.
Added calibration: DkMathTest/NumberTheory/GnomonPooledThresholdCalibration.lean. Eight regressions preserving the 038 examples and the new high/low threshold split.
Added axiom audit: DkMathTest/NumberTheory/GnomonPooledThresholdAxiomAudit.lean. All six public production declarations.

Audited unchanged APIs: 038 positive residual-product bridge and calibration, prime-power least-factor lower bound, Finset.prod_filter_mul_prod_filter_not and finite filtering. List sorting/prefix APIs were inspected as search candidates, but no second block principle was implemented. The coherent principle actually tested is thresholded cumulative prime-base products, with exact multiplicity retained.

The new production theorem refutes that threshold-capacity principle at 27. Its sufficient receiver is explicitly conditional; it is not reported as a new central-binomial upper bound. Existing 029-038 singleton machinery and correction budgets are unchanged.
