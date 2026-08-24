Global objective:
zero configuration -> independent source -> off-critical detector -> arithmetic control -> centered-coordinate uniqueness -> RiemannHypothesis

Current GWSS stage:
GWSS-001M-C1L

Load-bearing boundary:
The direct function-rank result is proved for the zero-independent family
`τ ↦ mellinSymmetricNumerator τ z`.  No RH assumption, classical Weil
positivity, Li criterion, fixed-Xi defect provider, horizontal decay, unrelated
limit exchange, prime-side sign assumption, carrier-dependent selector, or
finite-evaluation existence claim is introduced.

## C1L-A all-jet-row extraction

FOUND.  The theorem
`mellinSymmetricNumerator_combination_nextJet_eq_zero` extracts the next even
jet row from an identically zero combination after the lower rows have been
removed.  Its proof uses the punctured-neighborhood limit
`tendsto_mellinSymmetricNumerator_generalJet`; the lower Taylor part is
annihilated by finite-sum rearrangement.  Strong induction then proves every
row below `n` vanishes.

## C1L-B matrix-kernel discharge

FOUND.  The theorem
`mellinSymmetricNumerator_combination_eq_zero_imp_coeff_zero` identifies the
row equations with
`mellinJetCoefficientMatrix (fun j => (z j)^2) *ᵥ c = 0`, using the existing
coefficient-matrix bridge.  The existing
`mellinJetCoefficientMatrix_det_ne_zero` theorem and
`Matrix.eq_zero_of_mulVec_eq_zero` then give `c = 0` pointwise.

## C1L-C optional wrapper

NOT ADDED.  The direct annihilation theorem already establishes the requested
function-level rank extensionally.  A separate `LinearIndependent` wrapper
would add only a finitely-supported scalar-convention layer and is not needed
for the primary classification.

## Primary classification

`GENERAL-MELLIN-NUMERATOR-FUNCTION-RANK-FOUND`

## Next unresolved Gap

`GENERAL-FINITE-MELLIN-EVALUATION-BRIDGE-GAP`

The function-rank result does not provide a finite set of actual nonzero
`τ`-values in the Xi window with an invertible evaluation matrix.

## GWSS-002 authorization status

Not authorized.  C1E finite evaluation, C2 actual-window transfer, and
GWSS-002/003/004 remain outside the bounded assignment.

## Verification

- `lake build DkMath.RH.CFBRC.PascalCenteredXiMellinNumeratorFunctionRankAudit`
  succeeds under `leanprover/lean4:v4.32.2`.
- `git diff --check` succeeds.
- No `sorry`, `admit`, `axiom`, or `native_decide` is introduced.
- The new public theorem depends on the prior arbitrary-jet and
  Vandermonde determinant theorems; no independent second determinant proof
  is added.
- `#print axioms` for the new public theorem reports only the standard
  foundational axioms `propext`, `Classical.choice`, and `Quot.sound`.
