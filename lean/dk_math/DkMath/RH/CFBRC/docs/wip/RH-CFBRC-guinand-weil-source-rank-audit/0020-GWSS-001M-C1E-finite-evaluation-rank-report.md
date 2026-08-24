Global objective:
zero configuration -> independent source -> off-critical detector -> arithmetic control -> centered-coordinate uniqueness -> RiemannHypothesis

Current GWSS stage:
GWSS-001M-C1E

Load-bearing boundary:
The finite-evaluation witnesses are constructed for an arbitrary finite family
of complex coordinates with nonzero, pairwise-distinct squares.  No Xi zero
carrier, actual Xi-window representative, RH assumption, classical Weil
positivity, Li criterion, fixed-Xi defect provider, horizontal decay,
unrelated limit exchange, prime-side sign assumption, or arithmetic source is
used.

## C1E-A finite numerator evaluation

FOUND.  The theorem
`exists_mellinSymmetricNumerator_evaluation_det_ne_zero` is proved by induction
on `n`.  At a successor step, the old evaluation matrix is retained in the
first rows and a variable final row is added.  If every resulting determinant
vanished, `Matrix.det_succ_row` would give an identically zero combination of
the symmetric numerator functions.  The existing C1L annihilation theorem
then forces every cofactor to vanish, contradicting the final-column cofactor,
which is the old nonzero determinant up to the even sign factor.

## C1E-B parameter consequences

FOUND.  The theorem
`evaluation_det_ne_zero_imp_parameters_ne_zero` uses the numerator's value at
`τ = 0` and the zero-row determinant lemma to prove every selected parameter
is nonzero.  The theorem
`evaluation_det_ne_zero_imp_parameters_injective` uses the repeated-row
determinant lemma to prove `Function.Injective τ`; hence the parameters are
pairwise distinct on the finite index type.

## C1E-C bare-kernel transfer

FOUND.  The theorem
`exists_complexExpSecondDifferenceKernel_evaluation_det_ne_zero` writes the
numerator matrix as
`diagonal (fun i => (τ i : ℂ)^2) * kernelMatrix` using
`mellinSymmetricNumerator_eq_kernel_mul`.  The determinant factorization and
nonzero row scales transfer determinant nonvanishing to the bare Mellin
kernel.

## Primary classification

`GENERAL-FINITE-NONZERO-TAU-MELLIN-RANK-FOUND`

## Next unresolved Gap

`ACTUAL-XI-WINDOW-FULL-MELLIN-RANK-TRANSFER-GAP`

The theorem does not place the existential parameters in the actual Xi
window or construct the squared-orbit carrier.  That is the bounded C2 task.

## Authorization status

GWSS-001M-C1E is closed.  GWSS-001M-C2 is authorized for the next bounded
assignment and was not started here.  GWSS-002 remains unauthorized and was
not started.

## Verification

- `lake build DkMath.RH.CFBRC.PascalCenteredXiMellinFiniteEvaluationRankAudit`
  succeeds under `leanprover/lean4:v4.32.2`.
- The load-bearing theorem axioms contain only `propext`, `Classical.choice`,
  and `Quot.sound`.
- No `sorry`, `admit`, new axiom, or `native_decide` is introduced.
- The new determinant argument reuses C1L and the existing exact kernel
  identity; it does not add a second Vandermonde proof or an interpolation
  library.
