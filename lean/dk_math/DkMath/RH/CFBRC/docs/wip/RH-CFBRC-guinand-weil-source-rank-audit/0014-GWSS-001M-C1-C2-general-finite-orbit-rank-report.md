Global objective:
zero configuration -> independent source -> off-critical detector -> arithmetic control -> centered-coordinate uniqueness -> RiemannHypothesis

Current GWSS stage:
GWSS-001M-C1/C2

Load-bearing boundary:
The implemented theorem is algebraic coefficient rank only.  It uses no RH assumption, classical Weil positivity, Li criterion, fixed-Xi defect provider, horizontal decay, limit exchange, prime-side sign, or carrier-dependent selector.  It does not identify z with -z pointwise.

Next unresolved Gap:
GENERAL-FINITE-MELLIN-EVALUATION-BRIDGE-API-GAP

## C1 arbitrary-jet status

Not closed.  The existing exponential remainder API supports the already
proved low-order jets, but no public arbitrary-order kernel remainder theorem
was added in this bounded pass.  Promoting the private low-order remainder
pattern to the required arbitrary-order statement remains a separate analytic
API task.

## C1 general squared-coordinate rank status

Partially closed.  The new
`mellinJetCoefficientMatrix_det_ne_zero` theorem proves the coefficient matrix
rank for every `Fin n` family of nonzero pairwise-distinct squared coordinates.
It factors the matrix into row and column diagonal scalings of the transpose
of `Matrix.vandermonde` and uses the pinned Mathlib determinant theorem.

## C1 finite-evaluation status

Not closed.  The pinned surface has Vandermonde determinant support, but no
direct theorem was found converting linear independence of a finite family of
functions into finitely many evaluation points with an invertible evaluation
matrix.  Building that bridge by induction or span/rank infrastructure would
be a substantial new abstract development and is therefore recorded as the
named API gap rather than silently inferred from jet rank.

## C2 actual squared-orbit carrier status

Not started.  Representative construction over
`(pascalCenteredXiZeroDiskFinset R).image (fun z => z ^ 2)` is intentionally
deferred until C1 finite evaluation rank is available.

## C2 spectral-factor transfer status

Not started for arbitrary `n`.  The exact fixed-`ε` column-scaling identities
for ranks 2 and 3 from C0 remain trusted and unchanged; no arbitrary-rank
scaling theorem is claimed here.

## C2 actual-window full-rank status

Not closed.  The full squared-orbit actual-window theorem requires the missing
finite-evaluation bridge and therefore cannot be obtained by reusing only the
rank-2/rank-3 eventual results.

## primary classification

`GENERAL-FINITE-ORBIT-RANK-API-GAP`

The coefficient Vandermonde portion is implemented, but the assignment does
not claim general finite nonzero-`τ` Mellin evaluation rank or actual-window
full rank.

## GWSS-002 authorization status

Not authorized.  GWSS-002 is outside this assignment and the C1/C2 full-rank
classification was not reached.

## verification

- `lake build DkMath.RH.CFBRC.PascalCenteredXiMellinGeneralFiniteRankAudit`
  succeeds under `leanprover/lean4:v4.32.2`.
- `git diff --check` succeeds.
- No `sorry`, `admit`, or new axiom declaration was introduced.
- `#print axioms` on `mellinJetCoefficientMatrix_det_ne_zero` reports only
  the standard foundational axioms `propext`, `Classical.choice`, and
  `Quot.sound`.
