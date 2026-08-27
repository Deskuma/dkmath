Global objective:
zero configuration -> independent source -> off-critical detector -> arithmetic control -> centered-coordinate uniqueness -> RiemannHypothesis

Current GWSS stage:
GWSS-001M-C1J

Load-bearing boundary:
The implemented results use the zero-independent symmetric exponential numerator and the pinned exponential Taylor remainder API.  No RH assumption, Weil positivity, Li criterion, fixed-Xi defect provider, horizontal decay, limit exchange, prime-side sign, carrier-dependent selector, or finite-evaluation claim is introduced.

Next unresolved Gap:
GENERAL-MELLIN-NUMERATOR-LINEAR-INDEPENDENCE-API-GAP

## C1J-A numerator surface status

FOUND.  The module defines `mellinSymmetricNumerator` and proves its value at
`τ = 0`, its zero-coordinate vanishing, evenness under `z ↦ -z`, and its
exact relation to the unpatched bare kernel for `τ ≠ 0`.  The patched kernel
value at `τ = 0` is not identified with the numerator.

## C1J-B arbitrary jet status

FOUND.  For every `m : ℕ`,
`tendsto_mellinSymmetricNumerator_generalJet` gives the punctured-neighborhood
quotient limit with exact coefficient
`2 * z^(2*m+2) / (2*m+2)!`.  The proof uses finite exponential Taylor
remainders and an explicit finite parity-cancellation identity; no formal
infinite series or unproved limit interchange is used.

## C1J-C coefficient-matrix bridge status

FOUND.  `mellinSymmetricNumeratorJetCoeff_eq_generalCoeff` and
`mellinSymmetricNumeratorJetCoeff_eq_coefficientMatrix` identify the numerator
coefficients with the existing `mellinJetCoefficientMatrix` normalization from
the 0014 Vandermonde audit.

## C1J-D linear-independence status

NOT CLOSED.  The arbitrary jet rows and their nonzero coefficient determinant
are now available, but the final generic wrapper from vanishing of a linear
combination of functions `τ ↦ G_τ(z_j)` to all coefficient-row equations
would require additional finite-dimensional function-space/span machinery.
Per the bounded stop rule, this is recorded as an API gap rather than silently
promoting jet rank to function rank.

## Primary classification

`GENERAL-MELLIN-NUMERATOR-JET-FOUND-LINEAR-INDEPENDENCE-API-GAP`

## GWSS-002 authorization status

Not authorized.  C1J finite evaluation, C2 actual-window transfer, and
GWSS-002 remain outside this assignment.

## Verification

- `lake build DkMath.RH.CFBRC.PascalCenteredXiMellinGeneralNumeratorJetAudit`
  succeeds under `leanprover/lean4:v4.32.2`.
- `git diff --check` succeeds.
- No `sorry`, `admit`, or new axiom declaration is introduced.
- `#print axioms` was run on the public numerator surface, arbitrary-jet,
  coefficient bridge, and inherited coefficient-rank theorem; only the
  standard foundational axioms `propext`, `Classical.choice`, and
  `Quot.sound` occur.
